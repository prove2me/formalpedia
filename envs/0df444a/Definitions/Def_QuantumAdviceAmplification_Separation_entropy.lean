-- Prove2me | Definitions.Def_QuantumAdviceAmplification_Separation_entropy
-- name    : QuantumAdviceAmplification_Separation_entropy
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:00:41.1947+00:00
-- url     : https://prove2.me/theorems/ed093b84-18b4-4e14-a74a-9896e1289ba5
-- title:
--   Binary entropy, its restricted inverse, and the perturbation envelope
-- statement:
--   Binary entropy is measured in bits: $H(p)=(-p\ln p-(1-p)\ln(1-p))/\ln2$, including its zero endpoint values. Its inverse is the inverse of the restriction to $[0,1/2]$, with arguments outside $[0,1]$ clamped for a total function. With $\kappa=\sqrt{\ln2/2}$,
--   $$\Phi(\varepsilon,\eta)=\min\{\kappa\sqrt\eta,\kappa^2\eta/(1/2-\varepsilon)\}.$$
--   At $\varepsilon=1/2$ the second entry is infinite and the function is explicitly $\kappa\sqrt\eta$. Positive lengths, eventual polynomial bounds, divergence, inverse-polynomial bias, and big-endian binary rank are also fixed here. These conventions are shared by all later statements.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.4, Section 2.1, Eqs. (1)–(3)

import Definitions.Def_QAlgorithms_Defs_Information
set_option autoImplicit false
noncomputable section

namespace QuantumAdviceAmplification.Separation

abbrev Bits (n : ℕ) := Fin n → Bool
abbrev Length := ℕ+
abbrev Language := List Bool → Bool

def log₂ (x : ℝ) : ℝ := Real.log x / Real.log 2

def H (p : ℝ) : ℝ := QAlgorithms.binEntropy2 p

/-- Inverse on [0,1/2], extended by clamping its argument to [0,1].
The defining set contains 1/2 and is bounded below by zero. -/
def Hinv (y : ℝ) : ℝ :=
  sInf {p : ℝ | 0 ≤ p ∧ p ≤ 1 / 2 ∧ min 1 (max 0 y) ≤ H p}

def κ : ℝ := Real.sqrt (Real.log 2 / 2)
def etaBar : ℝ := 1 / (2 * Real.log 2)

/-- The second entry is +infinity at epsilon=1/2; it must not be real division by zero. -/
def Φ (ε η : ℝ) : ℝ :=
  if ε = 1 / 2 then κ * Real.sqrt η
  else min (κ * Real.sqrt η) (κ ^ 2 * η / (1 / 2 - ε))

def PolyBounded (f : Length → ℕ) : Prop :=
  ∃ (A c N : ℕ), 0 < A ∧ ∀ n : Length, N ≤ n.val → f n ≤ A * n.val ^ c

def Diverges (f : Length → ℕ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, ∀ n : Length, N ≤ n.val → K ≤ f n

def Eventually (P : Length → Prop) : Prop :=
  ∃ N : ℕ, ∀ n : Length, N ≤ n.val → P n

def InfinitelyOften (P : Length → Prop) : Prop :=
  ∀ N : ℕ, ∃ n : Length, N ≤ n.val ∧ P n

def InvPolyGap (ε : Length → ℝ) : Prop :=
  ∃ b : ℝ, Eventually (fun n => Real.rpow (n.val : ℝ) (-b) ≤ 1 / 2 - ε n)

def bits (w v : ℕ) : List Bool :=
  (List.range w).map fun i => v.testBit (w - 1 - i)

def bin (v : ℕ) : List Bool := bits (Nat.log 2 v + 1) v

def vectorList {n : ℕ} (x : Bits n) : List Bool := List.ofFn x

def value (x : List Bool) : ℕ := x.foldl (fun v b => 2 * v + b.toNat) 0

def rank (x : List Bool) : ℕ := 1 + value x

end QuantumAdviceAmplification.Separation


