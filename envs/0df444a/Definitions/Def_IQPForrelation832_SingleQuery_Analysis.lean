-- Prove2me | Definitions.Def_IQPForrelation832_SingleQuery_Analysis
-- name    : IQPForrelation832_SingleQuery_Analysis
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T03:04:44.856764+00:00
-- url     : https://prove2.me/theorems/e0b2f2b5-3cbb-4a7f-b04e-e2efa26f1c67
-- title:
--   Boolean cube, orthonormal Fourier transform and quadratic phases
-- statement:
--   Let $V_n=\mathbb F_2^n$, with coordinatewise XOR addition, binary pairing $x\cdot y$, and integer Hamming weight $|x|$. The published unrestricted forrelation is reused. With the same normalization as the paper,
--   $$
--   \Phi(f,g)=2^{-3n/2}\sum_{x,y\in V_n}(-1)^{x\cdot y}f(x)g(y),\qquad
--   \widehat h(x)=2^{-n/2}\sum_{y\in V_n}(-1)^{x\cdot y}h(y).
--   $$
--   Here $h$ may be complex-valued; a separate real-valued transform uses the same formula. Define $Q(x)=\sum_{i<j}x_ix_j$ modulo two, and define $\sigma_{\rm odd}$ and $\sigma_{\rm even}$ as $\sqrt2(-1)^{Q(x)}$ on the indicated Hamming-weight parity and zero elsewhere. The parity forrelations retain the corresponding pairs with $|x+y|$ odd or even. Padding ignores the last coordinate.
--
--   This module fixes the analysis shared by all ten results. An explicit coordinatewise equivalence between Boolean registers and $V_n$ preserves the first, most significant, wire. All dimensions, including zero, are allowed. No transform, polarization or padding identity is assumed.
-- source:
--   Quentin Buzet, André Chailloux, IQP circuits for 2-Forrelation, STOC 2027 submission #832 (October 2026), pp. 1–2, 11 (§2.1), 16 (Definition 5 and parity sums), 17–18 (phase functions), 20 (Definition 6). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/832.pdf

import Definitions.Def_ExtremalForrelation_Nonadaptive_Basic
import Definitions.Def_QAlgorithms_Defs_Circuit

set_option autoImplicit false

namespace IQPForrelation832.SingleQuery

abbrev Cube := ExtremalForrelation.Nonadaptive.V
abbrev dot := @ExtremalForrelation.Nonadaptive.dot
noncomputable abbrev Phi := @ExtremalForrelation.Nonadaptive.forr

/-- Coordinatewise identification, preserving the first (most significant) wire. -/
def bitEquiv : Bool ≃ ZMod 2 where
  toFun b := if b then 1 else 0
  invFun z := z == 1
  left_inv := by decide
  right_inv := by decide

def cubeEquiv (n : ℕ) : QAlgorithms.Qubits n ≃ Cube n :=
  Equiv.piCongrRight (fun _ => bitEquiv)

def weight {n : ℕ} (x : Cube n) : ℕ := ∑ i, (x i).val

def character {n : ℕ} (x y : Cube n) : ℝ := (-1 : ℝ) ^ (dot x y).val

def IsSign {α : Type} (f : α → ℝ) : Prop := ∀ x, f x = -1 ∨ f x = 1

noncomputable def fourier {n : ℕ} (h : Cube n → ℂ) (x : Cube n) : ℂ :=
  (Real.sqrt ((2 : ℝ) ^ n) : ℂ)⁻¹ * ∑ y, (character x y : ℂ) * h y

noncomputable def realFourier {n : ℕ} (h : Cube n → ℝ) (x : Cube n) : ℝ :=
  (Real.sqrt ((2 : ℝ) ^ n))⁻¹ * ∑ y, character x y * h y

/-- The summation is over i<j, in the field F₂. -/
def Q {n : ℕ} (x : Cube n) : ZMod 2 :=
  ∑ i : Fin n, ∑ j : Fin n, if i < j then x i * x j else 0

noncomputable def sigmaOdd {n : ℕ} (x : Cube n) : ℝ :=
  if Odd (weight x) then Real.sqrt 2 * (-1 : ℝ) ^ (Q x).val else 0

noncomputable def sigmaEven {n : ℕ} (x : Cube n) : ℝ :=
  if Even (weight x) then Real.sqrt 2 * (-1 : ℝ) ^ (Q x).val else 0

noncomputable def parityPhi {n : ℕ} (oddPart : Bool) (f g : Cube n → ℝ) : ℝ :=
  (Real.sqrt ((2 : ℝ) ^ (3*n)))⁻¹ *
    ∑ x, ∑ y, if (weight (x+y)) % 2 = (if oddPart then 1 else 0) then
      character x y * f x * g y else 0

/-- Definition 6: ignore the last, dummy, coordinate. -/
def pad {n : ℕ} (f : Cube n → ℝ) : Cube (n+1) → ℝ :=
  fun x => f (fun i => x i.castSucc)

/-- Self-delimiting address payload, first wire first. -/
def cubeBits {n : ℕ} (x : Cube n) : List Bool := List.ofFn ((cubeEquiv n).symm x)

end IQPForrelation832.SingleQuery


