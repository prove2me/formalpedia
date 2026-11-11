-- Prove2me | Definitions.Def_QuantumAdviceAmplification_Separation_parameters
-- name    : QuantumAdviceAmplification_Separation_parameters
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T06:03:30.182127+00:00
-- url     : https://prove2.me/theorems/d0744d09-23d1-4727-87e0-261dc289c2a3
-- title:
--   Quantitative advice parameters and the full separation predicate
-- statement:
--   The coding overhead is $\eta(k,s)=\log_2s/s+s/k$, and its entropy optimum is $H^{-1}(1-m/k)$. The upper-error function includes both the admissible-length and the default half-error branches. Define
--   $$k(n)=\min\{\lfloor m(n)/(1-H(\varepsilon(n)))\rfloor+1,2^n\}.$$
--   Good lengths and the piecewise gap $\delta$ are exactly equations (58)–(59). The balanced budget is the maximum of the two ceilings in equation (65). The fourth-root and square-root rates use binary logarithms. The predicate for upper-bound constants unfolds to the entire upper-bound theorem; it does not assert an axiom. The full separation predicate requires both classical noncontainment and strict quantum inclusion for the same gap. These formulas introduce no computed preparation or hidden algorithmic cost assumptions.
-- source:
--   Shih-Han Hung, Han-Hsuan Lin, STOC 2027 submission #1297 (October 2026), p.12, Eq. (30); p.15, Eqs. (49)–(50); pp.17–19, Eqs. (58)–(59), (65), (67)

import Definitions.Def_QuantumAdviceAmplification_Separation_classes
import Definitions.Def_QuantumAdviceAmplification_Separation_codes
set_option autoImplicit false
noncomputable section

namespace QuantumAdviceAmplification.Separation

open Classical

def overhead (k s : ℕ) : ℝ := log₂ s / s + (s : ℝ) / k

def optimumError (k m : ℕ) : ℝ := Hinv (1 - (m : ℝ) / k)

def upperError (c1 C : ℝ) (m k s : Length → ℕ) (n : Length) : ℝ :=
  if m n ≤ k n ∧ c1 * (log₂ (2 * k n)) ^ 2 ≤ s n then
    min (1 / 2) (optimumError (k n) (m n) + C * Φ (optimumError (k n) (m n)) (overhead (k n) (s n)))
  else 1 / 2

def separationK (m : Length → ℕ) (ε : Length → ℝ) (n : Length) : ℕ :=
  min (⌊(m n : ℝ) / (1 - H (ε n))⌋₊ + 1) (2 ^ n.val)

def Good (c1 : ℝ) (m s : Length → ℕ) (ε : Length → ℝ) (n : Length) : Prop :=
  (m n : ℝ) < (1 - H (ε n)) * 2 ^ n.val ∧
    c1 * (log₂ (2 * separationK m ε n)) ^ 2 ≤ s n

def separationDelta (c1 C : ℝ) (m s : Length → ℕ) (ε : Length → ℝ) (n : Length) : ℝ :=
  if Good c1 m s ε n then
    min (1 / 2) ((2 * C + 1) * Φ (ε n)
      (overhead (separationK m ε n) (s n) + 1 / (m n : ℝ)))
  else 1 / 2

def balancedBudget (c1 : ℝ) (m : Length → ℕ) (ε : Length → ℝ) (n : Length) : ℕ :=
  max ⌈Real.sqrt (separationK m ε n * log₂ (separationK m ε n))⌉₊
    ⌈c1 * (log₂ (2 * separationK m ε n)) ^ 2⌉₊

def fourthRootRate (m : ℕ) : ℝ := Real.rpow (log₂ m / m) (1 / 4)
def squareRootRate (m : ℕ) : ℝ := Real.sqrt (log₂ m / m)

/-- The entire quantified upper-bound property of Theorem 4.2, used to refer to
its absolute constants without adding the separation as a hypothesis. -/
def UpperBoundConstants (c1 C : ℝ) : Prop :=
  1 ≤ c1 ∧ 1 ≤ C ∧ ∀ (m k s : Length → ℕ),
    (∀ n, 0 < m n ∧ 0 < k n ∧ 0 < s n ∧ k n ≤ 2 ^ n.val) →
    ∀ R : Language, restrictedLanguage k R ∈
      DTIME (fun n => n.val ^ 2 + s n) m (upperError c1 C m k s)

def FullSeparation (G : GateAlphabet) (m : Length → ℕ) (ε δ : Length → ℝ) : Prop :=
  (¬ PAdvice m (fun n => ε n + δ n) ⊆ BQPAdvice G m ε) ∧
    BQPAdvice G m ε ⊂ BQPAdvice G m (fun n => ε n + δ n)

end QuantumAdviceAmplification.Separation


