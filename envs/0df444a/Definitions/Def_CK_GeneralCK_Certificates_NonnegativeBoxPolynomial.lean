-- Prove2me | Definitions.Def_CK_GeneralCK_Certificates_NonnegativeBoxPolynomial
-- name    : CK_GeneralCK_Certificates_NonnegativeBoxPolynomial
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-09-28T03:53:45.060577+00:00
-- url     : https://prove2.me/theorems/04c6572d-a46a-4ec6-8551-8abf79e08aef
-- title:
--   Courtade–Kumar proof module `GeneralCK.Certificates.NonnegativeBoxPolynomial` (transplant)
-- statement:
--   Verbatim transplant of the Lean module `GeneralCK.Certificates.NonnegativeBoxPolynomial` of the machine-checked proof of the general Courtade–Kumar theorem (the most informative Boolean function conjecture), so that the complete proof can be verified on this platform.
--
--   It is the original source with only two mechanical changes. Imports of project modules are redirected to their transplanted bundles `Definitions.Def_CK_*`. Declarations that already exist in earlier platform definition bundles of this mission are removed, and those bundles are imported instead, so every constant keeps a single platform identity.
--
--   The module contains both definitions and the lemmas proved alongside them in the source. They are kept together so the transplant stays faithful and every proof is re-checked by the server.
--
--   Source: Z. Chen, A. Gohari, A. Javanmard, H. Lin, V. Mirrokni, C. Nair, D. P. Woodruff, *A Proof of the Most Informative Boolean Function Conjecture*, arXiv:2609.24931 (2026). Lean development: https://github.com/dpwoodru/general-courtade-kumar-lean (Apache-2.0), module `GeneralCK.Certificates.NonnegativeBoxPolynomial` from release v1.0 (`sources_v3.tar.zst`).
-- source:
--   arXiv:2609.24931; https://github.com/dpwoodru/general-courtade-kumar-lean release v1.0, module GeneralCK.Certificates.NonnegativeBoxPolynomial (browse copy where available: https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/NonnegativeBoxPolynomial.lean)

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

-- ===== source module GeneralCK.Certificates.NonnegativeBoxPolynomial =====
section

namespace GeneralCK.Certificates.NonnegativeBoxPolynomial

noncomputable section

/-- A sparse integer coefficient monomial in three variables. -/
structure Term where
  coefficient : ℤ
  xPower : ℕ
  yPower : ℕ
  zPower : ℕ
  deriving DecidableEq, Repr

def evalTerm (m : Term) (x y z : ℝ) : ℝ :=
  (m.coefficient : ℝ) * (x ^ m.xPower * y ^ m.yPower * z ^ m.zPower)

def eval : List Term → ℝ → ℝ → ℝ → ℝ
  | [], _, _, _ => 0
  | m :: ms, x, y, z => evalTerm m x y z + eval ms x y z

/-- Keep the constant, bound negative monomials at the box maxima, and
discard positive nonconstant monomials. All checker arithmetic is rational. -/
def lowerTerm (m : Term) (X Y Z : ℚ) : ℚ :=
  if m.xPower = 0 ∧ m.yPower = 0 ∧ m.zPower = 0 then m.coefficient
  else if m.coefficient < 0 then
    m.coefficient * (X ^ m.xPower * Y ^ m.yPower * Z ^ m.zPower)
  else 0

def lowerBound : List Term → ℚ → ℚ → ℚ → ℚ
  | [], _, _, _ => 0
  | m :: ms, X, Y, Z => lowerTerm m X Y Z + lowerBound ms X Y Z

theorem lowerTerm_le_evalTerm (m : Term) {x y z : ℝ} {X Y Z : ℚ}
    (hx : 0 ≤ x) (hX : x ≤ (X : ℝ))
    (hy : 0 ≤ y) (hY : y ≤ (Y : ℝ))
    (hz : 0 ≤ z) (hZ : z ≤ (Z : ℝ)) :
    (lowerTerm m X Y Z : ℝ) ≤ evalTerm m x y z := by
  by_cases hzero : m.xPower = 0 ∧ m.yPower = 0 ∧ m.zPower = 0
  · simp [lowerTerm, hzero, evalTerm]
  · by_cases hc : m.coefficient < 0
    · have hX0 : (0 : ℝ) ≤ X := hx.trans hX
      have hY0 : (0 : ℝ) ≤ Y := hy.trans hY
      have hZ0 : (0 : ℝ) ≤ Z := hz.trans hZ
      have hmono : x ^ m.xPower * y ^ m.yPower * z ^ m.zPower ≤
          (X : ℝ) ^ m.xPower * (Y : ℝ) ^ m.yPower * (Z : ℝ) ^ m.zPower := by
        gcongr
      have hc' : (m.coefficient : ℝ) ≤ 0 := by exact_mod_cast hc.le
      simpa [lowerTerm, hzero, hc, evalTerm] using
        mul_le_mul_of_nonpos_left hmono hc'
    · have hc' : (0 : ℝ) ≤ m.coefficient := by exact_mod_cast (le_of_not_gt hc)
      simp only [lowerTerm, hzero, ↓reduceIte, hc, Rat.cast_zero, evalTerm]
      positivity

theorem lowerBound_le_eval (ms : List Term) {x y z : ℝ} {X Y Z : ℚ}
    (hx : 0 ≤ x) (hX : x ≤ (X : ℝ))
    (hy : 0 ≤ y) (hY : y ≤ (Y : ℝ))
    (hz : 0 ≤ z) (hZ : z ≤ (Z : ℝ)) :
    (lowerBound ms X Y Z : ℝ) ≤ eval ms x y z := by
  induction ms with
  | nil => simp [lowerBound, eval]
  | cons m ms ih =>
    simpa only [lowerBound, eval, Rat.cast_add] using
      add_le_add (lowerTerm_le_evalTerm m hx hX hy hY hz hZ) ih

theorem certificate_sound (ms : List Term) {x y z : ℝ} {X Y Z L : ℚ}
    (hcheck : L ≤ lowerBound ms X Y Z)
    (hx : 0 ≤ x) (hX : x ≤ (X : ℝ))
    (hy : 0 ≤ y) (hY : y ≤ (Y : ℝ))
    (hz : 0 ≤ z) (hZ : z ≤ (Z : ℝ)) :
    (L : ℝ) ≤ eval ms x y z := by
  have hc : (L : ℝ) ≤ (lowerBound ms X Y Z : ℝ) := by exact_mod_cast hcheck
  exact hc.trans (lowerBound_le_eval ms hx hX hy hY hz hZ)

#print axioms lowerTerm_le_evalTerm
#print axioms lowerBound_le_eval
#print axioms certificate_sound

end
end GeneralCK.Certificates.NonnegativeBoxPolynomial

end


