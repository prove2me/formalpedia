-- Prove2me | Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrame
-- name    : OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrame
-- status  : Definition
-- author  : @Yuxuan Xu
-- created : 2026-10-08T14:19:38.859743+00:00
-- url     : https://prove2.me/theorems/e07adae4-be61-459d-9ddf-444e8f6a176b
-- title:
--   Weighted-degree control for polynomial logarithmic and partial derivations
-- statement:
--   For polynomials over ℂ in m + 1 variables, FramePolynomial m abbreviates the corresponding multivariate polynomial type. The logarithmicDerivation is the derivation X₀ ∂₀ + ∑ᵢ₌₀^{m−1} ∂ᵢ₊₁, and polynomialFrame selects this derivation at index 0 and the indexed partial derivative at every nonzero index. polynomialFrameWord applies a finite list of these derivations by right fold. For a nonnegative weight function w, each selected derivation and every finite word of them preserves the predicate HasWeightedDegreeLE w N. The bundle also states the action formula for logarithmicDerivation, its special cases for polynomialFrame, and evaluation of a finite sum of derivations.
-- source:
--   OpenAI math, commit adc7f1241b42e322a6451854ab7e4b4c146bf78a: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Polynomials/PolynomialFrame.lean#L12-L169

import Definitions.Def_OAI_NumberTheory_PiExponent_Polynomials_PolynomialFrameDegree
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring




namespace OAI

namespace PiExponentApprox

noncomputable section

abbrev FramePolynomial (m : ℕ) := MvPolynomial (Fin (m + 1)) ℂ

def logarithmicDerivation (m : ℕ) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  (MvPolynomial.X (0 : Fin (m + 1)) : FramePolynomial m) •
    MvPolynomial.pderiv (R := ℂ) (0 : Fin (m + 1)) +
    ∑ i : Fin m, MvPolynomial.pderiv (R := ℂ) i.succ

def polynomialFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation ℂ (FramePolynomial m) (FramePolynomial m) :=
  if i = 0 then logarithmicDerivation m else MvPolynomial.pderiv i

theorem derivation_finset_sum_apply {α : Type*} (m : ℕ) (s : Finset α)
    (D : α → Derivation ℂ (FramePolynomial m) (FramePolynomial m))
    (p : FramePolynomial m) : (∑ a ∈ s, D a) p = ∑ a ∈ s, D a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Derivation.zero_apply]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

@[simp] theorem logarithmicDerivation_apply (m : ℕ) (p : FramePolynomial m) :
    logarithmicDerivation m p =
      MvPolynomial.X (0 : Fin (m + 1)) * MvPolynomial.pderiv 0 p +
        ∑ i : Fin m, MvPolynomial.pderiv i.succ p := by
  simp only [logarithmicDerivation, Derivation.add_apply, Derivation.smul_apply,
    derivation_finset_sum_apply, smul_eq_mul]

@[simp] theorem polynomialFrame_zero (m : ℕ) :
    polynomialFrame m 0 = logarithmicDerivation m := by
  simp only [polynomialFrame, ite_true]

@[simp] theorem polynomialFrame_pos (m : ℕ) (i : Fin (m + 1)) (hi : i ≠ 0) :
    polynomialFrame m i = MvPolynomial.pderiv i := by
  simp only [polynomialFrame, if_neg hi]













theorem HasWeightedDegreeLE.logarithmicDerivation {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) :
    HasWeightedDegreeLE w N (PiExponentApprox.logarithmicDerivation m p) := by
  rw [logarithmicDerivation_apply]
  apply (hp.X_mul_pderiv 0).add
  exact HasWeightedDegreeLE.sum Finset.univ _
    (fun i _ => hp.pderiv_preserves i.succ (hw i.succ))

theorem HasWeightedDegreeLE.polynomialFrame {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i) (i : Fin (m + 1)) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrame m i p) := by
  by_cases hi : i = 0
  · subst i
    rw [polynomialFrame_zero]
    exact hp.logarithmicDerivation hw
  · rw [polynomialFrame_pos m i hi]
    exact hp.pderiv_preserves i (hw i)

def polynomialFrameWord (m : ℕ) (word : List (Fin (m + 1)))
    (p : FramePolynomial m) : FramePolynomial m :=
  word.foldr (fun i q => polynomialFrame m i q) p







theorem HasWeightedDegreeLE.polynomialFrameWord {m : ℕ}
    {w : Fin (m + 1) → ℝ} {N : ℝ} {p : FramePolynomial m}
    (hp : HasWeightedDegreeLE w N p) (hw : ∀ i, 0 ≤ w i)
    (word : List (Fin (m + 1))) :
    HasWeightedDegreeLE w N (PiExponentApprox.polynomialFrameWord m word p) := by
  induction word with
  | nil => exact hp
  | cons i word ih => exact ih.polynomialFrame hw i

end
end PiExponentApprox

end OAI


