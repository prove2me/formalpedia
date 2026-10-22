-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
-- name    : LPCA_Solutions_LPCA_LocalizedDegreeSeparation_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:24:34.574036+00:00
-- url     : https://prove2.me/theorems/7450c4aa-2661-4dc2-b3fe-a52360e7a58c
-- title:
--   Localized Degree Separation for localized persistent commutative algebra
-- statement:
--   This bundle supplies localized Degree Separation for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Evaluation on any face containing the inversion set sends a degree-a piece into the Laurent line with that same full integer degree.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizedDegreeSeparation.lean, selected declarations in lines 12–98; source SHA-256 3182a87e741229ca044a40185f95a623c7115321150c51bbbe5117294aa029b7; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

theorem laurentLocalizationMap_monomial (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G)
    (a : V → ℤ) (m : V →₀ ℕ) (N : ℕ)
    (hm : m.support ⊆ G)
    (hdegree : ∀ j, (m j : ℤ) - (if j ∈ F then (N : ℤ) else 0) = a j) :
    laurentLocalizationMap k K G hG F hFG (localizedMonomial k K F m N) =
      AddMonoidAlgebra.single a (1 : k) := by
  classical
  have hs : laurentLocalizationMap k K G hG F hFG (localizedMonomial k K F m N) *
      laurentLocalizationMap k K G hG F hFG
        (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (invertedMonomial k K F ^ N)) =
      laurentLocalizationMap k K G hG F hFG
        (algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
          (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k)))) := by
    rw [← map_mul, localizedMonomial, IsLocalization.mk'_spec]
  simp only [laurentLocalizationMap_base, laurentFaceMap_mk] at hs
  rw [laurentPolynomialMap_monomial k G m hm, map_pow,
    laurentFaceMap_inverted k K G hG F hFG, AddMonoidAlgebra.single_pow, one_pow] at hs
  apply (laurentSingle_isUnit k (N • laurentIndicator F)).mul_left_inj.mp
  rw [hs, AddMonoidAlgebra.single_mul_single, one_mul]
  congr 1
  funext j
  have hj := hdegree j
  simp only [Pi.add_apply, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
    laurentIndicator_apply]
  by_cases hjF : j ∈ F
  · simp only [if_pos hjF, mul_one] at *
    omega
  · simp only [if_neg hjF, mul_zero, add_zero, sub_zero] at *
    exact hj

theorem laurentLocalizationMap_monomial_zero (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G)
    (m : V →₀ ℕ) (N : ℕ) (hm : ¬ m.support ⊆ G) :
    laurentLocalizationMap k K G hG F hFG (localizedMonomial k K F m N) = 0 := by
  classical
  have hs : laurentLocalizationMap k K G hG F hFG (localizedMonomial k K F m N) *
      laurentLocalizationMap k K G hG F hFG
        (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (invertedMonomial k K F ^ N)) =
      laurentLocalizationMap k K G hG F hFG
        (algebraMap (FaceRing k K) (LocalizedFaceRing k K F)
          (Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.monomial m (1 : k)))) := by
    rw [← map_mul, localizedMonomial, IsLocalization.mk'_spec]
  simp only [laurentLocalizationMap_base, laurentFaceMap_mk] at hs
  rw [laurentPolynomialMap_monomial_zero k G m hm, map_pow,
    laurentFaceMap_inverted k K G hG F hFG, AddMonoidAlgebra.single_pow, one_pow] at hs
  apply (laurentSingle_isUnit k (N • laurentIndicator F)).mul_left_inj.mp
  simpa only [zero_mul] using hs

/-- Evaluation on any face containing the inversion set sends a degree-a
piece into the Laurent line with that same full integer degree. -/
theorem laurentLocalizationLinearMap_piece (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G) (a : V → ℤ)
    {z : LocalizedFaceRing k K F} (hz : z ∈ localizedPiece k K F a) :
    laurentLocalizationLinearMap k K G hG F hFG z ∈
      Submodule.span k {AddMonoidAlgebra.single a (1 : k)} := by
  classical
  have hl : localizedPiece k K F a ≤
      (Submodule.span k {AddMonoidAlgebra.single a (1 : k)}).comap
        (laurentLocalizationLinearMap k K G hG F hFG) := by
    apply Submodule.span_le.mpr
    rintro z ⟨m, N, hd, rfl⟩
    change laurentLocalizationMap k K G hG F hFG (localizedMonomial k K F m N) ∈
      Submodule.span k {AddMonoidAlgebra.single a (1 : k)}
    by_cases hm : m.support ⊆ G
    · rw [laurentLocalizationMap_monomial k K G hG F hFG a m N hm hd]
      exact Submodule.subset_span (Set.mem_singleton _)
    · rw [laurentLocalizationMap_monomial_zero k K G hG F hFG m N hm]
      exact Submodule.zero_mem _
  exact hl hz

noncomputable def laurentDegreeCoefficient (a : V → ℤ) :
    LaurentDegreeRing (V := V) k →ₗ[k] k where
  toFun z := z.coeff a
  map_add' x y := by simp
  map_smul' c z := by simp

theorem laurentDegreeCoefficient_piece_ne (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G) (a b : V → ℤ)
    (hab : a ≠ b) {z : LocalizedFaceRing k K F} (hz : z ∈ localizedPiece k K F b) :
    laurentDegreeCoefficient k a (laurentLocalizationLinearMap k K G hG F hFG z) = 0 := by
  classical
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp
    (laurentLocalizationLinearMap_piece k K G hG F hFG b hz)
  rw [← hc]
  change (c • AddMonoidAlgebra.single b (1 : k)).coeff a = 0
  simp [hab, Ne.symm hab]

end LPCA


