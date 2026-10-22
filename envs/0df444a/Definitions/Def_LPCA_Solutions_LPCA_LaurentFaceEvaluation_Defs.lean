-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
-- name    : LPCA_Solutions_LPCA_LaurentFaceEvaluation_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:23:32.901095+00:00
-- url     : https://prove2.me/theorems/93b64d8d-1bdd-4155-be33-84f3b764b7ae
-- title:
--   Laurent Face Evaluation for localized persistent commutative algebra
-- statement:
--   This bundle supplies laurent Face Evaluation for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Laurent monomials keep the entire integer degree as an independent basis index. The target is used to detect distinct localized degrees.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LaurentFaceEvaluation.lean, selected declarations in lines 14–142; source SHA-256 e1909b5189ac4024abbbde8626b0622abeb99c693fc2c90dc8b6147200e4b328; source certificate Sapelo2 job 49172236.

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
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

/-- Laurent monomials keep the entire integer degree as an independent
basis index. The target is used to detect distinct localized degrees. -/
abbrev LaurentDegreeRing : Type u := AddMonoidAlgebra k (V → ℤ)

noncomputable def laurentPolynomialMap (G : Finset V) :
    MvPolynomial V k →+* LaurentDegreeRing (V := V) k := by
  classical
  exact MvPolynomial.eval₂Hom (algebraMap k (LaurentDegreeRing (V := V) k))
    (fun j => if j ∈ G then AddMonoidAlgebra.single (Pi.single j (1 : ℤ)) 1 else 0)

noncomputable def laurentIndicator (F : Finset V) : V → ℤ :=
  ∑ j ∈ F, Pi.single j (1 : ℤ)

theorem laurentIndicator_apply (F : Finset V) (j : V) :
    laurentIndicator F j = if j ∈ F then 1 else 0 := by
  classical
  simp [laurentIndicator, Pi.single_apply]

theorem laurentPolynomialMap_monomial (G : Finset V) (m : V →₀ ℕ)
    (hm : m.support ⊆ G) :
    laurentPolynomialMap k G (MvPolynomial.monomial m (1 : k)) =
      AddMonoidAlgebra.single (fun j => (m j : ℤ)) (1 : k) := by
  classical
  change MvPolynomial.eval₂ _ _ (MvPolynomial.monomial m (1 : k)) = _
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul]
  change (∏ j ∈ m.support,
    (if j ∈ G then AddMonoidAlgebra.single (Pi.single j (1 : ℤ)) (1 : k) else 0) ^ m j) = _
  calc
    _ = ∏ j ∈ m.support, AddMonoidAlgebra.single
        (m j • Pi.single j (1 : ℤ)) (1 : k) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [hm hj, AddMonoidAlgebra.single_pow]
    _ = AddMonoidAlgebra.single
        (∑ j ∈ m.support, m j • Pi.single j (1 : ℤ)) (1 : k) := by
      rw [AddMonoidAlgebra.prod_single]
      simp
    _ = _ := by
      congr 1
      funext j
      by_cases hj : j ∈ m.support
      · simp [Pi.single_apply, hj]
      · have hz : m j = 0 := by simpa only [Finsupp.mem_support_iff, not_not] using hj
        simp [Pi.single_apply, hj, hz]

theorem laurentPolynomialMap_monomial_zero (G : Finset V) (m : V →₀ ℕ)
    (hm : ¬ m.support ⊆ G) :
    laurentPolynomialMap k G (MvPolynomial.monomial m (1 : k)) = 0 := by
  classical
  obtain ⟨j, hj, hjG⟩ := Finset.not_subset.mp hm
  change MvPolynomial.eval₂ _ _ (MvPolynomial.monomial m (1 : k)) = _
  rw [MvPolynomial.eval₂_monomial, map_one, one_mul]
  change (∏ j ∈ m.support,
    (if j ∈ G then AddMonoidAlgebra.single (Pi.single j (1 : ℤ)) (1 : k) else 0) ^ m j) = 0
  apply Finset.prod_eq_zero hj
  simp [hjG, Finsupp.mem_support_iff.mp hj]

noncomputable def laurentFaceMap (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) : FaceRing k K →+* LaurentDegreeRing (V := V) k := by
  classical
  have hk : srIdeal k K ≤ RingHom.ker (laurentPolynomialMap k G) := by
    apply Ideal.span_le.mpr
    rintro p ⟨H, hH, rfl⟩
    have hn : ¬ H ⊆ G := fun hHG => hH (K.down_closed hG hHG)
    obtain ⟨j, hj, hjG⟩ := Finset.not_subset.mp hn
    change laurentPolynomialMap k G (∏ j ∈ H, MvPolynomial.X j) = 0
    rw [map_prod]
    apply Finset.prod_eq_zero hj
    simp [laurentPolynomialMap, hjG]
  exact Ideal.Quotient.lift (srIdeal k K) (laurentPolynomialMap k G)
    (fun p hp => RingHom.mem_ker.mp (hk hp))

@[simp] theorem laurentFaceMap_mk (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (p : MvPolynomial V k) :
    laurentFaceMap k K G hG (Ideal.Quotient.mk (srIdeal k K) p) =
      laurentPolynomialMap k G p := rfl

theorem laurentFaceMap_scalar (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (c : k) :
    laurentFaceMap k K G hG (algebraMap k (FaceRing k K) c) =
      algebraMap k (LaurentDegreeRing (V := V) k) c := by
  change laurentPolynomialMap k G (MvPolynomial.C c) = _
  simp [laurentPolynomialMap]

theorem laurentFaceMap_inverted (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G) :
    laurentFaceMap k K G hG (invertedMonomial k K F) =
      AddMonoidAlgebra.single (laurentIndicator F) (1 : k) := by
  classical
  unfold invertedMonomial
  rw [map_prod]
  calc
    _ = ∏ j ∈ F, AddMonoidAlgebra.single (Pi.single j (1 : ℤ)) (1 : k) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp [variableClass, laurentPolynomialMap, hFG hj]
    _ = _ := by rw [AddMonoidAlgebra.prod_single]; simp [laurentIndicator]

theorem laurentSingle_isUnit (a : V → ℤ) :
    IsUnit (AddMonoidAlgebra.single a (1 : k)) := by
  let v : Units (LaurentDegreeRing (V := V) k) := {
    val := AddMonoidAlgebra.single a 1
    inv := AddMonoidAlgebra.single (-a) 1
    val_inv := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def]
    inv_val := by simp [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.one_def] }
  exact ⟨v, rfl⟩

noncomputable def laurentLocalizationMap (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G) :
    LocalizedFaceRing k K F →+* LaurentDegreeRing (V := V) k :=
  IsLocalization.Away.lift (invertedMonomial k K F) (g := laurentFaceMap k K G hG) (by
    rw [laurentFaceMap_inverted k K G hG F hFG]
    exact laurentSingle_isUnit k _)

@[simp] theorem laurentLocalizationMap_base (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G) (r : FaceRing k K) :
    laurentLocalizationMap k K G hG F hFG
        (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) r) =
      laurentFaceMap k K G hG r :=
  IsLocalization.Away.lift_eq _ _ _

noncomputable def laurentLocalizationLinearMap (K : Complex V) (G : Finset V)
    (hG : G ∈ K.faces) (F : Finset V) (hFG : F ⊆ G) :
    LocalizedFaceRing k K F →ₗ[k] LaurentDegreeRing (V := V) k where
  toFun := laurentLocalizationMap k K G hG F hFG
  map_add' := map_add _
  map_smul' c z := by
    rw [localized_smul_base, map_mul, laurentLocalizationMap_base, laurentFaceMap_scalar]
    exact (Algebra.smul_def c _).symm

end LPCA


