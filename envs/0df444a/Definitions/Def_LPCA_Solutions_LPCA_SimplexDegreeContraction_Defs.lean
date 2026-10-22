-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
-- name    : LPCA_Solutions_LPCA_SimplexDegreeContraction_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:43:02.047491+00:00
-- url     : https://prove2.me/theorems/30faa766-b437-4654-9c3a-0c8afa671eba
-- title:
--   Simplex Degree Contraction for localized persistent commutative algebra
-- statement:
--   This bundle supplies simplex Degree Contraction for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The contraction restricts to the actual consecutive chain degrees.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_SimplexDegreeContraction.lean, selected declarations in lines 28–164; source SHA-256 0d9386151336d21745c6209e362caf25cce9f50569a21fb5338a685d757be819; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_Common_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_dd_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_eps_mul_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_exists_insert_of_inc_ne_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_hc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_eq_zero_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_inc_sum_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_insert_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_inc_sdiff_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_erase_self_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_gt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_insert_of_lt_Defs
import Definitions.Def_LPCA_Proofs_BassLyubeznik_SignedCore_nu_sdiff_add_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SimplexContraction_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V] [Fintype V]
variable (k : Type u) [Field k]

private theorem sum_subset_card (E : Finset V) (p : ℕ) (f : SubsetIndex E → k)
    (hf : ∀ F : SubsetIndex E, F.1.card ≠ p → f F = 0) :
    ∑ F : SubsetIndex E, f F =
      ∑ F : CechSlot E p, f ⟨F.1, F.2.1⟩ := by
  classical
  symm
  apply Fintype.sum_of_injective
    (fun F : CechSlot E p => (⟨F.1, F.2.1⟩ : SubsetIndex E))
    (fun F G h => Subtype.ext (congrArg (fun x : SubsetIndex E => x.1) h))
  · intro F hF
    apply hf F
    intro hcard
    exact hF ⟨⟨F.1, F.2, hcard⟩, Subtype.ext rfl⟩
  · intro F
    rfl

noncomputable def simplexDegreeInclude (E : Finset V) (p : ℕ) :
    (CechSlot E p → k) →ₗ[k] (SubsetIndex E → k) := by
  classical
  exact {
    toFun := fun y F => if h : F.1.card = p then y ⟨F.1, F.2, h⟩ else 0
    map_add' := by
      intro x y
      funext F
      simp only [Pi.add_apply]
      by_cases h : F.1.card = p
      · simp only [dif_pos h, Pi.add_apply]
      · simp only [dif_neg h, add_zero]
    map_smul' := by
      intro c y
      funext F
      simp only [Pi.smul_apply, RingHom.id_apply]
      by_cases h : F.1.card = p
      · simp only [dif_pos h, Pi.smul_apply]
      · simp only [dif_neg h, smul_zero] }

theorem simplexDegreeInclude_apply_card (E : Finset V) (p : ℕ)
    (y : CechSlot E p → k) (F : SubsetIndex E) (h : F.1.card = p) :
    simplexDegreeInclude k E p y F = y ⟨F.1, F.2, h⟩ := by
  exact dif_pos h

theorem simplexDegreeInclude_apply_not_card (E : Finset V) (p : ℕ)
    (y : CechSlot E p → k) (F : SubsetIndex E) (h : F.1.card ≠ p) :
    simplexDegreeInclude k E p y F = 0 := by
  exact dif_neg h

noncomputable def simplexDegreeProject (E : Finset V) (p : ℕ) :
    (SubsetIndex E → k) →ₗ[k] (CechSlot E p → k) where
  toFun y F := y ⟨F.1, F.2.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem simplexDegreeProject_include
    (E : Finset V) (p : ℕ) (y : CechSlot E p → k) :
    simplexDegreeProject k E p (simplexDegreeInclude k E p y) = y := by
  classical
  funext F
  simp [simplexDegreeProject, simplexDegreeInclude, F.2.2]

noncomputable def simplexDegreeBoundary (rank : V ↪ ℕ) (E : Finset V) (p : ℕ) :
    (CechSlot E (p + 1) → k) →ₗ[k] (CechSlot E p → k) :=
  Matrix.mulVecLin (fun F G => cechCoefficient k rank F.1 G.1)

noncomputable def simplexDegreeInsertion (rank : V ↪ ℕ) (E : Finset V) (j : V) (p : ℕ) :
    (CechSlot E p → k) →ₗ[k] (CechSlot E (p + 1) → k) :=
  Matrix.mulVecLin (fun G F => insertionCoefficient k rank j G.1 F.1)

theorem simplexBoundary_degreeInclude
    (rank : V ↪ ℕ) (E : Finset V) (p : ℕ) (y : CechSlot E (p + 1) → k) :
    simplexBoundary k rank E (simplexDegreeInclude k E (p + 1) y) =
      simplexDegreeInclude k E p (simplexDegreeBoundary k rank E p y) := by
  classical
  funext A
  by_cases hA : A.1.card = p
  · change (∑ F : SubsetIndex E, cechCoefficient k rank A.1 F.1 *
      simplexDegreeInclude k E (p + 1) y F) = _
    rw [sum_subset_card k E (p + 1) _ (by
      intro F hF
      rw [simplexDegreeInclude_apply_not_card k E (p + 1) y F hF, mul_zero])]
    rw [simplexDegreeInclude_apply_card k E p _ A hA]
    change (∑ F : CechSlot E (p + 1), _ * _) = ∑ F : CechSlot E (p + 1), _ * _
    apply Finset.sum_congr rfl
    intro F _
    rw [simplexDegreeInclude_apply_card k E (p + 1) y _ F.2.2]
  · change (∑ F : SubsetIndex E, cechCoefficient k rank A.1 F.1 *
      simplexDegreeInclude k E (p + 1) y F) = _
    have hzero : ∀ F : SubsetIndex E,
        cechCoefficient k rank A.1 F.1 * simplexDegreeInclude k E (p + 1) y F = 0 := by
      intro F
      by_cases hF : F.1.card = p + 1
      · have hcard : F.1.card ≠ A.1.card + 1 := by omega
        simp [cechCoefficient, hcard]
      · rw [simplexDegreeInclude_apply_not_card k E (p + 1) y F hF, mul_zero]
    rw [simplexDegreeInclude_apply_not_card k E p _ A hA]
    exact Finset.sum_eq_zero (fun F _ => hzero F)

theorem simplexBoundary_degreeInclude_zero
    (rank : V ↪ ℕ) (E : Finset V) (y : CechSlot E 0 → k) :
    simplexBoundary k rank E (simplexDegreeInclude k E 0 y) = 0 := by
  classical
  funext A
  change (∑ F : SubsetIndex E, cechCoefficient k rank A.1 F.1 *
    simplexDegreeInclude k E 0 y F) = 0
  apply Finset.sum_eq_zero
  intro F _
  by_cases hF : F.1.card = 0
  · have hcard : F.1.card ≠ A.1.card + 1 := by omega
    simp [cechCoefficient, hcard]
  · rw [simplexDegreeInclude_apply_not_card k E 0 y F hF, mul_zero]

theorem simplexInsertion_degreeInclude
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (p : ℕ) (y : CechSlot E p → k) :
    simplexInsertion k rank E j (simplexDegreeInclude k E p y) =
      simplexDegreeInclude k E (p + 1) (simplexDegreeInsertion k rank E j p y) := by
  classical
  funext A
  by_cases hA : A.1.card = p + 1
  · change (∑ F : SubsetIndex E, insertionCoefficient k rank j A.1 F.1 *
      simplexDegreeInclude k E p y F) = _
    rw [sum_subset_card k E p _ (by
      intro F hF
      rw [simplexDegreeInclude_apply_not_card k E p y F hF, mul_zero])]
    rw [simplexDegreeInclude_apply_card k E (p + 1) _ A hA]
    change (∑ F : CechSlot E p, _ * _) = ∑ F : CechSlot E p, _ * _
    apply Finset.sum_congr rfl
    intro F _
    rw [simplexDegreeInclude_apply_card k E p y _ F.2.2]
  · have hzero := simplexInsertion_supported_card k rank E j p
      (simplexDegreeInclude k E p y) (by
        intro F hF
        exact simplexDegreeInclude_apply_not_card k E p y F hF) A hA
    rw [simplexDegreeInclude_apply_not_card k E (p + 1) _ A hA]
    exact hzero

/-- The contraction restricts to the actual consecutive chain degrees. -/
theorem simplexDegreeContraction_identity
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (hj : j ∈ E)
    (p : ℕ) (y : CechSlot E (p + 1) → k) :
    simplexDegreeInsertion k rank E j p (simplexDegreeBoundary k rank E p y) +
      simplexDegreeBoundary k rank E (p + 1) (simplexDegreeInsertion k rank E j (p + 1) y) = y := by
  have h := congrArg (simplexDegreeProject k E (p + 1))
    (simplexContraction_identity k rank E j hj (simplexDegreeInclude k E (p + 1) y))
  simpa only [simplexBoundary_degreeInclude, simplexInsertion_degreeInclude,
    map_add, simplexDegreeProject_include] using h

theorem simplexDegreeContraction_zero
    (rank : V ↪ ℕ) (E : Finset V) (j : V) (hj : j ∈ E) (y : CechSlot E 0 → k) :
    simplexDegreeBoundary k rank E 0 (simplexDegreeInsertion k rank E j 0 y) = y := by
  have h := congrArg (simplexDegreeProject k E 0)
    (simplexContraction_identity k rank E j hj (simplexDegreeInclude k E 0 y))
  simpa only [simplexBoundary_degreeInclude_zero, map_zero, zero_add,
    simplexInsertion_degreeInclude, simplexBoundary_degreeInclude,
    simplexDegreeProject_include] using h



end LPCA


