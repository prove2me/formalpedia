-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
-- name    : LPCA_Solutions_LPCA_AmbientFieldScalars_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:38:38.252173+00:00
-- url     : https://prove2.me/theorems/aa923a18-800c-4d7b-ba17-60b4c788cc3a
-- title:
--   Ambient Field Scalars for localized persistent commutative algebra
-- statement:
--   This bundle supplies ambient Field Scalars for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - Restricting the ambient polynomial scalars to constants recovers the actual native field-module structure used by the homogeneous pieces.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AmbientFieldScalars.lean, selected declarations in lines 17–71; source SHA-256 094e4e8d1c570bf13a588cb75c874dd1d6949b975f18b9e067f7a1361d790dce; source certificate Sapelo2 job 49172236.

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
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
import Definitions.Def_LPCA_Solutions_LPCA_AmbientCechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedGradingSpan_Defs
import Definitions.Def_LPCA_Solutions_LPCA_SignedSubsetMatrices_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

/-- Restricting the ambient polynomial scalars to constants recovers the
actual native field-module structure used by the homogeneous pieces. -/
noncomputable def ambientLocalizationFieldIso (K : Complex V) (F : Finset V) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
        (ambientLocalizedModule k K F) ≅
      ModuleCat.of k (LocalizedFaceRing k K F) := by
  let e : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
      (ambientLocalizedModule k K F) ≃ₗ[k] LocalizedFaceRing k K F := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro c x
      let z : LocalizedFaceRing k K F := x
      change Ideal.Quotient.mk (srIdeal k K) (MvPolynomial.C c) • z = c • z
      have h := OreLocalization.smul_one_smul
        (R := k) (M := FaceRing k K) (S := Submonoid.powers (invertedMonomial k K F)) c z
      rw [← Algebra.algebraMap_eq_smul_one] at h
      exact h }
  exact e.toModuleIso



variable [Fintype V]

noncomputable def ambientCechTermFieldIso (K : Complex V) (T : Finset V) (p : ℕ) :
    (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
        (ModuleCat.of (MvPolynomial V k) (AmbientCechTerm k K T p)) ≅
      ModuleCat.of k (∀ F : CechSlot T p, LocalizedFaceRing k K F.1) := by
  let e : (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
      (ModuleCat.of (MvPolynomial V k) (AmbientCechTerm k K T p)) ≃ₗ[k]
        (∀ F : CechSlot T p, LocalizedFaceRing k K F.1) := {
    toFun := fun y F => y F
    invFun := fun y F => y F
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro c y
      funext F
      exact (ambientLocalizationFieldIso k K F.1).hom.hom.map_smul c
        (show (ModuleCat.restrictScalars (MvPolynomial.C : k →+* MvPolynomial V k)).obj
          (ambientLocalizedModule k K F.1) from y F) }
  exact e.toModuleIso

end LPCA


