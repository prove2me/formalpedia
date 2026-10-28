-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_FaceRestrictionLocalizations_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T21:13:52.784357+00:00
-- url     : https://prove2.me/theorems/01f63744-7a6d-46e2-8810-a152b10a501d
-- title:
--   Face Restriction Localizations — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for face restriction localizations used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_FaceRestrictionLocalizations.lean, selected declarations in lines 75–102; source SHA-256 821e5eab374035dcec45bffb76850500e26b5c42bd2c5c4ead68bdd1f8f4a0fa; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FaceRestrictionLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_FiltrationFunctor_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

namespace LPCA

open CategoryTheory

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]













theorem localizedFaceRestriction_refl (K : Complex V) (F : Finset V) :
    localizedFaceRestriction k (Finset.Subset.refl K.faces) F =
      AlgHom.id k (LocalizedFaceRing k K F) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (invertedMonomial k K F))
  apply RingHom.ext
  intro r
  change localizedFaceRestriction k (Finset.Subset.refl K.faces) F
    (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) r) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K F) r
  rw [localizedFaceRestriction_base, faceRingRestriction_refl]
  rfl

theorem localizedFaceRestriction_comp {K L M : Complex V}
    (hKL : K.faces ⊆ L.faces) (hLM : L.faces ⊆ M.faces) (F : Finset V) :
    (localizedFaceRestriction k hKL F).comp (localizedFaceRestriction k hLM F) =
      localizedFaceRestriction k (hKL.trans hLM) F := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (invertedMonomial k M F))
  apply RingHom.ext
  intro r
  change localizedFaceRestriction k hKL F
      (localizedFaceRestriction k hLM F
        (algebraMap (FaceRing k M) (LocalizedFaceRing k M F) r)) = _
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    localizedFaceRestriction_base]
  exact congrArg (algebraMap (FaceRing k K) (LocalizedFaceRing k K F))
    (congrArg (fun g => g r) (faceRingRestriction_comp k hKL hLM))















end LPCA


