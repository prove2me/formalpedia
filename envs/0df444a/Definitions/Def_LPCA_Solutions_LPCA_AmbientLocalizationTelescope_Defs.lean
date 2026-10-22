-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
-- name    : LPCA_Solutions_LPCA_AmbientLocalizationTelescope_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:21:16.518559+00:00
-- url     : https://prove2.me/theorems/2dbc1e9c-7cfa-4cae-9e44-d707b9cd0423
-- title:
--   Ambient Localization Telescope for localized persistent commutative algebra
-- statement:
--   This bundle supplies ambient Localization Telescope for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The coefficient module after canonical scalar restriction is the paper's actual face-ring module over the ambient polynomial ring.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AmbientLocalizationTelescope.lean, selected declarations in lines 16–50; source SHA-256 2625a43493c98e878ec6d7f66b13e22e0bfe7f0c4fbfbab32c5b5cd064c0056f; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationTelescope_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

/-- The coefficient module after canonical scalar restriction is the paper's
actual face-ring module over the ambient polynomial ring. -/
noncomputable def restrictedFaceRingIso (K : Complex V) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))).obj
      (ModuleCat.of (FaceRing k K) (FaceRing k K)) ≅
        ModuleCat.of (MvPolynomial V k) (FaceRing k K) := by
  let e : (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))).obj
      (ModuleCat.of (FaceRing k K) (FaceRing k K)) ≃ₗ[MvPolynomial V k] FaceRing k K := {
    toFun := fun x => x
    invFun := fun x => x
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := by
      intro r x
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      change Ideal.Quotient.mk (srIdeal k K) r * Ideal.Quotient.mk (srIdeal k K) p =
        Ideal.Quotient.mk (srIdeal k K) (r * p)
      exact (map_mul (Ideal.Quotient.mk (srIdeal k K)) r p).symm }
  exact e.toModuleIso

noncomputable def ambientLocalizationTelescope (K : Complex V) (F : Finset V) :
    ℕ ⥤ ModuleCat.{u} (MvPolynomial V k) :=
  localizationTelescope (invertedMonomial k K F) ⋙
    ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))

noncomputable def ambientLocalizationTelescopeCocone (K : Complex V) (F : Finset V) :
    Cocone (ambientLocalizationTelescope k K F) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))).mapCocone
    (localizationTelescopeCocone (invertedMonomial k K F))

noncomputable def ambientLocalizationTelescopeIsColimit (K : Complex V) (F : Finset V) :
    IsColimit (ambientLocalizationTelescopeCocone k K F) :=
  isColimitOfPreserves (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K)))
    (localizationTelescopeIsColimit (invertedMonomial k K F))





end LPCA


