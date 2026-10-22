-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_AmbientLocalizations_Defs
-- name    : LPCA_Solutions_LPCA_AmbientLocalizations_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:19:10.982659+00:00
-- url     : https://prove2.me/theorems/2bd8ee6c-a32d-4bad-a43e-c127766a27a9
-- title:
--   Ambient Localizations for localized persistent commutative algebra
-- statement:
--   This bundle supplies ambient Localizations for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The genuine localization map is linear over the face ring itself.
--   - Keep the actual localization and restrict its face-ring scalars through S -> k[K], without adding a second scalar instance on the raw ring.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_AmbientLocalizations.lean, selected declarations in lines 17–64; source SHA-256 7821f67b4b6d214a9400671c12f1ca519252675799b135536592a35fa7da3579; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace LPCA

open CategoryTheory CategoryTheory.Limits

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

/-- The genuine localization map is linear over the face ring itself. -/
noncomputable def faceLocalizationAlgMap
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) :
    LocalizedFaceRing k K F →ₐ[FaceRing k K] LocalizedFaceRing k K G :=
  { (localizationMap k K F G hFG).toRingHom with
    commutes' := localizationMap_base k K F G hFG }

noncomputable abbrev faceLocalizationModule (K : Complex V) (F : Finset V) : ModuleCat.{u} (FaceRing k K) :=
  ModuleCat.of (FaceRing k K) (LocalizedFaceRing k K F)

/-- Keep the actual localization and restrict its face-ring scalars through
S -> k[K], without adding a second scalar instance on the raw ring. -/
noncomputable def ambientLocalizedModule (K : Complex V) (F : Finset V) :
    ModuleCat.{u} (MvPolynomial V k) :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))).obj (faceLocalizationModule k K F)

noncomputable def ambientLocalizationMap
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) :
    ambientLocalizedModule k K F ⟶ ambientLocalizedModule k K G :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (srIdeal k K))).map
    (ModuleCat.ofHom (faceLocalizationAlgMap k K F G hFG).toLinearMap)







theorem ambientLocalizationMap_comp
    (K : Complex V) (F G H : Finset V) (hFG : F ⊆ G) (hGH : G ⊆ H) :
    ambientLocalizationMap k K F G hFG ≫ ambientLocalizationMap k K G H hGH =
      ambientLocalizationMap k K F H (hFG.trans hGH) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change localizationMap k K G H hGH (localizationMap k K F G hFG x) =
    localizationMap k K F H (hFG.trans hGH) x
  exact congrArg (fun f => f x) (localizationMap_comp k K F G H hFG hGH)



end LPCA


