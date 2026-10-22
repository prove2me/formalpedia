-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
-- name    : LPCA_Solutions_LPCA_LocalizationMaps_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-21T21:18:46.316542+00:00
-- url     : https://prove2.me/theorems/e07dd657-1af0-4c76-8643-7c6c4864a5b9
-- title:
--   Localization Maps for localized persistent commutative algebra
-- statement:
--   This bundle supplies localization Maps for localized persistent commutative algebra. The bundle contains the selected declarations used by this attachment checkpoint, with the hypotheses of their Lean statements retained. Its role as a dependency does not assert a stronger comparison, scalar compatibility or persistence theorem than those declarations state.
--
--   The included constructions and necessary compatibility results are:
--
--   - The genuine map of localizations obtained by inverting additional variables.
-- source:
--   https://arxiv.org/abs/2609.02858v1, formalization dependencies for Sections 2–4. Certified Lean source: Solutions/LPCA_LocalizationMaps.lean, selected declarations in lines 13–61; source SHA-256 fc1ef1bcad69882383c887ee2252f24da0957d6c284daf71c661360a2b39cb4e; source certificate Sapelo2 job 49172236.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA

set_option autoImplicit false

namespace LPCA

universe u

variable {V : Type u} [DecidableEq V]
variable (k : Type u) [Field k]

theorem invertedMonomial_dvd
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) :
    invertedMonomial k K F ∣ invertedMonomial k K G :=
  Finset.prod_dvd_prod_of_subset F G (variableClass k K) hFG

/-- The genuine map of localizations obtained by inverting additional variables. -/
noncomputable def localizationMap
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) :
    LocalizedFaceRing k K F →ₐ[k] LocalizedFaceRing k K G := by
  have hunit : IsUnit (algebraMap (FaceRing k K) (LocalizedFaceRing k K G)
      (invertedMonomial k K F)) :=
    IsLocalization.Away.isUnit_of_dvd (S := LocalizedFaceRing k K G)
      (invertedMonomial k K G) (invertedMonomial_dvd k K F G hFG)
  refine { IsLocalization.Away.lift (invertedMonomial k K F) hunit with
    commutes' := ?_ }
  intro c
  change IsLocalization.Away.lift (invertedMonomial k K F) hunit
    (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) (algebraMap k (FaceRing k K) c)) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K G) (algebraMap k (FaceRing k K) c)
  exact IsLocalization.Away.lift_eq _ _ _

theorem localizationMap_base
    (K : Complex V) (F G : Finset V) (hFG : F ⊆ G) (r : FaceRing k K) :
    localizationMap k K F G hFG (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) r) =
      algebraMap (FaceRing k K) (LocalizedFaceRing k K G) r := by
  simp [localizationMap, IsLocalization.Away.lift_eq]



theorem localizationMap_comp
    (K : Complex V) (F G H : Finset V) (hFG : F ⊆ G) (hGH : G ⊆ H) :
    (localizationMap k K G H hGH).comp (localizationMap k K F G hFG) =
      localizationMap k K F H (hFG.trans hGH) := by
  apply AlgHom.coe_ringHom_injective
  apply IsLocalization.ringHom_ext (Submonoid.powers (invertedMonomial k K F))
  apply RingHom.ext
  intro r
  change localizationMap k K G H hGH
    (localizationMap k K F G hFG
      (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) r)) =
    localizationMap k K F H (hFG.trans hGH)
      (algebraMap (FaceRing k K) (LocalizedFaceRing k K F) r)
  rw [localizationMap_base, localizationMap_base, localizationMap_base]

end LPCA


