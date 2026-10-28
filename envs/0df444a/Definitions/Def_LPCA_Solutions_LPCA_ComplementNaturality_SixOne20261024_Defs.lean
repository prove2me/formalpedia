-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:06:03.013888+00:00
-- url     : https://prove2.me/theorems/96c20364-5e80-4e87-83f6-2db134fc371b
-- title:
--   Complement Naturality — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for complement naturality used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   The complement equivalences commute with the genuine localization maps.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ComplementNaturality.lean, selected declarations in lines 15–104; source SHA-256 c9c4c79611a22e002fdc7aef3629ce4b7f3f295e153b182efe770c054a0350f7; exact-source certificate Sapelo2 job 49296539.

import Mathlib.Algebra.Homology.LocalCohomology
import Mathlib.Algebra.MvPolynomial.Division
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Tactic
import Definitions.Def_LPCA
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementRings_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_GradedLocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationConsequences_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizationMaps_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedBasis_Defs
import Definitions.Def_LPCA_Solutions_LPCA_LocalizedDimension_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VariableMultiplication_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_VertexSplitting_Defs

set_option autoImplicit false

namespace LPCA

open scoped Classical

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W]
variable (k : Type u) [Field k]

/-- The complement equivalences commute with the genuine localization maps. -/
theorem localizedRestriction_localization
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F G : Finset W) (hFG : F ⊆ G)
    (z : LocalizedFaceRing k (restrictComplex K e) F) :
    localizedRestrictionRingEquiv k K e hK G
        (localizationMap k (restrictComplex K e) F G hFG z) =
      localizationMap k K (F.map e) (G.map e) (Finset.map_subset_map.mpr hFG)
        (localizedRestrictionRingEquiv k K e hK F z) := by
  have hhom :
      (localizedRestrictionRingEquiv k K e hK G).toRingHom.comp
          (localizationMap k (restrictComplex K e) F G hFG).toRingHom =
        (localizationMap k K (F.map e) (G.map e)
          (Finset.map_subset_map.mpr hFG)).toRingHom.comp
            (localizedRestrictionRingEquiv k K e hK F).toRingHom := by
    apply IsLocalization.ringHom_ext
      (Submonoid.powers (invertedMonomial k (restrictComplex K e) F))
    apply RingHom.ext
    intro r
    change localizedRestrictionRingEquiv k K e hK G
      (localizationMap k (restrictComplex K e) F G hFG
        (algebraMap (FaceRing k (restrictComplex K e))
          (LocalizedFaceRing k (restrictComplex K e) F) r)) =
      localizationMap k K (F.map e) (G.map e) (Finset.map_subset_map.mpr hFG)
        (localizedRestrictionRingEquiv k K e hK F
          (algebraMap (FaceRing k (restrictComplex K e))
            (LocalizedFaceRing k (restrictComplex K e) F) r))
    rw [localizationMap_base, localizedRestrictionRingEquiv_base,
      localizedRestrictionRingEquiv_base, localizationMap_base]
  exact RingHom.congr_fun hhom z

variable [Fintype V] [Fintype W]

theorem localizedPieceRestriction_localization
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F G : Finset W) (hFG : F ⊆ G) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (z : localizedPiece k (restrictComplex K e) F (a ∘ e)) :
    localizedPieceRestrictionEquiv k K e hK G a ha
        (localizedPieceMap k (restrictComplex K e) F G hFG (a ∘ e) z) =
      localizedPieceMap k K (F.map e) (G.map e) (Finset.map_subset_map.mpr hFG) a
        (localizedPieceRestrictionEquiv k K e hK F a ha z) := by
  apply Subtype.ext
  exact localizedRestriction_localization k K e hK F G hFG z.1

omit [Fintype V] [Fintype W] in
theorem localizedRestriction_variable
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F : Finset W) (j : W)
    (z : LocalizedFaceRing k (restrictComplex K e) F) :
    localizedRestrictionRingEquiv k K e hK F
        (localizedVariableLinearMap k (restrictComplex K e) F j z) =
      localizedVariableLinearMap k K (F.map e) (e j)
        (localizedRestrictionRingEquiv k K e hK F z) := by
  change localizedRestrictionRingEquiv k K e hK F
      (algebraMap (FaceRing k (restrictComplex K e))
        (LocalizedFaceRing k (restrictComplex K e) F)
          (variableClass k (restrictComplex K e) j) * z) = _
  rw [map_mul, localizedRestrictionRingEquiv_base]
  change algebraMap (FaceRing k K) (LocalizedFaceRing k K (F.map e))
      (faceRingRename k K e (variableClass k (restrictComplex K e) j)) * _ = _
  rw [faceRingRename_variable]
  rfl

omit [Fintype V] [Fintype W] in
theorem increment_restrict
    (e : W ↪ V) (a b : V → ℤ) (j : W)
    (hab : ∀ v, b v = a v + if v = e j then 1 else 0) :
    ∀ w, (b ∘ e) w = (a ∘ e) w + if w = j then 1 else 0 := by
  intro w
  simpa only [Function.comp_apply, e.injective.eq_iff] using hab (e w)

theorem localizedPieceRestriction_variable
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (F : Finset W) (a b : V → ℤ) (j : W)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (hb : ∀ v, v ∉ Set.range e → b v = 0)
    (hab : ∀ v, b v = a v + if v = e j then 1 else 0)
    (z : localizedPiece k (restrictComplex K e) F (a ∘ e)) :
    localizedPieceRestrictionEquiv k K e hK F b hb
        (pieceVariableMap k (restrictComplex K e) F (a ∘ e) (b ∘ e) j
          (increment_restrict e a b j hab) z) =
      pieceVariableMap k K (F.map e) a b (e j) hab
        (localizedPieceRestrictionEquiv k K e hK F a ha z) := by
  apply Subtype.ext
  exact localizedRestriction_variable k K e hK F j z.1

end LPCA


