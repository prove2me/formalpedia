-- Prove2me | Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
-- name    : LPCA_Solutions_LPCA_ComplementCech_SixOne20261024_Defs
-- status  : Definition
-- author  : @kaiyue
-- created : 2026-10-24T20:09:11.513182+00:00
-- url     : https://prove2.me/theorems/b11b3b8b-b810-454e-8636-c0905d162801
-- title:
--   Complement Čech — coordinate chain dependencies
-- statement:
--   This bundle supplies the selected constructions and proved compatibility results for complement čech used in the coordinate Čech chain comparison. Each construction retains the rings, categories, grading indices and hypotheses in its formal declaration.
--
--   Remove the ghost coordinates in each actual localized homogeneous summand.
--
--   The localization indices are unchanged when all selected variables are renamed.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Section 6, Theorem 6.1 and its formalization dependencies. Certified Lean source: Solutions/LPCA_ComplementCech.lean, selected declarations in lines 17–148; source SHA-256 71b4e6c36bfcac1dca091090148b51fefeda8a2fedeb388ba3d755011e4edead; exact-source certificate Sapelo2 job 49296539.

import Mathlib
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
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
import Definitions.Def_LPCA_Solutions_LPCA_CechComplex_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechDifferential_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechSquareZero_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechTerms_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableMaps_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_Defs
import Definitions.Def_LPCA_Solutions_LPCA_CechVariableNaturality_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementCech_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementLocalizations_SixOne20261024_Defs
import Definitions.Def_LPCA_Solutions_LPCA_ComplementNaturality_SixOne20261024_Defs
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

open CategoryTheory CategoryTheory.Limits

universe u

variable {V W : Type u} [DecidableEq V] [DecidableEq W] [Fintype V] [Fintype W]
variable (k : Type u) [Field k]

attribute [local instance 2000] localizedTermAddCommGroup localizedTermModule

/-- The localization indices are unchanged when all selected variables are renamed. -/
noncomputable abbrev restrictionCechSlotEquiv (e : W ↪ V) (T : Finset W) (p : ℕ) :
    CechSlot T p ≃ CechSlot (T.map e) p :=
  { Equiv.ofBijective
    (fun F : CechSlot T p =>
      (⟨F.1.map e, Finset.map_subset_map.mpr F.2.1,
        by simpa only [Finset.card_map] using F.2.2⟩ : CechSlot (T.map e) p)) (by
    constructor
    · intro F G h
      apply Subtype.ext
      exact Finset.map_injective e (congrArg Subtype.val h)
    · intro G
      let F := G.1.preimage e e.injective.injOn
      have hmap : F.map e = G.1 := by
        ext v
        constructor
        · intro hv
          obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hv
          exact Finset.mem_preimage.mp hw
        · intro hv
          obtain ⟨w, _, rfl⟩ := Finset.mem_map.mp (G.2.1 hv)
          exact Finset.mem_map.mpr ⟨w, Finset.mem_preimage.mpr hv, rfl⟩
      have hFT : F ⊆ T := by
        apply Finset.map_subset_map.mp
        rw [hmap]
        exact G.2.1
      have hcard : F.card = p := by
        rw [← Finset.card_map e, hmap]
        exact G.2.2
      exact ⟨⟨F, hFT, hcard⟩, Subtype.ext hmap⟩) with
    toFun := fun F => ⟨F.1.map e, Finset.map_subset_map.mpr F.2.1,
      by simpa only [Finset.card_map] using F.2.2⟩ }



/-- Remove the ghost coordinates in each actual localized homogeneous summand. -/
noncomputable def restrictionActualTermEquiv
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a : V → ℤ) (p : ℕ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0) :
    LocalizedCechTerm k K (T.map e) a p ≃ₗ[k]
      LocalizedCechTerm k (restrictComplex K e) T (a ∘ e) p :=
  { (Equiv.piCongrLeft
      (fun G : CechSlot (T.map e) p => ↥(localizedPiece k K G.1 a))
      (restrictionCechSlotEquiv e T p)).symm.trans
        (Equiv.piCongrRight (fun F : CechSlot T p =>
          (localizedPieceRestrictionEquiv k K e hK F.1 a ha).symm.toEquiv)) with
    map_add' := fun x y => by
      funext F
      exact map_add (localizedPieceRestrictionEquiv k K e hK F.1 a ha).symm _ _
    map_smul' := fun c y => by
      funext F
      exact map_smul (localizedPieceRestrictionEquiv k K e hK F.1 a ha).symm c _ }

@[simp] theorem restrictionActualTermEquiv_apply
    (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a : V → ℤ) (p : ℕ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (y : LocalizedCechTerm k K (T.map e) a p) (F : CechSlot T p) :
    restrictionActualTermEquiv k K e hK T a p ha y F =
      (localizedPieceRestrictionEquiv k K e hK F.1 a ha).symm
        (y (restrictionCechSlotEquiv e T p F)) := rfl



theorem restrictionActualTermEquiv_differential
    (rank : V ↪ ℕ) (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a : V → ℤ) (p : ℕ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0)
    (y : LocalizedCechTerm k K (T.map e) a p) :
    restrictionActualTermEquiv k K e hK T a (p + 1) ha
        (actualDifferential k (cechCoefficient k rank) K (T.map e) a p y) =
      actualDifferential k (cechCoefficient k (e.trans rank))
        (restrictComplex K e) T (a ∘ e) p
          (restrictionActualTermEquiv k K e hK T a p ha y) := by
  classical
  funext G
  rw [restrictionActualTermEquiv_apply]
  apply (localizedPieceRestrictionEquiv k K e hK G.1 a ha).injective
  rw [LinearEquiv.apply_symm_apply]
  rw [actualDifferential_apply_full, actualDifferential_apply_full, map_sum]
  rw [← (restrictionCechSlotEquiv e T p).sum_comp]
  apply Finset.sum_congr rfl
  intro F _
  change (if hFG : F.1.map e ⊆ G.1.map e then
      cechCoefficient k rank (F.1.map e) (G.1.map e) •
        localizedPieceMap k K (F.1.map e) (G.1.map e) hFG a
          (y (restrictionCechSlotEquiv e T p F)) else 0) = _
  by_cases hFG : F.1 ⊆ G.1
  · have hmap : F.1.map e ⊆ G.1.map e := Finset.map_subset_map.mpr hFG
    simp only [dif_pos hFG, dif_pos hmap, map_smul, cechCoefficient_map]
    congr 1
    rw [localizedPieceRestriction_localization, restrictionActualTermEquiv_apply,
      LinearEquiv.apply_symm_apply]
  · have hmap : ¬ F.1.map e ⊆ G.1.map e := fun h => hFG (Finset.map_subset_map.mp h)
    simp only [dif_neg hFG, dif_neg hmap, map_zero]

noncomputable def restrictionCechComplexIso
    (rank : V ↪ ℕ) (K : Complex V) (e : W ↪ V)
    (hK : ∀ F ∈ K.faces, ∀ v ∈ F, v ∈ Set.range e)
    (T : Finset W) (a : V → ℤ)
    (ha : ∀ v, v ∉ Set.range e → a v = 0) :
    localizedCechComplex k rank K (T.map e) a ≅
      localizedCechComplex k (e.trans rank) (restrictComplex K e) T (a ∘ e) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun p => (restrictionActualTermEquiv k K e hK T a p ha).toModuleIso) ?_
  intro p q hpq
  change p + 1 = q at hpq
  subst q
  rw [localizedCechComplex_d, localizedCechComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro y
  exact (restrictionActualTermEquiv_differential k rank K e hK T a p ha y).symm



end LPCA


