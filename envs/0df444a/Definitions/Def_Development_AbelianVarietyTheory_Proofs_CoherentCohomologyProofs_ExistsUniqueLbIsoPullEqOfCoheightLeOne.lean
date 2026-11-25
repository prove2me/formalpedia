-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
-- name    : Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:36:33.015811+00:00
-- url     : https://prove2.me/theorems/367165ae-f783-419a-b0cf-b051f1c4b811
-- title:
--   Exists Unique Lb Iso Pull Eq Of Coheight Le One
-- statement:
--   Definitions and structural lemmas for Exists Unique Lb Iso Pull Eq Of Coheight Le One, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsUniqueLbIsoPullEqOfCoheightLeOne.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MemRangeOfForallHeightEqOneOfIsReflexive
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdIso
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_lcg_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace GlobalTheory
section Functions
variable {X Y : Scheme.{u}}
theorem ringKrullDim_stalk_le_one_iff (x : X) :
    ringKrullDim (X.presheaf.stalk x) ≤ 1 ↔ Order.coheight x ≤ 1 := by
  rw [ringKrullDim_stalk_eq_coheight]
  exact_mod_cast Iff.rfl
end Functions
section Charts
open ReciprocityTheory.ChartRestriction.G.Semi
variable {X Y : Scheme.{u}}
theorem res_appLE_apply (f : Y ⟶ X) {V : X.Opens} {W W' : Y.Opens} (e : W ≤ f ⁻¹ᵁ V) (h : W' ≤ W)
    (s : Γ(X, V)) :
    (Y.presheaf.map (homOfLE h).op).hom ((f.appLE V W e).hom s) =
      (f.appLE V W' (h.trans e)).hom s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
theorem appLE_res_apply (f : Y ⟶ X) {V V' : X.Opens} {W : Y.Opens} (h : V' ≤ V)
    (e : W ≤ f ⁻¹ᵁ V') (s : Γ(X, V)) :
    (f.appLE V' W e).hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (f.appLE V W (e.trans (f.preimage_mono h))).hom s := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
theorem lb_pull_U (L : LB X) (f : Y ⟶ X) (j : PUnit.{u + 1} → L.ι) :
    (L.pull f).U j = f ⁻¹ᵁ L.U (j PUnit.unit) :=
  le_antisymm (LB.wchart_le L (K := PUnit) (fun _ ↦ f) j PUnit.unit)
    fun _ hy ↦ Set.mem_iInter.mpr fun _ ↦ hy
theorem lb_pull_g (L : LB X) (f : Y ⟶ X) (i j : PUnit.{u + 1} → L.ι) :
    ((L.pull f).g i j).val =
      (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit)) ((L.pull f).U i ⊓ (L.pull f).U j)
        (inf_le_inf (lb_pull_U L f i).le (lb_pull_U L f j).le)).hom
        (L.g (i PUnit.unit) (j PUnit.unit)).val :=
  congrArg Units.val (LB.lcg_pull L f i j)
noncomputable def lbSecPull (L : LB X) (s : L.Sec) (f : Y ⟶ X) : (L.pull f).Sec where
  f j := (f.appLE (L.U (j PUnit.unit)) ((L.pull f).U j) (lb_pull_U L f j).le).hom
    (s.f (j PUnit.unit))
  compat i j := by
    rw [res_appLE_apply, res_appLE_apply, lb_pull_g L f i j]
    have := congrArg (f.appLE (L.U (i PUnit.unit) ⊓ L.U (j PUnit.unit))
      ((L.pull f).U i ⊓ (L.pull f).U j)
      (inf_le_inf (lb_pull_U L f i).le (lb_pull_U L f j).le)).hom
      (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at this
    exact (appLE_res_apply f _ _ _).symm.trans
      (this.trans (congrArg (_ * ·) (appLE_res_apply f _ _ _)))
noncomputable abbrev lbIsoPull {L M : LB X} (w : LB.Iso L M) (f : Y ⟶ X) :
    LB.Iso (L.pull f) (M.pull f) :=
  LB.linCombIso w (K := PUnit) (fun _ ↦ f) (fun _ ↦ 1)
theorem lb_div_pull_U (L M : LB X) (f : Y ⟶ X)
    (p : (PUnit.{u + 1} → M.ι) × (PUnit.{u + 1} → L.ι)) :
    ((M.pull f).div (L.pull f)).U p = f ⁻¹ᵁ (M.div L).U (p.1 PUnit.unit, p.2 PUnit.unit) :=
  congrArg₂ (· ⊓ ·) (lb_pull_U M f p.1) (lb_pull_U L f p.2)
end Charts
section SectionsOnOpens
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y : Scheme.{0}}
section Integral
variable [IsIntegral X]
variable [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X]
end Integral
theorem lb_pull_ι_U (L : LB X) (W : X.Opens) (j : PUnit.{1} → L.ι) :
    (L.pull W.ι).U j = W.ι ⁻¹ᵁ (W ⊓ L.U (j PUnit.unit)) :=
  (lb_pull_U L W.ι j).trans (le_antisymm (fun y hy ↦ ⟨y.2, hy⟩) fun _ hy ↦ hy.2)
end SectionsOnOpens
section Main
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
example : ∃ (X : Scheme.{0}) (_ : IsIntegral X) (_ : IsLocallyNoetherian X)
    (_ : Geo.Tor.IsNormalScheme X) (U : X.Opens), U ≠ ⊤ ∧
      ∀ x : X, ringKrullDim (X.presheaf.stalk x) ≤ 1 → x ∈ U := by
  obtain ⟨m, hm, h1⟩ : ∃ m : Ideal (Polynomial ℤ), m.IsMaximal ∧ ¬ m.height ≤ 1 := by
    by_contra! H
    have h := (ringKrullDim_le_iff_isMaximal_height_le (R := Polynomial ℤ) 1).mpr
      fun m hm ↦ by exact_mod_cast H m hm
    rw [Polynomial.ringKrullDim_of_isNoetherianRing,
      IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at h
    exact absurd h (by decide)
  let x : Spec (.of (Polynomial ℤ)) := ⟨m, hm.isPrime⟩
  have hc : IsClosed {x} := (PrimeSpectrum.isClosed_singleton_iff_isMaximal x).mpr hm
  refine ⟨Spec (.of (Polynomial ℤ)), inferInstance, inferInstance, GlobalTheory.IsNormalScheme.pred _,
    ⟨{x}ᶜ, hc.isOpen_compl⟩, fun h ↦ ?_, fun y hy hyx ↦ h1 ?_⟩
  · have : x ∈ (⟨{x}ᶜ, hc.isOpen_compl⟩ : (Spec (.of (Polynomial ℤ))).Opens) := h ▸ trivial
    exact this rfl
  · rw [show y = x from hyx, ringKrullDim_stalk_le_one_iff, ← idealHeight_eq_coheight] at hy
    exact hy
end Main
end GlobalTheory


