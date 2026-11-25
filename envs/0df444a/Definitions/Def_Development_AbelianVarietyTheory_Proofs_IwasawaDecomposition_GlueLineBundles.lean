-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
-- name    : Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_GlueLineBundles
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T13:59:22.353984+00:00
-- url     : https://prove2.me/theorems/6f8d27b3-bb78-570a-aab5-e9a36a097b42
-- title:
--   Glue Line Bundles
-- statement:
--   Definitions and structural lemmas for Glue Line Bundles, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/GlueLineBundles.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLineBundleExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mem_pull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
namespace GlobalTheory.GlueLineBundle
variable {X W : Scheme.{0}}
def imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) : Γ(W, V)ˣ →* Γ(X, j ''ᵁ V)ˣ :=
  Units.map (j.appIso V).inv.hom
theorem res_pull_imU (j : W ⟶ X) [IsOpenImmersion j] (V : W.Opens) (v : Γ(W, V)ˣ) :
    res (j.preimage_image_eq V).ge (pullU j _ (imU j V v)) = v := by
  apply Units.ext
  have h := congrArg (fun q => q.hom v.val) (j.appIso_inv_appLE (U := V) (V := V) (j.preimage_image_eq V).ge)
  have e : (homOfLE (le_refl V)) = 𝟙 V := rfl
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h
  refine h.trans ?_
  show (W.presheaf.map (𝟙 (Opposite.op V))).hom v.val = v.val
  rw [W.presheaf.map_id]; rfl
theorem gm_imU (j : W ⟶ X) [IsOpenImmersion j] {Y : Scheme.{0}} (f : Y ⟶ W) (y : Y) (V : W.Opens)
    (hy : f y ∈ V) (v : Γ(W, V)ˣ) : gm (f ≫ j) y (j ''ᵁ V) (imU j V v) = gm f y V v := by
  have h1 : j (f y) ∈ j ''ᵁ V := j.apply_mem_image_iff.2 hy
  rw [← gm_pull f j y _ h1, ← gm_res f y (j.preimage_image_eq V).ge hy, res_pull_imU]
end GlobalTheory.GlueLineBundle
namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}}
end GlobalTheory.GlueLineBundle
namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} (V : A → X.Opens) (M : ∀ a, LB (V a).toScheme)
abbrev NU (p : Σ a, (M a).ι) : X.Opens := (V p.1).ι ''ᵁ (M p.1).U p.2
def GSpec (p q : Σ a, (M a).ι) (u : Γ(X, NU V M p ⊓ NU V M q)ˣ) : Prop :=
  ∀ (c : A) (Y : Scheme.{0}) (f : Y ⟶ (V c).toScheme) (y : Y) (j l : (M c).ι),
    (⟨c, j⟩ : Σ a, (M a).ι) = p → (⟨c, l⟩ : Σ a, (M a).ι) = q → f y ∈ (M c).U j → f y ∈ (M c).U l →
    gm (f ≫ (V c).ι) y (NU V M p ⊓ NU V M q) u = gm f y ((M c).U j ⊓ (M c).U l) ((M c).g j l)
theorem exists_gSpec (p q : Σ a, (M a).ι) : ∃ u, GSpec V M p q u := by
  obtain ⟨a, i⟩ := p
  obtain ⟨b, k⟩ := q
  by_cases hab : a = b
  · subst hab
    have hle : (V a).ι ''ᵁ (M a).U i ⊓ (V a).ι ''ᵁ (M a).U k ≤ (V a).ι ''ᵁ ((M a).U i ⊓ (M a).U k) :=
      fun x hx => by
        obtain ⟨w, hw, rfl⟩ := hx.1
        exact (V a).ι.apply_mem_image_iff.2 ⟨hw, (V a).ι.apply_mem_image_iff.1 hx.2⟩
    refine ⟨res hle (imU (V a).ι _ ((M a).g i k)), ?_⟩
    intro c Y f y j l h1 h2 hj hl
    obtain ⟨rfl, h1'⟩ := Sigma.mk.inj_iff.1 h1
    obtain rfl := eq_of_heq h1'
    obtain rfl := eq_of_heq (Sigma.mk.inj_iff.1 h2).2
    have hm : (f ≫ (V c).ι) y ∈ (V c).ι ''ᵁ (M c).U j ⊓ (V c).ι ''ᵁ (M c).U l :=
      ⟨(V c).ι.apply_mem_image_iff.2 hj, (V c).ι.apply_mem_image_iff.2 hl⟩
    exact (gm_res (f ≫ (V c).ι) y hle hm _).trans (gm_imU (V c).ι f y ((M c).U j ⊓ (M c).U l) ⟨hj, hl⟩ _)
  · refine ⟨1, ?_⟩
    intro c Y f y j l h1 h2
    exact absurd ((Sigma.mk.inj_iff.1 h1).1.symm.trans (Sigma.mk.inj_iff.1 h2).1) hab
def glue : LB X where
  ι := Σ a, (M a).ι
  U := NU V M
  g p q := Classical.choose (exists_gSpec V M p q)
variable {V M}
end GlobalTheory.GlueLineBundle
namespace GlobalTheory.GlueLineBundle
variable {X : Scheme.{0}} {A : Type} {V : A → X.Opens} {M : ∀ a, LB (V a).toScheme}
theorem exists_isoUnit (a : A) (J : PUnit → (glue V M).ι) (k : (M a).ι) :
    ∃ u : Γ((V a).toScheme, ((glue V M).pull (V a).ι).U J ⊓ (M a).U k)ˣ,
      ∀ (Y : Scheme.{0}) (f : Y ⟶ (V a).toScheme) (y : Y) (i : (M a).ι),
        J PUnit.unit = (⟨a, i⟩ : Σ a, (M a).ι) → f y ∈ (M a).U i → f y ∈ (M a).U k →
        gm f y _ u = gm f y ((M a).U i ⊓ (M a).U k) ((M a).g i k) := by
  by_cases h : ∃ i' : (M a).ι, J PUnit.unit = (⟨a, i'⟩ : Σ a, (M a).ι)
  · obtain ⟨i', hi'⟩ := h
    have hle : ((glue V M).pull (V a).ι).U J ⊓ (M a).U k ≤ (M a).U i' ⊓ (M a).U k := fun w hw => by
      have h1 : (V a).ι w ∈ (glue V M).U (J PUnit.unit) := mem_pull.1 hw.1
      rw [hi'] at h1
      exact ⟨(V a).ι.apply_mem_image_iff.1 h1, hw.2⟩
    refine ⟨res hle ((M a).g i' k), fun Y f y i hJ hi hk => ?_⟩
    obtain rfl := sigma_mk_injective (hi'.symm.trans hJ)
    have hm : f y ∈ ((glue V M).pull (V a).ι).U J ⊓ (M a).U k := by
      refine ⟨mem_pull.2 ?_, hk⟩
      show (V a).ι (f y) ∈ (glue V M).U (J PUnit.unit)
      rw [hi']
      exact (V a).ι.apply_mem_image_iff.2 hi
    exact gm_res f y hle hm _
  · exact ⟨1, fun Y f y i hJ => absurd ⟨i, hJ⟩ h⟩
def isoGen (a : A) : LB.Iso (M a) ((glue V M).pull (V a).ι) :=
  ⟨fun p => Classical.choose (exists_isoUnit a p.1 p.2)⟩
end GlobalTheory.GlueLineBundle


