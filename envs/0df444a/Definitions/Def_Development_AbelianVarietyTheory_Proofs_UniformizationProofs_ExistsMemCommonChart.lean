-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMemCommonChart
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsMemCommonChart
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-25T15:52:15.712159+00:00
-- url     : https://prove2.me/theorems/23805940-9ea0-479c-8869-a5aec9dcb47b
-- title:
--   Exists Mem Common Chart
-- statement:
--   Definitions and structural lemmas for Exists Mem Common Chart, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsMemCommonChart.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Theorems.Thm_GlobalTheory_UU_IsWt_add
import Theorems.Thm_GlobalTheory_UU_IsWt_inv
import Theorems.Thm_GlobalTheory_UU_IsWt_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.UU
variable {S : Scheme.{0}}
theorem isWt_of_gm {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G} {V : G.left.Opens}
    (u : Γ(G.left, V)ˣ) (χ : X)
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), g.left z ∈ V →
      gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u) :
    IsWt i V u.val χ := by
  intro Z t g h₁ h₂
  apply TopCat.Presheaf.section_ext Z.left.sheaf ⊤
  intro z hz
  have hg : g.left z ∈ V := h₂ trivial
  have hf : ((t ≫ i) * g).left z ∈ V := h₁ trivial
  have ht : t.left z ∈ (⊤ : (splitTorus S X).left.Opens) := trivial
  have key := congrArg Units.val (h Z t g z hg)
  simp only [gm, dif_pos hg, dif_pos hf, dif_pos ht, pullU, MonoidHom.comp_apply, Units.coe_map,
    Units.val_mul] at key
  change Z.left.presheaf.germ ⊤ z hz _ = Z.left.presheaf.germ ⊤ z hz _
  simp only [Scheme.Hom.appLE, CommRingCat.comp_apply, map_mul, TopCat.Presheaf.germ_res_apply]
  exact key
attribute [local instance] SplitExt.free SplitExt.finite
variable {E : SplitExt S} {G : Over S} [GrpObj G]
theorem exists_mem_commonChart (E : SplitExt S) (x : E.B.left) : ∃ j, x ∈ E.chart j := by
  have hk : ∀ k, ∃ a, x ∈ (E.O (E.basis k)).L.U a := by
    intro k
    have hx : x ∈ (⊤ : E.B.left.Opens) := trivial
    rw [← (E.O (E.basis k)).isLB.cover] at hx
    simpa [TopologicalSpace.Opens.mem_iSup] using hx
  choose c hc using hk
  refine ⟨c, ?_⟩
  unfold SplitExt.chart
  rw [← SetLike.mem_coe, TopologicalSpace.Opens.coe_iInf]
  exact Set.mem_iInter.2 hc
theorem gm_res_pullU_eq_gm_comp {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {W : P.Opens}
    (h : W ≤ a ⁻¹ᵁ U) {z : Z} (hz : p z ∈ W) (w : Γ(Y, U)ˣ) :
    gm p z W (res h (pullU a U w)) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := h hz
  ext
  simp only [gm, dif_pos hz, dif_pos hz', pullU, res, MonoidHom.comp_apply, Units.coe_map]
  erw [← Scheme.Hom.germ_stalkMap_apply p W z hz, TopCat.Presheaf.germ_res_apply,
    Scheme.Hom.germ_stalkMap_apply]
  rfl
theorem gm_id_pullU_eq_gm {Z P Y : Scheme.{0}} (p : Z ⟶ P) (a : P ⟶ Y) {U : Y.Opens} {z : Z}
    (hz : p z ∈ a ⁻¹ᵁ U) (w : Γ(Y, U)ˣ) :
    gm p z (a ⁻¹ᵁ U) (pullU a U w) = gm (p ≫ a) z U w := by
  have hz' : (p ≫ a) z ∈ U := hz
  ext
  simp only [gm, dif_pos hz, dif_pos hz', pullU, MonoidHom.comp_apply, Units.coe_map]
  rfl
theorem isWt_coordinate (d : E.GtDatum G) (j : E.ChartIdx) (k : Module.Free.ChooseBasisIndex ℤ E.X) :
    IsWt d.i _ (d.u j k).val (E.basis k) := by
  refine isWt_of_gm (d.u j k) (E.basis k) ?_
  intro Z t g z hz
  have hf : (t ≫ d.i) * g = lift t g ≫ (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ) := by
    show lift (t ≫ d.i) g ≫ μ = _
    rw [← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
  have hp : (lift t g).left z ∈ (snd (splitTorus S E.X) G).left ⁻¹ᵁ (d.q.left ⁻¹ᵁ E.chart j) := by
    have e : ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) = g.left := by
      rw [← Over.comp_left, lift_snd]
    show ((lift t g).left ≫ (snd (splitTorus S E.X) G).left) z ∈ d.q.left ⁻¹ᵁ E.chart j
    rw [e]
    exact hz
  have key := congrArg (gm (lift t g).left z _) (d.equiv j k)
  rw [map_mul] at key
  rw [gm_res_pullU_eq_gm_comp (a := (lift (fst (splitTorus S E.X) G ≫ d.i) (snd (splitTorus S E.X) G) ≫ μ).left) _ _ hp,
    gm_id_pullU_eq_gm (a := (snd (splitTorus S E.X) G).left) _ hp] at key
  rw [← Over.comp_left, ← Over.comp_left, lift_snd, ← hf] at key
  rw [key]
  congr 1
  erw [gm_res_pullU_eq_gm_comp (a := (fst (splitTorus S E.X) G).left) _ _ hp]
  rw [← Over.comp_left, lift_fst]
theorem exists_unit_isWt (d : E.GtDatum G) (j : E.ChartIdx) (χ : E.X) :
    ∃ u : Γ(G.left, d.q.left ⁻¹ᵁ E.chart j)ˣ, IsWt d.i _ u.val χ := by
  have hχ : χ ∈ AddSubgroup.closure (Set.range E.basis) := by
    rw [← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup, E.basis.span_eq]
    exact Submodule.mem_top
  induction hχ using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, rfl⟩ := hx
    exact ⟨d.u j k, isWt_coordinate d j k⟩
  | zero => exact ⟨1, by simpa using (isWt_one : IsWt d.i (d.q.left ⁻¹ᵁ E.chart j) 1 0)⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨a * b, by simpa using ha.mul hb⟩
  | neg x _ hx =>
    obtain ⟨a, ha⟩ := hx
    exact ⟨a⁻¹, ha.inv⟩
def TQ.ofGtDatum (d : E.GtDatum G) : TQ G E.X where
  B := E.B
  comm := E.isAbelian.comm
  isAb := E.isAbelian
  q := d.q
  i := d.i
  q_hom := d.q_hom
  i_hom := d.i_hom
  q_flat := d.q_flat
  q_surj := d.q_surjective
  q_affine := d.q_affine
  isKernel := d.isKernel
  loc b χ := by
    obtain ⟨j, hj⟩ := exists_mem_commonChart E b
    exact ⟨E.chart j, hj, exists_unit_isWt d j χ⟩
end GlobalTheory.UU
end


