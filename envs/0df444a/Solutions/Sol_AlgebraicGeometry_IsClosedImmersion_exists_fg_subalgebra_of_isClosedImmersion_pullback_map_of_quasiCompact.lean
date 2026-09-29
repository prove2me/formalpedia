-- Prove2me | solution 1 for AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/f150ce52-e8ab-59fa-9a13-cde1de6c1f43

import Mathlib
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace ClosedImmQc18

variable {W V V' S B : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ S) (ι : V' ⟶ V) (b : B ⟶ S)

theorem isPullback_fst_of_comm
    (μ : pullback (m ≫ v) b ⟶ pullback v b) (hμ₁ : μ ≫ pullback.fst v b = pullback.fst (m ≫ v) b ≫ m)
    (hμ₂ : μ ≫ pullback.snd v b = pullback.snd (m ≫ v) b) :
    IsPullback μ (pullback.fst (m ≫ v) b) (pullback.fst v b) m := by
  have s : IsPullback (μ ≫ pullback.snd v b) (pullback.fst (m ≫ v) b) b (m ≫ v) := by
    rw [hμ₂]; exact (IsPullback.of_hasPullback (m ≫ v) b).flip
  exact IsPullback.of_right s hμ₁ (IsPullback.of_hasPullback v b).flip

theorem isPullback_chart
    (μ : pullback (m ≫ v) b ⟶ pullback v b) (hμ₁ : μ ≫ pullback.fst v b = pullback.fst (m ≫ v) b ≫ m)
    (hμ₂ : μ ≫ pullback.snd v b = pullback.snd (m ≫ v) b)
    (μ' : pullback (pullback.snd m ι ≫ ι ≫ v) b ⟶ pullback (ι ≫ v) b)
    (hμ'₁ : μ' ≫ pullback.fst (ι ≫ v) b = pullback.fst _ b ≫ pullback.snd m ι)
    (hμ'₂ : μ' ≫ pullback.snd (ι ≫ v) b = pullback.snd _ b)
    (κ : pullback (ι ≫ v) b ⟶ pullback v b) (hκ₁ : κ ≫ pullback.fst v b = pullback.fst (ι ≫ v) b ≫ ι)
    (hκ₂ : κ ≫ pullback.snd v b = pullback.snd (ι ≫ v) b)
    (lam : pullback (pullback.snd m ι ≫ ι ≫ v) b ⟶ pullback (m ≫ v) b)
    (hlam₁ : lam ≫ pullback.fst (m ≫ v) b = pullback.fst _ b ≫ pullback.fst m ι)
    (hlam₂ : lam ≫ pullback.snd (m ≫ v) b = pullback.snd _ b) :
    IsPullback lam μ' μ κ := by

  have h1 : IsPullback μ' (pullback.fst (pullback.snd m ι ≫ ι ≫ v) b) (pullback.fst (ι ≫ v) b) (pullback.snd m ι) := by
    have s : IsPullback (μ' ≫ pullback.snd (ι ≫ v) b) (pullback.fst (pullback.snd m ι ≫ ι ≫ v) b) b
        (pullback.snd m ι ≫ ι ≫ v) := by
      rw [hμ'₂]; exact (IsPullback.of_hasPullback _ b).flip
    exact IsPullback.of_right s hμ'₁ (IsPullback.of_hasPullback (ι ≫ v) b).flip
  have h2 : IsPullback (pullback.fst (pullback.snd m ι ≫ ι ≫ v) b ≫ pullback.fst m ι) μ' m
      (pullback.fst (ι ≫ v) b ≫ ι) :=
    IsPullback.paste_horiz h1.flip (IsPullback.of_hasPullback m ι)

  have h3 : IsPullback μ (pullback.fst (m ≫ v) b) (pullback.fst v b) m := isPullback_fst_of_comm m v b μ hμ₁ hμ₂
  have hp : lam ≫ μ = μ' ≫ κ := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hμ₁, hκ₁]
      rw [reassoc_of% hlam₁, reassoc_of% hμ'₁, pullback.condition]
    · simp only [Category.assoc, hμ₂, hκ₂]
      rw [hlam₂, hμ'₂]
  have s : IsPullback (lam ≫ pullback.fst (m ≫ v) b) μ' m (κ ≫ pullback.fst v b) := by
    rw [hlam₁, hκ₁]; exact h2
  exact IsPullback.of_right s hp h3.flip

end ClosedImmQc18

namespace ClosedImmQc18

theorem fg_finset_sup {R L : Type u} [CommRing R] [CommRing L] [Algebra R L] {ι' : Type v} (G : Finset ι')
    (T : ι' → Subalgebra R L) (h : ∀ i ∈ G, (T i).FG) : (G.sup T).FG := by
  classical
  induction G using Finset.induction_on with
  | empty => simpa using Subalgebra.fg_bot
  | insert i G hi ih =>
    rw [Finset.sup_insert]
    exact (h i (Finset.mem_insert_self i G)).sup (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

end ClosedImmQc18

open ClosedImmQc18 in
theorem solution
    {A₀ : Type u} [CommRing A₀] {A : Type u} [CommRing A] [Algebra A₀ A]
    {W V : Scheme.{u}} (m : W ⟶ V) (v : V ⟶ Spec (CommRingCat.of A₀)) [QuasiCompact v]
    [QuasiCompact m] [QuasiSeparated m] [LocallyOfFiniteType m]
    (hA : ∀ mA : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))) ⟶
        pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ A))),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mA ≫ pullback.snd _ _ = pullback.snd _ _ →
      IsClosedImmersion mA)
    (s : Finset A) :
    ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ mT : pullback (m ≫ v) (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))) ⟶
          pullback v (Spec.map (CommRingCat.ofHom (algebraMap A₀ ↥T))),
        mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ m → mT ≫ pullback.snd _ _ = pullback.snd _ _ →
        IsClosedImmersion mT := by
  classical
  haveI : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace v
  let 𝒰 := V.affineCover.finiteSubcover

  let ιR : ∀ (B : Type u) [CommRing B] [Algebra A₀ B], Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A₀) :=
    fun B _ _ => Spec.map (CommRingCat.ofHom (algebraMap A₀ B))

  let mj : ∀ j : 𝒰.I₀, pullback m (𝒰.f j) ⟶ 𝒰.X j := fun j => pullback.snd m (𝒰.f j)
  let vj : ∀ j : 𝒰.I₀, 𝒰.X j ⟶ Spec (CommRingCat.of A₀) := fun j => 𝒰.f j ≫ v

  have hcan : ∀ (B : Type u) [CommRing B] [Algebra A₀ B],
      (pullback.fst (m ≫ v) (ιR B) ≫ m) ≫ v = pullback.snd (m ≫ v) (ιR B) ≫ ιR B := by
    intro B _ _; rw [Category.assoc]; exact pullback.condition

  let μA : pullback (m ≫ v) (ιR A) ⟶ pullback v (ιR A) := pullback.lift _ _ (hcan A)
  have hμA : IsClosedImmersion μA := hA μA (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hAj : ∀ (j : 𝒰.I₀) (mA : pullback (mj j ≫ vj j) (ιR A) ⟶ pullback (vj j) (ιR A)),
      mA ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mj j → mA ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mA := by
    intro j mA h1 h2
    have hκ : (pullback.fst (𝒰.f j ≫ v) (ιR A) ≫ 𝒰.f j) ≫ v = pullback.snd (𝒰.f j ≫ v) (ιR A) ≫ ιR A := by
      rw [Category.assoc]; exact pullback.condition
    have hl : (pullback.fst (mj j ≫ vj j) (ιR A) ≫ pullback.fst m (𝒰.f j)) ≫ m ≫ v =
        pullback.snd (mj j ≫ vj j) (ιR A) ≫ ιR A := by
      rw [Category.assoc, ← Category.assoc (pullback.fst m (𝒰.f j)), pullback.condition, Category.assoc, ← Category.assoc]
      exact pullback.condition
    have sq := isPullback_chart m v (𝒰.f j) (ιR A) μA (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) mA h1 h2
      (pullback.lift _ _ hκ) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift _ _ hl) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    exact MorphismProperty.of_isPullback sq hμA

  have HT : ∀ j : 𝒰.I₀, ∃ (T : Subalgebra A₀ A), T.FG ∧ (↑s : Set A) ⊆ T ∧
      ∀ mT : pullback (mj j ≫ vj j) (ιR ↥T) ⟶ pullback (vj j) (ιR ↥T),
        mT ≫ pullback.fst _ _ = pullback.fst _ _ ≫ mj j → mT ≫ pullback.snd _ _ = pullback.snd _ _ → IsClosedImmersion mT :=
    fun j => AlgebraicGeometry.IsClosedImmersion.exists_fg_subalgebra_of_isClosedImmersion_pullback_map (mj j) (vj j) (hAj j) s
  choose Tj hTjfg hsTj hTj using HT

  let T : Subalgebra A₀ A := Finset.univ.sup Tj ⊔ Algebra.adjoin A₀ ↑s
  have hjT : ∀ j, Tj j ≤ T := fun j => (Finset.le_sup (Finset.mem_univ j)).trans le_sup_left
  refine ⟨T, (fg_finset_sup _ Tj (fun j _ => hTjfg j)).sup (Subalgebra.fg_adjoin_finset s),
    (Algebra.subset_adjoin).trans (le_sup_right : Algebra.adjoin A₀ ↑s ≤ T), ?_⟩
  intro mT h1 h2
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) (Scheme.Pullback.openCoverOfLeft 𝒰 v (ιR ↥T))
  intro j

  have hcj : ∀ (B : Type u) [CommRing B] [Algebra A₀ B],
      (pullback.fst (mj j ≫ vj j) (ιR B) ≫ mj j) ≫ vj j = pullback.snd (mj j ≫ vj j) (ιR B) ≫ ιR B := by
    intro B _ _; rw [Category.assoc]; exact pullback.condition
  let μT : pullback (mj j ≫ vj j) (ιR ↥T) ⟶ pullback (vj j) (ιR ↥T) := pullback.lift _ _ (hcj ↥T)
  let μj : pullback (mj j ≫ vj j) (ιR ↥(Tj j)) ⟶ pullback (vj j) (ιR ↥(Tj j)) := pullback.lift _ _ (hcj ↥(Tj j))
  have hμj : IsClosedImmersion μj := hTj j μj (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

  have hι : Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hjT j)).toRingHom) ≫ ιR ↥(Tj j) = ιR ↥T := by
    show _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]; rfl
  have hqP : pullback.fst (mj j ≫ vj j) (ιR ↥T) ≫ (mj j ≫ vj j) =
      (pullback.snd (mj j ≫ vj j) (ιR ↥T) ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hjT j)).toRingHom)) ≫ ιR ↥(Tj j) := by
    rw [Category.assoc, hι]; exact pullback.condition
  have hqQ : pullback.fst (vj j) (ιR ↥T) ≫ vj j =
      (pullback.snd (vj j) (ιR ↥T) ≫ Spec.map (CommRingCat.ofHom (Subalgebra.inclusion (hjT j)).toRingHom)) ≫ ιR ↥(Tj j) := by
    rw [Category.assoc, hι]; exact pullback.condition
  let qP := pullback.lift _ _ hqP
  let qQ := pullback.lift _ _ hqQ
  have hμT : IsClosedImmersion μT := by
    have s1 : IsPullback (qP ≫ pullback.fst _ _) μT (mj j) (qQ ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst, pullback.lift_fst]
      exact (isPullback_fst_of_comm (mj j) (vj j) (ιR ↥T) μT (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).flip
    have p : qP ≫ μj = μT ≫ qQ := by
      apply pullback.hom_ext
      · simp only [Category.assoc, qP, qQ, μj, μT, pullback.lift_fst, pullback.lift_fst_assoc]
      · simp only [Category.assoc, qP, qQ, μj, μT, pullback.lift_snd, pullback.lift_snd_assoc]
    have sq : IsPullback qP μT μj qQ :=
      IsPullback.of_right s1 p (isPullback_fst_of_comm (mj j) (vj j) (ιR ↥(Tj j)) μj (pullback.lift_fst _ _ _)
        (pullback.lift_snd _ _ _)).flip
    exact MorphismProperty.of_isPullback sq hμj

  have hκ1 : (Scheme.Pullback.openCoverOfLeft 𝒰 v (ιR ↥T)).f j ≫ pullback.fst v (ιR ↥T) = pullback.fst _ _ ≫ 𝒰.f j := by
    simp only [Scheme.Pullback.openCoverOfLeft]
    exact pullback.lift_fst _ _ _
  have hκ2 : (Scheme.Pullback.openCoverOfLeft 𝒰 v (ιR ↥T)).f j ≫ pullback.snd v (ιR ↥T) = pullback.snd _ _ := by
    simp only [Scheme.Pullback.openCoverOfLeft]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  have hl : (pullback.fst (mj j ≫ vj j) (ιR ↥T) ≫ pullback.fst m (𝒰.f j)) ≫ m ≫ v =
      pullback.snd (mj j ≫ vj j) (ιR ↥T) ≫ ιR ↥T := by
    rw [Category.assoc, ← Category.assoc (pullback.fst m (𝒰.f j)), pullback.condition, Category.assoc, ← Category.assoc]
    exact pullback.condition
  have sq := isPullback_chart m v (𝒰.f j) (ιR ↥T) mT h1 h2 μT (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    ((Scheme.Pullback.openCoverOfLeft 𝒰 v (ιR ↥T)).f j) hκ1 hκ2
    (pullback.lift _ _ hl) (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  have hsnd : Scheme.Cover.pullbackHom (Scheme.Pullback.openCoverOfLeft 𝒰 v (ιR ↥T)) mT j = sq.isoPullback.inv ≫ μT := by
    rw [Scheme.Cover.pullbackHom]
    exact (Iso.eq_inv_comp _).2 sq.isoPullback_hom_snd
  rw [hsnd]
  exact @IsClosedImmersion.comp _ _ _ _ _ inferInstance hμT

end S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact
end P2MW
export P2MW.S_AlgebraicGeometry_IsClosedImmersion_exists_fg_subalgebra_of_isClosedImmersion_pullback_map_of_quasiCompact (solution)
