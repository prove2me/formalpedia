-- Prove2me | solution 1 for AlgebraicGeometry.IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasiCompact
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/b8aacb8c-b752-5e49-8274-5167f627bc83

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact.AlgebraicGeometry TopologicalSpace"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "quasiSeparatedSpace_iff_forall_affineOpens Surjective HasAffineProperty Scheme.Hom IsLocalIso isIso_pushoutSection_iff HasAffineProperty.descendsAlong_of_affineAnd isAffine_of_isAffineHom QuasiCompact IsAffine IsZariskiLocalAtTarget Spec Spec.map Scheme.toSpecΓ_naturality IsLocalIso.le_of_isZariskiLocalAtSource Scheme Scheme.Hom.appTop isIso_pushoutSection_of_isQuasiSeparated_of_flat_right Flat isAffineOpen_top IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact Scheme.Spec IsAffineOpen IsAffineHom toSpecΓ Scheme.Hom.appLE"
namespace AffineDescent
p2m_open "AlgebraicGeometry"

theorem compactSpace_of_surjective_of_isAffine {P Y : Scheme.{u}} (p : P ⟶ Y) [IsAffine P]
    [Surjective p] : CompactSpace Y := by
  refine ⟨?_⟩
  rw [← p.surjective.range_eq]
  exact isCompact_range p.continuous

theorem quasiSeparatedSpace_of_surjective_of_isAffineHom {P Y : Scheme.{u}} (p : P ⟶ Y)
    [IsAffine P] [IsAffineHom p] [Surjective p] : QuasiSeparatedSpace Y := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  have hU : IsAffineOpen (p ⁻¹ᵁ (U : Y.Opens)) := U.2.preimage p
  have hV : IsAffineOpen (p ⁻¹ᵁ (V : Y.Opens)) := V.2.preimage p
  have hc : IsCompact ((p ⁻¹ᵁ (U : Y.Opens) : Set P) ∩ (p ⁻¹ᵁ (V : Y.Opens) : Set P)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ (p ⁻¹ᵁ (U : Y.Opens)).2 hU.isCompact
      (p ⁻¹ᵁ (V : Y.Opens)).2 hV.isCompact
  have himg : p.base '' ((p ⁻¹ᵁ (U : Y.Opens) : Set P) ∩ (p ⁻¹ᵁ (V : Y.Opens) : Set P)) =
      (U : Set Y) ∩ (V : Set Y) := by
    change p.base '' (p.base ⁻¹' (U : Set Y) ∩ p.base ⁻¹' (V : Set Y)) = _
    rw [← Set.preimage_inter, Set.image_preimage_eq _ p.surjective]
  rw [← himg]
  exact hc.image p.continuous

theorem isPullback_specMap_appTop {R S : CommRingCat.{u}} {Y P : Scheme.{u}} (φ : R ⟶ S)
    (g : Y ⟶ Spec R) (p₁ : P ⟶ Spec S) (p₂ : P ⟶ Y) (H : IsPullback p₁ p₂ (Spec.map φ) g)
    [Flat (Spec.map φ)] [CompactSpace Y] [QuasiSeparatedSpace Y] :
    IsPullback (Spec.map p₁.appTop) (Spec.map p₂.appTop) (Spec.map (Spec.map φ).appTop)
      (Spec.map g.appTop) := by
  have hUST : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_rfl
  have hUSX : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ (⊤ : (Spec R).Opens) := le_rfl
  have hUY : (⊤ : P.Opens) = p₂ ⁻¹ᵁ (⊤ : Y.Opens) ⊓ p₁ ⁻¹ᵁ (⊤ : (Spec S).Opens) := by simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip hUST hUSX hUY
    (isAffineOpen_top (Spec R)) (isAffineOpen_top (Spec S)) (isCompact_univ)
    (isQuasiSeparated_univ)
  have hpo := (isIso_pushoutSection_iff H.flip hUST hUSX hUY).mp hiso

  have := hpo.op.map Scheme.Spec
  convert this using 2
  all_goals
    first
    | rfl
    | (simp [Scheme.Hom.appLE, Scheme.Hom.appTop, Spec.map])

theorem isAffine_of_isPullback {R S : CommRingCat.{u}} {Y P : Scheme.{u}} (φ : R ⟶ S)
    (g : Y ⟶ Spec R) (p₁ : P ⟶ Spec S) (p₂ : P ⟶ Y) (H : IsPullback p₁ p₂ (Spec.map φ) g)
    [Surjective (Spec.map φ)] [Flat (Spec.map φ)] [IsAffine P] : IsAffine Y := by
  have hp₂a : IsAffineHom p₂ := MorphismProperty.of_isPullback (P := @IsAffineHom) H inferInstance
  have hp₂s : Surjective p₂ := MorphismProperty.of_isPullback (P := @Surjective) H inferInstance
  have : CompactSpace Y := compactSpace_of_surjective_of_isAffine p₂
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_surjective_of_isAffineHom p₂
  have SQ1 := isPullback_specMap_appTop φ g p₁ p₂ H
  have SQiso : IsPullback (Spec S).toSpecΓ (Spec.map φ) (Spec.map (Spec.map φ).appTop)
      (Spec R).toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality (Spec.map φ)).symm⟩
  have s := H.paste_horiz SQiso
  rw [Scheme.toSpecΓ_naturality p₁, Scheme.toSpecΓ_naturality g] at s
  have SQ2 : IsPullback P.toSpecΓ p₂ (Spec.map p₂.appTop) Y.toSpecΓ :=
    s.of_right (Scheme.toSpecΓ_naturality p₂).symm SQ1
  have e : Spec.map (Spec.map φ).appTop = inv (Spec S).toSpecΓ ≫ Spec.map φ ≫ (Spec R).toSpecΓ := by
    rw [IsIso.eq_inv_comp, ← Scheme.toSpecΓ_naturality]
  have h1 : Surjective (Spec.map (Spec.map φ).appTop) := by rw [e]; infer_instance
  have h2 : Flat (Spec.map (Spec.map φ).appTop) := by rw [e]; infer_instance
  have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (Spec.map p₂.appTop) :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) SQ1 h1,
      MorphismProperty.of_isPullback (P := @Flat) SQ1 h2⟩, inferInstance⟩
  have hiso : (isomorphisms Scheme.{u}) P.toSpecΓ := (isomorphisms.iff _).mpr inferInstance
  have : IsIso Y.toSpecΓ := (isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback_of_descendsAlong (P := isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) SQ2 hcov hiso)
  exact ⟨this⟩

theorem isAffineHom_descendsAlong :
    DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsAffineHom (@Surjective ⊓ @Flat)
  · intro X Y f hf
    exact ⟨hf.2, (MorphismProperty.le_def (P := @IsLocalIso) (Q := @Flat)).mp
      (IsLocalIso.le_of_isZariskiLocalAtSource @Flat) f hf.1⟩
  · intro R S Y φ g hφ h
    haveI : Surjective (Spec.map φ) := hφ.1
    haveI : Flat (Spec.map φ) := hφ.2
    haveI : IsAffineHom (pullback.fst (Spec.map φ) g) := h
    haveI : IsAffine (pullback (Spec.map φ) g) := isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
    haveI : IsAffine Y :=
      isAffine_of_isPullback φ g (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    infer_instance

end AlgebraicGeometry.AffineDescent

open AlgebraicGeometry.AffineDescent in
theorem solution :
    DescendsAlong (@IsAffineHom : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  isAffineHom_descendsAlong

end S_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact
end P2MW
export P2MW.S_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact (solution)
