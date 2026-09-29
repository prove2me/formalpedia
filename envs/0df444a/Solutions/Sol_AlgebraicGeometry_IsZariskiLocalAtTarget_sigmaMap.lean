-- Prove2me | solution 1 for AlgebraicGeometry.IsZariskiLocalAtTarget.sigmaMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/1c81bb36-4ef2-5cf6-b3aa-970a383d9ae2

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap

set_option autoImplicit false
universe u
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "sigmaMk_mk Scheme.Hom IsZariskiLocalAtTarget Scheme sigmaι_eq_iff IsOpenImmersion sigmaOpenCover IsZariskiLocalAtTarget.of_openCover sigmaMk IsOpenImmersion.isPullback Scheme.Hom.comp_apply"
namespace SigmaMapU4
p2m_open "AlgebraicGeometry"

variable {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i)

theorem sigmaMap_sigmaι_apply (i : σ) (x : X i) :
    (Limits.Sigma.map f) ((Limits.Sigma.ι X i) x) = (Limits.Sigma.ι Y i) (f i x) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Limits.Sigma.ι_map]

set_option backward.isDefEq.respectTransparency false in

theorem isPullback_sigmaι_sigmaMap (j : σ) :
    IsPullback (f j) (Limits.Sigma.ι X j) (Limits.Sigma.ι Y j) (Limits.Sigma.map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (by simp) ?_
  apply le_antisymm
  · rintro x ⟨y, hxy⟩
    obtain ⟨⟨i, x⟩, rfl⟩ := (sigmaMk X).surjective x
    rw [sigmaMk_mk] at hxy ⊢
    have hxy' : (Limits.Sigma.ι Y j) y = (Limits.Sigma.ι Y i) (f i x) := by
      rw [← sigmaMap_sigmaι_apply]; exact hxy
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp ((sigmaι_eq_iff Y j i _ _).mp hxy')
    exact ⟨x, rfl⟩
  · rintro _ ⟨x, rfl⟩
    exact ⟨f j x, (sigmaMap_sigmaι_apply f j x).symm⟩

end AlgebraicGeometry.SigmaMapU4

open AlgebraicGeometry.SigmaMapU4 in
set_option backward.isDefEq.respectTransparency false in
theorem solution
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {σ : Type u} {X Y : σ → Scheme.{u}} (f : ∀ i, X i ⟶ Y i) (hf : ∀ i, P (f i)) :
    P (Limits.Sigma.map f) := by
  refine IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y) ?_
  intro j
  show P (Limits.pullback.snd (Limits.Sigma.map f) (Limits.Sigma.ι Y j))
  rw [← MorphismProperty.cancel_left_of_respectsIso P (isPullback_sigmaι_sigmaMap f j).flip.isoPullback.hom,
    IsPullback.isoPullback_hom_snd]
  exact hf j

end S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap
end P2MW
export P2MW.S_AlgebraicGeometry_IsZariskiLocalAtTarget_sigmaMap (solution)
