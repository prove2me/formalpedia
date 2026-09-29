-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/96a8f2d6-1954-5fa8-8753-8c2d94d19614

import Mathlib.AlgebraicGeometry.Sites.Representability
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "IsOpenImmersion.lift Scheme.Opens.range_ι Scheme IsOpenImmersion Scheme.Opens IsOpenImmersion.lift_fac RelEffCartierDiv.supportedIn RelEffCartierDiv.functor RelEffCartierDiv"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "SupportedIn supportedInLocus supportedIn_pullbackAlong_iff supportedIn mem_supportedIn_iff functor functor_map_snd ext pullbackAlong"
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens)

set_option backward.isDefEq.respectTransparency false in

theorem isOpenImmersion_presheaf_supportedIn_incl_aux :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι := by
  apply MorphismProperty.relative.of_exists
  intro T g

  set x : (RelEffCartierDiv.functor f r).obj (op T) := yonedaEquiv g with hx
  have hg : ∀ {T' : Scheme.{u}ᵒᵖ} (φ : unop T' ⟶ T),
      g.app T' φ = (RelEffCartierDiv.functor f r).map φ.op x := by
    intro T' φ
    rw [hx, yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

  let W : T.Opens := x.2.supportedInLocus U
  have hxW : (RelEffCartierDiv.functor f r).map W.ι.op x ∈
      (RelEffCartierDiv.supportedIn f r U).obj (op (W : Scheme.{u})) := by
    rw [mem_supportedIn_iff, functor_map_snd]
    exact (supportedIn_pullbackAlong_iff _ _ _ _).mpr
      (by simp only [Quiver.Hom.unop_op, Scheme.Opens.range_ι]; exact subset_rfl)
  let y : (RelEffCartierDiv.supportedIn f r U).toFunctor.obj (op (W : Scheme.{u})) := ⟨_, hxW⟩
  refine ⟨W, yonedaEquiv.symm y, W.ι, ?_, inferInstance⟩
  apply IsPullback.of_forall_isPullback_app
  intro T'
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  ·
    refine ConcreteCategory.hom_ext _ _ fun ψ => ?_
    simp only [ConcreteCategory.comp_apply, yonedaEquiv_symm_app_apply, yoneda_map_app, hg]
    change (RelEffCartierDiv.functor f r).map ψ.op ((RelEffCartierDiv.functor f r).map W.ι.op x) = _
    rw [← Functor.map_comp_apply, ← op_comp]
    rfl
  ·
    rintro ψ₁ ψ₂ ⟨-, h⟩
    simp only [yoneda_map_app] at h
    exact (cancel_mono W.ι).mp h
  ·
    intro y₂ φ h
    change unop T' ⟶ T at φ
    change y₂.1 = g.app T' φ at h
    rw [hg] at h
    have hφ : (x.2.pullbackAlong φ rfl).SupportedIn U := by
      have := y₂.2
      rw [h, mem_supportedIn_iff, functor_map_snd] at this
      exact this
    rw [supportedIn_pullbackAlong_iff] at hφ
    have hW : Set.range φ ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
    refine ⟨IsOpenImmersion.lift W.ι φ hW, ?_, ?_⟩
    · apply Subtype.ext
      change (RelEffCartierDiv.functor f r).map (IsOpenImmersion.lift W.ι φ hW).op
        ((RelEffCartierDiv.functor f r).map W.ι.op x) = y₂.1
      rw [h, ← Functor.map_comp_apply, ← op_comp, IsOpenImmersion.lift_fac]
    · exact IsOpenImmersion.lift_fac W.ι φ hW

end AlgebraicGeometry.RelEffCartierDiv

theorem solution {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (U : 𝒞.Opens) :
    IsOpenImmersion.presheaf (RelEffCartierDiv.supportedIn f r U).ι :=
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_presheaf_supportedIn_incl_aux f r U

end S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_isOpenImmersion_presheaf_supportedIn_incl (solution)
