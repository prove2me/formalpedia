-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.Modules.ProjPresentation.isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/cfd158d1-a559-5da3-88c3-16cdf086f962

import Definitions.Def_AlgebraicGeometry_FramedPolarisedAbelianScheme
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_surjectiveOnStalks_of_forall_exists_eq_sum_smul
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_injective_toProj_of_forall_exists_eq_sum_smul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

theorem solution
    {S : Type u} [CommRing S] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of S)} {𝓛 : X.Modules}
    {M N : ℕ} (𝔔 : Scheme.Modules.ProjPresentation 𝓛 f M) (𝔓 : Scheme.Modules.ProjPresentation 𝓛 f N)
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → S,
      𝔔.σ j = ∑ k, ((f.appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (a k))) • 𝔓.σ k)
    (hQ : IsClosedImmersion 𝔔.toProj) :
    IsClosedImmersion 𝔓.toProj := by
  have hb : f.appLE ⊤ ⊤ le_top = f.appTop := Scheme.Hom.appLE_eq_app f
  have h' : ∀ i : Fin (M + 1), ∃ c : Fin (N + 1) → S,
      𝔔.σ i = ∑ j, (f.appTop ((Scheme.ΓSpecIso (.of S)).inv (c j))) • 𝔓.σ j := by
    intro i
    obtain ⟨a, ha⟩ := hspan i
    refine ⟨a, ha.trans (Finset.sum_congr rfl fun k _ => ?_)⟩
    have hk := congrArg
      (fun φ : Γ(Spec (CommRingCat.of S), ⊤) ⟶ Γ(X, ⊤) => φ.hom ((Scheme.ΓSpecIso (.of S)).inv (a k))) hb
    exact congrArg (· • 𝔓.σ k) hk
  haveI hsos : SurjectiveOnStalks 𝔓.toProj :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.surjectiveOnStalks_of_forall_exists_eq_sum_smul 𝔔 𝔓 h'
  have hinj : Function.Injective 𝔓.toProj.base :=
    AlgebraicGeometry.Scheme.Modules.ProjPresentation.injective_toProj_of_forall_exists_eq_sum_smul 𝔔 𝔓
      𝔔.toProj.isClosedEmbedding.injective h'
  have hf : IsProper f := by rw [← 𝔔.toProj_π]; infer_instance
  haveI : IsProper (𝔓.toProj ≫ ProjSpace.π S N) := by rw [𝔓.toProj_π]; exact hf
  haveI : IsProper 𝔓.toProj := IsProper.of_comp 𝔓.toProj (ProjSpace.π S N)
  exact { isClosedEmbedding :=
    Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap 𝔓.toProj.continuous hinj 𝔓.toProj.isClosedMap }

end

end S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul
end P2MW
export P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_isClosedImmersion_toProj_of_forall_exists_eq_sum_smul (solution)
