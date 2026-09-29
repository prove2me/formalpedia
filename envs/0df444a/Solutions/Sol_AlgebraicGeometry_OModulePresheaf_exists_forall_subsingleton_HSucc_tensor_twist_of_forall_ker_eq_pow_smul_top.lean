-- Prove2me | solution 1 for AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:02.935278+00:00
-- url     : https://prove2.me/submissions/0f9e4966-90d2-5f20-b480-17891efae500

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isFG_hom_injective_saturated_familyFramesGradedModule
import Theorems.Thm_ProjSpaceCech_GradedModule_exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace P2mGrVanishAsm

theorem exists_fin_span_eq {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∃ (s : ℕ) (g : Fin s → A), Ideal.span (Set.range g) = I :=
  Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian I)

end P2mGrVanishAsm

open _root_.AlgebraicGeometry.OModulePresheaf in
theorem solution
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (K : ℕ → OModulePresheaf q) (hKc : ∀ k, (K k).IsCoherent) (hKq : ∀ k, (K k).IsQuasicoherent)
    (j : ∀ k, OModulePresheaf.AffHom (K k) (F (k + 1)))
    (hji : ∀ (k : ℕ) (U : P.affineOpens), Function.Injective ((j k).app U))
    (hjr : ∀ (k : ℕ) (U : P.affineOpens), LinearMap.range ((j k).app U) = LinearMap.ker ((φ k).app U)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ (k i : ℕ),
      Subsingleton (((K k).tensor (ProjSpace.twist q ι d)).HSucc (ProjSpace.stdCoverPullback ι) i) := by

  obtain ⟨s, g, hg⟩ := P2mGrVanishAsm.exists_fin_span_eq I
  obtain ⟨θ, -, hcomm, hgen⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_affHom_apply_eq_smul_comm_iSup_range_eq_top_of_forall_ker_eq_pow_smul_top
      I g hg F φ hφs hφk K j hji hjr

  obtain ⟨D, hD, h, hinj, hsat⟩ :=
    AlgebraicGeometry.OModulePresheaf.exists_isFG_hom_injective_saturated_familyFramesGradedModule
      ι hιq K hKc hKq θ hcomm hgen

  obtain ⟨d₀, hd₀⟩ :=
    ProjSpaceCech.GradedModule.exists_forall_subsingleton_H_shift_of_isFG_of_hom_injective_saturated
      (familyFramesGradedModule ι K θ hcomm) D hD h hinj hsat
  refine ⟨d₀.toNat, fun d hd k i => ?_⟩

  have hv : Subsingleton (ProjSpaceCech.GradedModule.H
      (ProjSpaceCech.GradedModule.shift (familyFramesGradedModule ι K θ hcomm) (d : ℤ)) (i + 1)) :=
    hd₀ (d : ℤ) (by omega) (i + 1) (Nat.succ_le_succ (Nat.zero_le i))
  exact AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_tensor_twist_of_subsingleton_H_shift_familyFramesGradedModule
    ι K hKq θ hcomm d k i hv

end S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top
end P2MW
export P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top (solution)
