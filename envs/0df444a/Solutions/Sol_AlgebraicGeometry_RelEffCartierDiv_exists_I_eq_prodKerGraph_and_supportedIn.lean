-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_and_supportedIn
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b0b3475e-d6da-560a-b358-f3a700230d7d

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn

import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_supportedIn_I_eq_mul_of_supportedIn
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FltWs21
namespace M10b

theorem supportedIn_ofPoint {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens)
    {T : Scheme.{u}} {g : T ⟶ S} (a : T ⟶ 𝒞) (ha : a ≫ f = g) (haU : Set.range a.base ⊆ (U : Set 𝒞)) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  intro x hx
  rw [RelEffCartierDiv.ofPoint_I] at hx
  have hx' : x ∈ ((graphOver f a ha).ker.support : Set ↥(pullback f g)) := hx
  rw [Scheme.Hom.support_ker, (IsClosedImmersion.isClosedEmbedding (graphOver f a ha)).isClosed_range.closure_eq] at hx'
  obtain ⟨t, rfl⟩ := hx'
  show pullback.fst f g (graphOver f a ha t) ∈ U
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact haU ⟨t, rfl⟩

end FltWs21.M10b

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] (U : 𝒞.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ f)]
    {e : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (a : Fin e → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g)
    (haU : ∀ i, Set.range (a i).base ⊆ (U : Set 𝒞)) :
    ∃ D : RelEffCartierDiv f e g, D.I = prodKerGraph f a ha ∧ D.SupportedIn U := by
  induction e with
  | zero =>
      refine ⟨RelEffCartierDiv.empty f g, ?_, ?_⟩
      · rw [RelEffCartierDiv.empty_I, prodKerGraph_zero]
      · intro x hx
        rw [RelEffCartierDiv.empty_I] at hx
        have : x ∈ ((⊤ : (pullback f g).IdealSheafData).support : Set ↥(pullback f g)) := hx
        rw [Scheme.IdealSheafData.support_top] at this
        exact absurd this (by simp)
  | succ e ih =>
      obtain ⟨D', hD'I, hD'U⟩ := ih (fun i => a i.succ) (fun i => ha i.succ) (fun i => haU i.succ)
      obtain ⟨F, hFI, hFU⟩ := AlgebraicGeometry.RelEffCartierDiv.exists_supportedIn_I_eq_mul_of_supportedIn U D'
        (RelEffCartierDiv.ofPoint f (a 0) (ha 0)) hD'U (FltWs21.M10b.supportedIn_ofPoint U (a 0) (ha 0) (haU 0))
      refine ⟨F, ?_, hFU⟩
      rw [hFI, hD'I, RelEffCartierDiv.ofPoint_I, prodKerGraph_succ, mul_comm]

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_and_supportedIn (solution)
