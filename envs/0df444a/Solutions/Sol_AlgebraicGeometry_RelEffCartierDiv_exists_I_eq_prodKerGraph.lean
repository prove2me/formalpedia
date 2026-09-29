-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/ec98aaba-befd-5a96-8a3f-2a9c7db8ff5c

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph.AlgebraicGeometry"

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension Scheme Smooth IsSeparated prodKerGraph prodKerGraph_zero prodKerGraph_succ RelEffCartierDiv.empty RelEffCartierDiv.empty_I RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I RelEffCartierDiv RelEffCartierDiv.exists_I_eq_mul"
namespace RelEffCartierDiv
p2m_export "AlgebraicGeometry.RelEffCartierDiv" "empty empty_I ofPoint ofPoint_I I exists_I_eq_mul"
namespace SumInduction
p2m_open "AlgebraicGeometry.RelEffCartierDiv AlgebraicGeometry"

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
  {T : Scheme.{u}} {g : T ⟶ S}

theorem exists_I_eq_prodKerGraph : ∀ (r : ℕ) (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g),
    ∃ D : RelEffCartierDiv f r g, D.I = prodKerGraph f a ha
  | 0, a, ha => ⟨RelEffCartierDiv.empty f g, by rw [RelEffCartierDiv.empty_I, prodKerGraph_zero]⟩
  | r + 1, a, ha => by
    obtain ⟨E, hE⟩ := exists_I_eq_prodKerGraph r (fun i => a i.succ) (fun i => ha i.succ)
    obtain ⟨F, hF⟩ := RelEffCartierDiv.exists_I_eq_mul E (RelEffCartierDiv.ofPoint f (a 0) (ha 0))
    exact ⟨F, by rw [hF, hE, RelEffCartierDiv.ofPoint_I, prodKerGraph_succ, mul_comm]⟩

end AlgebraicGeometry.RelEffCartierDiv.SumInduction

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {r : ℕ} {T : Scheme.{u}} {g : T ⟶ S} (a : Fin r → (T ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g) :
    ∃ D : RelEffCartierDiv f r g, D.I = prodKerGraph f a ha :=
  AlgebraicGeometry.RelEffCartierDiv.SumInduction.exists_I_eq_prodKerGraph r a ha

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph (solution)
