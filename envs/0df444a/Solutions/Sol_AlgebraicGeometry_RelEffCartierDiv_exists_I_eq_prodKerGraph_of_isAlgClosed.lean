-- Prove2me | solution 1 for AlgebraicGeometry.RelEffCartierDiv.exists_I_eq_prodKerGraph_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/b3ee74aa-92c4-52c9-ae0b-8312af21a738

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSum
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_exists_split
import Theorems.Thm_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app"

set_option autoImplicit false

universe u

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed.AlgebraicGeometry"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension pointOfClosedPoint LocallyOfFiniteType Spec Scheme LocallyOfFiniteType.jacobsonSpace pointOfClosedPoint_comp IsSeparated RelEffCartierDiv mapOnProdOver RelEffCartierDiv.pullbackAlong_comp prodKerGraph RelEffCartierDiv.exists_split prodKerGraph_comap_mapOnProdOver" namespace SumPtsAux end AlgebraicGeometry.SumPtsAux
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f] [Nonempty X] :
    ∃ p : Spec (CommRingCat.of K) ⟶ X, p ≫ f = 𝟙 _ := by
  haveI : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  obtain ⟨x, -, hx⟩ :=
    nonempty_inter_closedPoints (X := X) Set.univ_nonempty isClosed_univ.isLocallyClosed
  exact ⟨pointOfClosedPoint f x hx, pointOfClosedPoint_comp f x hx⟩

theorem solution
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    {k : Type u} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    {r : ℕ} (D : RelEffCartierDiv f r x) :
    ∃ (a : Fin r → (Spec (CommRingCat.of k) ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = x),
      D.I = prodKerGraph f a ha := by
  obtain ⟨P, gP, p, hp, b, hb, hfin, -, -, hsurj, -, hsplit, -⟩ := D.exists_split
  haveI : Nonempty P := by
    obtain ⟨y, -⟩ := p.surjective (Classical.arbitrary _)
    exact ⟨y⟩
  obtain ⟨u, hu⟩ := AlgebraicGeometry.SumPtsAux.exists_comp_eq_id_of_isAlgClosed p
  have hu' : u ≫ gP = x := by rw [← hp, ← Category.assoc, hu, Category.id_comp]
  have key : D = (D.pullbackAlong p hp).pullbackAlong u hu' := by
    rw [RelEffCartierDiv.pullbackAlong_comp]
    have aux : ∀ (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) (hφ : φ ≫ x = x),
        φ = 𝟙 _ → D.pullbackAlong φ hφ = D := by
      rintro φ hφ rfl
      exact D.pullbackAlong_id
    exact (aux _ _ hu).symm
  refine ⟨fun i => u ≫ b i, fun i => by rw [Category.assoc, hb, hu'], ?_⟩
  calc D.I = ((D.pullbackAlong p hp).pullbackAlong u hu').I := by rw [← key]
    _ = (D.pullbackAlong p hp).I.comap (mapOnProdOver f u hu') := rfl
    _ = (prodKerGraph f b hb).comap (mapOnProdOver f u hu') := by rw [hsplit]
    _ = prodKerGraph f (fun i => u ≫ b i) _ := prodKerGraph_comap_mapOnProdOver b hb u hu'

end S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_RelEffCartierDiv_exists_I_eq_prodKerGraph_of_isAlgClosed (solution)
