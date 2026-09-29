-- Prove2me | solution 1 for AlgebraicGeometry.RelPicard.RepresentsRelSubPic.flat_mul_fst_snd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:03.589526+00:00
-- url     : https://prove2.me/submissions/455d95b2-703a-53ab-af0d-b43b68c8001c

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_flat_mul_fst_snd

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_flat_mul_fst_snd.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_flat_mul_fst_snd.AlgebraicGeometry.RelPicard"

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec Scheme Flat"
namespace RelPicard
p2m_export "AlgebraicGeometry.RelPicard" "RepresentsRelSubPic SubPicGroupCondition"
namespace GrpMulFlat
p2m_open "AlgebraicGeometry.RelPicard AlgebraicGeometry"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f) (hc : G.IsCommutative)

include hc in

theorem mul_inv_cancel' {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.mul t x (G.inv t x) = G.one t := by
  rw [hc t x]; exact G.inv_mul_cancel t x

include hc in

theorem inv_unique {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f)
    (hy : G.mul t y x = G.one t) : y = G.inv t x := by
  calc y = G.mul t y (G.one t) := (G.mul_one t y).symm
    _ = G.mul t y (G.mul t x (G.inv t x)) := by rw [mul_inv_cancel' G hc]
    _ = G.mul t (G.mul t y x) (G.inv t x) := (G.mul_assoc t _ _ _).symm
    _ = G.inv t x := by rw [hy, G.one_mul]

theorem one_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.one t) = G.one t' := by
  set c := GoodReductionJacobian.schemeHomOverComp ψ hψ (G.one t) with hcdef
  have hcc : G.mul t' c c = c := by
    rw [hcdef, ← G.mul_natural, G.one_mul]
  calc c = G.mul t' (G.one t') c := (G.one_mul t' c).symm
    _ = G.mul t' (G.mul t' (G.inv t' c) c) c := by rw [G.inv_mul_cancel]
    _ = G.mul t' (G.inv t' c) (G.mul t' c c) := G.mul_assoc t' _ _ _
    _ = G.one t' := by rw [hcc, G.inv_mul_cancel]

include hc in

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) = G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  apply inv_unique G hc
  rw [← G.mul_natural, G.inv_mul_cancel, one_natural G]

end AlgebraicGeometry.RelPicard.GrpMulFlat

open AlgebraicGeometry.RelPicard.GrpMulFlat in
theorem solution
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) [Flat D.toBase] :
    Flat (h.relativeGroupLaw.mul (pullback.fst D.toBase D.toBase ≫ D.toBase)
      ⟨pullback.fst D.toBase D.toBase, rfl⟩ ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩).1 := by
  let G := h.relativeGroupLaw
  have hc : G.IsCommutative := h.relativeGroupLaw_isCommutative
  let t₂ : pullback D.toBase D.toBase ⟶ Spec (CommRingCat.of R) := pullback.fst D.toBase D.toBase ≫ D.toBase
  let pr₁ : SchemeHomOver t₂ D.toBase := ⟨pullback.fst D.toBase D.toBase, rfl⟩
  let pr₂ : SchemeHomOver t₂ D.toBase := ⟨pullback.snd D.toBase D.toBase, pullback.condition.symm⟩
  let m := G.mul t₂ pr₁ pr₂
  let n := G.mul t₂ (G.inv t₂ pr₁) pr₂

  let φ : pullback D.toBase D.toBase ⟶ pullback D.toBase D.toBase :=
    pullback.lift pr₁.1 m.1 (pr₁.2.trans m.2.symm)
  let ψ : pullback D.toBase D.toBase ⟶ pullback D.toBase D.toBase :=
    pullback.lift pr₁.1 n.1 (pr₁.2.trans n.2.symm)
  have hφ : φ ≫ t₂ = t₂ := by show φ ≫ (pullback.fst _ _ ≫ D.toBase) = _; rw [pullback.lift_fst_assoc]
  have hψ : ψ ≫ t₂ = t₂ := by show ψ ≫ (pullback.fst _ _ ≫ D.toBase) = _; rw [pullback.lift_fst_assoc]

  have cφ₁ : GoodReductionJacobian.schemeHomOverComp φ hφ pr₁ = pr₁ := Subtype.ext (pullback.lift_fst _ _ _)
  have cφ₂ : GoodReductionJacobian.schemeHomOverComp φ hφ pr₂ = m := Subtype.ext (pullback.lift_snd _ _ _)
  have cψ₁ : GoodReductionJacobian.schemeHomOverComp ψ hψ pr₁ = pr₁ := Subtype.ext (pullback.lift_fst _ _ _)
  have cψ₂ : GoodReductionJacobian.schemeHomOverComp ψ hψ pr₂ = n := Subtype.ext (pullback.lift_snd _ _ _)
  have hφψ : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      show (GoodReductionJacobian.schemeHomOverComp φ hφ n).1 = pr₂.1
      congr 1
      show GoodReductionJacobian.schemeHomOverComp φ hφ (G.mul t₂ (G.inv t₂ pr₁) pr₂) = pr₂
      rw [G.mul_natural, inv_natural G hc, cφ₁, cφ₂, ← G.mul_assoc, G.inv_mul_cancel, G.one_mul]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, Category.id_comp]
      show (GoodReductionJacobian.schemeHomOverComp ψ hψ m).1 = pr₂.1
      congr 1
      show GoodReductionJacobian.schemeHomOverComp ψ hψ (G.mul t₂ pr₁ pr₂) = pr₂
      rw [G.mul_natural, cψ₁, cψ₂, ← G.mul_assoc, mul_inv_cancel' G hc, G.one_mul]
  haveI : IsIso φ := ⟨⟨ψ, hφψ, hψφ⟩⟩
  have hm : m.1 = φ ≫ pullback.snd D.toBase D.toBase := (pullback.lift_snd _ _ _).symm
  show Flat m.1
  rw [hm]
  infer_instance

end S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_flat_mul_fst_snd
end P2MW
export P2MW.S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_flat_mul_fst_snd (solution)
