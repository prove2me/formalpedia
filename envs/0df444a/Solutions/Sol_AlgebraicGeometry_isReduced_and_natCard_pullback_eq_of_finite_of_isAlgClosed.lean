-- Prove2me | solution 1 for AlgebraicGeometry.isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/9dda2438-ae1a-5798-8d28-04b4a4448204

import Mathlib
import Theorems.Thm_AlgebraicGeometry_isReduced_pullback_of_isReduced_pullback_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.AlgebraicGeometry"

universe u

noncomputable section

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp pointOfClosedPoint_apply pointOfClosedPoint LocallyOfFiniteType Spec Spec.map Scheme LocallyOfFiniteType.jacobsonSpace SpecMap_residueFieldIsoBase_inv Spec.map_injective pointEquivClosedPoint pointOfClosedPoint_comp Scheme.SpecToEquivOfField IsReduced ext_of_apply_closedPoint_eq Scheme.fromSpecResidueField_apply isReduced_of_isOpenImmersion residueFieldIsoBase isReduced_pullback_of_isReduced_pullback_of_perfectField"
namespace FiniteBC
p2m_open "AlgebraicGeometry"

variable {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k₀))
  [LocallyOfFiniteType z]

include z in

theorem discreteTopology_of_finite [Finite ↥Z] : DiscreteTopology ↥Z := by
  haveI : JacobsonSpace ↥Z := LocallyOfFiniteType.jacobsonSpace z
  infer_instance

variable {k : Type u} [Field k] (ι : k₀ →+* k)

abbrev zk : pullback z (Spec.map (CommRingCat.ofHom ι)) ⟶ Spec (CommRingCat.of k) := pullback.snd _ _

scoped instance : LocallyOfFiniteType (zk z ι) := inferInstance

def sectionsEquivOver :
    {q : Spec (CommRingCat.of k) ⟶ pullback z (Spec.map (CommRingCat.ofHom ι)) // q ≫ zk z ι = 𝟙 _} ≃
      {r : Spec (CommRingCat.of k) ⟶ Z // r ≫ z = Spec.map (CommRingCat.ofHom ι)} where
  toFun q := ⟨q.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, ← Category.assoc, q.2, Category.id_comp]⟩
  invFun r := ⟨pullback.lift r.1 (𝟙 _) (by rw [r.2, Category.id_comp]), pullback.lift_snd _ _ _⟩
  left_inv q := by
    apply Subtype.ext
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd, q.2]
  right_inv r := Subtype.ext (pullback.lift_fst _ _ _)

theorem eq_specMap_comp_pointOfClosedPoint (r : Spec (CommRingCat.of k) ⟶ Z)
    (hr : r ≫ z = Spec.map (CommRingCat.ofHom ι)) (hx : IsClosed ({r.base (IsLocalRing.closedPoint k)} : Set Z)) :
    r = Spec.map (CommRingCat.ofHom ι) ≫ pointOfClosedPoint z (r.base (IsLocalRing.closedPoint k)) hx := by

  set x := r.base (IsLocalRing.closedPoint k) with hxdef
  obtain ⟨⟨x', φ⟩, hφ⟩ : ∃ xf : Σ x, Z.residueField x ⟶ CommRingCat.of k, (Scheme.SpecToEquivOfField k Z).symm xf = r :=
    ⟨_, (Scheme.SpecToEquivOfField k Z).symm_apply_apply r⟩
  have hx' : x' = x := by
    have := congrArg (fun g : Spec (CommRingCat.of k) ⟶ Z => g.base (IsLocalRing.closedPoint k)) hφ
    simpa [Scheme.SpecToEquivOfField, Scheme.fromSpecResidueField_apply] using this
  subst hx'
  change Spec.map φ ≫ Z.fromSpecResidueField _ = r at hφ

  set e := residueFieldIsoBase z (r.base (IsLocalRing.closedPoint k)) hx with hedef
  have hφι : e.inv ≫ φ = CommRingCat.ofHom ι := by
    apply Spec.map_injective
    rw [Spec.map_comp, SpecMap_residueFieldIsoBase_inv, ← Category.assoc, hφ, hr]
  have hφ' : φ = e.hom ≫ CommRingCat.ofHom ι := by rw [← hφι, Iso.hom_inv_id_assoc]
  conv_lhs => rw [← hφ, hφ', Spec.map_comp, Category.assoc]
  rfl

variable [Finite ↥Z]

def overEquivSections :
    {r : Spec (CommRingCat.of k) ⟶ Z // r ≫ z = Spec.map (CommRingCat.ofHom ι)} ≃
      {p : Spec (CommRingCat.of k₀) ⟶ Z // p ≫ z = 𝟙 _} where
  toFun r := ⟨pointOfClosedPoint z (r.1.base (IsLocalRing.closedPoint k))
      (by haveI := discreteTopology_of_finite z; exact isClosed_discrete _), pointOfClosedPoint_comp _ _ _⟩
  invFun p := ⟨Spec.map (CommRingCat.ofHom ι) ≫ p.1, by rw [Category.assoc, p.2, Category.comp_id]⟩
  left_inv r := Subtype.ext (eq_specMap_comp_pointOfClosedPoint z ι r.1 r.2 _).symm
  right_inv p := by
    apply Subtype.ext
    apply ext_of_apply_closedPoint_eq z (pointOfClosedPoint_comp _ _ _) p.2
    rw [pointOfClosedPoint_apply]
    show p.1.base ((Spec.map (CommRingCat.ofHom ι)).base (IsLocalRing.closedPoint k)) = _
    congr 1
    exact Subsingleton.elim _ _

theorem overEquivSections_aux :
    Nonempty ({r : Spec (CommRingCat.of k) ⟶ Z // r ≫ z = Spec.map (CommRingCat.ofHom ι)} ≃
      {p : Spec (CommRingCat.of k₀) ⟶ Z // p ≫ z = 𝟙 _}) :=
  ⟨overEquivSections z ι⟩

end AlgebraicGeometry.FiniteBC
p2m_reactivate "P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.AlgebraicGeometry P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.AlgebraicGeometry.FiniteBC"
p2m_reactivate "P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.AlgebraicGeometry"

end
p2m_reactivate "P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.AlgebraicGeometry P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed.AlgebraicGeometry.FiniteBC"

open AlgebraicGeometry.FiniteBC in
theorem solution
    {k₀ : Type u} [Field k₀] [IsAlgClosed k₀] {Z : Scheme.{u}} (z : Z ⟶ Spec (CommRingCat.of k₀))
    [LocallyOfFiniteType z] [IsReduced Z] [Finite ↥Z]
    {k : Type u} [Field k] [IsAlgClosed k] (ι : k₀ →+* k) :
    IsReduced (pullback z (Spec.map (CommRingCat.ofHom ι))) ∧
      Nat.card ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) = Nat.card ↥Z := by
  constructor
  ·
    haveI : IsReduced (pullback z (𝟙 (Spec (CommRingCat.of k₀)))) :=
      isReduced_of_isOpenImmersion (pullback.fst z (𝟙 _))
    exact AlgebraicGeometry.isReduced_pullback_of_isReduced_pullback_of_perfectField z (𝟙 _) ι
      (Spec.map (CommRingCat.ofHom ι)) (Category.comp_id _).symm
  ·
    haveI : JacobsonSpace ↥Z := LocallyOfFiniteType.jacobsonSpace z
    haveI : JacobsonSpace ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) := LocallyOfFiniteType.jacobsonSpace (zk z ι)
    haveI := discreteTopology_of_finite z
    obtain ⟨e⟩ := overEquivSections_aux z ι

    have hZ : closedPoints Z = Set.univ := Set.eq_univ_of_forall fun x => isClosed_discrete _
    have eZ : ↥Z ≃ closedPoints Z := (Equiv.Set.univ _).symm.trans (Equiv.setCongr hZ.symm)
    have eK : closedPoints ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) ≃ ↥Z :=
      ((pointEquivClosedPoint (zk z ι)).symm.trans ((sectionsEquivOver z ι).trans (e.trans (pointEquivClosedPoint z)))).trans eZ.symm

    have hfin : (closedPoints ↥(pullback z (Spec.map (CommRingCat.ofHom ι)))).Finite :=
      Set.finite_coe_iff.mp (Finite.of_equiv _ eK.symm)
    haveI : DiscreteTopology ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) :=
      JacobsonSpace.discreteTopology hfin
    have hK : closedPoints ↥(pullback z (Spec.map (CommRingCat.ofHom ι))) = Set.univ :=
      Set.eq_univ_of_forall fun x => isClosed_discrete _
    calc Nat.card ↥(pullback z (Spec.map (CommRingCat.ofHom ι)))
        = Nat.card (closedPoints ↥(pullback z (Spec.map (CommRingCat.ofHom ι)))) :=
          Nat.card_congr ((Equiv.Set.univ _).symm.trans (Equiv.setCongr hK.symm))
      _ = Nat.card ↥Z := Nat.card_congr eK

#print axioms solution

end S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed
end P2MW
export P2MW.S_AlgebraicGeometry_isReduced_and_natCard_pullback_eq_of_finite_of_isAlgClosed (solution)
