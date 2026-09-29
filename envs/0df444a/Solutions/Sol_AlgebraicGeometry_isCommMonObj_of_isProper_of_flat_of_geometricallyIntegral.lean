-- Prove2me | solution 1 for AlgebraicGeometry.isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/318cba67-8e5b-5281-8a2e-f5846e0acd2e

import Mathlib
import Theorems.Thm_AlgebraicGeometry_comp_section_comp_eq_of_isClosedMap_of_surjective_app
import Theorems.Thm_AlgebraicGeometry_bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AlgebraicGeometry_isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
p2m_attr_erase "instance" "AlgebraicGeometry.SubalgebraStages.compactSpace_pullback AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_pullback AlgebraicGeometry.SubalgebraStages.compactSpace_obj AlgebraicGeometry.SubalgebraStages.quasiSeparatedSpace_obj AlgebraicGeometry.SubalgebraStages.quasiCompact_snd AlgebraicGeometry.SubalgebraStages.isAffineHom_leg AlgebraicGeometry.SubalgebraStages.isAffineHom_trans AlgebraicGeometry.SubalgebraStages.isAffineHom_diagram_map AlgebraicGeometry.SubalgebraStages.quasiSeparated_snd AlgebraicGeometry.SubalgebraStages.isCofiltered_op IsDirectLimit.Module.instDirectLimitCoeLinearMapIdOfOfNonempty AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "AlgebraicGeometry.SubalgebraStages.specCone_π_app AlgebraicGeometry.SubalgebraStages.specLeg_specHom AlgebraicGeometry.SubalgebraStages.specLeg_specTrans AlgebraicGeometry.SubalgebraStages.cone_pt AlgebraicGeometry.SubalgebraStages.trans_fst AlgebraicGeometry.SubalgebraStages.diagram_obj AlgebraicGeometry.SubalgebraStages.leg_snd AlgebraicGeometry.SubalgebraStages.diagram_map AlgebraicGeometry.SubalgebraStages.specTrans_refl AlgebraicGeometry.SubalgebraStages.trans_snd AlgebraicGeometry.SubalgebraStages.specTrans_specHom AlgebraicGeometry.SubalgebraStages.specCone_pt AlgebraicGeometry.SubalgebraStages.cone_π_app AlgebraicGeometry.SubalgebraStages.specDiagram_map AlgebraicGeometry.SubalgebraStages.specDiagram_obj AlgebraicGeometry.SubalgebraStages.leg_fst AlgebraicGeometry.SubalgebraStages.leg_trans IsDirectLimit.Module.linearEquiv_symm_apply IsDirectLimit.linearEquiv_symm_apply IsDirectLimit.lift_of IsDirectLimit.Module.linearEquiv_apply IsDirectLimit.Module.lift_of IsDirectLimit.Equiv_apply AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq"

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

universe u

namespace SolAbelianSchemeComm

p2m_open "MonObj CategoryTheory.MonObj TopologicalSpace Opposite"

set_option backward.isDefEq.respectTransparency false in

theorem pullback_map_commutator_eq {R : Type u} [CommRing R]
    (G : Over (Spec (.of R))) [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G]
    {K : Type u} [Field K] (k : Spec (.of K) ⟶ Spec (.of R)) :
    (Over.pullback k).map (GrpObj.commutator G) =
      (Over.pullback k).map (toUnit (G ⊗ G) ≫ η[G]) := by
  let G' := (Over.pullback k).obj G
  have : IsProper G'.hom := by dsimp [G']; infer_instance
  have : GeometricallyIntegral G'.hom := by dsimp [G']; infer_instance
  let : GrpObj G' := Functor.grpObjObj
  have := isCommMonObj_of_isProper_of_geometricallyIntegral G'
  rw [isCommMonObj_iff_commutator_eq_toUnit_η] at this
  rw [← cancel_epi (Functor.Monoidal.μIso (Over.pullback k) G G).hom]
  dsimp [GrpObj.commutator] at this ⊢
  simpa only [Functor.map_mul, one_eq_one, comp_one, Functor.map_one, Functor.map_inv',
    comp_mul, GrpObj.comp_inv, Functor.Monoidal.μIso_hom, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_snd]

set_option backward.isDefEq.respectTransparency false in

theorem commutator_apply_eq {R : Type u} [CommRing R]
    (G : Over (Spec (.of R))) [IsProper G.hom] [GeometricallyIntegral G.hom] [GrpObj G]
    (x : (G ⊗ G).left) :
    (GrpObj.commutator G).left x = η[G].left ((G ⊗ G).hom x) := by
  let k := (Spec (.of R)).fromSpecResidueField ((G ⊗ G).hom x)
  obtain ⟨x', hx'⟩ : x ∈ Set.range (pullback.fst (G ⊗ G).hom k) := by
    rw [Scheme.Pullback.range_fst]
    simp [k]
  have EQN := pullback_map_commutator_eq G k
  have h1 : ∀ φ : G ⊗ G ⟶ G, pullback.fst (G ⊗ G).hom k ≫ φ.left =
      ((Over.pullback k).map φ).left ≫ pullback.fst G.hom k := by
    intro φ
    simp
  have hmor : pullback.fst (G ⊗ G).hom k ≫ (GrpObj.commutator G).left
      = pullback.fst (G ⊗ G).hom k ≫ (toUnit (G ⊗ G) ≫ η[G]).left := by
    rw [h1, h1, EQN]
  have h2 := congr($hmor x')
  simp only [Scheme.Hom.comp_apply, hx'] at h2
  rw [h2, Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem main {R : Type u} [CommRing R]
    (G : Over (Spec (CommRingCat.of R))) [IsProper G.hom] [Flat G.hom]
    [LocallyOfFinitePresentation G.hom] [GeometricallyIntegral G.hom] [GrpObj G] :
    IsCommMonObj G := by

  let p : (G ⊗ G).left ⟶ G.left := (snd G G).left
  let εo : G ⟶ G ⊗ G := (λ_ G).inv ≫ η[G] ▷ G
  let ε : G.left ⟶ (G ⊗ G).left := εo.left
  have hεo : εo ≫ snd G G = 𝟙 G := by simp [εo]
  have hε : ε ≫ p = 𝟙 G.left := by
    change (εo ≫ snd G G).left = (𝟙 G : G ⟶ G).left
    rw [hεo]

  have : IsProper p := by dsimp [p]; infer_instance
  have : Flat p := by dsimp [p]; infer_instance
  have : LocallyOfFinitePresentation p := by dsimp [p]; infer_instance
  have : GeometricallyIntegral p := by dsimp [p]; infer_instance
  have : GeometricallyConnected p := ⟨fun K _ y Z fst snd h ↦ by
    have : IrreducibleSpace Z := GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ h
    infer_instance⟩
  have hp : IsClosedMap p := p.isClosedMap

  have hH0 : ∀ U : G.left.Opens, IsAffineOpen U → Function.Surjective (p.app U) :=
    fun U _ ↦
      (bijective_app_of_isProper_of_flat_of_geometricallyReduced_of_geometricallyConnected p U).2

  let f : (G ⊗ G).left ⟶ G.left := (GrpObj.commutator G).left
  have hεf : εo ≫ GrpObj.commutator G = toUnit G ≫ η[G] := by
    simp [εo]
  have hf : ∀ x, f (ε (p x)) = f x := by
    intro x
    change (ε ≫ f) (p x) = f x
    have : ε ≫ f = (toUnit G ≫ η[G]).left := by
      change (εo ≫ GrpObj.commutator G).left = _
      rw [hεf]
    rw [this, commutator_apply_eq G x, Over.comp_left, Over.toUnit_left, Scheme.Hom.comp_apply]
    congr 1
    change ((snd G G).left ≫ G.hom) x = (G ⊗ G).hom x
    rw [Over.w]

  have RIG := comp_section_comp_eq_of_isClosedMap_of_surjective_app p ε hε hp hH0 f hf
  rw [isCommMonObj_iff_commutator_eq_toUnit_η]
  apply Over.OverMorphism.ext
  change f = _
  rw [← RIG]
  change (snd G G ≫ εo ≫ GrpObj.commutator G).left = (toUnit (G ⊗ G) ≫ η[G]).left
  rw [hεf, comp_toUnit_assoc]

end SolAbelianSchemeComm

open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory in
theorem solution
    {R : Type u} [CommRing R]
    (G : Over (Spec (CommRingCat.of R))) [IsProper G.hom] [Flat G.hom]
    [LocallyOfFinitePresentation G.hom] [GeometricallyIntegral G.hom] [GrpObj G] :
    IsCommMonObj G :=
  SolAbelianSchemeComm.main G

end S_AlgebraicGeometry_isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral
end P2MW
export P2MW.S_AlgebraicGeometry_isCommMonObj_of_isProper_of_flat_of_geometricallyIntegral (solution)
