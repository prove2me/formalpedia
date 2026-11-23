-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
-- name    : Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ProdIrrAndWeakNeron
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:48:23.792273+00:00
-- url     : https://prove2.me/theorems/a3492db9-b357-47bd-a93b-65e83a3f155a
-- title:
--   Prod Irr And Weak Neron
-- statement:
--   Definitions and structural lemmas for Prod Irr And Weak Neron, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ProdIrrAndWeakNeron.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeometricallyIntegralOfIsIntegralOfIsAlgClosed
import Theorems.Thm_GlobalTheory_geometricallyIrreducible_of_isAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.SS
theorem isIrreducible_fibre_pullback {X Y S : Scheme.{0}} (f : X ⟶ S) (g : Y ⟶ S) [LocallyOfFiniteType f]
    {k : Type} [Field k] [IsAlgClosed k] (i : Spec (.of k) ⟶ S) [IsClosedImmersion i]
    (hf : IsIrreducible (f ⁻¹' Set.range i)) (hg : IsIrreducible (g ⁻¹' Set.range i)) :
    IsIrreducible ((pullback.fst f g ≫ f) ⁻¹' Set.range i) := by
  have irr : ∀ {X : Scheme.{0}} (f : X ⟶ S), IsIrreducible (f ⁻¹' Set.range i) →
      IrreducibleSpace ↥(pullback f i) := by
    intro X f h
    rw [← Scheme.Pullback.range_fst] at h
    have e := (pullback.fst f i).isClosedEmbedding.isEmbedding
    have := Subtype.irreducibleSpace h
    exact e.toHomeomorph.irreducibleSpace_iff.2 this
  have h1 := irr f hf
  have h2 := irr g hg
  have h3 : GeometricallyIrreducible (pullback.snd f i) := geometricallyIrreducible_of_isAlgClosed _
  have h4 : IrreducibleSpace ↥(pullback (pullback.snd f i) (pullback.snd g i)) := inferInstance
  let m := pullback.map (pullback.snd f i) (pullback.snd g i) f g (pullback.fst f i) (pullback.fst g i) i
    pullback.condition.symm pullback.condition.symm
  have hm : Set.range m = (pullback.fst f g ≫ f) ⁻¹' Set.range i := by
    rw [Scheme.Pullback.range_map, Scheme.Pullback.range_fst, Scheme.Pullback.range_fst]
    ext z
    have hz : g (pullback.snd f g z) = f (pullback.fst f g z) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
    simp only [Set.mem_inter_iff, Set.mem_preimage, Scheme.Hom.comp_apply, hz, and_self]
  rw [← hm, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ _).image _ m.continuous.continuousOn
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A A' : Over (Sp K)}
theorem Model.j_comp_of_comm (M : Model R A) (N : Model R A') (f : A ⟶ A') (g : M.Y ⟶ N.Y)
    (h : M.e.inv ≫ (Over.pullback (spMap (algebraMap R K))).map g = f ≫ N.e.inv) :
    M.j ≫ g.left = f.left ≫ N.j := by
  have h2 := congrArg (fun q => q.left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))) h
  have h4 : ((Over.pullback (spMap (algebraMap R K))).map g).left ≫ pullback.fst N.Y.hom (spMap (algebraMap R K))
      = pullback.fst M.Y.hom (spMap (algebraMap R K)) ≫ g.left := pullback.lift_fst _ _ _
  simp only [Over.comp_left, Category.assoc] at h2
  unfold Model.j
  rw [Category.assoc]
  exact (congrArg (fun q => M.e.inv.left ≫ q) h4).symm.trans h2
theorem Model.prod_j_fst (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (fst M.Y N.Y).left = (fst A A').left ≫ M.j :=
  Model.j_comp_of_comm (M.prod N) M (fst A A') (fst M.Y N.Y) (by simp [Model.prod])
theorem Model.prod_j_snd (M : Model R A) (N : Model R A') :
    (M.prod N).j ≫ (snd M.Y N.Y).left = (snd A A').left ≫ N.j :=
  Model.j_comp_of_comm (M.prod N) N (snd A A') (snd M.Y N.Y) (by simp [Model.prod])
theorem Model.sp_eq_preimage [IsLocalRing R] (M : Model R A) :
    M.sp = M.Y.hom ⁻¹' Set.range (spMap (IsLocalRing.residue R)) := by
  have : Set.range (spMap (IsLocalRing.residue R)) = {IsLocalRing.closedPoint R} := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint _)]
      exact IsLocalRing.comap_closedPoint (IsLocalRing.residue R)
    · rintro rfl
      exact ⟨IsLocalRing.closedPoint _, IsLocalRing.comap_closedPoint (IsLocalRing.residue R)⟩
  rw [this]; rfl
theorem Model.Irr.prod [IsLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)] {M : Model R A} {N : Model R A'}
    (hM : M.Irr) (hN : N.Irr) : (M.prod N).Irr := by
  have := M.smooth
  have : IsClosedImmersion (spMap (IsLocalRing.residue R)) :=
    IsClosedImmersion.spec_of_surjective _ IsLocalRing.residue_surjective
  unfold Model.Irr at *
  rw [Model.sp_eq_preimage] at *
  exact isIrreducible_fibre_pullback M.Y.hom N.Y.hom (spMap (IsLocalRing.residue R)) hM hN
theorem WeakNeron.prod [IsLocalRing R] {I I' : Type} {M : I → Model R A} {N : I' → Model R A'}
    (hM : WeakNeron M) (hN : WeakNeron N) : WeakNeron (fun p : I × I' => (M p.1).prod (N p.2)) := by
  intro R' K' _ _ _ _ _ _ _ hm a ha
  obtain ⟨i, b, hb, hb'⟩ := hM R' K' hm (a ≫ (fst A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (fst A A'), Category.assoc])
  obtain ⟨i', c, hc, hc'⟩ := hN R' K' hm (a ≫ (snd A A').left) (by
    rw [Category.assoc, ← ha, ← Over.w (snd A A'), Category.assoc])
  have e1 := Model.prod_j_fst (M i) (N i')
  have e2 := Model.prod_j_snd (M i) (N i')
  refine ⟨(i, i'), pullback.lift (f := (M i).Y.hom) (g := (N i').Y.hom) b c (hb.trans hc.symm), ?_, ?_⟩
  · exact (pullback.lift_fst_assoc _ _ _ _).trans hb
  · refine pullback.hom_ext (f := (M i).Y.hom) (g := (N i').Y.hom) ?_ ?_
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)).trans (hb'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e1.symm)
    · refine ((Category.assoc _ _ _).trans ?_).trans (Category.assoc _ _ _).symm
      refine (congrArg (_ ≫ ·) (pullback.lift_snd _ _ _)).trans (hc'.trans ?_)
      exact (Category.assoc _ _ _).trans (congrArg (a ≫ ·) e2.symm)
end GlobalTheory.SS


