-- Prove2me | solution 1 for AlgebraicGeometry.exists_normal_projective_alteration_with_smooth_integral_generic_curve
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-26T01:27:34.147908+00:00
-- url     : https://prove2.me/submissions/0826e0e4-d17f-47d6-b643-9eae8486abb8

import Mathlib
import Theorems.Thm_AlgebraicGeometry_exists_normal_projective_cover_with_integral_smooth_proper_generic_fiber_dimension_le_one
import Theorems.Thm_AlgebraicGeometry_isIntegral_genericFiber_of_isDominant
import Theorems.Thm_AlgebraicGeometry_toENat_trdeg_residueField_eq_topologicalKrullDim_closure

universe u
noncomputable section
set_option linter.style.haveILetI false

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 50000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
namespace PhilipponGenericDominance

lemma genericPoint_eq_of_dominant
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] : q (genericPoint X) = genericPoint S := by
  have h := (genericPoint_spec X).image q.continuous
  have hg : IsGenericPoint (q (genericPoint X)) (Set.univ : Set S) := by
    simpa only [Set.image_univ, q.denseRange.closure_range] using h
  exact hg.eq (genericPoint_spec S)

lemma genericFiber_inclusion
    {X S : Scheme.{u}} [IsIntegral X] [IsIntegral S]
    (q : X ⟶ S) [IsDominant q] (η : S) (hη : IsGenericPoint η Set.univ) :
    IsDominant (q.fiberι η) := by
  have hηeq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (q.fiberι (genericPoint S)) := by
    refine ⟨(q.fiberHomeo (genericPoint S)).symm
      ⟨genericPoint X, genericPoint_eq_of_dominant q⟩, ?_⟩
    exact q.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (q.fiberι (genericPoint S)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma of_recovered_generic_cover
    {C F Y X : Scheme.{u}} (e : C ⟶ Y) (f : Y ⟶ X) (a : C ⟶ F) (i : F ⟶ X)
    [Surjective a] [IsDominant i] (h : e ≫ f = a ≫ i) : IsDominant f := by
  haveI : IsDominant (e ≫ f) := by rw [h]; infer_instance
  exact IsDominant.of_comp e f

end PhilipponGenericDominance


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section
namespace PhilipponGenericDimensionFormula

abbrev residueAlgebra {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) : Algebra K (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
    X.presheaf.germ ⊤ x trivial ≫ X.residue x).hom.toAlgebra

lemma preimage_residue_comp {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) (x : X) :
    Spec.preimage (X.fromSpecResidueField x ≫ f) =
      (Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫
        X.presheaf.germ ⊤ x trivial ≫ X.residue x := by
  apply Spec.map_injective
  rw [Spec.map_preimage]
  apply ext_of_isAffine
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop,
    Scheme.fromSpecStalk_appTop]
  have ht : (Spec.map (Scheme.ΓSpecIso (.of K)).inv).appTop =
      (Scheme.ΓSpecIso Γ(Spec (.of K), ⊤)).inv := by
    apply (cancel_epi (Scheme.ΓSpecIso (.of K)).inv).mp
    exact (Scheme.ΓSpecIso_inv_naturality (Scheme.ΓSpecIso (.of K)).inv).symm
  simp
  simp only [Scheme.Hom.appTop] at ht ⊢
  rw [ht]

lemma residue_tower {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of K)) (x : X) :
    letI := residueAlgebra g (f x)
    letI := residueAlgebra (f ≫ g) x
    letI := (f.residueFieldMap x).hom.toAlgebra
    IsScalarTower K (Y.residueField (f x)) (X.residueField x) := by
  letI := residueAlgebra g (f x)
  letI := residueAlgebra (f ≫ g) x
  letI := (f.residueFieldMap x).hom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := congrArg Spec.preimage
    (congrArg (fun a => a ≫ g)
      (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField f x))
  simp only [Category.assoc, Spec.preimage_comp, Spec.preimage_map,
    preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h.symm

lemma isIso_residueFieldMap_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, ha⟩ := X.residue_surjective x z
  obtain ⟨b, hb⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  have h := congrArg (fun t : Y.presheaf.stalk (f x) ⟶ X.residueField x => t b)
    (Scheme.residue_residueFieldMap f x)
  simpa [hb, ha] using h


end PhilipponGenericDimensionFormula


set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
noncomputable section

namespace PhilipponGenericDimensionFormula

lemma isDominant_genericFiberι
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] : IsDominant (f.fiberι (genericPoint Y)) := by
  constructor
  rw [denseRange_iff_closure_range]
  have hmem : genericPoint X ∈ Set.range (f.fiberι (genericPoint Y)) := by
    refine ⟨(f.fiberHomeo (genericPoint Y)).symm
      ⟨genericPoint X, PhilipponGenericDominance.genericPoint_eq_of_dominant f⟩, ?_⟩
    exact f.fiberι_fiberHomeo_symm _ _
  have hsub : ({genericPoint X} : Set X) ⊆ Set.range (f.fiberι (genericPoint Y)) :=
    Set.singleton_subset_iff.mpr hmem
  have hcl : closure ({genericPoint X} : Set X) = Set.univ := genericPoint_spec X
  apply Set.eq_univ_of_forall
  intro x
  exact closure_mono hsub (hcl.symm ▸ Set.mem_univ x)

lemma residue_base_tower {K F : Type u} [Field K] [Field F] [Algebra K F]
    {X : Scheme.{u}} (s : X ⟶ Spec (.of F)) (x : X) :
    letI := residueAlgebra s x
    letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
    IsScalarTower K F (X.residueField x) := by
  letI := residueAlgebra s x
  letI := residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) x
  apply IsScalarTower.of_algebraMap_eq'
  simp only [RingHom.algebraMap_toAlgebra]
  have h := Spec.preimage_comp (X.fromSpecResidueField x ≫ s)
    (Spec.map (CommRingCat.ofHom (algebraMap K F)))
  rw [Spec.preimage_map] at h
  simp only [Category.assoc, preimage_residue_comp] at h
  exact congrArg CommRingCat.Hom.hom h

lemma dimension_eq_trdeg_of_genericPoint {K : Type u} [Field K]
    {X : Scheme.{u}} [IsIntegral X] (c : X ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (x : X) (hx : x = genericPoint X) :
    letI := residueAlgebra c x
    topologicalKrullDim X = (Cardinal.toENat (Algebra.trdeg K (X.residueField x)) : WithBot ℕ∞) := by
  letI := residueAlgebra c x
  have h := toENat_trdeg_residueField_eq_topologicalKrullDim_closure c x
  have hcl : closure ({x} : Set X) = Set.univ := by rw [hx]; exact genericPoint_spec X
  have hd : topologicalKrullDim X = topologicalKrullDim (closure ({x} : Set X)) := by
    rw [hcl]
    exact (IsHomeomorph.topologicalKrullDim_eq (Homeomorph.Set.univ X)
      (Homeomorph.Set.univ X).isHomeomorph).symm
  exact hd.trans h.symm

/-- Dimensions add along the actual generic fibre, with the structure-field maps retained. -/
theorem dimension_eq_add_genericFiber
    (K : Type u) [Field K] {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (c : Y ⟶ Spec (.of K)) [LocallyOfFiniteType c]
    (f : X ⟶ Y) [LocallyOfFiniteType f] [IsDominant f] :
    topologicalKrullDim X = topologicalKrullDim Y +
      topologicalKrullDim (f.fiber (genericPoint Y)) := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian (f ≫ c)
  let η := genericPoint Y
  let F := Y.residueField η
  let C := f.fiber η
  let s : C ⟶ Spec F := f.fiberToSpecResidueField η
  let t : C ⟶ X := f.fiberι η
  letI : IsIntegral C := AlgebraicGeometry.isIntegral_genericFiber_of_isDominant f
  letI : IsDominant t := isDominant_genericFiberι f
  let u := genericPoint C
  let z := t u
  let E := C.residueField u
  let L := X.residueField z
  letI : Algebra K F := residueAlgebra c η
  letI : Algebra F E := residueAlgebra s u
  letI : Algebra K E := residueAlgebra (t ≫ (f ≫ c)) u
  letI : Algebra K L := residueAlgebra (f ≫ c) z
  letI : Algebra L E := (t.residueFieldMap u).hom.toAlgebra
  letI : IsScalarTower K L E := residue_tower t (f ≫ c) u
  have hbase : t ≫ (f ≫ c) = s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    change f.fiberι η ≫ (f ≫ c) =
      f.fiberToSpecResidueField η ≫ Spec.map
        ((Scheme.ΓSpecIso (.of K)).inv ≫ c.appTop ≫
          Y.presheaf.germ ⊤ η trivial ≫ Y.residue η)
    rw [← preimage_residue_comp, Spec.map_preimage, ← Category.assoc, f.fiber_fac]
    exact Category.assoc _ _ _
  letI : IsScalarTower K F E := by
    apply IsScalarTower.of_algebraMap_eq'
    have hmap : (algebraMap F E).comp (algebraMap K F) =
        (residueAlgebra (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u).algebraMap := by
      letI : Algebra K E := residueAlgebra
        (s ≫ Spec.map (CommRingCat.ofHom (algebraMap K F))) u
      letI : IsScalarTower K F E := residue_base_tower (K := K) (F := F) s u
      exact (IsScalarTower.algebraMap_eq K F E).symm
    exact (hmap.trans (congrArg (fun a => (residueAlgebra a u).algebraMap) hbase.symm)).symm
  letI : IsIso (t.residueFieldMap u) := isIso_residueFieldMap_of_isPreimmersion t u
  let e : L ≃ₐ[K] E := AlgEquiv.ofBijective (IsScalarTower.toAlgHom K L E)
    (ConcreteCategory.bijective_of_isIso (t.residueFieldMap u))
  have he : Algebra.trdeg K L = Algebra.trdeg K E := e.trdeg_eq
  letI : LocallyOfFiniteType s := MorphismProperty.pullback_snd f
    (Y.fromSpecResidueField η) (inferInstance : LocallyOfFiniteType f)
  have hX := dimension_eq_trdeg_of_genericPoint (f ≫ c) z (PhilipponGenericDominance.genericPoint_eq_of_dominant t)
  have hY := dimension_eq_trdeg_of_genericPoint c η rfl
  have hC := dimension_eq_trdeg_of_genericPoint (K := F) s u rfl
  rw [hX, hY, hC]
  change (Cardinal.toENat (Algebra.trdeg K L) : WithBot ℕ∞) =
    (Cardinal.toENat (Algebra.trdeg K F) : WithBot ℕ∞) +
      (Cardinal.toENat (Algebra.trdeg F E) : WithBot ℕ∞)
  rw [he, ← trdeg_add_eq K F (A := E)]
  simp only [map_add, WithBot.coe_add]

end PhilipponGenericDimensionFormula



set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace PhilipponAlterationDimensionControl

lemma finite_of_dimension_le_zero
    (K : Type u) [Field K] {X : Scheme.{u}} [IsIntegral X]
    (π : X ⟶ Spec (.of K)) [LocallyOfFiniteType π]
    (hd : topologicalKrullDim X ≤ 0) : IsFinite π := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian π
  letI : IsLocallyArtinian X := .of_topologicalKrullDim_le_zero hd
  letI : Subsingleton X := Set.subsingleton_univ_iff.mp
    ((isDiscrete_univ_iff.mpr (inferInstance : DiscreteTopology X)).subsingleton_of_isPreirreducible
      PreirreducibleSpace.isPreirreducible_univ)
  exact (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := π)).mpr inferInstance

lemma dimension_nonneg (X : Scheme.{u}) [IsIntegral X] :
    0 ≤ topologicalKrullDim X := by
  change 0 ≤ Order.krullDim (IrreducibleCloseds X)
  letI : Nonempty (IrreducibleCloseds X) := ⟨{
    carrier := Set.univ
    isIrreducible' := IrreducibleSpace.isIrreducible_univ X
    isClosed' := isClosed_univ }⟩
  exact Order.krullDim_nonneg

lemma eq_one_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : ((r + 1 : ℕ) : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 1 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 1 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [Nat.cast_add, Nat.cast_one,
        WithBot.coe_add, WithBot.coe_natCast, WithBot.coe_one] using h)
    have hd : d = 1 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

lemma eq_zero_of_nat_add_eq (r : ℕ) (d : WithBot ℕ∞)
    (h : (r : WithBot ℕ∞) = (r : WithBot ℕ∞) + d) : d = 0 := by
  cases d with
  | bot => simp at h
  | coe d =>
    have he : (r : ℕ∞) + 0 = (r : ℕ∞) + d := by
      exact WithBot.coe_injective (by simpa only [add_zero,
        WithBot.coe_add, WithBot.coe_natCast] using h)
    have hd : d = 0 := (ENat.add_right_injective_of_ne_top (by simp) he).symm
    simp [hd]

/-- The controlled generic curve forces the covering model to preserve
dimension. Its map to the original variety has zero-dimensional generic fibre. -/
theorem dimension_eq_and_genericFiber_dimensions
    (K : Type u) [Field K] {G X N : Scheme.{u}}
    [IsIntegral G] [IsIntegral X] [IsIntegral N]
    (πX : X ⟶ Spec (.of K)) [LocallyOfFiniteType πX]
    (πN : N ⟶ Spec (.of K)) [LocallyOfFiniteType πN]
    (a : G ⟶ X) [LocallyOfFiniteType a] [IsDominant a]
    (f : G ⟶ N) [LocallyOfFiniteType f] [IsDominant f]
    (r : ℕ) (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞))
    (hdN : topologicalKrullDim N = (r : WithBot ℕ∞))
    (hdF : topologicalKrullDim (f.fiber (genericPoint N)) ≤ 1) :
    topologicalKrullDim G = topologicalKrullDim X ∧
      topologicalKrullDim (f.fiber (genericPoint N)) = 1 ∧
      topologicalKrullDim (a.fiber (genericPoint X)) = 0 := by
  have ha := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πX a
  have hf := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber K πN f
  haveI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (a ≫ πX)
  haveI : IsIntegral (a.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant a
  have hza := dimension_nonneg (a.fiber (genericPoint X))
  have hlow : topologicalKrullDim X ≤ topologicalKrullDim G := by
    calc
      topologicalKrullDim X = topologicalKrullDim X + 0 := (add_zero _).symm
      _ ≤ topologicalKrullDim X + topologicalKrullDim (a.fiber (genericPoint X)) :=
        add_le_add (le_refl _) hza
      _ = topologicalKrullDim G := ha.symm
  have hhigh : topologicalKrullDim G ≤ topologicalKrullDim X := by
    calc
      topologicalKrullDim G = (r : WithBot ℕ∞) +
          topologicalKrullDim (f.fiber (genericPoint N)) := hf.trans (by rw [hdN])
      _ ≤ (r : WithBot ℕ∞) + 1 := add_le_add (le_refl _) hdF
      _ = topologicalKrullDim X := by rw [hdX]; simp
  have heq := le_antisymm hhigh hlow
  refine ⟨heq, eq_one_of_nat_add_eq r _ ?_, eq_zero_of_nat_add_eq (r + 1) _ ?_⟩
  · simpa only [heq, hdX, hdN] using hf
  · simpa only [heq, hdX] using ha

end PhilipponAlterationDimensionControl


set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
attribute [local instance] MvPolynomial.gradedAlgebra
namespace PhilipponNormalCurveAlterationModel

/-- Apply the accepted finite-generic-field covering data and its global
normal projective completion to the original projective fibration. -/
theorem exists_normal_curve_alteration_model
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (r : ℕ) (hdS : topologicalKrullDim S = (r : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ topologicalKrullDim G = topologicalKrullDim X ∧
      IsFinite (fX.fiberToSpecResidueField (genericPoint X)) ∧
      IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) = 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  have hq := PhilipponGenericDimensionFormula.dimension_eq_add_genericFiber k πS q
  have hcurve : topologicalKrullDim (q.fiber (genericPoint S)) = 1 :=
    PhilipponAlterationDimensionControl.eq_one_of_nat_add_eq r _ (by
      simpa only [hdX, hdS] using hq)
  obtain ⟨N, qN, U, u, W, pW, G, fX, fN, tW,
    hN, hnN, hqN, hsqN, hdN, hU, hu, hdu, hsmU,
    hW, hsmW, hprW, hsurW, habsW, hG, hnG, hfX, hsfX, hfN, hsfN,
    htW, hdtW, hpull, hgeneric, hcomm, hcomp, hdG, hembN, hembG⟩ :=
    AlgebraicGeometry.exists_normal_projective_cover_with_integral_smooth_proper_generic_fiber_dimension_le_one
      k πS mS iS hiS πX mX iX hiX q hqπ (genericPoint S) (genericPoint_spec S) hcurve.le
  letI : IsIntegral N := hN
  letI : IsIntegral G := hG
  letI : IsProper qN := hqN
  letI : IsProper fX := hfX
  letI : Surjective fX := hsfX
  letI : IsProper fN := hfN
  letI : Surjective fN := hsfN
  obtain ⟨hdGX, hdimF, hdimX⟩ :=
    PhilipponAlterationDimensionControl.dimension_eq_and_genericFiber_dimensions
      k πX (qN ≫ πS) fX fN r hdX (hdN.trans hdS)
      (hgeneric (genericPoint N) (genericPoint_spec N)).2.2.2
  letI : IsLocallyNoetherian G := LocallyOfFiniteType.isLocallyNoetherian (fX ≫ πX)
  letI : IsIntegral (fX.fiber (genericPoint X)) :=
    AlgebraicGeometry.isIntegral_genericFiber_of_isDominant fX
  letI : LocallyOfFiniteType (fX.fiberToSpecResidueField (genericPoint X)) :=
    MorphismProperty.pullback_snd fX (X.fromSpecResidueField (genericPoint X)) inferInstance
  have hfin := PhilipponAlterationDimensionControl.finite_of_dimension_le_zero
    (X.residueField (genericPoint X)) (fX.fiberToSpecResidueField (genericPoint X)) hdimX.le
  have hgeneric' (ηN : N) (hηN : IsGenericPoint ηN Set.univ) :
      IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
      IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) = 1 := by
    obtain ⟨hi, hs, hp, _hd⟩ := hgeneric ηN hηN
    refine ⟨hi, hs, hp, ?_⟩
    have he : ηN = genericPoint N := hηN.eq (genericPoint_spec N)
    exact (congrArg (fun x : N => topologicalKrullDim (fN.fiber x)) he).trans hdimF
  exact ⟨N, qN, U, u, W, pW, G, fX, fN, tW,
    hN, hnN, hqN, hsqN, hdN, hU, hu, hdu, hsmU,
    hW, hsmW, hprW, hsurW, habsW, hG, hnG, hfX, hsfX, hdGX, hfin, hfN, hsfN,
    htW, hdtW, hpull, hgeneric', hcomm, hcomp, hdG, hembN, hembG⟩

end PhilipponNormalCurveAlterationModel

theorem solution
    (k : Type u) [Field k] [PerfectField k] {S X : Scheme.{u}} [IsIntegral S] [IsIntegral X]
    (πS : S ⟶ Spec (.of k)) [IsProper πS]
    (mS : ℕ) (iS : S ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mS + 1)) k))
    [IsClosedImmersion iS] (hiS : iS ≫ ProjSpace.π k mS = πS)
    (πX : X ⟶ Spec (.of k)) [IsProper πX]
    (mX : ℕ) (iX : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (mX + 1)) k))
    [IsClosedImmersion iX] (hiX : iX ≫ ProjSpace.π k mX = πX)
    (q : X ⟶ S) [IsProper q] [IsDominant q] (hqπ : q ≫ πS = πX)
    (r : ℕ) (hdS : topologicalKrullDim S = (r : WithBot ℕ∞))
    (hdX : topologicalKrullDim X = ((r + 1 : ℕ) : WithBot ℕ∞)) :
    ∃ (N : Scheme.{u}) (qN : N ⟶ S) (U : Scheme.{u}) (u : U ⟶ N)
      (W : Scheme.{u}) (pW : W ⟶ U) (G : Scheme.{u})
      (fX : G ⟶ X) (fN : G ⟶ N) (tW : W ⟶ G),
      IsIntegral N ∧ (∀ x : N, IsIntegrallyClosed (N.presheaf.stalk x)) ∧
      IsProper qN ∧ Surjective qN ∧ topologicalKrullDim N = topologicalKrullDim S ∧
      IsIntegral U ∧ IsOpenImmersion u ∧ IsDominant u ∧ Smooth (u ≫ qN ≫ πS) ∧
      IsIntegral W ∧ Smooth pW ∧ IsProper pW ∧ Surjective pW ∧
      Smooth (pW ≫ u ≫ qN ≫ πS) ∧
      IsIntegral G ∧ (∀ x : G, IsIntegrallyClosed (G.presheaf.stalk x)) ∧
      IsProper fX ∧ Surjective fX ∧ topologicalKrullDim G = topologicalKrullDim X ∧
      IsFinite (fX.fiberToSpecResidueField (genericPoint X)) ∧
      IsProper fN ∧ Surjective fN ∧
      IsOpenImmersion tW ∧ IsDominant tW ∧ IsPullback tW pW fN u ∧
      (∀ ηN : N, IsGenericPoint ηN Set.univ →
        IsIntegral (fN.fiber ηN) ∧ Smooth (fN.fiberToSpecResidueField ηN) ∧
        IsProper (fN.fiberToSpecResidueField ηN) ∧ topologicalKrullDim (fN.fiber ηN) = 1) ∧
      fX ≫ q = fN ≫ qN ∧ fX ≫ πX = fN ≫ qN ≫ πS ∧
      topologicalKrullDim G = topologicalKrullDim W ∧
      (∃ (dN : ℕ) (jN : N ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dN + 1)) k)),
        IsClosedImmersion jN ∧ jN ≫ ProjSpace.π k dN = qN ≫ πS) ∧
      ∃ (dG : ℕ) (jG : G ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (dG + 1)) k)),
        IsClosedImmersion jG ∧ jG ≫ ProjSpace.π k dG = fX ≫ πX := by
  exact PhilipponNormalCurveAlterationModel.exists_normal_curve_alteration_model k πS mS iS hiS πX mX iX hiX q hqπ r hdS hdX
