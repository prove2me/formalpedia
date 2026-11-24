-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.isIso_etale_restrictGlobalSections_of_separably_closed_field_extension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-24T01:57:26.437991+00:00
-- url     : https://prove2.me/submissions/f5d8b9fb-7fe6-4848-ae64-b5b8d0dadefb

import Definitions.Def_AlgebraicGeometry_EtaleDirectImageSectionGerms
import Definitions.Def_AlgebraicGeometry_EtaleFiniteSectionLifts
import Definitions.Def_AlgebraicGeometry_EtaleStrictHenselianSectionGerms
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.Topology.Irreducible
import Mathlib.Topology.JacobsonSpace
import Mathlib.Topology.LocallyConstant.Basic

set_option maxHeartbeats 1800000

noncomputable section

section

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace


namespace PhilipponEtaleConstantDegreeZero

universe u
variable (X : Scheme.{u}) (A : Type u) [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A]

private def constantMap : (Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of A) ⟶
    (continuousSheaf X A).obj where
  app W := AddCommGrpCat.ofHom
    { toFun := fun a => ContinuousMap.const W.unop.left a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  naturality := by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro a
    apply ContinuousMap.ext
    intro x
    rfl

private theorem constantMap_locallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W a b hab
  by_cases h : a = b
  · subst b
    rw [Presheaf.equalizerSieve_self_eq_top]
    exact X.smallEtaleTopology.top_mem _
  · have hW : IsEmpty W.unop.left := ⟨fun x => h (congrArg (fun f : C(W.unop.left, A) => f x) hab)⟩
    let V : Fin 0 → X.Etale := fun _ => W.unop
    let r : ∀ i, V i ⟶ W.unop := fun _ => 𝟙 W.unop
    have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W.unop :=
      (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr (Set.eq_univ_of_forall fun x => isEmptyElim x)
    apply X.smallEtaleTopology.superset_covering _ hcover
    apply (Sieve.generate_le_iff _ _).mpr
    rintro _ _ ⟨i⟩
    exact Fin.elim0 i

private theorem constantMap_locallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantMap X A) := by
  constructor
  intro W s
  change C(W.left, A) at s
  let U (a : A) : W.left.Opens := ⟨s ⁻¹' {a}, (isOpen_discrete {a}).preimage s.continuous⟩
  let V (a : A) := Scheme.Etale.mk ((U a).ι ≫ W.hom)
  let r (a : A) : V a ⟶ W := MorphismProperty.Over.homMk (U a).ι rfl
  have hcover : Sieve.ofArrows V r ∈ X.smallEtaleTopology W := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff r).mpr
    apply Set.eq_univ_of_forall
    intro x
    exact Set.mem_iUnion.mpr ⟨s x, ⟨⟨x, rfl⟩, rfl⟩⟩
  apply X.smallEtaleTopology.superset_covering _ hcover
  apply (Sieve.generate_le_iff _ _).mpr
  rintro _ _ ⟨a⟩
  refine ⟨a, ?_⟩
  apply ContinuousMap.ext
  intro x
  exact x.property.symm

/-- For discrete coefficients, sheafifying constant functions gives the
small étale sheaf of continuous functions. -/
def constantSheafIso : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
    (AddCommGrpCat.of A) ≅ continuousSheaf X A := by
  let J := X.smallEtaleTopology
  let G := presheafToSheaf J AddCommGrpCat.{u}
  have h := (J.W_iff_isLocallyBijective (constantMap X A)).mpr
    ⟨constantMap_locallyInjective X A, constantMap_locallySurjective X A⟩
  let : IsIso (G.map (constantMap X A)) := (J.W_iff _).mp h
  exact (asIso (G.map (constantMap X A))).trans (sheafificationIso (continuousSheaf X A)).symm


end PhilipponEtaleConstantDegreeZero

end

section

open Set

/-- An open map to an irreducible Jacobson space has irreducible source
if the source is nonempty and the fibers at closed points are irreducible. -/
theorem irreducibleSpace_of_isOpenMap_closedFibers
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    [IrreducibleSpace Y] [JacobsonSpace Y] (f : X → Y) (hf : IsOpenMap f)
    (hFibers : ∀ y : Y, IsClosed {y} → IsPreirreducible (f ⁻¹' {y})) :
    IrreducibleSpace X := by
  let : PreirreducibleSpace X := PreirreducibleSpace.of_forall_nonempty_inter (by
    intro U V hU hV hUn hVn
    have hOpen : IsOpen (f '' U ∩ f '' V) := (hf U hU).inter (hf V hV)
    have hNonempty := nonempty_preirreducible_inter (hf U hU) (hf V hV)
      (hUn.image f) (hVn.image f)
    obtain ⟨y, ⟨⟨hyU, hyV⟩, hy⟩⟩ := nonempty_inter_closedPoints hNonempty hOpen.isLocallyClosed
    obtain ⟨u, hu, rfl⟩ := hyU
    obtain ⟨v, hv, hvu⟩ := hyV
    obtain ⟨x, _, hxU, hxV⟩ := hFibers (f u) hy U V hU hV ⟨u, rfl, hu⟩ ⟨v, hvu, hv⟩
    exact ⟨x, hxU, hxV⟩)
  exact ⟨inferInstance⟩


open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace PhilipponIrreducibleOverJacobson

universe u

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Extension of a separably closed base field preserves irreducibility
for locally finite-type schemes. -/
theorem irreducibleSpace_pullback_of_isSepClosed {L E : Type u}
    [Field L] [IsSepClosed L] [Field E] [Algebra L E]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of L)) [LocallyOfFiniteType f] [IrreducibleSpace X] :
    IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap L E)))) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap L E))
  let q := pullback.fst f g
  let zE : Spec (.of E) := default
  let : Surjective g := ⟨fun y => ⟨zE, Subsingleton.elim _ _⟩⟩
  let : Nonempty ↥(pullback f g) := ⟨(q.surjective (Classical.choice inferInstance)).choose⟩
  let : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace f
  apply irreducibleSpace_of_isOpenMap_closedFibers q q.isOpenMap
  intro x hx
  let s := X.fromSpecResidueField x
  let m := s ≫ f
  let φ := Spec.preimage m
  let : Algebra L (X.residueField x) := φ.hom.toAlgebra
  let : IsClosedImmersion s := isClosed_singleton_iff_isClosedImmersion.mp hx
  let : IsFinite m := (isFinite_iff_locallyOfFiniteType_of_jacobsonSpace (f := m)).mpr inferInstance
  have hm : Spec.map φ = m := Spec.map_preimage _
  let : Module.Finite L (X.residueField x) := RingHom.finite_algebraMap.mp
    ((IsFinite.SpecMap_iff φ).mp (hm ▸ (inferInstance : IsFinite m)))
  let e := pullbackSymmetry q s ≪≫ pullbackRightPullbackFstIso f g s ≪≫ pullbackSymmetry m g
  have hAlg : m = Spec.map (CommRingCat.ofHom (algebraMap L (X.residueField x))) := hm.symm
  let e' : q.fiber x ≅ Spec (.of (E ⊗[L] X.residueField x)) :=
    e ≪≫ eqToIso (congrArg (pullback g ·) hAlg) ≪≫ pullbackSpecIso L E (X.residueField x)
  have hH := PrimeSpectrum.isHomeomorph_comap_of_isPurelyInseparable L (X.residueField x) E
  let : IrreducibleSpace (Spec (.of (E ⊗[L] X.residueField x))) :=
    (IsHomeomorph.homeomorph _ hH).irreducibleSpace_iff.mpr inferInstance
  let : IrreducibleSpace (q.fiber x) := e'.hom.homeomorph.irreducibleSpace_iff.mpr inferInstance
  rw [← q.range_fiberι x, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ (q.fiber x)).isPreirreducible.image _
    (q.fiberι x).continuous.continuousOn

open Algebra.TensorProduct in
/-- The tensor product of a domain and a field over a separably closed
field has prime nilradical. Each pair of elements comes from a finite-type stage. -/
theorem irreducibleSpace_tensorProduct {L M E : Type u} [Field L] [IsSepClosed L]
    [CommRing M] [IsDomain M] [Algebra L M] [Field E] [Algebra L E] :
    IrreducibleSpace (PrimeSpectrum (M ⊗[L] E)) := by
  apply PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mpr
  refine Ideal.isPrime_iff.mpr ⟨(Ideal.ne_top_iff_one _).mpr ?_, ?_⟩
  · rw [mem_nilradical]
    exact not_isNilpotent_one
  intro x y hxy
  let stage (A : Subalgebra L M) := Algebra.TensorProduct.map A.val (AlgHom.id L E)
  have stage_comp {A B : Subalgebra L M} (h : A ≤ B) (a : A ⊗[L] E) :
      stage B (Algebra.TensorProduct.map (Subalgebra.inclusion h) (AlgHom.id L E) a) = stage A a := by
    dsimp only [stage]
    rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp B.val (Subalgebra.inclusion h)
      (AlgHom.id L E) (AlgHom.id L E), Subalgebra.val_comp_inclusion, AlgHom.id_comp]
  obtain ⟨A, hA, a, ha⟩ := TensorProduct.Algebra.exists_of_fg x
  obtain ⟨B, hB, b, hb⟩ := TensorProduct.Algebra.exists_of_fg y
  let C := A ⊔ B
  let u := Algebra.TensorProduct.map (Subalgebra.inclusion (show A ≤ C from le_sup_left)) (AlgHom.id L E) a
  let v := Algebra.TensorProduct.map (Subalgebra.inclusion (show B ≤ C from le_sup_right)) (AlgHom.id L E) b
  have hu : stage C u = x := (stage_comp le_sup_left a).trans ha
  have hv : stage C v = y := (stage_comp le_sup_right b).trans hb
  have hc : Function.Injective (stage C) :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := E) C.val.toLinearMap Subtype.val_injective
  let : Algebra.FiniteType L C := (Subalgebra.fg_iff_finiteType C).mp (hA.sup hB)
  let f := Spec.map (CommRingCat.ofHom (algebraMap L C))
  let : LocallyOfFiniteType f := (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)
  let : IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap L E)))) :=
    irreducibleSpace_pullback_of_isSepClosed f
  have hC : IrreducibleSpace (PrimeSpectrum (C ⊗[L] E)) :=
    (pullbackSpecIso L C E).hom.homeomorph.irreducibleSpace_iff.mp inferInstance
  have hPrime := PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp hC
  have hProd : u * v ∈ nilradical (C ⊗[L] E) := by
    rw [mem_nilradical, ← IsNilpotent.map_iff hc, map_mul, hu, hv]
    exact mem_nilradical.mp hxy
  rcases hPrime.mem_or_mem hProd with h | h
  · exact Or.inl (mem_nilradical.mpr (hu ▸ (mem_nilradical.mp h).map (stage C)))
  · exact Or.inr (mem_nilradical.mpr (hv ▸ (mem_nilradical.mp h).map (stage C)))

/-- A field extension of a separably closed field is geometrically connected. -/
theorem geometricallyConnected_specMap {L E : Type u} [Field L] [IsSepClosed L]
    [Field E] [Algebra L E] :
    GeometricallyConnected (Spec.map (CommRingCat.ofHom (algebraMap L E))) := by
  refine ⟨geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro M _ _
  let : IrreducibleSpace ↥(Spec (.of (E ⊗[L] M))) := irreducibleSpace_tensorProduct
  exact (pullbackSpecIso L E M).hom.homeomorph.connectedSpace_iff.mpr inferInstance

end PhilipponIrreducibleOverJacobson

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleConstantDegreeZero (constantSheafIso continuousSheaf)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)


namespace PhilipponEtaleConstantFibers

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev T (X : Scheme.{u}) := Scheme.Etale.mk (𝟙 X)

section Field

variable (K : Type u) [Field K] [IsSepClosed K]

private abbrev S := Spec (.of K)
private abbrev Φ := Scheme.pointSmallEtale (𝟙 (S K))
private abbrev t : (Φ K).fiber.obj (T (S K)) := Over.homMk (𝟙 _) (Category.comp_id _)

private def initialNeighborhood : IsInitial ((Φ K).fiber.elementsMk (T (S K)) (t K)) := by
  refine IsInitial.ofUniqueHom (fun W => ?_) (fun W h => ?_)
  · let g : T (S K) ⟶ W.fst := MorphismProperty.Over.homMk W.snd.left (Over.w W.snd) trivial
    refine ⟨g, Over.OverMorphism.ext ?_⟩
    change 𝟙 (S K) ≫ W.snd.left = W.snd.left
    exact Category.id_comp _
  · apply Subtype.ext
    apply MorphismProperty.Comma.Hom.ext
    · have w := congrArg Over.Hom.left h.property
      change 𝟙 (S K) ≫ h.val.left = W.snd.left at w
      exact (Category.id_comp _).symm.trans w
    · exact Subsingleton.elim _ _

private theorem isIso_germ (P : (S K).Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    IsIso ((Φ K).toPresheafFiber (T (S K)) (t K) P) := by
  let D := (CategoryOfElements.π (Φ K).fiber).op ⋙ P
  change IsIso (colimit.ι D (op ((Φ K).fiber.elementsMk (T (S K)) (t K))))
  exact (colimit.isColimit D).isIso_ι_app_of_isTerminal _ (initialNeighborhood K).op

/-- Every abelian étale sheaf on a separably closed field is constant. -/
theorem isConstant_of_isSepClosed (F : Ab (S K)) : Sheaf.IsConstant (S K).smallEtaleTopology F := by
  let J := (S K).smallEtaleTopology
  let A := AddCommGrpCat.{u}
  let hT : IsTerminal (T (S K)) := IsTerminal.isTerminalOfObj (Scheme.Etale.forget (S K)) _ Over.mkIdTerminal
  let k := (constantPresheafAdj A hT).counit.app F.obj
  let Q := ObjectProperty.ofObj (fun _ : Unit => Φ K)
  have hQ : Q.IsConservativeFamilyOfPoints := by
    apply Scheme.isConservative_pointSmallEtale
    ext x
    exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨(), ⟨x, rfl⟩⟩⟩
  have hW : J.W k := by
    apply (hQ.W_iff k).mpr
    intro p
    obtain ⟨_, hp⟩ := (ObjectProperty.ofObj_iff _ _).mp p.property
    rw [← hp]
    let P := (Functor.const (S K).Etaleᵒᵖ).obj ((globalSections (S K)).obj F)
    let l := (Φ K).toPresheafFiber (T (S K)) (t K) P
    let r := (Φ K).toPresheafFiber (T (S K)) (t K) F.obj
    let : IsIso l := isIso_germ K P
    let : IsIso r := isIso_germ K F.obj
    have hkt : k.app (op (T (S K))) = 𝟙 (F.obj.obj (op (T (S K)))) := by
      change F.obj.map (hT.from (T (S K))).op = _
      rw [hT.hom_ext (hT.from _) (𝟙 _), op_id, F.obj.map_id]
    have hEq : k.app (op (T (S K))) ≫ r = l ≫ (Φ K).presheafFiber.map k :=
      ((Φ K).toPresheafFiber_naturality k (T (S K)) (t K)).symm
    have hComp : IsIso (l ≫ (Φ K).presheafFiber.map k) := by
      have hi : IsIso (k.app (op (T (S K)))) := hkt.symm ▸ (Iso.refl _).isIso_hom
      exact hEq ▸ (inferInstance : IsIso (k.app (op (T (S K))) ≫ r))
    exact IsIso.of_isIso_comp_left l ((Φ K).presheafFiber.map k)
  let G := presheafToSheaf J A
  let : IsIso (G.map k) := (J.W_iff _).mp hW
  exact ⟨_, ⟨asIso (G.map k) ≪≫ (sheafificationIso F).symm⟩⟩

end Field

/-- A single geometric germ determines a section of a constant sheaf
on a preconnected scheme. -/
theorem terminalGerm_injective_of_isConstant {X : Scheme.{u}} [PreconnectedSpace X]
    {K : Type u} [Field K] [IsSepClosed K] (v : Spec (.of K) ⟶ X)
    (F : Ab X) [Sheaf.IsConstant X.smallEtaleTopology F] : Function.Injective ((terminalGerm v).app F) := by
  obtain ⟨A, ⟨α⟩⟩ := Sheaf.mem_essImage_of_isConstant X.smallEtaleTopology F
  let : TopologicalSpace A := ⊥
  let : DiscreteTopology A := ⟨rfl⟩
  let G := continuousSheaf X A
  let e : F ≅ G := α.symm ≪≫ constantSheafIso X A
  let E := (globalSections X).mapIso e
  intro a b hab
  apply (ConcreteCategory.bijective_of_isIso E.hom).1
  let a' : C(X, A) := E.hom a
  let b' : C(X, A) := E.hom b
  change a' = b'
  let Φ := Scheme.pointSmallEtale v
  have hNat (c : (globalSections X).obj F) :
      (terminalGerm v).app G (E.hom c) = Φ.sheafFiber.map e.hom ((terminalGerm v).app F c) :=
    ConcreteCategory.congr_hom ((terminalGerm v).naturality e.hom) c
  have hEq : (terminalGerm v).app G a' = (terminalGerm v).app G b' := by
    rw [hNat a, hNat b, hab]
  let t : Φ.fiber.obj (T X) := Over.homMk v (Category.comp_id _)
  obtain ⟨W, g, w, hw, he⟩ := (Φ.toPresheafFiber_eq_iff' (P := G.obj) (T X) t a' b').mp hEq
  let z : Spec (.of K) := default
  have hComp : w.left ≫ g.left = v := congrArg Over.Hom.left hw
  have hPoint : g.left (w.left z) = v z :=
    (Scheme.Hom.comp_apply w.left g.left z).symm.trans (congrArg (fun f : Spec (.of K) ⟶ X => f z) hComp)
  have hEval := congrArg (fun c : C(W.left, A) => c (w.left z)) he
  change a' (g.left (w.left z)) = b' (g.left (w.left z)) at hEval
  rw [hPoint] at hEval
  have ha := (IsLocallyConstant.iff_continuous _).mpr a'.continuous
  have hb := (IsLocallyConstant.iff_continuous _).mpr b'.continuous
  exact ContinuousMap.ext fun x =>
    (ha.apply_eq_of_preconnectedSpace x (v z)).trans (hEval.trans (hb.apply_eq_of_preconnectedSpace (v z) x))

end PhilipponEtaleConstantFibers

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSectionFiniteRefinement (pullSectionAlong pullSectionAlong_germ restrictGlobalSections_germ)
open PhilipponEtaleSmallSite (pullbackSheaves)
open PhilipponEtaleStalkPullback (stalkPullbackIso)
open PhilipponStrictHenselianEtaleCohomology (terminalGerm)


namespace PhilipponEtaleSectionAgreement

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}
private abbrev terminal (X : Scheme.{u}) := Scheme.Etale.mk (𝟙 X)

variable {X : Scheme.{u}} (F : Ab X) (a b : (globalSections X).obj F)

private abbrev EqualizingArrows := {q : Σ W : X.Etale, W ⟶ terminal X //
  F.obj.map q.2.op a = F.obj.map q.2.op b}

/-- The open locus on which two global étale sections have equal germs. -/
def agreementLocus : X.Opens :=
  ⟨⋃ q : EqualizingArrows F a b, Set.range q.val.2.left,
    isOpen_iUnion fun q => q.val.2.left.isOpenMap.isOpen_range⟩

/-- Membership in the agreement locus can be tested at any geometric
point over the given scheme point. -/
theorem mem_agreementLocus_iff {K : Type u} [Field K] [IsSepClosed K] (v : Spec (.of K) ⟶ X) :
    v default ∈ agreementLocus F a b ↔ (terminalGerm v).app F a = (terminalGerm v).app F b := by
  let Φ := Scheme.pointSmallEtale v
  let T := terminal X
  let t : Φ.fiber.obj T := Over.homMk v (Category.comp_id _)
  change v default ∈ (⋃ q : EqualizingArrows F a b, Set.range q.val.2.left) ↔
    Φ.toPresheafFiber T t F.obj a = Φ.toPresheafFiber T t F.obj b
  rw [Φ.toPresheafFiber_eq_iff']
  constructor
  · intro h
    obtain ⟨⟨⟨W, g⟩, he⟩, y, hy⟩ := Set.mem_iUnion.mp h
    obtain ⟨l, hl, _⟩ := Scheme.exists_fac_of_etale_of_isSepClosed g.left v y hy
    have hW := Over.w ((Scheme.Etale.forget X).map g)
    change g.left ≫ 𝟙 X = W.hom at hW
    have hW' : (show W.left ⟶ X from g.left) = W.hom :=
      (Category.comp_id (show W.left ⟶ X from g.left)).symm.trans hW
    let v' : Φ.fiber.obj W := Over.homMk l (by
      change l ≫ W.hom = v
      exact (congrArg (l ≫ ·) hW'.symm).trans hl)
    exact ⟨W, g, v', Over.OverMorphism.ext hl, he⟩
  · rintro ⟨W, g, v', hv', he⟩
    refine Set.mem_iUnion.mpr ⟨⟨⟨W, g⟩, he⟩, ?_⟩
    let z : Spec (.of K) := default
    refine ⟨v'.left z, ?_⟩
    change g.left (v'.left z) = v z
    have hcomp : v'.left ≫ g.left = v := congrArg Over.Hom.left hv'
    exact (Scheme.Hom.comp_apply v'.left g.left z).symm.trans
      (congrArg (fun l : Spec (.of K) ⟶ X => l z) hcomp)

theorem eq_of_agreementLocus_eq_top (h : agreementLocus F a b = ⊤) : a = b := by
  let Q := EqualizingArrows F a b
  let V (q : Q) := q.val.1
  let g (q : Q) : V q ⟶ terminal X := q.val.2
  have hCover : Sieve.ofArrows V g ∈ X.smallEtaleTopology (terminal X) :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr (congrArg (fun U : X.Opens => (U : Set X)) h)
  let S := Presheaf.equalizerSieve (F := F.obj) (X := op (terminal X)) a b
  have hS : S ∈ X.smallEtaleTopology (terminal X) := X.smallEtaleTopology.superset_covering
    ((Sieve.generate_le_iff _ _).mpr (by rintro _ _ ⟨q⟩; exact q.property)) hCover
  have hSheaf := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp hSheaf _ hS).isSeparatedFor.ext (fun _ _ hab => hab)

/-- Pullback of sections pulls back their agreement locus. -/
theorem mem_agreementLocus_restrict_iff {Y : Scheme.{u}} (f : Y ⟶ X) (y : Y) :
    y ∈ agreementLocus ((pullbackSheaves f).obj F) ((restrictGlobalSections f).app F a)
      ((restrictGlobalSections f).app F b) ↔ f y ∈ agreementLocus F a b := by
  let v := geometricMap y
  have hv : v default = y := geometricMap_apply y
  have hv' : (v ≫ f) default = f y := by rw [Scheme.Hom.comp_apply, hv]
  have hLeft := mem_agreementLocus_iff ((pullbackSheaves f).obj F)
    ((restrictGlobalSections f).app F a) ((restrictGlobalSections f).app F b) v
  have hRight := mem_agreementLocus_iff F a b (v ≫ f)
  rw [hv] at hLeft
  rw [hv'] at hRight
  rw [hLeft, hRight]
  let e := (stalkPullbackIso f v).hom.app F
  have hGerm (c : (globalSections X).obj F) :
      e ((terminalGerm v).app ((pullbackSheaves f).obj F) ((restrictGlobalSections f).app F c)) =
        (terminalGerm (v ≫ f)).app F c :=
    ConcreteCategory.congr_hom (restrictGlobalSections_germ f v F) c
  rw [← hGerm a, ← hGerm b]
  exact (ConcreteCategory.bijective_of_isIso e).1.eq_iff.symm

/-- Sections on an étale chart are determined by their germs at geometric
points of the chart. -/
theorem eq_of_chart_germs (W : X.Etale) (c d : F.obj.obj (op W))
    (h : ∀ y : W.left, let v := geometricMap y
      let Φ := Scheme.pointSmallEtale (v ≫ W.hom)
      let t : Φ.fiber.obj W := Over.homMk v rfl
      Φ.toPresheafFiber W t F.obj c = Φ.toPresheafFiber W t F.obj d) : c = d := by
  classical
  let S := Presheaf.equalizerSieve (F := F.obj) (X := op W) c d
  have hRefine (y : W.left) : ∃ (U : X.Etale) (g : U ⟶ W), S g ∧ y ∈ Set.range g.left := by
    let v := geometricMap y
    let Φ := Scheme.pointSmallEtale (v ≫ W.hom)
    let t : Φ.fiber.obj W := Over.homMk v rfl
    obtain ⟨U, g, w, hw, he⟩ := (Φ.toPresheafFiber_eq_iff' (P := F.obj) W t c d).mp (h y)
    have hp : w.left ≫ g.left = v := congrArg Over.Hom.left hw
    let z : Spec (.of (SeparableClosure (W.left.residueField y))) := default
    refine ⟨U, g, he, w.left z, ?_⟩
    exact (Scheme.Hom.comp_apply w.left g.left z).symm.trans
      ((congrArg (fun l : Spec (.of _) ⟶ W.left => l z) hp).trans (geometricMap_apply y))
  choose U g hg hy using hRefine
  have hCover : Sieve.ofArrows U g ∈ X.smallEtaleTopology W :=
    (Scheme.ofArrows_mem_smallEtaleTopology_iff g).mpr
      (Set.eq_univ_of_forall fun y => Set.mem_iUnion.mpr ⟨y, hy y⟩)
  have hS : S ∈ X.smallEtaleTopology W := X.smallEtaleTopology.superset_covering
    ((Sieve.generate_le_iff _ _).mpr (by rintro _ _ ⟨y⟩; exact hg y)) hCover
  have hSheaf := Presheaf.isSheaf_comp_of_isSheaf X.smallEtaleTopology F.obj
    (CategoryTheory.forget AddCommGrpCat) F.property
  exact ((isSheaf_iff_isSheaf_of_type _ _).mp hSheaf _ hS).isSeparatedFor.ext (fun _ _ hab => hab)

/-- A section of an étale chart viewed on that chart with restricted coefficients. -/
abbrev realizeOnChart (W : X.Etale) :=
  pullSectionAlong W.hom (V := W) (𝟙 W.left) (Category.id_comp _) F

private theorem chart_germs_over_congr {K : Type u} [Field K] [IsSepClosed K] (W : X.Etale)
    {s s' : Spec (.of K) ⟶ X} (e : s = s')
    (t : (Scheme.pointSmallEtale s).fiber.obj W) (t' : (Scheme.pointSmallEtale s').fiber.obj W)
    (h : t.left = t'.left) (c d : F.obj.obj (op W)) :
    ((Scheme.pointSmallEtale s).toPresheafFiber W t F.obj c =
      (Scheme.pointSmallEtale s).toPresheafFiber W t F.obj d) ↔
    ((Scheme.pointSmallEtale s').toPresheafFiber W t' F.obj c =
      (Scheme.pointSmallEtale s').toPresheafFiber W t' F.obj d) := by
  subst s'
  have ht : t = t' := Over.OverMorphism.ext h
  subst t'
  rfl

/-- The germ comparison with restricted coefficients identifies the
agreement locus of realized chart sections. -/
theorem mem_agreementLocus_realizeOnChart_iff {K : Type u} [Field K] [IsSepClosed K]
    (W : X.Etale) (s : Spec (.of K) ⟶ X)
    (t : (Scheme.pointSmallEtale s).fiber.obj W) (c d : F.obj.obj (op W)) :
    t.left (default : Spec (.of K)) ∈ agreementLocus ((pullbackSheaves W.hom).obj F)
        (realizeOnChart F W c) (realizeOnChart F W d) ↔
      (Scheme.pointSmallEtale s).toPresheafFiber W t F.obj c =
        (Scheme.pointSmallEtale s).toPresheafFiber W t F.obj d := by
  let v : Spec (.of K) ⟶ W.left := t.left
  let u : (Scheme.pointSmallEtale (v ≫ W.hom)).fiber.obj W := Over.homMk v rfl
  let G := (pullbackSheaves W.hom).obj F
  let e := (stalkPullbackIso W.hom v).hom.app F
  have hGerm (b : F.obj.obj (op W)) :
      e ((terminalGerm v).app G (realizeOnChart F W b)) =
        (Scheme.pointSmallEtale (v ≫ W.hom)).toPresheafFiber W u F.obj b :=
    ConcreteCategory.congr_hom (pullSectionAlong_germ W.hom v (V := W) (𝟙 W.left)
      (Category.id_comp _) u (Category.comp_id v).symm F) b
  have hs : v ≫ W.hom = s := Over.w t
  refine (mem_agreementLocus_iff G (realizeOnChart F W c) (realizeOnChart F W d) v).trans ?_
  refine Iff.trans ?_ (chart_germs_over_congr F W hs u t rfl c d)
  constructor
  · intro h
    exact (hGerm c).symm.trans ((congrArg e h).trans (hGerm d))
  · intro h
    exact (ConcreteCategory.bijective_of_isIso e).1 ((hGerm c).trans (h.trans (hGerm d).symm))

/-- An isomorphism of coefficient sheaves preserves the agreement locus. -/
theorem mem_agreementLocus_mapIso_iff {G : Ab X} (e : F ≅ G) (y : X) :
    y ∈ agreementLocus G ((globalSections X).map e.hom a) ((globalSections X).map e.hom b) ↔
      y ∈ agreementLocus F a b := by
  let v := geometricMap y
  have h₁ := mem_agreementLocus_iff G ((globalSections X).map e.hom a) ((globalSections X).map e.hom b) v
  have h₂ := mem_agreementLocus_iff F a b v
  rw [geometricMap_apply y] at h₁ h₂
  rw [h₁, h₂]
  have hNat (c : (globalSections X).obj F) :
      (terminalGerm v).app G ((globalSections X).map e.hom c) =
        (Scheme.pointSmallEtale v).sheafFiber.map e.hom ((terminalGerm v).app F c) :=
    ConcreteCategory.congr_hom ((terminalGerm v).naturality e.hom) c
  rw [hNat a, hNat b]
  exact (ConcreteCategory.bijective_of_isIso
    ((Scheme.pointSmallEtale v).sheafFiber.map e.hom)).1.eq_iff

/-- Chart sections restrict equally along any arrow whose image lies in
their agreement locus. -/
theorem eq_restriction_of_mem_agreementLocus {U W : X.Etale} (g : U ⟶ W)
    (c d : F.obj.obj (op W))
    (h : ∀ y : U.left, g.left y ∈ agreementLocus ((pullbackSheaves W.hom).obj F)
      (realizeOnChart F W c) (realizeOnChart F W d)) :
    F.obj.map g.op c = F.obj.map g.op d := by
  refine eq_of_chart_germs F U (F.obj.map g.op c) (F.obj.map g.op d) ?_
  intro y
  let v := geometricMap y
  let s := v ≫ U.hom
  let Φ := Scheme.pointSmallEtale s
  let w : Φ.fiber.obj U := Over.homMk v rfl
  let t := Φ.fiber.map g w
  let z : Spec (.of (SeparableClosure (U.left.residueField y))) := default
  let left : U.left ⟶ W.left := g.left
  have hl : t.left = v ≫ left := rfl
  have ht : t.left z = left y := (congrArg (fun p : Spec (.of _) ⟶ W.left => p z) hl).trans
    ((Scheme.Hom.comp_apply v left z).trans (congrArg left (geometricMap_apply y)))
  have hm := (mem_agreementLocus_realizeOnChart_iff F W s t c d).mp (ht.symm ▸ h y)
  have hg (a : F.obj.obj (op W)) :
      Φ.toPresheafFiber U w F.obj (F.obj.map g.op a) = Φ.toPresheafFiber W t F.obj a :=
    ConcreteCategory.congr_hom (Φ.toPresheafFiber_w g w F.obj) a
  exact (hg c).trans (hm.trans (hg d).symm)

/-- The canonical realization of a chart section as a global section
of the restricted sheaf is injective. -/
theorem pullSectionAlong_self_injective (W : X.Etale) :
    Function.Injective (pullSectionAlong W.hom (V := W) (𝟙 W.left) (Category.id_comp _) F) := by
  intro c d hcd
  apply eq_of_chart_germs F W c d
  intro y
  let v := geometricMap y
  let Φ := Scheme.pointSmallEtale (v ≫ W.hom)
  let t : Φ.fiber.obj W := Over.homMk v rfl
  have hPull := pullSectionAlong_germ W.hom v (V := W) (𝟙 W.left)
    (Category.id_comp _) t (Category.comp_id v).symm F
  exact (ConcreteCategory.congr_hom hPull c).symm.trans
    ((congrArg (fun sec => (stalkPullbackIso W.hom v).hom.app F
      ((terminalGerm v).app ((pullbackSheaves W.hom).obj F) sec)) hcd).trans
      (ConcreteCategory.congr_hom hPull d))

end PhilipponEtaleSectionAgreement

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections pullbackConstantIso)
open PhilipponEtaleConstantFibers (isConstant_of_isSepClosed terminalGerm_injective_of_isConstant)
open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply)
open PhilipponEtalePullbackComposition (pullbackCompIso)
open PhilipponEtalePullbackResolution (restrictGlobalSections)
open PhilipponEtaleSectionAgreement (agreementLocus mem_agreementLocus_iff mem_agreementLocus_restrict_iff)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleConnectedAgreement

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

set_option maxHeartbeats 1000000 in
/-- Two sections of an inverse image agree on whole fibers when the
geometric fibers are connected. -/
theorem agreementLocus_saturated {X Y : Scheme.{u}} (f : Y ⟶ X) [GeometricallyConnected f]
    (F : Ab X) (a b : (globalSections Y).obj ((pullbackSheaves f).obj F))
    {y y' : Y} (h : f y = f y') (hy : y ∈ agreementLocus ((pullbackSheaves f).obj F) a b) :
    y' ∈ agreementLocus ((pullbackSheaves f).obj F) a b := by
  let x := f y
  let s := geometricMap x
  let V := pullback s f
  let t : V ⟶ Y := pullback.snd s f
  let g := pullback.fst s f
  have hPB : IsPullback g t s f := IsPullback.of_hasPullback s f
  let : ConnectedSpace V := GeometricallyConnected.geometrically_connectedSpace s t g hPB.flip
  have ht : Set.range t = f ⁻¹' Set.range s := Scheme.Pullback.range_snd s f
  have hx : x ∈ Set.range s := ⟨default, geometricMap_apply _⟩
  have hyV : y ∈ Set.range t := by rw [ht]; exact hx
  have hyV' : y' ∈ Set.range t := by
    rw [ht]
    change f y' ∈ Set.range s
    rw [← h]
    exact hx
  obtain ⟨z, hz⟩ := hyV
  obtain ⟨z', hz'⟩ := hyV'
  let D := (pullbackSheaves f).obj F
  let G := (pullbackSheaves s).obj F
  let H := (pullbackSheaves t).obj D
  let e : H ≅ (pullbackSheaves g).obj G :=
    (pullbackCompIso f t ≪≫ eqToIso (congrArg pullbackSheaves hPB.w.symm) ≪≫ (pullbackCompIso s g).symm).app F
  let : Sheaf.IsConstant _ G := isConstant_of_isSepClosed _ G
  obtain ⟨A, ⟨eG⟩⟩ := Sheaf.mem_essImage_of_isConstant _ G
  let : Sheaf.IsConstant V.smallEtaleTopology H :=
    ⟨_, ⟨((pullbackConstantIso g).app A).symm ≪≫ (pullbackSheaves g).mapIso eG ≪≫ e.symm⟩⟩
  let c := (restrictGlobalSections t).app D a
  let d := (restrictGlobalSections t).app D b
  have hzMem : z ∈ agreementLocus H c d :=
    (mem_agreementLocus_restrict_iff D a b t z).mpr (hz.symm ▸ hy)
  let v := geometricMap z
  have hv : v default ∈ agreementLocus H c d := (geometricMap_apply z).symm ▸ hzMem
  have hEq : c = d := terminalGerm_injective_of_isConstant v H ((mem_agreementLocus_iff H c d v).mp hv)
  let v' := geometricMap z'
  have hv' : v' default ∈ agreementLocus H c d := (mem_agreementLocus_iff H c d v').mpr (hEq ▸ rfl)
  have hzMem' : z' ∈ agreementLocus H c d := (geometricMap_apply z') ▸ hv'
  exact hz' ▸ (mem_agreementLocus_restrict_iff D a b t z').mp hzMem'

/-- Agreement of sections of a pullback descends to an open on the base
when the map is open and its geometric fibers are connected. -/
theorem exists_open_of_agreementLocus {X Y : Scheme.{u}} (f : Y ⟶ X) [GeometricallyConnected f]
    (hf : IsOpenMap f) (F : Ab X) (a b : (globalSections Y).obj ((pullbackSheaves f).obj F)) :
    ∃ U : X.Opens, ∀ y : Y, y ∈ agreementLocus ((pullbackSheaves f).obj F) a b ↔ f y ∈ U := by
  let W := agreementLocus ((pullbackSheaves f).obj F) a b
  refine ⟨⟨f '' W, hf W W.isOpen⟩, fun y => ⟨fun hy => ⟨y, hy, rfl⟩, ?_⟩⟩
  rintro ⟨z, hz, h⟩
  exact agreementLocus_saturated f F a b h hz

end PhilipponEtaleConnectedAgreement

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleDirectImageGerms (evalAtLift evalAtLift_germ_of_eq evalAtLift_unit)
open PhilipponEtaleGeometricStalks (geometricMap geometricMap_apply)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)
open PhilipponEtaleStalkPullback (pointFiberIso pointFiberIso_inv_fst stalkPullbackIso)


namespace PhilipponEtaleStalkUnitRefinement

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

private abbrev chart (W : X.Etale) := (baseChange p).obj W
private abbrev π (W : X.Etale) : (chart p W).left ⟶ W.left := pullback.fst W.hom p

/-- Agreement at a lift can be realized by restricting the base chart to
an open neighborhood of the image. -/
def RefinesEvaluationGerms : Prop :=
  ∀ (F : Ab X) (W : X.Etale)
    (c d : ((pullbackSheaves p).obj F).obj.obj (op (chart p W)))
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ Y)
    (t : (Scheme.pointSmallEtale s).fiber.obj (chart p W)),
    (Scheme.pointSmallEtale s).toPresheafFiber (chart p W) t ((pullbackSheaves p).obj F).obj c =
      (Scheme.pointSmallEtale s).toPresheafFiber (chart p W) t ((pullbackSheaves p).obj F).obj d →
    ∃ O : W.left.Opens, π p W (t.left (default : Spec (.of K))) ∈ O ∧
      ∀ (U : X.Etale) (g : U ⟶ W), (∀ x : U.left, g.left x ∈ O) →
        ((pullbackSheaves p).obj F).obj.map ((baseChange p).map g).op c =
        ((pullbackSheaves p).obj F).obj.map ((baseChange p).map g).op d

private theorem exists_openChart_at {K : Type u} [Field K] [IsSepClosed K]
    (W : X.Etale) (s : Spec (.of K) ⟶ X) (w : (Scheme.pointSmallEtale s).fiber.obj W)
    (O : W.left.Opens) (hMem : w.left (default : Spec (.of K)) ∈ O) :
    ∃ (U : X.Etale) (g : U ⟶ W) (u : (Scheme.pointSmallEtale s).fiber.obj U),
      (Scheme.pointSmallEtale s).fiber.map g u = w ∧ ∀ a : U.left, g.left a ∈ O := by
  let z : Spec (.of K) := default
  have hRange : Set.range w.left ⊆ Set.range O.ι := by
    rintro _ ⟨a, rfl⟩
    rw [O.range_ι]
    exact Eq.mp (congrArg (fun v : Spec (.of K) => w.left v ∈ O) (Subsingleton.elim z a)) hMem
  let l := IsOpenImmersion.lift O.ι w.left hRange
  have hl : l ≫ O.ι = w.left := IsOpenImmersion.lift_fac _ _ _
  let U := Scheme.Etale.mk (O.ι ≫ W.hom)
  let g : U ⟶ W := MorphismProperty.Over.homMk O.ι rfl trivial
  let u : (Scheme.pointSmallEtale s).fiber.obj U := Over.homMk l (by
    change l ≫ O.ι ≫ W.hom = s
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ W.hom) hl).trans (Over.w w)))
  have hu : (Scheme.pointSmallEtale s).fiber.map g u = w := Over.OverMorphism.ext hl
  have hg (a : U.left) : g.left a ∈ O := by
    change O.ι a ∈ (O : Set W.left)
    rw [← O.range_ι]
    exact ⟨a, rfl⟩
  exact ⟨U, g, u, hu, hg⟩

set_option maxHeartbeats 900000 in
private theorem germs_equal_of_evaluation (hRef : RefinesEvaluationGerms p)
    (F : Ab X) {K : Type u} [Field K] [IsSepClosed K] (v : Spec (.of K) ⟶ Y)
    (W : X.Etale) (w : (Scheme.pointSmallEtale (v ≫ p)).fiber.obj W)
    (c d : ((pullbackSheaves p).obj F).obj.obj (op (chart p W))) :
    let D := (pullbackSheaves p).obj F
    let H := (pushforward p).obj D
    let Φ := Scheme.pointSmallEtale (v ≫ p)
    let ev := evalAtLift p v D
    let germ := Φ.toPresheafFiber W w H.obj
    ev (germ c) = ev (germ d) → germ c = germ d := by
  let D := (pullbackSheaves p).obj F
  let H := (pushforward p).obj D
  let Φ := Scheme.pointSmallEtale (v ≫ p)
  let Ψ := Scheme.pointSmallEtale v
  let ev : Φ.sheafFiber.obj H ⟶ Ψ.sheafFiber.obj D := evalAtLift p v D
  dsimp only
  intro hxy
  let t := (pointFiberIso p v).inv.app W w
  have hPoint : (t.left ≫ π p W) = w.left := pointFiberIso_inv_fst p v W w
  have hEval : Φ.toPresheafFiber W w H.obj ≫ ev =
      Ψ.toPresheafFiber (chart p W) t D.obj := by
    simpa only [eqToHom_refl, Category.id_comp] using
      evalAtLift_germ_of_eq p v rfl D W w t hPoint
  have hcEval := ConcreteCategory.congr_hom hEval c
  have hdEval := ConcreteCategory.congr_hom hEval d
  have hGerm : Ψ.toPresheafFiber (chart p W) t D.obj c =
      Ψ.toPresheafFiber (chart p W) t D.obj d :=
    hcEval.symm.trans (hxy.trans hdEval)
  obtain ⟨O, hO, hEq⟩ := hRef F W c d v t hGerm
  let z : Spec (.of K) := default
  have hVal : π p W (t.left z) = w.left z :=
    (Scheme.Hom.comp_apply t.left (π p W) z).symm.trans
      (congrArg (fun h : Spec (.of K) ⟶ W.left => h z) hPoint)
  have hMem : w.left z ∈ O := Eq.mp (congrArg (fun a : W.left => a ∈ O) hVal) hO
  obtain ⟨U, g, u, hu, hg⟩ := exists_openChart_at W (v ≫ p) w O hMem
  have hAgree : H.obj.map g.op c = H.obj.map g.op d := hEq U g hg
  exact (Φ.toPresheafFiber_eq_iff' (P := H.obj) W w c d).mpr ⟨U, g, u, hu, hAgree⟩

/-- A germ of the direct image of an inverse image is determined by
evaluation at one geometric lift if the base charts have the
required refinements. -/
theorem evalAtLift_injective (hRef : RefinesEvaluationGerms p)
    (F : Ab X) {K : Type u} [Field K] [IsSepClosed K] (v : Spec (.of K) ⟶ Y) :
    Function.Injective (evalAtLift p v ((pullbackSheaves p).obj F)) := by
  let D := (pullbackSheaves p).obj F
  let H := (pushforward p).obj D
  let Φ := Scheme.pointSmallEtale (v ≫ p)
  let ev := evalAtLift p v D
  intro x y hxy
  obtain ⟨W, w, c, d, hc, hd⟩ := Φ.toPresheafFiber_jointly_surjective₂ (P := H.obj) x y
  have he : ev (Φ.toPresheafFiber W w H.obj c) = ev (Φ.toPresheafFiber W w H.obj d) :=
    (congrArg ev hc).trans (hxy.trans (congrArg ev hd).symm)
  exact hc.symm.trans ((germs_equal_of_evaluation p hRef F v W w c d he).trans hd)

/-- Refining equality at geometric lifts makes the inverse-image unit
invertible for a surjective morphism. -/
theorem isIso_unit_of_germ_refinement [Surjective p] (hRef : RefinesEvaluationGerms p)
    (F : Ab X) : IsIso ((pullbackAdjunction p).unit.app F) := by
  classical
  let η := (pullbackAdjunction p).unit.app F
  let D := (pullbackSheaves p).obj F
  choose y hy using fun x : X => p.surjective x
  let s (x : X) := geometricMap (y x) ≫ p
  let Q := ObjectProperty.ofObj (fun x : X => Scheme.pointSmallEtale (s x))
  have hQ : Q.IsConservativeFamilyOfPoints := by
    apply Scheme.isConservative_pointSmallEtale
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨x, default, (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg p (geometricMap_apply (y x))).trans (hy x))⟩
  apply ((hQ.jointlyReflectIsomorphisms AddCommGrpCat.{u}).isIso_iff η).mpr
  intro Φ
  obtain ⟨x, hx⟩ := (ObjectProperty.ofObj_iff _ _).mp Φ.property
  rw [← hx]
  let v := geometricMap (y x)
  let m := (Scheme.pointSmallEtale (s x)).sheafFiber.map η
  let ev := evalAtLift p v D
  let e := (stalkPullbackIso p v).hom.app F
  have hUnit : m ≫ (ev ≫ e) = 𝟙 _ := evalAtLift_unit p v F
  let : Mono ev := (AddCommGrpCat.mono_iff_injective ev).mpr (evalAtLift_injective p hRef F v)
  let : Epi (ev ≫ e) := epi_of_epi_fac hUnit
  let : IsIso (ev ≫ e) := isIso_of_mono_of_epi _
  let : IsIso (m ≫ (ev ≫ e)) := hUnit.symm ▸ (Iso.refl _).isIso_hom
  exact IsIso.of_isIso_comp_right m (ev ≫ e)

end PhilipponEtaleStalkUnitRefinement

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleConnectedAgreement (exists_open_of_agreementLocus)
open PhilipponEtalePullbackSquareUnits (pullbackSquareIso)
open PhilipponEtaleSectionAgreement (agreementLocus eq_restriction_of_mem_agreementLocus mem_agreementLocus_mapIso_iff
  mem_agreementLocus_realizeOnChart_iff realizeOnChart)
open PhilipponEtaleSmallSite (pullbackAdjunction pullbackSheaves)


namespace PhilipponEtaleConnectedChartLifts

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

variable {X Y : Scheme.{u}} (p : Y ⟶ X)

private abbrev chart (W : X.Etale) := (baseChange p).obj W
private abbrev π (W : X.Etale) : (chart p W).left ⟶ W.left := pullback.fst W.hom p

private theorem map_fst {U W : X.Etale} (g : U ⟶ W) :
    ((baseChange p).map g).left ≫ π p W = π p U ≫ g.left :=
  pullback.lift_fst _ _ _

private abbrev chartAgreement (F : Ab X) (W : X.Etale)
    (c d : ((pullbackSheaves p).obj F).obj.obj (op (chart p W))) : (chart p W).left.Opens :=
  let D := (pullbackSheaves p).obj F
  let V := chart p W
  agreementLocus ((pullbackSheaves V.hom).obj D) (realizeOnChart D V c) (realizeOnChart D V d)

set_option maxHeartbeats 600000 in
private theorem exists_open_of_chartAgreement [GeometricallyConnected p] [UniversallyOpen p]
    (F : Ab X) (W : X.Etale)
    (c d : ((pullbackSheaves p).obj F).obj.obj (op (chart p W))) :
    ∃ O : W.left.Opens, ∀ z : (chart p W).left, z ∈ chartAgreement p F W c d ↔ π p W z ∈ O := by
  let D := (pullbackSheaves p).obj F
  let V := chart p W
  let q := π p W
  let r := V.hom
  let A := (pullbackSheaves r).obj D
  let B := (pullbackSheaves W.hom).obj F
  let e : A ≅ (pullbackSheaves q).obj B :=
    ((pullbackSquareIso p W.hom).app F).symm
  let c' := realizeOnChart D V c
  let d' := realizeOnChart D V d
  let : GeometricallyConnected q :=
    inferInstanceAs (GeometricallyConnected (pullback.fst W.hom p))
  let : UniversallyOpen q := inferInstanceAs (UniversallyOpen (pullback.fst W.hom p))
  obtain ⟨O, hO⟩ := exists_open_of_agreementLocus q q.isOpenMap B
    ((globalSections V.left).map e.hom c') ((globalSections V.left).map e.hom d')
  exact ⟨O, fun z => (mem_agreementLocus_mapIso_iff A c' d' e z).symm.trans (hO z)⟩

set_option maxHeartbeats 600000 in
/-- Matching germs on a base-changed chart give equality after refining
the chart inside an open neighborhood on the original chart. -/
theorem exists_open_of_baseChanged_chart_germ_eq [GeometricallyConnected p] [UniversallyOpen p]
    (F : Ab X) (W : X.Etale)
    (c d : ((pullbackSheaves p).obj F).obj.obj (op (chart p W)))
    {K : Type u} [Field K] [IsSepClosed K] (s : Spec (.of K) ⟶ Y)
    (t : (Scheme.pointSmallEtale s).fiber.obj (chart p W))
    (h : (Scheme.pointSmallEtale s).toPresheafFiber (chart p W) t ((pullbackSheaves p).obj F).obj c =
      (Scheme.pointSmallEtale s).toPresheafFiber (chart p W) t ((pullbackSheaves p).obj F).obj d) :
    ∃ O : W.left.Opens, π p W (t.left (default : Spec (.of K))) ∈ O ∧
      ∀ (U : X.Etale) (g : U ⟶ W), (∀ x : U.left, g.left x ∈ O) →
        ((pullbackSheaves p).obj F).obj.map ((baseChange p).map g).op c =
        ((pullbackSheaves p).obj F).obj.map ((baseChange p).map g).op d := by
  obtain ⟨O, hO⟩ := exists_open_of_chartAgreement p F W c d
  have hMem : t.left (default : Spec (.of K)) ∈ chartAgreement p F W c d :=
    (mem_agreementLocus_realizeOnChart_iff ((pullbackSheaves p).obj F) (chart p W) s t c d).mpr h
  refine ⟨O, (hO _).mp hMem, ?_⟩
  intro U g hg
  let dmap := (baseChange p).map g
  refine eq_restriction_of_mem_agreementLocus ((pullbackSheaves p).obj F) dmap c d ?_
  intro y
  change dmap.left y ∈ chartAgreement p F W c d
  apply (hO (dmap.left y)).mpr
  let q := π p W
  let q' := π p U
  let left : (chart p U).left ⟶ (chart p W).left := dmap.left
  let top : U.left ⟶ W.left := g.left
  have hMap : left ≫ q = q' ≫ top := map_fst p g
  have hPoint : q (left y) = top (q' y) :=
    (Scheme.Hom.comp_apply left q y).symm.trans
      ((congrArg (fun f : (chart p U).left ⟶ W.left => f y) hMap).trans
        (Scheme.Hom.comp_apply q' top y))
  exact hPoint.symm ▸ hg (q' y)

/-- The inverse-image unit is invertible for universally open morphisms
with connected geometric fibers. -/
theorem isIso_unit_of_geometricallyConnected [GeometricallyConnected p] [UniversallyOpen p]
    (F : Ab X) : IsIso ((pullbackAdjunction p).unit.app F) :=
  PhilipponEtaleStalkUnitRefinement.isIso_unit_of_germ_refinement p
    (exists_open_of_baseChanged_chart_germ_eq p) F

end PhilipponEtaleConnectedChartLifts

end

open PhilipponEtalePullbackResolution (restrictGlobalSections)
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u

theorem solution
    (L E : Type u) [Field L] [IsSepClosed L] [Field E] [IsAlgClosed E]
    (g : L →+* E) {Z B : Scheme.{u}} (p : Z ⟶ Spec (.of L)) [IsProper p]
    (j : B ⟶ Spec (.of E)) (a : B ⟶ Z) (_h : IsPullback j a (Spec.map (CommRingCat.ofHom g)) p)
    (F : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) :
    IsIso ((restrictGlobalSections a).app F) := by
  let : Algebra L E := g.toAlgebra
  have hMap : GeometricallyConnected (Spec.map (CommRingCat.ofHom g)) :=
    PhilipponIrreducibleOverJacobson.geometricallyConnected_specMap (L := L) (E := E)
  let : GeometricallyConnected a := MorphismProperty.of_isPullback _h hMap
  let : UniversallyOpen a := MorphismProperty.of_isPullback _h
    (inferInstance : UniversallyOpen (Spec.map (CommRingCat.ofHom g)))
  rw [PhilipponEtalePullbackComposition.restrictGlobalSections_app_eq]
  let : IsIso ((PhilipponEtaleSmallSite.pullbackAdjunction a).unit.app F) :=
    PhilipponEtaleConnectedChartLifts.isIso_unit_of_geometricallyConnected a F
  infer_instance


end
