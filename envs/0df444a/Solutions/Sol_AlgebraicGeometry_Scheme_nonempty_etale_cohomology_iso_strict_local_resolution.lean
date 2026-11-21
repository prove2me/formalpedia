-- Prove2me | solution 1 for AlgebraicGeometry.Scheme.nonempty_etale_cohomology_iso_strict_local_resolution
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-11-21T04:52:46.746961+00:00
-- url     : https://prove2.me/submissions/e6faf990-767d-4b3e-8e23-b046b0e1b5f8

import Definitions.Def_AlgebraicGeometry_EtaleModeledCech

noncomputable section

section

section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial
open PhilipponCech
open PhilipponEtaleModeledGluing (qcqsCharts)
open PhilipponEtaleModeledSections (chartLimitFunctor)
open PhilipponEtaleModeledCech (inverseImage_cech_exact_of_modeled_cover)
open PhilipponEtaleModeledCoverArrow (exists_modeled_covering_arrow_refinement)
open PhilipponEtaleRefinementGluing (qcqsCharts_cechNerve modeledCharts)
open PhilipponEtaleSmallSite (pullbackSheaves)


namespace PhilipponEtaleModeledAcyclicity

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I] {Y : Scheme.{u}} (E : I ⥤ Y.Etale)

private abbrev D := E ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y

variable (c : Cone (D E)) (hc : IsLimit c)
  [∀ {j k : I} (b : j ⟶ k), IsAffineHom ((D E).map b)]
  (p : c.pt ⟶ Y) (hp : ∀ j, c.π.app j ≫ (E.obj j).hom = p)
  (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) [Injective F]

private abbrev P {X Z : Scheme.{u}} (f : X ⟶ Z)
    (T : Sheaf Z.smallEtaleTopology AddCommGrpCat.{u}) := (pullbackSheaves f).obj T

include hc hp in
/-- The inverse image of an injective sheaf has zero positive étale
cohomology on all modeled qcqs charts. -/
theorem inverseImage_acyclic_on_modeled (q : ℕ) :
    ∀ (i : I) (U : ((D E).obj i).Etale), qcqsCharts ((D E).obj i) U →
      Subsingleton ((P p F).H' (q + 1) ((chartLimitFunctor E c i).obj U)) := by
  induction q using Nat.strong_induction_on with
  | h q ih =>
      intro i U hU
      let X := c.pt
      let J := X.smallEtaleTopology
      let P' := P p F
      let A := (chartLimitFunctor E c i).obj U
      let Cq := P'.cohomologyPresheaf (q + 1)
      let : CompactSpace ((𝟭 Scheme.{u}).obj U.left) := hU.1
      let : IsAffineHom (c.π.app i) := AlgebraicGeometry.isAffineHom_π_app (D E) c hc i
      let : CompactSpace A.left := inferInstanceAs (CompactSpace ↥(pullback (c.π.app i) U.hom))
      refine subsingleton_of_forall_eq 0 (fun x => ?_)
      obtain ⟨B, a, hB, ha, hx⟩ := Scheme.exists_surjective_affine_arrow_killing_class A P' q x
      obtain ⟨j, T, V, e, b, g, hT, hV, hb, hcover, hfac⟩ :=
        exists_modeled_covering_arrow_refinement E c hc hU a ha
      let : Surjective b.left := ⟨hb⟩
      let : IsAffine V.left := hV
      let hV' : qcqsCharts ((D E).obj j) V := ⟨inferInstance, inferInstance⟩
      let K := chartLimitFunctor E c j
      let x' := Cq.map e.inv.op x
      have hx' : Cq.map (K.map b).op x' = 0 := by
        change Cq.map (K.map b).op (Cq.map e.inv.op x) = 0
        rw [← ConcreteCategory.comp_apply, ← Cq.map_comp, ← op_comp, ← hfac,
          op_comp, Cq.map_comp, ConcreteCategory.comp_apply, hx, map_zero]
      have hz : x' = 0 := by
        apply class_eq_zero_of_cech_exact (K.map b) J hcover P' q ?_
          (inverseImage_cech_exact_of_modeled_cover E b F c hc p hp hT hV') x' hx'
        intro m k hk hle
        cases k with
        | zero => exact (Nat.not_lt_zero _ hk).elim
        | succ k =>
          let W := (Arrow.mk b).cechNerve.obj (op ⦋m⦌)
          let L := P'.cohomologyPresheaf (k + 1)
          let : Subsingleton ↥(L.obj (op (K.obj W))) :=
            ih k (Nat.lt_of_succ_le hle) j W (qcqsCharts_cechNerve b hT hV' (op ⦋m⦌))
          let e' : K.obj W ≅ (Arrow.mk (K.map b)).cechNerve.obj (op ⦋m⦌) :=
            (cechNerveMapIso K b).app (op ⦋m⦌)
          let d := (P'.cohomologyPresheaf (k + 1)).mapIso e'.op
          exact d.addCommGroupIsoToAddEquiv.injective.subsingleton
      let d : Cq.obj (op A) ≅ Cq.obj (op (K.obj T)) := Cq.mapIso e.symm.op
      have he : x' = Cq.map e.inv.op 0 := hz.trans (map_zero _).symm
      exact d.addCommGroupIsoToAddEquiv.injective he

include hc hp in
/-- If the terminal chart has a qcqs model at a stage, the inverse image
of an injective sheaf is acyclic for global sections. -/
theorem inverseImage_acyclic_of_modeled_terminal
    (hT : modeledCharts E c (Scheme.Etale.mk (𝟙 c.pt))) (q : ℕ) :
    Subsingleton ((P p F).H (q + 1)) := by
  let T := Scheme.Etale.mk (𝟙 c.pt)
  obtain ⟨i, U, hU, ⟨e⟩⟩ := hT
  let L := (P p F).cohomologyPresheaf (q + 1)
  let : Subsingleton ↥(L.obj (op ((chartLimitFunctor E c i).obj U))) :=
    inverseImage_acyclic_on_modeled E c hc p hp F q i U hU
  let d := (L.mapIso e.symm.op).addCommGroupIsoToAddEquiv
  let hTerminal : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget c.pt) _ Over.mkIdTerminal
  let eT := PhilipponSheafCohomology.terminalComparison c.pt.smallEtaleTopology hTerminal (P p F) (q + 1)
  exact (eT.trans d).injective.subsingleton

end PhilipponEtaleModeledAcyclicity

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeComparison (baseChange)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)
open PhilipponEtaleStrictHenselization
  (IsAffineNeighborhood affineInclusion pullbackNeighborhoodLimitCone affinePullbackTransition toBase)


namespace PhilipponStrictLocalPresheaf

universe u

variable {X Y : Scheme.{u}} {K : Type u} [Field K] [IsSepClosed K]
  (s : Spec (CommRingCat.of K) ⟶ X) (f : Y ⟶ X)

private abbrev Local : Scheme.{u} := pullback (toBase s) f
private abbrev π : Local s f ⟶ Y := pullback.snd (toBase s) f
private abbrev T : (Local s f).Etale := Scheme.Etale.mk (𝟙 _)

private abbrev Φ := Scheme.pointSmallEtale s
private abbrev C := (IsAffineNeighborhood s).FullSubcategory
private abbrev Index := InitiallySmall.CofilteredInitialModel.{u} (C s)
private abbrev H := InitiallySmall.fromCofilteredInitialModel.{u} (C s)
private abbrev J := H s ⋙ affineInclusion s
private abbrev E := J s ⋙ CategoryOfElements.π (Φ s).fiber ⋙ baseChange f
private abbrev D := E s f ⋙ Scheme.Etale.forget Y ⋙ Over.forget Y
private abbrev limitCone : Cone (D s f) := (pullbackNeighborhoodLimitCone s f).cone.whisker (J s)
private abbrev t : (limitCone s f).pt ⟶ Local s f := 𝟙 _

private theorem stageComm (i : Index s) :
    (limitCone s f).π.app i ≫ ((E s f).obj i).hom = t s f ≫ π s f := by
  change pullback.lift _ _ _ ≫ pullback.snd _ _ = 𝟙 _ ≫ pullback.snd _ _
  exact (pullback.lift_snd ..).trans (Category.id_comp _).symm

private def limitWitness : IsLimit (limitCone s f) :=
  (Functor.Initial.isLimitWhiskerEquiv (J s) _).symm (pullbackNeighborhoodLimitCone s f).isLimit

private abbrev q (i : Index s) : (D s f).obj i ⟶ ((H s).obj i).obj.1.left :=
  pullback.fst ((H s).obj i).obj.1.hom f

local instance stageCompact [IsProper f] (i : Index s) : CompactSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : IsProper (q s f i) := inferInstanceAs (IsProper (pullback.fst ((H s).obj i).obj.1.hom f))
  exact (quasiCompact_iff_compactSpace (q s f i)).mp inferInstance

local instance stageQuasiSeparated [IsProper f] (i : Index s) :
    QuasiSeparatedSpace ((D s f).obj i) := by
  let : IsAffine ((H s).obj i).obj.1.left := ((H s).obj i).property
  let : IsProper (q s f i) := inferInstanceAs (IsProper (pullback.fst ((H s).obj i).obj.1.hom f))
  exact quasiSeparatedSpace_of_quasiSeparated (q s f i)

local instance stageAffine {i j : Index s} (b : i ⟶ j) : IsAffineHom ((D s f).map b) :=
  affinePullbackTransition s f ((H s).map b)

private theorem modeledTerminal [IsProper f] :
    PhilipponEtaleRefinementGluing.modeledCharts (E s f) (limitCone s f) (T s f) := by
  let c := limitCone s f
  let i := Classical.choice (IsCofiltered.nonempty (C := Index s))
  let V := Scheme.Etale.mk (𝟙 ((D s f).obj i))
  let g := pullback.fst (c.π.app i) (𝟙 ((D s f).obj i))
  let e : T s f ≅ (PhilipponEtaleModeledSections.chartLimitFunctor (E s f) c i).obj V :=
    MorphismProperty.Over.isoMk (asIso g).symm (IsIso.inv_hom_id g)
  exact ⟨i, V, ⟨stageCompact s f i, stageQuasiSeparated s f i⟩, ⟨e⟩⟩

/-- The inverse image of an injective abelian étale sheaf to the
strict-henselization pullback of a proper morphism is acyclic. -/
theorem strictLocalPullback_acyclic_of_injective [IsProper f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) [Injective F] (q : ℕ) :
    Subsingleton (((pullbackSheaves (π s f)).obj F).H (q + 1)) :=
  PhilipponEtaleModeledAcyclicity.inverseImage_acyclic_of_modeled_terminal (E s f) (limitCone s f)
    (limitWitness s f) (π s f) (fun j => (stageComm s f j).trans (Category.id_comp _))
    F (modeledTerminal s f) q

end PhilipponStrictLocalPresheaf

end

end

end

section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits HomologicalComplex Opposite


namespace PhilipponAcyclicResolution

universe u v

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem next_eq (j : ℕ) : (ComplexShape.up ℕ).next j = j + 1 :=
  (ComplexShape.up ℕ).next_eq' (ComplexShape.up_mk _ _ rfl)

private theorem prev_eq (j : ℕ) : (ComplexShape.up ℕ).prev (j + 1) = j :=
  (ComplexShape.up ℕ).prev_eq' (ComplexShape.up_mk _ _ rfl)

private abbrev cycleSequence (K : CochainComplex C ℕ) (j : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles j) (K.toCycles j (j + 1)) (by
    rw [← cancel_mono (K.iCycles (j + 1)), Category.assoc, K.toCycles_i,
      K.iCycles_d, zero_comp])

private theorem cycleSequence_exact (K : CochainComplex C ℕ) (j : ℕ) (h : K.ExactAt (j + 1)) :
    (cycleSequence K j).ShortExact := by
  have hEpi : Epi (K.toCycles j (j + 1)) := by
    have hp := ((K.exactAt_iff' j (j + 1) (j + 2) (prev_eq j) (next_eq (j + 1))).mp h).epi_toCycles
    rw [← K.toCycles_cyclesIsoSc'_hom _ _ _ (prev_eq j) (next_eq (j + 1))] at hp
    exact (epi_comp_iff_of_isIso (K.toCycles j (j + 1))
      (K.cyclesIsoSc' j (j + 1) (j + 2) (prev_eq j) (next_eq (j + 1))).hom).mp hp
  have hKernel : IsLimit (KernelFork.ofι (cycleSequence K j).f (cycleSequence K j).zero) := by
    refine KernelFork.IsLimit.ofι' (K.iCycles j) _ (fun t ht => ?_)
    apply KernelFork.IsLimit.lift' (K.cyclesIsKernel (i := j) (j := j + 1) (next_eq j)) t
    rw [← K.toCycles_i j (j + 1), ← Category.assoc, ht, zero_comp]
  exact ShortComplex.ShortExact.mk' ((cycleSequence K j).exact_of_f_is_kernel hKernel)
    (inferInstanceAs (Mono (K.iCycles j))) hEpi

variable [HasExt.{v} C]

private def dimensionShift (P : C) {S : ShortComplex C} (hS : S.ShortExact) (j : ℕ)
    [Subsingleton (Ext P S.X₂ (j + 1))] [Subsingleton (Ext P S.X₂ (j + 2))] :
    Ext P S.X₃ (j + 1) ≃+ Ext P S.X₁ (j + 2) := by
  refine AddEquiv.ofBijective (hS.extClass.postcomp P rfl) ⟨?_, ?_⟩
  · rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ P hS (n₁ := j + 2) x rfl hx
    rw [← hy, Subsingleton.elim y 0, Ext.zero_comp]
  · intro x
    exact Ext.covariant_sequence_exact₁ P hS x (Subsingleton.elim _ 0) rfl

private def dimensionShiftCycles (P : C) (K : CochainComplex C ℕ)
    (hExact : ∀ j : ℕ, K.ExactAt (j + 1)) (hAcyclic : ∀ j k : ℕ, Subsingleton (Ext P (K.X j) (k + 1)))
    (j n : ℕ) : Ext P (K.cycles j) (n + 1) ≃+ Ext P (K.cycles (j + n)) 1 := by
  induction n generalizing j with
  | zero => exact AddEquiv.refl _
  | succ n ih =>
    haveI : Subsingleton (Ext P (cycleSequence K j).X₂ (n + 1)) := hAcyclic j n
    haveI : Subsingleton (Ext P (cycleSequence K j).X₂ (n + 2)) := hAcyclic j (n + 1)
    have h : j + 1 + n = j + (n + 1) := by omega
    rw [← h]
    exact (dimensionShift P (cycleSequence_exact K j (hExact j)) n).symm.trans (ih (j + 1))

private abbrev G (P : C) := preadditiveCoyoneda.obj (op P)
private abbrev mapped (P : C) (K : CochainComplex C ℕ) :=
  ((G P).mapHomologicalComplex (ComplexShape.up ℕ)).obj K

private def mappedCyclesIso (P : C) (K : CochainComplex C ℕ) (j : ℕ) :
    (mapped P K).cycles j ≅ (G P).obj (K.cycles j) :=
  ((mapped P K).cyclesIsKernel (i := j) (j := j + 1) (next_eq j)).conePointUniqueUpToIso
    (KernelFork.mapIsLimit _ (K.cyclesIsKernel (i := j) (j := j + 1) (next_eq j)) (G P))

omit [HasExt.{v} C] in
private theorem mappedCyclesIso_hom_iCycles (P : C) (K : CochainComplex C ℕ) (j : ℕ) :
    (mappedCyclesIso P K j).hom ≫ (G P).map (K.iCycles j) = (mapped P K).iCycles j := by
  unfold mappedCyclesIso
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ Limits.WalkingParallelPair.zero

omit [HasExt.{v} C] in
private theorem mapped_toCycles (P : C) (K : CochainComplex C ℕ) (j : ℕ) :
    (mapped P K).toCycles j (j + 1) ≫ (mappedCyclesIso P K (j + 1)).hom =
      (G P).map (K.toCycles j (j + 1)) := by
  rw [← cancel_mono ((G P).map (K.iCycles (j + 1))), Category.assoc, mappedCyclesIso_hom_iCycles,
    toCycles_i, ← Functor.map_comp, toCycles_i]
  rfl

private abbrev boundarySequence (P : C) {S : ShortComplex C} (hS : S.ShortExact) :
    ShortComplex AddCommGrpCat.{v} :=
  let δ : (P ⟶ S.X₃) →+ Ext P S.X₁ 1 :=
    (hS.extClass.postcomp P (zero_add 1)).comp Ext.addEquiv₀.symm.toAddMonoidHom
  ShortComplex.mk ((G P).map S.g) (AddCommGrpCat.ofHom δ) (by
    apply ConcreteCategory.hom_ext
    intro x
    change (Ext.mk₀ (x ≫ S.g)).comp hS.extClass (zero_add 1) = 0
    rw [← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, Ext.comp_zero])

private theorem boundarySequence_exact (P : C) {S : ShortComplex C} (hS : S.ShortExact) :
    (boundarySequence P hS).Exact := by
  rw [ShortComplex.ab_exact_iff]
  intro x hx
  change (Ext.mk₀ x).comp hS.extClass (zero_add 1) = 0 at hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₃ P hS (Ext.mk₀ x) (zero_add 1) hx
  obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective P S.X₂).surjective y
  rw [Ext.mk₀_comp_mk₀] at hy
  exact ⟨z, (Ext.mk₀_bijective P S.X₃).injective hy⟩

private theorem boundarySequence_epi (P : C) {S : ShortComplex C} (hS : S.ShortExact)
    [Subsingleton (Ext P S.X₂ 1)] : Epi (boundarySequence P hS).g := by
  apply (AddCommGrpCat.epi_iff_surjective _).mpr
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ P hS (n₀ := 0) x (Subsingleton.elim _ 0) (zero_add 1)
  obtain ⟨z, rfl⟩ := (Ext.mk₀_bijective P S.X₃).surjective y
  exact ⟨z, hy⟩

private def homologyEquivCycleExt (P : C) (K : CochainComplex C ℕ) (j : ℕ)
    (h : K.ExactAt (j + 1)) [Subsingleton (Ext P (K.X j) 1)] :
    (mapped P K).homology (j + 1) ≃+ Ext P (K.cycles j) 1 := by
  let M := mapped P K
  let e := mappedCyclesIso P K (j + 1)
  let hS := cycleSequence_exact K j h
  let S := boundarySequence P hS
  let β := e.hom ≫ S.g
  have hw : M.toCycles j (j + 1) ≫ β = 0 := by
    rw [← Category.assoc, mapped_toCycles]
    exact S.zero
  let T := ShortComplex.mk (M.toCycles j (j + 1)) β hw
  let comparison : T ≅ S := ShortComplex.isoMk (Iso.refl _) e (Iso.refl _)
    (by simp only [Iso.refl_hom, Category.id_comp]; exact (mapped_toCycles P K j).symm)
    (by simp only [Iso.refl_hom, Category.comp_id]; rfl)
  have hT : T.Exact := ShortComplex.exact_of_iso comparison.symm (boundarySequence_exact P hS)
  haveI : Epi S.g := boundarySequence_epi P hS
  haveI : Epi T.g := epi_comp e.hom S.g
  let hc := M.homologyIsCokernel (i := j) (j := j + 1) (prev_eq j)
  exact (IsColimit.coconePointUniqueUpToIso hc hT.gIsCokernel).addCommGroupIsoToAddEquiv

/-- Positive Ext can be computed by a resolution whose terms are Ext-acyclic. -/
def extEquivAcyclicComplex (P F : C) (K : CochainComplex C ℕ) (e₀ : F ≅ K.cycles 0)
    (hExact : ∀ j : ℕ, K.ExactAt (j + 1)) (hAcyclic : ∀ j k : ℕ, Subsingleton (Ext P (K.X j) (k + 1)))
    (n : ℕ) : Ext P F (n + 1) ≃+ (mapped P K).homology (n + 1) := by
  haveI := hAcyclic n 0
  let a := ((extFunctorObj P (n + 1)).mapIso e₀).addCommGroupIsoToAddEquiv
  let b := dimensionShiftCycles P K hExact hAcyclic 0 n
  let c := homologyEquivCycleExt P K n (hExact n)
  have e : Ext P (K.cycles (0 + n)) 1 ≃+ Ext P (K.cycles n) 1 := by rw [Nat.zero_add]
  exact a.trans (b.trans (e.trans c.symm))

end PhilipponAcyclicResolution

end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open PhilipponEtaleAcyclicCohomology (globalSections)


namespace PhilipponEtaleDerivedSections

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

private abbrev constants (X : Scheme.{u}) : Ab X :=
  (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))

private abbrev liftSections := AddCommGrpCat.uliftFunctor.{u + 1, u}

private def sectionsCoyonedaIso (X : Scheme.{u}) :
    preadditiveCoyoneda.obj (op (constants X)) ≅ globalSections X ⋙ liftSections.{u} := by
  let T : X.Etale := Scheme.Etale.mk (𝟙 X)
  let hT : IsTerminal T := IsTerminal.isTerminalOfObj (Scheme.Etale.forget X) _ Over.mkIdTerminal
  let adj := constantSheafAdj X.smallEtaleTopology AddCommGrpCat.{u} hT
  let e (F : Ab X) : (constants X ⟶ F) ≃+ (globalSections X).obj F :=
    (adj.homAddEquiv _ F).trans (AddCommGrpCat.uliftZMultiplesAddEquiv _)
  refine NatIso.ofComponents (fun F => ((e F).trans AddEquiv.ulift.symm).toAddCommGrpIso) ?_
  intro F G a
  apply ConcreteCategory.hom_ext
  intro h
  change ULift.up (e G (h ≫ a)) = ULift.up ((globalSections X).map a (e F h))
  congr 1

/-- Applying Hom from the constant integer sheaf or taking global sections
produces cochain complexes with additively equivalent homology. -/
def homologyEquivGlobalSections {X : Scheme.{u}} (I : CochainComplex (Ab X) ℕ) (n : ℕ) :
    (((preadditiveCoyoneda.obj (op (constants X))).mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n ≃+
      (((globalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj I).homology n := by
  let Γ := globalSections X
  let K := (Γ.mapHomologicalComplex (ComplexShape.up ℕ)).obj I
  let e := (HomologicalComplex.homologyFunctor AddCommGrpCat.{u + 1} (ComplexShape.up ℕ) n).mapIso
    ((Functor.mapHomologicalComplexCompIso (sectionsCoyonedaIso X).symm (ComplexShape.up ℕ)).symm.app I)
  exact (e ≪≫ (K.sc n).mapHomologyIso liftSections).addCommGroupIsoToAddEquiv.trans AddEquiv.ulift

end PhilipponEtaleDerivedSections

end

end

end

section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open PhilipponEtaleAcyclicCohomology (globalSections)
open PhilipponEtaleBaseChangeMap (stalkToFiberSections stalkOfHigherImageIso)
open PhilipponEtaleClosedPushforward (pushforward)
open PhilipponEtaleSmallSite (pullbackSheaves pullbackAdjunction)


namespace PhilipponEtalePullbackResolution

universe u

private abbrev Ab (X : Scheme.{u}) := Sheaf X.smallEtaleTopology AddCommGrpCat.{u}

local instance (X : Scheme.{u}) : (globalSections X).Additive where
  map_add := rfl

local instance {X Y : Scheme.{u}} (f : Y ⟶ X) : (pullbackSheaves f).Additive :=
  (pullbackAdjunction f).left_adjoint_additive

private theorem extLarge (X : Scheme.{u}) : HasExt.{u + 1} (Ab X) := by
  have h (P Q : Ab X) (n : ℕ) : Small.{u + 1} (Ext.{u} P Q n) :=
    small_succ (Ext.{u} P Q n)
  exact (hasExt_iff_small_ext.{u + 1, u} (Ab X)).mpr h

private def extLift {X : Scheme.{u}} [HasExt.{u + 1} (Ab X)] (P Q : Ab X) (n : ℕ) :
    Ext.{u} P Q n ≃+ Ext.{u + 1} P Q n :=
  letI := HasDerivedCategory.standard (Ab X)
  Ext.homAddEquiv.trans Ext.homAddEquiv.symm

/-- A pulled-back injective resolution computes the positive cohomology of
the inverse image when all its terms have zero higher cohomology. -/
def cohomologyEquivPullbackResolution {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Ab X)
    (I : InjectiveResolution F)
    (h : ∀ j k : ℕ, Subsingleton (((pullbackSheaves f).obj (I.cocomplex.X j)).H (k + 1)))
    (n : ℕ) : ((pullbackSheaves f).obj F).H (n + 1) ≃+
      (((pullbackSheaves f ⋙ globalSections Y).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology (n + 1) := by
  let L := pullbackSheaves f
  let K := (L.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  haveI : L.IsLeftAdjoint := (pullbackAdjunction f).isLeftAdjoint
  have hExact (j : ℕ) : K.ExactAt (j + 1) :=
    (show (I.cocomplex.sc (j + 1)).Exact from I.cocomplex_exactAt_succ j).map L
  letI : HasExt.{u + 1} (Ab Y) := extLarge Y
  let P := (constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))
  have hExt (j k : ℕ) : Subsingleton (Ext.{u + 1} P (K.X j) (k + 1)) := by
    have : Subsingleton (Ext.{u} P (K.X j) (k + 1)) := h j k
    exact (extLift P (K.X j) (k + 1)).symm.injective.subsingleton
  let e := PhilipponAcyclicResolution.extEquivAcyclicComplex P (L.obj F) K
    (asIso (I.toRightDerivedZero' L)) hExact hExt n
  exact (extLift P (L.obj F) (n + 1)).trans
    (e.trans (PhilipponEtaleDerivedSections.homologyEquivGlobalSections K (n + 1)))

end PhilipponEtalePullbackResolution

end

end

end

section

section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian

universe siteU

local instance (priority := 2000) etaleHasSheafify (X : Scheme.{siteU}) :
    HasSheafify X.smallEtaleTopology AddCommGrpCat.{siteU} := inferInstance

local instance (priority := 2000) etaleHasExt (X : Scheme.{siteU}) :
    HasExt.{siteU} (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

local instance (priority := 2000) etaleEnoughInjectives (X : Scheme.{siteU}) :
    EnoughInjectives (Sheaf X.smallEtaleTopology AddCommGrpCat.{siteU}) := inferInstance

universe u

open CategoryTheory.Abelian

local instance (W : Scheme.{u}) : (PhilipponEtaleAcyclicCohomology.globalSections W).Additive where
  map_add := rfl

local instance {U V : Scheme.{u}} (g : U ⟶ V) : (PhilipponEtaleSmallSite.pullbackSheaves g).Additive :=
  (PhilipponEtaleSmallSite.pullbackAdjunction g).left_adjoint_additive

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

theorem solution {X Y : Scheme.{u}}
    (f : Y ⟶ X) [IsProper f] {K : Type u} [Field K] [IsSepClosed K]
    (s : Spec (CommRingCat.of K) ⟶ X)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u})
    (I : InjectiveResolution F) (q : ℕ) :
    Nonempty (AddCommGrpCat.of (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f)).obj F).H (q + 1)) ≅
      (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f) ⋙ PhilipponEtaleAcyclicCohomology.globalSections (pullback (PhilipponEtaleStrictHenselization.toBase s) f)).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        I.cocomplex).homology (q + 1)) := by
  have ha (j k : ℕ) :
      Subsingleton (((PhilipponEtaleSmallSite.pullbackSheaves (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f)).obj (I.cocomplex.X j)).H (k + 1)) := by
    let : Injective (I.cocomplex.X j) := I.injective j
    exact PhilipponStrictLocalPresheaf.strictLocalPullback_acyclic_of_injective s f (I.cocomplex.X j) k
  exact ⟨(PhilipponEtalePullbackResolution.cohomologyEquivPullbackResolution
    (pullback.snd (PhilipponEtaleStrictHenselization.toBase s) f) F I ha q).toAddCommGrpIso⟩


end

end

end
