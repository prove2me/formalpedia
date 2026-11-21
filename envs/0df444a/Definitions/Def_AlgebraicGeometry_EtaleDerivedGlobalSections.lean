-- Prove2me | Definitions.Def_AlgebraicGeometry_EtaleDerivedGlobalSections
-- name    : AlgebraicGeometry_EtaleDerivedGlobalSections
-- status  : Definition
-- author  : @tomasz
-- created : 2026-11-21T03:35:40.339662+00:00
-- url     : https://prove2.me/theorems/371d63ed-0f0e-469a-bf52-f36a280a3b02
-- title:
--   Injective and acyclic resolutions for étale cohomology
-- statement:
--   The identification of Ext from the constant integer sheaf with cohomology of global sections of an injective or acyclic resolution.

import Definitions.Def_AlgebraicGeometry_EtaleStrictLocalSites

noncomputable section

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


namespace PhilipponDerivedHom

universe u v u' v' w

private abbrev e := ComplexShape.embeddingUpNat

section Extend

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  (G : C ⥤ D) [G.Additive] (I : CochainComplex C ℕ)

private abbrev mapped := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I

private def extendComponent (j : ℤ) :
    ((mapped G I).extend e).X j ≅ G.obj ((I.extend e).X j) := by
  classical
  by_cases h : ∃ n, e.f n = j
  · exact (mapped G I).extendXIso e h.choose_spec ≪≫ G.mapIso (I.extendXIso e h.choose_spec).symm
  · exact ((mapped G I).isZero_extend_X e j (fun n hn => h ⟨n, hn⟩)).iso
      (G.map_isZero (I.isZero_extend_X e j (fun n hn => h ⟨n, hn⟩)))

private theorem extendComponent_at {n : ℕ} {j : ℤ} (h : e.f n = j) :
    extendComponent G I j =
      (mapped G I).extendXIso e h ≪≫ G.mapIso (I.extendXIso e h).symm := by
  classical
  let r : ∃ m, e.f m = j := ⟨n, h⟩
  unfold extendComponent
  rw [dif_pos r]
  have uniqueIso (m : ℕ) (hm : e.f m = j) (hn : m = n) :
      (mapped G I).extendXIso e hm ≪≫ G.mapIso (I.extendXIso e hm).symm =
        (mapped G I).extendXIso e h ≪≫ G.mapIso (I.extendXIso e h).symm := by
    subst m
    rfl
  exact uniqueIso r.choose r.choose_spec (e.injective_f (r.choose_spec.trans h.symm))

/-- An additive functor commutes with extending a cochain complex by zero
from nonnegative to integer degrees. -/
def mapExtendIso : ((mapped G I).extend e) ≅ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj (I.extend e) := by
  refine Hom.isoOfComponents (extendComponent G I) ?_
  intro j k _
  by_cases hj : ∃ n, e.f n = j
  · by_cases hk : ∃ n, e.f n = k
    · obtain ⟨n, hn⟩ := hj
      obtain ⟨m, hm⟩ := hk
      change (extendComponent G I j).hom ≫ G.map ((I.extend e).d j k) =
        ((mapped G I).extend e).d j k ≫ (extendComponent G I k).hom
      rw [extendComponent_at G I hn, extendComponent_at G I hm,
        extend_d_eq _ e hn hm, extend_d_eq _ e hn hm]
      simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Functor.map_comp,
        Functor.mapHomologicalComplex_obj_d, Category.assoc, Iso.inv_hom_id_assoc]
      rw [← G.map_comp_assoc (I.extendXIso e hn).inv (I.extendXIso e hn).hom,
        Iso.inv_hom_id, G.map_id, Category.id_comp]
    · exact (G.map_isZero (I.isZero_extend_X e k (fun n hn => hk ⟨n, hn⟩))).eq_of_tgt _ _
  · exact ((mapped G I).isZero_extend_X e j (fun n hn => hj ⟨n, hn⟩)).eq_of_src _ _

end Extend

section Coyoneda

variable {C : Type u} [Category.{v} C] [Abelian C] (P : C)

private abbrev homFunctor := preadditiveCoyoneda.obj (op P)

private def homComplexIso (K : CochainComplex C ℤ) :
    ((homFunctor P).mapHomologicalComplex (ComplexShape.up ℤ)).obj K ≅
      CochainComplex.HomComplex ((CochainComplex.singleFunctor C 0).obj P) K := by
  refine Hom.isoOfComponents (fun j => (CochainComplex.HomComplex.Cochain.fromSingleEquiv
    (X := P) (K := K) (p := 0) (zero_add j)).symm.toAddCommGrpIso) ?_
  intro j k _
  apply ConcreteCategory.hom_ext
  intro f
  change CochainComplex.HomComplex.δ j k
      (CochainComplex.HomComplex.Cochain.fromSingleMk f (zero_add j)) =
    CochainComplex.HomComplex.Cochain.fromSingleMk (f ≫ K.d j k) (zero_add k)
  exact CochainComplex.HomComplex.Cochain.δ_fromSingleMk f (zero_add j) _ _ (zero_add k)

/-- Compute Ext as the homology of the complex obtained by applying
`Hom(P, -)` to an injective resolution. -/
def extEquivHomology [HasExt.{w} C] {F : C} (I : InjectiveResolution F) (q : ℕ) :
    Ext P F q ≃+ (((homFunctor P).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology q := by
  let J := I.cocomplex.extend e
  let K := (CochainComplex.singleFunctor C 0).obj P
  let G := homFunctor P
  let M := (G.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  let h := homologyFunctor AddCommGrpCat.{v} (ComplexShape.up ℤ) (q : ℤ)
  let e₁ := PhilipponDerivedAdjunction.extViaExtendedResolution I P q
  let e₂ := (CochainComplex.HomComplex.CohomologyClass.homAddEquiv (K := K) (L := J) (n := (q : ℤ))).symm
  let e₃ := (CochainComplex.HomComplex.homologyAddEquiv K J (q : ℤ)).symm
  let e₄ := h.mapIso ((mapExtendIso G I.cocomplex ≪≫ homComplexIso P J).symm)
  let e₅ := M.extendHomologyIso e (j := q) (j' := (q : ℤ)) rfl
  exact e₁.trans (e₂.trans (e₃.trans
    ((e₄ ≪≫ e₅).addCommGroupIsoToAddEquiv)))

end Coyoneda

end PhilipponDerivedHom

end

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

/-- Étale cohomology can be computed as the homology of global sections of
any injective resolution, using the Ext definition of `Sheaf.H`. -/
def cohomologyEquivResolution {X : Scheme.{u}} (F : Ab X) (I : InjectiveResolution F) (n : ℕ) :
    F.H n ≃+ (((globalSections X).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex).homology n :=
  (PhilipponDerivedHom.extEquivHomology (constants X) I n).trans
    (homologyEquivGlobalSections I.cocomplex n)

/-- The Ext definition of étale cohomology agrees with the right derived
functor of global sections. -/
def cohomologyEquivRightDerived {X : Scheme.{u}} (F : Ab X) (n : ℕ) :
    F.H n ≃+ (((globalSections X).rightDerived n).obj F) :=
  let I := injectiveResolution F
  (cohomologyEquivResolution F I n).trans
    (I.isoRightDerivedObj (globalSections X) n).symm.addCommGroupIsoToAddEquiv

end PhilipponEtaleDerivedSections

end

end


