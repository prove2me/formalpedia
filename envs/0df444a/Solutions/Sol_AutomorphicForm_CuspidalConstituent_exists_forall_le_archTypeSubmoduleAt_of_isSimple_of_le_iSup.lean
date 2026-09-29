-- Prove2me | solution 1 for AutomorphicForm.CuspidalConstituent.exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.553648+00:00
-- url     : https://prove2.me/submissions/e1497c20-0895-5ef5-b1e1-0e0815dc0fb0

import Definitions.Def_AutomorphicForm_CuspidalSpectrumCarrier
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.RingTheory.FiniteLength
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.Artinian.Module
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open AutomorphicForm.CuspidalConstituent AutomorphicForm.CuspidalSpectrum
open scoped ComplexConjugate ENNReal InnerProductSpace

attribute [local instance] NumberField.AdelicHaar.glBorel

noncomputable section

namespace SubqPrep

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

private def IsSubquotient (R : Type*) [Ring R] (M : Type*) [AddCommGroup M] [Module R M]
    (S : Type*) [AddCommGroup S] [Module R S] : Prop :=
  ∃ (A : Submodule R M) (f : A →ₗ[R] S), Function.Surjective f

private theorem IsSubquotient.of_equiv {S : Type*} [AddCommGroup S] [Module R S] {S' : Type*} [AddCommGroup S'] [Module R S']
    (h : IsSubquotient R M S) (e : S ≃ₗ[R] S') : IsSubquotient R M S' := by
  obtain ⟨A, f, hf⟩ := h
  exact ⟨A, e.toLinearMap ∘ₗ f, e.surjective.comp hf⟩

private theorem IsSubquotient.of_injective {N : Type*} [AddCommGroup N] [Module R N]
    {S : Type*} [AddCommGroup S] [Module R S]
    (h : IsSubquotient R N S) (i : N →ₗ[R] M) (hi : Function.Injective i) : IsSubquotient R M S := by
  obtain ⟨A, f, hf⟩ := h

  let e : A ≃ₗ[R] (A.map i) := (Submodule.equivMapOfInjective i hi A)
  exact ⟨A.map i, f ∘ₗ e.symm.toLinearMap, hf.comp e.symm.surjective⟩

private theorem IsSubquotient.dichotomy {S : Type*} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (h : IsSubquotient R M S) (N : Submodule R M) :
    IsSubquotient R N S ∨ IsSubquotient R (M ⧸ N) S := by
  obtain ⟨A, f, hf⟩ := h

  let AN : Submodule R A := Submodule.comap A.subtype N
  let g : AN →ₗ[R] S := f ∘ₗ AN.subtype
  rcases eq_bot_or_eq_top (LinearMap.range g) with hg | hg
  ·
    right
    let h : A →ₗ[R] M ⧸ N := N.mkQ ∘ₗ A.subtype
    have hker : LinearMap.ker h ≤ LinearMap.ker f := by
      intro a ha
      have haN : (a : M) ∈ N := by
        simpa [h, LinearMap.mem_ker, Submodule.Quotient.mk_eq_zero] using ha
      have : g ⟨a, haN⟩ ∈ LinearMap.range g := LinearMap.mem_range_self g _
      rw [hg, Submodule.mem_bot] at this
      simpa [g] using this
    refine ⟨LinearMap.range h, (LinearMap.ker h).liftQ f hker ∘ₗ (LinearMap.quotKerEquivRange h).symm.toLinearMap, ?_⟩
    intro s
    obtain ⟨a, rfl⟩ := hf s
    refine ⟨LinearMap.quotKerEquivRange h (Submodule.Quotient.mk a), ?_⟩
    simp
  ·
    left
    have hgs : Function.Surjective g := LinearMap.range_eq_top.mp hg

    let AN' : Submodule R N := Submodule.comap N.subtype A
    let e : AN' →ₗ[R] AN :=
      { toFun := fun x => ⟨⟨(x : N), x.2⟩, by
          show ((⟨(x : N), x.2⟩ : A) : M) ∈ N
          exact (x : N).2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have he : Function.Surjective e := by
      rintro ⟨⟨m, hmA⟩, hmN⟩
      exact ⟨⟨⟨m, hmN⟩, hmA⟩, rfl⟩
    exact ⟨AN', g ∘ₗ e, hgs.comp he⟩

private theorem IsSubquotient.nonempty_equiv_of_isSimpleModule {S : Type*} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    [IsSimpleModule R M] (h : IsSubquotient R M S) : Nonempty (M ≃ₗ[R] S) := by
  obtain ⟨A, f, hf⟩ := h
  haveI : Nontrivial S := IsSimpleModule.nontrivial R S
  have hA : A ≠ ⊥ := by
    intro hA
    have hsub : Subsingleton A := by
      rw [hA]
      infer_instance
    have : Subsingleton S := ⟨fun x y => by
      obtain ⟨a, rfl⟩ := hf x
      obtain ⟨b, rfl⟩ := hf y
      rw [Subsingleton.elim a b]⟩
    exact false_of_nontrivial_of_subsingleton S
  have hA' : A = ⊤ := (eq_bot_or_eq_top A).resolve_left hA
  subst hA'
  let f' : M →ₗ[R] S := f ∘ₗ (Submodule.topEquiv (R := R) (M := M)).symm.toLinearMap
  have hf' : Function.Surjective f' := hf.comp (Submodule.topEquiv (R := R) (M := M)).symm.surjective
  have hker : LinearMap.ker f' = ⊥ := by
    rcases eq_bot_or_eq_top (LinearMap.ker f') with h | h
    · exact h
    · exfalso
      have : Subsingleton S := ⟨fun x y => by
        obtain ⟨a, rfl⟩ := hf' x
        obtain ⟨b, rfl⟩ := hf' y
        have ha : a ∈ LinearMap.ker f' := h ▸ Submodule.mem_top
        have hb : b ∈ LinearMap.ker f' := h ▸ Submodule.mem_top
        rw [LinearMap.mem_ker] at ha hb
        rw [ha, hb]⟩
      exact false_of_nontrivial_of_subsingleton S
  exact ⟨LinearEquiv.ofBijective f' ⟨LinearMap.ker_eq_bot.mp hker, hf'⟩⟩

end SubqPrep

namespace SubqPrep

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]

private abbrev entryQuot (p : Submodule R M × Submodule R M) : Type _ := ↥p.1 ⧸ (p.2.comap p.1.subtype)

private theorem nonempty_entryQuot_equiv_map (N : Submodule R M) (A B : Submodule R N) :
    Nonempty (entryQuot (R := R) (A, B) ≃ₗ[R] entryQuot (R := R) (A.map N.subtype, B.map N.subtype)) := by
  let e : ↥A ≃ₗ[R] ↥(A.map N.subtype) := Submodule.equivMapOfInjective N.subtype N.injective_subtype A
  refine ⟨Submodule.Quotient.equiv _ _ e ?_⟩
  ext ⟨x, hx⟩
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨⟨a, ha⟩, hB, hax⟩
    have hax' : ((a : N) : M) = x := by
      have := congrArg Subtype.val hax
      simpa [e] using this
    exact ⟨a, hB, hax'⟩
  · rintro ⟨b, hbB, hbx⟩
    obtain ⟨a', ha', hx'⟩ := (Submodule.mem_map.mp hx)
    have hb_a : b = a' := N.injective_subtype (by
      show (b : M) = (a' : M)
      rw [hbx]
      exact hx'.symm)
    refine ⟨⟨b, hb_a ▸ ha'⟩, hbB, ?_⟩
    apply Subtype.ext
    show ((e ⟨b, _⟩ : A.map N.subtype) : M) = x
    simp [e, hbx]

private theorem exists_list_forall_isSubquotient (h : IsFiniteLength R M) :
    ∃ l : List (Submodule R M × Submodule R M),
      (∀ p ∈ l, IsSimpleModule R (entryQuot p)) ∧
      ∀ (S : Type*) [AddCommGroup S] [Module R S], IsSimpleModule R S → IsSubquotient R M S →
        ∃ p ∈ l, Nonempty (entryQuot p ≃ₗ[R] S) := by
  induction h with
  | of_subsingleton =>
      refine ⟨[], fun p hp => by simp at hp, ?_⟩
      intro S _ _ hS hsq
      exfalso
      obtain ⟨A, f, hf⟩ := hsq
      haveI := IsSimpleModule.nontrivial R S
      have : Subsingleton S := ⟨fun x y => by
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        rw [Subsingleton.elim a b]⟩
      exact false_of_nontrivial_of_subsingleton S
  | @of_simple_quotient M' _ _ N hsimp hN ih =>
      obtain ⟨l, hl, hcov⟩ := ih
      have etop : entryQuot (R := R) ((⊤ : Submodule R M'), N) ≃ₗ[R] M' ⧸ N :=
        Submodule.Quotient.equiv _ _ Submodule.topEquiv (by
          ext x
          simp only [Submodule.mem_map, Submodule.mem_comap]
          constructor
          · rintro ⟨y, hy, rfl⟩
            simpa using hy
          · intro hx
            exact ⟨⟨x, Submodule.mem_top⟩, by simpa using hx, by simp⟩)
      refine ⟨(l.map fun p => (p.1.map N.subtype, p.2.map N.subtype)) ++
        [((⊤ : Submodule R M'), N)], ?_, ?_⟩
      · intro p hp
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hp
        rcases hp with ⟨q, hq, rfl⟩ | rfl
        · obtain ⟨e⟩ := nonempty_entryQuot_equiv_map N q.1 q.2
          haveI := hl q hq
          exact IsSimpleModule.congr e.symm
        · exact IsSimpleModule.congr etop
      · intro S _ _ hS hsq
        rcases hsq.dichotomy N with h1 | h2
        · obtain ⟨p, hp, ⟨e⟩⟩ := hcov S hS h1
          obtain ⟨e'⟩ := nonempty_entryQuot_equiv_map N p.1 p.2
          exact ⟨_, List.mem_append_left _ (List.mem_map.mpr ⟨p, hp, rfl⟩), ⟨e'.symm.trans e⟩⟩
        · haveI := hS
          obtain ⟨e⟩ := h2.nonempty_equiv_of_isSimpleModule
          exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), ⟨etop.trans e⟩⟩

end SubqPrep

namespace SubqPrep

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
variable {M' : Type*} [AddCommGroup M'] [Module R M']

private theorem IsSubquotient.of_ambient_equiv {S : Type*} [AddCommGroup S] [Module R S]
    (h : IsSubquotient R M S) (e : M ≃ₗ[R] M') : IsSubquotient R M' S :=
  h.of_injective e.toLinearMap e.injective

private theorem IsSubquotient.prod_elim {S : Type*} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    (h : IsSubquotient R (M × M') S) : IsSubquotient R M S ∨ IsSubquotient R M' S := by
  rcases h.dichotomy (LinearMap.ker (LinearMap.snd R M M')) with h1 | h2
  · left

    have e1 : M ≃ₗ[R] LinearMap.range (LinearMap.inl R M M') :=
      LinearEquiv.ofInjective (LinearMap.inl R M M') LinearMap.inl_injective
    have e2 : LinearMap.range (LinearMap.inl R M M') ≃ₗ[R] LinearMap.ker (LinearMap.snd R M M') :=
      LinearEquiv.ofEq _ _ (LinearMap.range_inl R M M')
    exact h1.of_ambient_equiv (e1.trans e2).symm
  · right
    exact h2.of_ambient_equiv (LinearMap.quotKerEquivOfSurjective _ LinearMap.snd_surjective)

private theorem IsSubquotient.pi_elim {S : Type*} [AddCommGroup S] [Module R S] [IsSimpleModule R S]
    {n : ℕ} {X : Fin n → Type*} [∀ i, AddCommGroup (X i)] [∀ i, Module R (X i)]
    (h : IsSubquotient R (∀ i, X i) S) : ∃ i, IsSubquotient R (X i) S := by
  induction n with
  | zero =>
      exfalso
      obtain ⟨A, f, hf⟩ := h
      haveI := IsSimpleModule.nontrivial R S
      haveI : Subsingleton (∀ i : Fin 0, X i) := ⟨fun a b => funext fun i => Fin.elim0 i⟩
      have : Subsingleton S := ⟨fun x y => by
        obtain ⟨a, rfl⟩ := hf x
        obtain ⟨b, rfl⟩ := hf y
        rw [Subsingleton.elim a b]⟩
      exact false_of_nontrivial_of_subsingleton S
  | succ n ih =>
      have h' := h.of_ambient_equiv (Fin.consLinearEquiv R X).symm
      rcases h'.prod_elim with h0 | hrest
      · exact ⟨0, h0⟩
      · obtain ⟨i, hi⟩ := ih hrest
        exact ⟨i.succ, hi⟩

end SubqPrep

namespace SubqPrep

open scoped MonoidAlgebra

variable {K : Type*} [Group K]

private noncomputable def conjRep {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ K E) (e : E ≃ₗ[ℂ] E') : Representation ℂ K E' where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by
    ext v
    simp
  map_mul' g h := by
    ext v
    simp

private theorem conjRep_apply {E E' : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup E'] [Module ℂ E']
    (ρ : Representation ℂ K E) (e : E ≃ₗ[ℂ] E') (g : K) (v : E') :
    conjRep ρ e g v = e (ρ g (e.symm v)) := rfl

private theorem exists_representation_fin_nonempty_equiv (E : Type*) [AddCommGroup E] [Module ℂ E] [Module ℂ[K] E]
    [IsScalarTower ℂ ℂ[K] E] [FiniteDimensional ℂ E] :
    ∃ (d : ℕ) (σ : Representation ℂ K (Fin d → ℂ)), Nonempty (σ.asModule ≃ₗ[ℂ[K]] E) := by
  let ρE : Representation ℂ K E := Representation.ofModule' E
  let b := Module.finBasis ℂ E
  let e : E ≃ₗ[ℂ] (Fin (Module.finrank ℂ E) → ℂ) := b.equivFun
  let σ : Representation ℂ K (Fin (Module.finrank ℂ E) → ℂ) := conjRep ρE e
  have hρE : ∀ (g : K) (x : E), ρE g x = MonoidAlgebra.of ℂ K g • x := by
    intro g x
    simp [ρE, Representation.ofModule', MonoidAlgebra.lift_symm_apply, Algebra.lsmul_coe]

  let f : σ.asModule →ₗ[ℂ] E := e.symm.toLinearMap ∘ₗ σ.asModuleEquiv.toLinearMap
  have hf : ∀ (c : ℂ[K]) (v : σ.asModule), f (c • v) = c • f v := by
    intro c v
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp [add_smul, hx, hy]
    | single g t =>
        simp only [f, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
        rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single, LinearMap.smul_apply,
          LinearEquiv.map_smul]
        show t • e.symm (σ g (σ.asModuleEquiv v)) = MonoidAlgebra.single g t • e.symm (σ.asModuleEquiv v)
        rw [conjRep_apply, LinearEquiv.symm_apply_apply, hρE, ← smul_assoc, MonoidAlgebra.of_apply, MonoidAlgebra.smul_single,
          smul_eq_mul, mul_one]
  let F : σ.asModule →ₗ[ℂ[K]] E :=
    { toFun := f
      map_add' := fun x y => f.map_add x y
      map_smul' := hf }
  have hFbij : Function.Bijective F := by
    show Function.Bijective f
    exact (e.symm.bijective).comp σ.asModuleEquiv.bijective
  exact ⟨_, σ, ⟨LinearEquiv.ofBijective F hFbij⟩⟩

set_option backward.isDefEq.respectTransparency false in

private theorem isIrreducible_of_equiv {d : ℕ} (σ : Representation ℂ K (Fin d → ℂ)) (E : Type*) [AddCommGroup E]
    [Module ℂ[K] E] (e : σ.asModule ≃ₗ[ℂ[K]] E) [IsSimpleModule ℂ[K] E] : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr e

end SubqPrep

namespace STDProof

open scoped MonoidAlgebra

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private def Rrep : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (AdelicGL2 (𝓞 F) F → ℂ) :=
  (rightRegular F).comp (rowIsometryInclAt₀ F w)

private theorem Rrep_apply (k : rowIsometrySubgroup₀ w.Completion) (f : AdelicGL2 (𝓞 F) F → ℂ) :
    Rrep F w k f = rightTranslate F (rowIsometryInclAt₀ F w k) f := rfl

private abbrev Fun : Type := (Rrep F w).asModule

private def stableSub (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) :
    Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (Fun F w) :=
  (Subrepresentation.mk (ρ := Rrep F w) S (fun k v hv => hS k v hv)).asSubmodule

private theorem mem_stableSub_iff (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (f : Fun F w) : f ∈ stableSub F w S hS ↔ (Rrep F w).asModuleEquiv f ∈ S := Iff.rfl

set_option backward.isDefEq.respectTransparency false in

private theorem of_smul_eq (k : rowIsometrySubgroup₀ w.Completion) (f : Fun F w) :
    (MonoidAlgebra.of ℂ (rowIsometrySubgroup₀ w.Completion) k • f : Fun F w)
      = (rightTranslate F (rowIsometryInclAt₀ F w k) ((Rrep F w).asModuleEquiv f) : AdelicGL2 (𝓞 F) F → ℂ) := by
  rw [MonoidAlgebra.of_apply, Representation.single_smul, one_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in

private theorem exists_stable_of_submodule (N : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (Fun F w)) :
    ∃ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ),
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') ∧
      ∀ f : Fun F w, (Rrep F w).asModuleEquiv f ∈ S' ↔ f ∈ N := by
  let σ : Subrepresentation (Rrep F w) := Subrepresentation.ofSubmodule' N
  refine ⟨σ.toSubmodule, fun k g hg => ?_, fun f => Iff.rfl⟩
  have := σ.apply_mem_toSubmodule k hg
  rwa [Rrep_apply] at this

end STDProof

namespace STDProof

open scoped MonoidAlgebra

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

set_option backward.isDefEq.respectTransparency false in
private theorem isSimpleModule_stableSub (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (hne : S ≠ ⊥)
    (hsimple : ∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
      (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
      S' = ⊥ ∨ S' = S) :
    IsSimpleModule ℂ[rowIsometrySubgroup₀ w.Completion] ↥(stableSub F w S hS) := by
  obtain ⟨f₀, hf₀S, hf₀ne⟩ := (Submodule.ne_bot_iff S).mp hne
  haveI : Nontrivial ↥(stableSub F w S hS) :=
    ⟨⟨⟨(Rrep F w).asModuleEquiv.symm f₀, (mem_stableSub_iff F w S hS _).mpr hf₀S⟩, 0,
      fun h => hf₀ne (congrArg Subtype.val h)⟩⟩
  suffices hall : ∀ N : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ↥(stableSub F w S hS), N = ⊥ ∨ N = ⊤ by
    haveI : IsSimpleOrder (Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ↥(stableSub F w S hS)) := ⟨hall⟩
    exact ⟨⟩
  intro N
  let N' : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (Fun F w) := N.map (stableSub F w S hS).subtype
  obtain ⟨S', hS'st, hS'mem⟩ := exists_stable_of_submodule F w N'
  have hN'le : N' ≤ stableSub F w S hS := Submodule.map_subtype_le _ _
  have hS'le : S' ≤ S := fun f hf =>
    (mem_stableSub_iff F w S hS ((Rrep F w).asModuleEquiv.symm f)).mp (hN'le ((hS'mem _).mp hf))
  rcases hsimple S' hS'le hS'st with h | h
  · left
    refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
    have hx' : (Rrep F w).asModuleEquiv (x : Fun F w) ∈ S' := (hS'mem _).mpr (Submodule.mem_map_of_mem hx)
    rw [h, Submodule.mem_bot] at hx'
    exact Subtype.ext hx'
  · right
    refine Submodule.eq_top_iff'.mpr fun x => ?_
    have hxS : (Rrep F w).asModuleEquiv (x : Fun F w) ∈ S' := by
      rw [h]
      exact (mem_stableSub_iff F w S hS _).mp x.2
    obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp ((hS'mem _).mp hxS)
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

set_option backward.isDefEq.respectTransparency false in
private theorem isFiniteLength_asModule {d : ℕ} (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ)) :
    IsFiniteLength ℂ[rowIsometrySubgroup₀ w.Completion] ρ.asModule := by
  rw [isFiniteLength_iff_isNoetherian_isArtinian]
  haveI : IsNoetherian ℂ ρ.asModule := IsNoetherian.iff_fg.mpr inferInstance
  haveI : IsArtinian ℂ ρ.asModule := isArtinian_of_fg_of_artinian'
  exact ⟨isNoetherian_of_tower ℂ inferInstance, isArtinian_of_tower ℂ inferInstance⟩

end STDProof

namespace STDProof

open scoped MonoidAlgebra

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private abbrev Entry (m : ℕ) (ρs : Fin m → ArchRepAt F w) : Type :=
  Σ i : Fin m, ((Fin (ρs i).n → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) × (Fin (ρs i).n → ℂ)

private theorem exists_list_of_mem_iSup (m : ℕ) (ρs : Fin m → ArchRepAt F w) (f : AdelicGL2 (𝓞 F) F → ℂ)
    (hf : f ∈ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    ∃ l : List (Entry F w m ρs),
      (∀ e ∈ l, IsRightEquivariant (rowIsometryInclAt₀ F w) (ρs e.1).ρ e.2.1) ∧ f = (l.map fun e => e.2.1 e.2.2).sum := by
  refine Submodule.iSup_induction _
    (motive := fun f => ∃ l : List (Entry F w m ρs),
      (∀ e ∈ l, IsRightEquivariant (rowIsometryInclAt₀ F w) (ρs e.1).ρ e.2.1) ∧ f = (l.map fun e => e.2.1 e.2.2).sum)
    hf ?_ ?_ ?_
  · intro i f hfi
    change f ∈ typeSubmodule (rowIsometryInclAt₀ F w) (ρs i).ρ at hfi
    unfold typeSubmodule at hfi
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hfi
    · rintro _ ⟨T, hT, v, rfl⟩
      exact ⟨[⟨i, T, v⟩], by simp [hT], by simp⟩
    · exact ⟨[], by simp, by simp⟩
    · rintro f g - - ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
      refine ⟨l₁ ++ l₂, fun e he => ?_, by simp⟩
      rcases List.mem_append.mp he with he | he
      · exact h₁ e he
      · exact h₂ e he
    · rintro c f - ⟨l, hl, rfl⟩
      refine ⟨l.map fun e => ⟨e.1, e.2.1, c • e.2.2⟩, fun e he => ?_, ?_⟩
      · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
        exact hl e' he'
      · rw [List.smul_sum, List.map_map, List.map_map]
        congr 1
        refine List.map_congr_left fun e _ => ?_
        simp
  · exact ⟨[], by simp, by simp⟩
  · rintro f g ⟨l₁, h₁, rfl⟩ ⟨l₂, h₂, rfl⟩
    refine ⟨l₁ ++ l₂, fun e he => ?_, by simp⟩
    rcases List.mem_append.mp he with he | he
    · exact h₁ e he
    · exact h₂ e he

set_option backward.isDefEq.respectTransparency false in

private def linOfEquivariant {d : ℕ} (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (T : (Fin d → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) (hT : IsRightEquivariant (rowIsometryInclAt₀ F w) σ T) :
    σ.asModule →ₗ[ℂ[rowIsometrySubgroup₀ w.Completion]] Fun F w where
  toFun v := (Rrep F w).asModuleEquiv.symm (T (σ.asModuleEquiv v))
  map_add' x y := by simp
  map_smul' c v := by
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add x y hx hy => simp only [add_smul, map_add, hx, hy]
    | single k t =>
        rw [Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single, LinearMap.smul_apply,
          map_smul, RingHom.id_apply]
        apply (Rrep F w).asModuleEquiv.injective
        rw [LinearEquiv.apply_symm_apply, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single,
          LinearMap.smul_apply, LinearEquiv.apply_symm_apply]
        congr 1
        funext x
        exact hT k (σ.asModuleEquiv v) x

private theorem linOfEquivariant_apply {d : ℕ} (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (T : (Fin d → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ)) (hT : IsRightEquivariant (rowIsometryInclAt₀ F w) σ T) (v : σ.asModule) :
    (Rrep F w).asModuleEquiv (linOfEquivariant F w σ T hT v) = T (σ.asModuleEquiv v) := rfl

end STDProof

namespace STDProof

open scoped MonoidAlgebra
open SubqPrep

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

private theorem sum_univ_get_map {α M : Type*} [AddCommMonoid M] (l : List α) (g : α → M) :
    ∑ s : Fin l.length, g (l.get s) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
      change ∑ s : Fin (l.length + 1), g ((a :: l).get s) = _
      rw [Fin.sum_univ_succ]
      simp

set_option backward.isDefEq.respectTransparency false in

private theorem isSubquotient_of_le_iSup (m : ℕ) (ρs : Fin m → ArchRepAt F w)
    (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    [FiniteDimensional ℂ ↥S] (hle : S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i)) :
    ∃ (n : ℕ) (idx : Fin n → Fin m),
      IsSubquotient ℂ[rowIsometrySubgroup₀ w.Completion] (∀ t : Fin n, (ρs (idx t)).ρ.asModule) ↥(stableSub F w S hS) := by
  classical
  let b := Module.finBasis ℂ ↥S
  choose L hLeq hLsum using fun l : Fin (Module.finrank ℂ ↥S) =>
    exists_list_of_mem_iSup F w m ρs ((b l : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) (hle (b l).2)
  let I : Type := Σ l : Fin (Module.finrank ℂ ↥S), Fin (L l).length
  let ent : I → Entry F w m ρs := fun p => (L p.1).get p.2
  have hent : ∀ p : I, IsRightEquivariant (rowIsometryInclAt₀ F w) (ρs (ent p).1).ρ (ent p).2.1 :=
    fun p => hLeq p.1 _ (List.get_mem _ _)
  let X : I → Type := fun p => (ρs (ent p).1).ρ.asModule
  let Θ : (∀ p : I, X p) →ₗ[ℂ[rowIsometrySubgroup₀ w.Completion]] Fun F w :=
    ∑ p : I, (linOfEquivariant F w _ (ent p).2.1 (hent p)) ∘ₗ LinearMap.proj p

  have hΘ : ∀ l : Fin (Module.finrank ℂ ↥S), ∃ x : ∀ p : I, X p,
      (Rrep F w).asModuleEquiv (Θ x) = ((b l : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) := by
    intro l
    let x : ∀ p : I, X p := fun p => if p.1 = l then (ρs (ent p).1).ρ.asModuleEquiv.symm (ent p).2.2 else 0
    refine ⟨x, ?_⟩
    rw [hLsum l]
    have hgoal : (Rrep F w).asModuleEquiv (Θ x) = ∑ p : I, (if p.1 = l then (ent p).2.1 (ent p).2.2 else 0) := by
      simp only [Θ, LinearMap.coe_sum, Finset.sum_apply, LinearMap.comp_apply, map_sum]
      refine Finset.sum_congr rfl (fun p _ => ?_)
      change (Rrep F w).asModuleEquiv (linOfEquivariant F w _ (ent p).2.1 (hent p)
        (if p.1 = l then (ρs (ent p).1).ρ.asModuleEquiv.symm (ent p).2.2 else 0)) = _
      split_ifs with h
      · rw [linOfEquivariant_apply, LinearEquiv.apply_symm_apply]
      · rw [map_zero, map_zero]
    rw [hgoal, ← Finset.univ_sigma_univ, Finset.sum_sigma]
    rw [Finset.sum_eq_single l]
    · have hif : ∀ s : Fin (L l).length,
          (if (⟨l, s⟩ : I).1 = l then (ent ⟨l, s⟩).2.1 (ent ⟨l, s⟩).2.2 else 0) = (ent ⟨l, s⟩).2.1 (ent ⟨l, s⟩).2.2 :=
        fun s => if_pos rfl
      simp only [hif]
      exact sum_univ_get_map (L l) fun e => e.2.1 e.2.2
    · intro l' _ hl'
      simp [hl']
    · intro h
      exact absurd (Finset.mem_univ l) h
  choose xs hxs using hΘ

  have hrange : ∀ y : ↥(stableSub F w S hS), ∃ x : ∀ p : I, X p, Θ x = (y : Fun F w) := by
    intro y
    let ys : ↥S := ⟨(Rrep F w).asModuleEquiv (y : Fun F w), (mem_stableSub_iff F w S hS _).mp y.2⟩
    refine ⟨∑ l, (b.repr ys l) • xs l, ?_⟩
    apply (Rrep F w).asModuleEquiv.injective
    rw [map_sum, map_sum]
    have hl : ∀ l, (Rrep F w).asModuleEquiv (Θ ((b.repr ys l) • xs l))
        = (b.repr ys l) • ((b l : ↥S) : AdelicGL2 (𝓞 F) F → ℂ) := by
      intro l
      rw [LinearMap.map_smul_of_tower, LinearEquiv.map_smul, hxs l]
    simp only [hl]
    have hsum := congrArg Subtype.val (b.sum_repr ys)
    simp only [AddSubmonoidClass.coe_finsetSum, SetLike.val_smul] at hsum
    exact hsum
  have hsq : IsSubquotient ℂ[rowIsometrySubgroup₀ w.Completion] (∀ p : I, X p) ↥(stableSub F w S hS) := by
    refine ⟨(stableSub F w S hS).comap Θ, Θ.restrict (fun x hx => hx), ?_⟩
    intro y
    obtain ⟨x, hx⟩ := hrange y
    exact ⟨⟨x, show Θ x ∈ stableSub F w S hS by rw [hx]; exact y.2⟩, Subtype.ext hx⟩
  let e := Fintype.equivFin I
  exact ⟨Fintype.card I, fun t => (ent (e.symm t)).1,
    hsq.of_ambient_equiv (LinearEquiv.piCongrLeft' ℂ[rowIsometrySubgroup₀ w.Completion] X e)⟩

end STDProof

namespace STDProof

open scoped MonoidAlgebra
open SubqPrep

variable (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)

set_option backward.isDefEq.respectTransparency false in
private theorem finite_entryQuot {d : ℕ} (ρ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (p : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ρ.asModule × Submodule ℂ[rowIsometrySubgroup₀ w.Completion] ρ.asModule) :
    Module.Finite ℂ (entryQuot p) := by
  haveI : Module.Finite ℂ ↥p.1 := Module.Finite.of_injective (p.1.subtype.restrictScalars ℂ) p.1.injective_subtype
  exact Module.Finite.quotient ℂ _

set_option backward.isDefEq.respectTransparency false in

private theorem le_typeSubmodule_of_equiv {d : ℕ} (σ : Representation ℂ (rowIsometrySubgroup₀ w.Completion) (Fin d → ℂ))
    (S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))
    (hS : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S)
    (e : σ.asModule ≃ₗ[ℂ[rowIsometrySubgroup₀ w.Completion]] ↥(stableSub F w S hS)) :
    S ≤ typeSubmodule (rowIsometryInclAt₀ F w) σ := by

  let T : (Fin d → ℂ) →ₗ[ℂ] (AdelicGL2 (𝓞 F) F → ℂ) :=
    (Rrep F w).asModuleEquiv.toLinearMap ∘ₗ ((stableSub F w S hS).subtype.restrictScalars ℂ) ∘ₗ
      (e.toLinearMap.restrictScalars ℂ) ∘ₗ σ.asModuleEquiv.symm.toLinearMap
  have hTapply : ∀ v : Fin d → ℂ,
      T v = (Rrep F w).asModuleEquiv ((e (σ.asModuleEquiv.symm v) : ↥(stableSub F w S hS)) : Fun F w) := fun v => rfl
  have hT : IsRightEquivariant (rowIsometryInclAt₀ F w) σ T := by
    intro k v x
    rw [hTapply, hTapply, Representation.asModuleEquiv_symm_map_rho, map_smul, Submodule.coe_smul, of_smul_eq]
    rfl
  intro g hg
  have hmem : (Rrep F w).asModuleEquiv.symm g ∈ stableSub F w S hS := (mem_stableSub_iff F w S hS _).mpr hg
  have hgT : g = T (σ.asModuleEquiv (e.symm ⟨(Rrep F w).asModuleEquiv.symm g, hmem⟩)) := by
    rw [hTapply, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]
    rfl
  rw [hgT]
  exact mem_typeSubmodule_of_isRightEquivariant hT _

end STDProof

set_option backward.isDefEq.respectTransparency false in
open STDProof SubqPrep in
open scoped MonoidAlgebra in
theorem solution
    (F : Type) [Field F] [NumberField F] (w : InfinitePlace F)
    (m : ℕ) (ρs : Fin m → ArchRepAt F w) :
    ∃ (r : ℕ) (σs : Fin r → ArchRepAt F w), (∀ j, (σs j).ρ.IsIrreducible) ∧
      ∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), FiniteDimensional ℂ ↥S →
        (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S, rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S) →
        S ≠ ⊥ →
        (∀ S' : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S' ≤ S →
          (∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ g ∈ S', rightTranslate F (rowIsometryInclAt₀ F w k) g ∈ S') →
          S' = ⊥ ∨ S' = S) →
        S ≤ ⨆ i, archTypeSubmoduleAt F w (ρs i) →
        ∃ j, S ≤ archTypeSubmoduleAt F w (σs j) := by
  classical

  choose lst hlst_simple hlst_cov using fun i : Fin m =>
    exists_list_forall_isSubquotient (isFiniteLength_asModule F w (ρs i).ρ)

  have hreal := fun (i : Fin m) (p : Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (ρs i).ρ.asModule ×
      Submodule ℂ[rowIsometrySubgroup₀ w.Completion] (ρs i).ρ.asModule) =>
    @exists_representation_fin_nonempty_equiv (rowIsometrySubgroup₀ w.Completion) _ (entryQuot p) _ _ _ _
      (finite_entryQuot F w (ρs i).ρ p)
  choose dq σq heq using hreal
  let data : List (ArchRepAt F w) :=
    (List.finRange m).flatMap fun i => (lst i).map fun p => (⟨dq i p, σq i p⟩ : ArchRepAt F w)
  refine ⟨data.length, fun j => data.get j, fun j => ?_, ?_⟩
  ·
    obtain ⟨i, -, hj⟩ := List.mem_flatMap.mp (List.get_mem data j)
    obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hj
    show (data.get j).ρ.IsIrreducible
    rw [← hpj]
    haveI := hlst_simple i p hp
    exact isIrreducible_of_equiv (σq i p) (entryQuot p) (heq i p).some
  · intro S hSfd hSst hSne hSsimple hSle
    haveI := hSfd
    haveI := isSimpleModule_stableSub F w S hSst hSne hSsimple
    obtain ⟨n, idx, hsq⟩ := isSubquotient_of_le_iSup F w m ρs S hSst hSle
    obtain ⟨t, ht⟩ := hsq.pi_elim
    obtain ⟨p, hp, ⟨e₂⟩⟩ := hlst_cov (idx t) ↥(stableSub F w S hSst) inferInstance ht

    have hmem : (⟨dq (idx t) p, σq (idx t) p⟩ : ArchRepAt F w) ∈ data :=
      List.mem_flatMap.mpr ⟨idx t, List.mem_finRange _, List.mem_map.mpr ⟨p, hp, rfl⟩⟩
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hmem
    refine ⟨j, ?_⟩
    show S ≤ archTypeSubmoduleAt F w (data.get j)
    rw [hj]
    exact le_typeSubmodule_of_equiv F w (σq (idx t) p) S hSst ((heq (idx t) p).some.trans e₂)

end
end S_AutomorphicForm_CuspidalConstituent_exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup
end P2MW
export P2MW.S_AutomorphicForm_CuspidalConstituent_exists_forall_le_archTypeSubmoduleAt_of_isSimple_of_le_iSup (solution)
