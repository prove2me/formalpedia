-- Prove2me | Definitions.Def_DeligneDrinfeldKZ
-- name    : DeligneDrinfeldKZ
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-07T18:35:40.235805+00:00
-- url     : https://prove2.me/theorems/7e234bde-c235-4795-b02e-51b0d3ce820e
-- title:
--   OpenAI's Deligne–Drinfeld proof — internal definitions II (the truncated KZ comparison value)
-- statement:
--   The definitions needed to state the lemmas about the Knizhnik–Zamolodchikov comparison value in OpenAI's proof of the Deligne–Drinfeld conjecture (*The Deligne–Drinfeld conjecture*, OpenAI Math Release, September 23, 2026, §7, [github.com/openai/math](https://github.com/openai/math), [paper](https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf)). They are taken from OpenAI's Lean development `lean/OAI/Algebra/Drinfeld` (Apache License 2.0), with comments removed and line-level edits for this platform's Lean and Mathlib, keep OpenAI's names, and build on the bundle `DeligneDrinfeldInternals`.
--
--   The central object is `KZComparison.value N`, an element of the free associative real algebra on $x, y$ truncated above length $N$. From the two normalized solutions of the truncated transport equation of the KZ connection at $s = \tfrac12$ one forms their quotient $P$ and its sign-flipped version $V$ (each word of length $k$ multiplied by $(-1)^k$), the automorphism $\theta = \tau_V \circ \tau_P^{-1}$ and the element $A = V\,\theta(P)^{-1}$; the value is the truncated operator logarithm $\log(1 + T)$, $T(a) = A\,\theta(a) - a$, applied to $1$ (`OperatorLog`, `LogCategory`, `GaugeAutomorphism`, `ConjugateComparison`). The bundle also contains the substitutions and normal forms through which the value is read (`TruncatedSubstitution`, `CutoffPrimitiveExtract.normalVal`, `TensorProjection.piece`), the rotation $x \mapsto y$, $y \mapsto -x-y$ of the truncated algebra (`ComplexComparison.realRotate`), and the lemmas these definitions need.
-- source:
--   OpenAI, The Deligne–Drinfeld conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf, Section 7, pp. 31-38 (the truncated KZ comparison value); Lean: https://github.com/openai/math/tree/main/lean/OAI/Algebra/Drinfeld (Apache-2.0)

import Mathlib
import Definitions.Def_DeligneDrinfeldInternals

/-!
# OpenAI's proof of the Deligne–Drinfeld conjecture: internal definitions

OpenAI, *The Deligne–Drinfeld conjecture*, OpenAI Math Release, September 23, 2026,
https://github.com/openai/math (paper:
`preprints/The-Deligne-Drinfeld-conjecture-September-23-2026/paper.pdf`).

The definitions, structures and instances below, with the lemmas they need, are taken from
OpenAI's Lean development `lean/OAI/Algebra/Drinfeld` in that repository (Apache License,
Version 2.0), with comments removed and line-level edits for this Lean and Mathlib version.
They are the declarations needed to state the published intermediate lemmas of that proof.
-/

section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]

theorem map_space {M : Type*} [AddCommGroup M] [Module R M]
    {P : FreeMonoid α → Prop} (f : A R α →ₗ[R] M) (T : Submodule R M)
    (h : ∀ w,P w → f (word w)∈T) {p : A R α} (hp : p∈space P) : f p∈T := by
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; exact h w hw
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using T.add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using T.smul_mem c hp

end WordGrading

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

end

namespace TensorProjection
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]

abbrev piece {α : Type*} (n : ℕ) : A R α →ₗ[R] A R α := WordGrading.piece (fun _ => 1) n

end TensorProjection

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

end

namespace FilteredComparison
variable {R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

structure Filtration (R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ) where
  step : ℕ → Submodule R V
  decreasing : Antitone step
  initial : step 0=⊤
  terminal : step (N+1)=⊥

variable {N : ℕ} (F : Filtration R V N) (G : Filtration R W N)
  (f : V →ₗ[R] W)

def GrInjective : Prop := ∀ n v,v∈F.step n → f v∈G.step (n+1) → v∈F.step (n+1)

def GrSurjective : Prop := ∀ n w,w∈G.step n → ∃ v,v∈F.step n ∧ w-f v∈G.step (n+1)

theorem injective (h : GrInjective F G f) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  apply eq_bot_iff.mpr
  intro v hv
  have hz : f v=0 := hv
  have hm : ∀ n,v∈F.step n := by
    intro n
    induction n with
    | zero => rw [F.initial]; trivial
    | succ n ih => exact h n v ih (by rw [hz]; exact Submodule.zero_mem _)
  simpa only [F.terminal,Submodule.mem_bot] using hm (N+1)

theorem lift_step (h : GrSurjective F G f) (n k : ℕ) (w : W) (hw : w∈G.step n) :
    ∃ v,v∈F.step n ∧ w-f v∈G.step (n+k) := by
  induction k with
  | zero => exact ⟨0,Submodule.zero_mem _,by simpa only [map_zero,sub_zero,Nat.add_zero] using hw⟩
  | succ k ih =>
    obtain ⟨v,hv,he⟩ := ih
    obtain ⟨u,hu,hr⟩ := h (n+k) (w-f v) he
    refine ⟨v+u,(F.step n).add_mem hv (F.decreasing (Nat.le_add_right n k) hu),?_⟩
    convert hr using 1 <;> first | (congr 1 <;> omega) | (rw [map_add]; abel)

theorem surjective (h : GrSurjective F G f) : Function.Surjective f := by
  intro w
  obtain ⟨v,_,hv⟩ := lift_step F G f h 0 (N+1) w (by rw [G.initial]; trivial)
  simp only [zero_add,G.terminal,Submodule.mem_bot,sub_eq_zero] at hv
  exact ⟨v,hv.symm⟩

end FilteredComparison

namespace TruncatedSubstitution
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R α)) N
local notation "F" => filtration (∅ : Set (A R α)) N

def gen (a : α) : Q := quotient ∅ N (atom a)

theorem gen_mem (a : α) : gen N a∈F 1 :=
  ⟨atom a,word_mem (FreeMonoid.of a) (by simp [wt]),rfl⟩

theorem lift_word_mem (f : α → Q) (hf : ∀ a,f a∈F 1) (w : FreeMonoid α) :
    lift (R:=R) f (word w)∈F (degree wt w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using filtration_one (∅ : Set (A R α)) N
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact filtration_mul ∅ N 1 _ (hf a) ih

theorem lift_mem (f : α → Q) (hf : ∀ a,f a∈F 1) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : lift (R:=R) f p∈F n :=
  map_space (lift (R:=R) f).toLinearMap _ (fun w hw => filtration_antitone ∅ N hw (lift_word_mem N f hf w)) hp

def subst (f : α → Q) (hf : ∀ a,f a∈F 1) : Q →ₐ[R] Q :=
  RingQuot.liftAlgHom R ⟨lift (R:=R) f,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · simpa only [filtration_terminal,Submodule.mem_bot,map_zero] using lift_mem N f hf hp⟩

@[simp] theorem subst_quotient (f : α → Q) (hf : ∀ a,f a∈F 1) (p : A R α) :
    subst N f hf (quotient ∅ N p)=lift (R:=R) f p := by
  simp only [subst,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]

@[simp] theorem subst_gen (f : α → Q) (hf : ∀ a,f a∈F 1) (a : α) :
    subst N f hf (gen N a)=f a := by rw [gen,subst_quotient,lift_atom]

theorem subst_preserves (f : α → Q) (hf : ∀ a,f a∈F 1) (n : ℕ) (u : Q)
    (hu : u∈F n) : subst N f hf u∈F n := by
  obtain ⟨p,hp,rfl⟩ := hu
  change subst N f hf (quotient ∅ N p)∈_
  rw [subst_quotient]
  exact lift_mem N f hf hp

theorem lift_word_difference (f g : α → Q) (hf : ∀ a,f a∈F 1) (hg : ∀ a,g a∈F 1)
    (hd : ∀ a,f a-g a∈F 2) (w : FreeMonoid α) :
    lift (R:=R) f (word w)-lift (R:=R) g (word w)∈F (degree wt w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,map_mul,lift_atom,lift_atom,degree_mul,degree_of]
    have he : f a*lift (R:=R) f (word w)-g a*lift (R:=R) g (word w)=
        (f a-g a)*lift (R:=R) g (word w)+f a*(lift (R:=R) f (word w)-lift (R:=R) g (word w)) := by
      rw [sub_mul,mul_sub]
      abel
    rw [he]
    exact (F (1+degree wt w+1)).add_mem
      (by
        simpa only [show 1+degree wt w+1=2+degree wt w by omega] using filtration_mul ∅ N 2 _ (hd a) (lift_word_mem N g hg w))
      (by simpa only [Nat.add_assoc] using filtration_mul ∅ N 1 _ (hf a) ih)

theorem lift_difference (f g : α → Q) (hf : ∀ a,f a∈F 1) (hg : ∀ a,g a∈F 1)
    (hd : ∀ a,f a-g a∈F 2) {n : ℕ} {p : A R α} (hp : p∈above wt n) :
    lift (R:=R) f p-lift (R:=R) g p∈F (n+1) :=
  map_space ((lift (R:=R) f).toLinearMap-(lift (R:=R) g).toLinearMap) _ (fun w hw =>
    filtration_antitone ∅ N (Nat.add_le_add_right hw 1) (lift_word_difference N f g hf hg hd w)) hp

@[simp] theorem lift_gen : lift (R:=R) (gen (R:=R) (α:=α) N)=quotient ∅ N := by
  apply hom_ext
  intro a
  simp only [lift_atom,gen]

theorem subst_raises (f : α → Q) (hf : ∀ a,f a∈F 1) (hd : ∀ a,f a-gen N a∈F 2)
    (n : ℕ) (u : Q) (hu : u∈F n) : subst N f hf u-u∈F (n+1) := by
  obtain ⟨p,hp,rfl⟩ := hu
  change subst N f hf (quotient ∅ N p)-quotient ∅ N p∈_
  rw [subst_quotient]
  simpa only [lift_gen] using lift_difference N f (gen N) hf (gen_mem N) hd hp

theorem filtration_initial : F 0=⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩

def filtered : FilteredComparison.Filtration R Q N where
  step := F
  decreasing := filtration_antitone ∅ N
  initial := filtration_initial N
  terminal := filtration_terminal ∅ N

theorem subst_bijective (f : α → Q) (hf : ∀ a,f a∈F 1) (hd : ∀ a,f a-gen N a∈F 2) :
    Function.Bijective (subst N f hf) := by
  have hi : FilteredComparison.GrInjective (filtered N) (filtered N) (subst N f hf).toLinearMap := by
    intro n u hu he
    change subst N f hf u∈F (n+1) at he
    change u∈F (n+1)
    have hh := (F (n+1)).sub_mem he (subst_raises N f hf hd n u hu)
    simpa only [sub_sub_cancel] using hh
  have hs : FilteredComparison.GrSurjective (filtered N) (filtered N) (subst N f hf).toLinearMap := by
    intro n u hu
    refine ⟨u,hu,?_⟩
    change u-subst N f hf u∈F (n+1)
    simpa only [neg_sub] using (F (n+1)).neg_mem (subst_raises N f hf hd n u hu)
  exact ⟨FilteredComparison.injective _ _ _ hi,FilteredComparison.surjective _ _ _ hs⟩

def equiv (f : α → Q) (hf : ∀ a,f a∈F 1) (hd : ∀ a,f a-gen N a∈F 2) : Q ≃ₐ[R] Q :=
  AlgEquiv.ofBijective (subst N f hf) (subst_bijective N f hf hd)

end TruncatedSubstitution

namespace NilpotentFreeLift
open AssociativeElimination WordGrading TruncatedWords FinitePicard
variable {α B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
variable (F : NilpotentFiltration B) (f : α → B) (hf : ∀ a,f a∈F.space 1)
include hf
 theorem lift_word_mem (w : FreeMonoid α) : lift (R:=ℝ) f (word w)∈F.space (degree wt w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using F.one_mem
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact F.mul_mem 1 _ (hf a) ih
 theorem lift_mem {n : ℕ} {p : A ℝ α} (hp : p∈above wt n) : lift (R:=ℝ) f p∈F.space n :=
  map_space (lift (R:=ℝ) f).toLinearMap _ (fun w hw => F.antitone hw (lift_word_mem F f hf w)) hp
 def eval : Q (∅ : Set (A ℝ α)) F.cutoff →ₐ[ℝ] B :=
  RingQuot.liftAlgHom ℝ ⟨lift (R:=ℝ) f,by
    rintro p q ⟨rfl,hp⟩
    rcases hp with hp|hp
    · exact False.elim hp
    · simpa only [F.terminal,Submodule.mem_bot,map_zero] using lift_mem F f hf hp⟩
 @[simp] theorem eval_quotient (p : A ℝ α) : eval F f hf (quotient ∅ F.cutoff p)=lift (R:=ℝ) f p := by
  simp only [eval,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]
 @[simp] theorem eval_gen (a : α) : eval F f hf (TruncatedSubstitution.gen F.cutoff a)=f a := by
  rw [TruncatedSubstitution.gen,eval_quotient,lift_atom]
end NilpotentFreeLift

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
open scoped Topology Ring
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]

variable [FiniteDimensional ℝ A]

theorem associator_isUnit (F : NilpotentFiltration A) {X Y : A}
    (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) : IsUnit (associator F X Y) := by
  apply IsUnit.mul
  · exact (rightSolution_isUnit F hX hY (1/2)).ringInverse
  · exact normalizedSolution_isUnit F hX hY (1/2)

end KZCollar

end

namespace KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

 theorem gauge_sub_one_mem (F : NilpotentFiltration A) {X : A}
    (hX : X∈F.space 1) (s : ℝ) : gauge X s-1∈F.space 1 := by
  rw [gauge_finite X (pow_cutoff_eq_zero F hX),Finset.sum_range_succ']
  simp only [pow_zero,Nat.factorial_zero,Nat.cast_one,div_one,one_smul,add_sub_cancel_right]
  apply Submodule.sum_mem
  intro i hi
  exact (F.space 1).smul_mem _ (F.antitone (by omega : 1 ≤ i+1) (pow_mem F hX (i+1)))

 theorem product_sub_one_mem (F : NilpotentFiltration A) {u v : A}
    (hu : u-1∈F.space 1) (hv : v-1∈F.space 1) : u*v-1∈F.space 1 := by
  have hv0 : v∈F.space 0 := by
    simpa only [sub_add_cancel] using (F.space 0).add_mem (F.antitone (by omega : 0≤1) hv) F.one_mem
  have hh := (F.space 1).add_mem (F.mul_mem 1 0 hu hv0) hv
  simpa only [sub_mul,one_mul,sub_add_sub_cancel] using hh

 theorem inverse_sub_one_mem (F : NilpotentFiltration A) {u : A}
    (hF : F.space 0=⊤) (hu : u-1∈F.space 1) (hunit : IsUnit u) :
    Ring.inverse u-1∈F.space 1 := by
  have hi : Ring.inverse u∈F.space 0 := by rw [hF]; trivial
  have hh := F.mul_mem 0 1 hi hu
  have he : Ring.inverse u*(u-1)= -(Ring.inverse u-1) := by
    rw [mul_sub,Ring.inverse_mul_cancel _ hunit,mul_one,neg_sub]
  rw [he] at hh
  exact (F.space 1).neg_mem_iff.mp hh

variable [CompleteSpace A] [FiniteDimensional ℝ A]

omit [CompleteSpace A] in
theorem normalizedSolution_sub_one_mem (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) (s : ℝ) :
    normalizedSolution F X Y s-1∈F.space 1 :=
  product_sub_one_mem F (gauge_sub_one_mem F hX s)
    (transport_sub_one_mem F (regularForm_mem F hX hY) 0 s F.cutoff)

 theorem associator_sub_one_mem (F : NilpotentFiltration A) {X Y : A}
    (hF : F.space 0=⊤) (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator F X Y-1∈F.space 1 :=
  product_sub_one_mem F
    (inverse_sub_one_mem F hF (normalizedSolution_sub_one_mem F hY hX _)
      (rightSolution_isUnit F hX hY _))
    (normalizedSolution_sub_one_mem F hX hY _)

end KZCollar

section

end

namespace CutoffKZ
open CutoffDepth FinitePicard KZCollar MeasureTheory Set Filter
open scoped Topology

 theorem depth_initial (N : ℕ) : depthSpace (R:=ℝ) N 0=⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ
    (TruncatedWords.relations (∅ : Set (AssociativeElimination.A ℝ Bool)) N) u
  exact ⟨p,WordGrading.mem_space (by intros; exact Nat.zero_le _),rfl⟩

 theorem gaugeX_depth_zero (N : ℕ) (s : ℝ) : KZCollar.gauge (X N) s∈depthSpace N 0 := by
  rw [depth_initial]; trivial

 theorem left_regularized_depth (N : ℕ) (s : ℝ) :
    KZCollar.gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s-KZCollar.gauge (X N) s∈depthSpace N 1 := by
  have hg := gauge_sub_one_mem (depth N) ((depthSpace N 1).neg_mem (gen_depth N true)) (1-s)
  have ht : transport (regularForm (X N) (Y N)) 0 N s-1∈depthSpace N 1 :=
    transport_sub_one_mem (depth N) (regularForm_depth N) 0 s N
  have hnorm : normalizedSolution (weight N) (X N) (Y N) s∈depthSpace N 0 := by
    rw [depth_initial]; trivial
  have h := (depthSpace N 1).add_mem (depth_mul N 1 0 hg hnorm)
    (depth_mul N 0 1 (gaugeX_depth_zero N s) ht)
  have he : KZCollar.gauge (-Y N) (1-s)*normalizedSolution (weight N) (X N) (Y N) s-KZCollar.gauge (X N) s=
      (KZCollar.gauge (-Y N) (1-s)-1)*normalizedSolution (weight N) (X N) (Y N) s+
      KZCollar.gauge (X N) s*(transport (regularForm (X N) (Y N)) 0 N s-1) := by
    unfold normalizedSolution
    change KZCollar.gauge (-Y N) (1-s)*(KZCollar.gauge (X N) s*transport (regularForm (X N) (Y N)) 0 N s)-KZCollar.gauge (X N) s=_
    change _= (KZCollar.gauge (-Y N) (1-s)-1)*(KZCollar.gauge (X N) s*transport (regularForm (X N) (Y N)) 0 N s)+_
    noncomm_ring
  rwa [he]

 theorem associator_depth_one (N : ℕ) :
    associator (weight N) (X N) (Y N)-1∈depthSpace N 1 := by
  have hg : Tendsto (KZCollar.gauge (X N)) (𝓝[<] (1:ℝ)) (𝓝 (1:Q ℝ N)) := by
    have hh := (gauge_derivative (X N) (s:=1) one_ne_zero).continuousAt.tendsto.mono_left
      (show 𝓝[<] (1:ℝ)≤𝓝 (1:ℝ) from nhdsWithin_le_nhds)
    simpa only [KZCollar.gauge,Real.log_one,zero_smul,NormedSpace.exp_zero] using hh
  exact (depthSpace (R:=ℝ) N 1).closed_of_finiteDimensional.mem_of_tendsto
    ((left_regularized_limit N).sub hg) (Eventually.of_forall (left_regularized_depth N))

end CutoffKZ

namespace ConjugateComparison

section
open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem mem_zero (u : Q) : u∈F 0 := by rw [filtration_initial]; trivial

def family (P : Qˣ) : Bool → Q
  | false => gen N false
  | true => ((P⁻¹:Qˣ):Q)*gen N true*(P:Q)

theorem family_mem (P : Qˣ) (b : Bool) : family N P b∈F 1 := by
  cases b
  · exact gen_mem N false
  · exact filtration_mul ∅ N 1 0
      (filtration_mul ∅ N 0 1 (mem_zero N _) (gen_mem N true)) (mem_zero N _)

theorem family_leading (P : Qˣ) (hP : (P:Q)-1∈F 1) (b : Bool) :
    family N P b-gen N b∈F 2 := by
  cases b
  · simp only [family,sub_self,Submodule.zero_mem]
  · have hh := (F 2).sub_mem
      (filtration_mul ∅ N 1 1 (gen_mem N true) hP)
      (filtration_mul ∅ N 1 1 hP (gen_mem N true))
    have hi := filtration_mul ∅ N 0 2 (mem_zero N ((P⁻¹:Qˣ):Q)) hh
    have he : ((P⁻¹:Qˣ):Q)*(gen N true*((P:Q)-1)-((P:Q)-1)*gen N true)=
        family N P true-gen N true := by
      simp only [family,mul_sub,sub_mul,mul_one,one_mul]
      rw [←mul_assoc ((P⁻¹:Qˣ):Q) (P:Q),Units.inv_mul,one_mul]
      rw [mul_assoc]
      abel
    rwa [he] at hi

def transport (P : Qˣ) (hP : (P:Q)-1∈F 1) : Q ≃ₐ[R] Q :=
  equiv N (family N P) (family_mem N P) (family_leading N P hP)

@[simp] theorem transport_gen (P : Qˣ) (hP : (P:Q)-1∈F 1) (b : Bool) :
    transport N P hP (gen N b)=family N P b := subst_gen N _ _ b

def theta (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) : Q ≃ₐ[R] Q :=
  (transport N P hP).symm.trans (transport N V hV)

def unitArrow (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) : Qˣ :=
  V*(Units.map (theta N P V hP hV).toMonoidHom P)⁻¹

end

open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

end ConjugateComparison

namespace DepthSubstitution
open AssociativeElimination WordGrading TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => CutoffDepth.Q R N
local notation "F" => CutoffDepth.depthSpace (R:=R) N

 theorem initial : F 0=⊤ := by
  apply eq_top_iff.mpr
  intro u _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R Bool)) N) u
  exact ⟨p,mem_space (by intros; exact Nat.zero_le _),rfl⟩

 theorem all_zero (u : Q) : u∈F 0 := by rw [initial]; trivial

 theorem lift_word_mem (f : Bool → Q) (hf : ∀ a,f a∈F (GenericIhara.depth a)) (w : FreeMonoid Bool) :
    lift (R:=R) f (word w)∈F (degree GenericIhara.depth w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simpa only [word_one,map_one,degree_one] using CutoffDepth.depth_one (R:=R) N
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,lift_atom,degree_mul,degree_of]
    exact CutoffDepth.depth_mul N _ _ (hf a) ih

 theorem lift_word_difference (f g : Bool → Q)
    (hf : ∀ a,f a∈F (GenericIhara.depth a)) (hg : ∀ a,g a∈F (GenericIhara.depth a))
    (hd : ∀ a,f a-g a∈F (GenericIhara.depth a+1)) (w : FreeMonoid Bool) :
    lift (R:=R) f (word w)-lift (R:=R) g (word w)∈F (degree GenericIhara.depth w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,map_mul,lift_atom,lift_atom,degree_mul,degree_of]
    have he : f a*lift (R:=R) f (word w)-g a*lift (R:=R) g (word w)=
        (f a-g a)*lift (R:=R) g (word w)+f a*(lift (R:=R) f (word w)-lift (R:=R) g (word w)) := by
      rw [sub_mul,mul_sub]; abel
    rw [he]
    exact (F _).add_mem
      (by simpa only [Nat.add_right_comm] using CutoffDepth.depth_mul N _ _ (hd a) (lift_word_mem N g hg w))
      (by simpa only [Nat.add_assoc] using CutoffDepth.depth_mul N _ _ (hf a) ih)

 theorem subst_raises (f : Bool → Q)
    (hw : ∀ a,f a∈filtration ∅ N 1)
    (hf : ∀ a,f a∈F (GenericIhara.depth a))
    (hd : ∀ a,f a-gen N a∈F (GenericIhara.depth a+1))
    (n : ℕ) (u : Q) (hu : u∈F n) : subst N f hw u-u∈F (n+1) := by
  obtain ⟨p,hp,rfl⟩ := hu
  change subst N f hw (quotient ∅ N p)-quotient ∅ N p∈_
  rw [subst_quotient]
  have hh := map_space ((lift (R:=R) f).toLinearMap-(lift (R:=R) (gen N)).toLinearMap) _
    (fun w hw => CutoffDepth.depth_antitone N (Nat.add_le_add_right hw 1)
      (lift_word_difference N f (gen N) hf (CutoffDepth.gen_depth N) hd w)) hp
  simpa only [LinearMap.sub_apply,AlgHom.toLinearMap_apply,lift_gen] using hh

 theorem family_mem (P : Qˣ) (b : Bool) : ConjugateComparison.family N P b∈F (GenericIhara.depth b) := by
  cases b
  · exact CutoffDepth.gen_depth N false
  · exact CutoffDepth.depth_mul N 1 0
      (CutoffDepth.depth_mul N 0 1 (all_zero N _) (CutoffDepth.gen_depth N true)) (all_zero N _)

 theorem family_leading (P : Qˣ) (hP : (P:Q)-1∈F 1) (b : Bool) :
    ConjugateComparison.family N P b-gen N b∈F (GenericIhara.depth b+1) := by
  cases b
  · simp only [ConjugateComparison.family,sub_self,Submodule.zero_mem]
  · have hh := (F 2).sub_mem
      (CutoffDepth.depth_mul N 1 1 (CutoffDepth.gen_depth N true) hP)
      (CutoffDepth.depth_mul N 1 1 hP (CutoffDepth.gen_depth N true))
    have hi := CutoffDepth.depth_mul N 0 2 (all_zero N ((P⁻¹:Qˣ):Q)) hh
    have he : ((P⁻¹:Qˣ):Q)*(gen N true*((P:Q)-1)-((P:Q)-1)*gen N true)=
        ConjugateComparison.family N P true-gen N true := by
      simp only [ConjugateComparison.family,mul_sub,sub_mul,mul_one,one_mul]
      rw [←mul_assoc ((P⁻¹:Qˣ):Q) (P:Q),Units.inv_mul,one_mul]
      rw [mul_assoc]
      abel
    change ((P⁻¹:Qˣ):Q)*(gen N true*((P:Q)-1)-((P:Q)-1)*gen N true)∈F 2 at hi
    rwa [he] at hi

end DepthSubstitution

namespace CutoffScaling
open AssociativeElimination WordGrading TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] {α : Type*} (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R α)) N

 def map (r : R) : Q →ₐ[R] Q := subst N (fun a => r • gen N a)
  (fun a => (filtration ∅ N 1).smul_mem r (gen_mem N a))

 @[simp] theorem map_gen (r : R) (a : α) : map N r (gen N a)=r • gen N a := subst_gen N _ _ a

 theorem lift_word (r : R) (w : FreeMonoid α) :
    lift (R:=R) (fun a => r • gen (R:=R) N a) (word w)=r^(degree wt w) • quotient (∅ : Set (A R α)) N (word w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    rw [word_mul,map_mul,word_of,lift_atom,ih,degree_mul,degree_of]
    change (r • gen N a)*(r^degree wt w • quotient ∅ N (word w))=r^(1+degree wt w) • quotient ∅ N (atom a*word w)
    rw [pow_add,pow_one,map_mul,smul_mul_assoc,mul_smul_comm,smul_smul]
    rfl

 theorem preserves_depth (r : R) (n : ℕ) (u : TruncatedWords.Q (∅ : Set (A R Bool)) N)
    (hu : u∈CutoffDepth.depthSpace N n) : map N r u∈CutoffDepth.depthSpace N n := by
  obtain ⟨p,hp,rfl⟩ := hu
  change map N r (quotient ∅ N p)∈_
  rw [map,subst_quotient]
  apply map_space (lift (R:=R) (fun a => r • gen N a)).toLinearMap _ (fun w hw => ?_) hp
  change lift (R:=R) (fun a => r • gen N a) (word w)∈CutoffDepth.depthSpace N n
  rw [lift_word]
  exact (CutoffDepth.depthSpace N n).smul_mem _ ⟨word w,word_mem w hw,rfl⟩

end CutoffScaling

namespace ConjugateComparison
open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => CutoffDepth.Q R N
local notation "F" => CutoffDepth.depthSpace (R:=R) N

 theorem transport_depth_raises (P : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hPd : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    transport N P hP u-u∈F (n+1) :=
  DepthSubstitution.subst_raises N (family N P) (family_mem N P)
    (DepthSubstitution.family_mem N P) (DepthSubstitution.family_leading N P hPd) n u hu

 theorem transport_inverse_depth (P : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hPd : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    (transport N P hP).symm u∈F n := by
  have hh : ∀ k≤n,(transport N P hP).symm u∈F k := by
    intro k
    induction k with
    | zero => intro _; exact DepthSubstitution.all_zero N _
    | succ k ih =>
      intro hk
      have hd := transport_depth_raises N P hP hPd k _ (ih (by omega))
      rw [AlgEquiv.apply_symm_apply] at hd
      have he := (F (k+1)).sub_mem (CutoffDepth.depth_antitone N hk hu) hd
      simpa only [sub_sub_cancel] using he
  exact hh n le_rfl

 theorem theta_depth_raises (P V : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hV : (V:Q)-1∈filtration ∅ N 1) (hPd : (P:Q)-1∈F 1) (hVd : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u-u∈F (n+1) := by
  have hh := transport_inverse_depth N P hP hPd n u hu
  have hd := (F (n+1)).sub_mem (transport_depth_raises N V hV hVd n _ hh)
    (transport_depth_raises N P hP hPd n _ hh)
  simpa only [sub_sub_sub_cancel_right,AlgEquiv.apply_symm_apply,theta,AlgEquiv.trans_apply] using hd

 theorem theta_depth_preserves (P V : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hV : (V:Q)-1∈filtration ∅ N 1) (hPd : (P:Q)-1∈F 1) (hVd : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u∈F n := by
  have h := (F n).add_mem (CutoffDepth.depth_antitone N (Nat.le_succ n)
    (theta_depth_raises N P V hP hV hPd hVd n u hu)) hu
  simpa only [sub_add_cancel] using h

 theorem units_product_depth (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    ((P*V:Qˣ):Q)-1∈F 1 := by
  have h := (F 1).add_mem (CutoffDepth.depth_mul N 1 0 hP (DepthSubstitution.all_zero N (V:Q))) hV
  simpa only [sub_mul,one_mul,sub_add_sub_cancel,Units.val_mul] using h

 theorem units_inverse_depth (P : Qˣ) (hP : (P:Q)-1∈F 1) : ((P⁻¹:Qˣ):Q)-1∈F 1 := by
  have h := CutoffDepth.depth_mul N 0 1 (DepthSubstitution.all_zero N ((P⁻¹:Qˣ):Q)) hP
  have he : ((P⁻¹:Qˣ):Q)*((P:Q)-1)= -(((P⁻¹:Qˣ):Q)-1) := by
    rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
  rw [he] at h
  exact (F 1).neg_mem_iff.mp h

 theorem unitArrow_depth (P V : Qˣ) (hP : (P:Q)-1∈filtration ∅ N 1)
    (hV : (V:Q)-1∈filtration ∅ N 1) (hPd : (P:Q)-1∈F 1) (hVd : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)-1∈F 1 := by
  apply units_product_depth N V _ hVd
  apply units_inverse_depth N
  change theta N P V hP hV (P:Q)-1∈_
  simpa only [map_sub,map_one] using theta_depth_preserves N P V hP hV hPd hVd 1 ((P:Q)-1) hPd

end ConjugateComparison

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace OperatorLog

section
open Polynomial

def binom (k : ℕ) : ℚ[X] := (k.factorial : ℚ)⁻¹ • descPochhammer ℚ k

@[simp] theorem binom_zero : binom 0=1 := by simp [binom]
@[simp] theorem binom_eval_nat (k n : ℕ) : (binom k).eval (n : ℚ)=(n.choose k : ℚ) := by
  rw [Nat.cast_choose_eq_descPochhammer_div]
  simp [binom,div_eq_mul_inv,mul_comm]

@[simp] theorem binom_coeff_zero (k : ℕ) : (binom k).coeff 0=if k=0 then 1 else 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  simp only [binom,eval_smul,smul_eq_mul,descPochhammer_eval_zero]
  split_ifs with h
  · simp [h]
  · simp

theorem desc_coeff_one (k : ℕ) : (descPochhammer ℚ (k+1)).coeff 1=(-1:ℚ)^k*(k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [descPochhammer_succ_right,mul_sub,coeff_sub,coeff_mul_X]
    have h0 : (descPochhammer ℚ (k+1)).coeff 0=0 := by
      rw [coeff_zero_eq_eval_zero]
      simp
    simp only [h0,zero_sub]
    rw [←C_eq_natCast,coeff_mul_C,ih,Nat.factorial_succ,Nat.cast_mul,pow_succ]
    ring

theorem binom_coeff_one_succ (k : ℕ) : (binom (k+1)).coeff 1=(-1:ℚ)^k/(k+1) := by
  rw [binom,coeff_smul,smul_eq_mul,desc_coeff_one,Nat.factorial_succ,Nat.cast_mul]
  have hf : (k.factorial : ℚ)≠0 := by exact_mod_cast k.factorial_ne_zero
  have hk : ((k+1 : ℕ):ℚ)≠0 := by positivity
  push_cast
  field_simp

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

def interpolate (N : ℕ) (T : Module.End ℚ V) (s : ℚ) : Module.End ℚ V :=
  ∑ k∈Finset.range (N+1),(binom k).eval s • T^k

def logarithm (N : ℕ) (T : Module.End ℚ V) : Module.End ℚ V :=
  ∑ k∈Finset.range (N+1),(binom k).coeff 1 • T^k

theorem logarithm_eq (N : ℕ) (T : Module.End ℚ V) :
    logarithm N T=∑ k∈Finset.range N,((-1:ℚ)^k/(k+1)) • T^(k+1) := by
  unfold logarithm
  rw [Finset.sum_range_succ']
  simp only [binom_coeff_one_succ,binom_zero,coeff_one,one_ne_zero,ite_false,zero_smul,add_zero]

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

end

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem logarithm_fixed (N : ℕ) (T : Module.End ℚ V) {v : V} (h : T v=0) :
    logarithm N T v=0 := by
  rw [logarithm_eq]
  simp only [LinearMap.sum_apply,LinearMap.smul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  rw [pow_succ,Module.End.mul_apply,h,map_zero,smul_zero]

theorem nilpotent_of_raises (T : Module.End ℚ V) (F : ℕ → Submodule ℚ V) (N : ℕ)
    (hzero : F 0=⊤) (hterminal : F (N+1)=⊥)
    (hraise : ∀ n v,v∈F n → T v∈F (n+1)) : T^(N+1)=0 := by
  have hpow : ∀ n v,(T^n) v∈F n := by
    intro n v
    induction n with
    | zero => simpa only [pow_zero,Module.End.one_apply,hzero] using Submodule.mem_top
    | succ n ih => simpa only [pow_succ',Module.End.mul_apply] using hraise n _ ih
  apply LinearMap.ext
  intro v
  simpa only [hterminal,Submodule.mem_bot,LinearMap.zero_apply] using hpow (N+1) v

end OperatorLog

namespace LogCategory
open OperatorLog
variable {A O : Type*} [Ring A] [Algebra ℚ A]

structure Data (A O : Type*) [Ring A] [Algebra ℚ A] where
  S : O → O → Module.End ℚ A
  N : ℕ
  nilpotent : ∀ p q,(S p q-1)^(N+1)=0
  comp : ∀ p q r (a b : A),S p r (b*a)=S q r b*S p q a
  one : ∀ p,S p p 1=1

def delta (g : Data A O) (p q : O) : Module.End ℚ A := logarithm g.N (g.S p q-1)

@[simp] theorem delta_one_loop (g : Data A O) (p : O) : delta g p p 1=0 := by
  apply logarithm_fixed
  simp only [LinearMap.sub_apply,Module.End.one_apply,g.one,sub_self]

attribute [local instance] LieRing.ofAssociativeRing

end LogCategory

namespace GaugeAutomorphism
variable {A O : Type*} [Ring A] [Algebra ℚ A]

 def map (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p q : O) : Module.End ℚ A :=
  ((LinearMap.mulLeft ℚ (H q:A)).comp (LinearMap.mulRight ℚ ((H p)⁻¹:Aˣ))).comp θ.toLinearMap

 @[simp] theorem map_apply (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p q : O) (a : A) :
    map θ H p q a=(H q:A)*θ a*((H p)⁻¹:Aˣ) := by
  simp only [map,LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]
  rfl

 theorem composition (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p q r : O) (a b : A) :
    map θ H p r (b*a)=map θ H q r b*map θ H p q a := by
  simp only [map_apply,map_mul,mul_assoc]
  rw [←mul_assoc (((H q)⁻¹:Aˣ):A) (H q:A),Units.inv_mul,one_mul]

 @[simp] theorem map_one_loop (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (p : O) :
    map θ H p p 1=1 := by simp only [map_apply,map_one,mul_one,Units.mul_inv]

 theorem raises (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (F : ℕ → Submodule ℚ A)
    (hF : Antitone F) (h0 : F 0=⊤)
    (hmul : ∀ i j {u v : A},u∈F i → v∈F j → u*v∈F (i+j))
    (hθ : ∀ n u,u∈F n → θ u-u∈F (n+1)) (hH : ∀ p,(H p:A)-1∈F 1)
    (p q : O) (n : ℕ) (u : A) (hu : u∈F n) : map θ H p q u-u∈F (n+1) := by
  have hθu : θ u∈F n := by
    simpa only [sub_add_cancel] using (F n).add_mem (hF (Nat.le_succ n) (hθ n u hu)) hu
  have hall : ∀ v : A,v∈F 0 := by intro v; rw [h0]; trivial
  have hinv : (((H p)⁻¹:Aˣ):A)-1∈F 1 := by
    have hh := hmul 0 1 (hall (((H p)⁻¹:Aˣ):A)) (hH p)
    have he : (((H p)⁻¹:Aˣ):A)*((H p:A)-1)= -((((H p)⁻¹:Aˣ):A)-1) := by
      rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
    rw [he] at hh
    exact (F 1).neg_mem_iff.mp hh
  have hh₁ := hmul (n+1) 0
    (show ((H q:A)-1)*θ u∈F (n+1) from by simpa only [Nat.add_comm 1 n] using hmul 1 n (hH q) hθu)
    (hall (((H p)⁻¹:Aˣ):A))
  have hh₂ := hmul n 1 hθu hinv
  have he : map θ H p q u-u=
      ((H q:A)-1)*θ u*((H p)⁻¹:Aˣ)+θ u*((((H p)⁻¹:Aˣ):A)-1)+(θ u-u) := by
    rw [map_apply]
    noncomm_ring
  rw [he]
  exact (F (n+1)).add_mem ((F (n+1)).add_mem hh₁ hh₂) (hθ n u hu)

 def data (θ : A ≃ₐ[ℚ] A) (H : O → Aˣ) (F : ℕ → Submodule ℚ A) (N : ℕ)
    (hF : Antitone F) (h0 : F 0=⊤) (ht : F (N+1)=⊥)
    (hmul : ∀ i j {u v : A},u∈F i → v∈F j → u*v∈F (i+j))
    (hθ : ∀ n u,u∈F n → θ u-u∈F (n+1)) (hH : ∀ p,(H p:A)-1∈F 1) :
    LogCategory.Data A O where
  S := map θ H
  N := N
  nilpotent p q := OperatorLog.nilpotent_of_raises _ F N h0 ht (raises θ H F hF h0 hmul hθ hH p q)
  comp := composition θ H
  one := map_one_loop θ H

end GaugeAutomorphism

namespace KZComparison
open CutoffDepth CutoffKZ FinitePicard KZCollar

 def positive (N : ℕ) : (Q ℝ N)ˣ :=
  (associator_isUnit (weight N) (gen_weight N false) (gen_weight N true)).unit

 @[simp] theorem positive_val (N : ℕ) : (positive N:Q ℝ N)=associator (weight N) (X N) (Y N) :=
  (associator_isUnit (weight N) (gen_weight N false) (gen_weight N true)).unit_spec

 def negative (N : ℕ) : (Q ℝ N)ˣ := Units.map (CutoffScaling.map N (-1:ℝ)).toMonoidHom (positive N)

 theorem positive_weight (N : ℕ) : (positive N:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  rw [positive_val]
  exact associator_sub_one_mem (weight N) (TruncatedSubstitution.filtration_initial N)
    (gen_weight N false) (gen_weight N true)

 theorem negative_weight (N : ℕ) : (negative N:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  have hh := TruncatedSubstitution.subst_preserves N (fun b => (-1:ℝ) • TruncatedSubstitution.gen N b)
    (fun b => (TruncatedWords.filtration ∅ N 1).smul_mem _ (TruncatedSubstitution.gen_mem N b))
    1 ((positive N:Q ℝ N)-1) (positive_weight N)
  change CutoffScaling.map N (-1:ℝ) ((positive N:Q ℝ N)-1)∈_ at hh
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)-1∈_
  simpa only [map_sub,map_one] using hh

 theorem positive_depth (N : ℕ) : (positive N:Q ℝ N)-1∈depthSpace N 1 := by
  rw [positive_val]; exact associator_depth_one N

 theorem negative_depth (N : ℕ) : (negative N:Q ℝ N)-1∈depthSpace N 1 := by
  have hh := CutoffScaling.preserves_depth N (-1:ℝ) 1 ((positive N:Q ℝ N)-1) (positive_depth N)
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)-1∈_
  simpa only [map_sub,map_one] using hh

 def theta (N : ℕ) : Q ℝ N ≃ₐ[ℝ] Q ℝ N :=
  ConjugateComparison.theta N (positive N) (negative N) (positive_weight N) (negative_weight N)

 def arrow (N : ℕ) : (Q ℝ N)ˣ :=
  ConjugateComparison.unitArrow N (positive N) (negative N) (positive_weight N) (negative_weight N)

 theorem theta_depth (N n : ℕ) (u : Q ℝ N) (hu : u∈depthSpace N n) :
    theta N u-u∈depthSpace N (n+1) :=
  ConjugateComparison.theta_depth_raises N _ _ _ _ (positive_depth N) (negative_depth N) n u hu

 theorem arrow_depth (N : ℕ) : (arrow N:Q ℝ N)-1∈depthSpace N 1 :=
  ConjugateComparison.unitArrow_depth N _ _ _ _ (positive_depth N) (negative_depth N)

 def frames (N : ℕ) : Bool → (Q ℝ N)ˣ | false => 1 | true => arrow N

 theorem frames_depth (N : ℕ) (b : Bool) : (frames N b:Q ℝ N)-1∈depthSpace N 1 := by
  cases b
  · simp only [frames,Units.val_one,sub_self,Submodule.zero_mem]
  · exact arrow_depth N

 def rationalDepth (N n : ℕ) : Submodule ℚ (Q ℝ N) := (depthSpace N n).restrictScalars ℚ

 theorem rationalDepth_initial (N : ℕ) : rationalDepth N 0=⊤ := by
  apply Submodule.ext
  intro u
  change u∈depthSpace N 0 ↔ True
  simp only [CutoffKZ.depth_initial,Submodule.mem_top]

 theorem rationalDepth_terminal (N : ℕ) : rationalDepth N (N+2)=⊥ := by
  apply eq_bot_iff.mpr
  intro u hu
  have hh := depth_antitone N (show N+1≤N+2 by omega) hu
  simpa only [depth_terminal,Submodule.mem_bot] using hh

 def category (N : ℕ) : LogCategory.Data (Q ℝ N) Bool :=
  GaugeAutomorphism.data ((theta N).restrictScalars ℚ) (frames N) (rationalDepth N) (N+1)
    (depth_antitone N) (rationalDepth_initial N) (rationalDepth_terminal N)
    (depth_mul N) (theta_depth N) (frames_depth N)

 def value (N : ℕ) : Q ℝ N := LogCategory.delta (category N) false true 1

end KZComparison

namespace CutoffPrimitiveExtract
open AssociativeElimination WordGrading TensorProjection
open scoped TensorProduct
variable {R α : Type*} [CommRing R]

def truncVal (N : ℕ) : A R α →ₗ[R] A R α :=
  (TruncatedFree.B R α N).subtype.comp (TruncatedFree.trunc N)

open CutoffDepth CutoffKZ CutoffDiagonal

def normalVal (N : ℕ) : Q ℝ N →ₗ[ℝ] A ℝ Bool :=
  (TruncatedFree.B ℝ Bool N).subtype.comp (TruncatedFree.normal N)
@[simp] theorem normalVal_quotient (N : ℕ) (p : A ℝ Bool) :
    normalVal N (TruncatedWords.quotient ∅ N p)=truncVal N p := by
  change (TruncatedFree.normal N (TruncatedWords.quotient ∅ N p)).val=_
  rw [TruncatedFree.normal_quotient]
  rfl
@[simp] theorem normalVal_one (N : ℕ) : normalVal N 1=1 := by
  have h := normalVal_quotient N (1:A ℝ Bool)
  rw [map_one] at h
  rw [h]
  change project _ (word 1)=word 1
  rw [project_word,if_pos (by simp)]

end CutoffPrimitiveExtract

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace ComplexComparison

section
open CutoffDepth HexagonUnits

end

section
open CutoffDepth

end

open CutoffDepth ConjugateComparison WordGrading

open AssociativeElimination

def realRotateFamily (N : ℕ) (b : Bool) : Q ℝ N :=
  if b then -gen N false-gen N true else gen N true

theorem realRotateFamily_mem (N : ℕ) (b : Bool) :
    realRotateFamily N b∈(CutoffKZ.weight N).space 1 := by
  cases b
  · exact gen_weight (R:=ℝ) N true
  · exact ((CutoffKZ.weight N).space 1).sub_mem
      (((CutoffKZ.weight N).space 1).neg_mem (gen_weight (R:=ℝ) N false)) (gen_weight (R:=ℝ) N true)

def realRotate (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (CutoffKZ.weight N) (realRotateFamily N) (realRotateFamily_mem N)

@[simp] theorem realRotate_gen (N : ℕ) (b : Bool) : realRotate N (gen N b)=realRotateFamily N b :=
  NilpotentFreeLift.eval_gen _ _ _ b

end ComplexComparison

end DeligneDrinfeld

end

end OAI

end


