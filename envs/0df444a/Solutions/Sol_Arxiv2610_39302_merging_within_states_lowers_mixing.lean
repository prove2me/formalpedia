-- Prove2me | solution 1 for Arxiv2610_39302.merging_within_states_lowers_mixing
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-26T08:21:49.821809+00:00
-- url     : https://prove2.me/submissions/ae2fc6fc-3196-4888-9216-bacc16f12802

import Mathlib
import Definitions.Def_Arxiv2610_39302_Basic

open Matrix
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section
namespace MW
open Arxiv2610_39302

variable {X Y Z : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Z] [DecidableEq Z]

lemma fib (c : X → Y) (F : X → ℝ) (G : Y → ℝ) :
    ∑ y, (∑ x, if c x = y then F x else 0) * G y = ∑ x, F x * G (c x) := by
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp

lemma fib1 (c : X → Y) (F : X → ℝ) :
    ∑ y, (∑ x, if c x = y then F x else 0) = ∑ x, F x := by
  have := fib c F (fun _ => 1)
  simpa using this

lemma sumB (c : X → Y) (ω : X → ℝ) (G : Y → ℝ) :
    ∑ y, mergeWeights c ω y * G y = ∑ x, ω x * G (c x) := fib c ω G

lemma marg (c : X → Y) (ω : X → ℝ) (s : X → Z) (s' : Y → Z) (hs' : ∀ x, s' (c x) = s x) (z : Z) :
    stateMarg (mergeWeights c ω) s' z = stateMarg ω s z := by
  unfold stateMarg
  have : ∀ y, (if s' y = z then mergeWeights c ω y else 0) =
      mergeWeights c ω y * (if s' y = z then 1 else 0) := by intro y; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun y _ => this y), sumB]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [hs']; split_ifs <;> ring

lemma pull (c : X → Y) (ω : X → ℝ) (s : X → Z) (s' : Y → Z) (hs' : ∀ x, s' (c x) = s x)
    (h' : Y → ℝ) (x : X) :
    (condExpMat (mergeWeights c ω) s').mulVec h' (c x) = (condExpMat ω s).mulVec (h' ∘ c) x := by
  simp only [mulVec, dotProduct, condExpMat]
  rw [hs', marg c ω s s' hs']
  have : ∀ y', (if s' y' = s x then mergeWeights c ω y' / stateMarg ω s (s x) else 0) * h' y' =
      mergeWeights c ω y' * ((if s' y' = s x then 1 else 0) * h' y' / stateMarg ω s (s x)) := by
    intro y'; split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun y _ => this y), sumB]
  refine Finset.sum_congr rfl (fun x' _ => ?_)
  rw [hs']; simp only [Function.comp]; split_ifs <;> ring

def Ec (c : X → Y) (ω : X → ℝ) (u : X → ℝ) (y : Y) : ℝ :=
  (∑ x, if c x = y then ω x * u x else 0) / mergeWeights c ω y

lemma Ec_sub (c : X → Y) (ω : X → ℝ) (a b : X → ℝ) (y : Y) :
    Ec c ω (a - b) y = Ec c ω a y - Ec c ω b y := by
  unfold Ec; rw [← sub_div, ← Finset.sum_sub_distrib]
  congr 1; refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · simp only [Pi.sub_apply]; ring
  · simp

lemma wpos (c : X → Y) (hc : Function.Surjective c) (ω : X → ℝ) (hω : ∀ x, 0 < ω x) (y : Y) :
    0 < mergeWeights c ω y := by
  obtain ⟨x, rfl⟩ := hc y
  unfold mergeWeights
  calc (0:ℝ) < ω x := hω x
    _ = if c x = c x then ω x else 0 := by simp
    _ ≤ ∑ x', if c x' = c x then ω x' else 0 :=
      Finset.single_le_sum (f := fun x' => if c x' = c x then ω x' else 0)
        (fun i _ => by split_ifs; exact (hω i).le; exact le_refl 0) (Finset.mem_univ x)

lemma mlsum (c : X → Y) (W : X → X → ℝ) (G : Y → ℝ) (y : Y) :
    ∑ y', mergeLaw c W y y' * G y' = ∑ x, if c x = y then ∑ x', W x x' * G (c x') else 0 := by
  unfold mergeLaw
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases hx : c x = y
  · simp only [hx, true_and, if_true]
    have := fib c (fun x' => W x x') G
    simpa [Finset.sum_mul] using this
  · simp [hx]

lemma markov (c : X → Y) (hc : Function.Surjective c) (ω : X → ℝ) (hω : ∀ x, 0 < ω x)
    (W : X → X → ℝ) (g' : Y → ℝ) (y : Y) :
    (markovOp (mergeWeights c ω) (mergeLaw c W)).mulVec g' y =
      Ec c ω ((markovOp ω W).mulVec (g' ∘ c)) y := by
  simp only [mulVec, dotProduct, markovOp, Ec]
  have : ∀ y', mergeLaw c W y y' / mergeWeights c ω y * g' y' =
      (mergeLaw c W y y' * g' y') / mergeWeights c ω y := by intro; ring
  rw [Finset.sum_congr rfl (fun y' _ => this y'), ← Finset.sum_div, mlsum]
  congr 1
  refine Finset.sum_congr rfl (fun x _ => ?_)
  split_ifs
  · rw [Finset.mul_sum]; refine Finset.sum_congr rfl (fun x' _ => ?_)
    simp only [Function.comp]; field_simp [(hω x).ne']
  · rfl

lemma Pcomm (c : X → Y) (hc : Function.Surjective c) (ω : X → ℝ) (hω : ∀ x, 0 < ω x)
    (s : X → Z) (s' : Y → Z) (hs' : ∀ x, s' (c x) = s x) (v : X → ℝ) (y : Y) :
    (condExpMat (mergeWeights c ω) s').mulVec (Ec c ω v) y =
      Ec c ω ((condExpMat ω s).mulVec v) y := by
  set A := ∑ x, ω x * v x * ((if s x = s' y then 1 else 0) / stateMarg ω s (s' y)) with hA
  have L : (condExpMat (mergeWeights c ω) s').mulVec (Ec c ω v) y = A := by
    simp only [mulVec, dotProduct, condExpMat]
    rw [marg c ω s s' hs']
    have : ∀ y', (if s' y' = s' y then mergeWeights c ω y' / stateMarg ω s (s' y) else 0) *
        Ec c ω v y' = (∑ x, if c x = y' then ω x * v x else 0) *
          ((if s' y' = s' y then 1 else 0) / stateMarg ω s (s' y)) := by
      intro y'; unfold Ec; have := (wpos c hc ω hω y').ne'; split_ifs with hh
      · field_simp
      · simp
    rw [Finset.sum_congr rfl (fun y' _ => this y'), fib]
    refine Finset.sum_congr rfl (fun x _ => ?_); rw [hs']
  have R : Ec c ω ((condExpMat ω s).mulVec v) y = A := by
    unfold Ec
    have : ∀ x, (if c x = y then ω x * (condExpMat ω s).mulVec v x else 0) =
        (if c x = y then ω x * A else 0) := by
      intro x; split_ifs with h
      · congr 1; simp only [mulVec, dotProduct, condExpMat]; rw [hA, ← h, hs']
        refine Finset.sum_congr rfl (fun x' _ => ?_); split_ifs <;> ring
      · rfl
    rw [Finset.sum_congr rfl (fun x _ => this x)]
    have h2 : (∑ x, if c x = y then ω x * A else 0) = mergeWeights c ω y * A := by
      unfold mergeWeights; rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun x _ => ?_); split_ifs <;> ring
    rw [h2]; field_simp [(wpos c hc ω hω y).ne']
  rw [L, R]

lemma contr (c : X → Y) (hc : Function.Surjective c) (ω : X → ℝ) (hω : ∀ x, 0 < ω x)
    (u : X → ℝ) :
    l2Inner (mergeWeights c ω) (Ec c ω u) (Ec c ω u) ≤ l2Inner ω u u := by
  unfold l2Inner
  have key : ∀ y, mergeWeights c ω y * Ec c ω u y * Ec c ω u y ≤
      ∑ x, if c x = y then ω x * u x * u x else 0 := by
    intro y
    have hw := wpos c hc ω hω y
    set E := Ec c ω u y with hE
    have hN : (∑ x, if c x = y then ω x * u x else 0) = mergeWeights c ω y * E := by
      rw [hE]; unfold Ec; field_simp [hw.ne']
    have h0 : 0 ≤ ∑ x, if c x = y then ω x * (u x - E) ^ 2 else 0 :=
      Finset.sum_nonneg (fun x _ => by
        split_ifs
        · exact mul_nonneg (hω x).le (sq_nonneg _)
        · exact le_refl 0)
    have hexp : (∑ x, if c x = y then ω x * (u x - E) ^ 2 else 0) =
        (∑ x, if c x = y then ω x * u x * u x else 0) -
          2 * E * (∑ x, if c x = y then ω x * u x else 0) +
          E ^ 2 * (∑ x, if c x = y then ω x else 0) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun x _ => ?_); split_ifs <;> ring
    have hm : (∑ x, if c x = y then ω x else 0) = mergeWeights c ω y := rfl
    rw [hexp, hN, hm] at h0; nlinarith
  calc _ ≤ ∑ y, ∑ x, (if c x = y then ω x * u x * u x else 0) :=
        Finset.sum_le_sum (fun y _ => key y)
    _ = _ := fib1 c _

lemma qform (c : X → Y) (hc : Function.Surjective c) (ω : X → ℝ) (hω : ∀ x, 0 < ω x)
    (G : Y → ℝ) (u : X → ℝ) :
    l2Inner (mergeWeights c ω) G (Ec c ω u) = l2Inner ω (G ∘ c) u := by
  unfold l2Inner
  have : ∀ y, mergeWeights c ω y * G y * Ec c ω u y =
      (∑ x, if c x = y then ω x * u x else 0) * G y := by
    intro y; unfold Ec; field_simp [(wpos c hc ω hω y).ne']
  rw [Finset.sum_congr rfl (fun y _ => this y), fib]
  refine Finset.sum_congr rfl (fun x _ => ?_); simp only [Function.comp]; ring

lemma nrm (c : X → Y) (ω : X → ℝ) (h' : Y → ℝ) :
    l2Inner (mergeWeights c ω) h' h' = l2Inner ω (h' ∘ c) (h' ∘ c) := by
  unfold l2Inner
  have := sumB c ω (fun y => h' y * h' y)
  simp only [Function.comp, mul_assoc] at this ⊢
  exact this

lemma mix (c : X → Y) (hc : Function.Surjective c) (ω : X → ℝ) (hω : ∀ x, 0 < ω x)
    (s : X → Z) (s' : Y → Z) (hs' : ∀ x, s' (c x) = s x) (W : X → X → ℝ) (h' : Y → ℝ) :
    (mixOp (mergeWeights c ω) s' (mergeLaw c W)).mulVec h' =
      Ec c ω ((mixOp ω s W).mulVec (h' ∘ c)) := by
  unfold mixOp
  simp only [← mulVec_mulVec, sub_mulVec, one_mulVec]
  have h1 : (condExpMat ω s).mulVec (h' ∘ c) =
      ((condExpMat (mergeWeights c ω) s').mulVec h') ∘ c := by
    funext x; simp only [Function.comp]; exact (pull c ω s s' hs' h' x).symm
  rw [h1]
  set g' := (condExpMat (mergeWeights c ω) s').mulVec h'
  have h2 : (markovOp (mergeWeights c ω) (mergeLaw c W)).mulVec g' =
      Ec c ω ((markovOp ω W).mulVec (g' ∘ c)) := by
    funext y; exact markov c hc ω hω W g' y
  rw [h2]
  have h3 : (condExpMat (mergeWeights c ω) s').mulVec (Ec c ω ((markovOp ω W).mulVec (g' ∘ c))) =
      Ec c ω ((condExpMat ω s).mulVec ((markovOp ω W).mulVec (g' ∘ c))) := by
    funext y; exact Pcomm c hc ω hω s s' hs' _ y
  rw [h3]; funext y; rw [Pi.sub_apply]; exact (Ec_sub c ω _ _ y).symm

lemma bdd {X : Type*} [Fintype X] (ω : X → ℝ) (hω : ∀ x, 0 < ω x) (M : Matrix X X ℝ) :
    BddAbove ((fun h : X → ℝ => Real.sqrt (l2Inner ω (M.mulVec h) (M.mulVec h))) ''
      {h | l2Inner ω h h ≤ 1}) := by
  set K := ∑ x, (1 + 1 / ω x)
  set R : X → ℝ := fun x => ∑ x', |M x x'| * K
  refine ⟨Real.sqrt (∑ x, ω x * R x * R x), ?_⟩
  rintro _ ⟨h, hh, rfl⟩
  apply Real.sqrt_le_sqrt
  have hb : ∀ x, |h x| ≤ K := by
    intro x
    have hw := hω x
    have t : ω x * h x * h x ≤ 1 :=
      le_trans (Finset.single_le_sum (f := fun x => ω x * h x * h x)
        (fun i _ => by have := hω i; rw [mul_assoc]; exact mul_nonneg this.le (mul_self_nonneg _))
        (Finset.mem_univ x)) hh
    have hp : 0 < 1 / ω x := by positivity
    have t2 : |h x| ≤ 1 + 1 / ω x := by
      rcases le_or_gt (|h x|) 1 with h1 | h1
      · linarith
      · have e : h x * h x ≤ 1 / ω x := by rw [le_div_iff₀ hw]; nlinarith
        rw [← abs_mul_abs_self] at e
        nlinarith
    refine t2.trans ?_
    exact Finset.single_le_sum (f := fun x => 1 + 1 / ω x)
      (fun i _ => by have := hω i; positivity) (Finset.mem_univ x)
  have hm : ∀ x, |M.mulVec h x| ≤ R x := by
    intro x; simp only [mulVec, dotProduct, R]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x' _ => ?_)
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb x') (abs_nonneg _)
  unfold l2Inner
  refine Finset.sum_le_sum fun x _ => ?_
  have h1 := hm x
  have h0 : 0 ≤ |M.mulVec h x| := abs_nonneg _
  have : M.mulVec h x * M.mulVec h x ≤ R x * R x := by
    rw [← abs_mul_abs_self]; exact mul_le_mul h1 h1 h0 (h0.trans h1)
  rw [mul_assoc, mul_assoc]; exact mul_le_mul_of_nonneg_left this (hω x).le

end MW

open Arxiv2610_39302 MW in
theorem solution {Z X Y : Type*} [Fintype Z] [DecidableEq Z]
    [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ω : X → ℝ) (s : X → Z) (W : X → X → ℝ) (hW : IsPairLaw ω W)
    (hp : ∀ z, 0 < stateMarg ω s z)
    (c : X → Y) (hc : Function.Surjective c) (s' : Y → Z) (hs' : ∀ x, s' (c x) = s x) :
    inducedKernel s' (mergeLaw c W) = inducedKernel s W ∧
    nuisanceTop (mergeWeights c ω) s' (mergeLaw c W) ≤ nuisanceTop ω s W ∧
    mixNorm (mergeWeights c ω) s' (mergeLaw c W) ≤ mixNorm ω s W := by
  have hω : ∀ x, 0 < ω x := hW.1
  refine ⟨?_, ?_, ?_⟩
  · funext z z'
    unfold inducedKernel
    have e1 : ∀ y y', (if s' y = z ∧ s' y' = z' then mergeLaw c W y y' else 0) =
        (if s' y = z then 1 else 0) * (mergeLaw c W y y' * if s' y' = z' then 1 else 0) := by
      intro y y'; split_ifs <;> simp_all
    simp only [e1, ← Finset.mul_sum]
    simp only [mlsum]
    have e2 : ∀ y, (if s' y = z then (1:ℝ) else 0) *
        (∑ x, if c x = y then ∑ x', W x x' * (if s' (c x') = z' then 1 else 0) else 0) =
        (∑ x, if c x = y then ∑ x', W x x' * (if s' (c x') = z' then 1 else 0) else 0) *
          (if s' y = z then 1 else 0) := fun y => mul_comm _ _
    rw [Finset.sum_congr rfl (fun y _ => e2 y), fib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x' _ => ?_)
    rw [hs', hs']; split_ifs <;> simp_all
  · unfold nuisanceTop
    apply sSup_le_sSup
    rintro _ ⟨h', ⟨hP, hn⟩, rfl⟩
    refine ⟨h' ∘ c, ⟨?_, ?_⟩, ?_⟩
    · funext x; rw [← pull c ω s s' hs', hP]; rfl
    · rw [← nrm c ω h']; exact hn
    · have : (markovOp (mergeWeights c ω) (mergeLaw c W)).mulVec h' =
          Ec c ω ((markovOp ω W).mulVec (h' ∘ c)) := funext (markov c hc ω hω W h')
      simp only [this, qform c hc ω hω]
  · unfold mixNorm opNormL2
    apply csSup_le
    · exact ⟨_, ⟨0, by simp [l2Inner], rfl⟩⟩
    · rintro _ ⟨h', hn, rfl⟩
      have hmem : h' ∘ c ∈ {h : X → ℝ | l2Inner ω h h ≤ 1} := by
        show l2Inner ω (h' ∘ c) (h' ∘ c) ≤ 1
        rw [← nrm c ω h']; exact hn
      refine le_trans ?_ (le_csSup (bdd ω hω _) ⟨h' ∘ c, hmem, rfl⟩)
      apply Real.sqrt_le_sqrt
      rw [mix c hc ω hω s s' hs' W h']
      exact contr c hc ω hω _
