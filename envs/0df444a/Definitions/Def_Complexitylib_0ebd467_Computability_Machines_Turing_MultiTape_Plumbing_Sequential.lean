-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:56.092072+00:00
-- url     : https://prove2.me/theorems/de02a7c7-769a-4b74-b2d0-ad4197b94178
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential — Space of a sequential run
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The additions of Christian Reitwiessner's branch `crei/tidy-universal` and of cslib PR #1111 to
--   `Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential`: sequential runs read through
--   `Turing.MultiTapeTM.runFrom`, with their space, and sequential composition of transformations given
--   by equations.
--
--   ### Main results
--
--   * `Turing.MultiTapeTM.runFrom_seq`: runs compose.
--   * `Turing.MultiTapeTM.forgetState_runFrom_seq`: invariants of a sequential run.
--   * `Turing.MultiTapeTM.space_seq_le`: the space of a sequential run is at most that of its phases.
--   * `Turing.MultiTapeTM.TransformsTapes.seq_eq`: sequential composition of transformations given by
--     equations.
--   * `Turing.MultiTapeTM.exists_runPath_seq_space_le`: the composed path visits at most the cells of
--     the two paths combined.
--
--   **Contents.** The module is published as a whole: 10 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Plumbing_Sequential`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/Plumbing/Sequential.lean

/-
Copyright (c) 2026 Christian Reitwiessner and Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- `exists_runPath_seq_space_le` is from cslib PR #1111 @3441fa81.
-- vendored: `space_seq_le` is stated with the space of run paths since cslib #1122

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_Plumbing_Sequential
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.Plumbing.Sequential` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Space of a sequential run

The additions of Christian Reitwiessner's branch `crei/tidy-universal` and of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Sequential`: sequential runs read through
`Turing.MultiTapeTM.runFrom`, with their space, and sequential composition of transformations given
by equations.

## Main results

* `Turing.MultiTapeTM.runFrom_seq`: runs compose.
* `Turing.MultiTapeTM.forgetState_runFrom_seq`: invariants of a sequential run.
* `Turing.MultiTapeTM.space_seq_le`: the space of a sequential run is at most that of its phases.
* `Turing.MultiTapeTM.TransformsTapes.seq_eq`: sequential composition of transformations given by
  equations.
* `Turing.MultiTapeTM.exists_runPath_seq_space_le`: the composed path visits at most the cells of
  the two paths combined.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State₀ State₁ : Type*} {input : List Symbol}

variable {tm₀ : MultiTapeTM k Symbol State₀} {tm₁ : MultiTapeTM k Symbol State₁}

open Sequential in
/-- **Space of a sequential run.** The run path of `seq` composed from two run paths visits at most
the cells of the two paths combined. -/
theorem exists_runPath_seq_space_le {p₀ : tm₀.RunPath input} (h₀ : p₀.last.Halted)
    {p₁ : tm₁.RunPath input} (h₁ : p₁.head = p₀.last.withState (some tm₁.q₀))
    (hp₁ : p₁.last.Halted) :
    ∃ p : (tm₀.seq tm₁).RunPath input, p.head = leftCfg tm₁ p₀.head ∧
      p.last = rightCfg p₁.last ∧ p.length ≤ p₀.length + p₁.length ∧
      p.space ≤ p₀.space + p₁.space := by
  obtain ⟨p, hh, hl, ht, hmem⟩ := exists_runPath_seq h₀ h₁ hp₁
  refine ⟨p, hh, hl, ht, ?_⟩
  -- every head position of the composed run is one of the first path or one of the second
  refine (p.space_le_sum_card
    (S := fun i => p₀.visitedByTapeHead i ∪ p₁.visitedByTapeHead i) fun c hc i => ?_).trans
    ((Finset.sum_le_sum fun i _ => Finset.card_union_le _ _).trans_eq Finset.sum_add_distrib)
  rcases hmem c hc with ⟨_, ⟨n, rfl⟩, he⟩ | ⟨_, ⟨n, rfl⟩, he⟩ <;>
    rw [show c.workTapePos i = _ from congrArg (·.workTapePos i) he]
  · exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))
  · exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ n))

namespace Sequential

/-- The second phase of `seq` mirrors the run of `tm₁`. -/
lemma runFrom_rightCfg (cfg : Cfg k Symbol State₁ input) (n : ℕ) :
    (tm₀.seq tm₁).runFrom (rightCfg cfg) n = rightCfg (tm₁.runFrom cfg n) :=
  (Function.Semiconj.iterate_right (fun c => (step_rightCfg c).symm) n cfg).symm

/-- While `tm₀` is running, `seq` mirrors it. -/
lemma runFrom_leftCfg (cfg : Cfg k Symbol State₀ input) (n : ℕ)
    (h : ∀ m < n, (tm₀.runFrom cfg m).state ≠ none) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) n = leftCfg tm₁ (tm₀.runFrom cfg n) := by
  simp only [runFrom] at h ⊢
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih fun m hm => h m (by omega),
      step_leftCfg _ (h n (by omega))]

@[simp]
lemma workTapePos_leftCfg (cfg : Cfg k Symbol State₀ input) :
    (leftCfg tm₁ cfg).workTapePos = cfg.workTapePos := rfl

@[simp]
lemma workTapePos_rightCfg (cfg : Cfg k Symbol State₁ input) :
    (rightCfg (State₀ := State₀) cfg).workTapePos = cfg.workTapePos := rfl

end Sequential

open Sequential in
/-- If `tm₀` halts at step `u`, then from step `u` on `seq` mirrors `tm₁`, started where `tm₀`
halted. -/
lemma HaltsAt.runFrom_seq {cfg : Cfg k Symbol State₀ input} {u : ℕ} (h : tm₀.HaltsAt cfg u)
    (n : ℕ) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + n) =
      rightCfg (tm₁.runFrom ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) n) := by
  have hhandoff : (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) u =
      rightCfg ((tm₀.runFrom cfg u).withState (some tm₁.q₀)) := by
    rw [runFrom_leftCfg cfg u fun _ hm => h.not_halted hm, leftCfg_of_halt h.halted]
  simp only [runFrom] at hhandoff ⊢
  rw [Nat.add_comm, Function.iterate_add_apply, hhandoff]
  exact runFrom_rightCfg _ n

open Sequential in
/-- **Sequential composition of runs.** If `tm₀` has halted in `mid` by step `t₀`, and `tm₁`,
started where `tm₀` halted, has halted in `fin` by step `t₁`, then the composed machine has halted
in `fin` by step `t₀ + t₁`. Each machine may halt earlier than its bound; in particular `tm₀` need
not be running at every step before `t₀`. -/
theorem runFrom_seq {cfg mid : Cfg k Symbol State₀ input} {fin : Cfg k Symbol State₁ input}
    {t₀ t₁ : ℕ} (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : tm₁.runFrom (mid.withState (some tm₁.q₀)) t₁ = fin) (hfin : fin.Halted) :
    (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (t₀ + t₁) = rightCfg fin := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  have hrun : (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + t₁) = rightCfg fin := by
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀, h₁]
  have hhalt : ((tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + t₁)).Halted := by
    simp only [hrun, Cfg.Halted] at hfin ⊢
    simp [rightCfg, hfin]
  rw [runFrom_eq_of_halt _ _ (by omega) hhalt, hrun]

open Sequential in
/-- **Invariants of a sequential run.** If `tm₀` has halted in `mid` by step `t₀`, then a property
of the state-free part of a configuration holds throughout the run of the composed machine if it
holds before step `t₀` of the run of `tm₀` and throughout the run of `tm₁` started where `tm₀`
halted. -/
theorem forgetState_runFrom_seq {P : Cfg k Symbol Unit input → Prop}
    {cfg mid : Cfg k Symbol State₀ input} {t₀ : ℕ} (h₀ : tm₀.runFrom cfg t₀ = mid)
    (hmid : mid.Halted) (hP₀ : ∀ m < t₀, P (tm₀.runFrom cfg m).forgetState)
    (hP₁ : ∀ n, P (tm₁.runFrom (mid.withState (some tm₁.q₀)) n).forgetState) (m : ℕ) :
    P ((tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) m).forgetState := by
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  rcases Nat.lt_or_ge m u with hm | hm
  · rw [runFrom_leftCfg cfg m fun _ hr => hhaltsAt.not_halted (by lia), forgetState_leftCfg]
    exact hP₀ m (by lia)
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀, forgetState_rightCfg]
    exact hP₁ n

open Sequential in
/-- If `tm₀` has halted in `mid` after `t₀` steps and `tm₁`, started from `mid`, has halted after
`t₁` steps, then in `t₀ + t₁` steps `tm₀.seq tm₁` uses at most the space of the two runs combined.
-/
theorem space_seq_le {cfg mid : Cfg k Symbol State₀ input} {t₀ t₁ : ℕ}
    (h₀ : tm₀.runFrom cfg t₀ = mid) (hmid : mid.Halted)
    (h₁ : (tm₁.runFrom (mid.withState (some tm₁.q₀)) t₁).Halted) :
    (MultiTapeNTM.RunPath.ofDeterministic (tm₀.seq tm₁) (leftCfg tm₁ cfg) (t₀ + t₁)).space ≤
      (MultiTapeNTM.RunPath.ofDeterministic tm₀ cfg t₀).space +
        (MultiTapeNTM.RunPath.ofDeterministic tm₁ (mid.withState (some tm₁.q₀)) t₁).space := by
  -- the first halting time of `tm₀`, which may be earlier than `t₀`
  obtain ⟨u, hu, hhaltsAt⟩ := exists_haltsAt (tm := tm₀) (cfg := cfg) (h₀ ▸ hmid)
  -- from step `u` on, `seq` mirrors `tm₁`, started on what `tm₀` left
  have hright (n : ℕ) : (tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + n) =
      rightCfg (tm₁.runFrom (mid.withState (some tm₁.q₀)) n) := by
    rw [hhaltsAt.runFrom_seq, ← hhaltsAt.runFrom_eq hu, h₀]
  have hhalt : ((tm₀.seq tm₁).runFrom (leftCfg tm₁ cfg) (u + t₁)).Halted := by
    simpa [hright, Cfg.Halted, rightCfg, Cfg.mapState] using h₁
  rw [space_eq_of_halt _ (by omega : u + t₁ ≤ t₀ + t₁) hhalt]
  refine le_trans (space_add_le _ _ _) (Nat.add_le_add ?_ ?_)
  · -- the first phase visits what the first machine visits
    refine le_trans (le_of_eq (space_eq_of_workTapePos _ _ u fun m hm => ?_))
      (space_mono tm₀ _ hu)
    rw [runFrom_leftCfg _ m fun _ hr => hhaltsAt.not_halted (by omega), workTapePos_leftCfg]
  · -- the second phase visits what the second machine visits
    rw [← add_zero u, hright 0]
    refine le_of_eq (space_eq_of_workTapePos _ _ t₁ fun m hm => ?_)
    rw [runFrom_rightCfg, workTapePos_rightCfg]
    rfl

/-- **Sequential composition of transformations given by equations.** If the first machine leaves
the words `ws₁` and emits `e₀`, and the second takes `ws₁` to `ws₂` emitting `e₁`, the composed
machine leaves `ws₂` and emits `e₀ ++ e₁`. -/
theorem TransformsTapes.seq_eq {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {ws₁ ws₂ : Fin k → List Symbol} {e₀ e₁ : List Symbol} {t₀ s₀ t₁ s₁ : ℕ}
    (h₀ : TransformsTapes tm₀ P (fun _ _ ws' e => ws' = ws₁ ∧ e = e₀) t₀ s₀)
    (h₁ : TransformsTapes tm₁ (fun _ ws => ws = ws₁) (fun _ _ ws' e => ws' = ws₂ ∧ e = e₁) t₁ s₁) :
    TransformsTapes (tm₀.seq tm₁) P (fun _ _ ws' e => ws' = ws₂ ∧ e = e₀ ++ e₁)
      (t₀ + t₁) (s₀ + s₁) :=
  (transformsTapes_seq h₀ h₁ fun _ _ _ _ _ h => h.1).imp (fun _ _ h => h)
    (by rintro _ _ _ _ _ ⟨_, _, _, ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl⟩; exact ⟨rfl, rfl⟩) le_rfl le_rfl

end Turing.MultiTapeTM


