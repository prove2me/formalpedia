-- Prove2me | Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas
-- name    : Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:35:18.414316+00:00
-- url     : https://prove2.me/theorems/335fb0f8-bcd3-4444-8728-2fff4d46ec4d
-- title:
--   Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas — Space of run paths and of halted runs
-- statement:
--   This is module `Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas` of [complexitylib](https://github.com/cslib-community/complexitylib), the complexity-theory library of the CSLib community (machine models, polynomial time, and the `polytime` tactic; Apache-2.0), at commit `0ebd467`. It is published here because the formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)) states and proves its running-time bounds with it.
--
--   The additions of Christian Reitwiessner's branch `crei/tidy-universal` and of cslib PR #1111 to
--   `Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`.
--
--   The space of the run path of the first `t` steps from a configuration,
--   `MultiTapeNTM.RunPath.ofDeterministic tm cfg t`, is read through the cells each head visits: the
--   visited set is monotone, splits along a run, stops growing once the machine halts, and depends only
--   on the head positions.
--
--   `MultiTapeNTM.RunPath.space_le_mul_time_add_one` bounds the space of any run path by its length.
--
--   `MultiTapeTM.runsInSpace_of_runPath` turns the space of a single run path to a halted configuration
--   into a space bound for every computation path, since a deterministic machine stays where it is
--   after halting.
--
--   ### Main results
--
--   * `Turing.MultiTapeNTM.RunPath.space_le_mul_time_add_one`.
--   * `Turing.MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic`: the cells visited by the run
--     path of the first `t` steps are the head positions of the run up to step `t`.
--   * `Turing.MultiTapeTM.mem_of_last_halted`, `Turing.MultiTapeTM.runsInSpace_of_runPath`.
--   * `Turing.MultiTapeTM.space_add_le`, `Turing.MultiTapeTM.space_eq_of_halt`,
--     `Turing.MultiTapeTM.space_eq_of_workTapePos`: the space of a run, split, after halting, and of
--     runs with the same head positions.
--   * `Turing.MultiTapeTM.runsInSpace_of_halted`: a space bound on a halted run bounds every
--     computation path.
--   * `Turing.MultiTapeTM.exists_runPath_iff_runFrom`: a run path to a halted configuration is the run
--     of the given number of steps, with its space.
--   * `Turing.MultiTapeTM.exists_visitedByTapeHead_eq_Icc`,
--     `Turing.MultiTapeTM.workTapes_runFrom_eq_of_notMem_visitedByTapeHead`: the visited cells of a
--     work-tape head form an interval, and unvisited cells keep their contents.
--
--   **Contents.** The module is published as a whole: 22 declarations (definitions, structures, instances and their supporting lemmas, with proofs).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with only its imports renamed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_TapeLemmas`.
-- source:
--   https://github.com/cslib-community/complexitylib/blob/0ebd4671c2e7278a91f5671c11109bb254ae413c/Complexity/Computability/Machines/Turing/MultiTape/TapeLemmas.lean

/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- `space_le_mul_time_add_one`, `mem_of_last_halted` and `runsInSpace_of_runPath` are from cslib PR
-- #1111 @3441fa81.

public import Definitions.Def_Cslib_254e30e_Computability_Machines_Turing_MultiTape_TapeLemmas
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Deterministic
public import Definitions.Def_Complexitylib_0ebd467_Computability_Machines_Turing_MultiTape_Nondeterministic

/- Prove2me definition bundle for `Complexity.Computability.Machines.Turing.MultiTape.TapeLemmas` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Space of run paths and of halted runs

The additions of Christian Reitwiessner's branch `crei/tidy-universal` and of cslib PR #1111 to
`Cslib.Computability.Machines.Turing.MultiTape.TapeLemmas`.

The space of the run path of the first `t` steps from a configuration,
`MultiTapeNTM.RunPath.ofDeterministic tm cfg t`, is read through the cells each head visits: the
visited set is monotone, splits along a run, stops growing once the machine halts, and depends only
on the head positions.

`MultiTapeNTM.RunPath.space_le_mul_time_add_one` bounds the space of any run path by its length.

`MultiTapeTM.runsInSpace_of_runPath` turns the space of a single run path to a halted configuration
into a space bound for every computation path, since a deterministic machine stays where it is
after halting.

## Main results

* `Turing.MultiTapeNTM.RunPath.space_le_mul_time_add_one`.
* `Turing.MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic`: the cells visited by the run
  path of the first `t` steps are the head positions of the run up to step `t`.
* `Turing.MultiTapeTM.mem_of_last_halted`, `Turing.MultiTapeTM.runsInSpace_of_runPath`.
* `Turing.MultiTapeTM.space_add_le`, `Turing.MultiTapeTM.space_eq_of_halt`,
  `Turing.MultiTapeTM.space_eq_of_workTapePos`: the space of a run, split, after halting, and of
  runs with the same head positions.
* `Turing.MultiTapeTM.runsInSpace_of_halted`: a space bound on a halted run bounds every
  computation path.
* `Turing.MultiTapeTM.exists_runPath_iff_runFrom`: a run path to a halted configuration is the run
  of the given number of steps, with its space.
* `Turing.MultiTapeTM.exists_visitedByTapeHead_eq_Icc`,
  `Turing.MultiTapeTM.workTapes_runFrom_eq_of_notMem_visitedByTapeHead`: the visited cells of a
  work-tape head form an interval, and unvisited cells keep their contents.
-/

@[expose] public section

namespace Turing.MultiTapeNTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {ntm : MultiTapeNTM k Symbol State}

namespace RunPath

/-- Each head visits at most one cell per configuration, so a path visits at most `k * (time + 1)`
cells. -/
lemma space_le_mul_time_add_one (p : ntm.RunPath input) : p.space ≤ k * (p.time + 1) :=
  calc p.space ≤ ∑ _ : Fin k, (p.time + 1) :=
        Finset.sum_le_sum fun _ _ => Finset.card_image_le.trans_eq (Finset.card_fin _)
    _ = k * (p.time + 1) := by simp

-- vendored: added with the restatement over run paths after cslib #1122
/-- The run path of the first `t` steps from `cfg` visits exactly the head positions of the run up
to step `t`. -/
lemma mem_visitedByTapeHead_ofDeterministic {tm : MultiTapeTM k Symbol State}
    {cfg : Cfg k Symbol State input} {t : ℕ} {i : Fin k} {z : ℤ} :
    z ∈ (ofDeterministic tm cfg t).visitedByTapeHead i ↔
      ∃ m ≤ t, (tm.runFrom cfg m).workTapePos i = z := by
  simp only [visitedByTapeHead, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨fun ⟨n, h⟩ => ⟨n, Nat.lt_succ_iff.mp n.isLt, h⟩,
    fun ⟨m, hm, h⟩ => ⟨⟨m, Nat.lt_succ_of_le hm⟩, h⟩⟩

end RunPath

end Turing.MultiTapeNTM

namespace Turing.MultiTapeTM

variable {k : ℕ}
variable {State Symbol : Type*}
variable {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-! ### Space of halted runs -/

/-- Every configuration on a path from the head of a path that ends halted lies on that path: after
halting, a deterministic machine stays where it is. -/
lemma mem_of_last_halted {p q : tm.RunPath input} (hp : p.last.Halted) (hq : q.head = p.head) :
    ∀ c ∈ q, c ∈ p := by
  rintro _ ⟨n, rfl⟩
  have hlast : tm.runFrom p.head p.length = p.last := (runPath_apply_eq_runFrom p (.last _)).symm
  rw [runPath_apply_eq_runFrom, hq]
  rcases le_or_gt n.val p.length with h | h
  · exact ⟨⟨n, Nat.lt_succ_of_le h⟩, runPath_apply_eq_runFrom p _⟩
  · rw [runFrom_eq_of_halt tm _ h.le (hlast ▸ hp), hlast]
    exact ⟨.last _, rfl⟩

/-- A run path from the initial configuration to a halted configuration, using at most `s` cells,
bounds the space of every computation path by `s`. -/
lemma runsInSpace_of_runPath {s : ℕ} {p : tm.RunPath input} (hhead : p.head = tm.initCfg input)
    (hp : p.last.Halted) (hs : p.space ≤ s) : tm.RunsInSpace input s :=
  fun q => (MultiTapeNTM.RunPath.space_le_of_subset
    (mem_of_last_halted hp (q.head_eq.trans hhead.symm))).trans hs

/-! ### Space of runs -/

-- vendored: since cslib #1122 space is counted only on run paths; the statements below, stated in
-- crei:crei/tidy-universal with `MultiTapeTM.space cfg t`, `spaceUsedByTape` and
-- `visitedByTapeHead`, are stated with the run path of the first `t` steps, which is what
-- `MultiTapeTM.space cfg t` abbreviated.

/-- The total space used is monotone in the number of steps. -/
lemma space_mono (tm : MultiTapeTM k Symbol State) (cfg : Cfg k Symbol State input) :
    Monotone fun t => (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).space :=
  fun _ _ h => MultiTapeNTM.RunPath.space_le_of_subset fun _ ⟨n, hn⟩ =>
    ⟨⟨n, Nat.lt_succ_of_le ((Nat.lt_succ_iff.mp n.isLt).trans h)⟩, hn⟩

/-- Every position the head takes up to step `t` lies in `S`, so the whole visited set does. This
is `Finset.image_subset_iff` for the visited set, and the workhorse behind the space bounds
below. -/
lemma visitedByTapeHead_subset (cfg : Cfg k Symbol State input) {t : ℕ} {i : Fin k} {S : Finset ℤ}
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos i ∈ S) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).visitedByTapeHead i ⊆ S :=
  Finset.image_subset_iff.mpr fun m _ => h m (Nat.lt_succ_iff.mp m.isLt)

/-- A set containing every position of a head bounds the space used by its tape. -/
lemma spaceUsedByTape_le_card (cfg : Cfg k Symbol State input) {t : ℕ} {i : Fin k} {S : Finset ℤ}
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos i ∈ S) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).spaceUsedByTape i ≤ S.card :=
  Finset.card_le_card (tm.visitedByTapeHead_subset cfg h)

/-- A run that starts with the head of tape `i` at cell `0` and uses at most `s` cells keeps that
head within `[-s, s]`. -/
lemma visitedByTapeHead_subset_Icc (cfg : Cfg k Symbol State input) {t s : ℕ} {i : Fin k}
    (h0 : cfg.workTapePos i = 0) (hs : (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).space ≤ s) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).visitedByTapeHead i ⊆
      Finset.Icc (-(s : ℤ)) (s : ℤ) := fun z hz => by
  have hz : (z - cfg.workTapePos i).natAbs ≤ _ :=
    MultiTapeNTM.RunPath.natAbs_le_spaceUsedByTape_of_mem_visited _ hz
  have := (Finset.single_le_sum (fun j _ => Nat.zero_le
    ((MultiTapeNTM.RunPath.ofDeterministic tm cfg t).spaceUsedByTape j))
    (Finset.mem_univ i)).trans hs
  rw [h0, sub_zero] at hz
  grind

/-- A run whose heads all stay within `[-σ, σ]` uses at most `2 * σ + 1` cells per tape. -/
lemma space_le_of_visited_subset_Icc (cfg : Cfg k Symbol State input) (t : ℕ) {σ : ℕ}
    (h : ∀ i, (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).visitedByTapeHead i ⊆
      Finset.Icc (-(σ : ℤ)) (σ : ℤ)) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).space ≤ 2 * k * σ + k := by
  unfold MultiTapeNTM.RunPath.space
  refine (Finset.sum_le_card_nsmul _ _ (2 * σ + 1) fun i _ => ?_).trans_eq ?_
  · exact (Finset.card_le_card (h i)).trans_eq (by rw [Int.card_Icc]; lia)
  · simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
    lia

/-- A head that never moves uses a single cell. -/
lemma spaceUsedByTape_le_one (cfg : Cfg k Symbol State input) {t : ℕ} {i : Fin k}
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos i = cfg.workTapePos i) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).spaceUsedByTape i ≤ 1 := by
  simpa using tm.spaceUsedByTape_le_card cfg (S := {cfg.workTapePos i})
    fun m hm => by simp [h m hm]

/-- The cells a run visits are the ones visited by its two halves. -/
lemma visitedByTapeHead_add (cfg : Cfg k Symbol State input) (a b : ℕ) (i : Fin k) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg (a + b)).visitedByTapeHead i =
      (MultiTapeNTM.RunPath.ofDeterministic tm cfg a).visitedByTapeHead i ∪
        (MultiTapeNTM.RunPath.ofDeterministic tm (tm.runFrom cfg a) b).visitedByTapeHead i := by
  ext z
  simp only [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic, Finset.mem_union]
  constructor
  · rintro ⟨r, hr, rfl⟩
    rcases Nat.lt_or_ge r (a + 1) with h | h
    · exact Or.inl ⟨r, by omega, rfl⟩
    · exact Or.inr ⟨r - a, by omega,
        by simp only [runFrom, ← Function.iterate_add_apply,
          Nat.sub_add_cancel (by omega : a ≤ r)]⟩
  · rintro (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩)
    · exact ⟨r, by omega, rfl⟩
    · exact ⟨a + r, by omega,
        by simp only [runFrom, ← Function.iterate_add_apply, Nat.add_comm]⟩

/-- Splitting a run into two phases can only overcount the cells it visits, since the two phases
may revisit each other's cells. -/
lemma space_add_le (cfg : Cfg k Symbol State input) (a b : ℕ) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg (a + b)).space ≤
      (MultiTapeNTM.RunPath.ofDeterministic tm cfg a).space +
        (MultiTapeNTM.RunPath.ofDeterministic tm (tm.runFrom cfg a) b).space := by
  simp only [MultiTapeNTM.RunPath.space, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [MultiTapeNTM.RunPath.spaceUsedByTape, visitedByTapeHead_add]
  exact Finset.card_union_le _ _

/-- Space usage only depends on where the work-tape heads are at each step, so two runs whose head
positions agree use the same space. This is what lets a machine be replaced by a simulation of
it. -/
lemma space_eq_of_workTapePos {State' : Type*} {input' : List Symbol}
    {tm' : MultiTapeTM k Symbol State'} (cfg : Cfg k Symbol State input)
    (cfg' : Cfg k Symbol State' input') (t : ℕ)
    (h : ∀ m ≤ t, (tm.runFrom cfg m).workTapePos = (tm'.runFrom cfg' m).workTapePos) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).space =
      (MultiTapeNTM.RunPath.ofDeterministic tm' cfg' t).space := by
  simp only [MultiTapeNTM.RunPath.space, MultiTapeNTM.RunPath.spaceUsedByTape,
    MultiTapeNTM.RunPath.visitedByTapeHead]
  refine Finset.sum_congr rfl fun i _ => congrArg Finset.card (Finset.image_congr fun m _ => ?_)
  exact congrFun (h m (Nat.lt_succ_iff.mp m.isLt)) i

/-- After the machine has halted the heads no longer move, so the visited set stops growing. -/
lemma visitedByTapeHead_eq_of_halt (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) (i : Fin k) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).visitedByTapeHead i =
      (MultiTapeNTM.RunPath.ofDeterministic tm cfg τ).visitedByTapeHead i := by
  refine Finset.Subset.antisymm (visitedByTapeHead_subset cfg fun m hm => ?_)
    (visitedByTapeHead_subset cfg fun m hm =>
      MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨m, by omega, rfl⟩)
  rcases Nat.le_total m τ with h | h
  · exact MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨m, h, rfl⟩
  · rw [runFrom_eq_of_halt tm cfg h hhalt]
    exact MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic.mpr ⟨τ, le_rfl, rfl⟩

/-- After the machine has halted the heads no longer move, so the space usage stops growing. -/
lemma space_eq_of_halt (cfg : Cfg k Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.runFrom cfg τ).state = none) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).space =
      (MultiTapeNTM.RunPath.ofDeterministic tm cfg τ).space := by
  simp only [MultiTapeNTM.RunPath.space, MultiTapeNTM.RunPath.spaceUsedByTape]
  exact Finset.sum_congr rfl fun i _ =>
    congrArg Finset.card (tm.visitedByTapeHead_eq_of_halt cfg hle hhalt i)

/-- A run that never moves a work-tape head visits one cell per tape. -/
lemma space_le_of_workTapePos_const (cfg : Cfg k Symbol State input) (u : ℕ)
    (h : ∀ m ≤ u, (tm.runFrom cfg m).workTapePos = cfg.workTapePos) :
    (MultiTapeNTM.RunPath.ofDeterministic tm cfg u).space ≤ k := by
  have hcard : ∀ i ∈ Finset.univ,
      (MultiTapeNTM.RunPath.ofDeterministic tm cfg u).spaceUsedByTape i ≤ 1 :=
    fun i _ => tm.spaceUsedByTape_le_one cfg fun m hm => congrFun (h m hm) i
  simpa [MultiTapeNTM.RunPath.space] using Finset.sum_le_card_nsmul _ _ 1 hcard

/-! ### Space of computation paths -/

/-- The space of a computation path is the space of the run of the same length. -/
lemma computationPath_space_eq_space (p : tm.ComputationPath input) :
    p.space = (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) p.time).space := by
  -- vendored: a computation path is the path of its first `time` steps since cslib #1117
  rw [p.eq_ofDeterministic]
  rfl

/-- A machine that has halted by step `t`, using at most `s` cells, uses at most `s` cells on every
computation path. -/
lemma runsInSpace_of_halted {t s : ℕ} (hhalt : (tm.runFrom (tm.initCfg input) t).Halted)
    (hs : (MultiTapeNTM.RunPath.ofDeterministic tm (tm.initCfg input) t).space ≤ s) :
    tm.RunsInSpace input s := by
  intro p
  rw [computationPath_space_eq_space]
  rcases le_total p.time t with h | h
  · exact (space_mono tm _ h).trans hs
  · rwa [space_eq_of_halt _ h hhalt]

/-! ### Run paths to halted configurations as runs -/

-- vendored: a bridge, not in crei:crei/tidy-universal. Its specifications are stated with
-- `runFrom` and `spaceUsed`; since cslib #1117 they are stated with run paths.
/-- A run path from `cfg` to a halted configuration `cfg'` within `t` steps and `s` cells is the run
of `t` steps from `cfg`, which ends in `cfg'` and uses at most `s` cells. -/
theorem exists_runPath_iff_runFrom {cfg cfg' : Cfg k Symbol State input} (h : cfg'.Halted)
    {t s : ℕ} :
    (∃ p : tm.RunPath input, p.head = cfg ∧ p.last = cfg' ∧ p.time ≤ t ∧ p.space ≤ s) ↔
      tm.runFrom cfg t = cfg' ∧ (MultiTapeNTM.RunPath.ofDeterministic tm cfg t).space ≤ s := by
  refine ⟨fun ⟨p, hh, hl, ht, hs⟩ => ?_, fun ⟨hrun, hs⟩ =>
    ⟨.ofDeterministic tm cfg t, rfl, hrun, le_rfl, hs⟩⟩
  have hlast : p.last = tm.runFrom cfg p.time := by
    rw [← hh]
    exact runPath_apply_eq_runFrom p (Fin.last _)
  have hhalt : (tm.runFrom cfg p.time).state = none := by rw [← hlast, hl]; exact h
  refine ⟨(runFrom_eq_of_halt tm cfg ht hhalt).trans (hlast.symm.trans hl), ?_⟩
  exact (MultiTapeNTM.RunPath.space_le_of_subset
    (mem_of_last_halted (p := p) (q := .ofDeterministic tm cfg t) (hl ▸ h) hh.symm)).trans hs

-- upstream: candidate
/-- The values of a function on `0, …, n` that changes by at most one per step form an interval. -/
private theorem exists_image_range_eq_Icc {f : ℕ → ℤ} (hf : ∀ m, |f (m + 1) - f m| ≤ 1) (n : ℕ) :
    ∃ L R, (Finset.range (n + 1)).image f = Finset.Icc L R := by
  induction n with
  | zero => exact ⟨f 0, f 0, by simp⟩
  | succ n ih =>
    obtain ⟨L, R, h⟩ := ih
    have hn : f n ∈ Finset.Icc L R := h ▸ Finset.mem_image_of_mem f (by simp)
    rw [Finset.mem_Icc] at hn
    have := abs_le.1 (hf n)
    refine ⟨min L (f (n + 1)), max R (f (n + 1)), ?_⟩
    rw [Finset.range_add_one, Finset.image_insert, h]
    ext x
    simp only [Finset.mem_insert, Finset.mem_Icc]
    omega

-- upstream: candidate
/-- The cells visited by a head up to step `n` form an interval. -/
theorem exists_visitedByTapeHead_eq_Icc {tm : MultiTapeTM k Symbol State}
    (c : Cfg k Symbol State input) (n : ℕ) (i : Fin k) :
    ∃ L R, (MultiTapeNTM.RunPath.ofDeterministic tm c n).visitedByTapeHead i = Finset.Icc L R := by
  obtain ⟨L, R, h⟩ := exists_image_range_eq_Icc (f := fun m => (tm.runFrom c m).workTapePos i)
    (fun m => by rw [runFrom_succ]; exact MultiTapeNTM.Step.workTapePos_le (step_iff.mpr rfl) i) n
  refine ⟨L, R, ?_⟩
  rw [← h]
  ext x
  simp only [MultiTapeNTM.RunPath.mem_visitedByTapeHead_ofDeterministic, Finset.mem_image,
    Finset.mem_range, Nat.lt_succ_iff]

-- upstream: candidate
/-- A cell the head of a tape never visits keeps its contents. -/
theorem workTapes_runFrom_eq_of_notMem_visitedByTapeHead {tm : MultiTapeTM k Symbol State}
    {c : Cfg k Symbol State input} {n : ℕ} {i : Fin k} {x : ℤ}
    (hx : x ∉ (MultiTapeNTM.RunPath.ofDeterministic tm c n).visitedByTapeHead i) :
    (tm.runFrom c n).workTapes i x = c.workTapes i x := by
  by_contra h
  exact hx (MultiTapeNTM.RunPath.mem_visitedByTapeHead_of_workTapes_ne _ h)

end Turing.MultiTapeTM


