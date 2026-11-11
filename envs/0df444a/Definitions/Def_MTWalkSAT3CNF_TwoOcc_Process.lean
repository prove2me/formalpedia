-- Prove2me | Definitions.Def_MTWalkSAT3CNF_TwoOcc_Process
-- name    : MTWalkSAT3CNF_TwoOcc_Process
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T21:23:55.184077+00:00
-- url     : https://prove2.me/theorems/9bd0097d-4cd7-42ba-954b-4c93f0af3348
-- title:
--   Histories, adaptive selection rules, the uniform rule and hitting times
-- statement:
--   The two algorithms are random processes $X_0,X_1,\dots$ on a state space $S$. Each state records the current assignment together with the **record of the last update** (which clause, and for WalkSAT which position, was chosen in the step that produced it); the record is empty at time $0$ and once the algorithm has stopped. A **history through time $t$** is the sequence $X_0,\dots,X_t$, so it contains all past choices as well as all past assignments.
--
--   An **adaptive rule** with eligible sets $\mathrm{occ}(s)\subseteq I$ chooses at each time $t$ an element of $I\cup\{\text{none}\}$ as a (possibly randomized) function of the history through time $t$: a probability distribution depending measurably on the history. Whenever $\mathrm{occ}(X_t)\neq\emptyset$ it must choose some $i\in \mathrm{occ}(X_t)$ almost surely; it never sees future random choices. Deterministic rules are the case of point masses. The **uniform rule** chooses each element of $\mathrm{occ}(X_t)$ with probability $1/|\mathrm{occ}(X_t)|$.
--
--   The **hitting time** of a set $G$ of states along a trajectory $\omega$ is
--
--   $$T(\omega)=\inf\{t\ge 0:\ \omega_t\in G\}\in\mathbb N\cup\{\infty\}.$$
--
--   **Formalization Note** The record type is `Choice I`, a copy of `Option I` with the discrete σ-algebra. A rule is a family of Markov kernels from `Finset.Iic t → S` (the domain of the step kernels of `ProbabilityTheory.Kernel.traj`) to `Choice I`. The uniform rule is defined on countable state spaces, where every function of the history is measurable.
-- source:
--   Minbo Gao, Kun He, Tao Jiang, Tight Variable-Occurrence Bounds and Exponential Separations for Moser–Tardos and WalkSAT on 3-CNF, STOC 2027 submission #914 (October 2026), §2.1–§2.2, p. 9. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/914.pdf

import Mathlib

set_option autoImplicit false

/-!
# Histories, adaptive clause-selection rules and hitting times

Gao–He–Jiang, STOC 2027 submission #914 (October 2026), §2.1–§2.2 (p. 9).

Conventions.
* A process with state space `S` is a sequence `X_0, X_1, …` in `S`; its law is built with the
  Ionescu–Tulcea theorem (`ProbabilityTheory.Kernel.trajMeasure`) from step kernels that read the
  whole history `X_0, …, X_t`, given as a function `Finset.Iic t → S`.
* The states of the processes of this development carry, besides the assignment, the record of
  the last update (`Choice`): `none` at time `0` and after termination, `some c` after a step
  that chose `c`. Hence a history contains all past choices, not only past assignments.
* An adaptive rule chooses, at each time `t`, an element of `Choice I` as a (measurable, possibly
  randomized) function of the history through time `t`; whenever the set `occ X_t` of currently
  eligible indices is nonempty it chooses `some i` with `i ∈ occ X_t` almost surely. Its values on
  histories with `occ X_t = ∅` are never used. Deterministic rules are the Dirac case.
* The uniform rule chooses each index of `occ X_t` with probability `1 / |occ X_t|`.
* The hitting time of a predicate is `inf {t : good (ω t)} ∈ ℕ∞`, equal to `⊤` if never.
-/

namespace MTWalkSAT3CNF.TwoOcc

open MeasureTheory ProbabilityTheory

/-- The record of a choice: `none` (no choice) or `some i`. A type synonym of `Option I`
carrying the discrete σ-algebra. -/
def Choice (I : Type*) : Type _ := Option I

namespace Choice

variable {I : Type*}

/-- No choice was made. -/
def none : Choice I := Option.none

/-- The choice `i`. -/
def some (i : I) : Choice I := Option.some i

instance : Inhabited (Choice I) := ⟨none⟩

instance [DecidableEq I] : DecidableEq (Choice I) := inferInstanceAs (DecidableEq (Option I))

instance [Fintype I] : Fintype (Choice I) := inferInstanceAs (Fintype (Option I))

instance [Countable I] : Countable (Choice I) := inferInstanceAs (Countable (Option I))

instance : MeasurableSpace (Choice I) := ⊤

instance : DiscreteMeasurableSpace (Choice I) := ⟨fun _ => trivial⟩

instance : MeasurableSingletonClass (Choice I) := ⟨fun _ => trivial⟩

/-- Case analysis on a choice. -/
def elim {β : Sort*} (c : Choice I) (b : β) (f : I → β) : β := Option.elim c b f

@[simp] lemma elim_none {β : Sort*} (b : β) (f : I → β) : (none : Choice I).elim b f = b := rfl

@[simp] lemma elim_some {β : Sort*} (i : I) (b : β) (f : I → β) :
    (some i : Choice I).elim b f = f i := rfl

end Choice

/-- A history through time `t`: the states `X_0, …, X_t`. This is the domain of the `t`-th step
kernel of `ProbabilityTheory.Kernel.traj`. -/
abbrev Hist (S : Type*) (t : ℕ) : Type _ := (i : Finset.Iic t) → S

/-- The current state `X_t` of a history through time `t`. -/
def Hist.cur {S : Type*} {t : ℕ} (h : Hist S t) : S := h ⟨t, Finset.mem_Iic.2 le_rfl⟩

/-- An adaptive selection rule: at each time `t`, a Markov kernel from the history through
time `t` to a choice, which selects an eligible index almost surely whenever one exists. -/
structure AdaptiveRule (S : Type*) [MeasurableSpace S] (I : Type*) (occ : S → Set I) where
  /-- the (possibly randomized) choice at time `t`, as a function of the history -/
  pick : (t : ℕ) → Kernel (Hist S t) (Choice I)
  /-- each choice is a probability distribution -/
  markov : ∀ t, IsMarkovKernel (pick t)
  /-- when some index is eligible at the current state, an eligible index is chosen a.s. -/
  legal : ∀ (t : ℕ) (h : Hist S t), (occ h.cur).Nonempty →
    pick t h {c | ∃ i ∈ occ h.cur, c = Choice.some i}ᶜ = 0

attribute [instance] AdaptiveRule.markov

/-- The law of the uniform choice among the eligible indices `occ s`, or `none` if there are
none. -/
noncomputable def uniformChoice {I : Type*} [Fintype I] (o : Finset I) : Measure (Choice I) :=
  if hne : o.Nonempty then ((PMF.uniformOfFinset o hne).map Choice.some).toMeasure
  else Measure.dirac Choice.none

/-- The uniform rule: at each time it chooses each index of the eligible set `occ X_t` with
probability `1 / |occ X_t|` (and `none` if `occ X_t = ∅`). The eligible set is given both as a
set `occ` and as a finset `occF` with the same elements. It is defined on countable state spaces,
where every function of the history is measurable. -/
noncomputable def uniformRule {S : Type*} [MeasurableSpace S] [Countable S]
    [MeasurableSingletonClass S] {I : Type*} [Fintype I] (occ : S → Set I)
    (occF : S → Finset I) (hocc : ∀ s, (occF s : Set I) = occ s) :
    AdaptiveRule S I occ where
  pick t := ⟨fun h => uniformChoice (occF h.cur), measurable_of_countable _⟩
  markov t := ⟨fun h => by
    show IsProbabilityMeasure (uniformChoice (occF h.cur))
    unfold uniformChoice
    split_ifs <;> infer_instance⟩
  legal t h hne := by
    show uniformChoice (occF h.cur) _ = 0
    rw [← hocc] at hne ⊢
    have hne' : (occF h.cur).Nonempty := by simpa using hne
    rw [uniformChoice, dif_pos hne', PMF.toMeasure_apply_eq_zero_iff _ (MeasurableSet.of_discrete)]
    rw [Set.disjoint_left]
    intro c hc hc'
    rw [PMF.support_map, PMF.support_uniformOfFinset] at hc
    obtain ⟨i, hi, rfl⟩ := hc
    exact hc' ⟨i, by simpa using hi, rfl⟩

/-- The hitting time `inf {t ≥ 0 : good (ω t)}` in `ℕ∞` (equal to `⊤` if `good` never holds). -/
noncomputable def hitTime {S : Type*} (good : S → Prop) (ω : ℕ → S) : ℕ∞ :=
  ⨅ (t : ℕ) (_ : good (ω t)), (t : ℕ∞)

end MTWalkSAT3CNF.TwoOcc


