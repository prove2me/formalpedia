-- Prove2me | Definitions.Def_AdaptSubCover_Rounds_Model
-- name    : AdaptSubCover_Rounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T07:17:20.656783+00:00
-- url     : https://prove2.me/theorems/88659d2b-3cb7-4c89-8e11-e8d65e7920bf
-- title:
--   §1.1–§2, pp. 3, 6–7 — stochastic submodular cover with independent items; adaptive and r-round-adaptive solutions, feasibility, expected cost
-- statement:
--   **Stochastic submodular cover with independent items.** Let $U$ be a finite ground set and let $f : 2^U \to \mathbb Z_{\ge 0}$ be monotone and submodular, with maximal value $Q := f(U)$. There are $m$ items $\mathcal X_1, \dots, \mathcal X_m$; item $\mathcal X_i$ has an integer cost $c_i \ge 1$ and realizes to a random element $X_i \in U$ with law $p_i$. The items are independent, so a joint realization $\omega = (X_1, \dots, X_m)$ has probability
--   $$\Pr[\omega] = \prod_{i=1}^m p_i(X_i).$$
--   All expectations $\mathbb E[F] = \sum_\omega \Pr[\omega]\, F(\omega)$ are finite sums, and $\Pr[A] = \mathbb E[\mathbf 1_A]$; the conditional expectation $\mathbb E[F \mid A]$ is $\mathbb E[F\,\mathbf 1_A]/\Pr[A]$ (taken as $0$ when $\Pr[A]=0$).
--
--   A **history** is the list of items probed so far with their realizations; its realization is the set $S = \{X_i : \mathcal X_i \text{ probed}\} \subseteq U$, and its cost is $c(\mathcal S) = \sum_{i : \mathcal X_i \in \mathcal S} c_i$. The probed items **cover** $f$ if $f(S) = Q$.
--
--   1. A **(fully) adaptive solution** is a decision tree: a rule that, given the history, names the next item to probe or stops. It is **feasible** if it covers $f$ with probability one; its expected cost is $\mathbb E[c(\mathcal S)]$ over the random decision path.
--   2. An **$r$-round-adaptive solution** (Definition 2.1) proceeds in rounds $k = 1, \dots, r$. At the start of round $k$ it chooses, as a function of the realizations seen in rounds $1, \dots, k-1$ only, an ordering of the items and a stopping rule; it then probes the items in this order (skipping items already probed) until the stopping rule, evaluated on the current history before each probe, fires — at that point the round ends. It is feasible if after its $r$ rounds it covers $f$ with probability one, and its expected cost is the expected total cost of the items probed in the $r$ rounds.
--
--   The paper's optimum $\mathtt{OPT}$ is an optimal feasible adaptive solution; statements comparing to $\mathtt{OPT}$ are made against every feasible adaptive solution.
--
--   **Formalization Note.** Items are `Fin m`, costs are natural numbers (the paper assumes integer costs, §3 p. 7; $c_i \ge 1$ is assumed so that $u^*_0 = 1$, p. 9), and $f$ is natural-number valued; submodularity is the published `NonmonotoneSubmod.Shared.Submodular` applied to $f$ cast to $\mathbb R$. The paper's ordering is of "all remaining items"; here any list is allowed, already-probed items being skipped — this is equivalent, since a missing item can be appended to the end of the list and the stopping rule extended to fire once every listed item is probed. An adaptive policy runs for at most $m$ steps (naming an already probed item ends the run), which suffices since each step probes a new item. Realizations always lie in $U$ (the subset-valued extension of p. 3 is not formalized).
-- source:
--   Ghuge, Gupta, Nagarajan, The Power of Adaptivity for Stochastic Submodular Cover, arXiv:2106.16115v1, pp. 3, 6–7, 9, §1.1, §2, Definition 2.1, §3

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_Submodular

namespace AdaptSubCover.Rounds

noncomputable section

/-- An instance of stochastic submodular cover with `m` independent items realizing in the
finite ground set `U` (§1.1, p. 3; §2, pp. 6–7; §3, p. 7): item `i` has law `p i` on `U` and
integer cost `c i`, and `f : 2^U → ℤ_{≥0}` is the function to be covered. -/
structure Instance (U : Type) (m : ℕ) where
  /-- `p i u` is the probability that item `i` realizes to `u`. -/
  p : Fin m → U → ℝ
  /-- integer cost `c_i` of probing item `i` -/
  c : Fin m → ℕ
  /-- the integer-valued set function `f` -/
  f : Finset U → ℕ

variable {U : Type} [Fintype U] [DecidableEq U] {m : ℕ}

/-- `Q := f(U)`, the maximal value of `f`. -/
def Instance.Q (I : Instance U m) : ℕ := I.f Finset.univ

/-- The standing assumptions of §1.1–§3: each `p i` is a probability vector on `U`, costs are
integers `≥ 1`, and `f` is monotone and submodular. -/
def Instance.Standing (I : Instance U m) : Prop :=
  (∀ i u, 0 ≤ I.p i u) ∧ (∀ i, ∑ u, I.p i u = 1) ∧ (∀ i, 1 ≤ I.c i) ∧
    Monotone I.f ∧ NonmonotoneSubmod.Shared.Submodular (fun S => (I.f S : ℝ))

/-- Independent items: the probability of the joint realization `ω` is the product of the
marginal probabilities. -/
def Instance.prob (I : Instance U m) (ω : Fin m → U) : ℝ := ∏ i, I.p i (ω i)

/-- Expectation of a function of the joint realization. -/
def Instance.E (I : Instance U m) (F : (Fin m → U) → ℝ) : ℝ := ∑ ω, I.prob ω * F ω

open Classical in
/-- Probability of an event of the joint realization. -/
def Instance.P (I : Instance U m) (A : (Fin m → U) → Prop) : ℝ :=
  I.E (fun ω => if A ω then 1 else 0)

open Classical in
/-- Conditional expectation `E[F | A] = E[F · 1_A] / P(A)` (`0` when `P(A) = 0`). -/
def Instance.condE (I : Instance U m) (A : (Fin m → U) → Prop) (F : (Fin m → U) → ℝ) : ℝ :=
  I.E (fun ω => if A ω then F ω else 0) / I.P A

/-- A history: the items probed so far, in order, with their realizations. -/
abbrev History (m : ℕ) (U : Type) := List (Fin m × U)

/-- The set of probed items of a history. -/
def History.items (h : History m U) : Finset (Fin m) := (h.map Prod.fst).toFinset

/-- The realized set `S = {X_i : 𝒳_i probed}` of a history. -/
def History.realized (h : History m U) : Finset U := (h.map Prod.snd).toFinset

/-- `c(𝒮)`: total cost of the probed items of a history. -/
def Instance.costOf (I : Instance U m) (h : History m U) : ℕ := ∑ i ∈ h.items, I.c i

/-- The probed items cover `f`: their realization `S` has `f(S) = Q`. -/
def Instance.Covers (I : Instance U m) (h : History m U) : Prop := I.f h.realized = I.Q

/-- A (fully) adaptive solution, i.e. a decision tree: given the history so far it names the
next item to probe, or `none` to stop. -/
abbrev AdaptivePolicy (m : ℕ) (U : Type) := History m U → Option (Fin m)

/-- One step of an adaptive policy under the joint realization `ω`: probe the named item
(an already probed item, or `none`, ends the run). -/
def AdaptivePolicy.step (π : AdaptivePolicy m U) (ω : Fin m → U) (h : History m U) :
    History m U :=
  match π h with
  | some i => if i ∈ h.items then h else h ++ [(i, ω i)]
  | none => h

/-- The decision path of an adaptive policy under `ω` (at most `m` probes). -/
def AdaptivePolicy.run (π : AdaptivePolicy m U) (ω : Fin m → U) : History m U :=
  (π.step ω)^[m] []

/-- An adaptive policy is feasible if it covers `f` with probability one. -/
def Instance.Feasible (I : Instance U m) (π : AdaptivePolicy m U) : Prop :=
  ∀ ω, 0 < I.prob ω → I.Covers (π.run ω)

/-- Expected cost of an adaptive policy. -/
def Instance.expCost (I : Instance U m) (π : AdaptivePolicy m U) : ℝ :=
  I.E (fun ω => (I.costOf (π.run ω) : ℝ))

/-- One round of an r-round-adaptive solution (Definition 2.1): an ordering of items, probed in
this order until a stopping rule fires. The stopping rule reads the whole history before each
probe; once it fires the round ends. -/
structure Round (m : ℕ) (U : Type) where
  /-- the ordering of the round (already probed items are skipped) -/
  order : List (Fin m)
  /-- the stopping rule, evaluated on the current history before each probe -/
  stop : History m U → Bool

/-- Execute an ordering with a stopping rule from history `h`. -/
def Round.go (stop : History m U → Bool) (ω : Fin m → U) :
    List (Fin m) → History m U → History m U
  | [], h => h
  | i :: L, h =>
      if stop h then h
      else Round.go stop ω L (if i ∈ h.items then h else h ++ [(i, ω i)])

/-- Execute a round from history `h`. -/
def Round.run (ρ : Round m U) (ω : Fin m → U) (h : History m U) : History m U :=
  Round.go ρ.stop ω ρ.order h

/-- A round-based solution: round `k` (`k = 0, 1, …`) is chosen as a function of the history
at the start of the round, i.e. of the realizations seen in the earlier rounds. -/
abbrev RoundPolicy (m : ℕ) (U : Type) := ℕ → History m U → Round m U

/-- The history after the first `k` rounds. -/
def RoundPolicy.run (σ : RoundPolicy m U) (ω : Fin m → U) : ℕ → History m U
  | 0 => []
  | k + 1 => (σ k (σ.run ω k)).run ω (σ.run ω k)

/-- An r-round solution is feasible if after its `r` rounds it covers `f` with probability one. -/
def Instance.FeasibleR (I : Instance U m) (r : ℕ) (σ : RoundPolicy m U) : Prop :=
  ∀ ω, 0 < I.prob ω → I.Covers (σ.run ω r)

/-- Expected cost of the first `r` rounds of a round-based solution. -/
def Instance.expCostR (I : Instance U m) (r : ℕ) (σ : RoundPolicy m U) : ℝ :=
  I.E (fun ω => (I.costOf (σ.run ω r) : ℝ))

end

end AdaptSubCover.Rounds


