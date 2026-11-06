-- Prove2me | Definitions.Def_PlanningProphet_OnlinePolicy
-- name    : PlanningProphet_OnlinePolicy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:11:37.495378+00:00
-- url     : https://prove2.me/theorems/9ba98fe7-e6fd-488b-b1b2-8d49e34efe22
-- title:
--   §2 — online policies, the path they select, $\mathbb E(ALG)$ and $\mathbb E(OPT)$
-- statement:
--   This module defines the decision-maker of §2 (p.6): "The DM knows the distribution of the values but only observes the realized weight of an edge $e=(u,v)$ if and when the node $u$ is reached."
--
--   1. **Online policy.** A randomized policy has a seed space $\Xi$. Given a seed $\xi$, the value vector $w$ and the edges $h$ taken so far, it returns the next edge (or stops). It is **non-anticipating**: if two value vectors agree on every edge leaving a node visited by $h$ (the current node included), the decision is the same.
--   2. **The run.** Starting at $s$, the policy appends edges until it is at $t$; the run is cut off after $|V|$ steps. The selected path is the run, and $ALG$ is its value $\sum_{e\in ALG}w_e$.
--   3. **Feasibility and measurability.** A policy has **feasible runs** when, for every seed and every value vector, the selected path is a feasible $s,t$-path. Its run is **measurable** for values $W$ when each event $\{ALG \text{ selects } p\}$ is measurable.
--   4. **Expectations.** With the seed drawn from a probability measure $\nu$ independently of the values $W\sim\mu$,
--   $$\mathbb E(ALG)=\int ALG\;d(\nu\otimes\mu),\qquad \mathbb E(OPT)=\int OPT(W)\,d\mu .$$
--
--   $ALG$ is $c$-competitive when $\mathbb E(ALG)\ge c\cdot\mathbb E(OPT)$ (p.7); Theorems 3 and 4 assert the existence of such policies.
--
--   **Formalization Note** Both integrals are lower Lebesgue integrals in $[0,\infty]$. An $s,t$-path of an acyclic graph has fewer than $|V|$ edges, so the cut-off never binds for a policy that walks along edges. The theorems quantify the seed space existentially; the product measure $\nu\otimes\mu$ is what makes the seed independent of the values.
-- source:
--   Cristi, Oren, Planning Against a Prophet: A Graph-Theoretic Framework for Making Sequential Decisions, arXiv:2406.13911v1, §2 Model, p.6 (the DM and ALG), p.7 (c-competitive)

import Mathlib
import Definitions.Def_PlanningProphet_Model

open scoped NNReal ENNReal
open MeasureTheory

namespace PlanningProphet

/-! # Online policies, their runs, `E(ALG)` and `E(OPT)` (arXiv:2406.13911v1, §2, pp.6–7)

"The DM knows the distribution of the values but only observes the realized weight of an edge
`e = (u, v)` if and when the node `u` is reached. […] An algorithm or policy `ALG` determines at
each node which edge to follow next, given the observed realizations so far." (p.6)

**Formalization Note.**
1. A (randomized) policy reads a seed `ξ` from a seed space `Ξ`, the value vector `w` and the
   list `h` of edges taken so far, and returns the next edge (`none` means it stops). The field
   `nonanticipating` says that the decision depends on `w` only through the values `w e` of the
   edges `e` leaving a node already visited (the current node included): two value vectors that
   agree on those edges give the same decision.
2. The seed is drawn from a probability measure `ν` on `Ξ` independently of the values: the
   expectation of `ALG` is taken over the product measure `ν ⊗ μ`.
3. A run starts at `s` with no edge, stops when it is at `t` (or when the policy returns `none`),
   and otherwise appends the policy's edge. It is cut off after `|V|` steps; an `s,t`-path of an
   acyclic graph has fewer than `|V|` edges, so a policy that walks along edges reaches `t` in
   time. The theorems require the run to be a label-feasible `s,t`-path for every seed and every
   value vector, so a policy that stops early, leaves the current node by an edge that does not
   start there, or breaks a capacity, is excluded.
4. `ALG` is the value of the selected path ("We slightly abuse the notation and use `ALG` to
   refer to both the set of selected edges and the sum of their values", p.6). -/

variable {V E L : Type}

/-- A randomized online policy on the graph `G` with seed space `Ξ` (arXiv:2406.13911v1, §2,
p.6). `next ξ w h` is the edge chosen after the edges `h`, with seed `ξ` and values `w`. -/
structure OnlinePolicy (G : Graph V E L) (Ξ : Type*) where
  /-- The next edge (or `none` to stop), from the seed, the values and the edges taken so far. -/
  next : Ξ → (E → ℝ≥0) → List E → Option E
  /-- Non-anticipation: the decision reads the values only of edges leaving visited nodes. -/
  nonanticipating : ∀ (ξ : Ξ) (h : List E) (w w' : E → ℝ≥0),
    (∀ e, G.tail e ∈ G.vertices h → w e = w' e) → next ξ w h = next ξ w' h

namespace Graph

variable (G : Graph V E L)

/-- The run of a step rule `next` from `s`: after `n + 1` steps, the run after `n` steps if it is
at `t` or `next` returns `none`, and otherwise that run followed by the chosen edge. -/
def runWith [DecidableEq V] (next : List E → Option E) : ℕ → List E
  | 0 => []
  | n + 1 =>
    let h := runWith next n
    if G.current h = G.t then h
    else match next h with
      | some e => h ++ [e]
      | none => h

end Graph

namespace OnlinePolicy

variable {G : Graph V E L} {Ξ : Type*}

/-- The path selected by the policy `π` with seed `ξ` and values `w`: its run for `|V|` steps. -/
def algPath [Fintype V] [DecidableEq V] (π : OnlinePolicy G Ξ) (ξ : Ξ) (w : E → ℝ≥0) : List E :=
  G.runWith (π.next ξ w) (Fintype.card V)

/-- `ALG`: the value of the selected path. -/
def algValue [Fintype V] [DecidableEq V] (π : OnlinePolicy G Ξ) (ξ : Ξ) (w : E → ℝ≥0) : ℝ≥0∞ :=
  pathValue w (π.algPath ξ w)

/-- The policy always selects a label-feasible `s,t`-path: for every seed and every value
vector (p.6, "select a path from `s` to `t`"; p.7, the label constraint binds the DM). -/
def IsFeasibleRun [Fintype V] [DecidableEq V] [DecidableEq L] (π : OnlinePolicy G Ξ) : Prop :=
  ∀ ξ w, G.IsSTPath (π.algPath ξ w) ∧ G.LabelFeasible (π.algPath ξ w)

/-- The selected path is a random variable on `Ξ × Ω` when the values are `W : Ω → E → ℝ≥0`:
each event `{ALG selects p}` is measurable. -/
def RunMeasurable [Fintype V] [DecidableEq V] [MeasurableSpace Ξ] {Ω : Type*} [MeasurableSpace Ω]
    (π : OnlinePolicy G Ξ) (W : Ω → E → ℝ≥0) : Prop :=
  ∀ p : List E, MeasurableSet {q : Ξ × Ω | π.algPath q.1 (W q.2) = p}

/-- `E(ALG)`: the expected value of the selected path, the seed drawn from `ν` independently of
the values, which are `W` under `μ`. -/
noncomputable def expectedAlg [Fintype V] [DecidableEq V] [MeasurableSpace Ξ] {Ω : Type*}
    [MeasurableSpace Ω] (π : OnlinePolicy G Ξ) (ν : Measure Ξ) (μ : Measure Ω)
    (W : Ω → E → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ q, π.algValue q.1 (W q.2) ∂(ν.prod μ)

end OnlinePolicy

namespace Graph

/-- `E(OPT)` (p.7): the expected value of the prophet when the values are `W` under `μ`. -/
noncomputable def expectedOpt (G : Graph V E L) [DecidableEq L] {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (W : Ω → E → ℝ≥0) : ℝ≥0∞ :=
  ∫⁻ ω, G.opt (W ω) ∂μ

end Graph

end PlanningProphet


