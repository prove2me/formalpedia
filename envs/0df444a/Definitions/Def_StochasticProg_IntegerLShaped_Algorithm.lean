-- Prove2me | Definitions.Def_StochasticProg_IntegerLShaped_Algorithm
-- name    : StochasticProg_IntegerLShaped_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:11:45.189904+00:00
-- url     : https://prove2.me/theorems/f2db8b9e-8e87-4285-8a36-c6d65bc08ffa
-- title:
--   Integer L-shaped method: cut state, master optimality, and the cut-adding transition
-- statement:
--   The **Integer L-shaped method** (Laporte & Louveaux 1993, restated p. 293) solves a
--   stochastic integer program with binary first-stage variables by repeatedly solving a
--   master problem over the first-stage feasible region augmented with optimality cuts of
--   the form (2.1), computing the true recourse value at the master's optimum, and either
--   stopping (the master value already matches the true value — "fathoming") or adding a
--   fresh cut that excludes the current binary solution and returning to the master.
--
--   A `State` records the set of subsets $S$ of the first-stage index set for which cut
--   (2.1) has already been imposed, one cut per binary point visited. A pair $(x,\theta)$ is
--   `IsBBOptimal` for a recorded cut set and lower bound $L$ when $x$ is binary,
--   SIP-feasible, satisfies every recorded cut, and $(x,\theta)$ minimizes $c^{\mathsf T}x +
--   \theta$ among all such pairs (with $\theta$ ignored, as the book directs, p. 293 Step 0,
--   when no cut has yet been recorded).
--
--   A `Step` from one cut set to the next holds when, at an `IsBBOptimal` pair $(x,\theta)$
--   with $x$ the indicator of a fresh subset $S$, the true recourse value $Q(x)$ (computed
--   at that point, Step 5) exceeds the master's $\theta$ (Step 6's "not yet fathomed" case),
--   so cut (2.1) for $S$ with $q_S = Q(x)$ is added.
--
--   **Formalization Note** The branch-and-bound bookkeeping around the master problem
--   (Steps 0, 1, 3, 4 of the book's procedure) is abstracted away: the finiteness argument
--   of Proposition 4 rests entirely on there being at most $2^{n_1}$ distinct first-stage
--   binary solutions, each excluded from ever recurring as the master's optimum by exactly
--   one application of Step 6 (fathomed, or given a fresh cut) — the same level of
--   abstraction the published `LShaped.Algorithm`/`LShaped.State` use for the continuous
--   L-shaped method's own master-problem bookkeeping. See `MODERATION_NOTES.md` for the
--   scope note in full.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 292-293, Chapter 7, §7.2, "Integer L-shaped Method"

import Mathlib
import Definitions.Def_StochasticProg_Recourse_Instance
import Definitions.Def_StochasticProg_IntegerLShaped_Instance

namespace StochasticProg.IntegerLShaped

open StochasticProg.Recourse

variable {n1 n2 m1 m2 K : ℕ}

/-- The algorithm's state: the set of subsets `S` for which an optimality cut (2.1)
has been imposed so far (Integer L-shaped Method, Step 6, p. 293: "impose one
optimality cut (2.1) with `qS = Q(xν)`, set `s = s + 1`"). Steps 0, 1, 3, 4 (the
branch-and-bound bookkeeping around the master, which only affects how fast the search
reaches a cut or a fathom, not whether finiteness holds) are abstracted away, as the
finiteness argument of Proposition 4's proof rests solely on "there are at most `2^n1`
different first-stage solutions" being excluded one at a time by Step 6; see
`MODERATION_NOTES.md` for the scope note. -/
abbrev State (n1 : ℕ) : Type := Finset (Finset (Fin n1))

/-- `(x, θ)` satisfies every optimality cut (2.1) recorded for `Cuts`, with the book's
`qS` value at each recorded `S`. -/
def CutsFeasible (_d : Data n1 n2 m1 m2 K) (Cuts : State n1) (L : ℝ) (qS : Finset (Fin n1) → ℝ)
    (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  ∀ S ∈ Cuts, θ ≥ cutRHS L (qS S) S x

/-- `(x, θ)` is a Step-2 optimal solution of the current master problem: a binary,
SIP-feasible `x` minimizing `cᵀx + θ` over all binary SIP-feasible pairs satisfying the
recorded cuts when there are any, `θ` "ignored" (p. 293, Step 0) otherwise — mirroring
`LShaped.IsMasterOptimal`'s treatment of an empty cut set. The relaxation from the
continuous master polytope of Steps 0-4 to optimizing directly over the binary feasible
set is the same abstraction as `State`'s doc-comment: cut (2.1) is proved valid (Prop.
3) for every binary feasible `x'`, so it applies unchanged whether or not a branching
tree is modeled explicitly. -/
def IsBBOptimal (d : Data n1 n2 m1 m2 K) (Cuts : State n1) (L : ℝ) (qS : Finset (Fin n1) → ℝ)
    (x : Fin n1 → ℝ) (θ : ℝ) : Prop :=
  x ∈ K1X d ∧ Binary x ∧
    (Cuts.Nonempty → CutsFeasible d Cuts L qS x θ) ∧
    (if Cuts.Nonempty then
        ∀ x' θ', x' ∈ K1X d → Binary x' → CutsFeasible d Cuts L qS x' θ' →
          dotProduct d.c x + θ ≤ dotProduct d.c x' + θ'
      else
        ∀ x', x' ∈ K1X d → Binary x' → dotProduct d.c x ≤ dotProduct d.c x')

/-- One admissible transition: from a Step-2 optimum `(x, θ)` with `x` the indicator of
a fresh `S`, Step 5 computes `qS S = Q(x)` and Step 6 finds `θ < Q(x)` (not yet
fathomed), so a fresh optimality cut (2.1) is imposed for `S` (p. 293). The case
`θ ≥ Q(x)` (fathom, no cut) is exactly the failure of this relation to hold — it is
read off `¬ Step` at the terminal state in `prop4_integer_lshaped_finite_convergence`. -/
inductive Step (d : Data n1 n2 m1 m2 K) (L : ℝ) (qS : Finset (Fin n1) → ℝ) :
    State n1 → State n1 → Prop
  | cut (Cuts : State n1) (x : Fin n1 → ℝ) (θ : ℝ) (hopt : IsBBOptimal d Cuts L qS x θ)
      (S : Finset (Fin n1)) (hS : x = indicator S) (hnew : S ∉ Cuts)
      (hqS : (qS S : EReal) = QY d x) (hviol : θ < qS S) :
      Step d L qS Cuts (insert S Cuts)

end StochasticProg.IntegerLShaped


