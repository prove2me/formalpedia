-- Prove2me | Definitions.Def_StochasticProg_Multistage_Algorithm
-- name    : StochasticProg_Multistage_Algorithm
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T20:09:41.280335+00:00
-- url     : https://prove2.me/theorems/16bfad42-78dc-417c-b781-3153a8c18373
-- title:
--   State and transition relation of the nested L-shaped method
-- statement:
--   The nested L-shaped (Benders decomposition) algorithm's bookkeeping and one-step
--   transition (Birge & Louveaux Ch. 6, pp. 288-289, "Nested L-Shaped Method for Multistage
--   Stochastic Linear Programs"), generalizing the two-stage method's state
--   (`StochasticProg.LShaped.State`/`Step`) from a flat scenario set to the tree.
--
--   `State inst` records, as `Sf : Finset (Node × FeasBasis n m)`, which feasibility cuts (1.3)
--   have been added so far (a pair `(k, b)` means: the cut derived from node $k$'s
--   infeasibility witness $b$, added to $k$'s parent), and, as `So : Finset (Node -> Basis n
--   m)`, which Step-3 witnesses have each produced an optimality cut (1.4).
--   `LocalFeasibleWithCuts inst Sf j xp xj` is node $j$'s local feasible region together with
--   every recorded feasibility cut targeting $j$. `LocalOptFeasible inst So j xj θj` is every
--   recorded optimality cut at $j$. `IsNodeOptimal inst Sf So j xp xj θj` is node $j$'s
--   Step-1 optimum given parent value $xp$ and the current cuts: it minimizes $(c^t_j)^Tx_j +
--   θ_j$ when $j$ has children (so carries a $θ_j$ term), or $(c^t_j)^Tx_j$ alone when $j$ is a
--   last-stage node ("we may also refer to the stage $H$ problem in which $θ^H_k$ ... [is] not
--   present", p. 288). `IsRootInfeasible inst Sf` is the algorithm's Step-1 infeasibility
--   certificate for the whole tree ("if infeasible and $t=1$, then stop", p. 288).
--
--   `Step inst` is one admissible transition: from a tree-wide Step-1-optimal assignment
--   $(x,θ)$ consistent with the current cuts, either a fresh feasibility cut is added (a
--   non-root node $k$ whose Step-2 test at its parent's current value is positive) or a fresh
--   optimality cut is added at a node $j$ with children, built from a witness basis for each
--   child that currently violates $j$'s recorded bound on $θ_j$ — both require the new
--   witness not already recorded, matching the "return to Step 1" branching of the text.
-- source:
--   Birge & Louveaux, Introduction to Stochastic Programming, 2nd ed., Springer 2011, pp. 288-289, Chapter 6, Section 6.1, "Nested L-Shaped Method for Multistage Stochastic Linear Programs", Eqs. (1.1)-(1.5)

import Mathlib
import Definitions.Def_StochasticProg_Multistage_Tree
import Definitions.Def_StochasticProg_Multistage_Instance
import Definitions.Def_StochasticProg_Multistage_Bases

namespace StochasticProg.Multistage

open scoped Matrix

variable {H n m : ℕ} {T : Tree H}

/-- The algorithm's state after some number of outer iterations: `Sf` records, as `(node,
basis)` pairs, which feasibility cuts (1.3) Step 2 has added so far (the cut derived from
node `k`'s infeasibility witness is added to `k`'s *parent*); `So` records which Step-3
witnesses (one basis per node) have each produced an optimality cut (1.4) so far — the same
shape as the two-stage `L`-shaped method's state (`Def_StochasticProg_LShaped_Algorithm`),
with the flat scenario set `Fin K` replaced by the tree's `T.Node`. -/
def State (inst : Instance H n m T) : Type := Finset (T.Node × FeasBasis n m) × Finset (T.Node → Basis n m)

variable (inst : Instance H n m T)

/-- Node `j` satisfies its own local constraints at parent value `xp`, and every feasibility
cut (1.3) recorded for a child of `j` (Step 1, using Eq. (1.10)-(1.11)). -/
def LocalFeasibleWithCuts (Sf : Finset (T.Node × FeasBasis n m)) (j : T.Node) (xp : Fin n → ℝ)
    (xj : Fin n → ℝ) : Prop :=
  LocalFeasible inst j xp xj ∧
    ∀ p ∈ Sf, T.anc p.1 = j → (feasCutCoeffs inst p.1 p.2).2 ≤ dotProduct (feasCutCoeffs inst p.1 p.2).1 xj

/-- `(x_j, θ_j)` satisfies every optimality cut (1.4) recorded at `j` (built from a
`So`-witness restricted to `j`'s children). -/
def LocalOptFeasible (So : Finset (T.Node → Basis n m)) (j : T.Node) (xj : Fin n → ℝ) (θj : ℝ) :
    Prop :=
  ∀ β ∈ So, (optCutCoeffs inst β j).2 ≤ dotProduct (optCutCoeffs inst β j).1 xj + θj

/-- `(x_j, θ_j)` is a Step-1 optimal solution of node `j`'s local master program (1.1)-(1.5)
with the recorded cuts `Sf`, `So`, at parent value `xp`: minimizes `(c^t_j)ᵀx_j + θ_j` over the
locally-cut-feasible region once an optimality cut has been recorded (`So.Nonempty`), and
minimizes `(c^t_j)ᵀx_j` alone before any cut exists — Step 0's "add the constraint `θ^t_k = 0`
to (1.1)-(1.5) for all `t` and `k`" (p. 288), under which `θ` is present in the LP from the
first solve but fixed/unconstrained until cuts start bounding it, never left to range
unboundedly free while simultaneously required to attain a joint minimum. The gate is on cut
existence (`So.Nonempty`), not on tree topology (`(T.children j).Nonempty`): the latter makes
this clause unsatisfiable for every node with children as soon as `So = ∅`, since
`LocalOptFeasible` is then vacuously true for every `θj'`, forcing an optimum over an unbounded
`θj'` — the bug `CHANGES_REQUESTED.md` (2026-09-19) identified, fixed here by mirroring the
already-passed two-stage sibling's `IsMasterOptimal` exactly. -/
def IsNodeOptimal (Sf : Finset (T.Node × FeasBasis n m)) (So : Finset (T.Node → Basis n m))
    (j : T.Node) (xp : Fin n → ℝ) (xj : Fin n → ℝ) (θj : ℝ) : Prop :=
  LocalFeasibleWithCuts inst Sf j xp xj ∧
    ((T.children j).Nonempty → LocalOptFeasible inst So j xj θj) ∧
    (if So.Nonempty then
        ∀ xj' θj', LocalFeasibleWithCuts inst Sf j xp xj' → LocalOptFeasible inst So j xj' θj' →
          dotProduct (inst.c j) xj + θj ≤ dotProduct (inst.c j) xj' + θj'
      else
        ∀ xj', LocalFeasibleWithCuts inst Sf j xp xj' → dotProduct (inst.c j) xj ≤ dotProduct (inst.c j) xj')

/-- The root's local master program has no feasible `x`: the algorithm's certificate
(Step 1, "If infeasible and `t = 1`, then stop; problem (3.4.1) is infeasible", p. 288) that
the tree-wide problem is infeasible. -/
def IsRootInfeasible (Sf : Finset (T.Node × FeasBasis n m)) : Prop :=
  ¬ ∃ x, LocalFeasibleWithCuts inst Sf T.root 0 x

/-- One admissible transition of the nested `L`-shaped algorithm: from cut set `(Sf, So)`,
given a tree-wide assignment `(x, θ)` of Step-1 optima at every node consistent with the
current cuts, either a fresh feasibility cut is added (Step 1/2: node `k`, not the root, whose
Step-2 test at its parent's current value has positive optimal value, so `k` is infeasible
there) or a fresh optimality cut is added at some node `j` with children (Step 2, Eq. (1.1)),
built from a witness basis for each child that currently violates `j`'s recorded bound on
`θ_j`. Both require the added basis (pair or tuple) not already recorded, matching the
"return to Step 1" branching of the text (p. 288-289). -/
inductive Step (inst : Instance H n m T) : State inst → State inst → Prop
  | feas (Sf : Finset (T.Node × FeasBasis n m)) (So : Finset (T.Node → Basis n m))
      (x : T.Node → Fin n → ℝ) (θ : T.Node → ℝ)
      (hopt : ∀ j, IsNodeOptimal inst Sf So j (if (T.stage j).val = 0 then 0 else x (T.anc j)) (x j) (θ j))
      (k : T.Node) (hk0 : (T.stage k).val ≠ 0) (b : FeasBasis n m)
      (hb : IsFeasBasisOptimalAt inst k b (x (T.anc k)))
      (hpos : 0 < feasBasisValue inst k b (x (T.anc k)))
      (hnew : (k, b) ∉ Sf) :
      Step inst (Sf, So) (insert (k, b) Sf, So)
  | opt (Sf : Finset (T.Node × FeasBasis n m)) (So : Finset (T.Node → Basis n m))
      (x : T.Node → Fin n → ℝ) (θ : T.Node → ℝ)
      (hopt : ∀ j, IsNodeOptimal inst Sf So j (if (T.stage j).val = 0 then 0 else x (T.anc j)) (x j) (θ j))
      (j : T.Node) (hj : (T.children j).Nonempty) (β : T.Node → Basis n m)
      (hβ : ∀ k ∈ T.children j, IsOptimalAt inst k (β k) (x j))
      (hviol : θ j < (optCutCoeffs inst β j).2 - dotProduct (optCutCoeffs inst β j).1 (x j))
      (hnew : β ∉ So) :
      Step inst (Sf, So) (Sf, insert β So)

end StochasticProg.Multistage


