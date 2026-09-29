-- Prove2me | Definitions.Def_BiconvexProg_BranchBound_run
-- name    : BiconvexProg_BranchBound_run
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-26T17:53:08.09605+00:00
-- url     : https://prove2.me/theorems/35233003-0d5e-44d1-a50e-27f78745f7e5
-- title:
--   Runs of the convex-envelope branch-and-bound algorithm, best bounds $v_b^k$, $V_b^k$, and the stage function $\psi^k$
-- statement:
--   Fix data $S, f, g, \Omega$ of Problem $\mathcal P$. A **run** of the branch-and-bound algorithm of Al-Khayyal and Falk consists of four sequences indexed by the stage $k = 0, 1, 2, \dots$:
--
--   1. the multiset $\mathcal N_k$ of **open nodes** (boxes), with $\mathcal N_0 = \{\Omega\}$;
--   2. a selected node $B_k \in \mathcal N_k$;
--   3. a **stage point** $(x^k, y^k) \in S \cap B_k$ satisfying the **Best Bound Rule**: $\psi^{B_k}(x^k,y^k) \le \psi^B(z)$ for every open node $B \in \mathcal N_k$ and every $z \in S \cap B$. Thus $(x^k,y^k)$ solves the selected node's subproblem, and that node's value is the least among the open nodes' values;
--   4. a **branching index** $I_k$, maximizing the gap $x^k_i y^k_i - \mathrm{Vex}_{(B_k)_i}\, x_i y_i$ over $i$;
--
--   with the update
--
--   $$\mathcal N_{k+1} = (\mathcal N_k \setminus \{B_k\}) \cup \{\text{the four children of } B_k \text{ split at index } I_k \text{ and point } (x^k_{I_k}, y^k_{I_k})\}.$$
--
--   Along a run, the **best lower bound** is $v_b^k = \psi^{B_k}(x^k, y^k)$, the least subproblem value over the open nodes. The **best upper bound** is $V_b^k = \min\{\varphi(x^l, y^l) : l \le k\}$. The **stage function** of a multiset $\mathcal N$ of open boxes is
--
--   $$\psi(z) = \min\{\psi^B(z) : B \in \mathcal N,\ z \in B\}.$$
--
--   **Formalization Note** Stages are numbered from $0$, so the paper's Stage $k+1$ is index $k$ here. Runs are infinite and ignore the stopping test $v_b^k = V_b^k$; a stopped run of the paper is a prefix of such a run. The optional pruning of nodes with $v^{lj} \ge V_b^k$ (p. 278) is omitted. It does not change which node the Best Bound Rule can select, apart from ties. Ties in selection and in the branching index are arbitrary. $V_b^k$ uses the defining formula of p. 279, not the recursive form. Only the selected node's solution is recorded, since the non-selected nodes' solutions enter nothing but their values. The stage function takes a **minimum** over the open boxes containing $z$. The paper defines $\psi^k(z) = \psi^{kj}(z)$ for $z \in \Omega^{kj}$ and claims (p. 277) that this is well defined on shared faces, but it is not: from stage 3 on, two open boxes can share a point at which their node functions differ (see the mission's notes). The minimum agrees with the paper wherever only one open box contains $z$. The stage function's value at points in no open box is the default $0$.
-- source:
--   Al-Khayyal, Falk, Jointly Constrained Biconvex Programming, Math. Oper. Res. 8(2), 1983, pp. 276–279, The algorithm (stage function, Problem 𝒫^{kj}, branching rule, open nodes, v_b^k, V_b^k, Best Bound Rule)

import Mathlib
import Definitions.Def_BiconvexProg_BranchBound_problem

namespace BiconvexProg.BranchBound

variable {n : ℕ}

open Classical in
/-- An (infinite) run of the convex-envelope branch-and-bound algorithm (pp. 276–279) on the data
`S, f, g, Ω`. Stages are numbered from `0` (the paper's stage `k + 1` is index `k`).
* `nodes k` : the multiset of open nodes (boxes) at stage `k`; stage `0` is `{Ω}`;
* `sel k` : the open node selected for branching at stage `k`;
* `pt k` : the stage point `(xᵏ, yᵏ)`, a solution of the selected node's subproblem
  `min {ψ^{sel k} : S ∩ sel k}`, whose value is least among all open nodes' subproblem
  values (Best Bound Rule); equivalently `ψ^{sel k}(pt k) ≤ ψ^B(z)` for every open `B` and every
  `z ∈ S ∩ B`;
* `idx k` : the branching index, maximising `x_i y_i − Vex_{(sel k)_i} x_i y_i` at `pt k`;
* the next stage removes `sel k` and adds its four children split at `idx k` and at the
  `idx k`-th coordinate pair of `pt k` (Figure 1).
Runs never stop (the stopping test `v_b = V_b` is ignored) and the optional pruning of p. 278 is
omitted. -/
structure IsRun (S : Set ((Fin n → ℝ) × (Fin n → ℝ))) (f g : (Fin n → ℝ) → ℝ) (Ω : Box n)
    (nodes : ℕ → Multiset (Box n)) (sel : ℕ → Box n) (idx : ℕ → Fin n)
    (pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) : Prop where
  init : nodes 0 = {Ω}
  sel_mem : ∀ k, sel k ∈ nodes k
  pt_mem : ∀ k, pt k ∈ S ∩ (sel k).toSet
  best_bound : ∀ k, ∀ B ∈ nodes k, ∀ z ∈ S ∩ B.toSet, nodeFun f g (sel k) (pt k) ≤ nodeFun f g B z
  idx_max : ∀ k i, gap (sel k) i (pt k) ≤ gap (sel k) (idx k) (pt k)
  step : ∀ k, nodes (k + 1) =
    (nodes k).erase (sel k) + (sel k).split (idx k) ((pt k).1 (idx k)) ((pt k).2 (idx k))

/-- The best lower bound `v_bᵏ` at stage `k` (p. 279): the value `ψ^{sel k}(xᵏ, yᵏ)` of the
selected node, which by the Best Bound Rule is the least subproblem value among open nodes. -/
noncomputable def bestLower (f g : (Fin n → ℝ) → ℝ) (sel : ℕ → Box n)
    (pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ)) (k : ℕ) : ℝ :=
  nodeFun f g (sel k) (pt k)

/-- The best upper bound `V_bᵏ = min {φ(xˡ, yˡ) : l ≤ k}` at stage `k` (p. 279, defining
formula; stages from `0`). -/
noncomputable def bestUpper (f g : (Fin n → ℝ) → ℝ) (pt : ℕ → (Fin n → ℝ) × (Fin n → ℝ))
    (k : ℕ) : ℝ :=
  (Finset.range (k + 1)).inf' ⟨0, by simp⟩ (fun l => objective f g (pt l))

/-- The stage function `ψᵏ` built from the open nodes `N` (pp. 276, 279): at a point `z`, the
least node value `ψ^B(z)` over the open boxes `B ∈ N` containing `z`. Where only one open box
contains `z` this is the paper's `ψᵏ(z) = ψ^{kj}(z)`; on shared faces the node values need not
agree, and the minimum is taken. Junk value: `0` at points lying in no open box
(real `sInf ∅`). -/
noncomputable def stageFun (f g : (Fin n → ℝ) → ℝ) (N : Multiset (Box n))
    (z : (Fin n → ℝ) × (Fin n → ℝ)) : ℝ :=
  sInf ((fun B => nodeFun f g B z) '' {B | B ∈ N ∧ z ∈ B.toSet})

end BiconvexProg.BranchBound


