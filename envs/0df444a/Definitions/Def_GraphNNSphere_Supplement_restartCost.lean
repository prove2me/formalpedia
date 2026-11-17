-- Prove2me | Definitions.Def_GraphNNSphere_Supplement_restartCost
-- name    : GraphNNSphere_Supplement_restartCost
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T09:47:54.582477+00:00
-- url     : https://prove2.me/theorems/22eec9c0-755a-408d-816b-580fa1263556
-- title:
--   Independent restarts and their distinct-evaluation cost
-- statement:
--   **Independent restarts** run greedy navigation repeatedly on one sampled graph from fresh entries $x^{(1)},x^{(2)},\dots$ until a run succeeds. Their cost counts the union of all points evaluated by every attempt, failed attempts included, through the successful attempt:
--
--   $$\Big|\bigcup_{i\le m}\mathrm{Ev}(x^{(i)})\Big|,\qquad m=\min\{i: W_G(q;x^{(i)})<\infty\},$$
--
--   where $\mathrm{Ev}(x_0)$ is the set of points evaluated by the run from $x_0$ (through its first successful expansion, or through its last expansion if it fails). The cost is $\infty$ if no attempt succeeds.
--
--   **Formalization Note** $\mathrm{Ev}$ follows the base mission's navigation run step by step, and on success its size is the run's evaluation count $W_G(q;x_0)$ (proved in the mission's sanity file).
-- source:
--   Lu, Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3; Theorem 5.1, p.54

import Mathlib
import Definitions.Def_GraphNNSphere_greedyRun
import Definitions.Def_GraphNNSphere_W

namespace GraphNNSphere

namespace Supplement

open Classical in
/-- The set of labels evaluated by one visit of the navigation run, mirroring the base mission's
`greedyLoop`: through the first completed expansion after which a target has been evaluated, or
through the final expansion of an unsuccessful run (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3). -/
noncomputable def greedyEvalLoop {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d)
    (k : ℕ) : ℕ → Fin n → Finset (Fin n) → Finset (Fin n)
  | 0, _, ev => ev
  | fuel + 1, cur, ev =>
    if ∃ j ∈ ev ∪ G cur, IsTarget k X q j then ev ∪ G cur
    else
      match successor G X q cur with
      | some y =>
        if geo q (X y) < geo q (X cur) then greedyEvalLoop G X q k fuel y (ev ∪ G cur)
        else ev ∪ G cur
      | none => ev ∪ G cur

/-- The set of labels evaluated by the navigation run from the entry `x₀` (its cardinality is the
evaluation count of `greedyRun` on success) (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3). -/
noncomputable def greedyEvalSet {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d) (k : ℕ)
    (x₀ : Fin n) : Finset (Fin n) :=
  greedyEvalLoop G X q k (n + 1) x₀ {x₀}

open Classical in
/-- The evaluation cost of independent restarts from the entries `e 0, e 1, …` on one sampled graph:
the number of distinct labels evaluated by all attempts, failed ones included, through the first
successful attempt, and `∞` if no attempt succeeds (Lu, *Sharp Limits of Graph-Based Nearest Neighbor Search on the Sphere*, STOC 2027 submission (manuscript sha256 93565bc5…), §1.2, p.3: "Across restarts, the cost
counts the union of all evaluated points"; Theorem 5.1, p.54). -/
noncomputable def restartCost {n d : ℕ} (G : NavGraph n) (X : Fin n → Sph d) (q : Sph d) (k : ℕ)
    (e : ℕ → Fin n) : ℕ∞ :=
  if h : ∃ m, W G X q k (e m) < ⊤ then
    (((Finset.range (Nat.find h + 1)).biUnion (fun i => greedyEvalSet G X q k (e i))).card : ℕ∞)
  else ⊤

end Supplement

end GraphNNSphere


