-- Prove2me | Definitions.Def_LNTopology_Hermetization_findHermetizable
-- name    : LNTopology_Hermetization_findHermetizable
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T03:28:06.782458+00:00
-- url     : https://prove2.me/theorems/05b1dc9f-a1ee-4fb4-80e5-ab562d1f94cf
-- title:
--   Algorithm of Theorem 3.8: find a hermetizable set
-- statement:
--   The **algorithm of Theorem 3.8** takes the flows $\Lambda$ of a network on $n$ nodes and oracle access to $c$ and $g_+$, and returns a node set:
--
--   1. for every node $v$, read its row of $\Lambda$ and compute $d(v)$, $s(v)$, $S(v)$ and the list of nodes $j$ with $\lambda_{v,j}\ne0$;
--   2. compute $D=\max_{v:\,d(v)\ne0}c(S(v))/c(s(v))$ (and $D=0$ if no node has a channel), which is $\mathrm{disc}(G)$;
--   3. for $d=0,1,\dots,n$, record whether $g_+(d)\le 2D$;
--   4. run the peeling algorithm on the lists of step 1 with the test "$d=0$, or $d\le n$ and $g_+(d)\le 2D$", and return its output.
--
--   When $g_+^{-1}(2\,\mathrm{disc}(G))$ exists, step 4 deletes exactly the isolated vertices and the vertices of degree $\le g_+^{-1}(2\,\mathrm{disc}(G))$, as in the paper's proof of Theorem 3.8 (Lemma B.3 applied with that threshold). No degree exceeds $n$, so the clause $d\le n$ never changes a test the algorithm performs. The algorithm makes $O((n+1)^2)$ ticks on every input.
--
--   **Formalization Note** Running time is counted in the real-RAM model of the mission's tick counter. The algorithm uses no choice and no search over subsets: every decision about real numbers is a ticked comparison of concrete values.
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 (PDF p. 9), and the proof of Theorem 3.8, p. 12 (PDF p. 13)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_tick
import Definitions.Def_LNTopology_Hermetization_lamAt
import Definitions.Def_LNTopology_Hermetization_cAt
import Definitions.Def_LNTopology_Hermetization_gAt
import Definitions.Def_LNTopology_Hermetization_rlt
import Definitions.Def_LNTopology_Hermetization_rle
import Definitions.Def_LNTopology_Hermetization_req
import Definitions.Def_LNTopology_Hermetization_rabs
import Definitions.Def_LNTopology_Hermetization_rmul
import Definitions.Def_LNTopology_Hermetization_rdiv
import Definitions.Def_LNTopology_Hermetization_peel

namespace LNTopology.Hermetization

/-- **The algorithm of Theorem 3.8: find a set whose hermetization reduces the cost.**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), Theorem 3.8, p. 8 ("there is a polynomial-time algorithm to find a set U whose
hermetization reduces its cost"), and the proof of Theorem 3.8, p. 12 (Lemma B.3's algorithm
applied with the threshold g₊⁻¹(2disc(G))).

Input: the flows `lam` of a network on `Fin n`, oracle access to `c` and `g` (= `g₊`).
1. For every node `v`, read its row through `lamAt` and compute `d(v)`, `s(v)`, `S(v)`
   (Definitions 3.4–3.5) and the list of `j` with `lam v j ≠ 0` (in increasing order).
2. Compute `D = max_{v : d(v) ≠ 0} c(S(v)) / c(s(v))`, and `D = 0` if no node has a channel;
   this is `disc c lam`.
3. Tabulate, for `d = 0, …, n`, whether `g(d) ≤ 2D` (one query of `g` and one comparison each).
4. Run `peel` on the adjacency lists with the test `bad d := d = 0 ∨ (d ≤ n ∧ g(d) ≤ 2D)` and
   return its output.

When `g₊⁻¹(2disc(G))` exists, step 4 deletes exactly the vertices of degree `≤ g₊⁻¹(2disc(G))`
(and isolated vertices), as in the proof of Theorem 3.8. No degree exceeds `n`, so the clause
`d ≤ n` never changes a test the algorithm performs.

**Formalization Note.** Reading R4: the running time is counted in ticks under the real-RAM
discipline of `tick`. The algorithm uses no choice and no search over subsets; every real
decision is a ticked comparison of concrete values. It runs in `O((n + 1)^2)` ticks on every
input. -/
noncomputable def findHermetizable {n : ℕ} (lam : Fin n → Fin n → ℝ) (c g : ℝ → ℝ) :
    StateM ℕ (Finset (Fin n)) := do
  -- 1. degrees, smallest and largest flows, adjacency lists
  let mut dg : Fin n → ℕ := fun _ => 0
  let mut sm : Fin n → ℝ := fun _ => 0
  let mut lg : Fin n → ℝ := fun _ => 0
  let mut adj : Fin n → List (Fin n) := fun _ => []
  for v in List.finRange n do
    tick 1
    for j in (List.finRange n).reverse do
      tick 1
      let x ← lamAt lam v j
      let a ← rabs x
      let bigger ← rlt (lg v) a
      if bigger then
        lg := Function.update lg v a
      let z ← req x 0
      if !z then
        if dg v = 0 then
          sm := Function.update sm v a
        else
          let smaller ← rlt a (sm v)
          if smaller then
            sm := Function.update sm v a
        dg := Function.update dg v (dg v + 1)
        adj := Function.update adj v (j :: adj v)
  -- 2. the discrepancy D = disc(G)
  let mut D : ℝ := 0
  let mut found : Bool := false
  for v in List.finRange n do
    tick 1
    if dg v ≠ 0 then
      let cS ← cAt c (lg v)
      let cs ← cAt c (sm v)
      let r ← rdiv cS cs
      if found then
        let up ← rlt D r
        if up then
          D := r
      else
        D := r
        found := true
  -- 3. the degree test g(d) ≤ 2D, tabulated for d = 0, …, n
  let twoD ← rmul 2 D
  let mut fails : ℕ → Bool := fun _ => false
  for d in List.range (n + 1) do
    tick 1
    let gd ← gAt g (d : ℝ)
    let f ← rle gd twoD
    fails := Function.update fails d f
  -- 4. Lemma B.3's peeling
  peel adj (fun d => d = 0 ∨ (d ≤ n ∧ fails d = true))

end LNTopology.Hermetization


