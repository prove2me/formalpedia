-- Prove2me | Definitions.Def_MinDegST_AddOne_Inputs
-- name    : MinDegST_AddOne_Inputs
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T06:53:04.406058+00:00
-- url     : https://prove2.me/theorems/c6c76944-97be-47e0-bdeb-e5851eb2e3cd
-- title:
--   Input layouts for Lemmas 14.3, 14.4 and 14.6
-- statement:
--   Input layouts of the local subroutines. Lemma 14.3 receives $[n,k,\theta,|E(F)|]$ and $F$'s edge list. Lemma 14.4 bounds its time by $|E(G[V(C)])|$ and Lemma 14.6 by $\sum_{v\in V(M)}\deg_G(v)$, below the size of the whole input; such a bound means something on a RAM only once one fixes what the subroutine is handed, which the paper does not say. The layouts hand the subroutine exactly its local piece: for Lemma 14.4, $[n,k,u,|V(C)|]$, each node of $C$ with its forest degree, the edge list of $G[V(C)]$ and that of $F[V(C)]$; for one molecule in Lemma 14.6, $[n,k,|V(\mu)|]$, each node $v$ of $\mu$ with $\deg_F(v)$, $\deg_G(v)$ and its adjacency list in $G$, and the edge list of $F$ inside $\mu$; for all molecules in Lemma 14.6, the graph, $k$, the forest and the decomposition as a list of molecules.
--
--   **Formalization Note.** Node names are the global names $0,\dots,n-1$; forest degrees are supplied because they decide slack and saturated nodes.
-- source:
--   Bhattacharya, Farokhnejad, Saranurak, Wang, Faster Algorithms for Minimum Degree Spanning Tree, STOC 2027 submission (manuscript sha256 7d985d3b…), p. 37–38 (Lemmas 14.3, 14.4, 14.6); layouts chosen by the formalization

import Mathlib
import Definitions.Def_MinDegST_AddOne_Graph
import Definitions.Def_MinDegST_AddOne_Machine
import Definitions.Def_MinDegST_AddOne_Molecules

open Classical

namespace MinDegST.AddOne

/-! # Input layouts of the local subroutines (Lemmas 14.3, 14.4, 14.6)

Lemma 14.4 and the first sentence of Lemma 14.6 bound the running time by the size of a local
piece of the graph (`Õ(|E(G[V(C)])|)`, `Õ(Σ_{v∈V(M)} deg_G(v))`), which is below the size of the
whole input. Such a bound only has a meaning on a RAM once one fixes what the subroutine is handed;
the paper does not say. The layouts below hand the subroutine exactly the local piece: the node
list, the current forest degrees of those nodes (which decide slack/saturated), and the local
edges. All node names are the global names `0, …, n − 1`. -/

variable {n : ℕ}

/-- Input of Lemma 14.3: `[n, k, θ, |E(F)|, u₁, v₁, …]` (the forest's edge list). -/
def encThetaInput (n k θ : ℕ) (fs : List (Fin n × Fin n)) : List ℤ :=
  [(n : ℤ), (k : ℤ), (θ : ℤ), (fs.length : ℤ)] ++ encPairs fs

/-- Input of Lemma 14.4 for the region `C`, the node `u` and the forest `F`:
`[n, k, u, |V(C)|]`, then `v, deg_F(v)` for each node `v` of the list `vs` of `V(C)`, then
`|gs|` and the edge list `gs` of `G[V(C)]`, then `|fs|` and the edge list `fs` of `F[V(C)]`. -/
noncomputable def encRegionInput (n k : ℕ) (u : Fin n) (F : SimpleGraph (Fin n)) (vs : List (Fin n))
    (gs fs : List (Fin n × Fin n)) : List ℤ :=
  [(n : ℤ), (k : ℤ), (u.val : ℤ), (vs.length : ℤ)] ++
    vs.flatMap (fun v => [(v.val : ℤ), (deg F v : ℤ)]) ++
    [(gs.length : ℤ)] ++ encPairs gs ++ [(fs.length : ℤ)] ++ encPairs fs

/-- Input of the first part of Lemma 14.6 for one molecule with node list `vs`: `[n, k, |vs|]`,
then for each node `v` of `vs`: `v, deg_F(v), deg_G(v)` and the adjacency list `nb v` of `v` in `G`;
then `|fs|` and the edge list `fs` of `F` inside the molecule. -/
noncomputable def encMoleculeInput (n k : ℕ) (F : SimpleGraph (Fin n)) (vs : List (Fin n))
    (nb : Fin n → List (Fin n)) (fs : List (Fin n × Fin n)) : List ℤ :=
  [(n : ℤ), (k : ℤ), (vs.length : ℤ)] ++
    vs.flatMap (fun v => [(v.val : ℤ), (deg F v : ℤ), ((nb v).length : ℤ)] ++
      (nb v).map fun w => (w.val : ℤ)) ++
    [(fs.length : ℤ)] ++ encPairs fs

/-- Input of the second part of Lemma 14.6: the graph, `k`, the forest (as in `encForestInput`),
followed by the molecular decomposition as a list of molecules (`encMolecules`). -/
def encDecompInput (n : ℕ) (es : List (Fin n × Fin n)) (k : ℕ) (fs : List (Fin n × Fin n))
    (lM : List (Molecule n)) : List ℤ :=
  encForestInput n es k fs ++ encMolecules lM

end MinDegST.AddOne


