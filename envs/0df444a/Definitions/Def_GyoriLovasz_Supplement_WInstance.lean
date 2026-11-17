-- Prove2me | Definitions.Def_GyoriLovasz_Supplement_WInstance
-- name    : GyoriLovasz_Supplement_WInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T07:10:07.650866+00:00
-- url     : https://prove2.me/theorems/9bd43c7a-477a-44cf-a4ca-6b69c8dcfeb8
-- title:
--   Weighted input: a digraph with terminals, capacities $c_t$ and non-terminal weights $w_v$; $w_{\max}$
-- statement:
--   A **weighted input** of the algorithms of Theorems 3 and 4 is an unweighted input (a directed graph on the vertices $0,\dots,n-1$, given by its edge list, and a list of distinct terminals $t_1,\dots,t_k$ with nonnegative integer capacities $c_1,\dots,c_k$) together with a list of weights $w_0,\dots,w_{n-1}$, one per vertex. Only the weights of the non-terminal vertices $v\in V\setminus T$ are used.
--
--   The input is **well formed** when the unweighted input is (all edge endpoints and terminals are vertices, terminals are distinct) and there is exactly one weight per vertex. The weights are **positive** when $w_v>0$ for every non-terminal $v$. The **maximum weight** is
--
--   $$
--   w_{\max}=\max_{v\in V\setminus T} w_v ,
--   $$
--
--   taken to be $0$ when every vertex is a terminal.
--
--   This is the data of the weighted Győri–Lovász problem: the capacity $c_t$ now bounds the total weight, not the number, of the non-terminals placed with $t$.
--
--   **Formalization Note** Positivity is a separate predicate (`PosWeights`), assumed in Theorems 3 and 4. When there is no non-terminal, $w_{\max}=0$ is never effective, since then every part has weight $0$.
-- source:
--   Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani, Breaking the Exponential Barrier: The First Polynomial-Time Algorithm for the Győri–Lovász Theorem, arXiv:2608.30945 (held file sha256 3f80f82d3e45b364bf6e7d363e7e2291bbe55b2f994efed6cc39405149cd780e), Theorem 3, p.11; Theorem 4, p.12; §2, p.14 (definition of $w_{\max}$)

import Mathlib
import Definitions.Def_GyoriLovasz_Instance

namespace GyoriLovasz

namespace Supplement

/-- **An input of the weighted algorithm of Theorems 3 and 4.** Hajiaghayi, JafariRaviz, Kaviani, Mohammadkhani,
*Breaking the Exponential Barrier*, arXiv:2608.30945 (held file sha256 3f80f82d…780e), Theorem 3, p.11, Theorem 4,
p.12, §2, p.14: a directed graph with terminal set `T`, a capacity `c_t` for every terminal and a weight `w_v` for every
non-terminal.

`base` is the published unweighted input (`n` vertices `0, …, n − 1`, the edge list, entry `i` of `terms` is
`(t_i, c_i)`); entry `v` of `weights` is `w_v`.

**Formalization Note.** Entries of `weights` at terminals are ignored. Positivity of the non-terminal weights is the
separate predicate `PosWeights`, a hypothesis of Theorems 3 and 4. -/
structure WInstance where
  base : Instance
  weights : List ℕ

namespace WInstance

/-- Well-formed weighted input: the unweighted input is well formed and there is one weight per vertex. -/
def WellFormed (I : WInstance) : Prop :=
  I.base.WellFormed ∧ I.weights.length = I.base.n

/-- The weight `w_v` of a vertex `v` (`0` beyond the list, where it is never read). -/
def w (I : WInstance) (v : ℕ) : ℕ := I.weights.getD v 0

/-- The non-terminal vertices `V \ T`. -/
def nonTerms (I : WInstance) : Finset ℕ := Finset.range I.base.n \ I.base.termSet

/-- Every non-terminal has a positive weight ("each non-terminal vertex `v` has a positive integer weight `w_v`",
Theorems 3 and 4). -/
def PosWeights (I : WInstance) : Prop := ∀ v ∈ I.nonTerms, 0 < I.w v

/-- **`w_max = max_{v ∈ V \ T} w_v`** (§2, p.14). It is `0` when there is no non-terminal; then every part has weight
`0` and the bound `c_t + w_max − 1` is never effective. -/
def wmax (I : WInstance) : ℕ := I.nonTerms.sup I.w

end WInstance

end Supplement

end GyoriLovasz


