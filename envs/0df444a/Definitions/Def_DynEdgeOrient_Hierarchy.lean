-- Prove2me | Definitions.Def_DynEdgeOrient_Hierarchy
-- name    : DynEdgeOrient_Hierarchy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:37:47.338282+00:00
-- url     : https://prove2.me/theorems/b15ab346-f72f-4de5-ae54-d84c6152075e
-- title:
--   Total and nearly isolated DIS's and the DIS hierarchy constructed in Lemma 4.9
-- statement:
--   A **dynamic induced subgraph (DIS)** $(S,I)$ consists of a vertex set $S$ and an interval of updates $I=[i,k)$, i.e. $u_i,\dots,u_{k-1}$; it is the dynamic graph $G_{i-1}[S],\dots,G_{k-1}[S]$. Its **window** is the set of times $i-1,\dots,k-1$.
--
--   1. $(S,I)$ is **total** if every edge inserted or deleted during $I$ has both endpoints in $S$.
--   2. $(S,I)$ is **nearly isolated** if no vertex $v\notin S$ has $|E(S,v)|\ge2\alpha$ at any time of the window.
--
--   The **hierarchy** for $|U|=2^K$ updates is built bottom-up as in the proof of Lemma 4.9. Node $(\ell,q)$, for $0\le\ell\le K$ and $0\le q<2^{K-\ell}$, has interval $I=[q2^\ell+1,(q+1)2^\ell+1)$ and window $[q2^\ell,(q+1)2^\ell]$; its children are $(\ell-1,2q)$ and $(\ell-1,2q+1)$.
--
--   1. The leaf $(0,q)$ has $S=\{w,v\}$, the endpoints of the edge changed by $u_{q+1}$.
--   2. The node $(\ell,q)$ with $\ell\ge1$ starts from $S=S_1\cup S_2$, the union of its children's sets, and adds vertices while some $v\notin S$ has $|E(v,S)|\ge2\alpha$ throughout the window.
--
--   The result of step 2 is the least superset $T$ of $S_1\cup S_2$ such that no $v\notin T$ has $|E(v,T)|\ge2\alpha$ at every time of the window. The hierarchy is **special** if every node is total and nearly isolated on its window.
--
--   The hierarchy organises the update sequence so that each node's flips can be confined to its own vertex set.
--
--   **Formalization Note** "Throughout $I$" means the states $G_{i-1},\dots,G_{k-1}$, both ends included. The least closed superset is an intersection over all closed supersets; the rule is monotone, so it coincides with the while-loop's result for every order of additions.
-- source:
--   S. Hiken, N. Wein, Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n Barrier, STOC 2027 submission (manuscript sha256 626b4eee…), Definitions 4.1, 4.3–4.6, pp.12–13, and the proof of Lemma 4.9, p.14

import Mathlib
import Definitions.Def_DynEdgeOrient_DynamicGraph

namespace DynEdgeOrient

/-!
# Total and nearly isolated DIS, and the DIS hierarchy of Lemma 4.9

S. Hiken, N. Wein, *Dynamic Edge Orientation on Low-Arboricity Graphs: Breaking the log n
Barrier*, STOC 2027 submission (manuscript sha256 626b4eee…), Definitions 4.1, 4.3–4.6, pp.12–13,
and the construction in the proof of Lemma 4.9, p.14.

**Formalization Note.**
* A DIS `(S, I)` with `I = [i, k)` consists of the updates `u_i, …, u_{k−1}`; "throughout `I`"
  means the states `G_{i−1}, …, G_{k−1}`. Here a DIS is given by `S` and its **window of times**
  `[lo, hi] = [i − 1, k − 1]`, both ends included; its updates are the transitions
  `G t → G (t+1)` for `lo ≤ t < hi`.
* `IsTotal ends G S lo hi` (Definition 4.3): every edge inserted or deleted during the window has
  both endpoints in `S`.
* `IsNearlyIsolated ends G α S lo hi` (Definition 4.4): no `v ∉ S` has `|E(S, v)| ≥ 2α` at any
  time of the window.
* **The hierarchy is the paper's construction** (proof of Lemma 4.9), indexed by level `ℓ` and
  position `q`: node `(ℓ, q)` has `I = [q·2^ℓ + 1, (q+1)·2^ℓ + 1)`, so window
  `[winLo ℓ q, winHi ℓ q] = [q·2^ℓ, (q+1)·2^ℓ]`, and children `(ℓ−1, 2q)`, `(ℓ−1, 2q+1)`. For
  `|U| = 2^K` the nodes are `ℓ ≤ K`, `q < 2^(K−ℓ)`; the root is `(K, 0)`; leaves are `ℓ = 0`.
* Step 1: the leaf `(0, q)` is the update `u_{q+1}`, and `hierS 0 q` is the set of endpoints of
  the edges of `G q ∆ G (q+1)` (exactly one edge under `IsDynamic`).
* Step v ("while there is `v ∈ V ∖ S` with `|E(v, S)| ≥ 2α`: add `v` to `S`") is `closure`: the
  **least** superset `T` of `S₁ ∪ S₂` such that no `v ∉ T` has `|E(v, T)| ≥ 2α` at every time of
  the window. The rule is monotone in `T` and closed sets are closed under intersection, so the
  least one exists and equals the result of the loop in any order of additions. The paper notes
  that `E(v, S)` is time invariant on the window (by totality of the children), so "at every time"
  is the paper's condition; the Lean definition does not presuppose the invariance.
* `IsSpecial ends G α K` (Definition 4.6): every node of the hierarchy is total and nearly
  isolated on its window.
-/

variable {V E : Type*} [DecidableEq V] [DecidableEq E]

/-- Definition 4.3: every edge inserted or deleted during the window `[lo, hi]` (the transitions
`G t → G (t+1)`, `lo ≤ t < hi`) has both endpoints in `S`. -/
def IsTotal (ends : E → V × V) (G : ℕ → Finset E) (S : Finset V) (lo hi : ℕ) : Prop :=
  ∀ t, lo ≤ t → t < hi → ∀ e ∈ symmDiff (G t) (G (t + 1)), (ends e).1 ∈ S ∧ (ends e).2 ∈ S

/-- Definition 4.4: no vertex outside `S` has `2α` or more edges into `S` at any time
`lo ≤ t ≤ hi` of the window. -/
def IsNearlyIsolated (ends : E → V × V) (G : ℕ → Finset E) (α : ℕ) (S : Finset V)
    (lo hi : ℕ) : Prop :=
  ∀ v, v ∉ S → ∀ t, lo ≤ t → t ≤ hi → (edgesBetween ends (G t) {v} S).card < 2 * α

/-- First time of the window of node `(ℓ, q)`: `i − 1 = q·2^ℓ`. -/
def winLo (ℓ q : ℕ) : ℕ := q * 2 ^ ℓ

/-- Last time of the window of node `(ℓ, q)`: `k − 1 = (q+1)·2^ℓ`. -/
def winHi (ℓ q : ℕ) : ℕ := (q + 1) * 2 ^ ℓ

/-- Step 1 of the construction: the endpoints of the edge changed by the update `u_{q+1}`. -/
def leafSet (ends : E → V × V) (G : ℕ → Finset E) (q : ℕ) : Finset V :=
  (symmDiff (G q) (G (q + 1))).biUnion (fun e => {(ends e).1, (ends e).2})

variable [Fintype V]

/-- Step v of the construction: the least `T ⊇ S₀` such that no `v ∉ T` has
`|E(v, T)| ≥ 2α` at every time `lo ≤ t ≤ hi`. -/
def closure (ends : E → V × V) (G : ℕ → Finset E) (α lo hi : ℕ) (S₀ : Finset V) : Finset V :=
  ((Finset.univ : Finset (Finset V)).filter (fun T => S₀ ⊆ T ∧
      ∀ v, v ∉ T → ∃ t ∈ Finset.Icc lo hi, (edgesBetween ends (G t) {v} T).card < 2 * α)).inf id

/-- The vertex set `S` of node `(ℓ, q)` of the DIS hierarchy built in the proof of Lemma 4.9:
leaves are the endpoints of their update, and node `(ℓ+1, q)` is the closure, on its window, of
the union of its children `(ℓ, 2q)` and `(ℓ, 2q+1)`. -/
def hierS (ends : E → V × V) (G : ℕ → Finset E) (α : ℕ) : ℕ → ℕ → Finset V
  | 0, q => leafSet ends G q
  | ℓ + 1, q => closure ends G α (winLo (ℓ + 1) q) (winHi (ℓ + 1) q)
      (hierS ends G α ℓ (2 * q) ∪ hierS ends G α ℓ (2 * q + 1))

/-- Definition 4.6 for the constructed hierarchy with `2^K` leaves: every node `(ℓ, q)`,
`ℓ ≤ K`, `q < 2^(K−ℓ)`, is total and nearly isolated on its window. -/
def IsSpecial (ends : E → V × V) (G : ℕ → Finset E) (α K : ℕ) : Prop :=
  ∀ ℓ ≤ K, ∀ q < 2 ^ (K - ℓ),
    IsTotal ends G (hierS ends G α ℓ q) (winLo ℓ q) (winHi ℓ q) ∧
    IsNearlyIsolated ends G α (hierS ends G α ℓ q) (winLo ℓ q) (winHi ℓ q)

end DynEdgeOrient


