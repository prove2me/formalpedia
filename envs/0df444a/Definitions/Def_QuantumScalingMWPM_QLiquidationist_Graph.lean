-- Prove2me | Definitions.Def_QuantumScalingMWPM_QLiquidationist_Graph
-- name    : QuantumScalingMWPM_QLiquidationist_Graph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-11T07:11:31.645767+00:00
-- url     : https://prove2.me/theorems/6601e007-904c-4373-b296-67f6c015bfcc
-- title:
--   Weighted simple graphs, perfect matchings, maximum-weight perfect matchings, input and output encodings
-- statement:
--   Let $G=(V,E)$ be a simple graph on the vertex set $V=\{0,\dots,n-1\}$ with $m=|E|$ edges, and let $w:E\to\mathbb Z$ be integer edge weights.
--
--   A **matching** is a set of edges no two of which share an endpoint. It is **perfect** if every vertex lies in exactly one matched edge. The weight of $M$ is $w(M)=\sum_{e\in M}w(e)$. A **maximum-weight perfect matching** is a perfect matching $M$ with $w(M')\le w(M)$ for every perfect matching $M'$ of $G$ (Appendix C, p. 35).
--
--   The algorithms of §§2–4 store a matching as the mate array $M[v]$ of Figure 4, with $M[v]=\bot$ for a free vertex. The module defines when a mate array is a matching (it is symmetric and matched pairs are edges) and its edge set $\{uv: M[u]=v\}$.
--
--   The input of Theorem 4 is the list $[n,m,u_1,v_1,w(u_1v_1),\dots,u_m,v_m,w(u_mv_m)]$, which lists every edge of $G$ exactly once, in any order and either orientation. The output is the mate list $[M[0],\dots,M[n-1]]$. An output list *encodes a maximum-weight perfect matching* if it has length $n$ and its decoded mate array is a perfect matching of $G$ of maximum weight.
--
--   These are the objects of the main theorem. The fixed output decoder keeps the decoding of the answer from being chosen together with the algorithm.
-- source:
--   Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026), §1, p. 2; Appendix C, p. 35; Figure 4, p. 8; Theorem 4, p. 28; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/842.pdf

import Mathlib

/-!
# Weighted graphs, perfect matchings, the input encoding and the output decoder

Kourosh Mirsohi, Sandy Irani, Michael Goodrich, STOC 2027 submission #842 (October 2026),
§1 (p. 2), Appendix C (p. 35), Figure 4 (p. 8), Theorem 4 (p. 28).

* Graph `G = (V, E)`: a simple graph on `Fin n` (`n = |V|`), `m = |E|` its number of edges;
  integer edge weights `w : Sym2 (Fin n) → ℤ` (only the values on edges matter).
* A **matching** is a set of edges no two of which share an endpoint; it is **perfect** if every
  vertex is incident to exactly one matched edge; `w(M) = Σ_{e ∈ M} w(e)`; a **maximum-weight
  perfect matching** is a perfect matching of maximum weight among all perfect matchings (App. C).
* The algorithms of §§2–4 store the matching as the mate array `M[v]` of Figure 4 (`M[v] = ⊥` for
  a free vertex): `Mate n = Fin n → Option (Fin n)`.

**Formalization Note.** The input of Theorem 4 is the list
`[n, m, u₁, v₁, w(u₁v₁), …, u_m, v_m, w(u_m v_m)]` (0-based vertex indices) listing every edge once,
in any order and either orientation; the output is the mate list `[M[0], …, M[n−1]]`, decoded by
`mateOfList`. Both encodings are fixed here once, so the output cannot be read by a decoder chosen
together with the algorithm.
-/

namespace QuantumScalingMWPM.QLiquidationist

open scoped Classical

variable {n : ℕ}

/-- A finite edge set `M` is a matching of `G`: it consists of edges of `G`, no two sharing an
endpoint. -/
def IsMatchingSet (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ e → v ∉ f

/-- A perfect matching of `G`: edges of `G` such that every vertex lies in exactly one of them. -/
def IsPerfectMatchingSet (G : SimpleGraph (Fin n)) (M : Finset (Sym2 (Fin n))) : Prop :=
  (∀ e ∈ M, e ∈ G.edgeSet) ∧ ∀ v : Fin n, ∃! e, e ∈ M ∧ v ∈ e

/-- The weight `w(M) = Σ_{e ∈ M} w(e)`. -/
def weight (w : Sym2 (Fin n) → ℤ) (M : Finset (Sym2 (Fin n))) : ℤ := ∑ e ∈ M, w e

/-- `M` is a maximum-weight perfect matching of `(G, w)`. -/
def IsMWPM (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (M : Finset (Sym2 (Fin n))) : Prop :=
  IsPerfectMatchingSet G M ∧ ∀ M', IsPerfectMatchingSet G M' → weight w M' ≤ weight w M

/-- The mate array of Figure 4: `M[v] = some u` if `v` is matched to `u`, `none` (`⊥`) if free. -/
abbrev Mate (n : ℕ) := Fin n → Option (Fin n)

/-- A mate array encodes a matching of `G`: it is symmetric and matched pairs are edges. -/
def IsMatching (G : SimpleGraph (Fin n)) (M : Mate n) : Prop :=
  ∀ u v, M u = some v → M v = some u ∧ G.Adj u v

/-- The edge set `{uv : M[u] = v}` of a mate array. -/
def edgesOf (M : Mate n) : Finset (Sym2 (Fin n)) :=
  Finset.univ.filter fun e => ∃ u v, e = s(u, v) ∧ M u = some v

/-- Decode a list of integers as a mate array: entry `v` is read as vertex `M[v]` when it lies in
`{0, …, n−1}`, and as `⊥` otherwise. -/
def mateOfList (o : List ℤ) : Mate n := fun v =>
  let z := o.getD v.val (-1)
  if h : 0 ≤ z ∧ z.toNat < n then some ⟨z.toNat, h.2⟩ else none

/-- The output list `o` encodes a maximum-weight perfect matching of `(G, w)`: it has length `n`,
its decoded mate array is a matching of `G` covering every vertex, and its edge set is a
maximum-weight perfect matching. -/
def DecodesMWPM (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (o : List ℤ) : Prop :=
  o.length = n ∧ IsMatching G (mateOfList (n := n) o) ∧ (∀ v, (mateOfList (n := n) o v).isSome) ∧
    IsMWPM G w (edgesOf (mateOfList (n := n) o))

/-- `I` is an input encoding of `(G, w)`: `I = [n, m, u₁, v₁, w(u₁v₁), …]` where the pairs
`(uᵢ, vᵢ)` list every edge of `G` exactly once (any order, either orientation). -/
def IsInputEncoding (G : SimpleGraph (Fin n)) (w : Sym2 (Fin n) → ℤ) (I : List ℤ) : Prop :=
  ∃ es : List (Fin n × Fin n),
    (es.map fun p => s(p.1, p.2)).Nodup ∧ (∀ p ∈ es, G.Adj p.1 p.2) ∧
    (∀ e ∈ G.edgeSet, ∃ p ∈ es, s(p.1, p.2) = e) ∧
    I = (n : ℤ) :: (es.length : ℤ) ::
      es.flatMap fun p => [((p.1 : ℕ) : ℤ), ((p.2 : ℕ) : ℤ), w s(p.1, p.2)]

/-! ### Sanity checks -/

/-- The empty matching is the (maximum-weight) perfect matching of the empty graph. -/
example (w : Sym2 (Fin 0) → ℤ) : IsMWPM (⊥ : SimpleGraph (Fin 0)) w ∅ := by
  refine ⟨⟨by simp, fun v => v.elim0⟩, fun M' _ => ?_⟩
  have : M' = ∅ := by
    ext e; induction e using Sym2.ind with | h a _ => exact a.elim0
  simp [this, weight]

/-- On two vertices joined by an edge, the output `[1, 0]` decodes to the mate array `0 ↔ 1`. -/
example : mateOfList (n := 2) [1, 0] 0 = some 1 ∧ mateOfList (n := 2) [1, 0] 1 = some 0 := by
  decide

end QuantumScalingMWPM.QLiquidationist


