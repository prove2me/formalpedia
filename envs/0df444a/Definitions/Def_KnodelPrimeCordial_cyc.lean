-- Prove2me | Definitions.Def_KnodelPrimeCordial_cyc
-- name    : KnodelPrimeCordial_cyc
-- status  : Definition
-- author  : @iris
-- created : 2026-11-12T05:59:09.782198+00:00
-- url     : https://prove2.me/theorems/7c110b77-e99c-476a-b869-31f6fe19c51d
-- title:
--   The cyclic model of $W_{3,n}$ on $v_0,\dots,v_{n-1}$
-- statement:
--   For $n\ge 1$, let $G_n$ be the graph on the vertices $v_0,\dots,v_{n-1}$ (indices read modulo $n$) with edge set
--
--   $$
--   \{v_iv_{i+1}:0\le i\le n-1\}\ \cup\ \{v_{2i}v_{2i+5}:0\le i\le n/2-1\}.
--   $$
--
--   That is, the $n$-cycle $v_0v_1\cdots v_{n-1}v_0$ together with a chord from every even-indexed vertex $v_{2i}$ to $v_{2i+5}$. The paper states (p.3) that for even $n\ge 8$ this is the Knödel graph $W_{3,n}$ under the naming $v_{2j}=(1,j)$, $v_{2j-1}=(2,j)$; the labelings of the paper's proof are all written in terms of the indices $i$ of $v_i$.
--
--   **Formalization Note** Vertices are `Fin n`, and $i+1$, $i+5$ are reduced modulo $n$. An explicit $a\ne b$ clause removes loops, which can only arise for $n\le 5$, outside the paper's range. The identification with $W_{3,n}$ is a milestone, not part of this definition.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), §1, p.3 (PDF p.3), display for V(W3,n) and E(W3,n)

import Mathlib

namespace KnodelPrimeCordial

/-- **The cyclic model of `W_{3,n}`** (Haque, Khanam, Shahriar, *Prime cordial labeling of
Knödel graph*, manuscript (2026), §1, p.3, display):
`V(W3,n) = {vi : 0 ≤ i ≤ n − 1}`,
`E(W3,n) = {vivi+1 : 0 ≤ i ≤ n − 1} ∪ {v2iv2i+5 : 0 ≤ i ≤ n/2 − 1}`,
"the vertex labels are read modulo n".

`cyc n` is the simple graph on `Fin n` (the indices `i` of `v_i`) whose edges are
`{i, i + 1 mod n}` for every `i` and `{i, i + 5 mod n}` for every even `i`.

**Formalization Note** Indices are read modulo `n`, as the paper says. The definition is
written for all `n`; the paper uses it for even `n ≥ 8`, where no pair `{i, i+1}` or `{i, i+5}`
degenerates to a loop. The `a ≠ b` clause only removes loops (relevant for `n ≤ 5`). That
`cyc n` is `W_{3,n}` under `v_{2j} = (1, j)`, `v_{2j−1} = (2, j)` is a milestone, not part of
this definition. -/
def cyc (n : ℕ) : SimpleGraph (Fin n) where
  Adj a b := a ≠ b ∧
    (b.val = (a.val + 1) % n ∨ a.val = (b.val + 1) % n ∨
      (Even a.val ∧ b.val = (a.val + 5) % n) ∨ (Even b.val ∧ a.val = (b.val + 5) % n))
  symm := ⟨fun a b h => by
    obtain ⟨hne, h | h | h | h⟩ := h
    · exact ⟨hne.symm, Or.inr (Or.inl h)⟩
    · exact ⟨hne.symm, Or.inl h⟩
    · exact ⟨hne.symm, Or.inr (Or.inr (Or.inr h))⟩
    · exact ⟨hne.symm, Or.inr (Or.inr (Or.inl h))⟩⟩
  loopless := ⟨fun a h => h.1 rfl⟩

instance (n : ℕ) : DecidableRel (cyc n).Adj := fun a b => by
  unfold cyc
  infer_instance

end KnodelPrimeCordial


