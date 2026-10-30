-- Prove2me | Definitions.Def_SpecExtremalConj_part
-- name    : SpecExtremalConj_part
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:07:50.092704+00:00
-- url     : https://prove2.me/theorems/b528df0f-cde0-4d9f-a058-0f9adabb06b5
-- title:
--   Part $V_i$ of an $r$-partition
-- statement:
--   A partition of the vertex set $V$ into $r$ labelled parts $V(G)=V_1\cup\dots\cup V_r$ is encoded as a map $P:V\to\{1,\dots,r\}$; the **$i$-th part** is
--
--   $$V_i=P^{-1}(i)=\{v\in V : P(v)=i\}.$$
--
--   Parts are allowed to be empty in this definition. All partition statements of Section 3 are phrased through this map.
--
--   **Formalization Note** Labels are `Fin r`; Lean label $i$ is the paper's $i+1$.
-- source:
--   Wang, Kang, Xue, On a conjecture of spectral extremal problems, arXiv:2203.10831v1, §3, p. 4 ("a partition V(G) = V_1 ∪ … ∪ V_r")

import Mathlib
open Finset SimpleGraph

namespace SpecExtremalConj

/-- **Part V_i of an r-partition.** Wang, Kang, Xue, *On a conjecture of spectral extremal problems*, arXiv:2203.10831v1, §3, p. 4 (unnumbered): "a partition
V(G) = V_1 ∪ … ∪ V_r".

An r-partition of the vertex set is encoded as a map `P : V → Fin r`; `part P i` is the part
`V_i = P⁻¹(i)`.

**Formalization Note.** Parts may be empty in the definition (Lemma 3.3 proves they are not); Lean
index `i : Fin r` is the paper's `i + 1 ∈ [r]`. -/
def part {V : Type*} [Fintype V] {r : ℕ} (P : V → Fin r) (i : Fin r) : Finset V :=
  {v | P v = i}

end SpecExtremalConj


