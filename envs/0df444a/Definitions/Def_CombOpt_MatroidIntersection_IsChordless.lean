-- Prove2me | Definitions.Def_CombOpt_MatroidIntersection_IsChordless
-- name    : CombOpt_MatroidIntersection_IsChordless
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:06:58.838758+00:00
-- url     : https://prove2.me/theorems/f68f7608-6493-4ac1-b523-724626aca253
-- title:
--   Chordless node sequence
-- statement:
--   A **chord** of a dipath $P$ with node sequence $v_0,v_1,\dots,v_k$ is an arc of the form $v_iv_j$ with $i<j-1$. A dipath is **chordless** if it has no chord.
--
--   Chordless augmenting paths are what make the symmetric-difference update of the matroid intersection algorithm preserve independence; a shortest dipath is chordless.
--
--   **Formalization Note** Positions are $0$-based list indices, and $i<j-1$ is written $i+1<j$.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), §8.3, p. 291 (PDF p. 298)

import Mathlib

namespace CombOpt.MatroidIntersection

/-- **A chordless node sequence.**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), §8.3,
p. 291 (PDF p. 298): "A *chord* of a dipath P having node-sequence v₀, v₁, …, v_k is an arc of
the form v_i v_j where i < j − 1."

`IsChordless arc P` says that for the node sequence `P = [v₀, …, v_k]` there is no arc `v_i v_j`
with `i + 1 < j`.

**Formalization Note.** Positions are `0`-based list indices; `i + 1 < j` is the book's
`i < j − 1` without natural-number subtraction. -/
def IsChordless {V : Type*} (arc : V → V → Prop) (P : List V) : Prop :=
  ∀ (i j : ℕ) (hi : i < P.length) (hj : j < P.length), i + 1 < j → ¬ arc P[i] P[j]

end CombOpt.MatroidIntersection


