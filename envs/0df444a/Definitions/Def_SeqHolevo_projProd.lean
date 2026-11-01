-- Prove2me | Definitions.Def_SeqHolevo_projProd
-- name    : SeqHolevo_projProd
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:57:59.437932+00:00
-- url     : https://prove2.me/theorems/47a76ca2-db63-49e6-b347-b5db45833b04
-- title:
--   Ordered product $\Pi_N\cdots\Pi_1$
-- statement:
--   For a sequence of projectors $\Pi_1,\Pi_2,\dots$, the ordered product
--
--   $$\Pi_N\cdots\Pi_1,$$
--
--   with the empty product equal to $I$. It appears in Sen's non-commutative union bound.
--
--   **Formalization Note** Lean's sequence is 0-based: the paper's $\Pi_i$ is Lean's `P (i-1)`.
-- source:
--   Wilde–Guha–Tan–Lloyd, Explicit capacity-achieving receivers for optical communication and quantum reading, arXiv:1202.0518v2, Appendix B, p.7 (Sen's bound)

import Mathlib
import Definitions.Def_SeqHolevo_idArr
import Definitions.Def_SeqHolevo_arrMul

namespace SeqHolevo

/-- Wilde–Guha–Tan–Lloyd, *Explicit capacity-achieving receivers for optical communication and quantum reading*, arXiv:1202.0518v2, Appendix B, p.7 (PDF page), Sen's non-commutative union bound: the ordered product
`Π_N ⋯ Π_1` of a sequence of projectors. With Lean's 0-based family `Π 0, Π 1, …`,
`projProd Π N = Π (N−1) ⋯ Π 0` (the empty product is `I`).

**Formalization Note.** Products are coefficientwise (`arrMul`); the paper's `Π_i` is Lean's
`Π (i−1)`. -/
noncomputable def projProd {J : Type} (P : ℕ → Matrix J J ℂ) : ℕ → Matrix J J ℂ
  | 0 => idArr J
  | k + 1 => arrMul (P k) (projProd P k)

end SeqHolevo


