-- Prove2me | Definitions.Def_ChapterLogPartitionConvex
-- name    : ChapterLogPartitionConvex
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-10-06T07:20:29.792718+00:00
-- url     : https://prove2.me/theorems/06ee01d5-ebd3-4b56-86af-a84e6cc42803
-- title:
--   Chapter LogPartitionConvex
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (source chapter `BookProof/ChapterLogPartitionConvex.lean`): generated def bundle for ChapterLogPartitionConvex. See BookProof/ChapterLogPartitionConvex.lean for full context.
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterLogPartitionConvex.lean

import Definitions.Def_ChapterSoftmaxDivergence
import Definitions.Def_ChapterAttentionEntropy
import Definitions.Def_ChapterSoftmaxSharpness
import Mathlib

/-!
# Chapter "The Coherent State of Attention" — convexity of the free energy

The log-partition function `log Z(β) = log ∑ⱼ exp (β sⱼ)` of an attention head is
the generating function of the attention statistics: its first derivative is the
mean score and its second derivative is the score variance
(`ChapterSoftmaxFluctuation`).  Because the variance is nonnegative, `log Z` is a
**convex** function of the inverse temperature, and strictly convex as soon as two
alignment scores differ.

* `hasDerivAt_deriv_logPartition` — the second derivative of `log Z` is `Var_β(s)`;
* `convexOn_logPartition` — **the headline**: `β ↦ log Z(β)` is convex on `ℝ`;
* `strictConvexOn_logPartition` — strict convexity when two scores differ;
* `logPartition_isGreatest` — the variational (Legendre) description: `log Z(β)`
  is the *largest* value of `β⟨s⟩_p + H(p)` over probability vectors `p`, attained
  at the Softmax distribution.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/
namespace BookProof.ChapterLogPartitionConvex

end BookProof.ChapterLogPartitionConvex


