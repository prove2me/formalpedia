-- Prove2me | Definitions.Def_QAlgorithms_Defs_AdaptiveQuery
-- name    : QAlgorithms_Defs_AdaptiveQuery
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:42:52.399024+00:00
-- url     : https://prove2.me/theorems/08848af9-ff48-4eeb-ba67-10eca989330f
-- title:
--   Adaptive quantum query algorithms with intermediate measurements (shared definition layer)
-- statement:
--   # Adaptive quantum query algorithms with intermediate measurements (shared definition layer)
--
--   A. Ambainis, K. Balodis, A. Belovs, T. Lee, M. Santha, J. Smotrovs, *Separations in query
--   complexity based on pointer functions* (arXiv:1410.0932v2), cited "ABBLSS p.N" (PDF pages),
--   §2.2 and Appendix C.
--
--   An adaptive algorithm runs a frozen `QueryAlg` (input-independent unitaries, XOR oracle
--   `|i, b⟩ ↦ |i, b ⊕ x_i⟩`), measures its whole register in the computational basis, and chooses the
--   next round (or halts with an output) classically from the outcome. The tree is data fixed before
--   the input (trap Q2).
--   -/
--
--   namespace QAlgorithms
--
--   /-- ABBLSS §2.2 (p.5) and Appendix C, Algorithm 28 (p.31): an adaptive quantum query algorithm
--   with output type `α` on inputs `x : ι → Bool`: either halt with output `a`, or run a `T`-query
--   `QueryAlg` with workspace `Fin w` against the XOR oracle of `x`, measure the full register, and
--   continue with `next z` on outcome `z`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\AdaptiveQuery.lean

import Definitions.Def_QAlgorithms_Defs_QAOA
/-!
# Adaptive quantum query algorithms with intermediate measurements (shared definition layer)

A. Ambainis, K. Balodis, A. Belovs, T. Lee, M. Santha, J. Smotrovs, *Separations in query
complexity based on pointer functions* (arXiv:1410.0932v2), cited "ABBLSS p.N" (PDF pages),
§2.2 and Appendix C.

An adaptive algorithm runs a frozen `QueryAlg` (input-independent unitaries, XOR oracle
`|i, b⟩ ↦ |i, b ⊕ x_i⟩`), measures its whole register in the computational basis, and chooses the
next round (or halts with an output) classically from the outcome. The tree is data fixed before
the input (trap Q2).
-/

namespace QAlgorithms

/-- ABBLSS §2.2 (p.5) and Appendix C, Algorithm 28 (p.31): an adaptive quantum query algorithm
with output type `α` on inputs `x : ι → Bool`: either halt with output `a`, or run a `T`-query
`QueryAlg` with workspace `Fin w` against the XOR oracle of `x`, measure the full register, and
continue with `next z` on outcome `z`. -/
inductive AdaptiveQueryAlg (ι : Type) [Fintype ι] [DecidableEq ι] (α : Type) where
  | halt (a : α)
  | round (T w : ℕ) (A : QueryAlg ι Bool (Fin w) T)
      (next : (ι × Bool) × Fin w → AdaptiveQueryAlg ι α)

namespace AdaptiveQueryAlg

variable {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type}

/-- ABBLSS §2.2 (p.5): the probability that the algorithm outputs `a` on input `x`. -/
noncomputable def outProb [DecidableEq α] : AdaptiveQueryAlg ι α → (ι → Bool) → α → ℝ
  | halt b, _, a => if a = b then 1 else 0
  | round _ _ A next, x, a =>
      ∑ z, prob (A.finalState (xorOracle x)) z * (next z).outProb x a

/-- ABBLSS Theorem 10 (p.13) and Appendix C (p.32): the expected total number of oracle queries
on input `x`. -/
noncomputable def expQueries : AdaptiveQueryAlg ι α → (ι → Bool) → ℝ
  | halt _, _ => 0
  | round T _ A next, x =>
      (T : ℝ) + ∑ z, prob (A.finalState (xorOracle x)) z * (next z).expQueries x

/-- ABBLSS Theorem 10 (p.13): the largest total number of queries over the measurement
transcripts of positive probability on input `x`. -/
noncomputable def maxQueries : AdaptiveQueryAlg ι α → (ι → Bool) → ℕ
  | halt _, _ => 0
  | round T _ A next, x =>
      open Classical in
      T + (Finset.univ.filter fun z => 0 < prob (A.finalState (xorOracle x)) z).sup
        fun z => (next z).maxQueries x

end AdaptiveQueryAlg

/-- ABBLSS Theorem 10 (p.13): the least marked index of `x` (0-based: the source's `d`-th element
is index `d − 1`), `none` if no index is marked. -/
def firstMarked {N : ℕ} (x : Fin N → Bool) : Option (Fin N) :=
  (List.finRange N).find? fun i => x i

/-! ### Sanity tests -/

example {ι : Type} [Fintype ι] [DecidableEq ι] (x : ι → Bool) :
    (AdaptiveQueryAlg.halt true : AdaptiveQueryAlg ι Bool).outProb x true = 1 ∧
      (AdaptiveQueryAlg.halt true : AdaptiveQueryAlg ι Bool).expQueries x = 0 := by
  simp [AdaptiveQueryAlg.outProb, AdaptiveQueryAlg.expQueries]

example {ι : Type} [Fintype ι] [DecidableEq ι] (A : QueryAlg ι Bool (Fin 1) 0) (x y : ι → Bool) :
    (AdaptiveQueryAlg.round 0 1 A fun _ => .halt true : AdaptiveQueryAlg ι Bool).outProb x true =
      (AdaptiveQueryAlg.round 0 1 A fun _ => .halt true : AdaptiveQueryAlg ι Bool).outProb y true := by
  simp only [AdaptiveQueryAlg.outProb]
  rfl

example : firstMarked (![false, true, true] : Fin 3 → Bool) = some 1 := by decide

example : firstMarked (![false, false] : Fin 2 → Bool) = none := by decide

end QAlgorithms


