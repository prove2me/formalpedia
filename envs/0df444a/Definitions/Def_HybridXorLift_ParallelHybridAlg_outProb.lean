-- Prove2me | Definitions.Def_HybridXorLift_ParallelHybridAlg_outProb
-- name    : HybridXorLift_ParallelHybridAlg_outProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:39.506201+00:00
-- url     : https://prove2.me/theorems/f01f375f-61fe-4426-ac11-21cfab2cb2ed
-- title:
--   Output probability of a parallel hybrid algorithm
-- statement:
--   For a parallel hybrid algorithm $A$, an input $x$ and an output $a$, the **output probability** is defined recursively: a leaf with label $b$ gives $1$ if $b = a$ and $0$ otherwise; at an internal node with final state $|\psi_x\rangle = V O^{(k)}_x |\phi\rangle$,
--   $$
--   \Pr[A(x) = a] = \sum_y |\langle y|\psi_x\rangle|^2 \, \Pr[A_y(x) = a].
--   $$
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definitions 2.1–2.2, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_ParallelHybridAlg
import Definitions.Def_HybridXorLift_ParallelSub_finalState

namespace HybridXorLift

/-- The probability that a parallel hybrid algorithm outputs `a` on input `x` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd),
Definitions 2.1–2.2, p.9 (PDF p.11)): outcome `y` of a subroutine has probability
`|⟨y| V O_x |ϕ⟩|²` and selects the child `next y`. -/
noncomputable def ParallelHybridAlg.outProb {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type}
    [DecidableEq α] : ParallelHybridAlg ι α → (ι → Bool) → α → ℝ
  | .halt b, _, a => if b = a then 1 else 0
  | .round _ _ S next, x, a =>
      ∑ y, QAlgorithms.prob (S.finalState x) y * (next y).outProb x a

end HybridXorLift


