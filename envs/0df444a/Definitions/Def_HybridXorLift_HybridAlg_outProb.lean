-- Prove2me | Definitions.Def_HybridXorLift_HybridAlg_outProb
-- name    : HybridXorLift_HybridAlg_outProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:12:57.78034+00:00
-- url     : https://prove2.me/theorems/a99f3c1a-211d-45f3-907a-331e9c90f07c
-- title:
--   Output probability of a hybrid algorithm
-- statement:
--   For a hybrid algorithm $A$, an input $x \in \{0,1\}^\iota$ and an output value $a$, the **output probability** $\Pr[A(x) = a]$ is defined recursively: a leaf with label $b$ outputs $a$ with probability $1$ if $b = a$ and $0$ otherwise; at an internal node with final state $|\psi_x\rangle$,
--   $$
--   \Pr[A(x) = a] = \sum_{z} |\langle z|\psi_x\rangle|^2 \, \Pr[A_z(x) = a],
--   $$
--   where $z$ ranges over the computational basis of the node's register and $A_z$ is the child selected by outcome $z$.
--
--   This is the probability that the algorithm, run on $x$, ends at a leaf labelled $a$.
-- source:
--   Shen–Zhong, XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees, STOC 2027 submission (manuscript sha256 5818ffef…), Definition 2.1, p.9 (PDF p.11)

import Definitions.Def_HybridXorLift_HybridAlg

namespace HybridXorLift

/-- The probability that the hybrid algorithm outputs `a` on input `x` (Shen–Zhong, *XOR Lifting for One-Query Hybrid Algorithms and the Complexity of AND–OR Trees*, STOC 2027 submission manuscript (sha256 5818ffef…7c3bd), Definition 2.1,
p.9 (PDF p.11)): at a node the subroutine's final state
`U_T O_x ⋯ O_x U_0 |start⟩` is measured in the computational basis, outcome `z` has probability
`|⟨z|ψ⟩|²` (`QAlgorithms.prob`), and the run continues at the child `next z`; a leaf outputs its
label. The oracle is the controlled phase oracle (2.1). -/
noncomputable def HybridAlg.outProb {ι : Type} [Fintype ι] [DecidableEq ι] {α : Type}
    [DecidableEq α] : HybridAlg ι α → (ι → Bool) → α → ℝ
  | .halt b, _, a => if b = a then 1 else 0
  | .round _ _ A next, x, a =>
      ∑ z, QAlgorithms.prob (A.finalState (QAlgorithms.controlledPhaseOracle x)) z *
        (next z).outProb x a

end HybridXorLift


