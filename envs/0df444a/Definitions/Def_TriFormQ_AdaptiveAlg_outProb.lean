-- Prove2me | Definitions.Def_TriFormQ_AdaptiveAlg_outProb
-- name    : TriFormQ_AdaptiveAlg_outProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T21:45:41.821793+00:00
-- url     : https://prove2.me/theorems/9b4fe7bf-cf4d-4c5d-8397-4fe98d7d963b
-- title:
--   Output probability of an adaptive quantum query algorithm
-- statement:
--   Let $A$ be an adaptive quantum query algorithm, $g:\iota\to\kappa$ an oracle function, and $P$ a property of outputs. The probability that $A$, run with the standard oracle $|i,b\rangle\mapsto|i,b+g(i)\rangle$, outputs a value satisfying $P$ is defined recursively: for a halting algorithm with output $a$ it is $1$ if $P(a)$ and $0$ otherwise; for a round with final state $\psi_g$ and continuation $\mathrm{next}$ it is
--
--   $$\Pr[A^g\in P]=\sum_{z}\ |\langle z|\psi_g\rangle|^2\ \Pr[\mathrm{next}(z)^g\in P].$$
--
--   Success probabilities of identification, verification and sampling algorithms in this mission are values of this quantity.
-- source:
--   Grigorescu–Juba–Wimmer–Xie, Optimal Quantum Query Bounds for Identifying Classes of 3-Tensors, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6)

import Definitions.Def_TriFormQ_AdaptiveAlg

namespace TriFormQ

/-- Grigorescu–Juba–Wimmer–Xie, *Optimal Quantum Query Bounds for Identifying Classes of
3-Tensors*, STOC 2027 submission (manuscript sha256 c56b0365…), Theorem 1, p.3 (PDF p.6): the
probability that the adaptive algorithm `A`, run with oracle access to `g`, outputs a value
satisfying `P` ("correctly identifies f … with probability at least 1 − δ").

**Formalization Note.** At a round the outcome `z` of the full computational-basis measurement
has probability `QAlgorithms.prob` of the round's final state, and the algorithm continues with
`next z`; the output probability is the sum over all transcripts. -/
noncomputable def AdaptiveAlg.outProb {ι κ α : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [AddCommGroup κ] (A : AdaptiveAlg ι κ α) (g : ι → κ) (P : α → Prop)
    [DecidablePred P] : ℝ :=
  match A with
  | .halt a => if P a then 1 else 0
  | .round _ _ Q next =>
      ∑ z, QAlgorithms.prob (Q.finalState (QAlgorithms.xorOracle g)) z * (next z).outProb g P

end TriFormQ


