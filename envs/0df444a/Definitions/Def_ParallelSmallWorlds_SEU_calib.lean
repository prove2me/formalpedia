-- Prove2me | Definitions.Def_ParallelSmallWorlds_SEU_calib
-- name    : ParallelSmallWorlds_SEU_calib
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:52:27.696607+00:00
-- url     : https://prove2.me/theorems/6dfe2e5c-9c9f-417d-b18b-8e5da20d8402
-- title:
--   Calibrated probability $P_{\Theta_w}(R)=\pi_R$
-- statement:
--   For an event $R$ of a small world, the **calibrated probability** of $R$ is
--
--   $$P_{\Theta}(R)=\inf\{\pi\in[0,1] : [0,\pi]\succeq_\Theta R\}.$$
--
--   Under Axioms PSW1–PSW6 the set on the right contains $1$, and its least element is the unique $\pi_R\in[0,1]$ with $R\sim_\Theta[0,\pi_R]$: the decision maker holds $R$ exactly as likely as the pointer of the probability wheel stopping in an arc of length $\pi_R$. This is the subjective probability the paper constructs, and the one that Theorem 1, the act distributions (5) and Axiom PSW16 refer to. Because all worlds use the same reference experiment, these probabilities are on a common scale across worlds.
--
--   **Formalization Note** `calib` is defined for every set; when the set is empty, which the axioms exclude, the real infimum is $0$.
-- source:
--   French, Axiomatising the Bayesian Paradigm in Parallel Small Worlds, author's accepted manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eqs. (9)–(10), p.43 (PDF p.44)

import Mathlib
import Definitions.Def_ParallelSmallWorlds_SEU_SmallWorld

namespace ParallelSmallWorlds.SEU

/-- **The calibrated probability `PΘw(R) = πR`.**
S. French, *Axiomatising the Bayesian Paradigm in Parallel Small Worlds*, author's accepted
manuscript OPRE-2018-05-258 (WRAP 118263), proof of Lemma 1(a), eqs. (9)–(10), p.43 (PDF p.44):
"Hence ∃πR ∈ [0,1] such that R ∼Θw [0,πR]. … Define PΘw(R) = πR, ∀R ∈ Qw."

`calib W R` is the infimum of `H = {π ∈ [0,1] | [0,π] ⪰Θw R}`, the set (9) of the proof.

**Formalization Note.** This is the probability the paper constructs, not an arbitrary
probability agreeing with `⪰Θw` (reading R1); Theorem 1, the act distribution (5) and Axiom PSW16
all refer to it. Under Axioms PSW1–PSW6 the set `H` contains `1` and its least element is the
unique `πR` with `R ∼Θw [0,πR]`. On inputs where `H` is empty (impossible under the axioms) the
real `sInf` returns `0`. -/
noncomputable def calib {Θ C : Type*} (W : SmallWorld Θ C) (R : Set Θ) : ℝ :=
  sInf {π : ℝ | π ∈ Set.Icc (0 : ℝ) 1 ∧ W.lik (Sum.inr (Set.Icc 0 π)) (Sum.inl R)}

end ParallelSmallWorlds.SEU


