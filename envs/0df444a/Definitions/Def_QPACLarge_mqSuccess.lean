-- Prove2me | Definitions.Def_QPACLarge_mqSuccess
-- name    : QPACLarge_mqSuccess
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:05:25.828434+00:00
-- url     : https://prove2.me/theorems/9c0f4ef0-a4df-43c7-8076-914430706ec9
-- title:
--   Success probability of a uniform randomized polynomial-time membership-query learner
-- statement:
--   A uniform randomized membership-query learner is given by a next-step function $g$, a round bound $p(n)$ and a number $\mathrm{rb}(n)$ of random bits. In each round $g$ sees $n$ (in unary), the random bits and the query history and either asks a membership query $x$, receiving $f(x)$, or halts with an output string. $\Pr_B[P]$ is the fraction of random strings $r \in \{0,1\}^{\mathrm{rb}(n)}$ on which the run halts within $p(n)$ rounds with the code of a Boolean circuit whose function $h$ satisfies $P$.
--
--   The learner is **polynomial time** when $g$ is polynomial-time computable and $p, \mathrm{rb}$ are polynomials; these are the learners of the conditional clause of Theorem 1.5.
--
--   **Formalization Note** This is the published `mqRun` model with the published decoding `OutputsCircuitWith`; running out of rounds, or an output that is not a circuit code, counts as failure.
-- source:
--   Oliveira, Unconditional Quantum PAC Learning Advantage in the Large Error Regime, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.2, p.15; Theorem 1.5, p.7; Section 5.3, p.37

import Mathlib
import Definitions.Def_QAlgorithms_Defs_LearningSeparation

namespace QPACLarge

open QAlgorithms QAlgorithms.Complexity QAlgorithms.Learning

/-- **Success probability of a uniform randomized membership-query learner.**
Oliveira, arXiv:2610.23268 (held file sha256 e749e7c9…), Section 2.2, p.15, and Theorem 1.5, p.7
("randomized membership-query polynomial-time learner `B`").

The learner is the published `mqRun` model: a next-step function `g` that sees `n` (in unary), the
random bits `r` and the query history, and either asks a membership query or halts with an output
string, for at most `p(n)` rounds, with `rb(n)` uniformly random bits. `mqSuccess g p rb n f P` is
the fraction of random strings on which the run halts with the code of a well-formed Boolean
circuit whose function satisfies `P`.

**Formalization Note.** Running out of rounds, or an output that is not a circuit code, counts as
failure. A learner is "polynomial time" when `g` is polynomial-time computable and `p`, `rb` are
polynomials. -/
noncomputable def mqSuccess (g : Str → Str) (p rb : Polynomial ℕ) (n : ℕ) (f : Qubits n → Bool)
    (P : (Qubits n → Bool) → Prop) : ℝ :=
  open Classical in
  ((2 : ℝ) ^ rb.eval n)⁻¹ *
    ((Finset.univ.filter fun r : Fin (rb.eval n) → Bool =>
      ∃ s, mqRun g n (List.ofFn r) f (p.eval n) [] = some s ∧ OutputsCircuitWith s P).card : ℝ)

end QPACLarge


