-- Prove2me | Definitions.Def_QNoiseStab_noiseProb
-- name    : QNoiseStab_noiseProb
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:22:45.011396+00:00
-- url     : https://prove2.me/theorems/a17d116f-9626-4d5b-a00e-bede79b57632
-- title:
--   Noise stability $\Pr[N_p^A(x)\in E]$ of an event
-- statement:
--   Let $X$ be a finite set, $A\subseteq[n]$, $p\in\mathbb R$, $x\in X^n$ and $E\subseteq X^n$. The probability that the restricted noise moves $x$ into $E$ is
--
--   $$
--   \Pr\bigl[N_p^A(x)\in E\bigr]=\sum_{y\in E}\Pr\bigl[N_p^A(x)=y\bigr].
--   $$
--
--   These are the quantities $\max_{x\in E}\Pr[N_p^A(x)\in E]$ in Theorems 3.4 and 3.5: an event that is unstable under noise cannot be produced with high probability by few queries.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.4, p.12, and Theorem 3.5, p.13 (Pr[N_p^A(x) ∈ E])

import Mathlib
import Definitions.Def_QNoiseStab_noiseKernel

namespace QNoiseStab

/-- The probability `Pr[N_p^A(x) ∈ E]` that the restricted noise moves `x` into the event
`E ⊆ Xⁿ` (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), Theorem 3.4 and Theorem 3.5, pp.12–13): the sum of `noiseKernel p A x y` over
`y ∈ E`. -/
noncomputable def noiseProb {X : Type} [Fintype X] [DecidableEq X] {n : ℕ} (p : ℝ)
    (A : Finset (Fin n)) (x : Fin n → X) (E : Finset (Fin n → X)) : ℝ :=
  ∑ y ∈ E, noiseKernel p A x y

end QNoiseStab


