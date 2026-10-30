-- Prove2me | Definitions.Def_FMMM_TSM_unifProb
-- name    : FMMM_TSM_unifProb
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:14:22.608206+00:00
-- url     : https://prove2.me/theorems/d57307ec-53af-48cd-a8d1-ebfb606e4c8e
-- title:
--   Probability under $n$ i.i.d. uniform draws
-- statement:
--   Let $\Omega$ be a finite set and $n \in \mathbb N$. For a property $P$ of sequences $\omega = (\omega_0, \dots, \omega_{n-1}) \in \Omega^n$, the probability that $n$ independent draws, each uniform on $\Omega$, satisfy $P$ is
--
--   $$\Pr[P] = \frac{\#\{\omega \in \Omega^n : P(\omega)\}}{|\Omega|^n}.$$
--
--   This is the probability model of the paper: impressions arrive as $n$ i.i.d. draws, and in the balls-in-bins facts $n$ balls are thrown independently and uniformly into $n$ bins. Every probability in this mission is this counting ratio.
--
--   **Formalization Note** Draws are indexed $0, \dots, n-1$ (`Fin n`). If $\Omega$ is empty and $n > 0$ the value is $0$; no statement uses that case.
-- source:
--   Feldman, Mehta, Mirrokni, Muthukrishnan, Online Stochastic Matching: Beating 1-1/e, arXiv:0905.4100v1, §2, p. 3 and §2.1, p. 4 (i.i.d. draws; balls into bins)

import Mathlib

namespace FMMM.TSM

/-- **Probability under `n` i.i.d. uniform draws from a finite set.**
Feldman, Mehta, Mirrokni, Muthukrishnan, *Online Stochastic Matching: Beating 1-1/e*,
arXiv:0905.4100v1, §2, p. 3 ("n i.i.d. draws of impressions i ∼ D arrive") and §2.1, p. 4
("n balls are thrown into n bins, i.i.d. with uniform probability over the bins").

`unifProb Ω n P` is the probability that the sequence `ω : Fin n → Ω` of `n` independent uniform
draws from the finite set `Ω` satisfies `P`, i.e. `#{ω : P ω} / |Ω|ⁿ`.

**Formalization Note.** Every probability of the mission is this counting ratio on the finite
sample space `Ω^n`; draws are indexed `0, …, n − 1`. When `Ω` is empty and `n > 0` the sample
space is empty and the value is `0` (no item uses that case). -/
noncomputable def unifProb (Ω : Type) [Fintype Ω] (n : ℕ) (P : (Fin n → Ω) → Prop) : ℝ := by
  classical
  exact ((Finset.univ.filter P).card : ℝ) / (Fintype.card Ω : ℝ) ^ n

end FMMM.TSM


