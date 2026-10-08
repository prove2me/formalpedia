-- Prove2me | Definitions.Def_SampleComplexityRL_Exploration_Empirical
-- name    : SampleComplexityRL_Exploration_Empirical
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T04:00:18.583312+00:00
-- url     : https://prove2.me/theorems/157701c5-b924-46be-ba85-8110b5ed2a90
-- title:
--   The empirical distribution of m samples from a set of N elements (Lemma 8.5.5)
-- statement:
--   For $m$ samples $\omega_1,\dots,\omega_m$ from a set of $N$ elements $\{1,\dots,N\}$, the empirical distribution is
--   $$
--   \hat p(i)=\frac{\#\{j:\omega_j=i\}}{m},
--   $$
--   the fraction of samples equal to $i$. It is the estimator of a distribution $p$ whose $\ell_1$ accuracy Lemma 8.5.5 controls, and it is how the $R_{max}$ algorithm estimates a transition row $P(\cdot\mid s,a)$ from observed transitions.
--
--   **Formalization Note** The elements are `Fin N`, the samples a function `Fin m → Fin N`. For $m=0$ the value is $0$ (division by zero); the hypotheses of Lemma 8.5.5 force $m\ge1$.
-- source:
--   Kakade, On the Sample Complexity of Reinforcement Learning, PhD thesis, University College London, 2003, p. 112, Lemma 8.5.5

import Mathlib

namespace SampleComplexityRL.Exploration

/-- The empirical distribution of `m` samples `ω : Fin m → Fin N` from a set of `N` elements
(Kakade 2003, Lemma 8.5.5, p. 112): `p̂(i) = (# of i's observed) / m`. -/
noncomputable def empiricalDist {N m : ℕ} (ω : Fin m → Fin N) (i : Fin N) : ℝ :=
  ((Finset.univ.filter (fun j => ω j = i)).card : ℝ) / (m : ℝ)

end SampleComplexityRL.Exploration


