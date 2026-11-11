-- Prove2me | Definitions.Def_QNoiseStab_coordNoise
-- name    : QNoiseStab_coordNoise
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:20:41.958185+00:00
-- url     : https://prove2.me/theorems/74a80ef7-963e-42c9-93d1-45e8722468b9
-- title:
--   Law of the single-coordinate noise $N_p(a)$: $\Pr[N_p(a)=b]=p/|X|+(1-p)[a=b]$
-- statement:
--   Let $X$ be a finite set and $p\in\mathbb R$. The single-coordinate noise $N_p(a)$ of a symbol $a\in X$ is the two-stage process: with probability $p$ replace $a$ by a uniformly random $b\in X$, and with probability $1-p$ return $a$. Its law is
--
--   $$
--   \Pr[N_p(a)=b]=\frac{p}{|X|}+(1-p)\,\delta_{a,b},
--   $$
--
--   where $\delta_{a,b}=1$ iff $a=b$. The uniform resample may return $a$ itself.
--
--   This is the building block of the restricted noise $N_p^A$ on $X^n$.
--
--   **Formalization Note** The random variable is represented by its law. The formula is defined for every real $p$; it is a probability distribution for $p\in[0,1]$.
-- source:
--   Beame–Holman–Kornerup, A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, p.11 (definition of N_p(x_i))

import Mathlib

namespace QNoiseStab

/-- The law of the single-coordinate noise `N_p(a)` (Beame–Holman–Kornerup, *A Noise Operator Approach to Quantum Query Complexity and Time-Space Tradeoff Lower Bounds*, arXiv:2609.40334 (version of 2026-11-02, sha256 814fe20e…), §3, p.11: "the random variable Np(xi)
on [m] is given by a two-stage process: with probability p, replace xi with a random y ∼ U[m] and
with probability 1 − p return xi"): `coordNoise p a b = Pr[N_p(a) = b] = p/|X| + (1 − p)·[a = b]`.
With probability `p` the value is a uniform draw from `X`, which equals `b` with probability
`1/|X|` (it may equal `a`); with probability `1 − p` the value is `a` itself.

**Formalization Note** The random variable is represented by its law (a function of `a, b`).
It is a probability law for `p ∈ [0, 1]`; the formula is defined for every real `p`. -/
noncomputable def coordNoise {X : Type} [Fintype X] [DecidableEq X] (p : ℝ) (a b : X) : ℝ :=
  p * (Fintype.card X : ℝ)⁻¹ + (1 - p) * (if a = b then 1 else 0)

end QNoiseStab


