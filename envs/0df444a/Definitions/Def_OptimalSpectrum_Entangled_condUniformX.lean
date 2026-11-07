-- Prove2me | Definitions.Def_OptimalSpectrum_Entangled_condUniformX
-- name    : OptimalSpectrum_Entangled_condUniformX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:41.522203+00:00
-- url     : https://prove2.me/theorems/d0f2bbdf-a39e-466a-8c8b-1b9d42369921
-- title:
--   Single-copy estimator $X=(d+1)|u\rangle\langle u|-I_d$
-- statement:
--   For an outcome $u$ of the conditioned uniform POVM,
--
--   $$X=\begin{cases}(d+1)\,|u\rangle\langle u|-I_d,& u\ne0\ (\text{retained copy}),\\ 0,& u=0\ (\text{discarded copy}).\end{cases}$$
--
--   Its mean is $\sigma$, and the unentangled moment estimates are symmetric polynomials in independent copies of $X$.
-- source:
--   Bakshi, Singh, Tan, Optimal spectrum estimation, arXiv:2609.30171, §7.1.1, p. 20 (PDF p. 22)

import Mathlib

open scoped Matrix

namespace OptimalSpectrum.Entangled

/-- **The matrix estimator `X` of one conditioned-uniform outcome.**
Bakshi, Singh, Tan, *Optimal spectrum estimation*, arXiv:2609.30171, §7.1.1, printed p. 20 (PDF p. 22): "Let |u⟩ ∈ C^d be the resulting unit vector, and set
X = (d + 1)|u⟩⟨u| − I_d. On a discarded copy, set X = 0."

With the encoding of `condUniformLaw` (the zero vector for a discarded copy), `condUniformX d u` is
`0` if `u = 0` and `(d+1)|u⟩⟨u| − I_d` otherwise. -/
noncomputable def condUniformX (d : ℕ) (u : EuclideanSpace ℂ (Fin d)) :
    Matrix (Fin d) (Fin d) ℂ :=
  if u = 0 then 0
  else ((d : ℂ) + 1) • Matrix.vecMulVec (WithLp.ofLp u) (star (WithLp.ofLp u)) - 1

end OptimalSpectrum.Entangled


