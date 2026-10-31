-- Prove2me | Definitions.Def_TransitoryQueue_Xn
-- name    : TransitoryQueue_Xn
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:02:31.401261+00:00
-- url     : https://prove2.me/theorems/ad144662-e85f-49b2-b705-4580ff936f51
-- title:
--   Nonstationary Gaussian process $X_n$ of Theorem 2.11
-- statement:
--   With $H_n$ and $E_n$ as above, a Brownian motion $B$, and the mean $\mu$ and standard deviation $\sigma$ of the service law,
--
--   $$X_n(t)=H_n(t)-\frac{c_nt}{\mu}+\sqrt n\,\frac{\sigma}{\mu}\,B_{E_n(t)}.$$
--
--   Its reflection $\phi(X_n)$ is the nonstationary reflected Brownian process that approximates the queue length in Theorem 2.11.
--
--   **Formalization Note** $B$ is evaluated at $E_n(t)\ge0$.
-- source:
--   Chakraborty and Honnappa, Strong Embeddings for Transitory Queueing Models, arXiv:1906.06740v1, Theorem 2.11, p.8

import Mathlib
import Definitions.Def_TransitoryQueue_Hn
import Definitions.Def_TransitoryQueue_En
open scoped NNReal

namespace TransitoryQueue

/-- The nonstationary Gaussian process of Theorem 2.11,
`X_n(t) = H_n(t) - c_n t/μ + √n (σ/μ) B_{E_n(t)}`, whose reflection approximates the queue
length. Chakraborty and Honnappa, *Strong Embeddings for Transitory Queueing Models*, arXiv:1906.06740v1, Theorem 2.11, p.8.

**Formalization Note** `H_n` is `Hn` (centred at `n p F_n(t)`) and `E_n` is `En`. `μ`, `σ` are the
mean and standard deviation of the service law. The Brownian motion `B` takes times in `ℝ≥0`;
`E_n(t) ≥ 0` for `t ≥ 0`, so `Real.toNNReal` does not truncate. -/
noncomputable def Xn {Ω : Type*} (F : ℕ → ℝ → ℝ) (G : ℝ → ℝ) (p μ σ c : ℝ) (n : ℕ)
    (Bbr : ℝ → Ω → ℝ) (Bh B : ℝ≥0 → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  Hn F G p n Bbr Bh t ω - c * t / μ + Real.sqrt n * (σ / μ) * B (En F G p μ c n t).toNNReal ω

end TransitoryQueue


