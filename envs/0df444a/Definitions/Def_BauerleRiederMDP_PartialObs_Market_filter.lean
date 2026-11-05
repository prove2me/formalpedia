-- Prove2me | Definitions.Def_BauerleRiederMDP_PartialObs_Market_filter
-- name    : BauerleRiederMDP_PartialObs_Market_filter
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T07:02:03.17881+00:00
-- url     : https://prove2.me/theorems/5a9309b2-4542-4321-bb0c-c2f9ee8d66fb
-- title:
--   The filter $\mu_n(\cdot\mid h_n)$
-- statement:
--   The filter is the conditional law of the hidden state $Y_n$ given the observations up to time $n$. It is computed recursively from the observed relative risks $z_1,\dots,z_n$:
--   $$
--   \mu_0:=\rho,\qquad \mu_{n+1}:=\Phi\big(\mu_n,z_{n+1}\big),
--   $$
--   where $\Phi$ is the Bayes operator. The filter of the book is the one started at the prior, $\rho=Q_0$; it depends on the observable history $h_n=(x_0,a_0,z_1,x_1,\dots,z_n,x_n)$ only through $z_1,\dots,z_n$.
--
--   **Formalization Note** The return path is a 0-indexed vector $r$ with $r_k=z_{k+1}$.
-- source:
--   Bäuerle & Rieder (2011), eqs. (5.3)–(5.4), p.151 (PDF 164), disturbance form p.154–155 (PDF 167–168); Theorem 6.1.1 d), p.177 (PDF 190)

import Mathlib
import Definitions.Def_BauerleRiederMDP_PartialObs_Market_Phi

open MeasureTheory ProbabilityTheory
open scoped ENNReal Matrix

namespace BauerleRiederMDP.PartialObs

/-- **The filter `μ_n(·|h_n)`**, the conditional law of the hidden state `Y_n` given the
observations up to time `n`.
Bäuerle & Rieder (2011), eqs. (5.3)–(5.4), p.151 (PDF 164), in the disturbance form of p.154
(PDF 167): `μ_0 := Q_0`, `μ_{n+1}(·|h_n, a_n, z_{n+1}, x_{n+1}) := Φ(μ_n(·|h_n), z_{n+1})`, with
the Bayes operator `Φ(ρ, z)` of Chapter 6 (p.177, PDF 190), which depends on the history only
through the observed relative risks `z_1, …, z_n` (p.155: `μ_n` "does not depend on `x_n`").

`M.filter ρ n r` is `μ_n` started from the belief `μ_0 = ρ` along the observed return path
`r = (z_1, …, z_n)`; the book's filter is `M.filter M.Q0`.

**Formalization Note.** The path `r : Fin n → ℝ^d` is 0-indexed: `r k = z_{k+1}`. -/
noncomputable def Market.filter {EY : Type*} [MeasurableSpace EY] {d : ℕ} (M : Market EY d)
    (ρ : ProbabilityMeasure EY) : (n : ℕ) → (Fin n → Fin d → ℝ) → ProbabilityMeasure EY
  | 0, _ => ρ
  | n + 1, r => M.Phi (Market.filter M ρ n (Fin.init r)) (r (Fin.last n))

end BauerleRiederMDP.PartialObs


