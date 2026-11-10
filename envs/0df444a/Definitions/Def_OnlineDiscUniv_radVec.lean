-- Prove2me | Definitions.Def_OnlineDiscUniv_radVec
-- name    : OnlineDiscUniv_radVec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:12:10.111915+00:00
-- url     : https://prove2.me/theorems/935c6452-b8d5-4b64-8326-7558ad49c32d
-- title:
--   Fair Rademacher law and Rademacher vectors in $\{\pm1\}^M$
-- statement:
--   The **fair Rademacher law** is $\tfrac12(\delta_{-1}+\delta_{+1})$ on $\mathbb R$. A **Rademacher vector** $\eta\in\{\pm1\}^M$ has independent fair Rademacher coordinates; its law is the $M$-fold product.
--
--   The fair sign $S$ of Lemma 3.3 and the perturbations $\eta_k$ of (3.29) have these laws.
-- source:
--   Jo, Lee, Exact Universality of Online Discrepancy, arXiv:2610.00103 (artifact sha256 cb190f127dea2c038b4a22a4787862f82356a983593dfdc3dc3fe3c7c8264ad5), p.1 (PDF p.2); (3.29), p.9 (PDF p.10); Lemma 3.3, p.8 (PDF p.9)

import Mathlib

set_option autoImplicit false

open MeasureTheory

namespace OnlineDiscUniv

/-- The fair Rademacher law `½(δ_{−1} + δ_{+1})` on `ℝ` (Jo–Lee, arXiv:2610.00103, artifact
sha256 cb190f12…, p.1, PDF p.2, and (3.29), p.9, PDF p.10). -/
noncomputable def fairCoin : Measure ℝ :=
  (2 : ENNReal)⁻¹ • (Measure.dirac (-1) + Measure.dirac 1)

/-- The law of a vector `η ∈ {±1}^M` with independent Rademacher coordinates (Jo–Lee,
arXiv:2610.00103, (3.29), p.9, PDF p.10). -/
noncomputable def radVec (M : ℕ) : Measure (Fin M → ℝ) :=
  Measure.pi fun _ : Fin M => fairCoin

end OnlineDiscUniv


