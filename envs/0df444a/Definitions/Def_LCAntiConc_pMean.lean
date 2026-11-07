-- Prove2me | Definitions.Def_LCAntiConc_pMean
-- name    : LCAntiConc_pMean
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:46:59.166504+00:00
-- url     : https://prove2.me/theorems/57fa4841-82c4-4536-811b-50cff312425f
-- title:
--   Pseudo-mean $\tilde{\mathbb E}\,v$
-- statement:
--   The **pseudo-mean** of a pseudo-expectation $\tilde{\mathbb E}$ is the vector
--
--   $$\mu_{\tilde{\mathbb E}}=\tilde{\mathbb E}\,v=\big(\tilde{\mathbb E}\,v_1,\dots,\tilde{\mathbb E}\,v_n\big)\in\mathbb R^n.$$
-- source:
--   Tiegel, Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions, STOC 2027 submission (manuscript sha256 7164444e…), Lemmas 4.3–4.4, p.18 (PDF p.20)

import Mathlib

namespace LCAntiConc

/-- The pseudo-mean `μ_Ẽ = Ẽ v ∈ ℝ^n` of a pseudo-expectation, coordinatewise `Ẽ vᵢ`.

Tiegel, *Dimension-Independent Anti-Concentration Certificates for Log-Concave Distributions*,
STOC 2027 submission (manuscript sha256 7164444e…), Lemma 4.3 ("μ = Ẽ v"), p.18 (PDF p.20),
and Lemma 4.4 ("μᵢ = Ẽᵢ v"), p.18 (PDF p.20). -/
noncomputable def pMean {n : ℕ} (L : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) : Fin n → ℝ :=
  fun i => L (MvPolynomial.X i)

end LCAntiConc


