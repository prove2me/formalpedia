-- Prove2me | Definitions.Def_KnownFidelity_Rank_hSigma
-- name    : KnownFidelity_Rank_hSigma
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:25.574338+00:00
-- url     : https://prove2.me/theorems/e3be5185-2e41-48fa-8e77-847dcc0e1679
-- title:
--   The parameter $h_\sigma=(\mathrm{tr}\sqrt\sigma)^2$
-- statement:
--   For a state $\sigma$,
--
--   $$h_\sigma=\big(\mathrm{tr}\sqrt\sigma\big)^2,\qquad 1\le h_\sigma\le\operatorname{rank}\sigma .$$
--
--   It measures how spread the spectrum of the reference is and appears in the risk bounds of Theorem 1.1, Lemma 3.1 and Proposition 3.2.
--
--   **Formalization Note** $\sqrt\sigma$ is `cfc Real.sqrt σ` and the trace is taken as a real number (its real part).
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, §1.1 (unnumbered display), p. 1 (PDF p. 3)

import Mathlib

namespace KnownFidelity.Rank

/-- **The parameter `h_σ = (tr √σ)²`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, §1.1 (unnumbered display), printed p. 1 (PDF p. 3): "Put
h_σ = (tr √σ)², 1 ≤ h_σ ≤ rank σ."

**Formalization Note.** `√σ` is `cfc Real.sqrt σ` (the positive square root on positive
semidefinite matrices, the same convention as `QAlgorithms.rootFidelity`), and the trace is
taken as a real number (its real part; it is real for Hermitian `σ`). -/
noncomputable def hSigma {ι : Type*} [Fintype ι] [DecidableEq ι] (σ : Matrix ι ι ℂ) : ℝ :=
  ((cfc Real.sqrt σ).trace.re) ^ 2

end KnownFidelity.Rank


