-- Prove2me | Definitions.Def_KnownFidelity_Rank_Tj
-- name    : KnownFidelity_Rank_Tj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T21:45:50.104341+00:00
-- url     : https://prove2.me/theorems/8800e99b-233c-4d11-9c93-b02ba42bf953
-- title:
--   The functional $T_j(\tau)=\mathrm{tr}\sqrt\tau/\sqrt j$
-- statement:
--   For a state $\tau$ on $\mathbb C^j$,
--
--   $$T_j(\tau)=\frac{\mathrm{tr}\sqrt\tau}{\sqrt j}=F\big(\tau,I_j/j\big),$$
--
--   the root fidelity with the maximally mixed state. Proposition 4.1 separates two priors by the value of $T_j$.
--
--   **Formalization Note** $\sqrt\tau$ is `cfc Real.sqrt τ`; the trace is taken as a real number.
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Proposition 4.1, p. 8 (PDF p. 10)

import Mathlib

namespace KnownFidelity.Rank

/-- **The functional `T_j(τ) = tr √τ / √j`.**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Proposition 4.1, printed p. 8 (PDF p. 10): "T_j(τ) := tr √τ / √j".

For a matrix `τ` on `ℂ^j`, `Tj τ = Re tr √τ / √j`; for a state, `Tj τ = F(τ, I_j/j)`.

**Formalization Note.** `√τ` is `cfc Real.sqrt τ`, and `j` is read off the index type `Fin j`. -/
noncomputable def Tj {j : ℕ} (τ : Matrix (Fin j) (Fin j) ℂ) : ℝ :=
  (cfc Real.sqrt τ).trace.re / Real.sqrt j

end KnownFidelity.Rank


