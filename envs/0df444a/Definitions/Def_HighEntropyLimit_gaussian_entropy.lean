-- Prove2me | Definitions.Def_HighEntropyLimit_gaussian_entropy
-- name    : HighEntropyLimit_gaussian_entropy
-- status  : Definition
-- author  : @Lucas
-- created : 2026-10-12T21:51:22.161004+00:00
-- url     : https://prove2.me/theorems/c3d3d79b-00c3-40e6-9e48-818380f863d3
-- title:
--   Classical and quantum Gaussian entropies $S_C$, $S_Q$, $S_Q^\lambda$
-- statement:
--   Fix the reduced Planck constant $\hbar$ and a Gaussian uncertainty $\Sigma = \sigma_x\sigma_p$. This file defines
--
--   1. the classical Gaussian entropy (Eq. 2) $$S_C(\Sigma) = \ln\frac{\Sigma}{\hbar} + 1 = \ln\Big(2\pi e\frac{\Sigma}{h}\Big);$$
--   2. the quantum Gaussian entropy (Eq. 3) $$S_Q(\Sigma) = \Big(\frac{\Sigma}{\hbar}+\frac12\Big)\ln\Big(\frac{\Sigma}{\hbar}+\frac12\Big) - \Big(\frac{\Sigma}{\hbar}-\frac12\Big)\ln\Big(\frac{\Sigma}{\hbar}-\frac12\Big);$$
--   3. the rescaled quantum entropy of Section 4.3 / Fig. 3: $S_Q^\lambda(\Sigma) = S_Q(\lambda\Sigma) - \ln\lambda$.
--
--   All entropies are in nats.
--
--   **Formalization Note** These are total real functions. Lean's `Real.log` returns $0$ at $0$ and $\ln|x|$ for negative $x$, so the formulas carry meaning only for $\hbar>0$, $\Sigma>0$ (classical) and $\Sigma\ge\hbar/2$ (quantum). Theorems state these ranges as hypotheses.
-- source:
--   Carcassi, Landini, Aidala, Classical mechanics as the high-entropy limit of quantum mechanics, arXiv:2411.00972v3 (1 Feb 2026), https://arxiv.org/abs/2411.00972, pp. 3 Eqs. (2),(3); p. 11 (Fig. 3 and the formula for S_Q^λ)

import Mathlib

namespace HighEntropyLimit

/-- Classical entropy (in nats) of a Gaussian phase-space distribution with uncertainty
`Sig = σₓσₚ`, Eq. (2): `S_C(Σ) = ln(2πe Σ / h) = ln(Σ/ħ) + 1`. -/
noncomputable def classicalGaussianEntropy (hbar Sig : ℝ) : ℝ :=
  Real.log (Sig / hbar) + 1

/-- Von Neumann entropy (in nats) of a Gaussian quantum state with uncertainty `Sig`, Eq. (3):
`S_Q(Σ) = (Σ/ħ + 1/2) ln(Σ/ħ + 1/2) - (Σ/ħ - 1/2) ln(Σ/ħ - 1/2)`. -/
noncomputable def quantumGaussianEntropy (hbar Sig : ℝ) : ℝ :=
  (Sig / hbar + 1 / 2) * Real.log (Sig / hbar + 1 / 2)
    - (Sig / hbar - 1 / 2) * Real.log (Sig / hbar - 1 / 2)

/-- The rescaled quantum Gaussian entropy of Section 4.3 / Fig. 3:
`S_Q^λ(Σ) = S_Q(λΣ) - ln λ`. -/
noncomputable def rescaledQuantumGaussianEntropy (hbar lam Sig : ℝ) : ℝ :=
  quantumGaussianEntropy hbar (lam * Sig) - Real.log lam

end HighEntropyLimit


