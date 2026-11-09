-- Prove2me | Definitions.Def_SublinearPauli_Fidelity_Energies
-- name    : SublinearPauli_Fidelity_Energies
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T09:41:43.590197+00:00
-- url     : https://prove2.me/theorems/96a6c04e-775e-435a-9d2b-af8e588d5e56
-- title:
--   Lemma 2, p.13 — $\lambda=(1+\sqrt{33})/8$, the rate $A_N$, the graph energy $E_\gamma$ and the lab-state norm $W_\gamma$
-- statement:
--   The exponent of the paper is
--   $$\lambda=\frac{1+\sqrt{33}}{8}\approx0.8431,$$
--   and the rate of Theorems 1 and 2 is $A_N=2^{\lambda N}(\sqrt3)^{(1-\lambda)N}$.
--
--   For a parameter $\gamma$, a target $\rho$ and a lab state $\sigma$ (with Pauli coefficients $\hat\rho$, $\hat\sigma$ normalized by $\sqrt d$), the **edge weight of the random Pauli graph** and the **lab-state norm** are
--   $$E_\gamma(\rho)=\sum_{(Q,Q')\in\mathcal S}\frac{|\hat\rho(Q)|^{\frac{2}{1+\gamma}}\cdot|\hat\rho(Q')|^{\frac{2}{1+\gamma}}}{3^{N-w(Q\cap Q')}},\qquad W_\gamma(\sigma)=\sum_{(Q,Q')\in\mathcal S}\frac{|\hat\sigma(Q\Delta Q')|^{\frac{2}{1-\gamma}}}{3^{N-w(Q\cap Q')}},$$
--   the sums over all ordered compatible pairs, including identities and diagonal pairs.
--
--   $E_\gamma$ and $W_\gamma$ are the two factors into which Lemma 2 splits the biased norm; Theorem 3 and Lemma 4 bound them.
--
--   **Formalization Note** Powers are real powers of absolute values; the paper uses $E_\gamma$ for $0\le\gamma\le\lambda$ and $W_\gamma$ for $0\le\gamma<1$, where the exponents are positive. The exponent $N-w(Q\cap Q')$ is a natural number since $w\le N$.
-- source:
--   Abhilash Dharmavarapu, Jayadev Acharya, Nengkun Yu, Yuhan Liu, STOC 2027 submission #230 (October 2026), PDF sha256 a007d4d449494d7b3589233107d1fc0190d256341e1bcbb1b95965363d6e10c4, Lemma 2 p.13 (E_γ, W_γ), Theorems 1–3 pp.11–13 (λ = (1+√33)/8, rate 2^{λN}√3^{(1−λ)N})

import Mathlib
import Definitions.Def_SublinearPauli_Fidelity_Pauli

open ClassicalShadow.Linear

namespace SublinearPauli.Fidelity

/-- The hypercontractivity exponent `λ = (1 + √33)/8` (Theorems 1–3). -/
noncomputable def lam : ℝ := (1 + Real.sqrt 33) / 8

/-- The rate `A_N = 2^{λN} (√3)^{(1−λ)N}` of Theorems 1 and 2. -/
noncomputable def rateA (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (lam * N) * Real.sqrt 3 ^ ((1 - lam) * N)

/-- The edge weight of the random Pauli graph (Lemma 2, p.13):
`E_γ(ρ) = Σ_{(Q,Q') ∈ 𝒮} |ρ̂(Q)|^{2/(1+γ)} |ρ̂(Q')|^{2/(1+γ)} / 3^{N − w(Q ∩ Q')}`. -/
noncomputable def energyE {N : ℕ} (γ : ℝ) (ρ : Op N) : ℝ :=
  ∑ Q : PauliString N, ∑ Q' : PauliString N,
    if Compatible Q Q' then
      |coeff ρ Q| ^ (2 / (1 + γ)) * |coeff ρ Q'| ^ (2 / (1 + γ)) /
        (3 : ℝ) ^ (N - weight (inter Q Q'))
    else 0

/-- The lab-state norm (Lemma 2, p.13):
`W_γ(σ) = Σ_{(Q,Q') ∈ 𝒮} |σ̂(Q Δ Q')|^{2/(1−γ)} / 3^{N − w(Q ∩ Q')}`. -/
noncomputable def energyW {N : ℕ} (γ : ℝ) (σ : Op N) : ℝ :=
  ∑ Q : PauliString N, ∑ Q' : PauliString N,
    if Compatible Q Q' then
      |coeff σ (symmDiff Q Q')| ^ (2 / (1 - γ)) / (3 : ℝ) ^ (N - weight (inter Q Q'))
    else 0

end SublinearPauli.Fidelity


