-- Prove2me | Definitions.Def_GapAgnosticGS_deff
-- name    : GapAgnosticGS_deff
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:31:01.890956+00:00
-- url     : https://prove2.me/theorems/329ed8d0-2fb3-4138-b359-1df2573ff144
-- title:
--   Effective excitation dimension $d_{\rm eff}=\Delta_{\rm gs}^2\Gamma_{\rm gs}$
-- statement:
--   For a Hamiltonian $H$ with spectral gap $\Delta_{\rm gs}=E_1-E_0$ and spectral complexity $\Gamma_{\rm gs}$, the **effective excitation dimension** is
--
--   $$d_{\rm eff}:=\Delta_{\rm gs}^2\,\Gamma_{\rm gs}.$$
--
--   For a unique ground state $1\le d_{\rm eff}\le n-1$. The main bound reads $\widetilde O\big((\alpha/\Delta_{\rm gs})\sqrt{d_{\rm eff}}\big)$, and the lower-bound families of Theorem 3.15 have $d_{\rm eff}=(k-1)+(n-k)(\Delta_{\rm gs}/2\alpha)^2$.
--
--   **Formalization Note** $\Delta_{\rm gs}$ is the published `QAlgorithms.spectralGap` (second smallest minus smallest eigenvalue, with multiplicity).
-- source:
--   Heidari–Moharrami–Tavakoli–Zhang, Gap-Agnostic Ground-State Preparation via Quantum Bandits, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.2 (PDF p.3), display "d_eff := ∆²_gs Γ_gs"

import Definitions.Def_GapAgnosticGS_gammaGS
open QAlgorithms

namespace GapAgnosticGS

/-- Heidari–Moharrami–Tavakoli–Zhang, *Gap-Agnostic Ground-State Preparation via Quantum Bandits*, manuscript (STOC 2027 submission, sha256 bd767ba1…c57acc), §1, p.2 (PDF p.3): the effective excitation dimension "d_eff := Δ_gs² Γ_gs", where
`Δ_gs = E_1 − E_0` is the published `QAlgorithms.spectralGap H` (second smallest minus smallest
eigenvalue, with multiplicity). -/
noncomputable def deff {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  spectralGap H ^ 2 * gammaGS H

end GapAgnosticGS


