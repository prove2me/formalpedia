-- Prove2me | Definitions.Def_WolfAreaLaw_thermalState
-- name    : WolfAreaLaw_thermalState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:35.439951+00:00
-- url     : https://prove2.me/theorems/6ba04edb-eb32-44c1-b163-8398958eae58
-- title:
--   Thermal state $\rho_\beta=e^{-\beta H}/\operatorname{tr}e^{-\beta H}$
-- statement:
--   For a Hamiltonian $H$ (a Hermitian matrix) on a finite-dimensional space and an inverse temperature $\beta$, the **thermal state** (Gibbs state) is
--
--   $$
--   \rho_\beta = \frac{e^{-\beta H}}{\operatorname{tr} e^{-\beta H}} .
--   $$
--
--   In the paper, $\rho_{AB}$ is the thermal state of $H=H_A+H_\partial+H_B$ on the composite system. The paper names the thermal state without writing a formula and characterizes it by the property that it minimizes the free energy; the formula above is the standard definition, and the minimization property is a milestone of this mission.
--
--   **Formalization Note** This is the published `QAlgorithms.gibbsState` (the matrix $e^{X}/\operatorname{tr}e^{X}$ with the power-series exponential) applied to $X=-\beta H$; the minus sign and the factor $\beta$ are written in this definition. On a zero-dimensional space the trace is $0$ and the value is the zero matrix.
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "The thermal state ρAB corresponding to the inverse temperature β"

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SDP

namespace WolfAreaLaw

/-- **Thermal state** at inverse temperature `β` of a Hamiltonian `H`:
`ρ_β = e^{−βH} / tr e^{−βH}`.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2: "The thermal state ρAB corresponding to
the inverse temperature β".

**Formalization Note** This is the published `QAlgorithms.gibbsState` (`exp(X)/tr exp(X)` with the
plain matrix exponential `NormedSpace.exp`) applied to `X = −βH`; the sign and the factor `β` are
written here. The paper names the thermal state without a formula and characterizes it as the
minimizer of the free energy; `e^{−βH}/tr e^{−βH}` is the standard definition. On an empty index
type the trace is `0` and the value is the zero matrix. -/
noncomputable def thermalState {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ℝ)
    (H : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  QAlgorithms.gibbsState (-(β : ℂ) • H)

end WolfAreaLaw


