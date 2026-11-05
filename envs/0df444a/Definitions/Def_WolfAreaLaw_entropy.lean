-- Prove2me | Definitions.Def_WolfAreaLaw_entropy
-- name    : WolfAreaLaw_entropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:49:25.165818+00:00
-- url     : https://prove2.me/theorems/9207904f-7e83-4ce0-846b-44523255ebc4
-- title:
--   Von Neumann entropy $S(\rho)=-\operatorname{tr}[\rho\log\rho]$ (natural logarithm)
-- statement:
--   For a finite-dimensional Hermitian matrix $\rho$, the **von Neumann entropy** is
--
--   $$
--   S(\rho) = -\operatorname{tr}[\rho\log\rho] = -\sum_{\lambda} \lambda\log\lambda ,
--   $$
--
--   the sum running over the eigenvalues of $\rho$ with multiplicity, with the convention $0\log 0 = 0$. For a density matrix it is the Shannon entropy of the spectrum. This is the entropy the paper uses in the quantum case, both inside the mutual information and inside the free energy.
--
--   **Formalization Note** The logarithm is the natural one: the thermal state $e^{-\beta H}/\operatorname{tr}e^{-\beta H}$ and the free energy $F=\operatorname{tr}[H\rho]-S/\beta$ fix this base. The function $x\mapsto x\log x$ is applied to $\rho$ by the continuous functional calculus, and the value is the real part of the trace. On a non-Hermitian matrix the value is the junk $0$; every statement applies it to a density matrix.
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "In the quantum case the ρ's become density operators (and their partial traces) and H has to be replaced by the von Neumann entropy S(ρ) = −tr[ρ log ρ]."

import Mathlib

namespace WolfAreaLaw

/-- **Von Neumann entropy in nats**, `S(ρ) = −tr[ρ log ρ]`.
Wolf–Verstraete–Hastings–Cirac, *Area laws in quantum systems: mutual information and
correlations*, arXiv:0704.3906v2, p.2: "In the quantum case the ρ's become density operators (and
their partial traces) and H has to be replaced by the von Neumann entropy S(ρ) = −tr[ρ log ρ]."

Computed as `−Re tr f(ρ)` for `f(x) = x log x`, applied to `ρ` by the continuous functional
calculus (the real function applied to the eigenvalues of a Hermitian `ρ`).

**Formalization Note** The logarithm is the natural one (`Real.log`): the paper's thermal state
`e^{−βH}/tr e^{−βH}` and free energy `F = tr[Hρ] − S/β` fix this base. `0 log 0 = 0` because
`Real.log 0 = 0`. On a non-Hermitian matrix `cfc` returns `0`, so the value is the junk `0`;
every statement applies it to a density matrix. -/
noncomputable def entropy {ι : Type*} [Fintype ι] [DecidableEq ι] (ρ : Matrix ι ι ℂ) : ℝ :=
  -(cfc (fun x : ℝ => x * Real.log x) ρ).trace.re

end WolfAreaLaw


