-- Prove2me | Definitions.Def_WolfAreaLaw_freeEnergy
-- name    : WolfAreaLaw_freeEnergy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:50:18.16614+00:00
-- url     : https://prove2.me/theorems/a0a13d85-6b79-4b78-82a2-677a496da438
-- title:
--   Free energy $F(\rho)=\operatorname{tr}[H\rho]-\frac1\beta S(\rho)$
-- statement:
--   For a Hamiltonian $H$, an inverse temperature $\beta>0$ and a state $\rho$ on the same finite-dimensional space, the **free energy** of $\rho$ is
--
--   $$
--   F(\rho) = \operatorname{tr}[H\rho] - \frac{1}{\beta}\,S(\rho),
--   $$
--
--   where $S$ is the von Neumann entropy. The thermal state at inverse temperature $\beta$ minimizes $F$ over all states, which is the starting point of the paper's proof of the finite-temperature area law.
--
--   **Formalization Note** $\operatorname{tr}[H\rho]$ is the real part of the trace of $H\rho$, which is real for Hermitian $H$ and $\rho$. $S$ uses the natural logarithm (`WolfAreaLaw.entropy`). The division by $\beta$ is real division; every statement that uses the free energy assumes $\beta>0$.
-- source:
--   Wolf–Verstraete–Hastings–Cirac, Area laws in quantum systems: mutual information and correlations, arXiv:0704.3906v2, p.2, paragraph "For quantum systems less information…", "minimizes the free energy F(ρ) = tr[Hρ] − (1/β) S(ρ)"

import Mathlib
import Definitions.Def_WolfAreaLaw_entropy

namespace WolfAreaLaw

/-- **Free energy** `F(ρ) = tr[Hρ] − (1/β) S(ρ)` of a state `ρ` for the Hamiltonian `H` at inverse
temperature `β`.
Wolf–Verstraete–Hastings–Cirac, arXiv:0704.3906v2, p.2: "The thermal state ρAB corresponding to
the inverse temperature β minimizes the free energy F(ρ) = tr[Hρ] − (1/β) S(ρ)."

**Formalization Note** `tr[Hρ]` is the real part of the trace of `H * ρ` (real for Hermitian `H`
and `ρ`); `S` is the natural-log `WolfAreaLaw.entropy`. The division `S(ρ)/β` is real division;
every statement that uses `freeEnergy` assumes `0 < β`. -/
noncomputable def freeEnergy {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ℝ)
    (H ρ : Matrix ι ι ℂ) : ℝ :=
  (H * ρ).trace.re - entropy ρ / β

end WolfAreaLaw


