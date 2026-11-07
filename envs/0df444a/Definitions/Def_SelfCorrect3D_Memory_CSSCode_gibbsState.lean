-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_CSSCode_gibbsState
-- name    : SelfCorrect3D_Memory_CSSCode_gibbsState
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:35:15.237815+00:00
-- url     : https://prove2.me/theorems/1a9ce490-917b-41af-aa87-2ce5491ad05c
-- title:
--   Gibbs state $\rho_\beta=e^{-\beta H}/\mathrm{Tr}\,e^{-\beta H}$
-- statement:
--   For an inverse temperature $\beta=1/T\in\mathbb R$, the **Gibbs state** of the stabilizer Hamiltonian is
--
--   $$\rho_\beta=\frac{e^{-\beta H}}{\mathrm{Tr}\,e^{-\beta H}} .$$
--
--   It is the stationary state of the thermalizing dynamics.
--
--   **Formalization Note** $e^{-\beta H}$ is the matrix exponential; its trace is positive for every real $\beta$.
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, p. 4 (after eq. (1)); §2.5, p. 20

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_CSSCode_hamiltonian

namespace SelfCorrect3D.Memory

/-- **Gibbs state** `ρ_β = e^{−βH}/Tr(e^{−βH})` of the stabilizer Hamiltonian. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
p. 4 ("The stationary state is the Gibbs state ρ_β = e^{−βH}/Tr(e^{−βH}) where β = 1/T") and
p. 20.

**Formalization Note.** `e^{−βH}` is `NormedSpace.exp` of the matrix `−βH` (the matrix
exponential). The trace is positive for every real `β`, so the division is never by zero. -/
noncomputable def CSSCode.gibbsState {n mX mZ : ℕ} (C : CSSCode n mX mZ) (β : ℝ) : Op n :=
  (Matrix.trace (NormedSpace.exp ((-(β : ℂ)) • C.hamiltonian)))⁻¹ •
    NormedSpace.exp ((-(β : ℂ)) • C.hamiltonian)

end SelfCorrect3D.Memory


