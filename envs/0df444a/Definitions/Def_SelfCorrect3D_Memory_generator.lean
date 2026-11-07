-- Prove2me | Definitions.Def_SelfCorrect3D_Memory_generator
-- name    : SelfCorrect3D_Memory_generator
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T06:33:17.589539+00:00
-- url     : https://prove2.me/theorems/c3c82e62-8e15-4b22-8af8-c4df3b3c47b9
-- title:
--   Master-equation generator $\rho\mapsto -i[H,\rho]+\mathcal L(\rho)$
-- statement:
--   The **generator** of the Markovian master equation for a Hamiltonian $H$ and jump operators $S_1,\dots,S_m$ is
--
--   $$\hat{\mathcal L}(\rho)=-i[H,\rho]+\mathcal L(\rho),$$
--
--   so that $\dot\rho=\hat{\mathcal L}(\rho)$ is equation (1)/(45).
-- source:
--   Balasubramanian, Davydova, Lin, A passive self-correcting quantum memory in three dimensions, arXiv:2605.10943, eq. (1), p. 4; eq. (45), p. 19

import Mathlib
import Definitions.Def_SelfCorrect3D_Memory_dissipator

namespace SelfCorrect3D.Memory

/-- **Generator of the Markovian master equation** `ρ ↦ −i[H, ρ] + 𝓛(ρ)`. Balasubramanian, Davydova, Lin, *A passive self-correcting quantum memory in three dimensions*, arXiv:2605.10943,
eq. (1), p. 4 and eq. (45), p. 19. -/
noncomputable def generator {n m : ℕ} (H : Op n) (J : Fin m → Op n) (ρ : Op n) : Op n :=
  (-Complex.I) • (H * ρ - ρ * H) + dissipator J ρ

end SelfCorrect3D.Memory


