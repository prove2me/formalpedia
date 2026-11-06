-- Prove2me | Definitions.Def_AutoQMem_Lindblad_diss
-- name    : AutoQMem_Lindblad_diss
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:53:35.461195+00:00
-- url     : https://prove2.me/theorems/64b623a0-4d95-424c-97ec-ae6f2a001afd
-- title:
--   Dissipator $\mathcal D[L]$ and adjoint dissipator $\mathcal D[L]^*$
-- statement:
--   For a jump operator $L$, the **dissipator** and its Heisenberg adjoint are
--   $$\mathcal D[L](\rho)=L\rho L^\dagger-\tfrac12\{L^\dagger L,\rho\},\qquad \mathcal D[L]^*(O)=L^\dagger OL-\tfrac12\{L^\dagger L,O\},$$
--   where $\{A,B\}=AB+BA$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), eq. (30), p. 19 (PDF p. 21); eq. (41), p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_Op
open Matrix

namespace AutoQMem.Lindblad

/-- **Lindblad dissipator** `D[L](ρ) = L ρ L† − ½{L†L, ρ}`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, eq. (30), p. 19 (PDF 21). -/
noncomputable def diss {n : ℕ} (L ρ : Op n) : Op n :=
  L * ρ * Lᴴ - (1 / 2 : ℂ) • (Lᴴ * L * ρ + ρ * (Lᴴ * L))

/-- **Adjoint dissipator** `D[L]*(O) = L† O L − ½{L†L, O}`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), §2.2.1, eq. (41), p. 22 (PDF 24). -/
noncomputable def dissAdj {n : ℕ} (L O : Op n) : Op n :=
  Lᴴ * O * L - (1 / 2 : ℂ) • (Lᴴ * L * O + O * (Lᴴ * L))

end AutoQMem.Lindblad


