-- Prove2me | Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian_gen
-- name    : AutoQMem_Lindblad_SyndromeLindbladian_gen
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:20.185358+00:00
-- url     : https://prove2.me/theorems/6bb62600-290a-4819-bf0c-de3b1e17f42a
-- title:
--   The generators $\mathcal L(t)$ and $\mathcal L^*(t)$
-- statement:
--   The Schrödinger-picture generator of a syndrome-based Lindbladian and its Heisenberg-picture generator are
--   $$\mathcal L(t)(\rho)=-i[H(t),\rho]+\sum_{i=1}^n\sum_{P\in\{I,X,Y,Z\}}\sum_\alpha\mathcal D[P_if_{P,i,\alpha}(t)](\rho),$$
--   $$\mathcal L^*(t)(O)=i[H(t),O]+\sum_{i=1}^n\sum_{P\in\{I,X,Y,Z\}}\sum_\alpha\mathcal D[P_if_{P,i,\alpha}(t)]^*(O).$$
--
--   **Formalization Note** $\mathcal L^*(t)$ is written by the paper's formula (42).
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.22, eq. (31), p. 20 (PDF p. 22); eq. (42), p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_SyndromeLindbladian
import Definitions.Def_AutoQMem_Lindblad_diss
import Definitions.Def_AutoQMem_Lindblad_pauliAt
open Matrix

namespace AutoQMem.Lindblad

namespace SyndromeLindbladian

variable {n mX mZ : ℕ} {C : CSSCode n mX mZ} {ι : Type} [Fintype ι]

/-- **The Lindbladian `L(t)`** (Schrödinger picture). Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.22, eq. (31), p. 20
(PDF 22): `L(t)(ρ) = −i[H(t), ρ] + Σ_i Σ_{P ∈ {I,X,Y,Z}} Σ_α D[P_i f_{P,i,α}(t)](ρ)`. -/
noncomputable def gen (L : SyndromeLindbladian C ι) (t : ℝ) (ρ : Op n) : Op n :=
  -Complex.I • (L.ham t * ρ - ρ * L.ham t) +
    ∑ i, ∑ P : Pauli1, ∑ α, diss (pauliAt P i * L.jump t i P α) ρ

/-- **The Heisenberg-picture generator `L*(t)`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), eq. (42), p. 22 (PDF 24):
`L*(t)(O) = i[H(t), O] + Σ_i Σ_P Σ_α D[P_i f_{P,i,α}(t)]*(O)`.

**Formalization Note.** Written by the paper's formula (42); it is the trace-pairing adjoint of
`gen L t` (for Hermitian `H(t)`). -/
noncomputable def genAdj (L : SyndromeLindbladian C ι) (t : ℝ) (O : Op n) : Op n :=
  Complex.I • (L.ham t * O - O * L.ham t) +
    ∑ i, ∑ P : Pauli1, ∑ α, dissAdj (pauliAt P i * L.jump t i P α) O

end SyndromeLindbladian

end AutoQMem.Lindblad


