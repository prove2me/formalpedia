-- Prove2me | Definitions.Def_OppenheimRelay_RelayCode_relayError
-- name    : OppenheimRelay_RelayCode_relayError
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T15:30:59.450072+00:00
-- url     : https://prove2.me/theorems/04b99653-49b0-46ab-b820-765f5e348923
-- title:
--   Error of a relay code
-- statement:
--   For a relay code and a vector $\psi$ on the relay source, the error is the trace norm
--   $$
--   \|\rho_{\text{output}}-\rho_{\text{target}}\|_1
--   $$
--   on the whole system: $R^n$, $C^n$, $A^nB^n$ at Bob, and both final Bell banks.
--
--   Requiring this to be small is the paper's requirement that the overall state remain "virtually unchanged (in terms of fidelity)" while the final ebits are produced.
--
--   **Formalization Note** The paper measures closeness by fidelity. Fidelity tending to 1 and trace distance tending to 0 are equivalent (Fuchs–van de Graaf inequalities), and the trace norm is the convention of the published Devetak–Yard layer (`redistributionError`).
-- source:
--   Oppenheim, State redistribution as merging: introducing the coherent relay, arXiv:0805.1065v1, p.1, "keeping the overall state |ψ⟩⊗n ABCR virtually unchanged (in terms of fidelity)"

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P20
import Definitions.Def_OppenheimRelay_RelayCode_output
import Definitions.Def_OppenheimRelay_RelayCode_target

open QAlgorithms QAlgorithms.Papers.Independent.Gap48.P20

namespace OppenheimRelay

attribute [local instance] Classical.propDecidable Classical.decEq

/-- **The relay error.** Oppenheim, *State redistribution as merging: introducing the coherent relay*, arXiv:0805.1065v1, p.1, "keeping the overall state |ψ⟩⊗n ABCR virtually unchanged
(in terms of fidelity)": the trace norm `‖output − target‖₁` on the whole system, that is on `R^n`,
`C^n`, `A^n B^n` and both final Bell banks.

**Formalization Note** The paper measures closeness by fidelity. Fidelity tending to 1 and trace
distance tending to 0 are equivalent (Fuchs–van de Graaf), and the trace norm is the convention of
the published Devetak–Yard layer (`TransferCode.redistributionError`). -/
noncomputable def RelayCode.relayError {A C B R : Type*} [Fintype A] [Fintype C] [Fintype B]
    [Fintype R] {n : ℕ} (P : RelayCode A C B n) (psi : EuclideanSpace ℂ (RelaySource A C B R)) :
    ℝ :=
  traceNorm (P.output psi - P.target psi)

end OppenheimRelay


