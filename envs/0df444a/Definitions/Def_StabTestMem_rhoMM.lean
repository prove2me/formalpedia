-- Prove2me | Definitions.Def_StabTestMem_rhoMM
-- name    : StabTestMem_rhoMM
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T09:09:30.807835+00:00
-- url     : https://prove2.me/theorems/1d29866b-dd7b-45eb-914e-3e3eb9ee6dfc
-- title:
--   Maximally mixed state on $t$ copies, $\rho_{\mathrm{mm}}=I^{\otimes t}/2^{nt}$
-- statement:
--   $t$ copies of the maximally mixed $n$-qubit state: $\rho_{\mathrm{mm}}=I^{\otimes t}/2^{nt}$. Its transcript distribution is $P_{\mathrm{mm}}(x)=\operatorname{Tr}[E_x]/2^{nt}$ (Eq. (76)).
-- source:
--   Arunachalam, Schatzki, Optimal stabilizer testing and learning with limited quantum memory, arXiv:2607.02444 (version of 2 Nov 2026), §5.2, p. 38; Eq. (76), p. 37

import Definitions.Def_QAlgorithms_Defs_Basic

namespace StabTestMem

open QAlgorithms

/-- **`t` copies of the maximally mixed state, `ρ_mm = I^{⊗t}/2^{nt}`.** Arunachalam, Schatzki, *Optimal stabilizer testing and learning with limited quantum memory*, arXiv:2607.02444 (version of 2 Nov 2026), §5.2, p. 38, item 3
("The maximally mixed state ρ_mm = I^{⊗t}/2^{nt}"), and Eq. (76), p. 37. -/
noncomputable def rhoMM (n t : ℕ) : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ :=
  ((2 : ℂ) ^ (n * t))⁻¹ • (1 : Matrix (Fin t → Qubits n) (Fin t → Qubits n) ℂ)

end StabTestMem


