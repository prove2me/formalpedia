-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_TX
-- name    : AutoQMem_Lindblad_LogicalQubit_TX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:08.130532+00:00
-- url     : https://prove2.me/theorems/c8299b37-b2c3-4b03-82b7-ce180adf9782
-- title:
--   Decoded logical observables $T_X$, $T_Z$
-- statement:
--   The **decoded logical observables** are the Heisenberg images of the bare logicals under the sector decoding channels:
--   $$T_X=\sum_{s\in\Sigma_X}\Pi^X_sR_X(s)^\dagger\bar XR_X(s)\Pi^X_s,\qquad T_Z=\sum_{s\in\Sigma_Z}\Pi^Z_sR_Z(s)^\dagger\bar ZR_Z(s)\Pi^Z_s,$$
--   with $R_X(s)=Z^{\mathrm{Dec}_X(s)}$, $R_Z(s)=X^{\mathrm{Dec}_Z(s)}$. Measuring $T_X$ on a state equals decoding it and then measuring $\bar X$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.16, eqs. (19)–(20), p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit
import Definitions.Def_AutoQMem_Lindblad_CSSCode_decodeChannel
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Decoded logical observable `T_X`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.16, eq. (19), p. 18 (PDF 20):
`T_X := E^{(X)*}_dec(X̄) = Σ_{s ∈ Σ_X} Π^X_s R_X(s)† X̄ R_X(s) Π^X_s`, with `R_X(s) = Z^{Dec_X(s)}`
and `X̄ = X^{ℓ_X}`. -/
noncomputable def TX (Q : LogicalQubit C) (DX : Decoder C.HX) : Op (n' + 1) :=
  ∑ s ∈ C.synX, C.projX s * (pauliZ (DX.dec s))ᴴ * pauliX Q.lX * pauliZ (DX.dec s) * C.projX s

/-- **Decoded logical observable `T_Z`** (Definition 2.16, eq. (20)):
`T_Z := Σ_{s ∈ Σ_Z} Π^Z_s R_Z(s)† Z̄ R_Z(s) Π^Z_s`, with `R_Z(s) = X^{Dec_Z(s)}`, `Z̄ = Z^{ℓ_Z}`. -/
noncomputable def TZ (Q : LogicalQubit C) (DZ : Decoder C.HZ) : Op (n' + 1) :=
  ∑ s ∈ C.synZ, C.projZ s * (pauliX (DZ.dec s))ᴴ * pauliZ Q.lZ * pauliX (DZ.dec s) * C.projZ s

end LogicalQubit

end AutoQMem.Lindblad


