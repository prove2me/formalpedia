-- Prove2me | Definitions.Def_AutoQMem_Lindblad_CSSCode_decodeChannel
-- name    : AutoQMem_Lindblad_CSSCode_decodeChannel
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:56:34.883201+00:00
-- url     : https://prove2.me/theorems/382c33cc-b2ee-47ab-9f8d-0930b939cca7
-- title:
--   Physical decoding channel $\mathcal E_{\mathrm{dec}}=\mathcal E^{(X)}_{\mathrm{dec}}\circ\mathcal E^{(Z)}_{\mathrm{dec}}$
-- statement:
--   With the Pauli readout corrections $R_X(s)=Z^{\mathrm{Dec}_X(s)}$ and $R_Z(s)=X^{\mathrm{Dec}_Z(s)}$, the sector decoding channels are
--   $$\mathcal E^{(X)}_{\mathrm{dec}}(\rho)=\sum_{s\in\Sigma_X}R_X(s)\Pi^X_s\,\rho\,\Pi^X_sR_X(s)^\dagger,\qquad \mathcal E^{(Z)}_{\mathrm{dec}}(\rho)=\sum_{s\in\Sigma_Z}R_Z(s)\Pi^Z_s\,\rho\,\Pi^Z_sR_Z(s)^\dagger,$$
--   and the physical decoding channel is $\mathcal E_{\mathrm{dec}}=\mathcal E^{(X)}_{\mathrm{dec}}\circ\mathcal E^{(Z)}_{\mathrm{dec}}$: measure both syndromes and apply the corresponding Pauli corrections.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.12, eq. (16), p. 17 (PDF p. 19); Definition 2.13, eq. (17), p. 17

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode_projX
import Definitions.Def_AutoQMem_Lindblad_Decoder
open Matrix

namespace AutoQMem.Lindblad

namespace CSSCode

variable {n mX mZ : ℕ}

/-- **X-sector decoding channel.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.13, eq. (17), p. 17 (PDF 19), with the Pauli
readout correction `R_X(s) := Z^{Dec_X(s)}` of Definition 2.12, eq. (16):
`E^{(X)}_dec(ρ) := Σ_{s ∈ Σ_X} R_X(s) Π^X_s ρ Π^X_s R_X(s)†`. -/
noncomputable def decX (C : CSSCode n mX mZ) (DX : Decoder C.HX) (ρ : Op n) : Op n :=
  ∑ s ∈ C.synX, pauliZ (DX.dec s) * C.projX s * ρ * C.projX s * (pauliZ (DX.dec s))ᴴ

/-- **Z-sector decoding channel** `E^{(Z)}_dec(ρ) := Σ_{s ∈ Σ_Z} R_Z(s) Π^Z_s ρ Π^Z_s R_Z(s)†` with
`R_Z(s) := X^{Dec_Z(s)}` (Definitions 2.12–2.13, "defined symmetrically"). -/
noncomputable def decZ (C : CSSCode n mX mZ) (DZ : Decoder C.HZ) (ρ : Op n) : Op n :=
  ∑ s ∈ C.synZ, pauliX (DZ.dec s) * C.projZ s * ρ * C.projZ s * (pauliX (DZ.dec s))ᴴ

/-- **Physical decoding channel** `E_dec = E^{(X)}_dec ∘ E^{(Z)}_dec` (Definition 2.13, p. 17). -/
noncomputable def decodeChannel (C : CSSCode n mX mZ) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (ρ : Op n) : Op n :=
  C.decX DX (C.decZ DZ ρ)

end CSSCode

end AutoQMem.Lindblad


