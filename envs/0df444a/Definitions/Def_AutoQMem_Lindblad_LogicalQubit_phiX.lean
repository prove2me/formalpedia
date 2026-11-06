-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_phiX
-- name    : AutoQMem_Lindblad_LogicalQubit_phiX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:50.4932+00:00
-- url     : https://prove2.me/theorems/19e09b14-0baf-4aad-8f4a-2567973ef162
-- title:
--   Readout decoder phases $\varphi_X(s)$, $\varphi_Z(s)$ and operators $\varphi_X$, $\varphi_Z$
-- statement:
--   For a valid syndrome $s$, the **readout decoder phase** $\varphi_X(s)\in\{\pm1\}$ is defined by
--   $$R_X(s)^\dagger\bar XR_X(s)=\varphi_X(s)\bar X,$$
--   and similarly $\varphi_Z(s)$ by $R_Z(s)^\dagger\bar ZR_Z(s)=\varphi_Z(s)\bar Z$. The syndrome-diagonal operators are
--   $$\varphi_X=\sum_{s\in\Sigma_X}\varphi_X(s)\Pi^X_s,\qquad \varphi_Z=\sum_{s\in\Sigma_Z}\varphi_Z(s)\Pi^Z_s .$$
--
--   **Formalization Note** Since $R_X(s)^\dagger\bar XR_X(s)=\pm\bar X$ and $\bar X^2=I$, the scalar is computed as $\operatorname{Tr}(R_X(s)^\dagger\bar XR_X(s)\bar X)/2^n$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 4.1, eqs. (79)–(80), p. 32 (PDF p. 34)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit
import Definitions.Def_AutoQMem_Lindblad_Decoder
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Readout decoder phase `φ_X(s)`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 4.1, eq. (79), p. 32 (PDF 34): "define
φ_X(s_X) ∈ {±1} by R_X(s_X)† X̄ R_X(s_X) = φ_X(s_X) X̄".

**Formalization Note.** Since `R_X(s)† X̄ R_X(s)` is `±X̄` and `X̄² = I`, the scalar is
`Tr(R_X(s)† X̄ R_X(s) X̄) / 2ⁿ`. -/
noncomputable def phaseX (Q : LogicalQubit C) (DX : Decoder C.HX) (s : Fin mX → ZMod 2) : ℂ :=
  ((pauliZ (DX.dec s))ᴴ * pauliX Q.lX * pauliZ (DX.dec s) * pauliX Q.lX).trace / 2 ^ (n' + 1)

/-- **Readout decoder phase `φ_Z(s)`**, `R_Z(s)† Z̄ R_Z(s) = φ_Z(s) Z̄` (Definition 4.1, eq. (79)),
computed as `Tr(R_Z(s)† Z̄ R_Z(s) Z̄) / 2ⁿ`. -/
noncomputable def phaseZ (Q : LogicalQubit C) (DZ : Decoder C.HZ) (s : Fin mZ → ZMod 2) : ℂ :=
  ((pauliX (DZ.dec s))ᴴ * pauliZ Q.lZ * pauliX (DZ.dec s) * pauliZ Q.lZ).trace / 2 ^ (n' + 1)

/-- **Syndrome-diagonal decoder-phase operator** `φ_X := Σ_{s ∈ Σ_X} φ_X(s) Π^X_s` (Definition 4.1,
eq. (80)). -/
noncomputable def phiX (Q : LogicalQubit C) (DX : Decoder C.HX) : Op (n' + 1) :=
  ∑ s ∈ C.synX, Q.phaseX DX s • C.projX s

/-- **Syndrome-diagonal decoder-phase operator** `φ_Z := Σ_{s ∈ Σ_Z} φ_Z(s) Π^Z_s` (Definition 4.1,
eq. (80)). -/
noncomputable def phiZ (Q : LogicalQubit C) (DZ : Decoder C.HZ) : Op (n' + 1) :=
  ∑ s ∈ C.synZ, Q.phaseZ DZ s • C.projZ s

end LogicalQubit

end AutoQMem.Lindblad


