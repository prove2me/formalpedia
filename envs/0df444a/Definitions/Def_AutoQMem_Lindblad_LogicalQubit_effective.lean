-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_effective
-- name    : AutoQMem_Lindblad_LogicalQubit_effective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:57:59.648095+00:00
-- url     : https://prove2.me/theorems/84dd708f-770d-4576-8693-2489d1aa9c40
-- title:
--   Encoding, decoding and the effective logical channel $\mathcal E_L[\mathcal W_*]$
-- statement:
--   For a physical evolution $\mathcal W_*$ on $\mathcal H$, the **effective logical channel** is
--   $$\mathcal E_L[\mathcal W_*]=\mathcal D_{\mathrm{dec}}\circ\mathcal W_*\circ\mathcal E_{\mathrm{enc}},$$
--   where
--   $$\mathcal E_{\mathrm{enc}}(\rho_Q)=U(\rho_Q\otimes|0\rangle\langle0|_{\mathrm{rest}})U^\dagger,\qquad \mathcal D_{\mathrm{dec}}(\rho)=\operatorname{Tr}_{\mathrm{rest}}\bigl[U^\dagger\mathcal E_{\mathrm{dec}}(\rho)U\bigr].$$
--   It maps $2\times2$ matrices on the carrier qubit to $2\times2$ matrices.
--
--   **Formalization Note** $\operatorname{Tr}_{\mathrm{rest}}$ is the published partial trace `WildeQIT.partialTraceRight`, after reindexing $\mathcal H$ as $\mathcal H_Q\times\mathcal H_{\mathrm{rest}}$ by $x\mapsto(x_0,(x_1,\dots,x_{n-1}))$.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.18, eqs. (23)–(25), pp. 18–19 (PDF pp. 20–21)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit
import Definitions.Def_AutoQMem_Lindblad_CSSCode_decodeChannel
import Definitions.Def_WildeQIT_partialTrace
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Encoding map** `E_enc(ρ_Q) := U (ρ_Q ⊗ |0⟩⟨0|_rest) U†`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.18, eq. (24),
p. 19 (PDF 21). -/
def encode (Q : LogicalQubit C) (ρQ : Matrix (ZMod 2) (ZMod 2) ℂ) : Op (n' + 1) :=
  Q.U * embed0 ρQ * Q.Uᴴ

/-- **Decoding map** `D_dec(ρ) := Tr_rest[U† E_dec(ρ) U]`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.18, eq. (25),
p. 19 (PDF 21).

**Formalization Note.** `H` is reindexed as `H_Q × H_rest` by `x ↦ (x 0, Fin.tail x)`
(`Fin.consEquiv`), and `Tr_rest` is `WildeQIT.partialTraceRight`. -/
noncomputable def decode (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (ρ : Op (n' + 1)) : Matrix (ZMod 2) (ZMod 2) ℂ :=
  WildeQIT.partialTraceRight
    (Matrix.reindex (Fin.consEquiv fun _ => ZMod 2).symm (Fin.consEquiv fun _ => ZMod 2).symm
      (Q.Uᴴ * C.decodeChannel DX DZ ρ * Q.U))

/-- **Effective logical channel** `E_L[W_*] := D_dec ∘ W_* ∘ E_enc`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.18,
eq. (23), p. 18 (PDF 20). `W` is the physical evolution between encoding and readout. -/
noncomputable def effective (Q : LogicalQubit C) (DX : Decoder C.HX) (DZ : Decoder C.HZ)
    (W : Op (n' + 1) → Op (n' + 1)) (ρQ : Matrix (ZMod 2) (ZMod 2) ℂ) :
    Matrix (ZMod 2) (ZMod 2) ℂ :=
  Q.decode DX DZ (W (Q.encode ρQ))

end LogicalQubit

end AutoQMem.Lindblad


