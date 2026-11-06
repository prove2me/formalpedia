-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_codeInner
-- name    : AutoQMem_Lindblad_LogicalQubit_codeInner
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:59:42.944053+00:00
-- url     : https://prove2.me/theorems/aa028852-c044-4b24-b876-662d2ec1221a
-- title:
--   Mixed code state $\rho_{\mathrm{code}}$ and code-space inner product $\langle A,B\rangle_{\mathrm{code}}$
-- statement:
--   The **mixed code state** is the encoding of the maximally mixed carrier state,
--   $$\rho_{\mathrm{code}}=U\bigl(\tfrac12I_Q\otimes|0\rangle\langle0|_{\mathrm{rest}}\bigr)U^\dagger,$$
--   and the **code-space inner product** of observables $A,B$ is
--   $$\langle A,B\rangle_{\mathrm{code}}=\operatorname{Tr}(\rho_{\mathrm{code}}A^\dagger B).$$
--   The autocorrelations $\langle T_\sigma,\mathcal W^*(T_\sigma)\rangle_{\mathrm{code}}$ quantify the quantum memory.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.17, eqs. (21)–(22), p. 18 (PDF p. 20)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit_effective
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Mixed code state** `ρ_code := U(½ I_Q ⊗ |0⟩⟨0|_rest)U†`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.17, eq. (21),
p. 18 (PDF 20). -/
noncomputable def rhoCode (Q : LogicalQubit C) : Op (n' + 1) :=
  Q.encode ((1 / 2 : ℂ) • (1 : Matrix (ZMod 2) (ZMod 2) ℂ))

/-- **Code-space inner product** `⟨A, B⟩_code := Tr(ρ_code A† B)`. Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.17, eq. (22),
p. 18 (PDF 20). -/
noncomputable def codeInner (Q : LogicalQubit C) (A B : Op (n' + 1)) : ℂ :=
  (Q.rhoCode * Aᴴ * B).trace

end LogicalQubit

end AutoQMem.Lindblad


