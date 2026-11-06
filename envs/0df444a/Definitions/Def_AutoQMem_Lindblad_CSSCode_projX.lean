-- Prove2me | Definitions.Def_AutoQMem_Lindblad_CSSCode_projX
-- name    : AutoQMem_Lindblad_CSSCode_projX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:55:40.102169+00:00
-- url     : https://prove2.me/theorems/e71dbf59-8f66-4a1a-82b8-4a611ccbd079
-- title:
--   Syndrome projectors $\Pi^X_s$, $\Pi^Z_s$ and the code projector $\Pi_{\mathrm{code}}$
-- statement:
--   For a syndrome string $s\in\mathbb F_2^{m_X}$, the **X-syndrome projector** is
--   $$\Pi^X_s=\prod_{a=1}^{m_X}\frac{I+(-1)^{s_a}S^X_a}{2},$$
--   the projector onto the states with X-syndrome $s$; $\Pi^Z_s$ is defined in the same way from the Z-type stabilizers. The **code-space projector** is $\Pi_{\mathrm{code}}=\Pi^X_0\Pi^Z_0$, the projector onto the joint $+1$ eigenspace of all stabilizers.
--
--   $\Pi^X_s=0$ for $s\notin\Sigma_X$. These projectors define the decoding channel, the decoded logical observables and the syndrome eigenvalue functions.
--
--   **Formalization Note** The factors commute but matrix multiplication is not commutative in general, so the product is taken in the order $a=1,\dots,m_X$; any order gives the same operator.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.3, eq. (5), p. 14 (PDF p. 16); Definition 2.1, p. 13

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_CSSCode
open Matrix

namespace AutoQMem.Lindblad

namespace CSSCode

variable {n mX mZ : ℕ}

/-- **X-syndrome projector.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 2.3, eq. (5), p. 14 (PDF 16):
`Π^X_s := ∏_{a=1}^{m_X} (I + (-1)^{s_a} S^X_a)/2`.

**Formalization Note.** The factors commute, but `Matrix` multiplication is not commutative, so the
product is the ordered list product over `a = 0, …, m_X - 1`; any order gives the same operator.
It is defined for every `s ∈ 𝔽₂^{m_X}` (it is `0` off `Σ_X`, Remark 2.15). -/
noncomputable def projX (C : CSSCode n mX mZ) (s : Fin mX → ZMod 2) : Op n :=
  (List.ofFn fun a => (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (s a).val • C.stabX a)).prod

/-- **Z-syndrome projector** `Π^Z_s := ∏_b (I + (-1)^{s_b} S^Z_b)/2` (Definition 2.3, "defined
symmetrically"). -/
noncomputable def projZ (C : CSSCode n mX mZ) (s : Fin mZ → ZMod 2) : Op n :=
  (List.ofFn fun b => (1 / 2 : ℂ) • (1 + (-1 : ℂ) ^ (s b).val • C.stabZ b)).prod

/-- **Code-space projector** `Π_code`, the projector onto the joint +1 eigenspace of all
stabilizers (Definition 2.1): `Π_code = Π^X_0 Π^Z_0`. -/
noncomputable def codeProj (C : CSSCode n mX mZ) : Op n := C.projX 0 * C.projZ 0

end CSSCode

end AutoQMem.Lindblad


