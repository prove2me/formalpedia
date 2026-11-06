-- Prove2me | Definitions.Def_AutoQMem_Lindblad_LogicalQubit_inVX
-- name    : AutoQMem_Lindblad_LogicalQubit_inVX
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:58:09.656216+00:00
-- url     : https://prove2.me/theorems/356a5a93-0bd0-418e-874b-fb12202a3763
-- title:
--   Logical sector subspaces $V_X$, $V_Z$
-- statement:
--   The **logical sector subspaces** are
--   $$V_X=\operatorname{span}\{\bar XA\mid A\in\mathcal A_X\},\qquad V_Z=\operatorname{span}\{\bar ZB\mid B\in\mathcal A_Z\}.$$
--   Since $\mathcal A_X$ is a linear space, $V_X=\{\bar XA\mid A\in\mathcal A_X\}$. The decoded logical observables lie in these subspaces, and the Heisenberg dynamics of a syndrome-based Lindbladian preserves them.
-- source:
--   Drechsler, Oreg, Aharonov, Autonomous Quantum Memories from Classical Stochastic Processes, arXiv:2610.05589 (PDF of 2026-11-03), Definition 4.3, eq. (83), p. 33 (PDF p. 35)

import Mathlib
import Definitions.Def_AutoQMem_Lindblad_LogicalQubit
open Matrix

namespace AutoQMem.Lindblad

namespace LogicalQubit

variable {n' mX mZ : ℕ} {C : CSSCode (n' + 1) mX mZ}

/-- **Membership in the logical sector subspace `V_X`.** Drechsler, Oreg, Aharonov, *Autonomous Quantum Memories from Classical Stochastic Processes*,
arXiv:2610.05589 (PDF of 2026-11-03), Definition 4.3, eq. (83), p. 33
(PDF 35): `V_X := span{X̄ A | A ∈ A_X}`.

**Formalization Note.** Since `A_X` is a subspace, the span is `{X̄ A | A ∈ A_X}` itself. -/
def inVX (Q : LogicalQubit C) (O : Op (n' + 1)) : Prop :=
  ∃ A ∈ C.algX, O = pauliX Q.lX * A

/-- **Membership in `V_Z := span{Z̄ B | B ∈ A_Z}`** (Definition 4.3, eq. (83)). -/
def inVZ (Q : LogicalQubit C) (O : Op (n' + 1)) : Prop :=
  ∃ B ∈ C.algZ, O = pauliZ Q.lZ * B

end LogicalQubit

end AutoQMem.Lindblad


