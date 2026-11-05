-- Prove2me | Definitions.Def_RotationLadder_Protocol_cnotSecond
-- name    : RotationLadder_Protocol_cnotSecond
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:33:53.455093+00:00
-- url     : https://prove2.me/theorems/4f028f0b-63fa-4aad-b942-cc46b25be79a
-- title:
--   The gate $\Lambda(X)$ of Figs. 1 and 2, with the second wire as control
-- statement:
--   The two-qubit gate $\Lambda(X)$ of Figs. 1 and 2 acts on basis states by
--
--   $$|q_1,q_2\rangle\longmapsto|q_1\oplus q_2,\;q_2\rangle .$$
--
--   The second wire is the control and the first wire is the target.
--
--   **Formalization Note** The platform's `QAlgorithms.cnot` has its control on the first wire, so it is a different matrix.
-- source:
--   Duclos-Cianci, Svore, A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations, arXiv:1210.1980v1, Sec. I, unnumbered, p. 2 and Sec. II, unnumbered, pp. 2-3

import Mathlib

namespace RotationLadder.Protocol

/-- **The gate `Λ(X)` of Figs. 1 and 2.**
Duclos-Cianci, Svore, *A State Distillation Protocol to Implement Arbitrary Single-qubit Rotations*,
arXiv:1210.1980v1, Sec. I, p. 2 and Sec. II, pp. 2-3: `|q₁, q₂⟩ ↦ |q₁ ⊕ q₂, q₂⟩`.

**Formalization Note.** The **second** wire is the control and the first the target, as in both
figures and in the displays `|01⟩ → |11⟩`, `|11⟩ → |01⟩`, `|10⟩ → |10⟩`. The platform's
`QAlgorithms.cnot` has its control on the first wire, so it is not this gate. -/
def cnotSecond : Matrix (Bool × Bool) (Bool × Bool) ℂ :=
  Matrix.of fun p q => if p.1 = xor q.1 q.2 ∧ p.2 = q.2 then 1 else 0

end RotationLadder.Protocol


