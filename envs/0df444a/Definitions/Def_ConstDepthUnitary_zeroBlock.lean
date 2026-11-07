-- Prove2me | Definitions.Def_ConstDepthUnitary_zeroBlock
-- name    : ConstDepthUnitary_zeroBlock
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:47:07.413979+00:00
-- url     : https://prove2.me/theorems/f35b1f0e-7cb3-4dcb-9013-deaf5650b266
-- title:
--   The zero-ancilla block of a circuit
-- statement:
--   The zero-ancilla block of a circuit $C$ is the matrix
--   $$A=(I\otimes\langle0|)\,C\,(I\otimes|0\rangle)$$
--   on the target register. It need not be unitary. Theorem 7.1 is a statement about this block.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 7.1, p.43

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_ancEmbed
open scoped Matrix

namespace ConstDepthUnitary

/-- The zero-ancilla block `(I ⊗ ⟨0|) C (I ⊗ |0⟩)` of a circuit.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 7.1, p.43. -/
noncomputable def zeroBlock {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (C : Circuit (S ⊕ A)) : Matrix (S → Bool) (S → Bool) ℂ :=
  (ancEmbed S A)ᴴ * C.matrix * ancEmbed S A

end ConstDepthUnitary


