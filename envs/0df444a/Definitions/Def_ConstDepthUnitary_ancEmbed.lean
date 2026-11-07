-- Prove2me | Definitions.Def_ConstDepthUnitary_ancEmbed
-- name    : ConstDepthUnitary_ancEmbed
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:43:20.034046+00:00
-- url     : https://prove2.me/theorems/d5003800-3e59-4a32-8e8a-78d585d34993
-- title:
--   The ancilla embedding $I\otimes|0\rangle$
-- statement:
--   For a target register $S$ and an ancilla register $A$, the isometry
--   $$I\otimes|0\rangle:\ |x\rangle\mapsto|x\rangle_S\,|0\cdots0\rangle_A$$
--   as a rectangular matrix: the entry at $(y,x)$ is $1$ when $y|_S=x$ and $y|_A=0$, and $0$ otherwise. It is the initialisation used in Eq. (70) and Theorem 7.1.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, Eq. (70), p.35

import Mathlib

namespace ConstDepthUnitary

/-- The embedding `I ⊗ |0⟩` of the target register `S` into the target and ancilla registers `S ⊕ A`:
the entry `(y, x)` is `1` if `y` restricts to `x` on `S` and vanishes on `A`, and `0` otherwise.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, Eq. (70), p.35. -/
noncomputable def ancEmbed (S A : Type) [Fintype S] [DecidableEq S] [Fintype A] :
    Matrix (S ⊕ A → Bool) (S → Bool) ℂ :=
  Matrix.of fun y x => if (fun s => y (Sum.inl s)) = x ∧ ∀ a, y (Sum.inr a) = false then 1 else 0

end ConstDepthUnitary


