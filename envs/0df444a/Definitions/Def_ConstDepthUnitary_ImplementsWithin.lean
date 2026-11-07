-- Prove2me | Definitions.Def_ConstDepthUnitary_ImplementsWithin
-- name    : ConstDepthUnitary_ImplementsWithin
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:24.455054+00:00
-- url     : https://prove2.me/theorems/f5f5f1b8-1d79-43a9-a36a-c3c587d6a8b2
-- title:
--   Implementing a unitary up to operator norm distance $\varepsilon$
-- statement:
--   A circuit $C$ on target register $S$ and ancillas $A$ implements $U$ up to $\varepsilon$ when
--   $$\bigl\|\,C\,(I\otimes|0\rangle)-(I\otimes|0\rangle)\,U\,\bigr\|\le\varepsilon,$$
--   which is Eq. (70) of the source: on every target input with the ancillas at zero, the output is $\varepsilon$-close to $U$ applied with the ancillas returned to zero.
--
--   **Formalization Note** The norm is the spectral operator norm of a rectangular matrix (`Matrix.Norms.L2Operator`), not an entrywise norm.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, Eq. (70), p.35

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_ancEmbed
open scoped Matrix.Norms.L2Operator

namespace ConstDepthUnitary

/-- `C` implements `U` up to operator norm distance `ε`, Eq. (70): `‖U ⊗ |0⟩ − C (I ⊗ |0⟩)‖ ≤ ε`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Theorem 6.1, Eq. (70), p.35.

**Formalization Note** The norm is the operator norm `Matrix.Norms.L2Operator` of a rectangular matrix. -/
def ImplementsWithin {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (C : Circuit (S ⊕ A)) (U : Matrix (S → Bool) (S → Bool) ℂ) (ε : ℝ) : Prop :=
  ‖C.matrix * ancEmbed S A - ancEmbed S A * U‖ ≤ ε

end ConstDepthUnitary


