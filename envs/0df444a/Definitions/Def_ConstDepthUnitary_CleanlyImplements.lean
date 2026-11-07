-- Prove2me | Definitions.Def_ConstDepthUnitary_CleanlyImplements
-- name    : ConstDepthUnitary_CleanlyImplements
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T02:46:20.100273+00:00
-- url     : https://prove2.me/theorems/b4130e2a-26d7-4dfb-9bcc-c1c6a5564e55
-- title:
--   Clean exact implementation
-- statement:
--   A circuit $C$ on target register $S$ and ancillas $A$ is a **clean, exact implementation** of $U$ when
--   $$C\,(I\otimes|0\rangle)=(I\otimes|0\rangle)\,U.$$
--   All ancillas start and end at $|0\rangle$, on every input of the target register, and no error is allowed.
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Corollary 7.2, p.43; Eq. (70), p.35

import Mathlib
import Definitions.Def_ConstDepthUnitary_Circuit
import Definitions.Def_ConstDepthUnitary_ancEmbed

namespace ConstDepthUnitary

/-- `C` is a clean, exact implementation of `U`: `C (I ⊗ |0⟩) = (I ⊗ |0⟩) U`, so that on every input of
the target register with the ancillas at `|0⟩`, it applies `U` and returns the ancillas to `|0⟩`.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Corollary 7.2, p.43 ("clean, exact implementation"); Eq. (70), p.35 with `ε = 0`. -/
def CleanlyImplements {S A : Type} [Fintype S] [DecidableEq S] [Fintype A] [DecidableEq A]
    (C : Circuit (S ⊕ A)) (U : Matrix (S → Bool) (S → Bool) ℂ) : Prop :=
  C.matrix * ancEmbed S A = ancEmbed S A * U

end ConstDepthUnitary


