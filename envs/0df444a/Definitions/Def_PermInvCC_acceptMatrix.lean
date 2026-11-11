-- Prove2me | Definitions.Def_PermInvCC_acceptMatrix
-- name    : PermInvCC_acceptMatrix
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T20:24:07.596359+00:00
-- url     : https://prove2.me/theorems/4f138df4-e520-4d0a-9fa9-f684c229c8b9
-- title:
--   Acceptance matrix $A(y,x)$
-- statement:
--   The **acceptance matrix** of a protocol has rows indexed by Bob's inputs $y$, columns by Alice's inputs $x$, and entry $A(y,x)$ the acceptance probability on $(x,y)$. Theorem B.3 factorizes it.
-- source:
--   Huang and Ye, Quantum Advantage of Permutation-Invariant Functions in Communication Complexity, arXiv:2609.40116 (held version, sha256 fe1797dd…), Theorem B.3, p.43

import Mathlib
import Definitions.Def_PermInvCC_EntQProtocol

namespace PermInvCC

/-- The **acceptance matrix** `A(y, x)` of a protocol (Y. Huang and Z. Ye, arXiv:2609.40116, held
version sha256 fe1797dd…, Theorem B.3, p.43): rows indexed by Bob's inputs, columns by Alice's,
entries the acceptance probabilities. -/
noncomputable def acceptMatrix {X Y : Type} (P : EntQProtocol X Y) : Matrix Y X ℝ :=
  fun y x => P.acceptProb x y

end PermInvCC


