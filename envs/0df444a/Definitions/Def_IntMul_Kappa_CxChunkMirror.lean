-- Prove2me | Definitions.Def_IntMul_Kappa_CxChunkMirror
-- name    : IntMul_Kappa_CxChunkMirror
-- status  : Definition
-- author  : @scuba8684
-- created : 2026-11-26T15:14:42.349182+00:00
-- url     : https://prove2.me/theorems/252902ea-79a3-47d4-9743-a881863bcb21
-- title:
--   Reverse traversal of a framed complex-network program
-- statement:
--   Let $P$ be a list of round-six complex-network chunks on a finite role set. Each chunk changes selected roles to a common binary-subspace label, then applies a list of scalar gates. For a label map $f$, the construction $B_f(P)$ visits the chunks in reverse order.
--
--   In each chunk it emits the gates in reverse order at the mapped common label, negating an off-diagonal shear and retaining the coefficient of a diagonal gate. It then returns each moved role to its mapped former label, processing moves in reverse order. This defines the program used to transport stage validity and child widths through orthogonal complementation.
-- source:
--   Formal construction and proof in the round-eight cxNetR8G trial. Stage-two complement time-reversal: S. Jain, integer-mult-kappa, commit 5868dc701a9bec375c9dc5391d992ab3b8c35f3f, https://github.com/Swapnil-jain/integer-mult-kappa/blob/5868dc701a9bec375c9dc5391d992ab3b8c35f3f/README.md#L61-L69 . Round-six chunk, validity and width definitions: Def_IntMul_Kappa_R6_Defs24, source module Solutions.R6CxNetSim, lines 143–229. Elementary append and finite-rank proof arguments follow xuanji’s accepted round-six proof, https://prove2.me/api/v1/submissions/534cb506-9a9f-4445-8a59-416047960d9d/solution .

import Definitions.Def_IntMul_Kappa_R6_Defs24

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CxChunkMirror

open IntMul.Kappa.R6.Cx

variable {R : Type} [DecidableEq R] {m n : ℕ}

/-- Off-diagonal shears change sign on reversal. A diagonal gate keeps its
coefficient, including the round-six sign gate with coefficient -2. -/
def inverseSignedGate (o : GOp R) : GOp R :=
  if o.dst = o.src then o else {o with c := -o.c}

/-- Undo one move by making its former label the destination. -/
def backwardMove (f : Lab m → Lab n) (v : Lab m) (p : R × Lab m) : GChunk R n :=
  ⟨f p.2, [(p.1, f v)], []⟩

/-- Distinct wires may have different former labels. Emit their return moves separately. -/
def backwardMoves (f : Lab m → Lab n) (v : Lab m) : List (R × Lab m) → List (GChunk R n)
  | [] => []
  | p :: ps => backwardMoves f v ps ++ [backwardMove f v p]

/-- A round-six chunk moves its wires first, then operates on them. Its mirror
starts with the inverse gates in the current frame and only then moves the wires back. -/
def backwardChunk (f : Lab m → Lab n) (c : GChunk R m) : List (GChunk R n) :=
  ⟨f c.V, [], c.ops.reverse.map inverseSignedGate⟩ :: backwardMoves f c.V c.mv

def backwardProgram (f : Lab m → Lab n) (cs : List (GChunk R m)) : List (GChunk R n) :=
  cs.reverse.flatMap (backwardChunk f)

end CxChunkMirror


