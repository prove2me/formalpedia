-- Prove2me | Definitions.Def_ThreeColorFloodIt_FixedHeight_machine
-- name    : ThreeColorFloodIt_FixedHeight_machine
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T11:50:39.344209+00:00
-- url     : https://prove2.me/theorems/2a8c127a-d57e-4e1f-bc70-d74755661fdd
-- title:
--   Binary board and witness encodings on a shared deterministic machine
-- statement:
--   The shared finite-state, finite-alphabet multitape machine executes one charged transition per step. Inputs consist of binary height and width followed by all target colors in row-major order; separators delimit natural numbers. Outputs contain a binary move count and a list of zero-based row, column and color triples.
--
--   Exact output means
--   $$|L|=d=F(P_k\square P_n,f),\qquad L\text{ is a legal solution}.$$
--   Optimality is tested against every legal solution and is never an input certificate. Coordinates occupy $O(\log(N+1))$ bits and a shortest witness contains at most $N-1$ moves, a consequence to prove. The XP predicate uses one machine for every height, allowing a height-dependent polynomial coefficient and exponent. This interface charges preprocessing, optimization and writing the entire witness.
-- source:
--   Zhou, Three-Color Free-Flood-It on Fixed-Height Grids Is Polynomial-Time Solvable, STOC 2027 submission #31, supplied 2026 preprint, SHA-256 222ec38f7c30952eda9e86f87b16e8d7dfc93aa0b6b9705ac931e1b56017d280, printed p. 19 (PDF 20), §5.1, final paragraph; §4.6 recovery; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/31.pdf Additional location: printed p. 17 (PDF 18), §4.6 (witness recovery); printed p. 4 (PDF 5), §2.2 (legal moves and optimum).

import Definitions.Def_ThreeColorFloodIt_FixedHeight_game
import Definitions.Def_IntMul_MultitapeWords

set_option autoImplicit false

namespace ThreeColorFloodIt.FixedHeight

/-- A binary natural with at least one bit. Separators make a list of these
words self-delimiting; no unary-coordinate overhead is hidden in the encoding. -/
def natBits (a : ℕ) : List Bool := IntMul.bin (IntMul.lg (a + 1)) a
def encodeNaturals (xs : List ℕ) : List (Option Bool) :=
  IntMul.joinSep (xs.map fun x => IntMul.bits (natBits x))

def boardInput {k n : ℕ} (f : Board k n) : List (Option Bool) :=
  encodeNaturals (k :: n ::
    (List.ofFn fun r => List.ofFn fun j => (f (r, j)).val).flatten)

def floodingOutput {k n : ℕ} (d : ℕ) (ms : List (Move (Cell k n) (Fin 3))) :
    List (Option Bool) :=
  encodeNaturals (d :: ms.flatMap fun m => [m.1.1.val, m.1.2.val, m.2.val])

/-- Correctness of the two returned objects, with optimality as a conclusion. -/
def ExactOutput {k n : ℕ} (f : Board k n) (d : ℕ)
    (ms : List (Move (Cell k n) (Fin 3))) : Prop :=
  Solves (Grid k n) f ms ∧ ms.length = d ∧
    (∀ qs, Solves (Grid k n) f qs → d ≤ qs.length) ∧
    floodOpt (Grid k n) f = (d : WithTop ℕ)

def ComputesFloodingAt (A : IntMul.MultitapeTM) (k n : ℕ)
    (bound : ℕ) : Prop :=
  ∀ f : Board k n, ∃ t d ms, t ≤ bound ∧
    A.HaltsWithOutputW (boardInput f) t (floodingOutput d ms) ∧ ExactOutput f d ms

/-- XP uses the same finite deterministic program for every height. -/
def FloodingXP (A : IntMul.MultitapeTM) : Prop :=
  ∀ k : ℕ, 0 < k → ∃ c e : ℕ, 0 < c ∧
    ∀ n : ℕ, 0 < n → ComputesFloodingAt A k n (c * n ^ e)

end ThreeColorFloodIt.FixedHeight


