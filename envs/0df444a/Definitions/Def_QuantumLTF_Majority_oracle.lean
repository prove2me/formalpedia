-- Prove2me | Definitions.Def_QuantumLTF_Majority_oracle
-- name    : QuantumLTF_Majority_oracle
-- status  : Definition
-- author  : @stockfish-soup
-- created : 2026-11-14T17:47:47.824974+00:00
-- url     : https://prove2.me/theorems/b38fdd3d-f2ba-4559-9f31-a46bd2ce34ab
-- title:
--   Boolean membership oracle for a hidden Majority support
-- statement:
--   For a hidden nonempty support $A\subseteq[n]$, define the Majority label on $x\in\{-1,1\}^n$ by $+1$ when at least half of the coordinates in $A$ equal $+1$, with ties labeled $+1$, and by $-1$ otherwise. The coherent membership oracle leaves $x$ unchanged and XORs a target qubit with the bit encoding this label.
--
--   This is the oracle used throughout Section 4 for learning the hidden support of an equal-weight homogeneous linear threshold function.
--
--   **Formalization Note** Boolean `true` on an input wire encodes $+1$; on the target wire, `false` encodes label $+1$ and `true` encodes $-1$.
-- source:
--   Krivcenko, Nguyen, de Wolf, Fast Quantum Algorithms for Learning Linear Threshold Functions, arXiv:2609.40331v3, Section 4, definition preceding Theorem 4.1, p. 39 (PDF p. 40)

import Mathlib

namespace QuantumLTF.Majority

/-- The Boolean bit encoding the `{-1,+1}` Majority label on a hidden support `A`:
`false` encodes `+1`, and `true` encodes `-1`. -/
def majorityBit {n : ℕ} (A : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (2 * (A.filter fun i => x i).card < A.card)

/-- The coherent Boolean membership oracle for Majority on the hidden support `A`.
The first `n` wires hold `x`; the last wire is XORed with `majorityBit A x`. -/
def majorityOracle {n : ℕ} (A : Finset (Fin n)) :
    Matrix (Fin (n + 1) → Bool) (Fin (n + 1) → Bool) ℂ :=
  Matrix.of fun y z =>
    if (∀ i : Fin n, y i.castSucc = z i.castSucc) ∧
        y (Fin.last n) = xor (z (Fin.last n)) (majorityBit A fun i => z i.castSucc)
    then 1 else 0

end QuantumLTF.Majority


