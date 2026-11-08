-- Prove2me | Definitions.Def_SingleInteraction_SIHInstance
-- name    : SingleInteraction_SIHInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:41.111358+00:00
-- url     : https://prove2.me/theorems/aece2f86-687c-492b-a854-ecabcb02a3e1
-- title:
--   Inputs of $\mathrm{SIH}_k$
-- statement:
--   An input of the single-interaction problem consists of the system size $n$ (in unary), a list $L$ of ordered tuples of physical qubits (each a list of qubit indices), and two thresholds $a,b$ (binary rationals). Its binary code writes $n$ in unary, then the tuples and the thresholds in a uniquely decodable code.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30 (Problem Input)

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- An input of the single-interaction problem (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Definition 31, pp.29–30, "Problem Input"):
the system size `n`, a list `L` of ordered tuples of physical qubits, and two thresholds `a, b`.

**Formalization Note** A tuple `(v₁, …, v_k)` is the list `[v₁, …, v_k]` of qubit indices in
`{0, …, n−1}`; the thresholds are binary rationals (`OAI.ContinuumCoulomb.BinaryRational`, numerator in
`ℤ`, denominator in `ℕ`). The constraints of the definition (tuple length, ranges, distinctness, bit
lengths and gap) are `SIHInstance.Valid`. -/
structure SIHInstance where
  /-- the system size `n` (number of physical qubits) -/
  n : ℕ
  /-- the ordered interaction tuples -/
  tuples : List (List ℕ)
  /-- the YES threshold -/
  a : BinaryRational
  /-- the NO threshold -/
  b : BinaryRational

/-- The bijection of instances with their components. -/
def sihInstanceEquiv : SIHInstance ≃ ℕ × (List (List ℕ) × (BinaryRational × BinaryRational)) where
  toFun x := (x.n, x.tuples, x.a, x.b)
  invFun y := ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨n, t, a, b⟩; rfl

/-- The binary code of an instance: `n` in unary, then the tuples (a length-prefixed list of
length-prefixed lists of binary naturals), then `a` and `b` as binary rationals. Built from the
published combinators of `OAI.ContinuumCoulomb.BinaryEncoding`, so it is uniquely decodable. -/
def sihCodec : Codec SIHInstance :=
  BinaryEncoding.equiv
    (pair unary (pair (BinaryEncoding.list (BinaryEncoding.list natural))
      (pair binaryRationalCodec binaryRationalCodec)))
    sihInstanceEquiv

end SingleInteraction


