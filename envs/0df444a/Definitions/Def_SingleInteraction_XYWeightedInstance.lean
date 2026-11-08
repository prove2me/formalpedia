-- Prove2me | Definitions.Def_SingleInteraction_XYWeightedInstance
-- name    : SingleInteraction_XYWeightedInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:41.838245+00:00
-- url     : https://prove2.me/theorems/b0b89414-c5c0-4431-b1c3-7069c3617039
-- title:
--   Inputs of the weighted XY problem
-- statement:
--   An input of the $\{X\otimes X+Y\otimes Y\}$-Hamiltonian problem: the number of qubits $n$ (unary), a list of terms $(u,v,\alpha)$ with $\alpha$ a binary rational, and thresholds $a,b$, with a uniquely decodable binary code.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.25

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- An input of the weighted `{X⊗X + Y⊗Y}`-Hamiltonian problem (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), §2.3.5, p.25): the number of
qubits `n`, a list of terms `(u, v, α)` (the interaction on qubits `u, v` with coefficient `α`), and
thresholds `a, b`.

**Formalization Note** Coefficients and thresholds are binary rationals. The constraints are in
`XYWeightedInstance.Valid`. -/
structure XYWeightedInstance where
  /-- the number of qubits -/
  n : ℕ
  /-- the terms `(u, v, α)` -/
  terms : List (ℕ × ℕ × BinaryRational)
  /-- the YES threshold -/
  a : BinaryRational
  /-- the NO threshold -/
  b : BinaryRational

/-- The bijection of instances with their components. -/
def xyWeightedEquiv :
    XYWeightedInstance ≃ ℕ × (List (ℕ × ℕ × BinaryRational) × (BinaryRational × BinaryRational)) where
  toFun x := (x.n, x.terms, x.a, x.b)
  invFun y := ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨n, t, a, b⟩; rfl

/-- The binary code of an instance (`n` in unary, then the terms and thresholds), built from the published
combinators of `OAI.ContinuumCoulomb.BinaryEncoding`. -/
def xyWeightedCodec : Codec XYWeightedInstance :=
  BinaryEncoding.equiv
    (pair unary (pair (BinaryEncoding.list (pair natural (pair natural binaryRationalCodec)))
      (pair binaryRationalCodec binaryRationalCodec)))
    xyWeightedEquiv

end SingleInteraction


