-- Prove2me | Definitions.Def_SingleInteraction_XYIntInstance
-- name    : SingleInteraction_XYIntInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:53:42.208188+00:00
-- url     : https://prove2.me/theorems/c5aeaf27-8475-4bb9-ba68-f97f685adc16
-- title:
--   Inputs of the positive-integer-weight XY problem
-- statement:
--   An input of the positive-integer-weight XY problem: the number of qubits $n$ (unary), a list of terms $(u,v,w)$ with $w$ a natural number in binary, and thresholds $a,b$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- An input of the positive-integer-weight XY problem (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55): the number of qubits
`n`, a list of terms `(u, v, w)` with integer coupling strength `w`, and thresholds `a, b`.

**Formalization Note** Weights are natural numbers in binary; thresholds are binary rationals. The
constraints are in `XYIntInstance.Valid`. -/
structure XYIntInstance where
  /-- the number of qubits -/
  n : ℕ
  /-- the terms `(u, v, w)` -/
  terms : List (ℕ × ℕ × ℕ)
  /-- the YES threshold -/
  a : BinaryRational
  /-- the NO threshold -/
  b : BinaryRational

/-- The bijection of instances with their components. -/
def xyIntEquiv : XYIntInstance ≃ ℕ × (List (ℕ × ℕ × ℕ) × (BinaryRational × BinaryRational)) where
  toFun x := (x.n, x.terms, x.a, x.b)
  invFun y := ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨n, t, a, b⟩; rfl

/-- The binary code of an instance, built from the published combinators. -/
def xyIntCodec : Codec XYIntInstance :=
  BinaryEncoding.equiv
    (pair unary (pair (BinaryEncoding.list (pair natural (pair natural natural)))
      (pair binaryRationalCodec binaryRationalCodec)))
    xyIntEquiv

end SingleInteraction


