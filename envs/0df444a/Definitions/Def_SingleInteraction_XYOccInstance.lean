-- Prove2me | Definitions.Def_SingleInteraction_XYOccInstance
-- name    : SingleInteraction_XYOccInstance
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T07:54:30.940388+00:00
-- url     : https://prove2.me/theorems/65a7acc4-796f-48cc-b863-c8168615899a
-- title:
--   Inputs of the XY occurrence-list problem
-- statement:
--   An input of the XY occurrence-list problem: the number of qubits $n$ (unary), a list of occurrences $(u_e,v_e)$, repeats allowed, and thresholds $a,b$.
-- source:
--   Hecker, The Complexity of Single-Interaction Hamiltonians, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55

import Mathlib
import Definitions.Def_ContinuumCoulombHardness

open OAI.ContinuumCoulomb OAI.ContinuumCoulomb.BinaryEncoding

namespace SingleInteraction

/-- An input of the XY occurrence-list problem (Hecker, *The Complexity of Single-Interaction Hamiltonians*, arXiv:2609.39592 (held version, sha256 19ddc444…), Lemma 61, p.55: "the Hamiltonian may be
specified as a polynomial-length list of interaction occurrences, `K = Σ_{e=1}^M K_{u_e v_e}`, where repeated
occurrences on the same qubit pair are permitted"): the number of qubits `n`, the list of occurrences
`(u_e, v_e)`, and thresholds `a, b`. -/
structure XYOccInstance where
  /-- the number of qubits -/
  n : ℕ
  /-- the occurrences `(u_e, v_e)`, repeats allowed -/
  pairs : List (ℕ × ℕ)
  /-- the YES threshold -/
  a : BinaryRational
  /-- the NO threshold -/
  b : BinaryRational

/-- The bijection of instances with their components. -/
def xyOccEquiv : XYOccInstance ≃ ℕ × (List (ℕ × ℕ) × (BinaryRational × BinaryRational)) where
  toFun x := (x.n, x.pairs, x.a, x.b)
  invFun y := ⟨y.1, y.2.1, y.2.2.1, y.2.2.2⟩
  left_inv x := by cases x; rfl
  right_inv y := by rcases y with ⟨n, t, a, b⟩; rfl

/-- The binary code of an instance, built from the published combinators. -/
def xyOccCodec : Codec XYOccInstance :=
  BinaryEncoding.equiv
    (pair unary (pair (BinaryEncoding.list (pair natural natural))
      (pair binaryRationalCodec binaryRationalCodec)))
    xyOccEquiv

end SingleInteraction


