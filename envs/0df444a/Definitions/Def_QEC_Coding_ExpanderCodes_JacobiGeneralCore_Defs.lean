-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
-- name    : QEC_Coding_ExpanderCodes_JacobiGeneralCore_Defs
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T08:32:42.044592+00:00
-- url     : https://prove2.me/theorems/af0bc396-0cd6-4260-91cc-112e04b08031
-- title:
--   Defs
-- statement:
--   Definitions and structural lemmas for Defs, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/JacobiGeneralCore/Defs.lean

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Defs.Filter
set_option autoImplicit false
open Finset Filter
open scoped Topology
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore.Nat
namespace QEC.Coding.TannerLiftedProduct.JacobiGeneralCore
variable {R : Type*}
def qPochhammer [CommRing R] (a q : R) (n : ℕ) : R :=
  ∏ k ∈ range n, (1 - a * q ^ k)
def qBinom [CommRing R] : ℕ → ℕ → R → R
  | 0,     0,     _ => 1
  | 0,     _ + 1, _ => 0
  | _ + 1, 0,     _ => 1
  | n + 1, k + 1, q => qBinom n (k + 1) q + q ^ (n - k) * qBinom n k q
end QEC.Coding.TannerLiftedProduct.JacobiGeneralCore


