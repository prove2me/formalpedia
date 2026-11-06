-- Prove2me | Definitions.Def_QEC_Coding_HypergraphProduct_Distance
-- name    : QEC_Coding_HypergraphProduct_Distance
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-05T13:51:24.999196+00:00
-- url     : https://prove2.me/theorems/056a31a9-6f24-4ec8-885b-7df9e6079fd7
-- title:
--   Distance
-- statement:
--   Definitions and structural lemmas for Distance, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/HypergraphProduct/Distance.lean

import Definitions.Def_QEC_Coding_HypergraphProduct_Parameters
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.HypergraphProduct
universe u v
def finitePredicateMinimum
    {alpha : Type u} [Fintype alpha] [DecidableEq alpha]
    (P : alpha → Prop) [DecidablePred P] (weight : alpha → Nat) : WithTop Nat :=
  Finset.univ.inf fun x => if P x then (weight x : WithTop Nat) else ⊤
def extendedMinimumDistance
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (C : LinearCode F iota) : WithTop Nat := by
  classical
  exact finitePredicateMinimum
    (fun x : Word F iota => x ∈ C.carrier ∧ x ≠ 0) HammingWeight
def IsCSSLogical
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota]
    (xCode zCode : LinearCode F iota) (x : Word F iota) : Prop :=
  (x ∈ zCode.dual.carrier ∧ x ∉ xCode.carrier) ∨
    (x ∈ xCode.dual.carrier ∧ x ∉ zCode.carrier)
def extendedAlgebraicCSSMinimumDistance
    {F : Type u} {iota : Type v}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype iota] [DecidableEq iota]
    (xCode zCode : LinearCode F iota) : WithTop Nat := by
  classical
  exact finitePredicateMinimum (IsCSSLogical xCode zCode) HammingWeight
end QEC.Coding.HypergraphProduct


