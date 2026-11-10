-- Prove2me | Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
-- name    : QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Incidence
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-10T01:54:56.570966+00:00
-- url     : https://prove2.me/theorems/7f25c4f3-ebda-4642-85e0-8503132570df
-- title:
--   Incidence
-- statement:
--   Definitions and structural lemmas for Incidence, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/FiniteAlternatingConstruction/CSSHamiltonian/Incidence.lean

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_CSSHamiltonian_Rows
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
set_option autoImplicit false
noncomputable section
namespace QEC.Coding.BDL26CSSHamiltonian
open Classical BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26BoundedValence PauliSymplectic
open scoped BigOperators
variable (S : OddScale) (n : Nat)
def checkSupport (j : Sum (ZLabel S n) (XLabel S n)) : Finset (Physical S n) := support (check S n j)
def incident (q : Physical S n) : Finset (Sum (ZLabel S n) (XLabel S n)) :=
  Finset.univ.filter (fun j => q ∈ checkSupport S n j)
def region (q : Physical S n) : Finset (Physical S n) :=
  {q} ∪ (incident S n q).biUnion (checkSupport S n)
end QEC.Coding.BDL26CSSHamiltonian


