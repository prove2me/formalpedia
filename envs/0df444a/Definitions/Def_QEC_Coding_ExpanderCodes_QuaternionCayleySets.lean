-- Prove2me | Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionCayleySets
-- name    : QEC_Coding_ExpanderCodes_QuaternionCayleySets
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-06T09:44:02.173585+00:00
-- url     : https://prove2.me/theorems/99b15107-fb6f-40df-a412-d4eccad172b5
-- title:
--   Quaternion Cayley Sets
-- statement:
--   Definitions and structural lemmas for Quaternion Cayley Sets, from The Lean-QECert contributors's pinned Lean-QECert development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/QudeLeap/Lean-QECert/blob/4a64933303628b4f94c4567347e86636853f64a4/QEC/Coding/ExpanderCodes/QuaternionCayleySets.lean

import Definitions.Def_QEC_Coding_ExpanderCodes_QuaternionGenerators
import Mathlib.GroupTheory.Subgroup.Centralizer
set_option autoImplicit false
namespace QEC.Coding.ExpanderCodes.QuaternionGenerators
universe u
variable {K : Type u} [Field K]
def projectiveAlpha (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    ProjectiveGroup epsilon y :=
  QuotientGroup.mk' _ (alphaUnit epsilon y hEpsilon)
def quadraticTorus (epsilon y : K) (hEpsilon : epsilon ≠ 0) :
    Subgroup (ProjectiveGroup epsilon y) :=
  (Subgroup.centralizer {alphaUnit epsilon y hEpsilon}).map
    (QuotientGroup.mk' _)
section Group
variable {H : Type*} [Group H]
def conjugacySet (T : Subgroup H) (a : H) : Set H :=
  Set.range (fun t : T => (t : H) * a * (t : H)⁻¹)
end Group
def leftSet (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Set (ProjectiveGroup epsilon y) :=
  conjugacySet (quadraticTorus epsilon y hEpsilon)
    (projectiveBase epsilon y hY hOne)
def rightSet (epsilon y : K) (hEpsilon : epsilon ≠ 0)
    (hY : y ≠ 0) (hOne : 1 + y ≠ 0) : Set (ProjectiveGroup epsilon y) :=
  conjugacySet (quadraticTorus epsilon y hEpsilon)
    (projectivePrime epsilon y hEpsilon hY hOne)
end QEC.Coding.ExpanderCodes.QuaternionGenerators


