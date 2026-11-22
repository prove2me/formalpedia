-- Prove2me | Definitions.Def_LeanPool_QECCertificates_GF2_Membership
-- name    : LeanPool_QECCertificates_GF2_Membership
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T11:45:23.916939+00:00
-- url     : https://prove2.me/theorems/c15fa94e-2d60-42c8-bae7-984c9706485f
-- title:
--   Membership
-- statement:
--   Definitions and structural lemmas for Membership, from Shuoming An; LeanPool contributors's pinned Quantum code certificates and hypergraph-product theory development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/QECCertificates/GF2/Membership.lean

module
public import Definitions.Def_LeanPool_QECCertificates_GF2_RowReduce
public import Definitions.Def_LeanPool_QECCertificates_RowspaceKernel
public import Theorems.Thm_QECCertificates_reduceAgainst_cons

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace QECCertificates
open scoped BigOperators
variable {n : ℕ}
lemma reduceAgainst_add (D : List (PivRow n)) :
    ∀ u v : Vec n, reduceAgainst D (u + v) = reduceAgainst D u + reduceAgainst D v := by
  induction D with
  | nil => intro u v; rfl
  | cons r D ih =>
      intro u v
      rw [reduceAgainst_cons, reduceAgainst_cons, reduceAgainst_cons]
      have harg : u + v + ((u + v) r.2) • r.1
          = (u + (u r.2) • r.1) + (v + (v r.2) • r.1) := by
        rw [Pi.add_apply, add_smul]
        ac_rfl
      rw [harg]
      exact ih _ _
lemma reduceAgainst_smul (D : List (PivRow n)) :
    ∀ (c : ZMod 2) (v : Vec n), reduceAgainst D (c • v) = c • reduceAgainst D v := by
  induction D with
  | nil => intro c v; rfl
  | cons r D ih =>
      intro c v
      rw [reduceAgainst_cons, reduceAgainst_cons]
      have harg : c • v + ((c • v) r.2) • r.1 = c • (v + (v r.2) • r.1) := by
        rw [Pi.smul_apply, smul_eq_mul, ← smul_smul, smul_add]
      rw [harg]
      exact ih _ _
def reduceAgainstLin (D : List (PivRow n)) : Vec n →ₗ[ZMod 2] Vec n where
  toFun := reduceAgainst D
  map_add' := reduceAgainst_add D
  map_smul' := reduceAgainst_smul D
def inSpanB (L : List (Vec n)) (v : Vec n) : Bool :=
  decide (reduceAgainst (rowReduce L) v = 0)
def inKerB {k : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Vec n) : Bool :=
  (List.ofFn fun i : Fin k => decide ((M i) ⬝ᵥ x = 0)).all id
end QECCertificates


