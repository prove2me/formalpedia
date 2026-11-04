-- Prove2me | Definitions.Def_Submission_ThreeSum_LightTernaryPairedPolynomial
-- name    : Submission_ThreeSum_LightTernaryPairedPolynomial
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:40:00.556314+00:00
-- url     : https://prove2.me/theorems/a42eb790-d4e0-4914-9621-98e5bfe3985d
-- title:
--   Light Ternary Paired Polynomial
-- statement:
--   Definitions and structural lemmas for Light Ternary Paired Polynomial, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/LightTernaryPairedPolynomial.lean

import Definitions.Def_Submission_ThreeSum_LightMomentDeterminant
import Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
import Theorems.Thm_Light_Ends_set
import Theorems.Thm_Light_SegN_read

set_option autoImplicit false
noncomputable section
namespace ThreeSum.LightTernaryPairedPolynomial
open Light LightFixedArithmetic LightMomentDeterminant TernaryPairedTensor
open scoped BigOperators
abbrev Quad (m : ℕ) := PairedIndex m × PairedIndex m × PairedIndex m × PairedIndex m
def encode {m : ℕ} (q : Quad m) : ℕ := (Fintype.equivFin (Quad m) q).val
def channel {m : ℕ} (σ τ : Equiv.Perm (PairedIndex m)) (i : Fin m) : Quad m :=
  (σ (.inl i),τ (.inl i),σ (.inr i),τ (.inr i))
def polynomial (m : ℕ) : Circuit :=
  sumCircuits ((Finset.univ : Finset (Equiv.Perm (PairedIndex m))).toList.map fun σ =>
    sumCircuits ((Finset.univ : Finset (Equiv.Perm (PairedIndex m))).toList.map fun τ =>
      .mul (.literal ((Equiv.Perm.sign σ : ℤ)*(Equiv.Perm.sign τ : ℤ)))
        (prodCircuits ((Finset.univ : Finset (Fin m)).toList.map fun i =>
          .atom (encode (channel σ τ i))))))
def tensorIndex (Λ a b c d : ℕ) : ℕ := ((a*Λ+b)*Λ+c)*Λ+d
def atomExpr (m : ℕ) (q : Quad m) : Expr :=
  let read := fun r : PairedIndex m => M (v 2 +' k (Fintype.equivFin (PairedIndex m) r).val)
  M (v 0 +' (((read q.1 *' v 1 +' read q.2.1) *' v 1 +' read q.2.2.1) *' v 1 +' read q.2.2.2))
def atoms (m : ℕ) (j : ℕ) : Expr :=
  if hj : j < Fintype.card (Quad m) then
    atomExpr m ((Fintype.equivFin (Quad m)).symm ⟨j,hj⟩) else k 0
def value {m : ℕ} (T : Quad m → ℤ) : ℤ :=
  ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
    ((Equiv.Perm.sign σ : ℤ)*(Equiv.Perm.sign τ : ℤ)) *
      ∏ i : Fin m, T (channel σ τ i)
def body (m : ℕ) : Stmt := .set 0 ((polynomial m).compile (atoms m))
def time (m : ℕ) : ℕ := ((polynomial m).compile (atoms m)).cost+2
end ThreeSum.LightTernaryPairedPolynomial


