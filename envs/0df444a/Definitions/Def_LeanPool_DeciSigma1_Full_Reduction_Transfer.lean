-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Transfer
-- name    : LeanPool_DeciSigma1_Full_Reduction_Transfer
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T14:18:13.17216+00:00
-- url     : https://prove2.me/theorems/d05205eb-6f5d-40ef-b4ee-cc0fbe016364
-- title:
--   Transfer
-- statement:
--   Definitions and structural lemmas for Transfer, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Reduction/Transfer.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Full_Reduction_Realization
public import Definitions.Def_LeanPool_DeciSigma1_Full_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Signed_Transfer
set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full.Reduction
open DeciSigma1.Semantics
open DeciSigma1.Full.Models DeciSigma1.Constraints
variable {n k : Nat} {V : Type}
variable {c : Fin n → Bool} {Γ : List (LitT n V)} {q : Fin k → V × V}
def countermodelObservations (q : Fin k → V × V) (m : Fin k → Bool)
    (W : Fin k → List (Fin n)) : List (Signed.Observation n V) :=
  (List.finRange k).flatMap fun i =>
    [(seed (q i) (m i) (W i), true), (exclusion (q i) (m i) (W i), false)]
end DeciSigma1.Full.Reduction


