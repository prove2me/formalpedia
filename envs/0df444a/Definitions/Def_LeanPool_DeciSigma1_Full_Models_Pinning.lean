-- Prove2me | Definitions.Def_LeanPool_DeciSigma1_Full_Models_Pinning
-- name    : LeanPool_DeciSigma1_Full_Models_Pinning
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-22T13:53:09.393576+00:00
-- url     : https://prove2.me/theorems/45e768e5-7dfa-4071-b88c-b91ba836947e
-- title:
--   Pinning
-- statement:
--   Definitions and structural lemmas for Pinning, from Yaoyu Zhao; LeanPool contributors's pinned Decidability of the Sigma-one theory of non-structural subtyping development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Full/Models/Pinning.lean

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_GroundBounds
public import Definitions.Def_LeanPool_DeciSigma1_Full_Models_Observations
public import Theorems.Thm_DeciSigma1_Constraints_UpperAt_map

set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace DeciSigma1.Full.Models.Pinning
open DeciSigma1.Semantics DeciSigma1.Constraints
variable {n : ℕ}
end DeciSigma1.Full.Models.Pinning
namespace DeciSigma1.Full.Models
open DeciSigma1.Constraints DeciSigma1.Semantics
variable {n : ℕ}
namespace Pinning
def vars {V : Type*} : LitT n V → List V
  | .le u v => [u, v]
  | .fLe a u | .leF u a => (List.finRange n).map a ++ [u]
  | .eqBot u | .eqTop u => [u]
end Pinning
end DeciSigma1.Full.Models


