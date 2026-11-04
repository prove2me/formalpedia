-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedTensor
-- name    : Submission_ThreeSum_TernaryPairedTensor
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:18:49.604648+00:00
-- url     : https://prove2.me/theorems/248dde89-dece-4edd-9296-bf0717bffb7c
-- title:
--   Ternary Paired Tensor
-- statement:
--   Definitions and structural lemmas for Ternary Paired Tensor, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedTensor.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedTensor
open Finset Matrix TernaryPairedPotential
open scoped BigOperators
variable {P I R : Type*} [Fintype P] [CommRing R]
abbrev PairedIndex (m : ℕ) := Fin m ⊕ Fin m
def pairedMinor {m : ℕ} (L R' : P → I → R) (e : Fin m → P) (cols : PairedIndex m → I) :
    Matrix (PairedIndex m) (PairedIndex m) R :=
  fun i j => Sum.elim (fun k => L (e k)) (fun k => R' (e k)) i (cols j)
def tensor (L R' : P → I → R) (a b c d : I) : R :=
  ∑ x : P, L x a * L x b * R' x c * R' x d
end ThreeSum.TernaryPairedTensor


