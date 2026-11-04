-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryPairedSupportConcrete
-- name    : Submission_ThreeSum_TernaryPairedSupportConcrete
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T08:16:02.698907+00:00
-- url     : https://prove2.me/theorems/8d0a97ec-2255-4364-a588-2276f37db290
-- title:
--   Ternary Paired Support Concrete
-- statement:
--   Definitions and structural lemmas for Ternary Paired Support Concrete, from the weighted-cache deterministic 3SUM development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryPairedSupportConcrete.lean

import Definitions.Def_Submission_ThreeSum_TernaryPairedPotential
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
import Theorems.Thm_P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_left_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_mapEdge_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_output_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_reindex_symm
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_mapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_right_swapEdge
import Theorems.Thm_ThreeSum_TernaryCoverRegularity_swapEdge_swapEdge
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_mapEdge_symm__4d2d267acd4d
attribute [local simp] P2M_ThreeSum_TernaryCoverRegularity_reindex_symm__dc387cbb7851
attribute [local simp] ThreeSum.HashFamily.hashMap_apply
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.left_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.mapEdge_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.output_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.reindex_symm
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_mapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.right_swapEdge
attribute [local simp] ThreeSum.TernaryCoverRegularity.swapEdge_swapEdge


set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryPairedSupportConcrete
open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators
variable {K : Type*} [Field K]
def flatten (J : ℕ) : ((Fin J → K) × (K × K)) →ₗ[K] (Fin (J+2) → K) where
  toFun u i := Sum.elim u.1 (fun j : Fin 2 => ![u.2.1,u.2.2] j) (finSumFinEquiv.symm i)
  map_add' u v := by
    funext i
    cases h : finSumFinEquiv.symm i with
    | inl j => simp [h]
    | inr j => fin_cases j <;> simp [h]
  map_smul' c u := by
    funext i
    cases h : finSumFinEquiv.symm i with
    | inl j => simp [h]
    | inr j => fin_cases j <;> simp [h]
def flattenInt (J : ℕ) (u : (Fin J → ℤ) × (ℤ × ℤ)) : Fin (J+2) → ℤ :=
  fun i => Sum.elim u.1 (fun j : Fin 2 => ![u.2.1,u.2.2] j) (finSumFinEquiv.symm i)
variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]
def tupleMatrix {J m : ℕ} (L R : P → Fin J → ℤ) (e : Fin m → P) :
    (Fin m ⊕ Fin m) → Fin (J+2) → ℤ :=
  Sum.elim (fun i => flattenInt J (L (e i),(1,0)))
    (fun i => flattenInt J (R (e i),(0,1)))
end ThreeSum.TernaryPairedSupportConcrete


