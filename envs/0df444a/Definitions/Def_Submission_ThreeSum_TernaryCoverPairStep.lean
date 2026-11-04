-- Prove2me | Definitions.Def_Submission_ThreeSum_TernaryCoverPairStep
-- name    : Submission_ThreeSum_TernaryCoverPairStep
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:53:16.90839+00:00
-- url     : https://prove2.me/theorems/a68bbbe4-94fa-436e-b8c4-c4dbc3008b66
-- title:
--   Ternary Cover Pair Step
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSum/TernaryCoverPairStep.lean

import Definitions.Def_Submission_ThreeSum_TernaryCoverRankFibers
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
set_option autoImplicit false
noncomputable section
namespace ThreeSum.TernaryCoverPairStep
open Finset TernaryCoverRankFibers
variable {K X : Type*} [Field K] [AddCommGroup X] [Module K X]
def vertical (S : Submodule K (X × (K × K))) : Submodule K (K × K) :=
  S.comap (LinearMap.inr K X (K × K))
def prefixSpace (S : Submodule K (X × (K × K))) : Submodule K X :=
  S.map (LinearMap.fst K X (K × K))
def prefixMap (S : Submodule K (X × (K × K))) : S →ₗ[K] X :=
  (LinearMap.fst K X (K × K)).comp S.subtype
def verticalMap (S : Submodule K (X × (K × K))) : vertical S →ₗ[K] S where
  toFun v := ⟨(0, v.val), v.property⟩
  map_add' a b := by apply Subtype.ext; ext <;> simp
  map_smul' a b := by apply Subtype.ext; simp
variable {E Z ι : Type*} [Fintype E] [Fintype Z] [Fintype ι] [DecidableEq K]
def pairedSet (left right : E → ι → K) (prior : Z → ι → X)
    (S : Submodule K (X × (K × K))) : Finset (Z × E) := by
  classical
  exact univ.filter fun ze => ∀ i, (prior ze.1 i, (left ze.2 i, right ze.2 i)) ∈ S
def priorSet (prior : Z → ι → X) (S : Submodule K (X × (K × K))) : Finset Z := by
  classical
  exact univ.filter fun z => ∀ i, prior z i ∈ prefixSpace S
end ThreeSum.TernaryCoverPairStep


