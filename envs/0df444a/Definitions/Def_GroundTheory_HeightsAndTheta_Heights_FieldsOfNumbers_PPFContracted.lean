-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:53.180164+00:00
-- url     : https://prove2.me/theorems/26b69506-af77-4c56-9537-723b4f1052f3
-- title:
--   PPFContracted
-- statement:
--   Definitions and structural lemmas for PPFContracted, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPFContracted.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace PFContracted
section Homog
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
def blockDeg (k : K) : (Σ k, ι k) → ℕ := fun v => blockWeight ι v k
end Homog
section Dim
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
end Dim
section Contract
variable {K K' : Type*} [DecidableEq K] [DecidableEq K'] {F : Type*} [Field F]
end Contract
section Main
variable (F : Type u) [Field F] (K K' : Type) [Fintype K] [DecidableEq K] [Fintype K']
  [DecidableEq K'] (j : K ↪ K') (ι' : K' → Type) [∀ k, Fintype (ι' k)]
def pullNat (e : K → ℕ) : K' → ℕ := ∑ κ, e κ • (Pi.single (j κ) 1 : K' → ℕ)
variable {F K K' j ι'}
def monoSmall (i : ∀ k', ι' k') (e : K → ℕ) : MRing (fun k => ι' (j k)) F :=
  ∏ κ, X ⟨κ, i (j κ)⟩ ^ e κ
end Main
end PFContracted
end
end GroundTheory.Heights₂.Heights.FieldNumbers


