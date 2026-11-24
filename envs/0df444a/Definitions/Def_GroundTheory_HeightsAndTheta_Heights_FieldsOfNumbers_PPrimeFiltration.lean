-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- name    : GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPrimeFiltration
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:28:49.745812+00:00
-- url     : https://prove2.me/theorems/10664caf-ee83-46f5-bf63-d33939f3e8ce
-- title:
--   PPrime Filtration
-- statement:
--   Definitions and structural lemmas for PPrime Filtration, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/FieldsOfNumbers/PPrimeFiltration.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
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
namespace PrimeFiltration
section Lex
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} {F : Type u} [Field F]
abbrev lexDecEq (n : ℕ) : DecidableEq (Lex (Fin n → ℕ)) := LinearOrder.toDecidableEq
attribute [local instance 2000] lexDecEq
@[irreducible] def blockIdx (K : Type) [Fintype K] : K ≃ Fin (Fintype.card K) :=
  Fintype.equivFin K
def lexEmb (K : Type) [Fintype K] : (K → ℕ) →+ Lex (Fin (Fintype.card K) → ℕ) where
  toFun b := toLex (fun i => b ((blockIdx K).symm i))
  map_zero' := rfl
  map_add' _ _ := rfl
def lexWeight : (Σ k, ι k) → Lex (Fin (Fintype.card K) → ℕ) :=
  fun v => lexEmb K (blockWeight ι v)
abbrev lexGrading (ι : K → Type) (F : Type u) [Field F] :
    Lex (Fin (Fintype.card K) → ℕ) → Submodule F (MRing ι F) :=
  weightedHomogeneousSubmodule F (lexWeight (ι := ι))
attribute [local instance] MvPolynomial.weightedGradedAlgebra
end Lex
section Length
variable {K : Type} {ι : K → Type} {F : Type u} [Field F]
end Length
section Dim
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
end Dim
section Main
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {F : Type u} [Field F]
end Main
end PrimeFiltration
end
end GroundTheory.Heights₂.Heights.FieldNumbers


