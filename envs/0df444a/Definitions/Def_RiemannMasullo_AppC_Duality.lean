-- Prove2me | Definitions.Def_RiemannMasullo_AppC_Duality
-- name    : RiemannMasullo_AppC_Duality
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:32:59.016189+00:00
-- url     : https://prove2.me/theorems/9cf935b1-a6bc-4883-a107-d39c7118f765
-- title:
--   Seminorms of evaluation and polar bornologies
-- statement:
--   Appendix C.2 defines the S-dual by uniform convergence on the sets of S. It defines seminorms of linear maps by taking suprema of continuous target seminorms on bounded test sets. For a bilinear pairing, a weakly bounded test set similarly defines a polar seminorm. A polar bornology is a nonempty directed family of weakly bounded sets that absorbs every nonzero rescaling of each member. The auxiliary precompactness predicate means relative compactness in the completion (Appendix C.1.4.2).
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec2a.lean

import Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts

noncomputable section
namespace RiemannMasullo
open Set Filter Topology Bornology
open scoped UniformConvergence UniformConvergenceCLM Pointwise

def IsPrecompactInCompletion {E : Type*} [UniformSpace E] (A : Set E) : Prop :=
  IsRelativelyCompact ((fun x : E ↦ (x : UniformSpace.Completion E)) '' A)

abbrev SDual (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (S : Set (Set E)) := E →Lᵤ[ℂ, S] ℂ

def IsPolarBornology {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (S : Set (Set E)) : Prop :=
  S.Nonempty ∧ DirectedOn (· ⊆ ·) S ∧
    (∀ T ∈ S, IsVonNBounded ℂ (toWeakSpace ℂ E '' T)) ∧
    ∀ T ∈ S, ∀ c : ℂ, c ≠ 0 → ∃ U ∈ S, c • T ⊆ U

local instance {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
    [PolynormableSpace ℂ V] : ContinuousSMul ℂ V :=
  (PolynormableSpace.withSeminorms ℂ V).continuousSMul

section
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [UniformSpace E] [IsUniformAddGroup E]
  [ContinuousSMul ℂ E] [T2Space E]
  [AddCommGroup F] [Module ℂ F] [UniformSpace F] [IsUniformAddGroup F]
  [PolynormableSpace ℂ F] [T2Space F]
def mappingSeminorm (T : {T : Set E // IsVonNBounded ℂ T})
    (p : {p : Seminorm ℂ F // Continuous p}) : Seminorm ℂ (E →L[ℂ] F) :=
  ⨆ x : T.val, p.val.comp ((ContinuousLinearMap.coeLM ℂ (R := ℂ) (M := E) (N₃ := F)).flip (x : E))
end

section
open scoped ComplexOrder
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [AddCommGroup F] [Module ℂ F]
variable (B : E →ₗ[ℂ] F →ₗ[ℂ] ℂ)

def polarSeminorm (A : {A : Set F // IsVonNBounded (E := WeakBilin B.flip) ℂ A}) :
    Seminorm ℂ E :=
  ⨆ y : A.val, (normSeminorm ℂ ℂ).comp (B.flip (y : F))
end
end RiemannMasullo


