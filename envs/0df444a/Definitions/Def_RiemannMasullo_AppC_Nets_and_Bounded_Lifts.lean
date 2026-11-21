-- Prove2me | Definitions.Def_RiemannMasullo_AppC_Nets_and_Bounded_Lifts
-- name    : RiemannMasullo_AppC_Nets_and_Bounded_Lifts
-- status  : Definition
-- author  : @dga471
-- created : 2026-11-20T22:27:31.102777+00:00
-- url     : https://prove2.me/theorems/8b837723-78ce-426c-8d2c-0bb32a30c443
-- title:
--   Cauchy-net equivalence, Fréchet spaces, relative compactness and bounded lifts
-- statement:
--   Definitions from Appendix C.1. Two Cauchy nets are equivalent when their difference on the product directed set tends to zero. A Fréchet space is polynormable, metrizable, and complete for its additive uniformity. Relative compactness means that the closure is compact. A bounded lift covers a specified target set by the image of a bounded source set. A map lifts bounded sets when this holds for every bounded target set.
-- source:
--   https://github.com/mccorvie/riemann-masullo/blob/8a05ee179a90e12e33a590c6412a9e9de416fa30/RiemannMasullo/AppC_LCTVS/Sec1.lean

import Mathlib

namespace RiemannMasullo
open Set Filter Topology TopologicalSpace Bornology
open scoped Pointwise DirectSum

section
universe u
variable {E : Type u} [AddCommGroup E] [UniformSpace E] [IsUniformAddGroup E]
variable {J K : Type*} [Preorder J] [Nonempty J] [IsDirectedOrder J]
  [Preorder K] [Nonempty K] [IsDirectedOrder K]

def EquivalentCauchyNets (f : J → E) (g : K → E) : Prop :=
  CauchySeq f ∧ CauchySeq g ∧ Tendsto (fun p : J × K ↦ f p.1 - g p.2) atTop (𝓝 0)
end

def IsFrechetTVS (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] : Prop :=
  ∃ h : IsTopologicalAddGroup E, letI := h
    PolynormableSpace ℂ E ∧ MetrizableSpace E ∧
      @CompleteSpace E (IsTopologicalAddGroup.rightUniformSpace E)

def IsRelativelyCompact {E : Type*} [TopologicalSpace E] (A : Set E) : Prop :=
  IsCompact (closure A)

section
variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
  [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
def HasBoundedLift (f : E →L[ℂ] F) (B : Set F) : Prop :=
  ∃ A : Set E, IsVonNBounded ℂ A ∧ B ⊆ f '' A

def LiftsBoundedSets (f : E →L[ℂ] F) : Prop :=
  ∀ B : Set F, IsVonNBounded ℂ B → HasBoundedLift f B
end
end RiemannMasullo


