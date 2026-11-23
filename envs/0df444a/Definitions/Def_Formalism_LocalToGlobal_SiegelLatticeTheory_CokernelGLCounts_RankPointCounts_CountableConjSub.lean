-- Prove2me | Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
-- name    : Formalism_LocalToGlobal_SiegelLatticeTheory_CokernelGLCounts_RankPointCounts_CountableConjSub
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T23:54:45.117747+00:00
-- url     : https://prove2.me/theorems/d4e3c85f-3f20-4c1d-9280-4081933d7ae7
-- title:
--   Countable Conj Sub
-- statement:
--   Definitions and structural lemmas for Countable Conj Sub, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/SiegelLatticeTheory/CokernelGLCounts/RankPointCounts/CountableConjSub.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal Pointwise
namespace Formalism.L2.SG.MeasureShiftInvariance
section SF
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
def SF (S : Set G) (Ω : Set G) : Prop :=
  MeasurableSet Ω ∧ (∀ x, ∃ s ∈ S, s * x ∈ Ω) ∧ ∀ x ∈ Ω, ∀ s ∈ S, s * x ∈ Ω → s = 1
variable (h : G)
def conjSub (Γ : Subgroup G) : Subgroup G := Γ.map (MulAut.conj h⁻¹).toMonoidHom
instance countable_conjSub (Γ : Subgroup G) [Countable Γ] : Countable (conjSub h Γ) := by
  unfold conjSub
  exact Countable.of_equiv _ (Γ.equivMapOfInjective _ (MulAut.conj h⁻¹).injective).toEquiv
end SF
section Unfold
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
end Unfold
section Boch
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul₂ G] [MeasurableInv G]
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant] (ν : Measure G) [SFinite ν]
end Boch
section Shift
variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
end Shift
section ShiftG
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
end ShiftG
end Formalism.L2.SG.MeasureShiftInvariance


