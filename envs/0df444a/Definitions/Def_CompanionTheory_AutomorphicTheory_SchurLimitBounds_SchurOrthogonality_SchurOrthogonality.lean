-- Prove2me | Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
-- name    : CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_SchurOrthogonality
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:28.672557+00:00
-- url     : https://prove2.me/theorems/ea5eb4f6-6b16-4111-884f-429ec26d346b
-- title:
--   Schur Orthogonality
-- statement:
--   Definitions and structural lemmas for Schur Orthogonality, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/SchurLimitBounds/SchurOrthogonality/SchurOrthogonality.lean

import Definitions.Def_CompanionTheory_AutomorphicTheory_SchurLimitBounds_SchurOrthogonality_URepSchur
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
set_option linter.unusedSectionVars false
namespace CompanionTheory.LimBd.URep
open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate
section Families
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
end Families
section Group
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
def SqInt (μ : Measure G) (π : UnitaryRep G H) : Prop := ∀ v w : H, MemLp (fun g => ⟪w, π g v⟫_ℂ) 2 μ
def pairing (μ : Measure G) (π : UnitaryRep G H) (σ : UnitaryRep G K) (v w : H) (v' w' : K) : ℂ :=
  ∫ g, ⟪w, π g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ
end Group
end CompanionTheory.LimBd.URep


