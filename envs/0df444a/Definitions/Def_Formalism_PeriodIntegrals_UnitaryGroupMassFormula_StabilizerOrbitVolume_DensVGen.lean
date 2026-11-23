-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensVGen
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T00:57:55.656802+00:00
-- url     : https://prove2.me/theorems/34f5e66b-b5a0-4bf1-ae44-1ef1241b4765
-- title:
--   Dens VGen
-- statement:
--   Definitions and structural lemmas for Dens VGen, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/StabilizerOrbitVolume/DensVGen.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabSW
open MeasureTheory Topology Set Filter
open scoped Pointwise
def IsLCcOn {V : Type} [TopologicalSpace V] (U : Set V) (φ : V → ℝ) : Prop :=
  IsLocallyConstant φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U
def HasCOSub (V : Type) [AddGroup V] [TopologicalSpace V] : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N
section Dens
variable {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
def HasDens (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (φ : V → ℝ) (g : X → ℝ) :
    Prop :=
  Integrable φ μ ∧ Continuous g ∧ ∀ S : Set X, IsCompact S →
    ∫ v in f ⁻¹' (ι '' S), φ v ∂μ = ∫ b in S, g b ∂ν
end Dens
section Approx
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
end Approx
section Main
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  [LocallyCompactSpace X]
def cosApx (Λ : AddSubgroup V) (φ : V → ℝ) (x : V) : ℝ := φ ((x : V ⧸ Λ).out)
end Main
end PI.VolStabSW


