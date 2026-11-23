-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCos
-- name    : Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVCos
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:14:56.134925+00:00
-- url     : https://prove2.me/theorems/f56aaa0c-3468-4afa-9f72-d209808f37e1
-- title:
--   Dens VCos
-- statement:
--   Definitions and structural lemmas for Dens VCos, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/WeilStabilizerVolume/DensVCos.lean

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensVGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.VolStabW
open MeasureTheory Topology Set Filter
section Cos
variable {V X Y : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [OpensMeasurableSpace V]
  [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X] [T2Space X]
  {μ : Measure V} {f : V → Y} {ι : X → Y} {ν : Measure X}
def DensCos (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X) (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν
def DensCosB (B : AddSubgroup V → Prop) (μ : Measure V) (f : V → Y) (ι : X → Y) (ν : Measure X)
    (U : Set V) : Prop :=
  ∀ x ∈ U, ∃ N ∈ 𝓝 (0 : V), ∀ y, y - x ∈ N → ∀ Λ : AddSubgroup V, B Λ → IsOpen (Λ : Set V) →
    IsCompact (Λ : Set V) → (Λ : Set V) ⊆ N → ∃ g : X → ℝ, Continuous g ∧
      ∀ S : Set X, IsCompact S →
        ∫ v in f ⁻¹' (ι '' S), {z | z - y ∈ Λ}.indicator (fun _ => (1 : ℝ)) v ∂μ =
          ∫ b in S, g b ∂ν
omit [IsTopologicalAddGroup V] in

def IsCOBasis (B : AddSubgroup V → Prop) : Prop :=
  ∀ N ∈ 𝓝 (0 : V), ∃ Λ : AddSubgroup V, B Λ ∧ IsOpen (Λ : Set V) ∧ IsCompact (Λ : Set V) ∧
    (Λ : Set V) ⊆ N
end Cos
end PI.VolStabW


