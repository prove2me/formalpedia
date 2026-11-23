-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
-- name    : Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfect
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T20:37:13.850361+00:00
-- url     : https://prove2.me/theorems/924507f6-3ea2-4836-a5a1-9006a1f82236
-- title:
--   Unramified Quadratic Integral Trace Form Perfect
-- statement:
--   Definitions and structural lemmas for Unramified Quadratic Integral Trace Form Perfect, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UnramifiedQuadraticIntegralTraceFormPerfect.lean

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
namespace GlobalTheory.NTr
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
def conj (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] : E ≃ₐ[F] E :=
  { starRingEnd E with
    invFun := starRingEnd E
    left_inv := fun x => by simp
    right_inv := fun x => by simp
    commutes' := fun x => by simpa [starRingEnd_apply] using Unram.star_fix (F := F) (E := E) x }
section Sq
variable {K : Type} [NormedField K] [IsUltrametricDist K]
def closeSetoid (K : Type) [NormedField K] [IsUltrametricDist K] : Setoid (Metric.closedBall (0 : K) 1) where
  r a b := ‖(a : K) - b‖ < 1
  iseqv := by
    refine ⟨fun a => by simp, fun h => by rwa [norm_sub_rev], fun h1 h2 => ?_⟩
    rename_i a b c
    calc ‖(a : K) - c‖ = ‖((a : K) - b) + ((b : K) - c)‖ := by ring_nf
      _ ≤ max ‖(a : K) - b‖ ‖(b : K) - c‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt h1 h2
end Sq
section Main
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [hU : Unram F E]
end Main
end GlobalTheory.NTr


