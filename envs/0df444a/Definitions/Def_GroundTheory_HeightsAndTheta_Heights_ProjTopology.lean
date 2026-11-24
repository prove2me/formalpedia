-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ProjTopology
-- name    : GroundTheory_HeightsAndTheta_Heights_ProjTopology
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:20.519589+00:00
-- url     : https://prove2.me/theorems/44793396-fa12-4cb3-9506-d4dca1095e6d
-- title:
--   Proj Topology
-- statement:
--   Definitions and structural lemmas for Proj Topology, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ProjTopology.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights
open scoped LinearAlgebra.Projectivization
variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [TopologicalSpace V]
instance : TopologicalSpace (ℙ K V) :=
  TopologicalSpace.coinduced (Projectivization.mk' K) inferInstance
namespace ProjTopology
lemma continuous_mk' : Continuous (Projectivization.mk' K : {v : V // v ≠ 0} → ℙ K V) :=
  continuous_coinduced_rng
end ProjTopology
instance compactSpace_projectivization_complex (N : ℕ) : CompactSpace (ℙ ℂ (Fin (N + 1) → ℂ)) := by
  have hS : IsCompact (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_sphere 0 1
  have : CompactSpace (Metric.sphere (0 : Fin (N + 1) → ℂ) 1) := isCompact_iff_compactSpace.mp hS
  have hne : ∀ w : Metric.sphere (0 : Fin (N + 1) → ℂ) 1, (w : Fin (N + 1) → ℂ) ≠ 0 := by
    intro w h
    have := w.2
    rw [h, mem_sphere_iff_norm, sub_zero, norm_zero] at this
    exact zero_ne_one this
  let g : Metric.sphere (0 : Fin (N + 1) → ℂ) 1 → ℙ ℂ (Fin (N + 1) → ℂ) := fun w =>
    Projectivization.mk' ℂ ⟨w.1, hne w⟩
  have hg : Continuous g :=
    ProjTopology.continuous_mk'.comp (Continuous.subtype_mk continuous_subtype_val _)
  have hsurj : Function.Surjective g := by
    intro v
    induction v using Projectivization.ind with
    | h w hw =>
      have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
      refine ⟨⟨(‖w‖⁻¹ : ℂ) • w, ?_⟩, ?_⟩
      · rw [mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Complex.norm_real, norm_norm,
          inv_mul_cancel₀ hn]
      · change Projectivization.mk ℂ _ _ = Projectivization.mk ℂ w hw
        rw [Projectivization.mk_eq_mk_iff]
        exact ⟨Units.mk0 (‖w‖⁻¹ : ℂ) (inv_ne_zero (by exact_mod_cast hn)), rfl⟩
  refine ⟨?_⟩
  rw [← hsurj.range_eq]
  exact isCompact_range hg
end GroundTheory.Heights₂.Heights


