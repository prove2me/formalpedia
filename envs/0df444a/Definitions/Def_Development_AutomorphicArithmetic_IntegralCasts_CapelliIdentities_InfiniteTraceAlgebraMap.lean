-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteTraceAlgebraMap
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_InfiniteTraceAlgebraMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T06:32:20.273608+00:00
-- url     : https://prove2.me/theorems/458ed401-a593-48e2-b461-523c8b9df804
-- title:
--   Infinite Trace Algebra Map
-- statement:
--   Definitions and structural lemmas for Infinite Trace Algebra Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CapelliIdentities/InfiniteTraceAlgebraMap.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable def UpperTheory.Reformulated.B.Qh34.infiniteTrace.{u_1} :
    (K : Type u_1) → [inst : Field K] → [NumberField K] → NumberField.InfiniteAdeleRing K →+ ℝ :=
    fun (K : Type u_1) [Field K] [NumberField K] ↦
      {
        toFun := fun (x : NumberField.InfiniteAdeleRing K) ↦
          ∑ w : NumberField.InfinitePlace K,
            (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re,
        map_zero' := (show ∀ (K : Type _) [inst : Field K] [inst_1 : NumberField K],
                  ∑ x : NumberField.InfinitePlace K,
                      (↑x.mult : ℝ) *
                        ((NumberField.InfinitePlace.Completion.extensionEmbedding x : x.Completion → ℂ)
                            ((0 : NumberField.InfiniteAdeleRing K) x)).re =
                    (0 : ℝ) from by
              intro K _ _
              refine Finset.sum_eq_zero fun w _ => ?_
              have h : (0 : NumberField.InfiniteAdeleRing K) w = 0 := rfl
              rw [h, map_zero, Complex.zero_re, mul_zero]
            ) K, map_add' := (show ∀ (K : Type _) [inst : Field K] [inst_1 : NumberField K] (x y : NumberField.InfiniteAdeleRing K),
                  ∑ w : NumberField.InfinitePlace K,
                      (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) ((x + y) w)).re =
                    ∑ w : NumberField.InfinitePlace K,
                        (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (x w)).re +
                      ∑ w : NumberField.InfinitePlace K,
                        (↑w.mult : ℝ) * ((NumberField.InfinitePlace.Completion.extensionEmbedding w : w.Completion → ℂ) (y w)).re from by
              intro K _ _ x y
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun w _ => ?_
              have h : (x + y) w = x w + y w := rfl
              rw [h, map_add, Complex.add_re, mul_add]
            ) K : NumberField.InfiniteAdeleRing K →+ ℝ }


