-- Prove2me | Definitions.Def_BianchiIX_Dynamics_IntegralClock
-- name    : BianchiIX_Dynamics_IntegralClock
-- status  : Definition
-- author  : @trppppp
-- created : 2026-11-04T21:03:16.514626+00:00
-- url     : https://prove2.me/theorems/5112e2d7-2d2f-49bd-8669-9233adff153e
-- title:
--   A positive integral clock on its entire interval
-- statement:
--   For $a:\mathbb R\to\mathbb R$ and $t_0\in\mathbb R$,
--   define the oriented integral clock
--   $$c_{a,t_0}(t)=\int_{t_0}^t a(u)\,du.$$
--
--   Assume $J\subset\mathbb R$ is open and convex, $t_0\in J$, and $a$ is
--   continuous and strictly positive on $J$. Let $e$ be the open partial
--   homeomorphism constructed from the restriction of $c_{a,t_0}$ to $J$.
--
--   The construction includes the strict derivative formula $c_{a,t_0}'=a$,
--   strict monotonicity, and openness on $J$. These proofs supply the
--   homeomorphism with source $J$ and target $c_{a,t_0}(J)$.
-- source:
--   https://github.com/l46430640-del/ERA-STATISTICS-FORMAL/blob/d74c241819f896ab8d050b21ace80c8e90eabd9e/BianchiIX/Dynamics/IntegralClock.lean

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section

namespace BianchiIX

open Set Filter MeasureTheory
open scoped Topology

def integralClock (a : ℝ → ℝ) (t₀ t : ℝ) : ℝ := ∫ u in t₀..t, a u



theorem hasStrictDerivAt_integralClock {J : Set ℝ} {a : ℝ → ℝ} {t₀ t : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (ht : t ∈ J) :
    HasStrictDerivAt (integralClock a t₀) (a t) t :=
  intervalIntegral.integral_hasStrictDerivAt_right
    (ha.mono (hJ.ordConnected.uIcc_subset ht₀ ht)).intervalIntegrable
    (ha.stronglyMeasurableAtFilter ho t ht) (ha.continuousAt (ho.mem_nhds ht))

theorem strictMonoOn_integralClock {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    StrictMonoOn (integralClock a t₀) J := by
  have hd := fun t ht => (hasStrictDerivAt_integralClock hJ ho ha ht₀ (t := t) ht).hasDerivAt
  exact strictMonoOn_of_deriv_pos hJ (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hd t (interior_subset ht)).deriv ▸ hpos t (interior_subset ht))

theorem isOpenMap_integralClock_restrict {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) :
    IsOpenMap (J.domRestrict (integralClock a t₀)) := by
  apply IsOpenMap.of_nhds_le
  intro t
  change 𝓝 (integralClock a t₀ t) ≤ map (integralClock a t₀ ∘ Subtype.val) (𝓝 t)
  rw [← map_map, map_nhds_subtype_val, ho.nhdsWithin_eq t.2]
  exact ((hasStrictDerivAt_integralClock hJ ho ha ht₀ t.2).map_nhds_eq
    (ne_of_gt (hpos t t.2))).ge

/-- The entire positive-clock interval, with its exact image as target. -/
def positiveIntegralClock {J : Set ℝ} {a : ℝ → ℝ} {t₀ : ℝ}
    (hJ : Convex ℝ J) (ho : IsOpen J) (ha : ContinuousOn a J)
    (ht₀ : t₀ ∈ J) (hpos : ∀ t ∈ J, 0 < a t) : OpenPartialHomeomorph ℝ ℝ :=
  OpenPartialHomeomorph.ofContinuousOpenRestrict
    ((strictMonoOn_integralClock hJ ho ha ht₀ hpos).injOn.toPartialEquiv _ _)
    (fun _ ht => (hasStrictDerivAt_integralClock hJ ho ha ht₀ ht).hasDerivAt.continuousAt.continuousWithinAt)
    (isOpenMap_integralClock_restrict hJ ho ha ht₀ hpos) ho













end BianchiIX


