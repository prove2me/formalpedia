-- Prove2me | Definitions.Def_ReedGGN_Regulator_Supplement_Convolution
-- name    : ReedGGN_Regulator_Supplement_Convolution
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-24T05:04:31.083425+00:00
-- url     : https://prove2.me/theorems/53cdf4c3-5864-4a1f-820e-209603c6edc8
-- title:
--   (4.7), (A.67)–(A.70) — Convolutions and strong solution functionals
-- statement:
--   Let $F$ be a service CDF, $G=1-F$, and $x$ a càdlàg path. The queue convolution counts an initial arrival burst and is defined by integration by parts:
--
--   $$K_G^{\rm cl}x(t)=G(0)x(t)-\int_{(0,t]}x(t-s)\,dF(s),\qquad K_G^{\rm inc}x(t)=K_G^{\rm cl}x(t)-G(t)x(0).$$
--
--   The increment transform is the map needed by the whole-coordinate function $f(q,w,a,m)=(q,w,K_G^{\rm inc}a,m)$ in Lemma A.9. The sign in the printed (A.69) is corrected: minus integration against $dF$ equals plus integration against $dG$. The queue's closed-arrival transform adds back the time-zero contribution explicitly. No stochastic integration or bounded variation of $x$ is assumed.
--
--   The fluid input is $\min(q,1)\bar F_0+(q-1)^+G+K_G^{\rm cl}a$. A strong regulator functional is measurable and nonanticipating in its data, has càdlàg output, satisfies the published regulator equation at all nonnegative times, and is unique among all càdlàg solutions. This names the full equation rather than a freely chosen limiting solution.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, (4.7), p.12; (A.67)–(A.70), pp.56–57

import Mathlib
import Definitions.Def_ReedGGN_Regulator_Supplement_QueueModel
import Definitions.Def_ReedGGN_Regulator_Equation

open MeasureTheory ProbabilityTheory Filter Topology

open scoped NNReal ENNReal

namespace ReedGGN.Regulator.Supplement

/-- Closed-arrival convolution, with x(0−)=0. Integration by parts against the service
 distribution (not an integral against an arbitrary rough x). The atom at service time zero
 is in G(0); the remaining service mass is over (0,t]. A burst x(0) at time zero contributes
 G(t)x(0). For a constant x=c this is cG(t), not zero. -/
noncomputable def arrivalTransform (μ : Measure ℝ) (x : RPath) : RPath :=
  fun t => tail μ 0 * x t -
    ∫ s in Set.Ioc (0 : ℝ) t, x (Real.toNNReal ((t : ℝ) - s)) ∂μ

/-- Increment convolution used for the map of Lemma A.9: integrate dx over (0,t],
 subtracting the starting value's tail. The printed (A.69) has the wrong sign for dG:
 here -dF = dG, so the integral is subtracted with respect to the positive law μ.
 Constant paths give zero. The closed-arrival transform adds G(t)x(0) back. -/
noncomputable def incrementTransform (μ : Measure ℝ) (x : RPath) : RPath :=
  fun t => arrivalTransform μ x t - tail μ t * x 0

/-- Entire four-coordinate map (A.67), with the increment convention of (A.69). -/
noncomputable def convolutionMap (μ : Measure ℝ) (x : State 3) : State 3 :=
  three x.1 (x.2 0) (incrementTransform μ (x.2 1)) (x.2 2)

/-- Full (4.7) input for arbitrary (possibly random) initial count and arrival path.
 Reuses the published tail and service law conventions, and adds general arrivals to the
 published equilibrium-arrival special case fluidInput. -/
noncomputable def fluidDriver (μ μ₀ : Measure ℝ) (x : State 1) : RPath :=
  fun t => min x.1 1 * tail μ₀ t + max (x.1 - 1) 0 * tail μ t +
    arrivalTransform μ (x.2 0) t

/-- Input data agree up to T, including the initial real coordinate. -/
def AgreeThrough {k : ℕ} (T : ℝ≥0) (x y : State k) : Prop :=
  x.1 = y.1 ∧ ∀ i t, t ≤ T → x.2 i t = y.2 i t

/-- Unique strong solution functional for the specified driver: measurable on ℝ×D^k,
 nonanticipating in every coordinate, càdlàg output, the published regulator equation, and
 uniqueness among all càdlàg solutions. No negative-time values are compared. -/
def StrongFor {k : ℕ} (μ : Measure ℝ) (a : ℝ) (driver : State k → RPath)
    (Φ : State k → RPath) : Prop :=
  Measurable (fun x : {x : State k // Admissible x} => Φ x.val) ∧
  (∀ x, Admissible x →
    KurtzProtter91.Integrals.IsCadlag (Φ x) ∧
    SolvesRegulator μ a (extendPath (driver x)) (extendPath (Φ x)) ∧
    ∀ z : RPath, KurtzProtter91.Integrals.IsCadlag z →
      SolvesRegulator μ a (extendPath (driver x)) (extendPath z) → z = Φ x) ∧
  ∀ T x y, Admissible x → Admissible y → AgreeThrough T x y →
    ∀ t, t ≤ T → Φ x t = Φ y t

end ReedGGN.Regulator.Supplement


