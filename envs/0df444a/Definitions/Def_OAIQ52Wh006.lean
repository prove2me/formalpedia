-- Prove2me | Definitions.Def_OAIQ52Wh006
-- name    : OAIQ52Wh006
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-27T18:45:40.640995+00:00
-- url     : https://prove2.me/theorems/92d798de-51dc-4f12-b9a5-27129139e8a8
-- title:
--   Definitions bundle OAIQ52Wh006 of the split of OpenAI, Weak Hessian bounds along every geodesic in RCD spaces
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.WeakHessian.every_geodesic`, carved from OpenAI's openai/math development (OpenAI, *Weak Hessian bounds along every geodesic in RCD spaces*, OpenAI Math Release, September 24, 2026, result family 358, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 9 declarations of OpenAI's Lean: 9 theorems.
--
--   **Sources.** They come from these modules of lean/OAI/Geometry/WeakHessian, in whole or in part: [`WeakHessian_Calculus_CompactHopf`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactHopf.lean), [`WeakHessian_Calculus_CompactHopfCurve`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Calculus/CompactHopfCurve.lean), [`WeakHessian_Measure_InlinedFile0`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Measure/InlinedFile0.lean), [`WeakHessian_Transport_BoundedHopfMapLipschitz`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/BoundedHopfMapLipschitz.lean), [`WeakHessian_Transport_LocalSlopeCompContraction`](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/WeakHessian/WeakHessian/Transport/LocalSlopeCompContraction.lean).
--
--   **Imports.** It imports the published bundle `Def_WeakHessian`; the bundles `OAIQ52Wh003` and `OAIQ52Wh004` of this split.
--
--   **Imported by** (directly, in this split): the bundle `OAIQ52Wh007`.
-- source:
--   OpenAI, Weak Hessian bounds along every geodesic in RCD spaces, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 358; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Weak-Hessian-bounds-along-every-geodesic-in-RCD-spaces-September-24-2026/weak-hessian-geodesics.pdf; Apache License 2.0); definitions carved from lean/OAI/Geometry/WeakHessian at commit adc7f12

import Mathlib
import Definitions.Def_WeakHessian
import Definitions.Def_OAIQ52Wh003
import Definitions.Def_OAIQ52Wh004

section
-- module Solutions.OAIQ52_WH.WeakHessian_Measure_InlinedFile0
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable
namespace WeakHessian

variable {X : Type*} [MetricSpace X]

variable [MeasurableSpace X] [BorelSpace X]

variable {m ν : Measure X}

omit [BorelSpace X]

theorem weakGradient_eq_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f : X → ℝ) : weakGradient m f =ᵐ[m] weakGradient ν f := by
  by_cases hf : ∃ W, IsMinimalLocalWeakUpperGradient m f W
  · have hfν : ∃ W, IsMinimalLocalWeakUpperGradient ν f W := by
      obtain ⟨W, hW⟩ := hf
      exact ⟨W, hW.change_measure hm hν⟩
    have hwm := weakGradient_isMinimal hf
    have hwν := (weakGradient_isMinimal hfν).change_measure hν hm
    filter_upwards [hwm.2 _ hwν.1, hwν.2 _ hwm.1] with x h₁ h₂
    exact le_antisymm h₁ h₂
  · have hfν : ¬ ∃ W, IsMinimalLocalWeakUpperGradient ν f W := by
      rintro ⟨W, hW⟩
      exact hf ⟨W, hW.change_measure hν hm⟩
    simp only [weakGradient, dite_eq_right hf, dite_eq_right hfν, Filter.EventuallyEq.refl]

theorem gamma_eq_of_comparable {C D : ℝ≥0}
    (hm : m ≤ (C : ℝ≥0∞) • ν) (hν : ν ≤ (D : ℝ≥0∞) • m)
    (f g : X → ℝ) : gamma m f g =ᵐ[m] gamma ν f g := by
  filter_upwards [weakGradient_eq_of_comparable hm hν (fun x => f x + g x),
    weakGradient_eq_of_comparable hm hν (fun x => f x - g x)] with x hp hn
  simp only [gamma, hp, hn]

theorem gamma_exponentialMeasure {V : X → ℝ} {B : ℝ}
    (hV : ∀ x, |V x| ≤ B) (f g : X → ℝ) :
    gamma m f g =ᵐ[m] gamma (exponentialMeasure m V) f g := by
  obtain ⟨hm, hν⟩ := exponentialMeasure_comparable (m := m) hV
  exact gamma_eq_of_comparable (C := (Real.exp B).toNNReal)
    (D := (Real.exp B).toNNReal) hm hν f g

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactHopf
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile82
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [ProperSpace X]

lemma boundedHopfMap_support_bound (f : X →ᵇ ℝ) (o : X) {R : ℝ} (hR : 0 ≤ R)
    (hs : Function.support f ⊆ Metric.closedBall o R) {s : ℝ} (hs0 : 0 < s) :
    Function.support (boundedHopfMap f s) ⊆ Metric.closedBall o (R+s+‖f‖+1) := by
  lift R to ℝ≥0 using hR
  intro x hx
  by_contra hout
  have hxD : R+s+‖f‖+1 < dist x o := lt_of_not_ge hout
  have hx0 : f x = 0 := by
    by_contra hh
    have := hs hh
    change dist x o ≤ R at this
    linarith [norm_nonneg f]
  have hqne : hopfLax f s x ≠ 0 := by simpa only [Function.mem_support,boundedHopfMap_apply_pos f hs0] using hx
  have hq : hopfLax f s x < 0 := lt_of_le_of_ne (by simpa only [hx0] using hopfLax_le_self (fun x => (boundedContinuous_bounds f x).1) hs0 x) hqne
  obtain ⟨y,hy⟩ := exists_hopf_minimizer f.continuous (fun x => (boundedContinuous_bounds f x).1) hs0 x
  have hfneg : f y < 0 := by
    have hc : 0 ≤ dist x y^2/(2*s) := by positivity
    dsimp only [hopfObjective] at hy
    linarith
  have hyR : dist y o ≤ R := hs (ne_of_lt hfneg)
  have hd := hopf_minimizer_distance_sq (fun x => (boundedContinuous_bounds f x).1) hs0 hy
  rw [hx0] at hd
  have htri := dist_triangle x y o
  have hn := norm_nonneg f
  have hsqd : (s+‖f‖+1)^2 < dist x y^2 := (sq_lt_sq₀ (by positivity) dist_nonneg).mpr (by linarith)
  nlinarith [sq_nonneg s,sq_nonneg ‖f‖]

lemma boundedHopfMap_compactSupport (f : X →ᵇ ℝ) (o : X)
    (hf : HasCompactSupport (f : X → ℝ)) {s : ℝ} (hs : 0 < s) :
    HasCompactSupport (boundedHopfMap f s : X → ℝ) := by
  obtain ⟨R,hR,hsub⟩ := hf.isCompact.isBounded.subset_closedBall_lt 0 o
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall o (R+s+‖f‖+1))
  exact boundedHopfMap_support_bound f o hR.le ((subset_tsupport f).trans hsub) hs

variable [MeasurableSpace X] [BorelSpace X] {m : Measure X}

lemma boundedHopfMap_memLp_compact (hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ) (o : X)
    (hf : HasCompactSupport (f : X → ℝ)) {s : ℝ} (hs : 0 < s) :
    MemLp (boundedHopfMap f s) 2 m := by
  let : IsLocallyFiniteMeasure m := ⟨fun x => ⟨Metric.ball x 1,Metric.ball_mem_nhds x zero_lt_one,
    hfin _ Metric.isBounded_ball⟩⟩
  apply (boundedHopfMap_compactSupport f o hf hs).memLp_of_bound (boundedHopfMap f s).continuous.aestronglyMeasurable
  exact ae_of_all _ fun x => (boundedHopfMap f s).norm_coe_le_norm x

end WeakHessianTransport

end
end InlinedFile82

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_LocalSlopeCompContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessian
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] {m : Measure X}

lemma cheegerEnergy_normalContraction {η : ℝ → ℝ} (hη : LipschitzWith 1 η)
    (hη0 : η 0 = 0) (f : X → ℝ) :
    cheegerEnergy m (η ∘ f) ≤ cheegerEnergy m f := by
  classical
  by_cases hf : MemLp f 2 m
  · change cheegerEnergy m (η ∘ f) ≤ (if MemLp f 2 m then _ else ∞)
    rw [ite_eq_left hf]
    apply le_sInf
    rintro a ⟨fs, hfs, hc, rfl⟩
    have hφ : MemLp (η ∘ f) 2 m := hη.comp_memLp hη0 hf
    have hφs : ∀ n, GloballyLipschitz (η ∘ fs n) ∧ MemLp (η ∘ fs n) 2 m := by
      intro n
      obtain ⟨L, hL⟩ := (hfs n).1
      exact ⟨⟨_, hη.comp hL⟩, hη.comp_memLp hη0 (hfs n).2⟩
    have hcφ : Tendsto (fun n => eLpNorm (fun x => η (fs n x)-η (f x)) 2 m) atTop (𝓝 0) := by
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le)
      intro n
      apply eLpNorm_mono
      intro x
      simpa only [Pi.sub_apply, Function.comp_apply, Real.norm_eq_abs, Real.dist_eq,
        NNReal.coe_one, one_mul] using
        hη.dist_le_mul (fs n x) (f x)
    apply (cheegerEnergy_le_liminf hφ hφs hcφ).trans
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    apply mul_le_mul_right
    apply lintegral_mono
    intro x
    exact pow_le_pow_left' (localSlope_comp_contraction hη (fs n) x) 2
  · simp only [cheegerEnergy, ite_eq_right hf, le_top]

end WeakHessian

end
end InlinedFile0

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Transport_BoundedHopfMapLipschitz
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open scoped ENNReal NNReal Topology BoundedContinuousFunction CompactlySupported
open scoped ENNReal NNReal Topology BoundedContinuousFunction
open scoped NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open scoped ENNReal NNReal Topology InnerProductSpace
open Set Filter Bornology
open MeasureTheory
open scoped ENNReal InnerProductSpace ComplexConjugate
open Set Filter
open scoped Topology ENNReal NNReal
open Set
open Set MeasureTheory CompactlySupported CompactlySupportedContinuousMap
open scoped Topology ENNReal NNReal InnerProductSpace
open scoped BoundedContinuousFunction
open Set MeasureTheory Filter
open Set Filter MeasureTheory Topology TopologicalSpace
open scoped ENNReal NNReal
open Set MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory ProbabilityTheory
open Set Filter Topology Bornology
open scoped InnerProductSpace
open Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

attribute [local instance] Classical.propDecidable
namespace WeakHessianTransport
open WeakHessian MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {m : Measure X}

omit [MeasurableSpace X] [BorelSpace X] in
lemma boundedHopfMap_lipschitz (f : X →ᵇ ℝ) {t : ℝ} (ht : 0 < t) :
    GloballyLipschitz (boundedHopfMap f t : X → ℝ) := by
  have H := hopfLax_lipschitz_radius f.continuous (fun x => (boundedContinuous_bounds f x).1)
    (fun x => (boundedContinuous_bounds f x).2) (by linarith [norm_nonneg f]) ht
    (Real.sqrt_nonneg (2*t*(‖f‖-(-‖f‖))))
    (Real.sq_sqrt (by have := norm_nonneg f; nlinarith : 0 ≤ 2*t*(‖f‖-(-‖f‖)))).ge
  have he : (boundedHopfMap f t : X → ℝ) = hopfLax f t := funext (boundedHopfMap_apply_pos f ht)
  rw [he]
  exact ⟨_,H⟩

end WeakHessianTransport
end

end OAI
end

section
-- module Solutions.OAIQ52_WH.WeakHessian_Calculus_CompactHopfCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section
noncomputable section
namespace WeakHessianTransport
open WeakHessian Set Filter MeasureTheory
open scoped Topology ENNReal NNReal InnerProductSpace BoundedContinuousFunction

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
variable [CompleteSpace X] [ProperSpace X] [TopologicalSpace.SeparableSpace X]
variable {m : Measure X} [SigmaFinite m]

omit [BorelSpace X] [CompleteSpace X] [TopologicalSpace.SeparableSpace X] [SigmaFinite m] in
lemma compactHopf_uniform_data (_hfin : FiniteOnBoundedSets m) (f : X →ᵇ ℝ)
    (o : X) (hf : HasCompactSupport (f : X → ℝ)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ (R : ℝ) (L : ℝ≥0), 0 < R ∧ ∀ t ∈ Icc a b,
      tsupport (boundedHopfMap f t : X → ℝ) ⊆ Metric.closedBall o R ∧
      LipschitzWith L (boundedHopfMap f t : X → ℝ) := by
  obtain ⟨R,hR,hsub⟩ := hf.isCompact.isBounded.subset_closedBall_lt 0 o
  have hb : 0 < b := ha.trans_le hab
  let D := Real.sqrt (4*b*‖f‖)
  have hD : 0 ≤ D := Real.sqrt_nonneg _
  have hDs : D^2 = 4*b*‖f‖ := Real.sq_sqrt (by positivity)
  let L : ℝ≥0 := ⟨D/a+1/(2*a)+2*‖f‖,by positivity⟩
  refine ⟨R+b+‖f‖+1,L,by positivity,?_⟩
  intro t ht
  have ht0 := ha.trans_le ht.1
  constructor
  · apply closure_minimal _ Metric.isClosed_closedBall
    exact (boundedHopfMap_support_bound f o hR.le ((subset_tsupport f).trans hsub) ht0).trans
      (Metric.closedBall_subset_closedBall (by linarith [ht.2]))
  · have H := hopfLax_lipschitz_radius f.continuous
      (fun x => (boundedContinuous_bounds f x).1) (fun x => (boundedContinuous_bounds f x).2)
      (by linarith [norm_nonneg f]) ht0 hD (by rw [hDs]; nlinarith [norm_nonneg f,ht.2])
    have hL : (⟨D/t+1/(2*t)+(‖f‖-(-‖f‖)),by simp only [sub_neg_eq_add]; positivity⟩ : ℝ≥0) ≤ L := by
      change D/t+1/(2*t)+(‖f‖-(-‖f‖)) ≤ D/a+1/(2*a)+2*‖f‖
      have h1 := div_le_div_of_nonneg_left hD ha ht.1
      have h2 := div_le_div_of_nonneg_left (by norm_num : (0:ℝ) ≤ 1)
        (by positivity : 0 < 2*a) (by linarith [ht.1] : 2*a ≤ 2*t)
      linarith
    convert! H.weaken hL using 1
    all_goals try with_reducible_and_instances rfl
    funext x
    exact boundedHopfMap_apply_pos f ht0 x

end WeakHessianTransport

end
end

end OAI
end


