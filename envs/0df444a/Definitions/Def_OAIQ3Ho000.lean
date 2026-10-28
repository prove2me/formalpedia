-- Prove2me | Definitions.Def_OAIQ3Ho000
-- name    : OAIQ3Ho000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T05:03:21.356884+00:00
-- url     : https://prove2.me/theorems/6063164e-a13a-40af-8681-3c915e889238
-- title:
--   Definitions bundle OAIQ3Ho000 of the split of OpenAI, The hot spots conjecture for simply connected planar domains
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.StrictHotSpots.main_theorem`, carved from OpenAI's openai/math development (OpenAI, *The hot spots conjecture for simply connected planar domains*, OpenAI Math Release, September 24, 2026, result family 369, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 371 declarations of OpenAI's Lean: 94 definitions, 2 inductive types or structures, 5 instances and 270 theorems. The definitions and types are `OAI.CompactChart.transport`, `OAI.ReciprocalKernel.ConditionallyNegative`, `OAI.ReciprocalKernel.OnePositiveSquare`, `OAI.ReciprocalKernel.bordered`, `OAI.ReciprocalKernel.eliminate`, `OAI.ReciprocalKernel.pairing`, `OAI.SquaredDistanceKernel.ConditionallyNegative`, `OAI.SquaredDistanceKernel.anchored`, `OAI.SquaredDistanceKernel.lifted`, `OAI.StrictHotSpots.BanachResolvent.resolvent`, `OAI.StrictHotSpots.BoundarySign.cut`, `OAI.StrictHotSpots.BoundarySign.cutSupport`, `OAI.StrictHotSpots.BoundarySign.test_interior`, `OAI.StrictHotSpots.CircleSigns.weightedMoment`, `OAI.StrictHotSpots.ClosedEigenJet`, `OAI.StrictHotSpots.CompactKernel.invMap`, `OAI.StrictHotSpots.CompactKernel.kernelOp`, `OAI.StrictHotSpots.CompactKernel.l2Op`, `OAI.StrictHotSpots.CompactKernel.l2ResolvedKernel`, `OAI.StrictHotSpots.CompactKernel.l2SectionOp`, `OAI.StrictHotSpots.CompactKernel.quantize`, `OAI.StrictHotSpots.CompactKernel.rescaledKernel`, `OAI.StrictHotSpots.CompactKernel.sampleOp`, `OAI.StrictHotSpots.CompactKernel.scaledKernel`, `OAI.StrictHotSpots.CompactKernel.singularResolvedKernel`, `OAI.StrictHotSpots.CompactParameter.paramDeriv`, `OAI.StrictHotSpots.CompactRows.instMeasurableSpaceSubtypeAEEqFunRealMemAddSubgroupLpOfNatENNReal_solutions`, `OAI.StrictHotSpots.CompactRows.rowOperator`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.datumTrace`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.densityBound`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.diskMap`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.potential`, `OAI.StrictHotSpots.Conformal.ClosedDiskChart.pullDatum`, `OAI.StrictHotSpots.Conformal.CoordinatePlane`, `OAI.StrictHotSpots.Conformal.chartMeasure`, `OAI.StrictHotSpots.Conformal.coordinate`, `OAI.StrictHotSpots.Conformal.planeMul`, `OAI.StrictHotSpots.Conformal.potentialMeasure`, `OAI.StrictHotSpots.DiskH10.disk` and 56 more.
--
--   **Sources.** They come from these modules of lean/OAI/Analysis/HotSpots, in whole or in part: `HotSpots_BoundaryEnergy`, `HotSpots_BoundaryKernel`, `HotSpots_ClosedChart`, `HotSpots_Conformal`, `HotSpots_Douglas`, `HotSpots_DouglasEnergy`, `HotSpots_Eigenfunction`, `HotSpots_Green`, `HotSpots_GreenOperator`, `HotSpots_GreenSolution`, `HotSpots_Hodge`, `HotSpots_Multiplicity`, `HotSpots_Poisson`, `HotSpots_Pullback`, `HotSpots_Reciprocal`, `HotSpots_Riemann`, `HotSpots_Sobolev`, `HotSpots_Trace`, `HotSpots_Variational`.
--
--   **Imports.** It imports the published bundle `Def_HotSpots`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ3Ho002` and `OAIQ3Ho003`; the statements `OAI.StrictHotSpots.Conformal.ClosedDiskChart.noncritical`, `OAI.StrictHotSpots.H10.minimum` and `OAI.StrictHotSpots.H10.subcritical`; the proof of `OAI.StrictHotSpots.CircleSigns.disk_family_finrank_le_two`.
-- source:
--   OpenAI, The hot spots conjecture for simply connected planar domains, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 369; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Strict-hot-spots-and-absence-of-interior-critical-points-on-smooth-simply-connected-planar-domains-September-24-2026/main.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/HotSpots at commit adc7f12

import Mathlib
import Definitions.Def_HotSpots

section
-- module Solutions.OAIQ3_Hot.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Reciprocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section SingularLayer



namespace ReciprocalKernel

open Matrix Filter Topology
open scoped BigOperators

variable {ι : Type*} [Fintype ι]


def pairing (A : Matrix ι ι ℝ) (x y : ι → ℝ) : ℝ := x ⬝ᵥ A *ᵥ y



def OnePositiveSquare (A : Matrix ι ι ℝ) : Prop :=
  A.IsSymm ∧ ∀ x y : ι → ℝ, 0 < pairing A x x → pairing A x y = 0 → pairing A y y ≤ 0


def bordered (B : Matrix ι ι ℝ) (l : ι → ℝ) : Matrix (ι ⊕ Unit) (ι ⊕ Unit) ℝ :=
  Matrix.fromBlocks B (Matrix.of (fun i _ => l i)) (Matrix.of (fun _ j => l j)) 0


def ConditionallyNegative (D : Matrix ι ι ℝ) : Prop :=
  D.IsSymm ∧ ∀ x : ι → ℝ, (∑ i, x i) = 0 → pairing D x x ≤ 0


end ReciprocalKernel

namespace ReciprocalKernel
open Matrix
open scoped BigOperators
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


def eliminate (M : Matrix ι ι ℝ) (w : ι → ℝ) (z : ι) : Matrix ι ι ℝ :=
  Matrix.of fun i j => M i j + (w z / (1 - w z * M z z)) * M i z * M z j


open scoped Matrix.Norms.L2Operator

end ReciprocalKernel






open Filter
open scoped Topology
namespace StrictHotSpots.BanachResolvent
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def resolvent (A : E →L[ℝ] E) : E →L[ℝ] E := ∑' n : ℕ, A ^ n

end StrictHotSpots.BanachResolvent







open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal
namespace StrictHotSpots.CompactKernel

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma kernel_integrable (C : C(X × X, ℝ)) (f : C(X, ℝ)) :
    Integrable (fun z => f z • C.curry z) ν :=
  (f.continuous.smul C.curry.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)




def kernelOp (C : C(X × X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ z, f z • C.curry z ∂ν
      map_add' := by
        intro f g
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (kernel_integrable ν C f) (kernel_integrable ν C g)
      map_smul' := by
        intro r f
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul]
        exact integral_smul r _ }
    (ν.real univ * ‖C‖) (by
      intro f
      calc
        ‖∫ z, f z • C.curry z ∂ν‖ ≤ ∫ z, ‖f z • C.curry z‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ ∫ _ : X, ‖f‖ * ‖C‖ ∂ν := by
          apply integral_mono (kernel_integrable ν C f).norm (integrable_const _)
          intro z
          dsimp only
          rw [norm_smul]
          apply mul_le_mul (f.norm_coe_le_norm z) _ (norm_nonneg _) (norm_nonneg _)
          exact (ContinuousMap.norm_le _ (norm_nonneg C)).mpr fun x => C.norm_coe_le_norm (z,x)
        _ = ν.real univ * ‖C‖ * ‖f‖ := by simp [integral_const]; ring)


def sampleOp (π : SimpleFunc X X) (C : C(X × X, ℝ)) : C(X, ℝ) →L[ℝ] C(X, ℝ) :=
  ∑ z ∈ π.range, ν.real (π ⁻¹' {z}) • (ContinuousMap.evalCLM ℝ z).smulRight (C.curry z)

variable [Nonempty X]



def quantize (n : ℕ) : SimpleFunc X X := SimpleFunc.nearestPt (denseSeq X) n

end StrictHotSpots.CompactKernel


namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent
open scoped Topology ENNReal
variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

lemma integral_norm_L2_le (f : Lp ℝ 2 ν) :
    ∫ z, ‖f z‖ ∂ν ≤ ‖f‖ * ‖ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))‖ := by
  have he : ∫ z, ‖f z‖ ∂ν =
      inner ℝ |f| (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_abs f, ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) ν (1 : C(X, ℝ))]
      with z hz h1
    change ‖f z‖ = (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))) z * (|f|) z
    rw [hz, h1]
    simp [Real.norm_eq_abs]
  rw [he]
  simpa only [norm_abs_eq_norm] using real_inner_le_norm |f| (ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ)))

lemma l2kernel_integrable (C : C(X × X, ℝ)) (f : Lp ℝ 2 ν) :
    Integrable (fun z => f z • C.curry z) ν := by
  apply ((Lp.memLp f).integrable (by norm_num)).norm.mul_const ‖C‖ |>.mono'
    ((Lp.aestronglyMeasurable f).smul C.curry.continuous.aestronglyMeasurable)
  exact Eventually.of_forall fun z => by
    change ‖f z • C.curry z‖ ≤ _
    rw [norm_smul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (ContinuousMap.norm_le _ (norm_nonneg C)).mpr fun x => C.norm_coe_le_norm (z,x)



def l2SectionOp (C : C(X × X, ℝ)) : Lp ℝ 2 ν →L[ℝ] C(X, ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ z, f z • C.curry z ∂ν
      map_add' := by
        intro f g
        change (∫ z, (f+g) z • C.curry z ∂ν) = _
        calc
          _ = ∫ z, f z • C.curry z + g z • C.curry z ∂ν := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_add f g] with z hz
            rw [hz, Pi.add_apply, add_smul]
          _ = _ := integral_add (l2kernel_integrable ν C f) (l2kernel_integrable ν C g)
      map_smul' := by
        intro r f
        calc
          _ = ∫ z, r • (f z • C.curry z) ∂ν := by
            apply integral_congr_ae
            filter_upwards [Lp.coeFn_smul r f] with z hz
            simp [hz, mul_smul]
          _ = _ := integral_smul r _ }
    (‖C‖ * ‖ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))‖) (by
      intro f
      calc
        ‖∫ z, f z • C.curry z ∂ν‖ ≤ ∫ z, ‖f z • C.curry z‖ ∂ν := norm_integral_le_integral_norm _
        _ ≤ ∫ z, ‖f z‖ * ‖C‖ ∂ν := by
          apply integral_mono (l2kernel_integrable ν C f).norm
            (((Lp.memLp f).integrable (by norm_num)).norm.mul_const _)
          intro z
          dsimp only
          rw [norm_smul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact (ContinuousMap.norm_le _ (norm_nonneg C)).mpr fun x => C.norm_coe_le_norm (z,x)
        _ = (∫ z, ‖f z‖ ∂ν) * ‖C‖ := integral_mul_const _ _
        _ ≤ (‖f‖ * ‖ContinuousMap.toLp 2 ν ℝ (1 : C(X, ℝ))‖) * ‖C‖ :=
          mul_le_mul_of_nonneg_right (integral_norm_L2_le ν f) (norm_nonneg _)
        _ = _ := by ring)

def l2Op (C : C(X × X, ℝ)) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (ContinuousMap.toLp 2 ν ℝ).comp (l2SectionOp ν C)

end StrictHotSpots.CompactKernel


namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]

def invMap (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) : C(X, ℝ) :=
  ⟨fun x => (f x)⁻¹, f.continuous.inv₀ (fun x => (hf x).ne')⟩

def scaledKernel (C : C(X × X, ℝ)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x) :
    C(X × X, ℝ) :=
  ⟨fun p => C p * f p.1 / f p.2,
    (C.continuous.mul (f.continuous.comp continuous_fst)).div
      (f.continuous.comp continuous_snd) (fun p => (hf p.2).ne')⟩



def rescaledKernel (C : C(X × X, ℝ)) (f : C(X, ℝ)) (hf : ∀ x, 0 < f x)
    (A : C(X, ℝ) →L[ℝ] C(X, ℝ)) (x y : X) : ℝ :=
  f x * resolvent A (invMap f hf * C.curry y) x

end StrictHotSpots.CompactKernel

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set TopologicalSpace BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]


def l2ResolvedKernel (C : C(X × X, ℝ)) (x y : X) : ℝ :=
  C (y,x) + l2SectionOp ν C
    (resolvent (l2Op ν C) (ContinuousMap.toLp 2 ν ℝ (C.curry y))) x

end StrictHotSpots.CompactKernel




open MeasureTheory Filter
open scoped Topology ENNReal
namespace StrictHotSpots.L2Limits
variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

lemma norm_sq_eq_integral_sq (f : Lp ℝ 2 ν) :
    ‖f‖ ^ 2 = ∫ x, (f x)^2 ∂ν := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  change (∫ x, f x * f x ∂ν) = _
  simp only [pow_two]

lemma norm_toLp_sub_sq {f g : X → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, (f x - g x)^2 ∂ν := by
  rw [norm_sq_eq_integral_sq]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hf.toLp f) (hg.toLp g), hf.coeFn_toLp, hg.coeFn_toLp]
    with x hx hfx hgx
  simp only [hx, hfx, hgx, Pi.sub_apply]

lemma tendsto_toLp_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {f : ι → X → ℝ} {g b : X → ℝ}
    (hf : ∀ n, MemLp (f n) 2 ν) (hg : MemLp g 2 ν) (hb : MemLp b 2 ν)
    (hdom : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖f n x‖ ≤ b x)
    (hlim : ∀ᵐ x ∂ν, Tendsto (fun n => f n x) l (𝓝 (g x))) :
    Tendsto (fun n => (hf n).toLp (f n)) l (𝓝 (hg.toLp g)) := by
  have ht : Tendsto (fun n => ∫ x, (f n x - g x)^2 ∂ν) l (𝓝 0) := by
    have hm : ∀ᶠ n in l, AEStronglyMeasurable (fun x => (f n x-g x)^2) ν :=
      Eventually.of_forall fun n => ((hf n).sub hg).aestronglyMeasurable.pow 2
    have hd : ∀ᶠ n in l, ∀ᵐ x ∂ν, ‖(f n x-g x)^2‖ ≤ (b x+‖g x‖)^2 := by
      filter_upwards [hdom] with n hn
      filter_upwards [hn] with x hx
      have h1 : ‖f n x-g x‖ ≤ b x+‖g x‖ :=
        by linarith [norm_sub_le (f n x) (g x)]
      rw [Real.norm_eq_abs, abs_pow, ← Real.norm_eq_abs]
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hl : ∀ᵐ x ∂ν, Tendsto (fun n => (f n x-g x)^2) l (𝓝 (0 : ℝ)) := by
      filter_upwards [hlim] with x hx
      simpa using (hx.sub_const (g x)).pow 2
    simpa using tendsto_integral_filter_of_dominated_convergence
      (fun x => (b x+‖g x‖)^2) hm hd (hb.add hg.norm).integrable_sq hl
  have hs : Tendsto (fun n => ‖(hf n).toLp (f n)-hg.toLp g‖^2) l (𝓝 0) := by
    simpa only [norm_toLp_sub_sq] using ht
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hr

end StrictHotSpots.L2Limits

namespace StrictHotSpots.CompactKernel
open MeasureTheory Filter Set BanachResolvent ReciprocalKernel
open scoped Topology ENNReal
variable {X : Type} [MetricSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] (ν : Measure X) [IsFiniteMeasure ν]



def singularResolvedKernel (G : X → X → ℝ)
    (hG : ∀ x, MemLp (fun z => G z x) 2 ν)
    (T : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) (x y : X) : ℝ :=
  G x y + inner ℝ ((hG x).toLp (fun z => G z x))
    (resolvent T ((hG y).toLp (fun z => G z y)))

end StrictHotSpots.CompactKernel

end SingularLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section SquaredDistanceKernelLayer
noncomputable section
open Set Filter Topology
open scoped BigOperators InnerProductSpace
open scoped NNReal
namespace SquaredDistanceKernel

universe u
variable {X : Type u}


def ConditionallyNegative (D : Matrix X X ℝ) : Prop :=
  D.IsHermitian ∧ (∀ x, D x x = 0) ∧
    ∀ c : X →₀ ℝ, c.sum (fun _ a => a) = 0 →
      c.sum (fun x a => c.sum (fun y b => a * D x y * b)) ≤ 0

def anchored (D : Matrix X X ℝ) (o : X) : Matrix X X ℝ :=
  Matrix.of fun x y => (D x o + D y o - D x y) / 2

def lifted (G : Matrix X X ℝ) : Matrix X X (ℝ →L[ℝ] ℝ) :=
  Matrix.of fun x y => G x y • ContinuousLinearMap.id ℝ ℝ

end SquaredDistanceKernel
end
end SquaredDistanceKernelLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Sobolev
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer



open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
namespace StrictHotSpots




lemma test_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp φ 2 (volume.restrict Ω) :=
  MemLp.mono_measure Measure.restrict_le_self
    (hφ.continuous.memLp_of_hasCompactSupport hc)

lemma test_derivative_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : Plane) :
    MemLp (fun x => (fderiv ℝ φ x) e) 2 (volume.restrict Ω) :=
  MemLp.mono_measure Measure.restrict_le_self
    (((hφ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport (hc.fderiv_apply ℝ e))

lemma HasH1Gradient.add {Ω : Set Plane} {v w : Plane → ℝ} {g k : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hw : HasH1Gradient Ω w k) :
    HasH1Gradient Ω (v + w) (g + k) := by
  refine ⟨hv.1.add hw.1, hv.2.1.add hw.2.1, ?_⟩
  intro φ hφ hc hs e
  have hi1 : Integrable (fun x => v x * (fderiv ℝ φ x) e) (volume.restrict Ω) :=
    hv.1.integrable_mul (test_derivative_memLp hφ hc e)
  have hi2 : Integrable (fun x => w x * (fderiv ℝ φ x) e) (volume.restrict Ω) :=
    hw.1.integrable_mul (test_derivative_memLp hφ hc e)
  have hj1 : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
    (hv.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
  have hj2 : Integrable (fun x => inner ℝ (k x) e * φ x) (volume.restrict Ω) :=
    (hw.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
  simp only [Pi.add_apply, inner_add_left, add_mul]
  rw [integral_add hi1 hi2, integral_add hj1 hj2,
    hv.2.2 φ hφ hc hs e, hw.2.2 φ hφ hc hs e]
  ring

lemma HasH1Gradient.smul {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (a : ℝ) :
    HasH1Gradient Ω (a • v) (a • g) := by
  refine ⟨hv.1.const_smul a, hv.2.1.const_smul a, ?_⟩
  intro φ hφ hc hs e
  simp only [Pi.smul_apply, smul_eq_mul, real_inner_smul_left, mul_assoc,
    integral_const_mul]
  rw [hv.2.2 φ hφ hc hs e]
  ring

lemma HasH1Gradient.sub {Ω : Set Plane} {v w : Plane → ℝ} {g k : Plane → Plane}
    (hv : HasH1Gradient Ω v g) (hw : HasH1Gradient Ω w k) :
    HasH1Gradient Ω (v - w) (g - k) := by
  simpa [sub_eq_add_neg] using hv.add (hw.smul (-1))

lemma integrable_mul_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => f x * φ x) volume := by
  have hh : Continuous (fun x => f x * φ x) :=
    (hf.mul hφ.continuousOn).continuous_of_tsupport_subset hΩ
      (tsupport_mul_subset_right.trans hs)
  exact hh.integrable_of_hasCompactSupport hc.mul_left

lemma setIntegral_mul_test {Ω : Set Plane} {f φ : Plane → ℝ}
    (hs : tsupport φ ⊆ Ω) :
    (∫ x in Ω, f x * φ x) = ∫ x, f x * φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hs hh)), mul_zero]

lemma integral_mul_test_fderiv {Ω : Set Plane} {f φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (e : Plane) :
    (∫ x in Ω, f x * (fderiv ℝ φ x) e) =
      -(∫ x in Ω, (fderiv ℝ f x) e * φ x) := by
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdf : ContinuousOn (fun x => (fderiv ℝ f x) e) Ω :=
    (hf.continuousOn_fderiv_of_isOpen hΩ (by simp)).clm_apply continuousOn_const
  have hds : tsupport (fun x => (fderiv ℝ φ x) e) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ e).trans hs
  rw [setIntegral_mul_test hds, setIntegral_mul_test hs]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_test hΩ hdf hφ.continuous hc hs)
    (integrable_mul_test hΩ hf.continuousOn hdφ (hc.fderiv_apply ℝ e) hds)
    (integrable_mul_test hΩ hf.continuousOn hφ.continuous hc hs)
    (fun x hx => ((hf x (hs hx)).contDiffAt (hΩ.mem_nhds (hs hx))).differentiableAt (by simp))
    (fun x _ => hφ.differentiable (by simp) x)

lemma HasH1Gradient.of_contDiffOn {Ω : Set Plane} {f : Plane → ℝ}
    (hΩ : IsOpen Ω) (hf : ContDiffOn ℝ ∞ f Ω)
    (hv : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp (gradient f) 2 (volume.restrict Ω)) :
    HasH1Gradient Ω f (gradient f) := by
  refine ⟨hv, hg, ?_⟩
  intro φ hφ hc hs e
  simpa only [inner_gradient_left] using integral_mul_test_fderiv hΩ hf hφ hc hs e

lemma test_gradient_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    MemLp (gradient φ) 2 (volume.restrict Ω) := by
  apply MemLp.mono_measure Measure.restrict_le_self
  have hdc : Continuous (gradient φ) :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp
      (hφ.continuous_fderiv (by simp))
  apply hdc.memLp_of_hasCompactSupport
  exact (hc.fderiv ℝ).comp_left (map_zero (InnerProductSpace.toDual ℝ Plane).symm)

lemma HasH1Gradient.test {Ω : Set Plane} {φ : Plane → ℝ}
    (hΩ : IsOpen Ω) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    HasH1Gradient Ω φ (gradient φ) :=
  .of_contDiffOn hΩ hφ.contDiffOn (test_memLp hφ hc) (test_gradient_memLp hφ hc)


lemma test_vector_memLp {Ω : Set Plane} {φ : Plane → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (e : Plane) :
    MemLp (fun x => φ x • e) 2 (volume.restrict Ω) :=
  (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) e).comp_memLp'
    (test_memLp hφ hc)


structure H1Test (Ω : Set Plane) where
  val : Plane → ℝ
  smooth : ContDiff ℝ ∞ val
  compact : HasCompactSupport val
  support : tsupport val ⊆ Ω

namespace H1Test
variable {Ω : Set Plane}

def derivative (φ : H1Test Ω) (e : Plane) : Lp ℝ 2 (volume.restrict Ω) :=
  (test_derivative_memLp φ.smooth φ.compact e).toLp (fun x => (fderiv ℝ φ.val x) e)

def vector (φ : H1Test Ω) (e : Plane) : Lp Plane 2 (volume.restrict Ω) :=
  (test_vector_memLp φ.smooth φ.compact e).toLp (fun x => φ.val x • e)
end H1Test

abbrev H1Ambient (Ω : Set Plane) := WithLp 2
  (Lp ℝ 2 (volume.restrict Ω) × Lp Plane 2 (volume.restrict Ω))


def h1Graph (Ω : Set Plane) : Submodule ℝ (H1Ambient Ω) where
  carrier := {v | ∀ (φ : H1Test Ω) (e : Plane),
    ⟪v.fst, φ.derivative e⟫_ℝ + ⟪v.snd, φ.vector e⟫_ℝ = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw φ e
    simp only [WithLp.add_fst, WithLp.add_snd, inner_add_left]
    linear_combination hv φ e + hw φ e
  smul_mem' := by
    intro a v hv φ e
    simp only [WithLp.smul_fst, WithLp.smul_snd, real_inner_smul_left]
    linear_combination a * hv φ e

lemma h1Graph_closed (Ω : Set Plane) : IsClosed (h1Graph Ω : Set (H1Ambient Ω)) := by
  change IsClosed {v : H1Ambient Ω | ∀ (φ : H1Test Ω) (e : Plane),
    ⟪v.fst, φ.derivative e⟫_ℝ + ⟪v.snd, φ.vector e⟫_ℝ = 0}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro φ
  apply isClosed_iInter
  intro e
  apply isClosed_eq _ continuous_const
  exact (((WithLp.fstL 2 ℝ _ _).continuous.inner continuous_const).add
    ((WithLp.sndL 2 ℝ _ _).continuous.inner continuous_const))

abbrev H1 (Ω : Set Plane) := h1Graph Ω

instance H1.completeSpace (Ω : Set Plane) : CompleteSpace (H1 Ω) :=
  (h1Graph_closed Ω).completeSpace_coe

lemma h1Graph_mem_iff (Ω : Set Plane) (v : H1Ambient Ω) :
    v ∈ h1Graph Ω ↔ HasH1Gradient Ω v.fst v.snd := by
  have hscalar (φ : H1Test Ω) (e : Plane) :
      ⟪v.fst, φ.derivative e⟫_ℝ = ∫ x in Ω, v.fst x * (fderiv ℝ φ.val x) e := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(test_derivative_memLp (Ω := Ω) φ.smooth φ.compact e).coeFn_toLp] with x hx
    simp only [H1Test.derivative] at *
    simp [hx, RCLike.inner_apply, mul_comm]
  have hvector (φ : H1Test Ω) (e : Plane) :
      ⟪v.snd, φ.vector e⟫_ℝ = ∫ x in Ω, inner ℝ (v.snd x) e * φ.val x := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(test_vector_memLp (Ω := Ω) φ.smooth φ.compact e).coeFn_toLp] with x hx
    simp only [H1Test.vector] at *
    rw [hx, inner_smul_right]
    simp [mul_comm]
  constructor
  · intro hv
    refine ⟨Lp.memLp _, Lp.memLp _, ?_⟩
    intro φ hφ hc hs e
    have h := hv (H1Test.mk φ hφ hc hs) e
    rw [hscalar, hvector] at h
    exact eq_neg_of_add_eq_zero_left h
  · intro hv φ e
    rw [hscalar, hvector, hv.2.2 φ.val φ.smooth φ.compact φ.support e]
    exact neg_add_cancel _

lemma HasH1Gradient.congr {Ω : Set Plane} {v w : Plane → ℝ} {g k : Plane → Plane}
    (h : HasH1Gradient Ω v g) (hv : v =ᵐ[volume.restrict Ω] w)
    (hg : g =ᵐ[volume.restrict Ω] k) : HasH1Gradient Ω w k := by
  refine ⟨(memLp_congr_ae hv).mp h.1, (memLp_congr_ae hg).mp h.2.1, ?_⟩
  intro φ hφ hc hs e
  calc
    (∫ x in Ω, w x * (fderiv ℝ φ x) e) = ∫ x in Ω, v x * (fderiv ℝ φ x) e := by
      apply integral_congr_ae
      filter_upwards [hv] with x hx
      rw [hx]
    _ = -(∫ x in Ω, inner ℝ (g x) e * φ x) := h.2.2 φ hφ hc hs e
    _ = -(∫ x in Ω, inner ℝ (k x) e * φ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]

def HasH1Gradient.toH1 {Ω : Set Plane} {v : Plane → ℝ} {g : Plane → Plane}
    (h : HasH1Gradient Ω v g) : H1 Ω :=
  ⟨WithLp.toLp 2 (h.1.toLp v, h.2.1.toLp g),
    (h1Graph_mem_iff Ω _).mpr (h.congr h.1.coeFn_toLp.symm h.2.1.coeFn_toLp.symm)⟩

namespace H1
variable {Ω : Set Plane}
def value : H1 Ω →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  (WithLp.fstL 2 ℝ _ _).comp (h1Graph Ω).subtypeL

def grad : H1 Ω →L[ℝ] Lp Plane 2 (volume.restrict Ω) :=
  (WithLp.sndL 2 ℝ _ _).comp (h1Graph Ω).subtypeL

lemma hasH1Gradient (u : H1 Ω) : HasH1Gradient Ω (value u) (grad u) :=
  (h1Graph_mem_iff Ω u.val).mp u.property

lemma norm_sq (u : H1 Ω) : ‖u‖^2 = ‖value u‖^2 + ‖grad u‖^2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 u.val

lemma value_toH1 {v : Plane → ℝ} {g : Plane → Plane} (h : HasH1Gradient Ω v g) :
    value h.toH1 = h.1.toLp v := rfl

lemma grad_unique (hΩ : IsOpen Ω) {v : Plane → ℝ} {g k : Plane → Plane}
    (hg : HasH1Gradient Ω v g) (hk : HasH1Gradient Ω v k) :
    g =ᵐ[volume.restrict Ω] k := by
  have hi (e : Plane) : ∀ᵐ x ∂volume.restrict Ω, inner ℝ (g x - k x) e = 0 := by
    have hl := ((hg.2.1.sub hk.2.1).inner_const (𝕜 := ℝ) e).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have ht := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (μ := volume.restrict Ω) (hl.locallyIntegrableOn Ω)
      (fun φ hφ hc hs => show (∫ x in Ω, φ x • inner ℝ (g x - k x) e) = 0 from by
        have hgφ := hg.2.2 φ hφ hc hs e
        have hkφ := hk.2.2 φ hφ hc hs e
        have hgi : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
          (hg.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        have hki : Integrable (fun x => inner ℝ (k x) e * φ x) (volume.restrict Ω) :=
          (hk.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        simp only [smul_eq_mul, inner_sub_left, mul_sub]
        rw [integral_sub (by simpa [Pi.mul_apply, mul_comm] using hgi) (by simpa [Pi.mul_apply, mul_comm] using hki)]
        simp_rw [mul_comm (φ _)]
        linarith)
    filter_upwards [ht, ae_restrict_mem hΩ.measurableSet] with x hx hxΩ
    exact hx hxΩ
  have hb : ∀ᵐ x ∂volume.restrict Ω, ∀ i : Fin 2,
      inner ℝ (g x - k x) (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 :=
    ae_all_iff.mpr fun i => hi _
  filter_upwards [hb] with x hx
  have hz : g x - k x = 0 := by
    ext i
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right] using hx i
  exact sub_eq_zero.mp hz

lemma value_injective (hΩ : IsOpen Ω) : Function.Injective (value (Ω := Ω)) := by
  intro u v huv
  have hdata : (value u : Plane → ℝ) =ᵐ[volume.restrict Ω] value v := by rw [huv]
  have hgrad := grad_unique hΩ ((hasH1Gradient u).congr hdata (Filter.EventuallyEq.refl _ _))
    (hasH1Gradient v)
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  exact Prod.ext huv (Lp.ext hgrad)
end H1


def smoothTestSpace (Ω : Set Plane) : Submodule ℝ (Plane → ℝ) where
  carrier := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ Ω}
  zero_mem' := by
    refine ⟨contDiff_const, ?_, by simp⟩
    change IsCompact (tsupport (0 : Plane → ℝ))
    simp
  add_mem' := by
    rintro f g ⟨hf, hfc, hfs⟩ ⟨hg, hgc, hgs⟩
    exact ⟨hf.add hg, hfc.add hgc, (tsupport_add f g).trans (union_subset hfs hgs)⟩
  smul_mem' := by
    rintro a f ⟨hf, hfc, hfs⟩
    exact ⟨hf.const_smul a, hfc.smul_left,
      (tsupport_smul_subset_right (fun _ => a) f).trans hfs⟩

def smoothTestToH1 {Ω : Set Plane} (hΩ : IsOpen Ω) : smoothTestSpace Ω →ₗ[ℝ] H1 Ω where
  toFun f := (HasH1Gradient.test hΩ f.property.1 f.property.2.1).toH1
  map_add' f g := by
    apply H1.value_injective hΩ
    exact (test_memLp (Ω := Ω) f.property.1 f.property.2.1).toLp_add
      (test_memLp (Ω := Ω) g.property.1 g.property.2.1)
  map_smul' a f := by
    apply H1.value_injective hΩ
    exact (test_memLp (Ω := Ω) f.property.1 f.property.2.1).toLp_const_smul a


def h10Submodule {Ω : Set Plane} (hΩ : IsOpen Ω) : Submodule ℝ (H1 Ω) :=
  (smoothTestToH1 hΩ).range.topologicalClosure

abbrev H10 {Ω : Set Plane} (hΩ : IsOpen Ω) := h10Submodule hΩ

instance H10.innerProductSpace {Ω : Set Plane} (hΩ : IsOpen Ω) :
    InnerProductSpace ℝ (H10 hΩ) := (h10Submodule hΩ).innerProductSpace

namespace H10
variable {Ω : Set Plane} (hΩ : IsOpen Ω)

def value : H10 hΩ →L[ℝ] Lp ℝ 2 (volume.restrict Ω) :=
  H1.value.comp (h10Submodule hΩ).subtypeL

def grad : H10 hΩ →L[ℝ] Lp Plane 2 (volume.restrict Ω) :=
  H1.grad.comp (h10Submodule hΩ).subtypeL


def energy : H10 hΩ →L[ℝ] H10 hΩ →L[ℝ] ℝ := by
  letI : NormedSpace ℝ (H10 hΩ) := (H10.innerProductSpace hΩ).toNormedSpace
  let a : Lp Plane 2 (volume.restrict Ω) →L[ℝ]
      Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ := innerSL ℝ
  let b : H10 hΩ →L[ℝ] Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ :=
    a.comp (grad hΩ)
  let c : Lp Plane 2 (volume.restrict Ω) →L[ℝ] H10 hΩ →L[ℝ] ℝ := ContinuousLinearMap.flip (E := H10 hΩ) (F := Lp Plane 2 (volume.restrict Ω)) b
  let d : H10 hΩ →L[ℝ] H10 hΩ →L[ℝ] ℝ := c.comp (grad hΩ)
  exact ContinuousLinearMap.flip (E := H10 hΩ) (F := H10 hΩ) d

@[simp] lemma energy_apply (u v : H10 hΩ) :
    energy hΩ u v = inner ℝ (grad hΩ u) (grad hΩ v) := rfl

end H10
end StrictHotSpots




open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff

namespace StrictHotSpots

namespace DiskH10

def disk : Set Plane := Metric.ball 0 1

end DiskH10
end StrictHotSpots

open scoped Laplacian







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Green
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian

open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace

open scoped Convolution



open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
namespace StrictHotSpots.CompactParameter

variable {s k : Set ℂ} {F : ℂ × ℂ → ℝ}

def paramDeriv (F : ℂ × ℂ → ℝ) (e : ℂ) (p : ℂ × ℂ) : ℝ :=
  fderiv ℝ F p (e,0)

end StrictHotSpots.CompactParameter




open InnerProductSpace
open scoped Laplacian ContDiff


namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma diskOpen : IsOpen disk := Metric.isOpen_ball

noncomputable def complexIso : ℂ ≃ₗᵢ[ℝ] Plane := Complex.orthonormalBasisOneI.repr

end StrictHotSpots.PlaneGreen







end WeightedLayer

end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer
section WeightedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace ENNReal NNReal
open Set Filter MeasureTheory InnerProductSpace NormedSpace
open scoped Topology ContDiff
open scoped Laplacian
open Set MeasureTheory Filter InnerProductSpace Bornology
open scoped Topology Laplacian ContDiff RealInnerProductSpace
open scoped Convolution
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ContDiff Convolution Laplacian
open InnerProductSpace
open scoped Laplacian ContDiff

open Filter Set
open scoped Topology




open MeasureTheory Filter
open scoped Topology ENNReal





open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal


open MeasureTheory Filter Metric Set
open scoped Topology ENNReal



open MeasureTheory Filter
open scoped ENNReal Topology InnerProductSpace



open MeasureTheory Filter InnerProductSpace
open scoped ENNReal Topology







open scoped InnerProductSpace


open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

lemma diskBounded : Bornology.IsBounded disk := Metric.isBounded_ball

instance diskFinite : IsFiniteMeasure (volume.restrict disk) :=
  isFiniteMeasure_restrict.mpr diskBounded.measure_lt_top.ne

lemma complexIso_disk_preserving : MeasurePreserving complexIso.symm
    (volume.restrict disk) (volume.restrict (Metric.ball (0 : ℂ) 1)) := by
  have h := complexIso.symm.measurePreserving.restrict_preimage
    (show MeasurableSet (Metric.ball (0 : ℂ) 1) from measurableSet_ball)
  have he : complexIso.symm ⁻¹' Metric.ball (0 : ℂ) 1 = disk := by
    ext x
    simp [disk]
  rwa [he] at h

end StrictHotSpots.PlaneGreen


open MeasureTheory
open scoped InnerProductSpace ENNReal


open MeasureTheory Filter
open scoped ENNReal InnerProductSpace

end WeightedLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section FullBoundaryCombinedLayer

section PlaneBoundaryLayer
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10
abbrev Boundary := {s : Plane // ‖s‖ = 1}

end StrictHotSpots.PlaneGreen
end
end PlaneBoundaryLayer


end FullBoundaryCombinedLayer

end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Douglas
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase

noncomputable section

section DouglasMonomialCombinedLayer
open Set MeasureTheory AddCircle
open scoped InnerProductSpace
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

instance haar_nullSingleton : NullSingletonClass (@haarAddCircle T hT) := by
  constructor
  intro t
  have hv : (volume : Measure (AddCircle T)) {t} = 0 := by
    simpa only [Metric.closedBall_zero,mul_zero,min_eq_right hT.out.le,ENNReal.ofReal_zero]
      using (AddCircle.volume_closedBall T (x := t) 0)
  rw [volume_eq_smul_haarAddCircle,Measure.smul_apply,smul_eq_mul] at hv
  exact (mul_eq_zero.mp hv).resolve_left (ENNReal.ofReal_pos.mpr hT.out).ne'


def polynomial (n : ℕ) (a : ℕ → ℂ) : C(AddCircle T, ℂ) :=
  ∑ k ∈ Finset.range n, a k • fourier (k : ℤ)

omit hT in
lemma polynomial_apply (n : ℕ) (a : ℕ → ℂ) (s : AddCircle T) :
    polynomial n a s = ∑ k ∈ Finset.range n, a k * fourier (k : ℤ) s := by
  simp [polynomial,ContinuousMap.sum_apply]

lemma integral_norm_sq_polynomial (n : ℕ) (a : ℕ → ℂ) :
    (∫ s : AddCircle T, ‖polynomial n a s‖^2 ∂haarAddCircle) =
      ∑ k ∈ Finset.range n, ‖a k‖^2 := by
  have ho := (orthonormal_fourier (T := T)).comp (fun n : ℕ => (n : ℤ))
    Int.ofNat_injective
  have he := ho.inner_sum a a (Finset.range n)
  have he' : inner ℂ ((ContinuousMap.toLp 2 (@haarAddCircle T hT) ℂ) (polynomial n a))
      ((ContinuousMap.toLp 2 (@haarAddCircle T hT) ℂ) (polynomial n a)) =
        ∑ k ∈ Finset.range n, star (a k) * a k := by
    simpa only [polynomial,map_sum,map_smul,Function.comp_apply,RCLike.star_def]
      using he
  rw [ContinuousMap.inner_toLp] at he'
  have hi : Integrable (fun s : AddCircle T =>
      polynomial n a s * star (polynomial n a s)) haarAddCircle := by
    exact ((polynomial (T:=T) n a).memLp haarAddCircle ℂ (p:=2)).integrable_mul
      ((polynomial (T:=T) n a).memLp haarAddCircle ℂ (p:=2)).star
  have hr := congrArg Complex.re he'
  have hir : (∫ s : AddCircle T, polynomial n a s *
      (starRingEnd ℂ) (polynomial n a s) ∂haarAddCircle).re =
      ∫ s : AddCircle T, (polynomial n a s *
        (starRingEnd ℂ) (polynomial n a s)).re ∂haarAddCircle := (integral_re hi).symm
  rw [hir] at hr
  simpa only [RCLike.star_def,Complex.re_sum,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    mul_neg,neg_mul,sub_neg_eq_add,← Complex.normSq_eq_norm_sq,Complex.normSq_apply] using hr

omit hT in
lemma fourier_nat (n : ℕ) (s : AddCircle T) :
    fourier (n : ℤ) s = (s.toCircle : ℂ)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,fourier_add,ih,fourier_one,pow_succ]

omit hT in
lemma polynomial_geom (n : ℕ) (s t : AddCircle T) :
    polynomial n (fun k => (t.toCircle : ℂ)^(n-1-k)) s =
      ∑ k ∈ Finset.range n, (s.toCircle : ℂ)^k * (t.toCircle : ℂ)^(n-1-k) := by
  rw [polynomial_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [fourier_nat,mul_comm]

lemma normalized_monomial_quotient (n : ℕ) (t : AddCircle T) :
    (∫ s : AddCircle T,
      ‖((s.toCircle : ℂ)^n-(t.toCircle : ℂ)^n) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2 ∂haarAddCircle) = (n : ℝ) := by
  have hnull : ∀ᵐ s : AddCircle T ∂haarAddCircle, s ≠ t := by
    simp only [ae_iff, not_not, measure_singleton, Set.ofPred_eq_eq_singleton]
  have he : (fun s : AddCircle T =>
      ‖((s.toCircle : ℂ)^n-(t.toCircle : ℂ)^n) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) =ᵐ[haarAddCircle]
      (fun s => ‖polynomial n (fun k => (t.toCircle : ℂ)^(n-1-k)) s‖^2) := by
    filter_upwards [hnull] with s hs
    have hne : (s.toCircle : ℂ)-(t.toCircle : ℂ) ≠ 0 := by
      intro hz
      apply hs
      exact injective_toCircle hT.out.ne' (Subtype.ext (sub_eq_zero.mp hz))
    rw [polynomial_geom,← geom_sum₂_mul _ _ n,mul_div_cancel_right₀ _ hne]
  rw [integral_congr_ae he,integral_norm_sq_polynomial]
  simp [norm_pow,Circle.norm_coe]



theorem monomial_double_integral (n : ℕ) :
    (∫ t : AddCircle T, ∫ s : AddCircle T,
      ‖((s.toCircle : ℂ)^n-(t.toCircle : ℂ)^n) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) = T^2 * (n : ℝ) := by
  rw [volume_eq_smul_haarAddCircle]
  simp_rw [integral_smul_measure,ENNReal.toReal_ofReal hT.out.le,smul_eq_mul,
    normalized_monomial_quotient]
  simp [pow_two,mul_assoc]

end StrictHotSpots.Douglas
end DouglasMonomialCombinedLayer

section LipschitzBoundaryEnergyCombinedLayer
open Set Filter MeasureTheory AddCircle
open scoped Topology
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]


def boundaryDifference (h : AddCircle T → ℂ) (p : AddCircle T × AddCircle T) : ℂ :=
  (h p.1-h p.2) / ((p.1.toCircle : ℂ)-(p.2.toCircle : ℂ))


def ChordLipschitz (K : ℝ) (h : AddCircle T → ℂ) : Prop :=
  ∀ s t, ‖h s-h t‖ ≤ K*‖(s.toCircle : ℂ)-(t.toCircle : ℂ)‖

omit hT in
lemma boundaryDifference_bound {K : ℝ} (hK : 0 ≤ K) {h : AddCircle T → ℂ}
    (hh : ChordLipschitz K h) (p : AddCircle T × AddCircle T) :
    ‖boundaryDifference h p‖ ≤ K := by
  rw [boundaryDifference,norm_div]
  by_cases hz : (p.1.toCircle : ℂ)-(p.2.toCircle : ℂ) = 0
  · simpa only [hz,norm_zero,div_zero] using hK
  · exact (div_le_iff₀ (norm_pos_iff.mpr hz)).mpr (hh p.1 p.2)

omit hT in
lemma measurable_boundaryDifference {h : AddCircle T → ℂ} (hh : Continuous h) :
    Measurable (boundaryDifference h) := by
  apply Measurable.div
  · exact (hh.measurable.comp measurable_fst).sub (hh.measurable.comp measurable_snd)
  · exact ((continuous_subtype_val.comp continuous_toCircle).measurable.comp measurable_fst).sub
      ((continuous_subtype_val.comp continuous_toCircle).measurable.comp measurable_snd)

lemma integrable_boundaryDifference_sq {K : ℝ} (hK : 0 ≤ K)
    {h : AddCircle T → ℂ} (hc : Continuous h) (hh : ChordLipschitz K h) :
    Integrable (fun p => ‖boundaryDifference h p‖^2) := by
  refine (integrable_const (K^2)).mono'
    ((measurable_boundaryDifference hc).norm.pow_const 2).aestronglyMeasurable ?_
  exact ae_of_all _ fun p => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (boundaryDifference_bound hK hh p) 2


def boundaryEnergy (h : AddCircle T → ℂ) : ℝ :=
  ∫ p : AddCircle T × AddCircle T, ‖boundaryDifference h p‖^2



end StrictHotSpots.Douglas
end LipschitzBoundaryEnergyCombinedLayer

section BoundaryFourierCrossCombinedLayer
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

omit hT in
lemma fourier_shift (m : ℤ) (s r : AddCircle T) :
    fourier m (s+r) = fourier m s * fourier m r := by
  simp only [fourier_apply,smul_add,toCircle_add,Circle.coe_mul]


def boundaryModeCross (m n : ℤ) (p : AddCircle T × AddCircle T) : ℂ :=
  ((fourier m p.1-fourier m p.2)*conj (fourier n p.1-fourier n p.2)) /
    ((‖(p.1.toCircle : ℂ)-(p.2.toCircle : ℂ)‖^2 : ℝ) : ℂ)

omit hT in
lemma boundaryModeCross_shift (m n : ℤ) (p : AddCircle T × AddCircle T)
    (r : AddCircle T) :
    boundaryModeCross m n (p+(r,r)) = boundaryModeCross m n p * fourier (m-n) r := by
  rw [show m-n = m+(-n) by rfl,fourier_add,fourier_neg]
  simp only [boundaryModeCross,Prod.fst_add,Prod.snd_add,fourier_shift,toCircle_add,
    Circle.coe_mul]
  rw [← sub_mul,← sub_mul,← sub_mul]
  simp only [norm_mul,Circle.norm_coe,mul_one,map_mul]
  ring


theorem boundaryModeCross_integral_zero {m n : ℤ} (hmn : m ≠ n) :
    (∫ p : AddCircle T × AddCircle T, boundaryModeCross m n p) = 0 := by
  let r : AddCircle T := (T/2/(m-n) : ℝ)
  have hf : fourier (m-n) r = -1 := by
    simpa only [zero_add,fourier_eval_zero,Int.cast_sub,r] using
      fourier_add_half_inv_index (sub_ne_zero.mpr hmn) hT.out (0 : AddCircle T)
  let : (volume : Measure (AddCircle T × AddCircle T)).IsAddRightInvariant := ⟨fun g =>
    ((measurePreserving_add_right (volume : Measure (AddCircle T)) g.1).prod
      (measurePreserving_add_right (volume : Measure (AddCircle T)) g.2)).map_eq⟩
  apply integral_eq_zero_of_add_right_eq_neg (g := (r,r))
  intro p
  rw [boundaryModeCross_shift,hf,mul_neg_one]

end StrictHotSpots.Douglas
end BoundaryFourierCrossCombinedLayer

section DouglasBulkModeCombinedLayer
open Set MeasureTheory Metric
open scoped Topology
namespace StrictHotSpots.Douglas

lemma integral_disk_norm_pow (n : ℕ) :
    (∫ z : ℂ in ball 0 1, ‖z‖^n) = (2*Real.pi)/(n+2) := by
  classical
  let f : ℂ → ℝ := (ball 0 1).indicator (fun z => ‖z‖^n)
  have h1 : (∫ z : ℂ in ball 0 1, ‖z‖^n) =
      ∫ p in polarCoord.target, p.1 * f (Complex.polarCoord.symm p) := by
    rw [← integral_indicator measurableSet_ball]
    exact (Complex.integral_comp_polarCoord_symm f).symm
  rw [h1]
  have he : polarCoord.target.indicator
      (fun p : ℝ × ℝ => p.1 * f (Complex.polarCoord.symm p)) =
      ((Ioo (0:ℝ) 1) ×ˢ (Ioo (-Real.pi) Real.pi)).indicator
        (fun p => p.1^(n+1)) := by
    funext p
    have hf : f (Complex.polarCoord.symm p) =
        if |p.1| < 1 then |p.1|^n else 0 := by
      change (if Complex.polarCoord.symm p ∈ ball (0:ℂ) 1 then
        ‖Complex.polarCoord.symm p‖^n else 0) = _
      rw [mem_ball_zero_iff,Complex.norm_polarCoord_symm]
    by_cases hr : 0 < p.1
    · by_cases ht : -Real.pi < p.2 ∧ p.2 < Real.pi
      · by_cases hR : p.1 < 1 <;>
          simp only [Set.indicator_apply,polarCoord_target,mem_prod,mem_Ioi,mem_Ioo,
            hr,ht,hR,and_self,ite_true,ite_false,hf,abs_of_pos hr,mul_zero,
            pow_succ,mul_comm,false_and,and_false]
      · simp only [Set.indicator_apply,polarCoord_target,mem_prod,mem_Ioi,mem_Ioo,
          hr,ht,and_false,ite_false]
    · simp [polarCoord_target,hr]
  rw [← integral_indicator polarCoord.open_target.measurableSet,he,
    integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  have hi : (∫ r : ℝ in Ioo 0 1, r^(n+1)) = 1/(n+2) := by
    rw [← integral_Ioc_eq_integral_Ioo,← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_pow]
    simp [add_assoc]
    norm_num
  have hp := setIntegral_prod_mul (fun r : ℝ => r^(n+1)) (fun _ : ℝ => (1:ℝ))
    (Ioo 0 1) (Ioo (-Real.pi) Real.pi) (μ:=volume) (ν:=volume)
  simp only [mul_one] at hp
  rw [Measure.volume_eq_prod ℝ ℝ,hp,hi]
  have hpos : 0 ≤ Real.pi - -Real.pi := by linarith [Real.pi_pos]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,Real.volume_Ioo,ENNReal.toReal_ofReal hpos,
    smul_eq_mul,mul_one]
  ring



lemma holomorphic_mode_energy (n : ℕ) :
    (∫ z : ℂ in ball 0 1, 2 * ‖((n+1 : ℕ) : ℂ) * z^n‖^2) =
      2*Real.pi*(n+1) := by
  simp_rw [norm_mul,Complex.norm_natCast,norm_pow,mul_pow,← pow_mul]
  rw [integral_const_mul,integral_const_mul,integral_disk_norm_pow]
  push_cast
  field_simp

end StrictHotSpots.Douglas
end DouglasBulkModeCombinedLayer

section DouglasModesCombinedLayer
open Set MeasureTheory Metric AddCircle InnerProductSpace
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas


def harmonicMode : ℤ → ℂ → ℂ
  | .ofNat n, z => z^n
  | .negSucc n, z => conj (z^(n+1))

lemma harmonicMode_boundary {T : ℝ} (m : ℤ) (s : AddCircle T) :
    harmonicMode m s.toCircle = fourier m s := by
  cases m with
  | ofNat n => exact (fourier_nat n s).symm
  | negSucc n =>
    change conj ((s.toCircle : ℂ)^(n+1)) = fourier (-(↑(n+1) : ℤ)) s
    rw [fourier_neg,fourier_nat]

lemma harmonicMode_harmonic (m : ℤ) (z : ℂ) : HarmonicAt (harmonicMode m) z := by
  cases m with
  | ofNat n => exact (analyticAt_id.pow n).harmonicAt
  | negSucc n => exact (analyticAt_id.pow (n+1)).harmonicAt_conj

lemma harmonicMode_continuous (m : ℤ) : Continuous (harmonicMode m) := by
  cases m with
  | ofNat n =>
    change Continuous (fun z : ℂ => z^n)
    fun_prop
  | negSucc n =>
    change Continuous (fun z : ℂ => conj (z^(n+1)))
    fun_prop

lemma harmonicMode_poisson (m : ℤ) {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • harmonicMode m) 0 1 =
      harmonicMode m z := by
  have hk : ContinuousOn (poissonKernel 0 z) (sphere 0 1) := by
    unfold poissonKernel
    refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
    intro w hw
    simp only [sub_zero]
    apply pow_ne_zero
    apply norm_ne_zero_iff.mpr
    apply sub_ne_zero.mpr
    intro he
    have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
    have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    rw [he] at hw'
    linarith
  have hci : CircleIntegrable (poissonKernel 0 z • harmonicMode m) 0 1 :=
    (hk.smul (harmonicMode_continuous m).continuousOn).circleIntegrable (by norm_num)
  have hr : HarmonicOnNhd (Complex.reCLM ∘ harmonicMode m) (closedBall 0 1) :=
    fun w _ => (harmonicMode_harmonic m w).comp_CLM Complex.reCLM
  have hi : HarmonicOnNhd (Complex.imCLM ∘ harmonicMode m) (closedBall 0 1) :=
    fun w _ => (harmonicMode_harmonic m w).comp_CLM Complex.imCLM
  apply Complex.ext
  · have h := hr.circleAverage_poissonKernel_smul hz
    change Complex.reCLM (Real.circleAverage _ _ _) = _
    rw [← Complex.reCLM.circleAverage_comp_comm hci]
    have he : Complex.reCLM ∘ (poissonKernel 0 z • harmonicMode m) =
        poissonKernel 0 z • (Complex.reCLM ∘ harmonicMode m) := by
      funext w
      exact map_smul Complex.reCLM (poissonKernel 0 z w) (harmonicMode m w)
    rw [he]
    exact h
  · have h := hi.circleAverage_poissonKernel_smul hz
    change Complex.imCLM (Real.circleAverage _ _ _) = _
    rw [← Complex.imCLM.circleAverage_comp_comm hci]
    have he : Complex.imCLM ∘ (poissonKernel 0 z • harmonicMode m) =
        poissonKernel 0 z • (Complex.imCLM ∘ harmonicMode m) := by
      funext w
      exact map_smul Complex.imCLM (poissonKernel 0 z w) (harmonicMode m w)
    rw [he]
    exact h

lemma fderiv_pow_mode (n : ℕ) (z e : ℂ) :
    fderiv ℝ (fun w : ℂ => w^(n+1)) z e = e * ((n+1 : ℕ) * z^n) := by
  have h := (hasDerivAt_pow (n+1) z).hasFDerivAt.restrictScalars ℝ
  simpa using congrArg (fun L : ℂ →L[ℝ] ℂ => L e) h.fderiv

lemma fderiv_conj_mode (n : ℕ) (z e : ℂ) :
    fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e =
      conj (e * ((n+1 : ℕ) * z^n)) := by
  have h := (hasDerivAt_pow (n+1) z).hasFDerivAt.restrictScalars ℝ
  have hc := Complex.conjCLE.toContinuousLinearMap.hasFDerivAt.comp z h
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) hc.fderiv
  change fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e =
    conj (e * ((n+1 : ℕ) * z^(n+1-1))) at he
  simpa only [Nat.add_sub_cancel] using he



theorem harmonicMode_energy (m : ℤ) :
    (∫ z : ℂ in ball 0 1,
      ‖fderiv ℝ (harmonicMode m) z 1‖^2 + ‖fderiv ℝ (harmonicMode m) z Complex.I‖^2) =
      2*Real.pi*(m.natAbs : ℝ) := by
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change (∫ z : ℂ in ball 0 1,
        ‖fderiv ℝ (fun _ : ℂ => (1:ℂ)) z 1‖^2 +
        ‖fderiv ℝ (fun _ : ℂ => (1:ℂ)) z Complex.I‖^2) = _
      simp
    | succ n =>
      change (∫ z : ℂ in ball 0 1,
        ‖fderiv ℝ (fun w : ℂ => w^(n+1)) z 1‖^2 +
        ‖fderiv ℝ (fun w : ℂ => w^(n+1)) z Complex.I‖^2) = _
      simp_rw [fderiv_pow_mode,one_mul,norm_mul,Complex.norm_I,one_mul,← two_mul]
      change _ = 2*Real.pi*((n+1 : ℕ) : ℝ)
      simpa only [norm_mul,Nat.cast_add,Nat.cast_one] using holomorphic_mode_energy n
  | negSucc n =>
    change (∫ z : ℂ in ball 0 1,
      ‖fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z 1‖^2 +
      ‖fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z Complex.I‖^2) = _
    simp_rw [fderiv_conj_mode,Complex.norm_conj,one_mul,norm_mul,Complex.norm_I,
      one_mul,← two_mul]
    simpa only [norm_mul,Int.natAbs_negSucc,Nat.cast_add,Nat.cast_one,Nat.succ_eq_add_one]
      using holomorphic_mode_energy n


theorem fourier_double_integral {T : ℝ} [Fact (0 < T)] (m : ℤ) :
    (∫ t : AddCircle T, ∫ s : AddCircle T,
      ‖(fourier m s-fourier m t) / ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) =
        T^2 * (m.natAbs : ℝ) := by
  cases m with
  | ofNat n =>
    have h := monomial_double_integral (T:=T) n
    simp_rw [← fourier_nat] at h
    exact h
  | negSucc n =>
    change (∫ t : AddCircle T, ∫ s : AddCircle T,
      ‖(fourier (-(↑(n+1) : ℤ)) s-fourier (-(↑(n+1) : ℤ)) t) /
        ((s.toCircle : ℂ)-(t.toCircle : ℂ))‖^2) = _
    simp_rw [fourier_neg,← map_sub,norm_div,Complex.norm_conj,← norm_div,fourier_nat]
    exact monomial_double_integral (n+1)


end StrictHotSpots.Douglas
end DouglasModesCombinedLayer

section BoundaryFourierIntegrableCombinedLayer
open Set Filter MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

lemma norm_pow_sub_pow_of_unit {a b : ℂ} (ha : ‖a‖=1) (hb : ‖b‖=1) (n : ℕ) :
    ‖a^n-b^n‖ ≤ (n:ℝ)*‖a-b‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have he : a^(n+1)-b^(n+1)=a^n*(a-b)+(a^n-b^n)*b := by ring
    rw [he]
    calc
      _ ≤ ‖a^n*(a-b)‖+‖(a^n-b^n)*b‖ := norm_add_le _ _
      _ = ‖a-b‖+‖a^n-b^n‖ := by rw [norm_mul,norm_mul,norm_pow,ha,hb]; simp
      _ ≤ ‖a-b‖+(n:ℝ)*‖a-b‖ := add_le_add_right ih _
      _ = ((n+1:ℕ):ℝ)*‖a-b‖ := by push_cast; ring

omit hT in
lemma chordLipschitz_fourier (m : ℤ) : ChordLipschitz (m.natAbs:ℝ) (@fourier T m) := by
  intro s t
  cases m with
  | ofNat n =>
    change ‖fourier (n:ℤ) s-fourier (n:ℤ) t‖ ≤ (n:ℝ)*_
    rw [fourier_nat,fourier_nat]
    exact norm_pow_sub_pow_of_unit (Circle.norm_coe _) (Circle.norm_coe _) n
  | negSucc n =>
    change ‖fourier (-(↑(n+1) : ℤ)) s-fourier (-(↑(n+1) : ℤ)) t‖ ≤ _
    rw [fourier_neg,fourier_neg,← map_sub,Complex.norm_conj,fourier_nat,fourier_nat]
    exact norm_pow_sub_pow_of_unit (Circle.norm_coe _) (Circle.norm_coe _) (n+1)

omit hT in
lemma boundaryModeCross_eq (m n : ℤ) (p : AddCircle T × AddCircle T) :
    boundaryModeCross m n p =
      boundaryDifference (fourier m) p * conj (boundaryDifference (fourier n) p) := by
  simp only [boundaryModeCross,boundaryDifference,map_div₀,div_mul_div_comm,
    Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma integrable_boundaryModeCross (m n : ℤ) :
    Integrable (boundaryModeCross (T:=T) m n) := by
  have he : boundaryModeCross (T:=T) m n = fun p =>
      boundaryDifference (fourier m) p * conj (boundaryDifference (fourier n) p) := by
    funext p; exact boundaryModeCross_eq m n p
  rw [he]
  refine (integrable_const ((m.natAbs:ℝ)*(n.natAbs:ℝ))).mono' ?_ ?_
  · exact ((measurable_boundaryDifference (fourier m).continuous).mul
      ((Complex.continuous_conj.measurable).comp
        (measurable_boundaryDifference (fourier n).continuous))).aestronglyMeasurable
  · exact ae_of_all _ fun p => by
      rw [norm_mul,Complex.norm_conj]
      exact mul_le_mul (boundaryDifference_bound (by positivity) (chordLipschitz_fourier m) p)
        (boundaryDifference_bound (by positivity) (chordLipschitz_fourier n) p)
        (norm_nonneg _) (by positivity)

lemma boundaryDifference_sq_integral (m : ℤ) :
    (∫ p : AddCircle T × AddCircle T, ‖boundaryDifference (fourier m) p‖^2) =
      T^2*(m.natAbs:ℝ) := by
  have hi := integrable_boundaryDifference_sq (by positivity : 0 ≤ (m.natAbs:ℝ))
    (fourier (T:=T) m).continuous (chordLipschitz_fourier m)
  rw [Measure.volume_eq_prod (AddCircle T) (AddCircle T),integral_prod _ hi]
  have he : (∫ x : AddCircle T, ∫ y : AddCircle T,
      ‖boundaryDifference (fourier m) (x,y)‖^2) =
    (∫ x : AddCircle T, ∫ y : AddCircle T,
      ‖(fourier m y-fourier m x)/((y.toCircle:ℂ)-(x.toCircle:ℂ))‖^2) := by
    apply integral_congr_ae
    exact ae_of_all _ fun x => integral_congr_ae (ae_of_all _ fun y => by
      simp only [boundaryDifference,norm_div]
      rw [norm_sub_rev (fourier m x),norm_sub_rev (x.toCircle:ℂ)])
  exact he.trans (fourier_double_integral m)


theorem boundaryModeCross_integral (m n : ℤ) :
    (∫ p : AddCircle T × AddCircle T, boundaryModeCross m n p) =
      if m=n then ((T^2*(m.natAbs:ℝ):ℝ):ℂ) else 0 := by
  classical
  split_ifs with h
  · subst n
    have he : boundaryModeCross (T:=T) m m = fun p =>
        ((‖boundaryDifference (fourier m) p‖^2:ℝ):ℂ) := by
      funext p
      rw [boundaryModeCross_eq,Complex.mul_conj,Complex.normSq_eq_norm_sq]
    rw [he,integral_complex_ofReal,boundaryDifference_sq_integral]
  · exact boundaryModeCross_integral_zero h

end StrictHotSpots.Douglas
end BoundaryFourierIntegrableCombinedLayer

section BoundaryFourierPolynomialCombinedLayer
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ} [hT : Fact (0 < T)]

def boundaryPolynomial (S : Finset ℤ) (a : ℤ → ℂ) (x : AddCircle T) : ℂ :=
  ∑ m ∈ S, a m * fourier m x

omit hT in
lemma boundaryDifference_polynomial (S : Finset ℤ) (a : ℤ → ℂ)
    (p : AddCircle T × AddCircle T) :
    boundaryDifference (boundaryPolynomial S a) p =
      ∑ m ∈ S, a m * boundaryDifference (fourier m) p := by
  simp only [boundaryDifference,boundaryPolynomial,← Finset.sum_sub_distrib,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro m _
  ring

omit hT in
lemma boundaryPolynomial_sq (S : Finset ℤ) (a : ℤ → ℂ)
    (p : AddCircle T × AddCircle T) :
    ((‖boundaryDifference (boundaryPolynomial S a) p‖^2 : ℝ) : ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (a m*conj (a n))*boundaryModeCross m n p := by
  rw [← Complex.normSq_eq_norm_sq,← Complex.mul_conj,boundaryDifference_polynomial]
  simp only [map_sum,Finset.sum_mul,Finset.mul_sum,map_mul,boundaryModeCross_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  ring

lemma boundaryPolynomial_energy (S : Finset ℤ) (a : ℤ → ℂ) :
    boundaryEnergy (boundaryPolynomial (T:=T) S a) =
      T^2 * ∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖^2 := by
  classical
  have hi (m n : ℤ) : Integrable (fun p : AddCircle T × AddCircle T =>
      (a m*conj (a n))*boundaryModeCross m n p) :=
    (integrable_boundaryModeCross m n).const_mul _
  have he : (fun p : AddCircle T × AddCircle T =>
      ((‖boundaryDifference (boundaryPolynomial S a) p‖^2 : ℝ) : ℂ)) =
      fun p => ∑ m ∈ S, ∑ n ∈ S, (a m*conj (a n))*boundaryModeCross m n p := by
    funext p; exact boundaryPolynomial_sq S a p
  apply Complex.ofReal_injective
  change ((∫ p : AddCircle T × AddCircle T,
      ‖boundaryDifference (boundaryPolynomial S a) p‖^2 : ℝ) : ℂ) = _
  rw [← integral_complex_ofReal,he]
  rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hi m n))]
  simp_rw [integral_finsetSum S (fun n _ => hi _ n),integral_const_mul,
    boundaryModeCross_integral]
  have hs : (∑ m ∈ S, ∑ n ∈ S,
      (a m*conj (a n))*(if m=n then ((T^2*(m.natAbs:ℝ):ℝ):ℂ) else 0)) =
      ∑ m ∈ S, (a m*conj (a m))*((T^2*(m.natAbs:ℝ):ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm
      simp [Ne.symm hnm]
    · exact fun h => (h hm).elim
  rw [hs]
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_mul,
    Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

end StrictHotSpots.Douglas
end BoundaryFourierPolynomialCombinedLayer

section DiskRotationCombinedLayer
open Set MeasureTheory Metric
namespace StrictHotSpots.Douglas

def circleRotation (u : Circle) : ℂ ≃ₗᵢ[ℝ] ℂ where
  toFun z := u • z
  invFun z := u⁻¹ • z
  left_inv z := inv_smul_smul u z
  right_inv z := smul_inv_smul u z
  map_add' z w := smul_add u z w
  map_smul' r z := smul_comm u r z
  norm_map' z := Circle.norm_smul u z

lemma circleRotation_apply (u : Circle) (z : ℂ) : circleRotation u z = (u:ℂ)*z := rfl

lemma integral_disk_rotation (u : Circle) (f : ℂ → ℂ) :
    (∫ z : ℂ in ball 0 1, f ((u:ℂ)*z)) = ∫ z : ℂ in ball 0 1, f z := by
  have h := (circleRotation u).measurePreserving.integral_comp
    (circleRotation u).toHomeomorph.measurableEmbedding ((ball (0:ℂ) 1).indicator f)
  have he : (fun z => (ball (0:ℂ) 1).indicator f (circleRotation u z)) =
      (ball (0:ℂ) 1).indicator (fun z => f ((u:ℂ)*z)) := by
    funext z
    have hm : circleRotation u z ∈ ball (0:ℂ) 1 ↔ z ∈ ball 0 1 := by
      simp only [mem_ball_zero_iff,(circleRotation u).norm_map]
    by_cases hz : z ∈ ball (0:ℂ) 1
    · rw [Set.indicator_of_mem (hm.mpr hz),Set.indicator_of_mem hz,circleRotation_apply]
    · rw [Set.indicator_of_notMem (mt hm.mp hz),Set.indicator_of_notMem hz]
  rw [he,integral_indicator measurableSet_ball,integral_indicator measurableSet_ball] at h
  exact h
end StrictHotSpots.Douglas
end DiskRotationCombinedLayer

section DiskMonomialCrossCombinedLayer
open Set MeasureTheory Metric AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

lemma monomialCross_rotation (k l : ℕ) (s : AddCircle (2*Real.pi)) (z : ℂ) :
    ((s.toCircle:ℂ)*z)^k * conj (((s.toCircle:ℂ)*z)^l) =
      (z^k * conj (z^l)) * fourier ((k:ℤ)-(l:ℤ)) s := by
  rw [sub_eq_add_neg,fourier_add,fourier_neg,fourier_nat,fourier_nat]
  simp only [mul_pow,map_mul]
  ring

lemma integral_disk_monomial_cross_zero {k l : ℕ} (hkl : k ≠ l) :
    (∫ z : ℂ in ball 0 1, z^k * conj (z^l)) = 0 := by
  let r : AddCircle (2*Real.pi) := ((2*Real.pi)/2/((k:ℤ)-(l:ℤ)) : ℝ)
  have hne : (k:ℤ)-(l:ℤ) ≠ 0 := sub_ne_zero.mpr (Int.ofNat_inj.not.mpr hkl)
  have hf : fourier ((k:ℤ)-(l:ℤ)) r = -1 := by
    simpa only [zero_add,fourier_eval_zero,r,Int.cast_sub] using
      fourier_add_half_inv_index hne (by positivity : 0 < 2*Real.pi)
        (0 : AddCircle (2*Real.pi))
  have h := integral_disk_rotation r.toCircle (fun z => z^k*conj (z^l))
  simp_rw [monomialCross_rotation,hf,mul_neg_one] at h
  rw [integral_neg] at h
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  apply Complex.ext <;> simp only [Complex.neg_re,Complex.neg_im,Complex.zero_re,
    Complex.zero_im] at * <;> linarith

end StrictHotSpots.Douglas
end DiskMonomialCrossCombinedLayer

section DiskModeCrossCombinedLayer
open Set MeasureTheory Metric
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

def bulkModeCross (m n : ℤ) (z : ℂ) : ℂ :=
  fderiv ℝ (harmonicMode m) z 1 * conj (fderiv ℝ (harmonicMode n) z 1) +
  fderiv ℝ (harmonicMode m) z Complex.I * conj (fderiv ℝ (harmonicMode n) z Complex.I)

lemma bulkModeCross_zero_left (n : ℤ) (z : ℂ) : bulkModeCross 0 n z = 0 := by
  have he : harmonicMode 0 = fun _ : ℂ => (1:ℂ) := by funext w; change w^0=1; exact pow_zero w
  simp [bulkModeCross,he]

lemma bulkModeCross_symm (m n : ℤ) (z : ℂ) :
    bulkModeCross m n z = conj (bulkModeCross n m z) := by
  simp only [bulkModeCross,map_add,map_mul,Complex.conj_conj]
  ring

lemma bulkModeCross_pos (k l : ℕ) (z : ℂ) :
    bulkModeCross (k+1:ℕ) (l+1:ℕ) z =
      (2*((k+1:ℕ):ℂ)*((l+1:ℕ):ℂ))*(z^k * conj (z^l)) := by
  change (fderiv ℝ (fun w : ℂ => w^(k+1)) z 1 *
      conj (fderiv ℝ (fun w : ℂ => w^(l+1)) z 1) +
    fderiv ℝ (fun w : ℂ => w^(k+1)) z Complex.I *
      conj (fderiv ℝ (fun w : ℂ => w^(l+1)) z Complex.I)) = _
  simp only [fderiv_pow_mode,one_mul,map_mul,map_natCast,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma bulkModeCross_neg (k l : ℕ) (z : ℂ) :
    bulkModeCross (Int.negSucc k) (Int.negSucc l) z =
      conj (bulkModeCross (k+1:ℕ) (l+1:ℕ) z) := by
  change (fderiv ℝ (fun w : ℂ => conj (w^(k+1))) z 1 *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z 1) +
    fderiv ℝ (fun w : ℂ => conj (w^(k+1))) z Complex.I *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z Complex.I)) = _
  rw [bulkModeCross_pos]
  simp only [fderiv_conj_mode,one_mul,map_mul,map_natCast,Complex.conj_I,
    Complex.conj_conj,map_ofNat]
  ring_nf
  simp only [map_neg,Complex.conj_I]
  ring_nf
  rw [Complex.I_sq]
  ring

lemma bulkModeCross_mixed (k l : ℕ) (z : ℂ) :
    bulkModeCross (k+1:ℕ) (Int.negSucc l) z = 0 := by
  change (fderiv ℝ (fun w : ℂ => w^(k+1)) z 1 *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z 1) +
    fderiv ℝ (fun w : ℂ => w^(k+1)) z Complex.I *
      conj (fderiv ℝ (fun w : ℂ => conj (w^(l+1))) z Complex.I)) = _
  simp only [fderiv_pow_mode,fderiv_conj_mode,one_mul,Complex.conj_conj]
  ring_nf
  simp only [Complex.I_sq]
  ring

lemma bulkModeCross_continuous (m n : ℤ) : Continuous (bulkModeCross m n) := by
  have hp (k l : ℕ) : Continuous (bulkModeCross (k+1:ℕ) (l+1:ℕ)) := by
    simp_rw [funext (bulkModeCross_pos k l)]
    fun_prop
  have hn (k l : ℕ) : Continuous (bulkModeCross (Int.negSucc k) (Int.negSucc l)) := by
    simp_rw [funext (bulkModeCross_neg k l)]
    exact Complex.continuous_conj.comp (hp k l)
  cases m with
  | ofNat k =>
    cases k with
    | zero =>
      change Continuous (bulkModeCross 0 n)
      rw [funext (bulkModeCross_zero_left n)]; exact continuous_const
    | succ k =>
      cases n with
      | ofNat l =>
        cases l with
        | zero =>
          have he : bulkModeCross (k+1:ℕ) 0 = fun _ => (0:ℂ) := by
            funext z; rw [bulkModeCross_symm,bulkModeCross_zero_left,map_zero]
          change Continuous (bulkModeCross (k+1:ℕ) 0)
          rw [he]; exact continuous_const
        | succ l => exact hp k l
      | negSucc l =>
        change Continuous (bulkModeCross (k+1:ℕ) (Int.negSucc l))
        rw [funext (bulkModeCross_mixed k l)]; exact continuous_const
  | negSucc k =>
    cases n with
    | ofNat l =>
      cases l with
      | zero =>
        have he : bulkModeCross (Int.negSucc k) 0 = fun _ => (0:ℂ) := by
          funext z; rw [bulkModeCross_symm,bulkModeCross_zero_left,map_zero]
        change Continuous (bulkModeCross (Int.negSucc k) 0)
        rw [he]; exact continuous_const
      | succ l =>
        have he : bulkModeCross (Int.negSucc k) (l+1:ℕ) = fun _ => (0:ℂ) := by
          funext z; rw [bulkModeCross_symm,bulkModeCross_mixed,map_zero]
        change Continuous (bulkModeCross (Int.negSucc k) (l+1:ℕ))
        rw [he]; exact continuous_const
    | negSucc l => exact hn k l

lemma bulkModeCross_integrable (m n : ℤ) :
    IntegrableOn (bulkModeCross m n) (ball 0 1) :=
  ((bulkModeCross_continuous m n).continuousOn.integrableOn_compact (isCompact_closedBall 0 1)).mono_set
    ball_subset_closedBall

end StrictHotSpots.Douglas
end DiskModeCrossCombinedLayer

section DiskModeGramCombinedLayer
open Set MeasureTheory Metric
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

lemma bulkModeCross_self_integral (m : ℤ) :
    (∫ z : ℂ in ball 0 1, bulkModeCross m m z) =
      ((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) := by
  have he : bulkModeCross m m = fun z =>
      ((‖fderiv ℝ (harmonicMode m) z 1‖^2 +
        ‖fderiv ℝ (harmonicMode m) z Complex.I‖^2 : ℝ):ℂ) := by
    funext z
    simp only [bulkModeCross,Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_add]
  rw [he,integral_complex_ofReal,harmonicMode_energy]

lemma bulkModeCross_pos_integral_zero {k l : ℕ} (hkl : k ≠ l) :
    (∫ z : ℂ in ball 0 1, bulkModeCross (k+1:ℕ) (l+1:ℕ) z) = 0 := by
  simp_rw [bulkModeCross_pos]
  rw [integral_const_mul,integral_disk_monomial_cross_zero hkl,mul_zero]

lemma bulkModeCross_zero_right (m : ℤ) (z : ℂ) : bulkModeCross m 0 z = 0 := by
  rw [bulkModeCross_symm,bulkModeCross_zero_left,map_zero]

lemma bulkModeCross_opposite (k l : ℕ) (z : ℂ) :
    bulkModeCross (Int.negSucc k) (l+1:ℕ) z = 0 := by
  rw [bulkModeCross_symm,bulkModeCross_mixed,map_zero]

lemma bulkModeCross_integral_zero {m n : ℤ} (hmn : m ≠ n) :
    (∫ z : ℂ in ball 0 1, bulkModeCross m n z) = 0 := by
  cases m with
  | ofNat k =>
    cases k with
    | zero =>
      change (∫ z : ℂ in ball 0 1, bulkModeCross 0 n z) = 0
      simp_rw [bulkModeCross_zero_left]; exact integral_zero _ _
    | succ k =>
      cases n with
      | ofNat l =>
        cases l with
        | zero =>
          change (∫ z : ℂ in ball 0 1, bulkModeCross (k+1:ℕ) 0 z) = 0
          simp_rw [bulkModeCross_zero_right]; exact integral_zero _ _
        | succ l =>
          exact bulkModeCross_pos_integral_zero (fun h => hmn (by subst l; rfl))
      | negSucc l =>
        change (∫ z : ℂ in ball 0 1, bulkModeCross (k+1:ℕ) (Int.negSucc l) z) = 0
        simp_rw [bulkModeCross_mixed]; exact integral_zero _ _
  | negSucc k =>
    cases n with
    | ofNat l =>
      cases l with
      | zero =>
        change (∫ z : ℂ in ball 0 1, bulkModeCross (Int.negSucc k) 0 z) = 0
        simp_rw [bulkModeCross_zero_right]; exact integral_zero _ _
      | succ l =>
        change (∫ z : ℂ in ball 0 1, bulkModeCross (Int.negSucc k) (l+1:ℕ) z) = 0
        simp_rw [bulkModeCross_opposite]; exact integral_zero _ _
    | negSucc l =>
      simp_rw [bulkModeCross_neg]
      rw [integral_conj,bulkModeCross_pos_integral_zero (fun h => hmn (by subst l; rfl)),map_zero]


theorem bulkModeCross_integral (m n : ℤ) :
    (∫ z : ℂ in ball 0 1, bulkModeCross m n z) =
      if m=n then ((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) else 0 := by
  classical
  split_ifs with h
  · subst n; exact bulkModeCross_self_integral m
  · exact bulkModeCross_integral_zero h
end StrictHotSpots.Douglas
end DiskModeGramCombinedLayer

section DouglasPolynomialCombinedLayer
open Set MeasureTheory Metric AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

def harmonicPolynomial (S : Finset ℤ) (a : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑ m ∈ S, a m * harmonicMode m z

lemma harmonicMode_differentiable (m : ℤ) : Differentiable ℝ (harmonicMode m) := by
  cases m with
  | ofNat n => exact differentiable_pow n
  | negSucc n =>
    exact Complex.conjCLE.toContinuousLinearMap.differentiable.comp (differentiable_pow (n+1))

lemma harmonicPolynomial_deriv (S : Finset ℤ) (a : ℤ → ℂ) (z e : ℂ) :
    fderiv ℝ (harmonicPolynomial S a) z e =
      ∑ m ∈ S, a m * fderiv ℝ (harmonicMode m) z e := by
  have h := HasFDerivAt.fun_sum (u:=S) (fun m _ =>
    ((harmonicMode_differentiable m z).hasFDerivAt.const_mul (a m)))
  have he := congrArg (fun L : ℂ →L[ℝ] ℂ => L e) h.fderiv
  change fderiv ℝ (fun y => ∑ i ∈ S, a i * harmonicMode i y) z e = _
  simpa using he

lemma harmonicPolynomial_sq (S : Finset ℤ) (a : ℤ → ℂ) (z : ℂ) :
    ((‖fderiv ℝ (harmonicPolynomial S a) z 1‖^2 +
       ‖fderiv ℝ (harmonicPolynomial S a) z Complex.I‖^2 : ℝ):ℂ) =
      ∑ m ∈ S, ∑ n ∈ S, (a m*conj (a n))*bulkModeCross m n z := by
  simp only [Complex.ofReal_add,← Complex.normSq_eq_norm_sq,← Complex.mul_conj,
    harmonicPolynomial_deriv,map_sum,Finset.sum_mul,Finset.mul_sum,map_mul]
  rw [← Finset.sum_add_distrib,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [bulkModeCross]
  ring

lemma harmonicPolynomial_energy (S : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z : ℂ in ball 0 1, ‖fderiv ℝ (harmonicPolynomial S a) z 1‖^2 +
        ‖fderiv ℝ (harmonicPolynomial S a) z Complex.I‖^2) =
      2*Real.pi * ∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖^2 := by
  classical
  have hi (m n : ℤ) : IntegrableOn (fun z : ℂ =>
      (a m*conj (a n))*bulkModeCross m n z) (ball 0 1) :=
    (bulkModeCross_integrable m n).const_mul _
  have he := funext (harmonicPolynomial_sq S a)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal,he]
  rw [integral_finsetSum S (fun m _ => integrable_finsetSum S (fun n _ => hi m n))]
  simp_rw [integral_finsetSum S (fun n _ => hi _ n),integral_const_mul,
    bulkModeCross_integral]
  have hs : (∑ m ∈ S, ∑ n ∈ S,
      (a m*conj (a n))*(if m=n then ((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) else 0)) =
      ∑ m ∈ S, (a m*conj (a m))*((2*Real.pi*(m.natAbs:ℝ):ℝ):ℂ) := by
    apply Finset.sum_congr rfl
    intro m hm
    rw [Finset.sum_eq_single m]
    · simp
    · intro n _ hnm
      simp [Ne.symm hnm]
    · exact fun h => (h hm).elim
  rw [hs]
  simp only [Complex.mul_conj,Complex.normSq_eq_norm_sq,Complex.ofReal_mul,
    Complex.ofReal_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

local instance instFactLtRealOfNatHMulPi_solutions_1 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩


theorem douglas_polynomial (S : Finset ℤ) (a : ℤ → ℂ) :
    (∫ z : ℂ in ball 0 1, ‖fderiv ℝ (harmonicPolynomial S a) z 1‖^2 +
        ‖fderiv ℝ (harmonicPolynomial S a) z Complex.I‖^2) =
    (1/(2*Real.pi))*boundaryEnergy (boundaryPolynomial (T:=2*Real.pi) S a) := by
  rw [harmonicPolynomial_energy,boundaryPolynomial_energy]
  field_simp

end StrictHotSpots.Douglas
end DouglasPolynomialCombinedLayer

section DouglasSeriesBoundsCombinedLayer
open Set MeasureTheory Metric Filter
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas

lemma harmonicMode_norm_le_one (m : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖harmonicMode m z‖ ≤ 1 := by
  cases m with
  | ofNat n =>
    change ‖z^n‖ ≤ 1
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz
  | negSucc n =>
    change ‖conj (z^(n+1))‖ ≤ 1
    rw [Complex.norm_conj,norm_pow]
    exact pow_le_one₀ (norm_nonneg z) hz

lemma harmonicMode_deriv_apply_bound (m : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) (e : ℂ) :
    ‖fderiv ℝ (harmonicMode m) z e‖ ≤ (m.natAbs:ℝ)*‖e‖ := by
  have hp (n : ℕ) : ‖e*((n+1:ℕ)*z^n)‖ ≤ ((n+1:ℕ):ℝ)*‖e‖ := by
    rw [norm_mul,norm_mul,Complex.norm_natCast,norm_pow]
    have h := mul_le_mul_of_nonneg_left (pow_le_one₀ (norm_nonneg z) hz (n:=n))
      (mul_nonneg (norm_nonneg e) (Nat.cast_nonneg (n+1) : (0:ℝ) ≤ (n+1:ℕ)))
    calc
      ‖e‖ * (((n+1:ℕ):ℝ) * ‖z‖^n) = (‖e‖ * ((n+1:ℕ):ℝ)) * ‖z‖^n := by ring
      _ ≤ (‖e‖ * ((n+1:ℕ):ℝ)) * 1 := h
      _ = ((n+1:ℕ):ℝ)*‖e‖ := by ring
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change ‖fderiv ℝ (fun _ : ℂ => (1:ℂ)) z e‖ ≤ _
      simp
    | succ n =>
      change ‖fderiv ℝ (fun w : ℂ => w^(n+1)) z e‖ ≤ ((n+1:ℕ):ℝ)*‖e‖
      rw [fderiv_pow_mode]
      exact hp n
  | negSucc n =>
    change ‖fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e‖ ≤ ((n+1:ℕ):ℝ)*‖e‖
    rw [fderiv_conj_mode,Complex.norm_conj]
    exact hp n

lemma harmonicMode_deriv_bound (m : ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖fderiv ℝ (harmonicMode m) z‖ ≤ (m.natAbs:ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  exact harmonicMode_deriv_apply_bound m hz



def harmonicSeries (a : ℤ → ℂ) (z : ℂ) : ℂ := ∑' m : ℤ, a m*harmonicMode m z

lemma harmonicSeries_summable {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : ‖z‖ ≤ 1) : Summable (fun m => a m*harmonicMode m z) := by
  apply Summable.of_norm_bounded ha
  intro m
  rw [norm_mul]
  simpa using mul_le_mul_of_nonneg_left (harmonicMode_norm_le_one m hz) (norm_nonneg (a m))

lemma harmonicSeries_deriv_summable {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun m => a m • fderiv ℝ (harmonicMode m) z) := by
  apply Summable.of_norm_bounded ha
  intro m
  rw [norm_smul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left (harmonicMode_deriv_bound m hz) (norm_nonneg (a m))

end StrictHotSpots.Douglas
end DouglasSeriesBoundsCombinedLayer

section DouglasSeriesDerivCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas

def firstMoment (a : ℤ → ℂ) : ℝ := ∑' m : ℤ, (m.natAbs:ℝ)*‖a m‖
lemma firstMoment_nonneg (a : ℤ → ℂ) : 0 ≤ firstMoment a :=
  tsum_nonneg (fun _m => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))

lemma harmonicSeries_hasFDerivAt {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    HasFDerivAt (harmonicSeries a) (∑' m : ℤ, a m • fderiv ℝ (harmonicMode m) z) z := by
  apply hasFDerivAt_tsum_of_isPreconnected (s:=ball (0:ℂ) 1) h1 isOpen_ball
    (convex_ball (0:ℂ) 1).isPreconnected
    (fun m w _ => (harmonicMode_differentiable m w).hasFDerivAt.const_mul (a m))
  · intro m w hw
    rw [norm_smul]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left
      (harmonicMode_deriv_bound m (mem_ball_zero_iff.mp hw).le) (norm_nonneg (a m))
  · exact mem_ball_self (by norm_num)
  · exact harmonicSeries_summable h0 (z:=0) (by simp)
  · exact hz

lemma harmonicPolynomial_deriv_bound {a : ℤ → ℂ}
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖))
    (S : Finset ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) (e : ℂ) :
    ‖fderiv ℝ (harmonicPolynomial S a) z e‖ ≤ firstMoment a * ‖e‖ := by
  rw [harmonicPolynomial_deriv]
  calc
    _ ≤ ∑ m ∈ S, ‖a m * fderiv ℝ (harmonicMode m) z e‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ((m.natAbs:ℝ)*‖a m‖)*‖e‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      convert mul_le_mul_of_nonneg_left (harmonicMode_deriv_apply_bound m hz e)
        (norm_nonneg (a m)) using 1; ring
    _ = (∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖)*‖e‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ firstMoment a * ‖e‖ := mul_le_mul_of_nonneg_right
      (h1.sum_le_tsum S (fun m _ => by positivity)) (norm_nonneg _)

lemma harmonicMode_deriv_continuous (m : ℤ) (e : ℂ) :
    Continuous (fun z => fderiv ℝ (harmonicMode m) z e) := by
  cases m with
  | ofNat n =>
    cases n with
    | zero =>
      change Continuous (fun z : ℂ => fderiv ℝ (fun _ : ℂ => (1:ℂ)) z e)
      simpa using (continuous_const : Continuous (fun _ : ℂ => (0:ℂ)))
    | succ n =>
      change Continuous (fun z : ℂ => fderiv ℝ (fun w : ℂ => w^(n+1)) z e)
      simp_rw [fderiv_pow_mode]
      fun_prop
  | negSucc n =>
    change Continuous (fun z : ℂ => fderiv ℝ (fun w : ℂ => conj (w^(n+1))) z e)
    simp_rw [fderiv_conj_mode]
    fun_prop

lemma harmonicPolynomial_deriv_continuous (S : Finset ℤ) (a : ℤ → ℂ) (e : ℂ) :
    Continuous (fun z => fderiv ℝ (harmonicPolynomial S a) z e) := by
  simp_rw [harmonicPolynomial_deriv]
  exact continuous_finsetSum _ (fun m _ => continuous_const.mul (harmonicMode_deriv_continuous m e))

lemma harmonicPolynomial_deriv_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) (e : ℂ) :
    Tendsto (fun S : Finset ℤ => fderiv ℝ (harmonicPolynomial S a) z e)
      atTop (𝓝 (fderiv ℝ (harmonicSeries a) z e)) := by
  rw [(harmonicSeries_hasFDerivAt h0 h1 hz).fderiv]
  have ht := (harmonicSeries_deriv_summable h1 (mem_ball_zero_iff.mp hz).le).hasSum
  have he := ((ContinuousLinearMap.apply ℝ ℂ e).continuous.tendsto _).comp ht
  change Tendsto (fun S : Finset ℤ => (∑ m ∈ S, a m • fderiv ℝ (harmonicMode m) z) e)
    atTop (𝓝 ((∑' m : ℤ, a m • fderiv ℝ (harmonicMode m) z) e)) at he
  simpa only [sum_apply,smul_apply,smul_eq_mul,harmonicPolynomial_deriv] using he

end StrictHotSpots.Douglas
end DouglasSeriesDerivCombinedLayer

section DouglasSeriesBoundaryCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas
variable {T : ℝ}

lemma harmonicSeries_boundary_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖)) (x : AddCircle T) :
    Tendsto (fun S : Finset ℤ => boundaryPolynomial S a x)
      atTop (𝓝 (harmonicSeries a x.toCircle)) := by
  have h := harmonicSeries_summable h0 (z:=(x.toCircle : ℂ)) (Circle.norm_coe x.toCircle).le
  have ht := h.hasSum
  change Tendsto (fun S : Finset ℤ => ∑ m ∈ S, a m * harmonicMode m x.toCircle)
    atTop (𝓝 (harmonicSeries a x.toCircle)) at ht
  simpa only [harmonicMode_boundary,boundaryPolynomial] using ht

lemma boundaryPolynomial_chordLipschitz {a : ℤ → ℂ}
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) (S : Finset ℤ) :
    ChordLipschitz (firstMoment a) (boundaryPolynomial (T:=T) S a) := by
  intro s t
  simp only [boundaryPolynomial,← Finset.sum_sub_distrib,← mul_sub]
  calc
    _ ≤ ∑ m ∈ S, ‖a m*(fourier m s-fourier m t)‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ((m.natAbs:ℝ)*‖a m‖)*‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      convert mul_le_mul_of_nonneg_left (chordLipschitz_fourier m s t)
        (norm_nonneg (a m)) using 1; ring
    _ = (∑ m ∈ S, (m.natAbs:ℝ)*‖a m‖)*‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ :=
      (Finset.sum_mul _ _ _).symm
    _ ≤ firstMoment a * ‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ :=
      mul_le_mul_of_nonneg_right (h1.sum_le_tsum S (fun m _ => by positivity)) (norm_nonneg _)

lemma boundaryPolynomial_continuous (S : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (boundaryPolynomial (T:=T) S a) :=
  continuous_finsetSum _ (fun m _ => continuous_const.mul (fourier m).continuous)

variable [hT : Fact (0 < T)]
theorem boundaryEnergy_tendsto_filter {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {K : ℝ} (hK : 0 ≤ K) {h : AddCircle T → ℂ} {f : ι → AddCircle T → ℂ}
    (hc : ∀ i, Continuous (f i)) (hf : ∀ i, ChordLipschitz K (f i))
    (hl : ∀ s, Tendsto (fun i => f i s) l (𝓝 (h s))) :
    Tendsto (fun i => boundaryEnergy (f i)) l (𝓝 (boundaryEnergy h)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : AddCircle T × AddCircle T => K^2)
  · exact Eventually.of_forall fun i =>
      ((measurable_boundaryDifference (hc i)).norm.pow_const 2).aestronglyMeasurable
  · exact Eventually.of_forall fun i => ae_of_all _ fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (boundaryDifference_bound hK (hf i) p) 2
  · exact integrable_const _
  · exact ae_of_all _ fun p => (((hl p.1).sub (hl p.2)).div_const _).norm.pow 2

lemma harmonicSeries_boundaryEnergy_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    Tendsto (fun S : Finset ℤ => boundaryEnergy (boundaryPolynomial (T:=T) S a)) atTop
      (𝓝 (boundaryEnergy (fun x : AddCircle T => harmonicSeries a x.toCircle))) :=
  boundaryEnergy_tendsto_filter (firstMoment_nonneg a)
    (fun S => boundaryPolynomial_continuous S a) (boundaryPolynomial_chordLipschitz h1)
    (harmonicSeries_boundary_tendsto h0)

end StrictHotSpots.Douglas
end DouglasSeriesBoundaryCombinedLayer

section DouglasSeriesEnergyCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas

def diskEnergy (f : ℂ → ℂ) : ℝ :=
  ∫ z : ℂ in ball 0 1, ‖fderiv ℝ f z 1‖^2 + ‖fderiv ℝ f z Complex.I‖^2

lemma harmonicSeries_diskEnergy_tendsto {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    Tendsto (fun S : Finset ℤ => diskEnergy (harmonicPolynomial S a)) atTop
      (𝓝 (diskEnergy (harmonicSeries a))) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℂ => 2*(firstMoment a)^2)
  · exact Eventually.of_forall fun S =>
      (((harmonicPolynomial_deriv_continuous S a 1).norm.pow 2).add
        ((harmonicPolynomial_deriv_continuous S a Complex.I).norm.pow 2)).aestronglyMeasurable
  · exact Eventually.of_forall fun S =>
      (ae_restrict_mem measurableSet_ball).mono fun z hz => by
        have ha := harmonicPolynomial_deriv_bound h1 S (mem_ball_zero_iff.mp hz).le 1
        have hb := harmonicPolynomial_deriv_bound h1 S (mem_ball_zero_iff.mp hz).le Complex.I
        rw [norm_one,mul_one] at ha
        rw [Complex.norm_I,mul_one] at hb
        rw [Real.norm_eq_abs,abs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
        have hA := pow_le_pow_left₀ (norm_nonneg _) ha 2
        have hB := pow_le_pow_left₀ (norm_nonneg _) hb 2
        linarith
  · exact integrableOn_const
  · exact (ae_restrict_mem measurableSet_ball).mono fun z hz =>
      ((harmonicPolynomial_deriv_tendsto h0 h1 hz 1).norm.pow 2).add
        ((harmonicPolynomial_deriv_tendsto h0 h1 hz Complex.I).norm.pow 2)

local instance instFactLtRealOfNatHMulPi_solutions_2 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩



theorem douglas_series {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    diskEnergy (harmonicSeries a) = (1/(2*Real.pi))*
      boundaryEnergy (fun x : AddCircle (2*Real.pi) => harmonicSeries a x.toCircle) := by
  have hb := (harmonicSeries_boundaryEnergy_tendsto (T:=2*Real.pi) h0 h1).const_mul
    (1/(2*Real.pi))
  have he : (fun S : Finset ℤ => (1/(2*Real.pi))*
      boundaryEnergy (boundaryPolynomial (T:=2*Real.pi) S a)) =
      fun S => diskEnergy (harmonicPolynomial S a) := by
    funext S
    exact (douglas_polynomial S a).symm
  rw [he] at hb
  exact tendsto_nhds_unique (harmonicSeries_diskEnergy_tendsto h0 h1) hb

end StrictHotSpots.Douglas
end DouglasSeriesEnergyCombinedLayer

section DouglasSeriesPoissonCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas

lemma poissonKernel_continuousOn_sphere {z : ℂ} (hz : z ∈ ball 0 1) :
    ContinuousOn (poissonKernel 0 z) (sphere 0 1) := by
  unfold poissonKernel
  refine ContinuousOn.div (by fun_prop) (by fun_prop) ?_
  intro w hw
  simp only [sub_zero]
  apply pow_ne_zero
  apply norm_ne_zero_iff.mpr
  apply sub_ne_zero.mpr
  intro he
  have hw' : ‖w‖ = 1 := mem_sphere_zero_iff_norm.mp hw
  have hz' : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  rw [he] at hw'
  linarith

lemma harmonicPolynomial_continuous (S : Finset ℤ) (a : ℤ → ℂ) :
    Continuous (harmonicPolynomial S a) :=
  continuous_finsetSum _ (fun m _ => continuous_const.mul (harmonicMode_continuous m))

lemma harmonicPolynomial_poisson (S : Finset ℤ) (a : ℤ → ℂ)
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • harmonicPolynomial S a) 0 1 =
      harmonicPolynomial S a z := by
  have hk := poissonKernel_continuousOn_sphere hz
  have he : poissonKernel 0 z • harmonicPolynomial S a =
      fun w => ∑ m ∈ S, a m • (poissonKernel 0 z w • harmonicMode m w) := by
    funext w
    change poissonKernel 0 z w • (∑ m ∈ S, a m * harmonicMode m w) = _
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro m _
    change poissonKernel 0 z w • (a m • harmonicMode m w) = _
    exact smul_comm (poissonKernel 0 z w) (a m) (harmonicMode m w)
  rw [he,Real.circleAverage_fun_sum]
  · change (∑ m ∈ S, Real.circleAverage (fun w => a m • (poissonKernel 0 z w • harmonicMode m w)) 0 1) = _
    simp only [Real.circleAverage_fun_smul]
    change (∑ m ∈ S, a m • Real.circleAverage (poissonKernel 0 z • harmonicMode m) 0 1) = _
    simp only [harmonicMode_poisson _ hz,smul_eq_mul,harmonicPolynomial]
  · intro m _
    exact ((hk.smul (harmonicMode_continuous m).continuousOn).circleIntegrable
      (by norm_num)).smul (a m)

lemma harmonicPolynomial_bound {a : ℤ → ℂ} (h0 : Summable (fun m => ‖a m‖))
    (S : Finset ℤ) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖harmonicPolynomial S a z‖ ≤ ∑' m : ℤ, ‖a m‖ := by
  calc
    _ ≤ ∑ m ∈ S, ‖a m*harmonicMode m z‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ‖a m‖ := by
      apply Finset.sum_le_sum
      intro m _
      rw [norm_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (harmonicMode_norm_le_one m hz) (norm_nonneg (a m))
    _ ≤ _ := h0.sum_le_tsum S (fun m _ => norm_nonneg (a m))

lemma harmonicSeries_poisson_tendsto {a : ℤ → ℂ} (h0 : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Tendsto (fun S : Finset ℤ => Real.circleAverage
      (poissonKernel 0 z • harmonicPolynomial S a) 0 1) atTop
      (𝓝 (Real.circleAverage (poissonKernel 0 z • harmonicSeries a) 0 1)) := by
  have hk := poissonKernel_continuousOn_sphere hz
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hk
  have hmap (t : ℝ) : circleMap (0:ℂ) 1 t ∈ sphere 0 1 := by
    exact circleMap_mem_sphere (0:ℂ) (by norm_num) t
  have hkc : Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
    hk.comp_continuous (continuous_circleMap 0 1) hmap
  apply Filter.Tendsto.smul tendsto_const_nhds
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => C*(∑' m : ℤ, ‖a m‖))
  · exact Eventually.of_forall fun S =>
      (hkc.smul ((harmonicPolynomial_continuous S a).comp (continuous_circleMap 0 1))).aestronglyMeasurable
  · exact Eventually.of_forall fun S => ae_of_all _ fun t _ => by
      rw [Pi.smul_apply',norm_smul]
      exact mul_le_mul (hC _ (hmap t))
        (harmonicPolynomial_bound h0 S (mem_sphere_zero_iff_norm.mp (hmap t)).le)
        (norm_nonneg _) (le_trans (norm_nonneg _) (hC _ (hmap t)))
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun t _ => ?_
    change Tendsto (fun S : Finset ℤ => poissonKernel 0 z (circleMap 0 1 t) •
      (∑ m ∈ S, a m*harmonicMode m (circleMap 0 1 t))) atTop
      (𝓝 (poissonKernel 0 z (circleMap 0 1 t) • ∑' m : ℤ, a m*harmonicMode m (circleMap 0 1 t)))
    exact tendsto_const_nhds.smul
      (harmonicSeries_summable h0 (mem_sphere_zero_iff_norm.mp (hmap t)).le).hasSum



theorem harmonicSeries_poisson {a : ℤ → ℂ} (h0 : Summable (fun m => ‖a m‖))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    Real.circleAverage (poissonKernel 0 z • harmonicSeries a) 0 1 = harmonicSeries a z := by
  have ht := harmonicSeries_poisson_tendsto h0 hz
  simp only [harmonicPolynomial_poisson _ _ hz] at ht
  exact tendsto_nhds_unique ht (harmonicSeries_summable h0 (mem_ball_zero_iff.mp hz).le).hasSum

end StrictHotSpots.Douglas
end DouglasSeriesPoissonCombinedLayer

section FourierSmoothMomentCombinedLayer
open Set MeasureTheory AddCircle
open scoped ComplexConjugate
namespace StrictHotSpots.Douglas
local instance instFactLtRealOfNatHMulPi_solutions_3 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma norm_fourierCoeff_le (f : C(AddCircle τ, ℂ)) (m : ℤ) :
    ‖fourierCoeff f m‖ ≤ ‖f‖ := by
  have h := norm_integral_le_of_norm_le_const (μ:=haarAddCircle) (C:=‖f‖)
    (f:=fun x : AddCircle τ => fourier (-m) x • f x) (ae_of_all _ fun x => by
    rw [norm_smul]
    have hf : ‖fourier (T:=τ) (-m) x‖ = 1 := by
      rw [fourier_apply,Circle.norm_coe]
    rw [hf,one_mul]
    exact ContinuousMap.norm_coe_le_norm f x)
  simpa only [fourierCoeff,probReal_univ,mul_one] using h

lemma fourierCoeffOn_coe (f : C(AddCircle τ, ℂ)) (m : ℤ) :
    fourierCoeffOn (a:=0) (b:=τ) (by positivity) (fun t : ℝ => f t) m =
      fourierCoeff f m := by
  rw [fourierCoeffOn_eq_integral,fourierCoeff_eq_intervalIntegral _ _ 0]
  simp_rw [fourier_coe_apply]
  simp only [sub_zero,zero_add]

lemma fourierCoeff_derivative (f g : C(AddCircle τ, ℂ))
    (hfg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t) (g t) t)
    {m : ℤ} (hm : m ≠ 0) :
    ((m:ℂ)*Complex.I)*fourierCoeff f m = fourierCoeff g m := by
  have h := fourierCoeffOn_of_hasDerivAt (a:=0) (b:=τ) (by positivity) hm
    (fun t _ => hfg t) ((g.continuous.comp (AddCircle.continuous_mk' τ)).intervalIntegrable _ _)
  rw [fourierCoeffOn_coe f m,fourierCoeffOn_coe g m] at h
  have he : f ((τ:ℝ):AddCircle τ) = f (0:AddCircle τ) := by rw [AddCircle.coe_period]
  simp only [he] at h
  rw [h]
  have hm' : (m:ℂ) ≠ 0 := Int.cast_ne_zero.mpr hm
  push_cast
  field_simp [hm',Real.pi_ne_zero]
  ring

lemma norm_fourierCoeff_derivative (f g : C(AddCircle τ, ℂ))
    (hfg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f t) (g t) t)
    {m : ℤ} (hm : m ≠ 0) :
    (m.natAbs:ℝ)*‖fourierCoeff f m‖ = ‖fourierCoeff g m‖ := by
  have h := congrArg norm (fourierCoeff_derivative f g hfg hm)
  have ha : (m.natAbs:ℝ) = |(m:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
  simpa only [norm_mul,Complex.norm_intCast,Complex.norm_I,mul_one,ha] using h


lemma firstMoment_fourierCoeff_bound (f0 f1 f2 f3 : C(AddCircle τ, ℂ))
    (h01 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f0 t) (f1 t) t)
    (h12 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f1 t) (f2 t) t)
    (h23 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f2 t) (f3 t) t) (m : ℤ) :
    (m.natAbs:ℝ)*‖fourierCoeff f0 m‖ ≤ ‖f3‖*(1/(m:ℝ)^2) := by
  by_cases hm : m=0
  · subst m; simp
  have h0 := norm_fourierCoeff_derivative f0 f1 h01 hm
  have h1 := norm_fourierCoeff_derivative f1 f2 h12 hm
  have h2 := norm_fourierCoeff_derivative f2 f3 h23 hm
  have hm' : (m:ℝ) ≠ 0 := Int.cast_ne_zero.mpr hm
  rw [mul_one_div]
  apply (le_div_iff₀ (sq_pos_of_ne_zero hm')).2
  calc
    _ = (m.natAbs:ℝ)*((m.natAbs:ℝ)*((m.natAbs:ℝ)*‖fourierCoeff f0 m‖)) := by
      have ha : (m.natAbs:ℝ) = |(m:ℝ)| := by rw [Nat.cast_natAbs,Int.cast_abs]
      rw [ha]
      calc
        _ = |(m:ℝ)| * ‖fourierCoeff f0 m‖ * |(m:ℝ)|^2 := by rw [sq_abs]
        _ = _ := by ring
    _ = ‖fourierCoeff f3 m‖ := by rw [h0,h1,h2]
    _ ≤ ‖f3‖ := norm_fourierCoeff_le f3 m

lemma summable_firstMoment_fourierCoeff (f0 f1 f2 f3 : C(AddCircle τ, ℂ))
    (h01 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f0 t) (f1 t) t)
    (h12 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f1 t) (f2 t) t)
    (h23 : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f2 t) (f3 t) t) :
    Summable (fun m : ℤ => (m.natAbs:ℝ)*‖fourierCoeff f0 m‖) := by
  have hp : Summable (fun m : ℤ => (1:ℝ)/(m:ℝ)^2) := Real.summable_one_div_int_pow.mpr (by norm_num)
  exact Summable.of_nonneg_of_le (fun m => by positivity)
    (firstMoment_fourierCoeff_bound f0 f1 f2 f3 h01 h12 h23) (hp.mul_left ‖f3‖)

end StrictHotSpots.Douglas
end FourierSmoothMomentCombinedLayer

section DouglasSmoothDataCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate
namespace StrictHotSpots.Douglas
local instance instFactLtRealOfNatHMulPi_solutions_4 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma summable_norm_of_firstMoment {a : ℤ → ℂ}
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) : Summable (fun m => ‖a m‖) := by
  apply h1.of_norm_bounded_eventually
  filter_upwards [eventually_cofinite_ne (0:ℤ)] with m hm
  rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hm' : 1 ≤ (m.natAbs:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr hm)
  exact le_mul_of_one_le_left (norm_nonneg _) hm'

lemma harmonicSeries_fourier_boundary (f : C(AddCircle τ, ℂ))
    (h : Summable (fun m => ‖fourierCoeff f m‖)) (s : AddCircle τ) :
    harmonicSeries (fourierCoeff f) s.toCircle = f s := by
  have hf := has_pointwise_sum_fourier_series_of_summable h.of_norm s
  simpa only [harmonicSeries,harmonicMode_boundary,smul_eq_mul] using hf.tsum_eq

lemma circleMap_eq_toCircle (t : ℝ) :
    circleMap (0:ℂ) 1 t = (AddCircle.toCircle (t:AddCircle τ) : ℂ) := by
  rw [toCircle_apply_mk,Circle.coe_exp]
  simp only [circleMap,Complex.ofReal_one,one_mul,zero_add]
  congr 1
  push_cast
  field_simp


def poissonExtension (f : AddCircle τ → ℂ) (z : ℂ) : ℂ :=
  τ⁻¹ • ∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • f t

lemma poissonExtension_eq_harmonicSeries (f : C(AddCircle τ, ℂ))
    (h : Summable (fun m => ‖fourierCoeff f m‖)) {z : ℂ} (hz : z ∈ ball 0 1) :
    poissonExtension f z = harmonicSeries (fourierCoeff f) z := by
  rw [← harmonicSeries_poisson h hz]
  unfold poissonExtension Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [Pi.smul_apply',circleMap_eq_toCircle,harmonicSeries_fourier_boundary f h]



end StrictHotSpots.Douglas
end DouglasSmoothDataCombinedLayer

section DouglasClosureCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas

lemma harmonicMode_contDiff (m : ℤ) : ContDiff ℝ ∞ (harmonicMode m) := by
  cases m with
  | ofNat n => exact contDiff_id.pow n
  | negSucc n => exact Complex.conjCLE.contDiff.comp (contDiff_id.pow (n+1))

lemma harmonicSeries_continuousOn {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    ContinuousOn (harmonicSeries a) (closedBall 0 1) := by
  apply continuousOn_tsum (fun m =>
    (continuous_const.mul (harmonicMode_continuous m)).continuousOn) ha
  intro m z hz
  dsimp only [Pi.mul_apply]
  rw [norm_mul]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (harmonicMode_norm_le_one m (mem_closedBall_zero_iff.mp hz)) (norm_nonneg (a m))

def harmonicD (a : ℤ → ℂ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  ∑' m : ℤ, a m • fderiv ℝ (harmonicMode m) z

lemma harmonicD_continuousOn {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    ContinuousOn (harmonicD a) (closedBall 0 1) := by
  unfold harmonicD
  apply continuousOn_tsum (f := fun m z => a m • fderiv ℝ (harmonicMode m) z)
    (fun m => (Continuous.const_smul ((harmonicMode_contDiff m).continuous_fderiv (by simp))
      (a m)).continuousOn) ha
  intro m z hz
  rw [norm_smul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    (harmonicMode_deriv_bound m (mem_closedBall_zero_iff.mp hz)) (norm_nonneg (a m))

end StrictHotSpots.Douglas
end DouglasClosureCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section C1WeakGradientWeightedCombinedLayer
open Set MeasureTheory
open scoped ContDiff InnerProductSpace
namespace StrictHotSpots
lemma integral_mul_test_hasFDerivAt {Ω : Set Plane} {f φ : Plane → ℝ}
    {D : Plane → Plane →L[ℝ] ℝ} (ho : IsOpen Ω)
    (hcF : ContinuousOn f Ω) (hcD : ContinuousOn D Ω)
    (hd : ∀ x ∈ Ω, HasFDerivAt f (D x) x)
    (hφ : ContDiff ℝ ∞ φ) (hk : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω)
    (e : Plane) :
    (∫ x in Ω, f x * (fderiv ℝ φ x) e) = -(∫ x in Ω, D x e * φ x) := by
  have hdφ : Continuous (fun x => (fderiv ℝ φ x) e) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcDf : ContinuousOn (fun x => fderiv ℝ f x e) Ω := by
    apply (hcD.clm_apply continuousOn_const).congr
    intro x hx
    exact congrArg (fun A : Plane →L[ℝ] ℝ => A e) (hd x hx).fderiv
  have hds : tsupport (fun x => (fderiv ℝ φ x) e) ⊆ Ω :=
    (tsupport_fderiv_apply_subset ℝ e).trans hs
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_mul_test ho hcDf hφ.continuous hk hs)
    (integrable_mul_test ho hcF hdφ (hk.fderiv_apply ℝ e) hds)
    (integrable_mul_test ho hcF hφ.continuous hk hs)
    (fun x hx => (hd x (hs hx)).differentiableAt)
    (fun x _ => hφ.differentiable (by simp) x)
  rw [setIntegral_mul_test hds]
  rw [hi,← setIntegral_mul_test hs]
  congr 1
  apply setIntegral_congr_fun ho.measurableSet
  intro x hx
  change fderiv ℝ f x e * φ x = D x e * φ x
  rw [(hd x hx).fderiv]

lemma HasH1Gradient.of_hasFDerivAt {Ω : Set Plane} {f : Plane → ℝ} {g : Plane → Plane}
    (ho : IsOpen Ω) (hf : ContinuousOn f Ω) (hg : ContinuousOn g Ω)
    (hd : ∀ x ∈ Ω, HasFDerivAt f (InnerProductSpace.toDual ℝ Plane (g x)) x)
    (hmf : MemLp f 2 (volume.restrict Ω)) (hmg : MemLp g 2 (volume.restrict Ω)) :
    HasH1Gradient Ω f g := by
  refine ⟨hmf,hmg,fun φ hφ hk hs e => ?_⟩
  exact integral_mul_test_hasFDerivAt ho hf
    ((InnerProductSpace.toDual ℝ Plane).continuous.comp_continuousOn hg) hd hφ hk hs e
end StrictHotSpots
end C1WeakGradientWeightedCombinedLayer

section DouglasH1CombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10

def planeSeries (a : ℤ → ℂ) (x : Plane) : ℝ :=
  (harmonicSeries a (complexIso.symm x)).re

def planeD (a : ℤ → ℂ) (x : Plane) : Plane →L[ℝ] ℝ :=
  (Complex.reCLM.comp (harmonicD a (complexIso.symm x))).comp
    complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap

def planeGrad (a : ℤ → ℂ) (x : Plane) : Plane :=
  (InnerProductSpace.toDual ℝ Plane).symm (planeD a x)

lemma planeSeries_continuousOn {a : ℤ → ℂ} (ha : Summable (fun m => ‖a m‖)) :
    ContinuousOn (planeSeries a) (closedBall 0 1) := by
  apply Complex.continuous_re.comp_continuousOn
  apply (harmonicSeries_continuousOn ha).comp complexIso.symm.continuous.continuousOn
  intro x hx
  simpa only [mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx

lemma planeD_continuousOn {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    ContinuousOn (planeD a) (closedBall 0 1) := by
  have hc : ContinuousOn (fun x : Plane => harmonicD a (complexIso.symm x)) (closedBall 0 1) := by
    apply (harmonicD_continuousOn ha).comp complexIso.symm.continuous.continuousOn
    intro x hx
    simpa only [mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact (continuousOn_const.clm_comp hc).clm_comp continuousOn_const

lemma planeGrad_continuousOn {a : ℤ → ℂ}
    (ha : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    ContinuousOn (planeGrad a) (closedBall 0 1) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn (planeD_continuousOn ha)

lemma planeSeries_hasFDerivAt {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) {x : Plane} (hx : x ∈ disk) :
    HasFDerivAt (planeSeries a) (planeD a x) x := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact (Complex.reCLM.hasFDerivAt.comp _ (harmonicSeries_hasFDerivAt h0 h1 hz)).comp x
    complexIso.symm.toContinuousLinearEquiv.hasFDerivAt

lemma disk_memLp_of_continuousOn {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (hf : ContinuousOn f (closedBall 0 1)) : MemLp f 2 (volume.restrict disk) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Plane) 1)) :=
    isFiniteMeasure_restrict.mpr (isBounded_ball (x := (0:Plane)) (r := 1)).measure_lt_top.ne
  obtain ⟨C,hC⟩ := (isCompact_closedBall (0:Plane) 1).exists_bound_of_continuousOn hf
  apply MemLp.of_bound ((hf.mono ball_subset_closedBall).aestronglyMeasurable measurableSet_ball) C
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact hC x (ball_subset_closedBall hx)



theorem planeSeries_hasH1Gradient {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    HasH1Gradient disk (planeSeries a) (planeGrad a) := by
  apply HasH1Gradient.of_hasFDerivAt isOpen_ball
    ((planeSeries_continuousOn h0).mono ball_subset_closedBall)
    ((planeGrad_continuousOn h1).mono ball_subset_closedBall)
  · intro x hx
    simpa only [planeGrad,LinearIsometryEquiv.apply_symm_apply] using planeSeries_hasFDerivAt h0 h1 hx
  · exact disk_memLp_of_continuousOn (planeSeries_continuousOn h0)
  · exact disk_memLp_of_continuousOn (planeGrad_continuousOn h1)

lemma planeSeries_gradient {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    HasH1Gradient disk (planeSeries a) (gradient (planeSeries a)) := by
  have h := planeSeries_hasH1Gradient h0 h1
  have he : planeGrad a =ᵐ[volume.restrict disk] gradient (planeSeries a) := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    unfold planeGrad gradient
    rw [(planeSeries_hasFDerivAt h0 h1 hx).fderiv]
  exact ⟨h.1,h.2.1.ae_eq he,fun φ hφ hc hs e => by
    rw [h.2.2 φ hφ hc hs e]
    congr 1
    apply integral_congr_ae
    filter_upwards [he] with x hx
    rw [hx]⟩

end StrictHotSpots.Douglas
end DouglasH1CombinedLayer

section DouglasInteriorCombinedLayer
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10

lemma poissonAverage_contDiffOn {f : ℂ → ℝ} (hf : CircleIntegrable f 0 1) :
    ContDiffOn ℝ ∞ (fun z => Real.circleAverage (poissonKernel 0 z • f) 0 1) (ball 0 1) := by
  have hfc : CircleIntegrable (fun z => (f z : ℂ)) 0 1 := by
    simp only [CircleIntegrable,intervalIntegrable_iff] at hf ⊢
    exact Complex.ofRealCLM.integrable_comp hf
  have hball : ball (0 : ℂ) 1 ⊆ (sphere (0 : ℂ) |(1 : ℝ)|)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, abs_one, Metric.mem_sphere]
    exact ne_of_lt (Metric.mem_ball.mp hz)
  have ha := analyticOnNhd_circleAverage_herglotzRieszKernel_smul hfc
  have hc : ContDiffOn ℝ ∞ (fun z =>
      (Real.circleAverage (fun ζ => herglotzRieszKernel 0 z ζ • (f ζ : ℂ)) 0 1).re)
        (ball 0 1) :=
    Complex.reCLM.contDiff.comp_contDiffOn (ha.contDiffOn_of_completeSpace.restrict_scalars ℝ)
  apply hc.congr
  intro z hz
  rw [re_circleAverage_herglotzRieszKernel_smul hf hz]
  congr 1
  funext ζ
  simp only [poissonKernel_eq_re_herglotzRieszKernel]

end StrictHotSpots.Douglas
end DouglasInteriorCombinedLayer

section H1RayleighFormCombinedLayer
open Set MeasureTheory Filter
open scoped InnerProductSpace Topology
namespace StrictHotSpots.H1
variable {Ω : Set Plane}

variable (hb : Bornology.IsBounded Ω)
def mean : H1 Ω →L[ℝ] ℝ := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  exact (innerSL ℝ ((memLp_const (1 : ℝ)).toLp (fun _ : Plane => (1 : ℝ)))).comp value

end StrictHotSpots.H1
end H1RayleighFormCombinedLayer

section CompactRowsCombinedLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.CompactRows
variable {α H : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def rowOperator : Lp H 2 μ →L[ℝ] H →L[ℝ] Lp ℝ 2 μ :=
  (ContinuousLinearMap.compLpL₂ 2 μ (innerSL ℝ)).flip

end StrictHotSpots.CompactRows
end CompactRowsCombinedLayer

section MeasurableRowsCombinedLayer

open MeasureTheory Set Filter
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.CompactRows

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {ν : Measure Y} [SFinite ν] [IsSeparable ν]

local instance instMeasurableSpaceSubtypeAEEqFunRealMemAddSubgroupLpOfNatENNReal_solutions : MeasurableSpace (Lp ℝ 2 ν) := borel _

end StrictHotSpots.CompactRows
end MeasurableRowsCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section
section NodalSmoothingCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff
namespace StrictHotSpots.Nodal

lemma transition_deriv_zero {t : ℝ} (h : t ≤ 0 ∨ 1 ≤ t) :
    deriv Real.smoothTransition t = 0 := by
  rcases h with h | h
  · apply IsLocalMin.deriv_eq_zero
    exact Eventually.of_forall fun y => by
      rw [Real.smoothTransition.zero_of_nonpos h]
      exact Real.smoothTransition.nonneg y
  · apply IsLocalMax.deriv_eq_zero
    exact Eventually.of_forall fun y => by
      rw [Real.smoothTransition.one_of_one_le h]
      exact Real.smoothTransition.le_one y

def cutoff (n : ℕ) (t : ℝ) : ℝ := t * Real.smoothTransition (((n:ℝ)+1)*t-1)

lemma cutoff_contDiff (n : ℕ) : ContDiff ℝ ∞ (cutoff n) := by
  unfold cutoff
  exact contDiff_id.mul (Real.smoothTransition.contDiff.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))

lemma cutoff_deriv (n : ℕ) (t : ℝ) : deriv (cutoff n) t =
    Real.smoothTransition (((n:ℝ)+1)*t-1) +
      (((n:ℝ)+1)*t) * deriv Real.smoothTransition (((n:ℝ)+1)*t-1) := by
  have hh := (hasDerivAt_id t).mul
    ((((Real.smoothTransition.contDiff : ContDiff ℝ ∞ _).differentiable (by simp)).differentiableAt.hasDerivAt).comp t
      (((hasDerivAt_id t).const_mul ((n:ℝ)+1)).sub_const 1))
  have he : (id * Real.smoothTransition ∘ (fun x : ℝ => ((n:ℝ)+1)*id x-1)) = cutoff n := rfl
  rw [he] at hh
  rw [hh.deriv]
  simp only [Function.comp_apply,id_eq,one_mul,mul_one]
  ring

lemma cutoff_zero (n : ℕ) {t : ℝ} (ht : t < 1/((n:ℝ)+1)) : cutoff n t = 0 := by
  unfold cutoff
  rw [Real.smoothTransition.zero_of_nonpos, mul_zero]
  have hn : 0 < (n:ℝ)+1 := by positivity
  have := (lt_div_iff₀ hn).mp ht
  nlinarith

lemma cutoff_deriv_bound : ∃ C : ℝ, 1 ≤ C ∧ ∀ n t, ‖deriv (cutoff n) t‖ ≤ C := by
  obtain ⟨M,hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((Real.smoothTransition.contDiff.continuous_deriv (by simp : (1:ℕ∞ω) ≤ ∞)).continuousOn :
      ContinuousOn (deriv Real.smoothTransition) (Icc (0:ℝ) 1))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0 (by simp))
  refine ⟨1+2*M,by linarith,fun n t => ?_⟩
  rw [cutoff_deriv]
  have hτ : ‖Real.smoothTransition (((n:ℝ)+1)*t-1)‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  by_cases h : ((n:ℝ)+1)*t-1 ∈ Icc (0:ℝ) 1
  · have hnt : ‖((n:ℝ)+1)*t‖ ≤ 2 := by
      rw [Real.norm_eq_abs,abs_le]
      constructor <;> linarith [h.1,h.2]
    calc
      _ ≤ ‖Real.smoothTransition (((n:ℝ)+1)*t-1)‖ +
          ‖((n:ℝ)+1)*t * deriv Real.smoothTransition (((n:ℝ)+1)*t-1)‖ := norm_add_le _ _
      _ ≤ 1 + 2*M := by rw [norm_mul]; gcongr; exact hM _ h
  · have hd : deriv Real.smoothTransition (((n:ℝ)+1)*t-1) = 0 := by
      apply transition_deriv_zero
      simp only [mem_Icc,not_and_or,not_le] at h
      exact h.imp le_of_lt le_of_lt
    rw [hd,mul_zero,add_zero]
    linarith

lemma cutoff_eventually_eq {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, cutoff n t = t ∧ deriv (cutoff n) t = 1 := by
  have hn : Tendsto (fun n : ℕ => ((n:ℝ)+1)*t-1) atTop atTop :=
    by
      simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-1 : ℝ)
        ((tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop).atTop_mul_const ht)
  filter_upwards [hn.eventually_ge_atTop 1] with n hn
  constructor
  · simp [cutoff,Real.smoothTransition.one_of_one_le hn]
  · rw [cutoff_deriv,Real.smoothTransition.one_of_one_le hn,
      transition_deriv_zero (Or.inr hn),mul_zero,add_zero]

end StrictHotSpots.Nodal
end NodalSmoothingCombinedLayer

section BoundarySignTestsCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
def cut (Ω : Set Plane) (u : Plane → ℝ) (n : ℕ) : Plane → ℝ :=
  Ω.indicator (fun x => Nodal.cutoff n (u x))
def cutSupport (Ω : Set Plane) (u : Plane → ℝ) (n : ℕ) : Set Plane :=
  closure Ω ∩ u ⁻¹' Ici (1 / ((n:ℝ)+1))
lemma support_cut_subset (n : ℕ) : Function.support (cut Ω u n) ⊆ cutSupport Ω u n := by
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · refine ⟨subset_closure hxΩ, ?_⟩
    by_contra h
    apply hx
    exact (indicator_of_mem hxΩ _).trans (Nodal.cutoff_zero n (lt_of_not_ge h))
  · exact False.elim (hx (indicator_of_notMem hxΩ _))
lemma cutSupport_closed (hu : ContinuousOn u (closure Ω)) (n : ℕ) :
    IsClosed (cutSupport Ω u n) :=
  hu.preimage_isClosed_of_isClosed isClosed_closure isClosed_Ici
lemma cutSupport_subset (ho : IsOpen Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    cutSupport Ω u n ⊆ Ω := by
  intro x hx
  by_contra hn
  have hf : x ∈ frontier Ω := by
    rw [frontier,ho.interior_eq]
    exact ⟨hx.1,hn⟩
  have hp : 0 < 1 / ((n:ℝ)+1) := by positivity
  exact (not_le_of_gt hp) (hx.2.trans (hb x hf))
lemma cut_eq_zero_nhds (hu : ContinuousOn u (closure Ω)) (n : ℕ) {x : Plane}
    (hx : x ∉ cutSupport Ω u n) : cut Ω u n =ᶠ[𝓝 x] 0 := by
  filter_upwards [(cutSupport_closed hu n).isOpen_compl.mem_nhds hx] with y hy
  by_contra h
  exact hy (support_cut_subset n h)
lemma cut_eq_nhds (ho : IsOpen Ω) (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
    cut Ω u n =ᶠ[𝓝 x] (fun y => Nodal.cutoff n (u y)) := by
  filter_upwards [ho.mem_nhds hx] with y hy
  exact indicator_of_mem hy _
lemma cut_tsupport_subset (ho : IsOpen Ω) (hu : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) : tsupport (cut Ω u n) ⊆ Ω :=
  ((cutSupport_closed hu n).closure_subset_iff.mpr (support_cut_subset n)).trans
    (cutSupport_subset ho hb n)
lemma cut_hasCompactSupport (hu : ContinuousOn u (closure Ω))
    (hb : Bornology.IsBounded Ω) (n : ℕ) : HasCompactSupport (cut Ω u n) := by
  apply hb.isCompact_closure.of_isClosed_subset isClosed_closure
  exact ((cutSupport_closed hu n).closure_subset_iff.mpr (support_cut_subset n)).trans
    inter_subset_left

end StrictHotSpots.BoundarySign
end BoundarySignTestsCombinedLayer

section NodalRestrictionWeightedCombinedLayer

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots.Nodal

variable {Ω U : Set Plane} {u : Plane → ℝ}

lemma cutoff_indicator_zero_nhds (hΩ : IsOpen Ω) (hu : ContinuousOn u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0)
    (n : ℕ) {x : Plane} (hx : x ∈ Ω) (hxU : x ∉ U) :
    U.indicator (fun y => cutoff n (u y)) =ᶠ[𝓝 x] 0 := by
  by_cases hxc : x ∈ closure U
  · have hux : u x = 0 := hf x ⟨⟨hxc,by simpa [hU.interior_eq] using hxU⟩,hx⟩
    have hε : u x < 1/((n:ℝ)+1) := by rw [hux]; positivity
    filter_upwards [((hu x hx).continuousAt (hΩ.mem_nhds hx)).eventually (gt_mem_nhds hε)] with y hy
    by_cases hyU : y ∈ U
    · simp only [Pi.zero_apply,indicator_of_mem hyU,cutoff_zero n hy]
    · simp only [Pi.zero_apply,indicator_of_notMem hyU]
  · filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxc] with y hy
    exact indicator_of_notMem (fun hyU => hy (subset_closure hyU)) _

lemma cutoff_indicator_contDiffOn (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ) :
    ContDiffOn ℝ ∞ (U.indicator (fun x => cutoff n (u x))) Ω := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hxU : x ∈ U
  · apply ((cutoff_contDiff n).contDiffAt.comp x (hu.contDiffAt (hΩ.mem_nhds hx))).congr_of_eventuallyEq
    filter_upwards [hU.mem_nhds hxU] with y hy
    exact indicator_of_mem hy _
  · exact contDiffAt_const.congr_of_eventuallyEq (cutoff_indicator_zero_nhds hΩ hu.continuousOn hU hf n hx hxU)

lemma cutoff_indicator_fderiv (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ)
    {x : Plane} (hx : x ∈ Ω) :
    fderiv ℝ (U.indicator (fun y => cutoff n (u y))) x =
      U.indicator (fun y => (deriv (cutoff n) (u y)) • fderiv ℝ u y) x := by
  by_cases hxU : x ∈ U
  · rw [indicator_of_mem hxU]
    have he : U.indicator (fun y => cutoff n (u y)) =ᶠ[𝓝 x] (fun y => cutoff n (u y)) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact indicator_of_mem hy _
    rw [he.fderiv_eq]
    exact (((cutoff_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
      ((hu.contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv
  · rw [indicator_of_notMem hxU,(cutoff_indicator_zero_nhds hΩ hu.continuousOn hU hf n hx hxU).fderiv_eq]
    exact (hasFDerivAt_const (𝕜 := ℝ) (0 : ℝ) x).fderiv

lemma cutoff_indicator_gradient (hΩ : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hU : IsOpen U) (hf : ∀ x ∈ frontier U ∩ Ω, u x = 0) (n : ℕ)
    {x : Plane} (hx : x ∈ Ω) :
    gradient (U.indicator (fun y => cutoff n (u y))) x =
      U.indicator (fun y => (deriv (cutoff n) (u y)) • gradient u y) x := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  simp only [gradient]
  rw [cutoff_indicator_fderiv hΩ hu hU hf n hx]
  by_cases hxU : x ∈ U
  · simp only [indicator_of_mem hxU,map_smul]
  · simp only [indicator_of_notMem hxU,map_zero]

lemma cutoff_grad_memLp (hU : IsOpen U) (hu : HasH1Gradient Ω u (gradient u)) (n : ℕ) :
    MemLp (U.indicator (fun x => deriv (cutoff n) (u x) • gradient u x)) 2 (volume.restrict Ω) := by
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  apply (hu.2.1.norm.const_mul C).mono'
    ((((cutoff_contDiff n).continuous_deriv (by simp)).comp_aestronglyMeasurable
      hu.1.aestronglyMeasurable).smul hu.2.1.aestronglyMeasurable |>.indicator hU.measurableSet)
  exact Eventually.of_forall fun x => by
    by_cases hx : x ∈ U
    · rw [indicator_of_mem hx]
      change ‖deriv (cutoff n) (u x) • gradient u x‖ ≤ C * ‖gradient u x‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (hbd n (u x)) (norm_nonneg (gradient u x))
    · rw [indicator_of_notMem hx,norm_zero]
      exact mul_nonneg (le_trans zero_le_one hC) (norm_nonneg _)

end StrictHotSpots.Nodal
end NodalRestrictionWeightedCombinedLayer

section ContinuousZeroTraceCombinedLayer
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff InnerProductSpace
namespace StrictHotSpots
namespace BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
lemma cut_contDiff_interior (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω) (hc : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) : ContDiff ℝ ∞ (cut Ω u n) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ Ω
  · exact ((Nodal.cutoff_contDiff n).contDiffAt.comp x
      (hu.contDiffAt (ho.mem_nhds hx))).congr_of_eventuallyEq
      (cut_eq_nhds ho n hx)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (cut_eq_zero_nhds hc n (fun h => hx (cutSupport_subset ho hb n h)))
def test_interior (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (hc : ContinuousOn u (closure Ω)) (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    smoothTestSpace Ω :=
  ⟨cut Ω u n, cut_contDiff_interior ho hu hc hb n, cut_hasCompactSupport hc hbound n,
    cut_tsupport_subset ho hc hb n⟩
lemma cut_gradient_interior (ho : IsOpen Ω) (hu : ContDiffOn ℝ ∞ u Ω)
    (n : ℕ) {x : Plane} (hx : x ∈ Ω) :
    gradient (cut Ω u n) x = deriv (Nodal.cutoff n) (u x) • gradient u x := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  simp only [gradient,map_smul]
  rw [(cut_eq_nhds ho n hx).fderiv_eq]
  simp only [LinearIsometryEquiv.apply_symm_apply]
  exact (((Nodal.cutoff_contDiff n).differentiable (by simp)).differentiableAt.hasDerivAt.comp_hasFDerivAt x
    ((hu.contDiffAt (ho.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt).fderiv

end BoundarySign
end StrictHotSpots
end ContinuousZeroTraceCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Poisson
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section CircleMollifierCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function ContinuousLinearMap
open scoped Topology ComplexConjugate ContDiff Convolution
namespace StrictHotSpots.Douglas
local notation "τ" => (2*Real.pi)

lemma chord_translate (s t u : AddCircle τ) :
    ‖((s-u).toCircle:ℂ)-((t-u).toCircle:ℂ)‖ = ‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ := by
  rw [show s-u=s+(-u) from sub_eq_add_neg s u,show t-u=t+(-u) from sub_eq_add_neg t u]
  simp only [AddCircle.toCircle_add,Circle.coe_mul,← sub_mul,norm_mul,Circle.norm_coe,mul_one]


def angleSmooth (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) : ℝ → ℂ :=
  φ.normed volume ⋆[lsmul ℝ ℝ,volume] (fun t : ℝ => f t)

lemma angleSmooth_smooth (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    ContDiff ℝ ∞ (angleSmooth φ f) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
    (f.continuous.comp (AddCircle.continuous_mk' τ)).locallyIntegrable

lemma angleSmooth_periodic (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    Periodic (angleSmooth φ f) τ := by
  intro t
  unfold angleSmooth
  simp only [convolution_def,lsmul_apply]
  apply integral_congr_ae (ae_of_all _ fun u => ?_)
  congr 2
  rw [show t+τ-u = (t-u)+τ by ring,AddCircle.coe_add,AddCircle.coe_period,add_zero]

lemma angleSmooth_integrable (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    Integrable (fun u : ℝ => φ.normed volume u • f ((t-u:ℝ):AddCircle τ)) := by
  exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
    (lsmul ℝ ℝ) φ.integrable_normed.locallyIntegrable
    (f.continuous.comp (AddCircle.continuous_mk' τ)) t

lemma angleSmooth_chordLipschitz (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (h : ChordLipschitz K f) (s t : ℝ) :
    ‖angleSmooth φ f s-angleSmooth φ f t‖ ≤
      K*‖(AddCircle.toCircle (s:AddCircle τ):ℂ)-(AddCircle.toCircle (t:AddCircle τ):ℂ)‖ := by
  have hi := (angleSmooth_integrable φ f s).sub (angleSmooth_integrable φ f t)
  have hp (u : ℝ) : ‖φ.normed volume u • f ((s-u:ℝ):AddCircle τ) -
      φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ ≤
      φ.normed volume u * (K*‖(AddCircle.toCircle (s:AddCircle τ):ℂ)-(AddCircle.toCircle (t:AddCircle τ):ℂ)‖) := by
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed u)]
    apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed u)
    have hh := h ((s-u:ℝ):AddCircle τ) ((t-u:ℝ):AddCircle τ)
    simpa only [AddCircle.coe_sub,chord_translate] using hh
  change ‖(∫ u : ℝ, φ.normed volume u • f ((s-u:ℝ):AddCircle τ))-
    (∫ u : ℝ, φ.normed volume u • f ((t-u:ℝ):AddCircle τ))‖ ≤ _
  rw [← integral_sub (angleSmooth_integrable φ f s) (angleSmooth_integrable φ f t)]
  calc
    _ ≤ ∫ u : ℝ, ‖φ.normed volume u • f ((s-u:ℝ):AddCircle τ) -
        φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, φ.normed volume u *
        (K*‖(AddCircle.toCircle (s:AddCircle τ):ℂ)-(AddCircle.toCircle (t:AddCircle τ):ℂ)‖) :=
      integral_mono hi.norm (φ.integrable_normed.mul_const _) hp
    _ = _ := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma periodic_lift_continuous {g : ℝ → ℂ} (hg : Periodic g τ) (hc : Continuous g) :
    Continuous hg.lift := by
  apply (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples τ)).continuous_iff.2
  exact hc


def circleSmooth (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) : C(AddCircle τ,ℂ) :=
  ⟨(angleSmooth_periodic φ f).lift,
    periodic_lift_continuous _ (angleSmooth_smooth φ f).continuous⟩

lemma circleSmooth_chordLipschitz (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (h : ChordLipschitz K f) : ChordLipschitz K (circleSmooth φ f) := by
  intro s t
  induction s using QuotientAddGroup.induction_on with | H s =>
    induction t using QuotientAddGroup.induction_on with | H t =>
      exact angleSmooth_chordLipschitz φ f h s t

lemma circleSmooth_tendsto {ι : Type*} {l : Filter ι} {φ : ι → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    Tendsto (fun i => circleSmooth (φ i) f s) l (𝓝 (f s)) := by
  induction s using QuotientAddGroup.induction_on with | H t =>
    exact ContDiffBump.convolution_tendsto_right_of_continuous hφ
      (f.continuous.comp (AddCircle.continuous_mk' τ)) t

end StrictHotSpots.Douglas
end CircleMollifierCombinedLayer

section CircleSmoothFourierCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas
local instance instFactLtRealOfNatHMulPi_solutions_8 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma periodic_deriv {g : ℝ → ℂ} (hg : Periodic g τ) : Periodic (deriv g) τ := by
  intro t
  rw [← deriv_comp_add_const]
  exact congrArg (fun h : ℝ → ℂ => deriv h t) (funext hg)

lemma angleLift_periodic (f : C(AddCircle τ,ℂ)) : Periodic (fun t : ℝ => f t) τ := by
  intro t
  dsimp only
  rw [AddCircle.coe_add,AddCircle.coe_period,add_zero]



theorem summable_firstMoment_of_smooth_lift (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    Summable (fun m : ℤ => (m.natAbs:ℝ)*‖fourierCoeff f m‖) := by
  let g : ℝ → ℂ := fun t => f t
  have hp : Periodic g τ := angleLift_periodic f
  have h1 : ContDiff ℝ ∞ (deriv g) := (contDiff_infty_iff_deriv.mp hf).2
  have h2 : ContDiff ℝ ∞ (deriv (deriv g)) := (contDiff_infty_iff_deriv.mp h1).2
  have h3 : ContDiff ℝ ∞ (deriv (deriv (deriv g))) := (contDiff_infty_iff_deriv.mp h2).2
  let f1 : C(AddCircle τ,ℂ) := ⟨(periodic_deriv hp).lift,
    periodic_lift_continuous _ h1.continuous⟩
  let f2 : C(AddCircle τ,ℂ) := ⟨(periodic_deriv (periodic_deriv hp)).lift,
    periodic_lift_continuous _ h2.continuous⟩
  let f3 : C(AddCircle τ,ℂ) := ⟨(periodic_deriv (periodic_deriv (periodic_deriv hp))).lift,
    periodic_lift_continuous _ h3.continuous⟩
  apply summable_firstMoment_fourierCoeff f f1 f2 f3
  · intro t
    exact (hf.differentiable (by simp) t).hasDerivAt
  · intro t
    exact (h1.differentiable (by simp) t).hasDerivAt
  · intro t
    exact (h2.differentiable (by simp) t).hasDerivAt


theorem douglas_smooth_lift (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    diskEnergy (poissonExtension f) = (1/τ)*boundaryEnergy f := by
  have h1 := summable_firstMoment_of_smooth_lift f hf
  have h0 := summable_norm_of_firstMoment h1
  have he : EqOn (poissonExtension f) (harmonicSeries (fourierCoeff f)) (ball 0 1) :=
    fun z hz => poissonExtension_eq_harmonicSeries f h0 hz
  have hE : diskEnergy (poissonExtension f) = diskEnergy (harmonicSeries (fourierCoeff f)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have hd := (he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).fderiv_eq (𝕜:=ℝ)
    dsimp only
    rw [hd]
  rw [hE,douglas_series h0 h1]
  have hb : (fun s : AddCircle τ => harmonicSeries (fourierCoeff f) s.toCircle) = f :=
    funext (harmonicSeries_fourier_boundary f h0)
  rw [hb]




end StrictHotSpots.Douglas
end CircleSmoothFourierCombinedLayer

section CircleApproximationCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas
local instance instFactLtRealOfNatHMulPi_solutions_9 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma chordLipschitz_sub {T : ℝ} {f g : AddCircle T → ℂ} {K L : ℝ}
    (hf : ChordLipschitz K f) (hg : ChordLipschitz L g) :
    ChordLipschitz (K+L) (fun s => f s-g s) := by
  intro s t
  rw [show (f s-g s)-(f t-g t) = (f s-f t)-(g s-g t) by ring]
  exact (norm_sub_le _ _).trans ((add_le_add (hf s t) (hg s t)).trans_eq (add_mul _ _ _).symm)

@[simp] lemma boundaryEnergy_zero {T : ℝ} [Fact (0 < T)] : boundaryEnergy (fun _ : AddCircle T => (0:ℂ)) = 0 := by
  simp [boundaryEnergy,boundaryDifference]




theorem circleSmooth_poisson_cauchy {ι : Type*} {l : Filter ι}
    [l.IsCountablyGenerated] {φ : ι → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0)) (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun p : ι × ι => diskEnergy (poissonExtension
      (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f))) (l ×ˢ l) (𝓝 0) := by
  have hh := boundaryEnergy_tendsto_filter (add_nonneg hK hK)
    (l:=l ×ˢ l)
    (fun p : ι × ι => (circleSmooth (φ p.1) f).continuous.sub (circleSmooth (φ p.2) f).continuous)
    (fun p : ι × ι => chordLipschitz_sub (circleSmooth_chordLipschitz (φ p.1) f h)
      (circleSmooth_chordLipschitz (φ p.2) f h))
    (fun s => ((circleSmooth_tendsto hφ f s).comp tendsto_fst).sub
      ((circleSmooth_tendsto hφ f s).comp tendsto_snd))
  have hz : Tendsto (fun p : ι × ι => (1/τ)*boundaryEnergy
      (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f)) (l ×ˢ l) (𝓝 0) := by
    simpa only [Pi.sub_apply, ContinuousMap.coe_sub, sub_self,boundaryEnergy_zero,mul_zero] using hh.const_mul (1/τ)
  apply hz.congr'
  exact Eventually.of_forall fun p => (douglas_smooth_lift
    (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f)
    ((angleSmooth_smooth (φ p.1) f).sub (angleSmooth_smooth (φ p.2) f))).symm

end StrictHotSpots.Douglas
end CircleApproximationCombinedLayer

section CirclePoissonConvergenceCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff
namespace StrictHotSpots.Douglas
local instance instFactLtRealOfNatHMulPi_solutions_10 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma angleSmooth_norm_le (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    ‖angleSmooth φ f t‖ ≤ ‖f‖ := by
  change ‖∫ u : ℝ, φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ ≤ ‖f‖
  calc
    _ ≤ ∫ u : ℝ, ‖φ.normed volume u • f ((t-u:ℝ):AddCircle τ)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, φ.normed volume u * ‖f‖ := by
      apply integral_mono (angleSmooth_integrable φ f t).norm (φ.integrable_normed.mul_const _)
      intro u
      dsimp only
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (φ.nonneg_normed u)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (φ.nonneg_normed u)
    _ = ‖f‖ := by rw [integral_mul_const,φ.integral_normed,one_mul]

lemma circleSmooth_norm_le (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    ‖circleSmooth φ f s‖ ≤ ‖f‖ := by
  induction s using QuotientAddGroup.induction_on with | H s => exact angleSmooth_norm_le φ f s



theorem circleSmooth_poisson_tendsto {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    Tendsto (fun i => poissonExtension (circleSmooth (φ i) f) z) l
      (𝓝 (poissonExtension f z)) := by
  have hk := poissonKernel_continuousOn_sphere hz
  obtain ⟨C,hC⟩ := (isCompact_sphere (0:ℂ) 1).exists_bound_of_continuousOn hk
  have hmap (t : ℝ) : circleMap (0:ℂ) 1 t ∈ sphere 0 1 :=
    circleMap_mem_sphere (0:ℂ) (by norm_num) t
  have hkc : Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
    hk.comp_continuous (continuous_circleMap 0 1) hmap
  unfold poissonExtension
  apply Filter.Tendsto.smul tendsto_const_nhds
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => C*‖f‖)
  · exact Eventually.of_forall fun i =>
      (hkc.smul ((circleSmooth (φ i) f).continuous.comp (AddCircle.continuous_mk' τ))).aestronglyMeasurable
  · exact Eventually.of_forall fun i => ae_of_all _ fun t _ => by
      rw [norm_smul]
      exact mul_le_mul (hC _ (hmap t)) (circleSmooth_norm_le (φ i) f t)
        (norm_nonneg _) (le_trans (norm_nonneg _) (hC _ (hmap t)))
  · exact intervalIntegrable_const
  · exact ae_of_all _ fun t _ => tendsto_const_nhds.smul (circleSmooth_tendsto hφ f t)

end StrictHotSpots.Douglas
end CirclePoissonConvergenceCombinedLayer

section DouglasRealEnergyCombinedLayer
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10

lemma real_component_gradient_bound (L : ℂ →L[ℝ] ℂ) :
    ‖(InnerProductSpace.toDual ℝ Plane).symm ((Complex.reCLM.comp L).comp
      complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖^2 ≤
      ‖L 1‖^2+‖L Complex.I‖^2 := by
  let v : Plane := (InnerProductSpace.toDual ℝ Plane).symm ((Complex.reCLM.comp L).comp
    complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  have hi (z : ℂ) : inner ℝ v (complexIso z) = (L z).re := by
    rw [show v = (InnerProductSpace.toDual ℝ Plane).symm ((Complex.reCLM.comp L).comp
      complexIso.symm.toContinuousLinearEquiv.toContinuousLinearMap) from rfl,
      InnerProductSpace.toDual_symm_apply]
    simp only [ContinuousLinearMap.comp_apply,ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_coe,LinearIsometryEquiv.symm_apply_apply,Complex.reCLM_apply]
  have hi' (z : ℂ) : inner ℝ (complexIso z) v = (L z).re := by
    rw [real_inner_comm]
    exact hi z
  have he := (Complex.orthonormalBasisOneI.map complexIso).sum_inner_mul_inner v v
  simp only [Fin.sum_univ_two,OrthonormalBasis.map_apply,Complex.coe_orthonormalBasisOneI,
    Matrix.cons_val_zero,Matrix.cons_val_one] at he
  simp only [hi,hi',real_inner_self_eq_norm_sq] at he
  change ‖v‖^2 ≤ _
  rw [← he,← sq,← sq]
  exact add_le_add (by simpa only [Complex.normSq_eq_norm_sq,pow_two] using Complex.re_sq_le_normSq (L 1))
    (by simpa only [Complex.normSq_eq_norm_sq,pow_two] using Complex.re_sq_le_normSq (L Complex.I))



theorem planeSeries_energy_le {a : ℤ → ℂ}
    (h0 : Summable (fun m => ‖a m‖))
    (h1 : Summable (fun m => (m.natAbs:ℝ)*‖a m‖)) :
    (∫ x : Plane in disk, ‖gradient (planeSeries a) x‖^2) ≤ diskEnergy (harmonicSeries a) := by
  have hm (x : Plane) (hx : x ∈ disk) :
      ‖gradient (planeSeries a) x‖^2 ≤
      ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) 1‖^2+
        ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) Complex.I‖^2 := by
    have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
      simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
    rw [(harmonicSeries_hasFDerivAt h0 h1 hz).fderiv]
    have hp := (planeSeries_hasFDerivAt h0 h1 hx).fderiv
    simp only [gradient]
    rw [hp]
    exact real_component_gradient_bound (harmonicD a (complexIso.symm x))
  have hI : Integrable (fun x : Plane =>
      ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) 1‖^2+
      ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) Complex.I‖^2) (volume.restrict disk) := by
    have hi : Integrable (fun x : Plane => ‖harmonicD a (complexIso.symm x) 1‖^2+
        ‖harmonicD a (complexIso.symm x) Complex.I‖^2) (volume.restrict disk) := by
      have hc : ContinuousOn (fun x : Plane => harmonicD a (complexIso.symm x))
          (closedBall 0 1) := (harmonicD_continuousOn h1).comp complexIso.symm.continuous.continuousOn (by
        intro x hx
        simpa only [mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx)
      have he : ContinuousOn (fun x : Plane => ‖harmonicD a (complexIso.symm x) 1‖^2+
          ‖harmonicD a (complexIso.symm x) Complex.I‖^2) (closedBall 0 1) :=
        ((hc.clm_apply continuousOn_const).norm.pow 2).add
          ((hc.clm_apply continuousOn_const).norm.pow 2)
      exact (he.integrableOn_compact (isCompact_closedBall (0:Plane) 1)).mono_set ball_subset_closedBall
    apply hi.congr
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
      simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
    rw [(harmonicSeries_hasFDerivAt h0 h1 hz).fderiv]
    rfl
  calc
    _ ≤ ∫ x : Plane in disk,
        ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) 1‖^2+
        ‖fderiv ℝ (harmonicSeries a) (complexIso.symm x) Complex.I‖^2 :=
      integral_mono_ae ((memLp_two_iff_integrable_sq_norm
        (planeSeries_gradient h0 h1).2.1.aestronglyMeasurable).mp (planeSeries_gradient h0 h1).2.1)
        hI ((ae_restrict_mem measurableSet_ball).mono fun x hx => hm x hx)
    _ = _ := complexIso_disk_preserving.integral_comp complexIso.symm.toHomeomorph.measurableEmbedding
      (fun z : ℂ => ‖fderiv ℝ (harmonicSeries a) z 1‖^2+‖fderiv ℝ (harmonicSeries a) z Complex.I‖^2)

end StrictHotSpots.Douglas
end DouglasRealEnergyCombinedLayer
end
end DouglasLipschitzBase


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_DouglasEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section PoissonContinuous


noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local notation "τ" => (2*Real.pi)



def circleDatum (f : C(AddCircle τ,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if hz : z ∈ sphere 0 1 then
    f ((AddCircle.homeomorphCircle (by positivity : τ ≠ 0)).symm ⟨z,hz⟩)
  else 0

@[simp] lemma circleDatum_toCircle (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    circleDatum f s.toCircle = f s := by
  have hs : (s.toCircle:ℂ) ∈ sphere 0 1 := by
    simp only [mem_sphere_zero_iff_norm,Circle.norm_coe]
  classical
  rw [circleDatum,dite_eq_left hs]
  apply congrArg f
  have he : (⟨(s.toCircle:ℂ),hs⟩ : Circle) =
      (AddCircle.homeomorphCircle (by positivity : τ ≠ 0)) s := by
    rw [AddCircle.homeomorphCircle_apply]
    exact Subtype.ext rfl
  rw [he,Homeomorph.symm_apply_apply]

@[simp] lemma circleDatum_circleMap (f : C(AddCircle τ,ℂ)) (t : ℝ) :
    circleDatum f (circleMap 0 1 t) = f t := by
  rw [circleMap_eq_toCircle,circleDatum_toCircle]

lemma poisson_angle_continuous (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t) • f t) := by
  have hk := poissonKernel_continuousOn_sphere hz
  have hkc : Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
    hk.comp_continuous (continuous_circleMap 0 1)
      (fun t => circleMap_mem_sphere (0:ℂ) (by norm_num) t)
  exact hkc.smul (f.continuous.comp (AddCircle.continuous_mk' τ))

lemma poissonExtension_eq_circleAverage (f : C(AddCircle τ,ℂ)) (z : ℂ) :
    poissonExtension f z = Real.circleAverage (poissonKernel 0 z • circleDatum f) 0 1 := by
  unfold poissonExtension Real.circleAverage
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Pi.smul_apply',circleDatum_circleMap]

lemma poissonExtension_re_eq_circleAverage (f : C(AddCircle τ,ℂ))
    {z : ℂ} (hz : z ∈ ball 0 1) :
    (poissonExtension f z).re =
      Real.circleAverage (poissonKernel 0 z • (fun ζ => (circleDatum f ζ).re)) 0 1 := by
  rw [poissonExtension_eq_circleAverage]
  have hi : CircleIntegrable (poissonKernel 0 z • circleDatum f) 0 1 := by
    change IntervalIntegrable (fun t : ℝ =>
      (poissonKernel 0 z • circleDatum f) (circleMap 0 1 t)) volume 0 τ
    simp only [Pi.smul_apply',circleDatum_circleMap]
    exact (poisson_angle_continuous f hz).intervalIntegrable _ _
  have he := Complex.reCLM.circleAverage_comp_comm hi
  refine he.symm.trans (congrArg (fun F : ℂ → ℝ => Real.circleAverage F 0 1) ?_)
  funext ζ
  simp only [Function.comp_apply,Pi.smul_apply',Complex.reCLM_apply,Complex.smul_re,smul_eq_mul]

lemma circleDatum_re_circleIntegrable (f : C(AddCircle τ,ℂ)) :
    CircleIntegrable (fun ζ => (circleDatum f ζ).re) 0 1 := by
  change IntervalIntegrable (fun t : ℝ => (circleDatum f (circleMap 0 1 t)).re) volume 0 τ
  simp only [circleDatum_circleMap]
  exact (Complex.continuous_re.comp (f.continuous.comp (AddCircle.continuous_mk' τ))).intervalIntegrable _ _



lemma poissonExtension_re_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (fun z => (poissonExtension f z).re) (ball 0 1) := by
  apply (poissonAverage_contDiffOn (circleDatum_re_circleIntegrable f)).congr
  intro z hz
  exact poissonExtension_re_eq_circleAverage f hz



def planePoisson (f : C(AddCircle τ,ℂ)) (x : Plane) : ℝ :=
  (poissonExtension f (complexIso.symm x)).re

lemma planePoisson_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (planePoisson f) disk := by
  apply (poissonExtension_re_contDiffOn f).comp complexIso.symm.contDiff.contDiffOn
  intro x hx
  simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx

end StrictHotSpots.Douglas
end
end PoissonContinuous

section PoissonBounds

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance instFactLtRealOfNatHMulPi_solutions_12 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma poisson_angle_kernel_nonneg {z : ℂ} (hz : z ∈ ball 0 1) (t : ℝ) :
    0 ≤ poissonKernel 0 z (circleMap 0 1 t) := by
  have hn : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
  have ht : ‖circleMap (0:ℂ) 1 t‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (circleMap_mem_sphere (0:ℂ) (by norm_num) t)
  rw [poissonKernel_def,sub_zero,sub_zero,ht,one_pow]
  exact div_nonneg (by nlinarith [norm_nonneg z]) (sq_nonneg _)

lemma poisson_angle_kernel_continuous {z : ℂ} (hz : z ∈ ball 0 1) :
    Continuous (fun t : ℝ => poissonKernel 0 z (circleMap 0 1 t)) :=
  (poissonKernel_continuousOn_sphere hz).comp_continuous (continuous_circleMap 0 1)
    (fun t => circleMap_mem_sphere (0:ℂ) (by norm_num) t)

lemma poisson_angle_mass {z : ℂ} (hz : z ∈ ball 0 1) :
    τ⁻¹ * (∫ t : ℝ in 0..τ, poissonKernel 0 z (circleMap 0 1 t)) = 1 := by
  have hc : InnerProductSpace.HarmonicOnNhd (fun _ : ℂ => (1:ℝ)) (closedBall 0 1) :=
    fun _ _ => InnerProductSpace.harmonicAt_const _
  have he := hc.circleAverage_poissonKernel_smul hz
  simpa only [Real.circleAverage,Pi.smul_apply',smul_eq_mul,mul_one] using he



theorem poissonExtension_norm_le (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    ‖poissonExtension f z‖ ≤ ‖f‖ := by
  have ht : (0:ℝ) ≤ τ := le_of_lt (by positivity)
  have hi := (poisson_angle_continuous f hz).intervalIntegrable (μ := volume) 0 τ
  have hk := (poisson_angle_kernel_continuous hz).intervalIntegrable (μ := volume) 0 τ
  rw [poissonExtension,norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ht)]
  calc
    _ ≤ τ⁻¹ * (∫ t : ℝ in 0..τ, ‖poissonKernel 0 z (circleMap 0 1 t) • f t‖) :=
      mul_le_mul_of_nonneg_left (intervalIntegral.norm_integral_le_integral_norm ht) (inv_nonneg.mpr ht)
    _ ≤ τ⁻¹ * (∫ t : ℝ in 0..τ, poissonKernel 0 z (circleMap 0 1 t)*‖f‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht)
      apply intervalIntegral.integral_mono ht hi.norm (hk.mul_const ‖f‖)
      intro t
      simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg (poisson_angle_kernel_nonneg hz t)]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (poisson_angle_kernel_nonneg hz t)
    _ = ‖f‖ := by
      rw [intervalIntegral.integral_mul_const,← mul_assoc,poisson_angle_mass hz,one_mul]

lemma planePoisson_norm_le (f : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) :
    ‖planePoisson f x‖ ≤ ‖f‖ := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact (Complex.abs_re_le_norm _).trans (poissonExtension_norm_le f hz)

lemma planePoisson_memLp (f : C(AddCircle τ,ℂ)) :
    MemLp (planePoisson f) 2 (volume.restrict disk) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Plane) 1)) :=
    isFiniteMeasure_restrict.mpr (isBounded_ball (x := (0:Plane)) (r := 1)).measure_lt_top.ne
  apply MemLp.of_bound ((planePoisson_contDiffOn f).continuousOn.aestronglyMeasurable measurableSet_ball) ‖f‖
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  exact planePoisson_norm_le f hx

lemma circleSmooth_sup_norm_le (φ : ContDiffBump (0:ℝ)) (f : C(AddCircle τ,ℂ)) :
    ‖circleSmooth φ f‖ ≤ ‖f‖ :=
  (ContinuousMap.norm_le (circleSmooth φ f) (norm_nonneg _)).mpr (circleSmooth_norm_le φ f)



theorem circleSmooth_planePoisson_tendsto_L2 {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) :
    Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) l
      (𝓝 ((planePoisson_memLp f).toLp (planePoisson f))) := by
  let : IsFiniteMeasure (volume.restrict (ball (0:Plane) 1)) :=
    isFiniteMeasure_restrict.mpr (isBounded_ball (x := (0:Plane)) (r := 1)).measure_lt_top.ne
  apply L2Limits.tendsto_toLp_of_dominated (fun i => planePoisson_memLp (circleSmooth (φ i) f))
    (planePoisson_memLp f) (memLp_const (‖f‖ : ℝ))
  · exact Eventually.of_forall fun i => (ae_restrict_mem measurableSet_ball).mono fun x hx =>
      (planePoisson_norm_le (circleSmooth (φ i) f) hx).trans (circleSmooth_sup_norm_le (φ i) f)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
      simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
    exact Complex.continuous_re.continuousAt.tendsto.comp (circleSmooth_poisson_tendsto hφ f hz)

end StrictHotSpots.Douglas
end
end PoissonBounds

section SmoothPoissonH1

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance instFactLtRealOfNatHMulPi_solutions_13 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma poissonExtension_sub (f g : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    poissonExtension (f-g) z = poissonExtension f z-poissonExtension g z := by
  change τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • (f t-g t)) =
    τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • f t) -
      τ⁻¹ • (∫ t in 0..τ, poissonKernel 0 z (circleMap 0 1 t) • g t)
  simp_rw [smul_sub]
  rw [intervalIntegral.integral_sub ((poisson_angle_continuous f hz).intervalIntegrable _ _)
    ((poisson_angle_continuous g hz).intervalIntegrable _ _),smul_sub]

lemma planePoisson_sub (f g : C(AddCircle τ,ℂ)) {x : Plane} (hx : x ∈ disk) :
    planePoisson (f-g) x = planePoisson f x-planePoisson g x := by
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact congrArg Complex.re (poissonExtension_sub f g hz)

lemma planePoisson_eq_series (f : C(AddCircle τ,ℂ))
    (h0 : Summable (fun m => ‖fourierCoeff f m‖)) :
    EqOn (planePoisson f) (planeSeries (fourierCoeff f)) disk := by
  intro x hx
  have hz : complexIso.symm x ∈ ball (0:ℂ) 1 := by
    simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx
  exact congrArg Complex.re (poissonExtension_eq_harmonicSeries f h0 hz)


lemma smooth_planePoisson_hasH1Gradient (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    HasH1Gradient disk (planePoisson f) (gradient (planePoisson f)) := by
  have h1 := summable_firstMoment_of_smooth_lift f hf
  have h0 := summable_norm_of_firstMoment h1
  have he := planePoisson_eq_series f h0
  apply (planeSeries_gradient h0 h1).congr
  · filter_upwards [ae_restrict_mem (show MeasurableSet disk from measurableSet_ball)] with x hx
    exact (he hx).symm
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    unfold gradient
    rw [(he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]


def smoothPoissonH1 (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) : H1 disk :=
  (smooth_planePoisson_hasH1Gradient f hf).toH1

lemma smoothPoissonH1_value (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    H1.value (smoothPoissonH1 f hf) = (planePoisson_memLp f).toLp (planePoisson f) := rfl

lemma smoothPoissonH1_sub (f g : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t))
    (hg : ContDiff ℝ ∞ (fun t : ℝ => g t)) :
    smoothPoissonH1 (f-g) (hf.sub hg) = smoothPoissonH1 f hf-smoothPoissonH1 g hg := by
  apply H1.value_injective (Ω := disk) isOpen_ball
  rw [map_sub,smoothPoissonH1_value,smoothPoissonH1_value,smoothPoissonH1_value]
  rw [← MemLp.toLp_sub]
  apply Lp.ext
  filter_upwards [(planePoisson_memLp (f-g)).coeFn_toLp,
    ((planePoisson_memLp f).sub (planePoisson_memLp g)).coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x h1 h2 hx
  rw [h1,h2]
  exact planePoisson_sub f g hx

lemma lp_norm_sq_eq_integral_norm_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    (u : Lp E 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma norm_toLp_sq_eq_integral_norm_sq {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {μ : Measure X}
    {u : X → E} (hu : MemLp u 2 μ) :
    ‖hu.toLp u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [lp_norm_sq_eq_integral_norm_sq]
  exact integral_congr_ae (hu.coeFn_toLp.mono fun x hx => by dsimp only; rw [hx])



lemma smoothPoissonH1_grad_energy_le (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    ‖H1.grad (smoothPoissonH1 f hf)‖^2 ≤ diskEnergy (poissonExtension f) := by
  have h1 := summable_firstMoment_of_smooth_lift f hf
  have h0 := summable_norm_of_firstMoment h1
  have he := planePoisson_eq_series f h0
  change ‖(smooth_planePoisson_hasH1Gradient f hf).2.1.toLp _‖^2 ≤ _
  rw [norm_toLp_sq_eq_integral_norm_sq]
  have hE : (∫ x : Plane in disk, ‖gradient (planePoisson f) x‖^2) =
      ∫ x : Plane in disk, ‖gradient (planeSeries (fourierCoeff f)) x‖^2 := by
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    unfold gradient
    rw [(he.eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]
  rw [hE]
  have hC : diskEnergy (poissonExtension f) = diskEnergy (harmonicSeries (fourierCoeff f)) := by
    apply setIntegral_congr_fun measurableSet_ball
    intro z hz
    have he' : EqOn (poissonExtension f) (harmonicSeries (fourierCoeff f)) (ball 0 1) :=
      fun z hz => poissonExtension_eq_harmonicSeries f h0 hz
    have hd := (he'.eventuallyEq_of_mem (isOpen_ball.mem_nhds hz)).fderiv_eq (𝕜:=ℝ)
    dsimp only
    rw [hd]
  rw [hC]
  exact planeSeries_energy_le h0 h1

end StrictHotSpots.Douglas
end
end SmoothPoissonH1

section SmoothWeakGradient

noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots





theorem HasH1Gradient.eq_gradient_of_contDiffOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {g : Plane → Plane} (hg : HasH1Gradient Ω v g)
    (hv : ContDiffOn ℝ ∞ v Ω) :
    g =ᵐ[volume.restrict Ω] gradient v := by
  have hgc : ContinuousOn (gradient v) Ω :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hv.continuousOn_fderiv_of_isOpen ho (by simp))
  have hi (e : Plane) : ∀ᵐ x ∂volume.restrict Ω, inner ℝ (g x - gradient v x) e = 0 := by
    have hgL := ((hg.2.1.inner_const (𝕜 := ℝ) e).locallyIntegrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)).locallyIntegrableOn Ω
    have hkc : ContinuousOn (fun x => inner ℝ (gradient v x) e) Ω :=
      hgc.inner continuousOn_const
    have hkL : LocallyIntegrableOn (fun x => inner ℝ (gradient v x) e) Ω
        (volume.restrict Ω) := hkc.locallyIntegrableOn ho.measurableSet
    have hl : LocallyIntegrableOn (fun x => inner ℝ (g x-gradient v x) e) Ω
        (volume.restrict Ω) := by
      have he : (fun x => inner ℝ (g x-gradient v x) e) =
          (fun x => inner ℝ (g x) e) - (fun x => inner ℝ (gradient v x) e) := by
        funext x
        exact inner_sub_left _ _ _
      rw [he]
      exact hgL.sub hkL
    have ht := ho.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (μ := volume.restrict Ω) hl
      (fun φ hφ hc hs => show (∫ x in Ω, φ x • inner ℝ (g x-gradient v x) e) = 0 from by
        have hgφ := hg.2.2 φ hφ hc hs e
        have hkφ := integral_mul_test_fderiv ho hv hφ hc hs e
        have hgi : Integrable (fun x => inner ℝ (g x) e * φ x) (volume.restrict Ω) :=
          (hg.2.1.inner_const e).integrable_mul (test_memLp hφ hc)
        have hki : Integrable (fun x => inner ℝ (gradient v x) e * φ x) (volume.restrict Ω) :=
          (integrable_mul_test ho hkc hφ.continuous hc hs).restrict
        simp only [smul_eq_mul, inner_sub_left, mul_sub]
        rw [integral_sub (by simpa [Pi.mul_apply, mul_comm] using hgi)
          (by simpa [Pi.mul_apply, mul_comm] using hki)]
        simp_rw [mul_comm (φ _)]
        simp only [inner_gradient_left] at *
        linarith)
    filter_upwards [ht, ae_restrict_mem ho.measurableSet] with x hx hxΩ
    exact hx hxΩ
  have hb : ∀ᵐ x ∂volume.restrict Ω, ∀ i : Fin 2,
      inner ℝ (g x-gradient v x) (EuclideanSpace.basisFun (Fin 2) ℝ i) = 0 :=
    ae_all_iff.mpr fun i => hi _
  filter_upwards [hb] with x hx
  have hz : g x-gradient v x = 0 := by
    ext i
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.inner_single_right] using hx i
  exact sub_eq_zero.mp hz

lemma HasH1Gradient.actual_of_contDiffOn {Ω : Set Plane} (ho : IsOpen Ω)
    {v : Plane → ℝ} {g : Plane → Plane} (hg : HasH1Gradient Ω v g)
    (hv : ContDiffOn ℝ ∞ v Ω) : HasH1Gradient Ω v (gradient v) :=
  hg.congr (Filter.EventuallyEq.refl _ _) (hg.eq_gradient_of_contDiffOn ho hv)

end StrictHotSpots
end
end SmoothWeakGradient

section LipschitzPoissonH1

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local notation "τ" => (2*Real.pi)

lemma cauchySeq_of_pair_norm_sq_zero {E : Type*} [NormedAddCommGroup E] {u : ℕ → E}
    (hu : Tendsto (fun p : ℕ × ℕ => ‖u p.1-u p.2‖^2) (atTop ×ˢ atTop) (𝓝 0)) :
    CauchySeq u := by
  have ht : Tendsto (fun p : ℕ × ℕ => ‖u p.1-u p.2‖) (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hu
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  have h := ht.eventually (gt_mem_nhds hε)
  rw [prod_atTop_atTop_eq] at h
  obtain ⟨⟨N,M⟩,hNM⟩ := eventually_atTop.mp h
  refine ⟨max N M,fun n hn m hm => ?_⟩
  rw [dist_eq_norm]
  exact hNM (n,m) ⟨le_trans (le_max_left _ _) hn,le_trans (le_max_right _ _) hm⟩



theorem circleSmooth_cauchy_H1 {φ : ℕ → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    CauchySeq (fun i => smoothPoissonH1 (circleSmooth (φ i) f) (angleSmooth_smooth (φ i) f)) := by
  let u := fun i => smoothPoissonH1 (circleSmooth (φ i) f) (angleSmooth_smooth (φ i) f)
  have hv : Tendsto (fun i => H1.value (u i)) atTop
      (𝓝 ((planePoisson_memLp f).toLp (planePoisson f))) := by
    change Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) atTop _
    exact circleSmooth_planePoisson_tendsto_L2 hφ f
  have hv0 : Tendsto (fun p : ℕ × ℕ => ‖H1.value (u p.1)-H1.value (u p.2)‖^2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0)] using
      ((hv.comp tendsto_fst).sub (hv.comp tendsto_snd)).norm.pow 2
  have hg0 : Tendsto (fun p : ℕ × ℕ => ‖H1.grad (u p.1-u p.2)‖^2)
      (atTop ×ˢ atTop) (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ (circleSmooth_poisson_cauchy hφ f hK h)
    intro p
    rw [show u p.1-u p.2 = smoothPoissonH1
      (circleSmooth (φ p.1) f-circleSmooth (φ p.2) f)
      ((angleSmooth_smooth (φ p.1) f).sub (angleSmooth_smooth (φ p.2) f)) from
        (smoothPoissonH1_sub _ _ _ _).symm]
    exact smoothPoissonH1_grad_energy_le _ _
  apply cauchySeq_of_pair_norm_sq_zero
  have hs := hv0.add hg0
  simpa only [H1.norm_sq,map_sub,add_zero] using hs




theorem hasH1Gradient_of_circleSmooth {φ : ℕ → ContDiffBump (0:ℝ)}
    (hφ : Tendsto (fun i => (φ i).rOut) atTop (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    HasH1Gradient disk (planePoisson f) (gradient (planePoisson f)) := by
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete (circleSmooth_cauchy_H1 hφ f hK h)
  have hv : H1.value u = (planePoisson_memLp f).toLp (planePoisson f) := by
    apply tendsto_nhds_unique (H1.value.continuous.continuousAt.tendsto.comp hu)
    change Tendsto (fun i => (planePoisson_memLp (circleSmooth (φ i) f)).toLp
      (planePoisson (circleSmooth (φ i) f))) atTop _
    exact circleSmooth_planePoisson_tendsto_L2 hφ f
  have hw : HasH1Gradient disk (planePoisson f) (H1.grad u) := by
    apply (H1.hasH1Gradient u).congr _ (Filter.EventuallyEq.refl _ _)
    rw [hv]
    exact (planePoisson_memLp f).coeFn_toLp
  exact hw.actual_of_contDiffOn isOpen_ball (planePoisson_contDiffOn f)



def circleApproxBump (n : ℕ) : ContDiffBump (0:ℝ) where
  rIn := (2*((n:ℝ)+1))⁻¹
  rOut := ((n:ℝ)+1)⁻¹
  rIn_pos := by positivity
  rIn_lt_rOut := by
    apply inv_strictAnti₀ (by positivity)
    nlinarith [Nat.cast_nonneg (α:=ℝ) n]

lemma circleApproxBump_rOut_tendsto :
    Tendsto (fun n => (circleApproxBump n).rOut) atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)


theorem lipschitz_planePoisson_hasH1Gradient (f : C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    HasH1Gradient disk (planePoisson f) (gradient (planePoisson f)) :=
  hasH1Gradient_of_circleSmooth circleApproxBump_rOut_tendsto f hK h

end StrictHotSpots.Douglas
end
end LipschitzPoissonH1

section PoissonBoundaryContinuous

noncomputable section
open Set MeasureTheory Filter Metric AddCircle Function
open scoped Topology ComplexConjugate ContDiff InnerProductSpace
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local instance instFactLtRealOfNatHMulPi_solutions_17 : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
local notation "τ" => (2*Real.pi)

lemma chordLipschitz_equicontinuous {ι : Type*} (F : ι → C(AddCircle τ,ℂ))
    {K : ℝ} (hK : 0 ≤ K) (h : ∀ i, ChordLipschitz K (F i)) :
    Equicontinuous (fun i => (F i : AddCircle τ → ℂ)) := by
  intro s
  rw [Metric.equicontinuousAt_iff_right]
  intro ε hε
  have hc : Continuous (fun t : AddCircle τ => ‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖) := by
    fun_prop
  have he : ∀ᶠ t in 𝓝 s, ‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖ < ε/(K+1) :=
    hc.continuousAt.preimage_mem_nhds (Iio_mem_nhds (by simp; positivity))
  filter_upwards [he] with t ht i
  rw [dist_comm,dist_eq_norm]
  calc
    _ ≤ K*‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖ := h i t s
    _ ≤ (K+1)*‖(t.toCircle:ℂ)-(s.toCircle:ℂ)‖ :=
      mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < ε := by nlinarith [(lt_div_iff₀ (by linarith : 0 < K+1)).mp ht]

lemma circleSmooth_tendsto_uniform {ι : Type*} {l : Filter ι}
    {φ : ι → ContDiffBump (0:ℝ)} (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    (f : C(AddCircle τ,ℂ)) {K : ℝ} (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    Tendsto (fun i => circleSmooth (φ i) f) l (𝓝 f) := by
  have he := chordLipschitz_equicontinuous (fun i => circleSmooth (φ i) f) hK
    (fun i => circleSmooth_chordLipschitz (φ i) f h)
  have ht := (he.tendsto_uniformFun_iff_pi l f).mpr
    (tendsto_pi_nhds.mpr (fun s => circleSmooth_tendsto hφ f s))
  exact ContinuousMap.tendsto_iff_tendstoUniformly.mpr
    (UniformFun.tendsto_iff_tendstoUniformly.mp ht)




def closedPoisson (f : C(AddCircle τ,ℂ)) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ ball 0 1 then poissonExtension f z else circleDatum f z

lemma closedPoisson_interior (f : C(AddCircle τ,ℂ)) {z : ℂ} (hz : z ∈ ball 0 1) :
    closedPoisson f z = poissonExtension f z := by
  classical
  exact ite_eq_left hz

lemma closedPoisson_boundary (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    closedPoisson f s.toCircle = f s := by
  classical
  rw [closedPoisson,ite_eq_right (by simp only [mem_ball_zero_iff,Circle.norm_coe,lt_self_iff_false,not_false_eq_true]),circleDatum_toCircle]

lemma exists_toCircle {z : ℂ} (hz : z ∈ sphere 0 1) :
    ∃ s : AddCircle τ, (s.toCircle:ℂ) = z := by
  obtain ⟨s,hs⟩ := (AddCircle.homeomorphCircle (by positivity : τ ≠ 0)).surjective ⟨z,hz⟩
  refine ⟨s,?_⟩
  have he := congrArg (fun c : Circle => (c:ℂ)) hs
  simpa only [AddCircle.homeomorphCircle_apply] using he

lemma smooth_closedPoisson_continuousOn (f : C(AddCircle τ,ℂ))
    (hf : ContDiff ℝ ∞ (fun t : ℝ => f t)) :
    ContinuousOn (closedPoisson f) (closedBall 0 1) := by
  have h0 := summable_norm_of_firstMoment (summable_firstMoment_of_smooth_lift f hf)
  apply (harmonicSeries_continuousOn h0).congr
  intro z hz
  by_cases hi : z ∈ ball 0 1
  · exact (closedPoisson_interior f hi).trans (poissonExtension_eq_harmonicSeries f h0 hi)
  · have hs : z ∈ sphere 0 1 := by
      simp only [mem_ball_zero_iff,not_lt] at hi
      simp only [mem_closedBall_zero_iff] at hz
      exact mem_sphere_zero_iff_norm.mpr (le_antisymm hz hi)
    obtain ⟨s,rfl⟩ := exists_toCircle hs
    rw [closedPoisson_boundary,harmonicSeries_fourier_boundary f h0]

lemma closedPoisson_sub (f g : C(AddCircle τ,ℂ)) (z : ℂ) :
    closedPoisson (f-g) z = closedPoisson f z-closedPoisson g z := by
  classical
  by_cases hi : z ∈ ball 0 1
  · simp only [closedPoisson,ite_eq_left hi]
    exact poissonExtension_sub f g hi
  · simp only [closedPoisson,ite_eq_right hi,circleDatum]
    split_ifs <;> simp

lemma closedPoisson_norm_le (f : C(AddCircle τ,ℂ)) (z : ℂ) :
    ‖closedPoisson f z‖ ≤ ‖f‖ := by
  classical
  by_cases hi : z ∈ ball 0 1
  · rw [closedPoisson_interior f hi]
    exact poissonExtension_norm_le f hi
  · simp only [closedPoisson,ite_eq_right hi,circleDatum]
    split_ifs
    · exact f.norm_coe_le_norm _
    · simp



theorem closedPoisson_continuousOn (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    ContinuousOn (closedPoisson f) (closedBall 0 1) := by
  have ht := ((circleSmooth_tendsto_uniform circleApproxBump_rOut_tendsto f hK h).sub
    (tendsto_const_nhds (x:=f))).norm
  have hzero : Tendsto (fun n : ℕ => ‖circleSmooth (circleApproxBump n) f-f‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using ht
  have hu : TendstoUniformlyOn (fun n : ℕ => closedPoisson (circleSmooth (circleApproxBump n) f))
      (closedPoisson f) atTop (closedBall 0 1) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    filter_upwards [hzero.eventually (Iio_mem_nhds hε)] with n hn z _
    rw [dist_comm,dist_eq_norm,← closedPoisson_sub]
    exact (closedPoisson_norm_le _ z).trans_lt hn
  apply hu.continuousOn
  exact Eventually.frequently (Eventually.of_forall fun n =>
    smooth_closedPoisson_continuousOn _ (angleSmooth_smooth (circleApproxBump n) f))

end StrictHotSpots.Douglas
end
end PoissonBoundaryContinuous

section LipschitzPoissonVariational

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology ContDiff InnerProductSpace Laplacian
namespace StrictHotSpots.Douglas
open PlaneGreen DiskH10
local notation "τ" => (2*Real.pi)

def closedPlanePoisson (f : C(AddCircle τ,ℂ)) (x : Plane) : ℝ :=
  (closedPoisson f (complexIso.symm x)).re

lemma closedPlanePoisson_eqOn (f : C(AddCircle τ,ℂ)) :
    EqOn (closedPlanePoisson f) (planePoisson f) disk := by
  intro x hx
  exact congrArg Complex.re (closedPoisson_interior f
    (by simpa only [disk,mem_ball_zero_iff,LinearIsometryEquiv.norm_map] using hx))

lemma closedPlanePoisson_boundary (f : C(AddCircle τ,ℂ)) (s : AddCircle τ) :
    closedPlanePoisson f (complexIso s.toCircle) = (f s).re := by
  simp only [closedPlanePoisson,LinearIsometryEquiv.symm_apply_apply,closedPoisson_boundary]

lemma closedPlanePoisson_contDiffOn (f : C(AddCircle τ,ℂ)) :
    ContDiffOn ℝ ∞ (closedPlanePoisson f) disk :=
  (planePoisson_contDiffOn f).congr (closedPlanePoisson_eqOn f)

lemma closedPlanePoisson_continuousOn (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    ContinuousOn (closedPlanePoisson f) (closure disk) := by
  apply Complex.continuous_re.comp_continuousOn
  apply (closedPoisson_continuousOn f hK h).comp complexIso.symm.continuous.continuousOn
  intro x hx
  simpa only [disk,closure_ball (0:Plane) (by norm_num : (1:ℝ) ≠ 0),
    mem_closedBall_zero_iff,LinearIsometryEquiv.norm_map] using hx

lemma closedPlanePoisson_hasH1Gradient (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    HasH1Gradient disk (closedPlanePoisson f) (gradient (closedPlanePoisson f)) := by
  apply (lipschitz_planePoisson_hasH1Gradient f hK h).congr
  · exact (ae_restrict_mem measurableSet_ball).mono (fun x hx => (closedPlanePoisson_eqOn f hx).symm)
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    unfold gradient
    rw [((closedPlanePoisson_eqOn f).eventuallyEq_of_mem (isOpen_ball.mem_nhds hx)).fderiv_eq]

lemma closedPlanePoisson_toH1 (f : C(AddCircle τ,ℂ)) {K : ℝ}
    (hK : 0 ≤ K) (h : ChordLipschitz K f) :
    (closedPlanePoisson_hasH1Gradient f hK h).toH1 =
      (lipschitz_planePoisson_hasH1Gradient f hK h).toH1 := by
  apply H1.value_injective (Ω:=disk) isOpen_ball
  rw [H1.value_toH1,H1.value_toH1]
  apply Lp.ext
  filter_upwards [(closedPlanePoisson_hasH1Gradient f hK h).1.coeFn_toLp,
    (lipschitz_planePoisson_hasH1Gradient f hK h).1.coeFn_toLp,
    ae_restrict_mem measurableSet_ball] with x h1 h2 hx
  rw [h1,h2]
  exact closedPlanePoisson_eqOn f hx




end StrictHotSpots.Douglas
end
end LipschitzPoissonVariational

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section LipschitzBoundaryScalarSupport

noncomputable section

section BoundaryMeasureScalarSupportLayer

section BoundaryMeasureLayer
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology InnerProductSpace
namespace StrictHotSpots.PlaneGreen
open DiskH10

def circleBoundary : Circle ≃ₜ Boundary where
  toFun s := ⟨complexIso (s : ℂ), by simp [Circle.norm_coe]⟩
  invFun s := ⟨complexIso.symm (s : Plane), by change dist (complexIso.symm (s : Plane)) 0 = 1; simpa using s.property⟩
  left_inv s := by ext; simp
  right_inv s := by ext; simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

def angleBoundary : AddCircle (2 * Real.pi) ≃ₜ Boundary :=
  AddCircle.homeomorphCircle'.trans circleBoundary


end StrictHotSpots.PlaneGreen
end
end BoundaryMeasureLayer
end BoundaryMeasureScalarSupportLayer

end
end LipschitzBoundaryScalarSupport


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Conformal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalCoordinates


noncomputable section
open Set MeasureTheory _root_.Complex ComplexConjugate InnerProductSpace
open scoped InnerProductSpace Topology ContDiff
namespace StrictHotSpots.Conformal

abbrev CoordinatePlane := EuclideanSpace ℝ (Fin 2)
def coordinate : ℂ ≃ₗᵢ[ℝ] CoordinatePlane := Complex.orthonormalBasisOneI.repr

def planeMul (a : ℂ) : CoordinatePlane →L[ℝ] CoordinatePlane :=
  coordinate.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (((ContinuousLinearMap.toSpanSingleton ℂ a).restrictScalars ℝ).comp
      coordinate.symm.toContinuousLinearEquiv.toContinuousLinearMap)

lemma planeMul_apply (a : ℂ) (z : CoordinatePlane) :
    planeMul a z = coordinate (a*coordinate.symm z) := by
  simp [planeMul,mul_comm]

lemma plane_gradient_comp {f : CoordinatePlane → CoordinatePlane}
    {w : CoordinatePlane → ℝ} {a : ℂ} {x : CoordinatePlane}
    (hf : HasFDerivAt f (planeMul a) x) (hw : DifferentiableAt ℝ w (f x)) :
    gradient (w ∘ f) x = coordinate (conj a * coordinate.symm (gradient w (f x))) := by
  apply ext_inner_right ℝ
  intro z
  rw [inner_gradient_left,(hw.hasFDerivAt.comp x hf).fderiv]
  change fderiv ℝ w (f x) (planeMul a z) = _
  rw [planeMul_apply,← inner_gradient_left]
  have he (g : CoordinatePlane) (v : ℂ) :
      inner ℝ g (coordinate v) = inner ℝ (coordinate.symm g) v := by
    rw [← coordinate.inner_map_map (coordinate.symm g) v, coordinate.apply_symm_apply]
  rw [he,← coordinate.symm.inner_map_map (coordinate _) z,coordinate.symm_apply_apply]
  simp only [Complex.inner, map_mul, conj_conj]
  congr 1
  ring

lemma plane_norm_gradient_comp {f : CoordinatePlane → CoordinatePlane}
    {w : CoordinatePlane → ℝ} {a : ℂ} {x : CoordinatePlane}
    (hf : HasFDerivAt f (planeMul a) x) (hw : DifferentiableAt ℝ w (f x)) :
    ‖gradient (w ∘ f) x‖ = ‖a‖ * ‖gradient w (f x)‖ := by
  rw [plane_gradient_comp hf hw, coordinate.norm_map,norm_mul,norm_conj,
    coordinate.symm.norm_map]

end StrictHotSpots.Conformal
end
end ConformalCoordinates

section CompactChartTransport




noncomputable section
open Set Filter
open scoped Topology ContDiff Classical
namespace CompactChart
variable {E : Type*} [NormedAddCommGroup E]

variable (e : OpenPartialHomeomorph E E)

def transport (f : E → ℝ) : E → ℝ := fun y => if y ∈ e.target then f (e.symm y) else 0

lemma transport_apply {f : E → ℝ} {y : E} (hy : y ∈ e.target) :
    transport e f y = f (e.symm y) := ite_eq_left hy

lemma support_transport_subset {f : E → ℝ} :
    Function.support (transport e f) ⊆ e '' tsupport f := by
  intro y hy
  by_cases hyt : y ∈ e.target
  · refine ⟨e.symm y,subset_tsupport _ ?_,e.right_inv hyt⟩
    simpa only [Function.mem_support,transport_apply e hyt] using hy
  · exact False.elim (hy (ite_eq_right hyt))

lemma compact_image_tsupport {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : IsCompact (e '' tsupport f) :=
  hc.image_of_continuousOn (e.continuousOn.mono hs)

lemma tsupport_transport_subset {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : tsupport (transport e f) ⊆ e '' tsupport f := by
  exact closure_minimal (support_transport_subset e) (compact_image_tsupport e hc hs).isClosed

lemma hasCompactSupport_transport {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : HasCompactSupport (transport e f) :=
  (compact_image_tsupport e hc hs).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_transport_subset e hc hs)

lemma transport_support_target {f : E → ℝ} (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ e.source) : tsupport (transport e f) ⊆ e.target := by
  intro y hy
  obtain ⟨x,hx,rfl⟩ := tsupport_transport_subset e hc hs hy
  exact e.map_source (hs hx)

lemma transport_eventuallyEq {f : E → ℝ} {y : E} (hy : y ∈ e.target) :
    transport e f =ᶠ[𝓝 y] f ∘ e.symm := by
  filter_upwards [e.open_target.mem_nhds hy] with z hz
  exact transport_apply e hz

lemma contDiff_transport [NormedSpace ℝ E] {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ e.source)
    (he : ContDiffOn ℝ ∞ e.symm e.target) : ContDiff ℝ ∞ (transport e f) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y ∈ e.target
  · exact (hf.contDiffAt.comp y ((he y hy).contDiffAt (e.open_target.mem_nhds hy))).congr_of_eventuallyEq
      (transport_eventuallyEq e hy)
  · exact contDiffAt_const.congr_of_eventuallyEq
      (notMem_tsupport_iff_eventuallyEq.mp (fun h => hy (transport_support_target e hc hs h)))

lemma transport_add (f g : E → ℝ) :
    transport e (f+g) = transport e f+transport e g := by
  funext y
  by_cases hy : y ∈ e.target <;> simp [transport,hy]

lemma transport_smul (c : ℝ) (f : E → ℝ) :
    transport e (c • f) = c • transport e f := by
  funext y
  by_cases hy : y ∈ e.target <;> simp [transport,hy]

end CompactChart
end
end CompactChartTransport

section ConformalMeasure




noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph CoordinatePlane CoordinatePlane) (d : CoordinatePlane → ℂ)

def chartMeasure : Measure CoordinatePlane :=
  (volume.restrict e.source).withDensity (fun x => ENNReal.ofReal (‖d x‖^2))

end StrictHotSpots.Conformal
end
end ConformalMeasure


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Riemann
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ConformalPotential





noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology ENNReal
namespace StrictHotSpots.Conformal

variable (e : OpenPartialHomeomorph Plane Plane) (d : Plane → ℂ)
variable (hd : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x)


def potentialMeasure (μ : ℝ) : Measure Plane :=
  ENNReal.ofReal μ • chartMeasure e d

lemma potentialMeasure_density {μ : ℝ} (hμ : 0 ≤ μ) :
    potentialMeasure e d μ = (volume.restrict e.source).withDensity
      (fun x => ENNReal.ofReal (μ*‖d x‖^2)) := by
  have hh := withDensity_smul' (μ:=volume.restrict e.source) (ENNReal.ofReal μ)
    (fun x => ENNReal.ofReal (‖d x‖^2)) ENNReal.ofReal_ne_top
  simpa only [potentialMeasure,chartMeasure,Pi.smul_def,smul_eq_mul,
    ENNReal.ofReal_mul hμ] using hh.symm

end StrictHotSpots.Conformal
end
end ConformalPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_ClosedChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section RiemannBoundaryCompatible

noncomputable section


section SmoothBoundaryGeometryCompatibleLayer

open Set Filter Metric
open scoped Topology ContDiff
namespace StrictHotSpots

lemma HasFDerivAt.eventually_lt_along_ray {f : Plane → ℝ} {D : Plane →L[ℝ] ℝ}
    {p v : Plane} (hf : HasFDerivAt f D p) (hv : D v < 0) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), f (p + t • v) < f p := by
  have hl : HasDerivAt (fun t : ℝ => p + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add p
  have hh : HasDerivAt (fun t : ℝ => f (p + t • v)) (D v) 0 := by
    exact (show HasFDerivAt f D (p + (0 : ℝ) • v) by simpa using hf).comp_hasDerivAt 0 hl
  have ht := (HasDerivAt.tendsto_slope_zero_right hh).eventually (gt_mem_nhds hv)
  filter_upwards [ht,self_mem_nhdsWithin] with t ht htp
  simp only [zero_add,zero_smul,add_zero,smul_eq_mul,inv_mul_eq_div] at ht
  have hh : f (p + t • v) - f p < 0 := by
    have := (div_lt_iff₀ htp).mp ht
    simpa only [zero_mul] using this
  exact sub_neg.mp hh

lemma regular_level_uniqueDiffWithinAt {Ω U : Set Plane} {ρ : Plane → ℝ} {p : Plane}
    (hU : IsOpen U) (hpU : p ∈ U) (hρ : DifferentiableAt ℝ ρ p)
    (hD : fderiv ℝ ρ p ≠ 0) (hp : ρ p = 0)
    (hlevel : Ω ∩ U = {x | ρ x < 0} ∩ U) (hpcl : p ∈ closure Ω) :
    UniqueDiffWithinAt ℝ (closure Ω) p := by
  have hopen : IsOpen {v : Plane | fderiv ℝ ρ p v < 0} :=
    isOpen_lt (fderiv ℝ ρ p).continuous continuous_const
  have hne : {v : Plane | fderiv ℝ ρ p v < 0}.Nonempty := by
    have hn : ∃ v, fderiv ℝ ρ p v ≠ 0 := by
      by_contra hh
      apply hD
      ext v
      simpa using not_exists.mp hh v
    obtain ⟨v,hv⟩ := hn
    rcases lt_or_gt_of_ne hv with hv | hv
    · exact ⟨v,hv⟩
    · refine ⟨-v,?_⟩
      change fderiv ℝ ρ p (-v) < 0
      rw [map_neg]
      linarith
  have hsub : {v : Plane | fderiv ℝ ρ p v < 0} ⊆ tangentConeAt ℝ Ω p := by
    intro v hv
    apply mem_tangentConeAt_of_add_smul_mem (c := fun t : ℝ => t)
      (tendsto_id'.mpr (nhdsGT_le_nhdsNE (0 : ℝ)))
    have ht : Tendsto (fun t : ℝ => p + t • v) (𝓝[>] 0) (𝓝 p) := by
      simpa using tendsto_const_nhds.add ((tendsto_id'.mpr (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)).smul_const v)
    filter_upwards [HasFDerivAt.eventually_lt_along_ray hρ.hasFDerivAt hv,ht (hU.mem_nhds hpU)] with t hneg htU
    have hh : p + t • v ∈ {x | ρ x < 0} ∩ U := ⟨by change ρ (p + t • v) < 0; simpa only [hp] using hneg,htU⟩
    rw [← hlevel] at hh
    exact hh.1
  have hspan : Submodule.span ℝ (tangentConeAt ℝ Ω p) = ⊤ := by
    apply Submodule.eq_top_of_nonempty_interior'
    obtain ⟨v,hv⟩ := hne
    refine ⟨v,?_⟩
    exact interior_mono (hsub.trans Submodule.subset_span) (hopen.interior_eq.symm ▸ hv)
  rw [uniqueDiffWithinAt_iff,tangentConeAt_closure,hspan]
  exact ⟨by simp,subset_closure hpcl⟩

lemma SmoothBoundary.uniqueDiffOn_closure {Ω : Set Plane} (hs : SmoothBoundary Ω)
    (hΩ : IsOpen Ω) : UniqueDiffOn ℝ (closure Ω) := by
  intro p hp
  by_cases hpi : p ∈ Ω
  · exact (hΩ.uniqueDiffOn p hpi).mono subset_closure
  · have hpf : p ∈ frontier Ω := ⟨hp,by simpa only [hΩ.interior_eq] using hpi⟩
    obtain ⟨U,ρ,hU,hpU,hρ,hD,hpρ,hlevel⟩ := hs p hpf
    exact regular_level_uniqueDiffWithinAt hU hpU
      ((hρ p hpU).contDiffAt (hU.mem_nhds hpU) |>.differentiableAt (by simp))
      hD hpρ hlevel hp

end StrictHotSpots
end SmoothBoundaryGeometryCompatibleLayer


end
end RiemannBoundaryCompatible

section ActualClosedConformal

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal
namespace StrictHotSpots.Conformal



structure ClosedDiskChart (Ω : Set Plane) where
  e : OpenPartialHomeomorph Plane Plane
  d : Plane → ℂ
  d' : Plane → ℂ
  source_eq : e.source = DiskH10.disk
  target_eq : e.target = Ω
  smooth : ContDiffOn ℝ ∞ e e.source
  inverse_smooth : ContDiffOn ℝ ∞ e.symm e.target
  deriv : ∀ x ∈ e.source, HasFDerivAt e (planeMul (d x)) x
  inverse_deriv : ∀ y ∈ e.target, HasFDerivAt e.symm (planeMul (d' y)) y
  nonzero : ∀ x ∈ e.source, d x ≠ 0
  inverse_nonzero : ∀ y ∈ e.target, d' y ≠ 0
  bound : ℝ
  inverse_bound : ℝ
  bound_pos : 0 < bound
  inverse_bound_pos : 0 < inverse_bound
  bounded_deriv : ∀ x ∈ e.source, ‖d x‖ ≤ bound
  bounded_inverse_deriv : ∀ y ∈ e.target, ‖d' y‖ ≤ inverse_bound
  F : Plane → Plane
  G : Plane → Plane
  Lip : ℝ≥0
  InvLip : ℝ≥0
  lipschitz : LipschitzWith Lip F
  inverse_lipschitz : LipschitzWith InvLip G
  agrees : EqOn e F e.source
  inverse_agrees : EqOn e.symm G e.target
  maps_closure : MapsTo F (closure e.source) (closure Ω)
  inverse_maps_closure : MapsTo G (closure Ω) (closure e.source)
  left_inverse : ∀ z ∈ closure e.source, G (F z) = z
  right_inverse : ∀ x ∈ closure Ω, F (G x) = x



end StrictHotSpots.Conformal
end
end ActualClosedConformal

section ClosedConformalData

noncomputable section
open Set Filter Metric
open scoped ContDiff NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)



def diskMap : OpenPartialHomeomorph Plane Plane where
  toFun := c.e
  invFun := c.e.symm
  source := DiskH10.disk
  target := Ω
  map_source' := fun _ hx => c.target_eq.subset (c.e.map_source (c.source_eq.symm.subset hx))
  map_target' := fun _ hy => c.source_eq.subset (c.e.map_target (c.target_eq.symm.subset hy))
  left_inv' := fun _ hx => c.e.left_inv (c.source_eq.symm ▸ hx)
  right_inv' := fun _ hy => c.e.right_inv (c.target_eq.symm ▸ hy)
  open_source := PlaneGreen.diskOpen
  open_target := c.target_eq ▸ c.e.open_target
  continuousOn_toFun := c.source_eq ▸ c.e.continuousOn
  continuousOn_invFun := c.e.continuousOn_symm.mono c.target_eq.symm.subset

lemma diskMap_smooth : ContDiffOn ℝ ∞ c.diskMap DiskH10.disk := by
  change ContDiffOn ℝ ∞ c.e DiskH10.disk
  exact c.source_eq ▸ c.smooth
lemma diskMap_deriv : ∀ x ∈ DiskH10.disk, HasFDerivAt c.diskMap (planeMul (c.d x)) x :=
  fun x hx => c.deriv x (c.source_eq.symm ▸ hx)
lemma continuous_closed : ContinuousOn c.F (closure DiskH10.disk) := c.lipschitz.continuous.continuousOn
lemma maps_closed : MapsTo c.F (closure DiskH10.disk) (closure Ω) := c.source_eq ▸ c.maps_closure
lemma diskMap_agrees : EqOn c.diskMap c.F DiskH10.disk := fun _ hx => c.agrees (c.source_eq.symm ▸ hx)

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedConformalData

section ClosedSmoothData



noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace Topology
namespace StrictHotSpots


def closedGradient (Ω : Set Plane) (u : Plane → ℝ) (x : Plane) : Plane :=
  (InnerProductSpace.toDual ℝ Plane).symm (fderivWithin ℝ u (closure Ω) x)

lemma closedGradient_eq {Ω : Set Plane} {u : Plane → ℝ} (ho : IsOpen Ω) {x : Plane}
    (hx : x ∈ Ω) : closedGradient Ω u x = gradient u x := by
  unfold closedGradient gradient
  rw [fderivWithin_of_mem_nhds (mem_of_superset (ho.mem_nhds hx) subset_closure)]

lemma closedGradient_continuous {Ω : Set Plane} {u : Plane → ℝ} (ho : IsOpen Ω)
    (hs : SmoothBoundary Ω) (hu : ContDiffOn ℝ ∞ u (closure Ω)) :
    ContinuousOn (closedGradient Ω u) (closure Ω) :=
  (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
    (hu.continuousOn_fderivWithin (hs.uniqueDiffOn_closure ho) (by simp))


lemma continuous_closure_memLp {Ω : Set Plane} {F : Type*} [NormedAddCommGroup F]
    {f : Plane → F} (ho : IsOpen Ω) (hb : Bornology.IsBounded Ω)
    (hf : ContinuousOn f (closure Ω)) : MemLp f 2 (volume.restrict Ω) := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hb.measure_lt_top.ne
  obtain ⟨C,hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn hf
  apply MemLp.of_bound ((hf.mono subset_closure).aestronglyMeasurable ho.measurableSet) C
  filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
  exact hC x (subset_closure hx)

end StrictHotSpots

namespace StrictHotSpots.Conformal.ClosedDiskChart
open Set Filter Metric MeasureTheory
open scoped ContDiff InnerProductSpace NNReal
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

def pullDatum (w : Plane → ℝ) : Plane → ℝ := w ∘ c.F

lemma pullDatum_continuous {w : Plane → ℝ} (hw : ContinuousOn w (closure Ω)) :
    ContinuousOn (c.pullDatum w) (closure disk) := hw.comp c.continuous_closed c.maps_closed

lemma pullDatum_eq_inner {w : Plane → ℝ} : EqOn (c.pullDatum w) (w ∘ c.diskMap) disk :=
  fun _ hx => congrArg w (c.diskMap_agrees hx).symm

lemma pullDatum_smooth {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w Ω) :
    ContDiffOn ℝ ∞ (c.pullDatum w) disk :=
  (hw.comp c.diskMap_smooth c.diskMap.mapsTo).congr c.pullDatum_eq_inner

lemma pullDatum_grad_norm {w : Plane → ℝ} (hw : DifferentiableOn ℝ w Ω)
    {x : Plane} (hx : x ∈ disk) :
    ‖gradient (c.pullDatum w) x‖ = ‖c.d x‖ * ‖gradient w (c.diskMap x)‖ := by
  have he : c.pullDatum w =ᶠ[nhds x] w ∘ c.diskMap :=
    eventually_of_mem (diskOpen.mem_nhds hx) (fun _ hy => c.pullDatum_eq_inner hy)
  have hg : gradient (c.pullDatum w) x = gradient (w ∘ c.diskMap) x := by
    unfold gradient
    rw [he.fderiv_eq]
  rw [hg]
  exact plane_norm_gradient_comp (c.diskMap_deriv x hx)
    ((hw _ (c.diskMap.map_source hx)).differentiableAt
      (c.diskMap.open_target.mem_nhds (c.diskMap.map_source hx)))

lemma pullDatum_bounded_gradient (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    ∃ B : ℝ≥0, ∀ x ∈ disk, ‖gradient (c.pullDatum w) x‖ ≤ B := by
  obtain ⟨C,hC⟩ := hb.isCompact_closure.exists_bound_of_continuousOn
    (closedGradient_continuous c.diskMap.open_target hs hw)
  let B : ℝ≥0 := ⟨c.bound * max C 0,mul_nonneg c.bound_pos.le (le_max_right _ _)⟩
  refine ⟨B,fun x hx => ?_⟩
  rw [c.pullDatum_grad_norm ((hw.mono subset_closure).differentiableOn (by simp)) hx]
  have ht := c.diskMap.map_source hx
  have hcg := hC (c.diskMap x) (subset_closure ht)
  rw [closedGradient_eq (Ω := Ω) (show IsOpen Ω from c.diskMap.open_target) ht] at hcg
  exact mul_le_mul (c.bounded_deriv x (c.source_eq.symm.subset hx))
    (hcg.trans (le_max_left _ _)) (norm_nonneg _) c.bound_pos.le

lemma pullDatum_H1 (hb : Bornology.IsBounded Ω) (hs : SmoothBoundary Ω)
    {w : Plane → ℝ} (hw : ContDiffOn ℝ ∞ w (closure Ω)) :
    HasH1Gradient disk (c.pullDatum w) (gradient (c.pullDatum w)) := by
  have hsm := c.pullDatum_smooth (hw.mono subset_closure)
  apply HasH1Gradient.of_contDiffOn diskOpen hsm
    (continuous_closure_memLp diskOpen diskBounded (c.pullDatum_continuous hw.continuousOn))
  let : IsFiniteMeasure (volume.restrict disk) := isFiniteMeasure_restrict.mpr diskBounded.measure_lt_top.ne
  obtain ⟨B,hB⟩ := c.pullDatum_bounded_gradient hb hs hw
  have hc : ContinuousOn (gradient (c.pullDatum w)) disk :=
    (InnerProductSpace.toDual ℝ Plane).symm.continuous.comp_continuousOn
      (hsm.continuousOn_fderiv_of_isOpen diskOpen (by simp))
  apply MemLp.of_bound (hc.aestronglyMeasurable diskOpen.measurableSet) B
  filter_upwards [ae_restrict_mem diskOpen.measurableSet] with x hx
  exact hB x hx

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ClosedSmoothData

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Hodge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualVectorSupport
noncomputable section
section ActualNeumannHilbertLayer
open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots


def meanZeroSubmodule {Ω : Set Plane} (hb : Bornology.IsBounded Ω) : Submodule ℝ (H1 Ω) :=
  (H1.mean hb).ker

abbrev N1 {Ω : Set Plane} (hb : Bornology.IsBounded Ω) := meanZeroSubmodule hb

instance N1.innerProductSpace {Ω : Set Plane} (hb : Bornology.IsBounded Ω) :
    InnerProductSpace ℝ (N1 hb) := (meanZeroSubmodule hb).innerProductSpace

namespace N1
variable {Ω : Set Plane} (hb : Bornology.IsBounded Ω)

local instance instNormedSpaceRealSubtypeH1AmbientMemSubmoduleH1 : NormedSpace ℝ (N1 hb) := (N1.innerProductSpace hb).toNormedSpace

def grad : N1 hb →L[ℝ] Lp Plane 2 (volume.restrict Ω) :=
  H1.grad.comp (meanZeroSubmodule hb).subtypeL

def energy : N1 hb →L[ℝ] N1 hb →L[ℝ] ℝ := by
  let a : Lp Plane 2 (volume.restrict Ω) →L[ℝ]
      Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ := innerSL ℝ
  let b : N1 hb →L[ℝ] Lp Plane 2 (volume.restrict Ω) →L[ℝ] ℝ := a.comp (grad hb)
  let c : Lp Plane 2 (volume.restrict Ω) →L[ℝ] N1 hb →L[ℝ] ℝ :=
    ContinuousLinearMap.flip (E := N1 hb) (F := Lp Plane 2 (volume.restrict Ω)) b
  let d : N1 hb →L[ℝ] N1 hb →L[ℝ] ℝ := c.comp (grad hb)
  exact ContinuousLinearMap.flip (E := N1 hb) (F := N1 hb) d

@[simp] lemma energy_apply (u v : N1 hb) :
    energy hb u v = inner ℝ (grad hb u) (grad hb v) := rfl

end N1
end StrictHotSpots

open Set MeasureTheory Filter
open scoped ContDiff InnerProductSpace
end ActualNeumannHilbertLayer


end

end ActualVectorSupport

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_GreenSolution
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section BoundaryPoissonTransport

noncomputable section
open Set MeasureTheory Filter Metric AddCircle
open scoped Topology InnerProductSpace ENNReal NNReal
namespace StrictHotSpots.PlaneGreen
open DiskH10
local notation "τ" => (2*Real.pi)

lemma angleBoundary_coe (s : AddCircle τ) :
    (angleBoundary s : Plane) = complexIso s.toCircle := by
  induction s using QuotientAddGroup.induction_on with
  | H θ =>
    change complexIso (Circle.exp θ : ℂ) = complexIso (AddCircle.toCircle (θ : AddCircle τ) : ℂ)
    congr 2
    rw [AddCircle.toCircle_apply_mk]
    congr 1
    field_simp

lemma angleBoundary_dist (s t : AddCircle τ) :
    dist (angleBoundary s) (angleBoundary t) = ‖(s.toCircle:ℂ)-(t.toCircle:ℂ)‖ := by
  rw [Subtype.dist_eq,dist_eq_norm,angleBoundary_coe,angleBoundary_coe,
    ← map_sub,LinearIsometryEquiv.norm_map]



def boundaryAngleData (f : C(Boundary,ℝ)) : C(AddCircle τ,ℂ) :=
  ⟨fun s => (f (angleBoundary s):ℂ),
    Complex.continuous_ofReal.comp (f.continuous.comp angleBoundary.continuous)⟩

@[simp] lemma boundaryAngleData_apply (f : C(Boundary,ℝ)) (s : AddCircle τ) :
    boundaryAngleData f s = (f (angleBoundary s):ℂ) := rfl

lemma boundaryAngleData_lipschitz (f : C(Boundary,ℝ)) {A : ℝ≥0}
    (hf : LipschitzWith A f) : Douglas.ChordLipschitz (A:ℝ) (boundaryAngleData f) := by
  intro s t
  simpa only [boundaryAngleData_apply,← Complex.ofReal_sub,Complex.norm_real,
    ← Real.norm_eq_abs,← dist_eq_norm,angleBoundary_dist] using hf.dist_le_mul (angleBoundary s) (angleBoundary t)


def boundaryPoissonH1 (f : C(Boundary,ℝ)) {A : ℝ≥0} (hf : LipschitzWith A f) : H1 disk :=
  (Douglas.lipschitz_planePoisson_hasH1Gradient (boundaryAngleData f) A.coe_nonneg
    (boundaryAngleData_lipschitz f hf)).toH1

end StrictHotSpots.PlaneGreen
end
end BoundaryPoissonTransport

section ActualBoundaryDatum

noncomputable section
open Set MeasureTheory Filter Metric
open scoped ContDiff InnerProductSpace NNReal
namespace StrictHotSpots.Conformal.ClosedDiskChart
open DiskH10 PlaneGreen
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

lemma boundary_mem_closed (s : Boundary) : (s : Plane) ∈ closure disk := by
  rw [disk, closure_ball (0 : Plane) (by norm_num : (1:ℝ) ≠ 0)]
  exact sphere_subset_closedBall (by simpa only [mem_sphere, dist_zero_right] using s.property)

def datumTrace (w : Plane → ℝ) (hw : ContinuousOn w (closure Ω)) : C(Boundary,ℝ) where
  toFun s := c.pullDatum w s
  continuous_toFun := (c.pullDatum_continuous hw).comp_continuous continuous_subtype_val
    boundary_mem_closed

end StrictHotSpots.Conformal.ClosedDiskChart
end
end ActualBoundaryDatum


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Pullback
attribute [-instance] _root_.OAI.StrictHotSpots.N1.innerProductSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualPotential

noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.Conformal
open DiskH10

lemma potentialMeasure_bounded {e : OpenPartialHomeomorph Plane Plane} {d : Plane → ℂ}
    {μ B : ℝ} (hμ : 0 ≤ μ) (hB : 0 ≤ B) (hd : ∀ x ∈ e.source, ‖d x‖ ≤ B) :
    potentialMeasure e d μ ≤ ENNReal.ofReal (μ*B^2) • volume.restrict e.source := by
  rw [potentialMeasure_density e d hμ, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left (sq_le_sq₀ (norm_nonneg _) hB |>.mpr (hd x hx)) hμ

namespace ClosedDiskChart
variable {Ω : Set Plane} (c : ClosedDiskChart Ω)

def potential : Measure Plane := potentialMeasure c.e c.d (firstPositiveNeumannValue Ω)
def densityBound : ℝ≥0∞ := ENNReal.ofReal (firstPositiveNeumannValue Ω*c.bound^2)

lemma density_bound (hμ : 0 ≤ firstPositiveNeumannValue Ω) :
    c.potential ≤ c.densityBound • volume.restrict disk := by
  have h := potentialMeasure_bounded hμ c.bound_pos.le c.bounded_deriv
  simpa only [potential,densityBound,c.source_eq] using h

lemma densityBound_ne_top : c.densityBound ≠ ∞ := ENNReal.ofReal_ne_top

end ClosedDiskChart
end StrictHotSpots.Conformal
end
end ActualPotential


end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Eigenfunction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ClosedEigenAlgebra

noncomputable section
open Set Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace StrictHotSpots




abbrev ClosedEigenJet (Ω : Set Plane) := ((closure Ω) → ℝ) × ((closure Ω) → Plane)

end StrictHotSpots
end
end ClosedEigenAlgebra

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section MultiplicityComplete

noncomputable section

section DiskMultiplicityLayer
open Set MeasureTheory Metric Function Module
open scoped Topology InnerProductSpace
namespace StrictHotSpots.CircleSigns
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def weightedMoment (F : ℂ → E) (w q : ℝ → ℝ)
    (hc : Continuous (fun θ => w θ*q θ))
    (hF : ContinuousOn F (closedBall 0 1)) : E →ₗ[ℝ] ℝ where
  toFun a := ∫ θ in (0:ℝ)..2*Real.pi, w θ*q θ*inner ℝ a (F (Circle.exp θ : ℂ))
  map_add' a b := by
    simp only [inner_add_left,mul_add]
    have hcont : Continuous (fun θ : ℝ => F (Circle.exp θ : ℂ)) :=
      hF.comp_continuous (by fun_prop) (fun θ => by simp [mem_closedBall,dist_zero_right])
    exact intervalIntegral.integral_add
      ((hc.mul (continuous_const.inner hcont)).intervalIntegrable _ _)
      ((hc.mul (continuous_const.inner hcont)).intervalIntegrable _ _)
  map_smul' c a := by
    simp only [inner_smul_left,conj_trivial,RingHom.id_apply,smul_eq_mul]
    simp_rw [show ∀ θ, w θ * q θ * (c * inner ℝ a (F (Circle.exp θ : ℂ))) =
      c * (w θ*q θ*inner ℝ a (F (Circle.exp θ : ℂ))) from fun _ => by ring]
    exact intervalIntegral.integral_const_mul _ _




end StrictHotSpots.CircleSigns
end DiskMultiplicityLayer
end
end MultiplicityComplete


end OAI
end


