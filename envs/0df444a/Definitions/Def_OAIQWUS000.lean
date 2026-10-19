-- Prove2me | Definitions.Def_OAIQWUS000
-- name    : OAIQWUS000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-19T01:46:52.562595+00:00
-- url     : https://prove2.me/theorems/8a8ba6c3-8a1d-4dfd-b56c-43e7123bf9c1
-- title:
--   OpenAI uniform sparsest cut split: definitions bundle (pivot families, rounded charts, kernels, cube cells, cut duality)
-- statement:
--   The definitions bundle of the split of OpenAI's proof that the Goemans–Linial semidefinite relaxation of uniform sparsest cut has integrality gaps of order $\sqrt{\log n}/(\log\log n)^3$ (`OAI.UniformSparsestCut.mainGap`). It holds OpenAI's Lean definitions from `lean/OAI/Combinatorics/SparsestCut` (OpenAI, *Near-square-root logarithmic integrality gaps for uniform sparsest cut*, OpenAI Math Release, September 24, 2026, result family 117, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies.
--
--   Among them: the pivot families `PivotFamily.PFamily` and their vectors and maps, the rounded charts and their vertex sets (`RoundedCharts`), the kernel constant `KernelApprox.cstar`, the source parameters and metric (`SourceParameters.p`, `SourceMetric.V`, `SourceMetric.err`, `SourceMetric.C₀`), the contraction constants `SourceContraction.H`, `SourceContraction.C` and `SourceContraction.weight`, the cube cell functions `ConcreteCells.function`, the uniform measure on the cube `CubePoincare.cube`, and the rotation path `GaussianPoincare.path`, `GaussianPoincare.tangent`.
--
--   The definitions of the published statement (`Capacity`, `OPT`, `glValue` and the rest) are not repeated: the bundle imports them from the published bundle `Def_UniformSparsestCut`. It imports no other bundle.
--
--   Modules: `GaussianTools`, `Directions`, `GaussianNonparallel`, `DirectionInterpolation`, `DirectionFamily`, `PivotFamily`, `ChartLinear`, `RoundedCharts`, `KernelApprox`, `CommonKernel`, `Profiles`, `ChartKernel`, `ChartAngles`, `TriangleRepair`, `ChartMetric`, `Parameters`, `Metric`, `Mollifier`, `ContractionBounds`, `ProductSlice`, `SliceIntegration`, `CellInterface`, `Smoothing`, `CoordinateSplit`, `EuclideanCells`, `ConcreteCells`, `GradientBudget`, `ContractionCore`, `GaussianPoincare`, `GaussianCDF`, `CubePoincare`, `FiniteDuality`, `CutSums`, `Semimetrics`, `CutDuality`, `VertexMeasure`, `WeightedMetric`, `LabelCount`, `Replication`, `Logarithms` (each `.lean` in `lean/OAI/Combinatorics/SparsestCut`).
-- source:
--   OpenAI, Near-square-root logarithmic integrality gaps for uniform sparsest cut, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 117; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/SparsestCut at commit adc7f12

import Mathlib
import Definitions.Def_UniformSparsestCut

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianTools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianTools

section Truncation
variable {n : ℕ}

noncomputable def truncate (n : ℕ) (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  {g | ‖g‖^2 ≤ 4*(n : ℝ)}.indicator f

end Truncation

end UniformSparsestCut.GaussianTools

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Directions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Directions
open GaussianTools MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators NNReal Topology

section ProductMeasures
variable {E : Type u1} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

noncomputable def badCount {S : ℕ} (A : Set E) (x : Fin S → E) : ℕ := by
  classical
  exact (Finset.univ.filter (fun s => x s ∈ A)).card

end ProductMeasures

section GaussianSelection
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => stdGaussian E

noncomputable def fourierSummand (v w : E) : E → ℝ :=
  truncate m (fun g => inner ℝ g v * Real.sin (inner ℝ g w))
noncomputable def covarianceSummand (v : E) : E → ℝ :=
  truncate m (fun g => (inner ℝ v g)^2)

def normBad : Set (Fin N → E) :=
  {x | ∃ i, ‖x i‖^2 < (m : ℝ)/4 ∨ 4*(m : ℝ) < ‖x i‖^2}
noncomputable def fourierBad (u : ℝ) (v w : E) : Set (Fin N → E) :=
  {x | u < |(∑ i, fourierSummand v w (x i))/(N : ℝ) - ∫ g, fourierSummand v w g ∂μ|}
noncomputable def covarianceBad (v : E) : Set (Fin N → E) :=
  {x | (1/8 : ℝ) < |(∑ i, covarianceSummand v (x i))/(N : ℝ) - ∫ g, covarianceSummand v g ∂μ|}
def projectionBad (q : ℝ) (v : E) : Set (Fin N → E) :=
  {x | ∃ i, q < |inner ℝ v (x i)|}

noncomputable def chartBad (V W : Finset E) (u : ℝ) : Set (Fin N → E) :=
  normBad ∪ {x | ∃ z : V × W, x ∈ fourierBad u z.1 z.2} ∪
    {x | ∃ v : V, x ∈ covarianceBad v}

end GaussianSelection

end UniformSparsestCut.Directions

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianNonparallel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianNonparallel

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def cross (i j : Fin m) (x y : E) : ℝ := x i * y j - x j * y i

end UniformSparsestCut.GaussianNonparallel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.DirectionInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionInterpolation
open GaussianTools MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
noncomputable def empiricalSin (g : Fin N → E) (w : E) : E :=
  (N : ℝ)⁻¹ • ∑ i, Real.sin (inner ℝ (g i) w) • g i
noncomputable def empiricalCov (g : Fin N → E) (v : E) : ℝ :=
  (∑ i, (inner ℝ v (g i))^2)/(N : ℝ)

end UniformSparsestCut.DirectionInterpolation

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.DirectionFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.DirectionFamily
open Directions DirectionInterpolation GaussianTools
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

variable {m N S : ℕ}

structure Family (m : ℕ) where
  g : Fin (m^3) → Fin (m^6) → EuclideanSpace ℝ (Fin m)
  norms : ∀ s i, Real.sqrt m/2 ≤ ‖g s i‖ ∧ ‖g s i‖ ≤ 2*Real.sqrt m
  nonparallel : ∀ s a b, a ≠ b → ∀ t : ℝ, g s a ≠ t • g s b
  covariance : ∀ s v, ‖v‖ = 1 → 1/2 ≤ empiricalCov (g s) v ∧ empiricalCov (g s) v ≤ 2
  fourier : ∀ s w, ‖w‖ ≤ (m : ℝ)^42 →
    ‖empiricalSin (g s) w - Real.exp (-‖w‖^2/2) • w‖ ≤ 2/Real.sqrt m
  good : ∀ v, ‖v‖ = 1 →
    (badCount (projectionBad (11*Real.sqrt (Real.log m)) v) g : ℝ) ≤ ((m^3 : ℕ) : ℝ)/2

end UniformSparsestCut.DirectionFamily

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.PivotFamily
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.PivotFamily
open UniformSparsestCut.GaussianTools UniformSparsestCut.Directions
open UniformSparsestCut.DirectionFamily
open UniformSparsestCut.DirectionInterpolation
open scoped NNReal

variable {m : ℕ}

structure PFamily (m : ℕ) extends Family m where
  pivot : ∀ s i j, 1/(m:ℝ)^30 < |g s i j|

end UniformSparsestCut.PivotFamily

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartLinear
variable {E : Type u1} {F : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F]

lemma gram_injective (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : Function.Injective (J.adjoint.comp J) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  have hh : ‖J x‖^2 = 0 := by
    have := congrArg (fun z => inner ℝ x z) hx
    change inner ℝ x (J.adjoint (J x)) = inner ℝ x 0 at this
    simpa only [J.adjoint_inner_right, real_inner_self_eq_norm_sq, inner_zero_right] using this
  have hn : ‖x‖^2 = 0 := by nlinarith [hl x, sq_nonneg ‖x‖]
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hn)

noncomputable def gramEquiv (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : E ≃L[ℝ] E :=
  ContinuousLinearEquiv.ofBijective (J.adjoint.comp J)
    (LinearMap.ker_eq_bot.mpr (gram_injective J ha hl))
    (LinearMap.range_eq_top.mpr (LinearMap.injective_iff_surjective.mp
      (gram_injective J ha hl)))

noncomputable def pseudoInverse (J : E →L[ℝ] F) {a : ℝ} (ha : 0 < a)
    (hl : ∀ x, a * ‖x‖^2 ≤ ‖J x‖^2) : F →L[ℝ] E :=
  (gramEquiv J ha hl).symm.toContinuousLinearMap.comp J.adjoint

end UniformSparsestCut.ChartLinear

namespace UniformSparsestCut.FrameCharts
open scoped RealInnerProductSpace BigOperators
variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def chart (u : Fin N → E) : E →L[ℝ] F :=
  (EuclideanSpace.equiv (Fin N) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => innerSL ℝ (u i)))

@[simp] lemma chart_apply (u : Fin N → E) (x : E) (i : Fin N) :
    chart u x i = inner ℝ (u i) x := rfl

lemma chart_energy (u : Fin N → E) (x : E) :
    ‖chart u x‖^2 = ∑ i, (inner ℝ (u i) x)^2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [chart_apply, Real.norm_eq_abs, sq_abs]

lemma extend_covariance (g : Fin N → E) (hN : 0 < N) (a b : ℝ)
    (hc : ∀ v : E, ‖v‖ = 1 → a ≤ (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ∧
      (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ≤ b) (x : E) :
    a*(N : ℝ)*‖x‖^2 ≤ ∑ i, (inner ℝ (g i) x)^2 ∧
      (∑ i, (inner ℝ (g i) x)^2) ≤ b*(N : ℝ)*‖x‖^2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hx : x = 0
  · simp [hx]
  have hx0 : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let v : E := ‖x‖⁻¹ • x
  have hv : ‖v‖ = 1 := by simp [v, norm_smul, hx0.ne']
  have he : (∑ i, (inner ℝ v (g i))^2) = ‖x‖⁻¹^2 * ∑ i, (inner ℝ (g i) x)^2 := by
    simp only [v, real_inner_smul_left, mul_pow, Finset.mul_sum]
    congr 1
    funext i
    rw [real_inner_comm]
  obtain ⟨hl,hu⟩ := hc v hv
  rw [div_le_iff₀ hn] at hu
  rw [le_div_iff₀ hn] at hl
  rw [he] at hl hu
  have hsq : 0 ≤ ‖x‖^2 := sq_nonneg _
  constructor
  · have h := mul_le_mul_of_nonneg_right hl hsq
    have hz : ‖x‖⁻¹^2*‖x‖^2 = 1 := by field_simp
    calc
      _ ≤ _ := h
      _ = _ := by rw [mul_right_comm, hz, one_mul]
  · have h := mul_le_mul_of_nonneg_right hu hsq
    have hz : ‖x‖⁻¹^2*‖x‖^2 = 1 := by field_simp
    calc
      _ = _ := by rw [mul_right_comm, hz, one_mul]
      _ ≤ _ := h

lemma normalized_energy (g : Fin N → E) (_hm : 0 < m) (x : E) :
    ‖chart (fun i => (Real.sqrt m)⁻¹ • g i) x‖^2 =
      (∑ i, (inner ℝ (g i) x)^2)/(m : ℝ) := by
  rw [chart_energy]
  simp only [real_inner_smul_left, mul_pow, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg m), div_eq_inv_mul]

lemma normalized_bounds (g : Fin N → E) (hm : 0 < m) (hN : 0 < N)
    (hc : ∀ v : E, ‖v‖ = 1 → 1/2 ≤ (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ∧
      (∑ i, (inner ℝ v (g i))^2)/(N : ℝ) ≤ 2) (x : E) :
    ((N : ℝ)/(2*m))*‖x‖^2 ≤ ‖chart (fun i => (Real.sqrt m)⁻¹ • g i) x‖^2 ∧
    ‖chart (fun i => (Real.sqrt m)⁻¹ • g i) x‖^2 ≤ ((2*N : ℝ)/m)*‖x‖^2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  obtain ⟨hl,hu⟩ := extend_covariance g hN (1/2) 2 hc x
  rw [normalized_energy g hm x]
  constructor
  · apply (le_div_iff₀ hm0).mpr
    calc
      _ = (1/2:ℝ)*N*‖x‖^2 := by field_simp
      _ ≤ _ := hl
  · apply (div_le_iff₀ hm0).mpr
    calc
      _ ≤ (2:ℝ)*N*‖x‖^2 := hu
      _ = _ := by field_simp

lemma normalized_norms (g : Fin N → E) (hm : 0 < m)
    (hg : ∀ i, Real.sqrt m/2 ≤ ‖g i‖ ∧ ‖g i‖ ≤ 2*Real.sqrt m) (i : Fin N) :
    1/2 ≤ ‖(Real.sqrt m)⁻¹ • g i‖ ∧ ‖(Real.sqrt m)⁻¹ • g i‖ ≤ 2 := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs), ← div_eq_inv_mul]
  constructor
  · exact (le_div_iff₀ hs).mpr (by linarith [(hg i).1])
  · exact (div_le_iff₀ hs).mpr (hg i).2

end UniformSparsestCut.FrameCharts

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.RoundedCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceCharts
open scoped BigOperators RealInnerProductSpace
open Filter Set
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin (m^6))
def u (s : Fin (m^3)) (i : Fin (m^6)) : E := (Real.sqrt m)⁻¹ • f.g s i
def lower (m : ℕ) : ℝ := (m:ℝ)^6/(2*m)
include hm
lemma lower_pos : 0<lower m := by unfold lower; positivity
lemma energy (s : Fin (m^3)) (x : E) : lower m*‖x‖^2≤‖FrameCharts.chart (u f s) x‖^2 := by
  have hc (v : E) (hv : ‖v‖=1) := f.covariance s v hv
  have h := (FrameCharts.normalized_bounds (f.g s) hm (pow_pos hm _) (by
    intro v hv
    simpa only [DirectionInterpolation.empiricalCov,real_inner_comm,div_eq_mul_inv,mul_comm] using hc v hv) x).1
  change (m:ℝ)^6/(2*m)*‖x‖^2≤‖FrameCharts.chart (fun i => (Real.sqrt m)⁻¹ • f.g s i) x‖^2
  simpa only [Nat.cast_pow] using h
def B (s : Fin (m^3)) : F →L[ℝ] E :=
  ChartLinear.pseudoInverse (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s)
lemma u_norm (s : Fin (m^3)) (i : Fin (m^6)) : 1/2≤‖u f s i‖ ∧ ‖u f s i‖≤2 :=
  FrameCharts.normalized_norms (f.g s) hm (f.norms s) i
lemma u_pivot (s : Fin (m^3)) (i : Fin (m^6)) (j : Fin m ) :
    1/((m:ℝ)^30*Real.sqrt m) < |u f s i j| := by
  have hq : 0<Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  change _ < |(Real.sqrt m)⁻¹*(f.g s i j)|
  rw [abs_mul,abs_of_pos (inv_pos.mpr hq)]
  simpa only [one_div,mul_inv,mul_comm] using mul_lt_mul_of_pos_left (f.pivot s i j) (inv_pos.mpr hq)
end
end UniformSparsestCut.SourceCharts

namespace UniformSparsestCut.RoundedCharts
open MeasureTheory Set Filter
open scoped Topology BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def cube (R : ℝ) : Set E := {θ | ∀ j, |θ j| < R}

def regular (u : Fin N → E) (τ : ℝ) (θ : E) : Prop :=
  ∀ i (k : ℤ), inner ℝ (u i) θ ≠ (k:ℝ)*τ

def integerLabel (u : Fin N → E) (τ : ℝ) (θ : E) (i : Fin N) : ℤ :=
  ⌊inner ℝ (u i) θ/τ⌋

def rounded (u : Fin N → E) (τ : ℝ) (θ : E) : F :=
  WithLp.toLp 2 (fun i => τ*(integerLabel u τ θ i : ℝ))

def Vertex (u : Fin S → Fin N → E) (τ : ℝ) :=
  {p : Fin S × (Fin N → ℤ) // ∃ θ ∈ cube 2, regular (u p.1) τ θ ∧ integerLabel (u p.1) τ θ = p.2}

def coordinate (u : Fin S → Fin N → E) (τ : ℝ) (v : Vertex u τ) : F :=
  WithLp.toLp 2 (fun i => τ*(v.val.2 i : ℝ))

lemma cube_norm {R : ℝ} (hR : 0 ≤ R) {θ : E} (hθ : θ ∈ cube R) :
    ‖θ‖ ≤ R*Real.sqrt m := by
  have hs : ‖θ‖^2 ≤ (m:ℝ)*R^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, R^2 := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθ j).le _
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg m)
  have hp : 0 ≤ R*Real.sqrt m := mul_nonneg hR (Real.sqrt_nonneg _)
  have he : (R*Real.sqrt m)^2 = (m:ℝ)*R^2 := by rw [mul_pow,hroot]; ring
  nlinarith [norm_nonneg θ]

lemma integerLabel_bound (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (hu : ∀ i, ‖u i‖ ≤ 2)
    {θ : E} (hθ : θ ∈ cube 2) (i : Fin N) :
    |(integerLabel u τ θ i : ℝ)| ≤ 4*Real.sqrt m/τ+1 := by
  have hn := cube_norm (by norm_num : (0:ℝ) ≤ 2) hθ
  have hh : |inner ℝ (u i) θ| ≤ 4*Real.sqrt m := by
    calc
      _ ≤ ‖u i‖*‖θ‖ := abs_real_inner_le_norm _ _
      _ ≤ 2*(2*Real.sqrt m) := mul_le_mul (hu i) hn (norm_nonneg θ) (by norm_num)
      _ = _ := by ring
  have hf := Int.floor_le (inner ℝ (u i) θ/τ)
  have hfl := Int.lt_floor_add_one (inner ℝ (u i) θ/τ)
  have hab : |inner ℝ (u i) θ/τ| ≤ 4*Real.sqrt m/τ := by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right hh hτ.le
  change |(⌊inner ℝ (u i) θ/τ⌋:ℝ)| ≤ _
  rw [abs_le] at hab ⊢
  constructor <;> linarith

lemma vertex_finite (u : Fin S → Fin N → E) {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ s i, ‖u s i‖ ≤ 2) : Finite (Vertex u τ) := by
  let B : ℤ := ⌈4*Real.sqrt m/τ+1⌉
  let f : Vertex u τ → Fin S × (Fin N → ↥(Finset.Icc (-B) B)) := fun v =>
    (v.val.1, fun i => ⟨v.val.2 i, by
      obtain ⟨θ,hθ,hr,hlabel⟩ := v.property
      have hb := integerLabel_bound (u v.val.1) hτ (hu v.val.1) hθ i
      have hB := Int.le_ceil (4*Real.sqrt m/τ+1)
      have hv : |(v.val.2 i:ℝ)| ≤ (B:ℝ) := by rw [← hlabel]; exact hb.trans hB
      have hlo : -B ≤ v.val.2 i := by exact_mod_cast (abs_le.mp hv).1
      have hhi : v.val.2 i ≤ B := by exact_mod_cast (abs_le.mp hv).2
      exact Finset.mem_Icc.mpr ⟨hlo,hhi⟩⟩)
  apply Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Fin S × (Fin N → ↥(Finset.Icc (-B) B)) => z.1) h
  · funext i
    exact congrArg (fun z : Fin S × (Fin N → ↥(Finset.Icc (-B) B)) => (z.2 i).val) h

end UniformSparsestCut.RoundedCharts

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.KernelApprox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.KernelApprox

def profile (t : ℝ) : ℝ := 1 - Real.exp (-1/(2*t^2))

noncomputable def cstar : ℝ := 2 * ∫ t in Ioi (0 : ℝ), profile t

def scaled (r t : ℝ) : ℝ := 1-Real.exp (-r^2/(2*t^2))

end UniformSparsestCut.KernelApprox

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CommonKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CommonKernel
open MeasureTheory Set
open scoped RealInnerProductSpace BigOperators Matrix

variable {ι : Type u1} [Fintype ι]

def circle (t q : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 ![Real.cos t-q*Real.sin t, Real.sin t+q*Real.cos t]

variable {E : Type u2} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {κ : Type u3} [Fintype κ]

def gram (g : κ → E) (θ : ι → E) (α : ι → κ → ℝ) (M ε a b : ℝ) : Matrix ι ι ℝ :=
  fun v w => M*(∫ σ in a..b, Real.exp (-‖θ v-θ w‖^2/(2*σ^2))) +
    ε*∑ k, ∫ σ in a..b,
      inner ℝ (circle (inner ℝ (g k) (θ v)/σ) (α v k))
        (circle (inner ℝ (g k) (θ w)/σ) (α w k)) / σ

end UniformSparsestCut.CommonKernel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Profiles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Profile
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} [Fintype ι]

def pairing (g : ι → E) (q ε σ : ℝ) (θ η : E) (α β : ι → ℝ) : ℝ :=
  q*Real.exp (-‖η-θ‖^2/(2*σ^2)) + ε/σ*(∑ i, (
    (1+α i*β i)*Real.cos (inner ℝ (g i) (η-θ)/σ) +
      (α i-β i)*Real.sin (inner ℝ (g i) (η-θ)/σ)))

def differential (g : ι → E) (q ε σ : ℝ) (θ η v : E)
    (α β δ : ι → ℝ) : ℝ :=
  q/σ*(inner ℝ ((σ⁻¹:ℝ) • (η-θ)) v)*Real.exp (-‖η-θ‖^2/(2*σ^2)) +
    ε/σ*(∑ i, (δ i*(β i*Real.cos (inner ℝ (g i) (η-θ)/σ)+Real.sin (inner ℝ (g i) (η-θ)/σ)) +
      (inner ℝ (g i) v/σ)*((1+α i*β i)*Real.sin (inner ℝ (g i) (η-θ)/σ)-
        (α i-β i)*Real.cos (inner ℝ (g i) (η-θ)/σ))))

end UniformSparsestCut.Profile

namespace UniformSparsestCut.Profile
variable {E : Type u6} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u7} [Fintype ι]

def kernel (g : ι → E) (q ε a b : ℝ) (θ η : E) (α β : ι → ℝ) : ℝ :=
  ∫ σ in a..b, pairing g q ε σ θ η α β

end UniformSparsestCut.Profile

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartKernel
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "F" => EuclideanSpace ℝ (Fin N)

def residual (J : E →L[ℝ] F) (B : F →L[ℝ] E) : F →L[ℝ] F :=
  ContinuousLinearMap.id ℝ F-J.comp B

def alpha (g : Fin S → Fin N → E) (B : Fin S → F →L[ℝ] E)
    (q k ε : ℝ) (s : Fin S) (x : F) (j : Fin S × Fin N) : ℝ :=
  if j.1=s then k/ε*(x j.2-inner ℝ (g j.1 j.2) (B s x)/q) else 0

end UniformSparsestCut.ChartKernel

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ChartAngles
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type u2} {κ : Type u3} [Fintype ι] [Fintype κ]

def distance (g : κ → E) (q ε a b : ℝ) (θ η : E) (α β : κ → ℝ) : ℝ :=
  Profile.kernel g q ε a b θ θ α α+Profile.kernel g q ε a b η η β β-
    2*Profile.kernel g q ε a b θ η α β

end UniformSparsestCut.ChartAngles

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.TriangleRepair
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.TriangleRepair
variable {ι : Type u1} [Fintype ι]

section Charts

variable {κ : Type u3} {H : Type u4} [Fintype κ] [DecidableEq κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

noncomputable def chartKernel (c : ι → κ) (h : ι → H) (l : ℝ) : Matrix ι ι ℝ :=
  Matrix.of fun i j => if c i = c j then Real.exp (-‖h i - h j‖ ^ 2 / l) else 0

noncomputable def cappedDistance (c : ι → κ) (h : ι → H) (r : ℝ) (i j : ι) : ℝ :=
  if c i = c j then min r (‖h i - h j‖ ^ 2) else r

def ChartTriangle (c : ι → κ) (h : ι → H) : Prop :=
  ∀ i j k, c i = c j → c j = c k →
    ‖h i - h k‖ ^ 2 ≤ ‖h i - h j‖ ^ 2 + ‖h j - h k‖ ^ 2

def IsRepairGram (c : ι → κ) (h : ι → H) (r : ℝ)
    (q : ι → EuclideanSpace ℝ ι) : Prop :=
  ∀ i j, ⟪q i, q j⟫_ℝ = 4 * ∫ l in (0 : ℝ)..r, chartKernel c h l i j

noncomputable def angleIntegrand (c : ι → κ) (h : ι → H) (i j z : ι) (l : ℝ) : ℝ :=
  1 - chartKernel c h l i z - chartKernel c h l j z + chartKernel c h l i j

end Charts

end UniformSparsestCut.TriangleRepair

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ChartMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GramMetric
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {V : Type u6} [Fintype V]

def localCost (N S : ℕ) (q k ε a b R γ : ℝ) : ℝ :=
  2*((k+q*γ*(4*k)+ε*((S:ℝ)*N)*(9*k/ε)*(k/ε*R))*Real.log (b/a)+
    (ε*((S:ℝ)*N)*(2*q)*(4*k)*(1+(k/ε*R)^2+2*(k/ε*R)))/a)

def macroCost (N S : ℕ) (q k ε a b R T Rpos : ℝ) : ℝ :=
  q*(2*a+(2*T)^2/b)+4*ε*((S:ℝ)*N)*Real.log (b/a)+
    4*(ε*((S:ℝ)*N)*((k/ε*R)^2+2*(k/ε*R))*Real.log (b/a))+2*KernelApprox.cstar*q*Rpos

end
end UniformSparsestCut.GramMetric

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Parameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceParameters
open Filter
noncomputable section

def p (x : ℝ) (n : ℕ) : ℝ := 1/x^n
lemma p_pos {x : ℝ} (hx : 0<x) (n : ℕ) : 0<p x n := by unfold p; positivity
end
end UniformSparsestCut.SourceParameters

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Metric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m)
abbrev V := RoundedCharts.Vertex (u f) (p m 2000)
noncomputable instance vertexFintype [NeZero m] : Fintype (V f) := by
  letI := RoundedCharts.vertex_finite (u f) (τ := p m 2000) (p_pos (by exact_mod_cast NeZero.pos m) _) (fun s i => (u_norm f (NeZero.pos m) s i).2)
  exact Fintype.ofFinite _
def L : ℝ := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
  (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)
def err : ℝ := GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
  (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0
end
end UniformSparsestCut.SourceMetric

namespace UniformSparsestCut.SourceMetric
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts
noncomputable section
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]
local notation "E" => EuclideanSpace ℝ (Fin m)
def C₀ : ℝ := 9+2*KernelApprox.cstar
def vertex (s : Fin (m^3)) (θ : E) (hθ : θ∈RoundedCharts.cube 2)
    (hs : RoundedCharts.regular (u f s) (p m 2000) θ) : V f :=
  ⟨(s,RoundedCharts.integerLabel (u f s) (p m 2000) θ),θ,hθ,hs,rfl⟩
end
end UniformSparsestCut.SourceMetric

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Mollifier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductMollifier

def bump : ContDiffBump (0:ℝ) := ⟨1/2,1,by norm_num,by norm_num⟩
def rho : ℝ → ℝ := bump.normed volume

def density (ell : ℝ) (x : ℝ) : ℝ := ell⁻¹*rho (x/ell)

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
def coordinate (i : Fin m) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap
@[simp] lemma coordinate_apply (i : Fin m) (x : E) : coordinate i x = x i := rfl

def kernel (φ : ℝ → ℝ) (x : E) : ℝ := ∏ i, φ (x i)

end UniformSparsestCut.ProductMollifier

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ContractionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.KernelGeometry
open MeasureTheory Set ProductMollifier
open scoped BigOperators Topology
noncomputable section
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
def κ (lam : ℝ) : E → ℝ := kernel (density lam)
def L (lam : ℝ) : ℝ := lam⁻¹*(∫ t, |deriv rho t|)
end
end UniformSparsestCut.KernelGeometry

namespace UniformSparsestCut.SourceContraction
open scoped BigOperators RealInnerProductSpace
open SourceParameters SourceCharts SourceMetric
open MeasureTheory
noncomputable section
def H : ℝ := ∫ t, |deriv ProductMollifier.rho t|
def weight (m : ℕ) : ℝ := Real.sqrt m*(Real.log m)^2*Real.sqrt (Real.log m)
def C : ℝ := 2*(KernelApprox.cstar+C₀)+Real.pi*(1100000000+C₀*H)+1
end
end UniformSparsestCut.SourceContraction

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ProductSlice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {K : Type u3} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype K] [DecidableEq I] [DecidableEq K]

def form (B : Z →L[ℝ] ℝ) : (ℝ × Z) →L[ℝ] ℝ :=
  ContinuousLinearMap.fst ℝ ℝ Z-B.comp (ContinuousLinearMap.snd ℝ ℝ Z)
omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] in
@[simp] lemma form_apply (B : Z →L[ℝ] ℝ) (x : ℝ × Z) : form B x=x.1-B x.2 := rfl

def cell (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → ℝ) (x : ℝ × Z) : ℝ :=
  F (Finset.univ.filter (fun p => form (B p.1) x+q p.1 p.2<0))

def law (ψ : Z → ℝ) (ν : Measure Z) : Measure Z := ν.withDensity (fun z => ENNReal.ofReal (ψ z))
end
end UniformSparsestCut.ProductSlice

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.SliceIntegration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {K : Type u3} {A : Type u4} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype K] [Fintype A] [DecidableEq I] [DecidableEq K]

def jump (B : I → Z →L[ℝ] ℝ) (q : I → K → ℝ) (F : Finset (I × K) → A → ℝ)
    (θ : ℝ × Z) (i : I) (k : K) (z : Z) (α : A) : ℝ :=
  F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 ≤ form (B i) θ+B i z+q i k)) α-
  F (Finset.univ.filter (fun p => form (B p.1) θ+B p.1 z+q p.1 p.2 < form (B i) θ+B i z+q i k)) α

end
end UniformSparsestCut.ProductSlice

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CellInterface
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CellInterface
open Filter Set
open scoped Topology BigOperators
noncomputable section
variable {E : Type u3} {I : Type u4} {A : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]

def regular (ell : I → E →L[ℝ] ℝ) (τ : ℝ) (x : E) : Prop :=
  ∀ i (k : ℤ), ell i x≠(k:ℝ)*τ

def label (ell : I → E →L[ℝ] ℝ) (τ : ℝ) (x : E) : I → ℤ := fun i => ⌊ell i x/τ⌋

def LabelVertex (ell : I → E →L[ℝ] ℝ) (τ : ℝ) (U : Set E) :=
  {l : I → ℤ // ∃ x∈U, regular ell τ x ∧ label ell τ x=l}

def vertex (ell : I → E →L[ℝ] ℝ) (τ : ℝ) {U : Set E} (x : E) (hx : x∈U)
    (hr : regular ell τ x) : LabelVertex ell τ U := ⟨label ell τ x,x,hx,hr,rfl⟩

def pattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ) (x : E) : Finset (I × s) :=
  Finset.univ.filter (fun p => (ell p.1 x-(p.2.val:ℝ)*τ)/pivot p.1<0)
def weakPattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ) (x : E) : Finset (I × s) :=
  Finset.univ.filter (fun p => (ell p.1 x-(p.2.val:ℝ)*τ)/pivot p.1≤0)

def extension (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ)
    (U : Set E) (F : LabelVertex ell τ U → A → ℝ) (P : Finset (I × s)) : A → ℝ := by
  classical
  exact if h : ∃ x : E, ∃ hx : x∈U, ∃ hr : regular ell τ x, pattern ell pivot τ s x=P then
    F (vertex ell τ h.choose (h.choose_spec.choose) (h.choose_spec.choose_spec.choose))
  else fun _ => 0

end
end UniformSparsestCut.CellInterface

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ProductSlice
open MeasureTheory Set CellInterface
open scoped BigOperators
noncomputable section
variable {Z : Type u1} {I : Type u2} {A : Type u3} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure]
  [Fintype I] [Fintype A] [DecidableEq I]

def ell (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (i : I) : (ℝ × Z) →L[ℝ] ℝ :=
  pivot i • form (B i)
omit [FiniteDimensional ℝ Z] [MeasureSpace Z] [BorelSpace Z] [(volume : Measure Z).IsAddHaarMeasure] [Fintype I] [DecidableEq I] in
@[simp] lemma ell_apply (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (i : I) (x : ℝ × Z) :
    ell B pivot i x=pivot i*(x.1-B i x.2) := rfl

def eventPoint (B : I → Z →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ)
    (θ : ℝ × Z) (i : I) (k : ℤ) (z : Z) : ℝ × Z :=
  θ-(form (B i) θ+B i z-(k:ℝ)*τ/pivot i,z)

end
end UniformSparsestCut.ProductSlice

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CoordinateSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CoordinateSplit
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def splitLinear : E ≃ₗ[ℝ] ℝ × Z where
  toFun x := (x 0, WithLp.toLp 2 (fun j => x j.succ))
  invFun p := WithLp.toLp 2 (Fin.cons p.1 (fun j => p.2 j))
  left_inv x := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> simp
  right_inv p := by ext <;> simp
  map_add' x y := by ext <;> simp
  map_smul' t x := by ext <;> simp

def split : E ≃L[ℝ] ℝ × Z := splitLinear.toContinuousLinearEquiv
@[simp] lemma split_apply (x : E) : split x=(x 0,WithLp.toLp 2 (fun j => x j.succ)) := rfl
@[simp] lemma split_symm_apply (p : ℝ × Z) : split.symm p=WithLp.toLp 2 (Fin.cons p.1 (fun j => p.2 j)) := rfl

def splitMeasurable : E ≃ᵐ ℝ × Z := split.toHomeomorph.toMeasurableEquiv

def rest (u : E) : Z →L[ℝ] ℝ :=
  (InnerProductSpace.toDual ℝ E u).comp
    (split.symm.toContinuousLinearMap.comp (ContinuousLinearMap.inr ℝ ℝ Z))
def slope (u : E) : Z →L[ℝ] ℝ := -(u 0)⁻¹ • rest u
lemma rest_apply (u : E) (z : Z) : rest u z=∑ j, u j.succ*z j := by
  simp [rest,PiLp.inner_apply,Fin.sum_univ_succ,mul_comm]
lemma inner_formula (u x : E) : inner ℝ u x=u 0*(split x).1+rest u (split x).2 := by
  simp [rest_apply,PiLp.inner_apply,Fin.sum_univ_succ]
  congr 1
  · ring
  · apply Finset.sum_congr rfl; intro j _; ring
lemma normalized_form (u : E) (hu : u 0≠0) (x : E) :
    inner ℝ u x/(u 0)=(split x).1-slope u (split x).2 := by
  rw [inner_formula]
  simp only [slope,_root_.smul_apply,smul_eq_mul]
  field_simp
  ring
end UniformSparsestCut.CoordinateSplit

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.EuclideanCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.EuclideanCells
open MeasureTheory Set ProductSlice CellInterface CoordinateSplit
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {I : Type u1} {A : Type u2} [Fintype I] [Fintype A] [DecidableEq I]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def B (u : I → E) : I → Z →L[ℝ] ℝ := fun i => slope (u i)
def pivot (u : I → E) (i : I) : ℝ := u i 0

def values (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) : Finset (I × s) → A → ℝ :=
  extension (ell (B u) (pivot u)) (pivot u) τ s U F

def chartFunction (u : I → E) (τ : ℝ) (s : Finset ℤ) (U : Set (ℝ × Z))
    (F : LabelVertex (ell (B u) (pivot u)) τ U → A → ℝ) (a : A) : E → ℝ :=
  (cell (B u) (fun i (k : s) => -((k:ℤ)*τ/pivot u i)) (fun P => values u τ s U F P a)) ∘ split

end
end UniformSparsestCut.EuclideanCells

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ConcreteCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ConcreteCells
open MeasureTheory Set Filter CoordinateSplit EuclideanCells
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))
local notation "Z" => EuclideanSpace ℝ (Fin m)

def domain : Set (ℝ × Z) := split.symm ⁻¹' RoundedCharts.cube 2

def labels (τ : ℝ) : Finset ℤ := Finset.Icc (-⌈4*Real.sqrt (m+1:ℕ)/τ+1⌉) ⌈4*Real.sqrt (m+1:ℕ)/τ+1⌉

lemma ell_eq (u : Fin N → E) (hu : ∀ i, u i 0≠0) (x : ℝ × Z) (i : Fin N) :
    ProductSlice.ell (B u) (pivot u) i x=inner ℝ (u i) (split.symm x) := by
  have h := normalized_form (u i) (hu i) (split.symm x)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at h
  change pivot u i*ProductSlice.form (B u i) x=_
  change u i 0*(x.1-slope (u i) x.2)=_
  rw [← h]
  field_simp [hu i]

lemma regular_eq (u : Fin N → E) (hu : ∀ i, u i 0≠0) (τ : ℝ) (x : ℝ × Z) :
    CellInterface.regular (ProductSlice.ell (B u) (pivot u)) τ x ↔
      RoundedCharts.regular u τ (split.symm x) := by
  simp only [CellInterface.regular,RoundedCharts.regular,ell_eq u hu]
lemma label_eq (u : Fin N → E) (hu : ∀ i, u i 0≠0) (τ : ℝ) (x : ℝ × Z) :
    CellInterface.label (ProductSlice.ell (B u) (pivot u)) τ x =
      RoundedCharts.integerLabel u τ (split.symm x) := by
  ext i
  simp only [CellInterface.label,RoundedCharts.integerLabel,ell_eq u hu]

def mapVertex (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ) (s : Fin S)
    (v : CellInterface.LabelVertex (ProductSlice.ell (B (u s)) (pivot (u s))) τ domain) : RoundedCharts.Vertex u τ :=
  ⟨(s,v.val),by
    obtain ⟨x,hx,hr,hl⟩ := v.property
    refine ⟨split.symm x,hx,(regular_eq (u s) (hu s) τ x).mp hr,?_⟩
    exact (label_eq (u s) (hu s) τ x).symm.trans hl⟩

def function (u : Fin S → Fin N → E) (hu : ∀ s i, u s i 0≠0) (τ : ℝ)
    (F : RoundedCharts.Vertex u τ → A → ℝ) (s : Fin S) (a : A) : E → ℝ :=
  chartFunction (u s) τ (labels (m := m) τ) domain (fun v => F (mapVertex u hu τ s v)) a

end
end UniformSparsestCut.ConcreteCells

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GradientBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ConvolutionBounds
open MeasureTheory Set
open scoped BigOperators
variable {G : Type u5} {A : Type u6} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [Fintype A]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

def smooth (κ f : G → ℝ) (μ : Measure G) : G → ℝ :=
  convolution κ f (ContinuousLinearMap.mul ℝ ℝ) μ

end UniformSparsestCut.ConvolutionBounds

namespace UniformSparsestCut.GradientCalculus
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {A : Type u7} {S : Type u8} {I : Type u9} [Fintype A] [Fintype S] [Fintype I] [DecidableEq S]
local notation "E" => EuclideanSpace ℝ (Fin m)

def vector (D : StrongDual ℝ E) : E := (InnerProductSpace.toDual ℝ E).symm D
@[simp] lemma vector_norm (D : StrongDual ℝ E) : ‖vector D‖=‖D‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map D
@[simp] lemma vector_inner (D : StrongDual ℝ E) (x : E) : inner ℝ (vector D) x=D x :=
  InnerProductSpace.toDual_symm_apply
end
end UniformSparsestCut.GradientCalculus

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.ContractionCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.ContractionCore
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ} {A : Type u1} [Fintype A]
local notation "E" => EuclideanSpace ℝ (Fin (m+1))

def vertex (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (x : E)
    (hx : x∈RoundedCharts.cube 2) (hr : RoundedCharts.regular (u s) τ x) : RoundedCharts.Vertex u τ :=
  ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,hx,hr,rfl⟩

end
end UniformSparsestCut.ContractionCore

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianPoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianPoincare
variable {E : Type u1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def path (t : ℝ) (z : E × E) : E := Real.cos t • z.1 + Real.sin t • z.2
noncomputable def tangent (t : ℝ) (z : E × E) : E := -Real.sin t • z.1 + Real.cos t • z.2

end UniformSparsestCut.GaussianPoincare

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.GaussianCDF
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GaussianCDF
local notation "μ" => gaussianReal 0 1
def Φ (x : ℝ) : ℝ := cdf μ x
def φ (x : ℝ) : ℝ := gaussianPDFReal 0 1 x

def ψ (x : ℝ) : ℝ := 2*Φ x-1

def uniform : Measure ℝ := (2:ℝ≥0∞)⁻¹ • volume.restrict (Ioo (-1:ℝ) 1)

end UniformSparsestCut.GaussianCDF

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CubePoincare
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.CubePoincare
open MeasureTheory ProbabilityTheory Set
open scoped Topology ContDiff ENNReal BigOperators
variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def Ψ (x : E) : E := WithLp.toLp 2 (fun i => GaussianCDF.ψ (x i))
def cube : Measure E := (Measure.pi (fun _ : Fin m => GaussianCDF.uniform)).map (WithLp.toLp 2)

def coordinate (i : Fin m) : E →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj i).comp (EuclideanSpace.equiv (Fin m) ℝ).toContinuousLinearMap

@[simp] lemma coordinate_apply (i : Fin m) (x : E) : coordinate i x = x i := rfl

def derivative (x : E) : E →L[ℝ] E :=
  (EuclideanSpace.equiv (Fin m) ℝ).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => (2*GaussianCDF.φ (x i)) • coordinate i))

@[simp] lemma derivative_apply (x v : E) (i : Fin m) : derivative x v i = 2*GaussianCDF.φ (x i)*v i := rfl

end UniformSparsestCut.CubePoincare

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.FiniteDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

namespace FiniteDuality

variable {E : Type u1} {K : Type u2} [Fintype E] [Fintype K]

def packingCone (A : E → K → ℝ) (w : K → ℝ) : Set ((E → ℝ) × ℝ) :=
  {y | ∃ t : K → ℝ, (∀ k, 0 ≤ t k) ∧
      (∀ e, ∑ k, A e k * t k ≤ y.1 e) ∧ y.2 ≤ ∑ k, w k * t k}

lemma packingCone_closed (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, 0 ≤ A e k) (hcol : ∀ k, 0 < ∑ e, A e k) :
    IsClosed (packingCone A w) := by
  classical
  apply isSeqClosed_iff_isClosed.mp
  intro y b hy hyb
  choose t ht0 htA htw using hy
  have hsum : Tendsto (fun n => ∑ e, (y n).1 e) atTop (𝓝 (∑ e, b.1 e)) :=
    tendsto_finsetSum _ (fun e he => (tendsto_pi_nhds.mp hyb.fst_nhds) e)
  obtain ⟨B, hB⟩ := hsum.bddAbove_range
  have hbound (n : ℕ) (k : K) : t n k ≤ B / (∑ e, A e k) := by
    apply (le_div_iff₀ (hcol k)).mpr
    calc
      t n k * ∑ e, A e k = ∑ e, A e k * t n k := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ e, ∑ j, A e j * t n j := by
        apply Finset.sum_le_sum
        intro e he
        exact Finset.single_le_sum (fun j hj => mul_nonneg (hA e j) (ht0 n j))
          (Finset.mem_univ k)
      _ ≤ ∑ e, (y n).1 e := Finset.sum_le_sum (fun e he => htA n e)
      _ ≤ B := hB (Set.mem_range_self n)
  obtain ⟨u, hu, φ, hφ, htend⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : K → ℝ) (fun k => B / (∑ e, A e k)))).tendsto_subseq
      (fun n => ⟨ht0 n, hbound n⟩)
  refine ⟨u, hu.1, ?_, ?_⟩
  · intro e
    apply le_of_tendsto_of_tendsto
      (tendsto_finsetSum _ (fun k hk =>
        tendsto_const_nhds.mul ((tendsto_pi_nhds.mp htend) k)))
      (((tendsto_pi_nhds.mp hyb.fst_nhds) e).comp hφ.tendsto_atTop)
    exact Eventually.of_forall (fun n => htA (φ n) e)
  · apply le_of_tendsto_of_tendsto (hyb.snd_nhds.comp hφ.tendsto_atTop)
      (tendsto_finsetSum _ (fun k hk =>
        tendsto_const_nhds.mul ((tendsto_pi_nhds.mp htend) k)))
    exact Eventually.of_forall (fun n => htw (φ n))

noncomputable def packingProperCone (A : E → K → ℝ) (w : K → ℝ)
    (hA : ∀ e k, 0 ≤ A e k) (hcol : ∀ k, 0 < ∑ e, A e k) :
    ProperCone ℝ ((E → ℝ) × ℝ) where
  carrier := packingCone A w
  zero_mem' := by
    refine ⟨0, by simp, ?_, ?_⟩ <;> simp
  add_mem' := by
    rintro x y ⟨s, hs0, hsA, hsw⟩ ⟨t, ht0, htA, htw⟩
    refine ⟨s+t, fun k => add_nonneg (hs0 k) (ht0 k), ?_, ?_⟩
    · intro e
      simpa [mul_add, Finset.sum_add_distrib] using add_le_add (hsA e) (htA e)
    · simpa [mul_add, Finset.sum_add_distrib] using add_le_add hsw htw
  smul_mem' := by
    rintro ⟨a, ha⟩ x ⟨t, ht0, htA, htw⟩
    refine ⟨a • t, fun k => mul_nonneg ha (ht0 k), ?_, ?_⟩
    · intro e
      change (∑ k, A e k * (a * t k)) ≤ a * x.1 e
      simpa [← Finset.mul_sum, mul_left_comm] using
        mul_le_mul_of_nonneg_left (htA e) ha
    · change a * x.2 ≤ ∑ k, w k * (a * t k)
      simpa [← Finset.mul_sum, mul_left_comm] using
        mul_le_mul_of_nonneg_left htw ha
  isClosed' := packingCone_closed A w hA hcol

end FiniteDuality

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CutSums
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section CutSums

variable {n : ℕ}

noncomputable def cutIndicator (B : Finset (Fin n)) (i : Fin n) : ℝ := if i ∈ B then 1 else 0
noncomputable def cutDist (B : Finset (Fin n)) (i j : Fin n) : ℝ :=
  |cutIndicator B i - cutIndicator B j|
noncomputable def cutDemand (B : Finset (Fin n)) : ℝ := (B.card : ℝ) * (Bᶜ.card : ℝ)

def Cut (n : ℕ) := {B : Finset (Fin n) // B.Nonempty ∧ B ≠ Finset.univ}

noncomputable instance instFintypeCut : Fintype (Cut n) := by unfold Cut; exact Fintype.ofFinite _

@[simp] lemma cutDist_self (B : Finset (Fin n)) (i : Fin n) : cutDist B i i = 0 := by
  simp [cutDist]

end CutSums

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Semimetrics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section SemimetricBounds

variable {n : ℕ}

def IsSemimetric (d : Fin n → Fin n → ℝ) : Prop :=
  (∀ i j, 0 ≤ d i j) ∧ (∀ i j, d i j = d j i) ∧
    (∀ i, d i i = 0) ∧ (∀ i j k, d i k ≤ d i j + d j k)

end SemimetricBounds

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.CutDuality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut

section CutConeDuality
variable {n : ℕ}

noncomputable def symmetrizeCapacity (c : (Fin n × Fin n) → ℝ)
    (hc : ∀ e, 0 ≤ c e) : Capacity n where
  cap i j := if i = j then 0 else c (i,j) + c (j,i)
  nonneg i j := by split_ifs; exact le_rfl; exact add_nonneg (hc _) (hc _)
  symm i j := by by_cases h : i = j <;> simp [h, eq_comm, add_comm]
  diagonal i := by simp

end CutConeDuality

end UniformSparsestCut

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.VertexMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.VertexMeasure
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m N S : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)
local notation "μ" => (CubePoincare.cube (m:=m))
local instance instMeasurableSpaceVertex {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSpace (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
local instance instMeasurableSingletonClassVertex_r28fabd_1 {u : Fin S → Fin N → E} {τ : ℝ} : MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
open Classical in
def label (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) (x : E) : RoundedCharts.Vertex u τ :=
  if h : x∈RoundedCharts.cube 2 ∧ RoundedCharts.regular (u s) τ x then
    ⟨(s,RoundedCharts.integerLabel (u s) τ x),x,h.1,h.2,rfl⟩ else v₀
def measure (u : Fin S → Fin N → E) (τ : ℝ) (s : Fin S) (v₀ : RoundedCharts.Vertex u τ) : Measure (RoundedCharts.Vertex u τ) :=
  (μ).map (label u τ s v₀)
end
end UniformSparsestCut.VertexMeasure

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.WeightedMetric
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceWeighted
open MeasureTheory Set Filter
open scoped BigOperators RealInnerProductSpace
open SourceCharts SourceParameters SourceMetric
noncomputable section
local instance instMeasurableSpaceVertex {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSpace (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance

local instance instMeasurableSingletonClassVertex_r28fabd_2 {m N S : ℕ} {u : Fin S → Fin N → EuclideanSpace ℝ (Fin m)} {τ : ℝ} :
    MeasurableSingletonClass (RoundedCharts.Vertex u τ) := by unfold RoundedCharts.Vertex; infer_instance
def D : ℝ := 4*KernelApprox.cstar+C₀
end
end UniformSparsestCut.SourceWeighted

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.LabelCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.LabelCount
open scoped BigOperators RealInnerProductSpace
open UniformSparsestCut
variable {m N : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

def signature (B : ℤ) (l : Fin N → ℤ) : Finset (Fin N × ↥(Finset.Icc (-B) B)) :=
  Finset.univ.filter (fun p => p.2.val ≤ l p.1)

def affineForm (u : Fin N → E) (τ : ℝ) (B : ℤ)
    (p : Fin N × ↥(Finset.Icc (-B) B)) : E × ℝ →ₗ[ℝ] ℝ :=
  (innerSL ℝ (u p.1)).toLinearMap.comp (LinearMap.fst ℝ E ℝ) -
    ((p.2.val:ℝ)*τ) • LinearMap.snd ℝ E ℝ

end UniformSparsestCut.LabelCount

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Replication
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u1 u2 u3 u4

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.Replication
variable {V : Type u1} [Fintype V]
def count (M : ℕ) (w : V → ℝ) (v : V) : ℕ := 1+⌊(M:ℝ)*w v⌋₊
def Copies (M : ℕ) (w : V → ℝ) := (v : V) × Fin (count M w v)
instance instFintypeCopies (M : ℕ) (w : V → ℝ) : Fintype (Copies M w) := inferInstanceAs (Fintype (Sigma _))
def n (M : ℕ) (w : V → ℝ) : ℕ := Fintype.card (Copies M w)
def q (M : ℕ) (w : V → ℝ) (v : V) : ℝ := (count M w v:ℝ)/(n M w:ℝ)
omit [Fintype V] in
lemma count_pos (M : ℕ) (w : V → ℝ) (v : V) : 0<count M w v := by unfold count; omega
end UniformSparsestCut.Replication

namespace UniformSparsestCut.Replication
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {V : Type u2} [Fintype V]
def rep (M : ℕ) (w : V → ℝ) (i : Fin (n M w)) : V := ((Fintype.equivFin (Copies M w)).symm i).1
def representative (M : ℕ) (w : V → ℝ) (v : V) : Fin (n M w) :=
  (Fintype.equivFin (Copies M w)) ⟨v,⟨0,count_pos M w v⟩⟩
end
end UniformSparsestCut.Replication

end

end OAI
end

section
-- module Solutions.OAIQW_UniformSparsestCut.Logarithms
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.RateComparison
open Filter
noncomputable section
def weight (x : ℝ) : ℝ := Real.sqrt x*(Real.log x)^2*Real.sqrt (Real.log x)
end
end UniformSparsestCut.RateComparison

end

end OAI
end


