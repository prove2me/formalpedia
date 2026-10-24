-- Prove2me | Definitions.Def_OAIQWQL000
-- name    : OAIQWQL000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-23T18:10:37.365171+00:00
-- url     : https://prove2.me/theorems/0d41a773-d85b-4d3c-aa98-47fd857929a4
-- title:
--   OpenAI quintic Liénard split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof that a Liénard system $\dot x = y - F(x)$, $\dot y = -x$ with $\deg F \le 5$ has at most two limit cycles, and that two occur (`OAI.QuinticLienard.main`). It holds OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Analysis/LienardCycles` (OpenAI, *Two limit cycles for quintic Liénard systems*, OpenAI Math Release, September 24, 2026, result family 143, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a. Among them are:
--   - arches of a profile and their endpoints, half-width and midpoint (`ScalarArcs.IsArch`, `ScalarArcs.width`, `ScalarArcs.midpoint`, `PositiveWidth.midpointAtWidth`, `PositiveWidth.Admissible`);
--   - the quintic profile and its derivatives (`ScaledProfile.poly`, `QuinticProfile.profile`, `ScaledProfile.slope`, `ScaledProfile.curvature`, `ScaledProfile.third`, `ScaledProfile.reflectX`);
--   - the quadratic comparison profiles and the global quadratic fit (`QuadraticFit.fitD`, `QuadraticFit.fitK`, `QuinticFit.lambda`, `QuinticFit.kappa`, `QuadraticCoordinates.Cr`);
--   - the height-zero matching data (`AxisFlow.transversePeaks`, `AxisFlow.axisWidths`, `AxisFlow.axisM`, `AxisFlow.axisLambda`, `AxisFlow.matchingDelta`, `AxisFlow.matchingDomain`) and `IsIsolatedZeroOn`;
--   - the arch quantities along a fixed peak (`ActualCharacteristic.Adm`, `ActualCharacteristic.point`, `ActualCharacteristic.feed`) and the sharpness family (`Sharpness.F`).
--
--   The bundle also contains the lemmas those definitions use in their bodies, together with the analytic-flow and path machinery (`SmoothFlow`) that several of them are built on.
--
--   The definitions of the published statement (`Plane`, `vectorField`, `IsSolution`, `IsPeriodicOrbit`, `IsLimitCycle`) are not repeated: the bundle imports them from the published bundle `Def_QuinticLienard`. It imports no other bundle.
--
--   Modules: `SmoothFlow.lean`, `GlobalODE.lean`, `PartialCalculus.lean`, `ScalarArcs.lean`, `ArcFamilies.lean`, `ArcEndpoints.lean`, `PolynomialModel.lean`, `WidthCoordinates.lean`, `WidthTransport.lean`, `QuadraticCoordinates.lean`, `QuadraticDerivatives.lean`, `ModelEndpoint.lean`, `RiccatiJets.lean`, `RiccatiDerivatives.lean`, `Riccati.lean`, `QuadraticSlices.lean`, `Characteristic.lean`, `CharacteristicJets.lean`, `RadiusLimits.lean`, `HeightLimits.lean`, `Schwarzian.lean`, `ModelAlgebra.lean`, `EndpointAlgebra.lean`, `RealAnalysis.lean`, `EndpointJets.lean`, `CurvatureJets.lean`, `QuadraticFit.lean`, `SqrtPaths.lean`, `AlgebraicFlow.lean`, `AlgebraicNotation.lean`, `ScaledAlgebraic.lean`, `ScaledExpansion.lean`, `PositiveWidth.lean`, `PositiveTransport.lean`, `ConditionalFit.lean`, `HyperbolicCoordinate.lean`, `FitAngles.lean`, `FitProperness.lean`, `GlobalFit.lean`, `CubicVariation.lean`, `PositiveFit.lean`, `ScaledCoefficients.lean`, `OriginalProfile.lean`, `ScaledDerivative.lean`, `ScaledActual.lean`, `ActualFitTransport.lean`, `CurvatureTransport.lean`, `PositiveBase.lean`, `ActualCharacteristic.lean`, `ActualError.lean`, `CurvaturePositive.lean`, `Intercept.lean`, `AxisLimits.lean`, `BoundaryFlow.lean`, `AxisBranches.lean`, `AxisRegularity.lean`, `AxisWidthGerm.lean`, `AxisWidthRegularity.lean`, `AxisFit.lean`, `AxisZeros.lean`, `AxisSecants.lean`, `AxisIntercept.lean`, `CoefficientCases.lean`, `SharpFlow.lean`, `SharpReturn.lean`, `SharpPhysical.lean`, `ExcursionGraph.lean`, `PeriodicSymmetry.lean`, `OpenArch.lean`, `ReturnNeighborhood.lean`, `CaseOne.lean`, `CycleTransform.lean`, `SharpCycles.lean`.
--
--   The theorems of the development that the definitions do not need are proved in the eleven solutions of this split. Ten of them prove the published intermediate statements: the two halves of Theorem 1.1, `OAI.QuinticLienard.upper_bound` and `OAI.QuinticLienard.Sharpness.sharpness`, and eight lemmas behind the upper bound (three coefficient-sign cases of the matching count and five comparison results for the fitted slope and curvature). The last one proves `OAI.QuinticLienard.main` from the two halves. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Two limit cycles for quintic Liénard systems, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 143; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/two-limit-cycles-for-quintic-lienard-systems-September-24-2026/two-limit-cycles-for-quintic-lienard-systems-September-24-2026.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/LienardCycles at commit adc7f12

import Mathlib
import Definitions.Def_QuinticLienard

section
-- module Solutions.OAIQW_QuinticLienard.SmoothFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uι

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace QuinticLienard.SmoothFlow

abbrev UnitInterval := Icc (-1 : ℝ) 1
abbrev Path (E : Type uE) [TopologicalSpace E] := C(UnitInterval, E)

noncomputable def clamp (t : ℝ) : UnitInterval := projIcc (-1) 1 (by norm_num) t

@[simp] lemma clamp_val (t : UnitInterval) : clamp t = t := by
  simp [clamp]

lemma continuous_clamp : Continuous clamp := by
  exact continuous_projIcc (h := by norm_num)

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def extend (u : Path E) : ℝ → E := fun t => u (clamp t)

omit [NormedSpace ℝ E] in
lemma continuous_extend (u : Path E) : Continuous (extend u) :=
  u.continuous.comp continuous_clamp

omit [NormedSpace ℝ E] in
@[simp] lemma extend_val (u : Path E) (t : UnitInterval) : extend u t = u t := by
  simp [extend]

omit [NormedSpace ℝ E] in
@[simp] lemma extend_add (u v : Path E) : extend (u+v) = extend u + extend v := rfl
@[simp] lemma extend_smul (c : ℝ) (u : Path E) : extend (c • u) = c • extend u := rfl

noncomputable def primitive (u : Path E) : Path E where
  toFun t := ∫ s in (0:ℝ)..(t:ℝ), extend u s
  continuous_toFun := by
    have hc : Continuous (fun t : ℝ => ∫ s in (0:ℝ)..t, extend u s) :=
      intervalIntegral.continuous_primitive (continuous_extend u).intervalIntegrable 0
    exact hc.comp continuous_subtype_val

@[simp] lemma primitive_apply (u : Path E) (t : UnitInterval) :
    primitive u t = ∫ s in (0:ℝ)..(t:ℝ), extend u s := rfl

lemma norm_primitive_le (u : Path E) : ‖primitive u‖ ≤ ‖u‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro t
  calc
    ‖primitive u t‖ ≤ ‖u‖ * |(t:ℝ)-0| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun s _ => u.norm_coe_le_norm (clamp s)
    _ ≤ ‖u‖ := by
      have ht : |(t:ℝ)| ≤ 1 := abs_le.mpr t.property
      simpa using mul_le_mul_of_nonneg_left ht (norm_nonneg u)

noncomputable def primitiveCLM : Path E →L[ℝ] Path E :=
  LinearMap.mkContinuous
    { toFun := primitive
      map_add' := by
        intro u v
        ext t
        simp only [primitive_apply, ContinuousMap.add_apply, extend_add, Pi.add_apply]
        exact intervalIntegral.integral_add ((continuous_extend u).intervalIntegrable _ _)
          ((continuous_extend v).intervalIntegrable _ _)
      map_smul' := by
        intro c u
        ext t
        simp [primitive_apply, intervalIntegral.integral_smul] }
    1 (by intro u; simpa using norm_primitive_le u)

@[simp] lemma primitiveCLM_apply (u : Path E) : primitiveCLM u = primitive u := rfl

noncomputable def constCLM : E →L[ℝ] Path E :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.const UnitInterval
      map_add' := by intro x y; ext; rfl
      map_smul' := by intro c x; ext; rfl }
    1 (by
      intro x
      rw [one_mul]
      exact (ContinuousMap.norm_le _ (norm_nonneg x)).mpr (fun _ => le_rfl))

@[simp] lemma constCLM_apply (x : E) (t : UnitInterval) : constCLM x t = x := rfl

@[simp] lemma extend_const (x : E) : extend (constCLM x) = fun _ => x := rfl

@[simp] lemma primitive_zero (u : Path E) : extend (primitive u) 0 = 0 := by
  simp [extend, primitive_apply, clamp, projIcc_of_mem (by norm_num : (-1 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ∈ Icc (-1) 1)]

noncomputable def reparam (u : Path E) (q : ℝ) : Path E where
  toFun s := extend u (q * s)
  continuous_toFun := (continuous_extend u).comp (continuous_const.mul continuous_subtype_val)

omit [NormedSpace ℝ E] in
@[simp] lemma reparam_apply (u : Path E) (q : ℝ) (s : UnitInterval) :
    reparam u q s = extend u (q * s) := rfl

section PolynomialFields
variable {ι : Type uι} [Fintype ι]

noncomputable def coordinate (i : ι) : Path (ι → ℝ) →L[ℝ] Path ℝ :=
  ContinuousLinearMap.compLeftContinuous ℝ UnitInterval (ContinuousLinearMap.proj i)

omit [Fintype ι] in
@[simp] lemma coordinate_apply (i : ι) (u : Path (ι → ℝ)) (s : UnitInterval) :
    coordinate i u s = u s i := rfl

noncomputable def assemble : (ι → Path ℝ) →L[ℝ] Path (ι → ℝ) :=
  LinearMap.mkContinuous
    { toFun := ContinuousMap.pi
      map_add' := by intro u v; ext s i; rfl
      map_smul' := by intro c u; ext s i; rfl }
    1 (by
      intro u
      rw [one_mul]
      apply (ContinuousMap.norm_le _ (norm_nonneg u)).mpr
      intro s
      apply (pi_norm_le_iff_of_nonneg (norm_nonneg u)).mpr
      intro i
      exact (u i).norm_coe_le_norm s |>.trans (norm_le_pi_norm u i))

@[simp] lemma assemble_apply (u : ι → Path ℝ) (s : UnitInterval) (i : ι) :
    assemble u s i = u i s := rfl

noncomputable def scalarPolynomial (p : MvPolynomial ι ℝ) (u : Path (ι → ℝ)) : Path ℝ :=
  MvPolynomial.eval₂ (algebraMap ℝ (Path ℝ)) (fun i => coordinate i u) p

end PolynomialFields

end QuinticLienard.SmoothFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.GlobalODE
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold

namespace QuinticLienard.GlobalODE

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem bounded_lipschitz_global_solution (V : E → E) {K L : ℝ≥0}
    (hK : LipschitzWith K V) (hL : ∀ x, ‖V x‖ ≤ L) (x₀ : E) :
    ∃ u : ℝ → E, u 0 = x₀ ∧ ∀ t, HasDerivAt u (V (u t)) t := by
  have hex (N : ℕ) : ∃ u : ℝ → E, u 0 = x₀ ∧
      ∀ t, |t| < (N:ℝ)+1 → HasDerivAt u (V (u t)) t := by
    let T : ℝ := (N:ℝ)+1
    have hT : 0 < T := by dsimp [T]; positivity
    let t₀ : Icc (-T) T := ⟨0, by constructor <;> linarith⟩
    have hpl : IsPicardLindelof (fun _ : ℝ => V) t₀ x₀ (L * (N+1)) 0 L K := by
      constructor
      · exact fun _ _ => hK.lipschitzOnWith
      · exact fun _ _ => continuous_const.continuousOn
      · exact fun _ _ x _ => hL x
      · simp [t₀, T, mul_add]
    obtain ⟨u,hu,hdu⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    refine ⟨u,hu,fun t ht => ?_⟩
    have ht' : t ∈ Ioo (-T) T := abs_lt.mp ht
    exact (hdu t (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2)
  choose u hu hdu using hex
  have hmatch (N M : ℕ) {t : ℝ} (htN : |t| < (N:ℝ)+1) (htM : |t| < (M:ℝ)+1) :
      u N t = u M t := by
    let R : ℝ := min ((N:ℝ)+1) ((M:ℝ)+1)
    have hR : 0 < R := lt_min (by positivity) (by positivity)
    have hsubN {s : ℝ} (hs : s ∈ Ioo (-R) R) : |s| < (N:ℝ)+1 :=
      (abs_lt.mpr hs).trans_le (min_le_left _ _)
    have hsubM {s : ℝ} (hs : s ∈ Ioo (-R) R) : |s| < (M:ℝ)+1 :=
      (abs_lt.mpr hs).trans_le (min_le_right _ _)
    have he := ODE_solution_unique_of_mem_Ioo
      (v := fun _ : ℝ => V) (s := fun _ => (Set.univ : Set E))
      (fun _ _ => hK.lipschitzOnWith)
      (show (0:ℝ) ∈ Ioo (-R) R by constructor <;> linarith)
      (fun s hs => ⟨hdu N s (hsubN hs), mem_univ _⟩)
      (fun s hs => ⟨hdu M s (hsubM hs), mem_univ _⟩)
      (by rw [hu N, hu M])
    exact he (abs_lt.mp (lt_min htN htM))
  let U : ℝ → E := fun t => u ⌈|t|⌉₊ t
  have hpoint (N : ℕ) {t : ℝ} (ht : |t| < (N:ℝ)+1) : U t = u N t := by
    apply hmatch _ N _ ht
    exact (Nat.le_ceil _).trans_lt (by linarith)
  refine ⟨U,by simp [U,hu],fun t => ?_⟩
  let N := ⌈|t|⌉₊
  have ht : |t| < (N:ℝ)+1 := (Nat.le_ceil _).trans_lt (by linarith)
  have hevent : U =ᶠ[𝓝 t] u N := by
    filter_upwards [Ioo_mem_nhds (abs_lt.mp ht).1 (abs_lt.mp ht).2] with s hs
    exact hpoint N (abs_lt.mpr hs)
  rw [hpoint N ht]
  exact (hdu N t ht).congr_of_eventuallyEq hevent

section Flow
variable (V : E → E) {K L : ℝ≥0} (hK : LipschitzWith K V) (hL : ∀ x, ‖V x‖ ≤ L)

noncomputable def flow (x : E) : ℝ → E :=
  Classical.choose (bounded_lipschitz_global_solution V hK hL x)

@[simp] theorem flow_zero (x : E) : flow V hK hL x 0 = x :=
  (Classical.choose_spec (bounded_lipschitz_global_solution V hK hL x)).1

end Flow

end QuinticLienard.GlobalODE

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PartialCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

open Set Filter MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold

open Filter Set
open scoped Topology ContDiff

namespace QuinticLienard.PartialCalculus

variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

noncomputable def direction (v : E) (f : E → F) (x : E) : F := fderiv ℝ f x v

noncomputable def first (f : ℝ × ℝ → F) : ℝ × ℝ → F := direction (1,0) f
noncomputable def second (f : ℝ × ℝ → F) : ℝ × ℝ → F := direction (0,1) f

end QuinticLienard.PartialCalculus

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScalarArcs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open scoped Topology ContDiff

open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff

namespace QuinticLienard.ScalarArcs

structure IsArch (φ u : ℝ → ℝ) (h t a b : ℝ) : Prop where
  continuous : Continuous u
  lower_lt_peak : a < φ t
  peak_lt_upper : φ t < b
  peak : u (φ t) = t
  lower : u a = h
  upper : u b = h
  lower_transverse : a < φ h
  upper_transverse : φ h < b
  equation : ∀ y ∈ Icc a b, HasDerivAt u (φ (u y)-y) y
  range_mem : ∀ y ∈ Icc a b, h ≤ u y ∧ u y ≤ t
  inc : StrictMonoOn u (Icc a (φ t))
  dec : StrictAntiOn u (Icc (φ t) b)

noncomputable def archTuple (φ : ℝ → ℝ) (h t : ℝ) : (ℝ → ℝ) × ℝ × ℝ :=
  Classical.epsilon (fun p => IsArch φ p.1 h t p.2.1 p.2.2)

noncomputable def archFunction (φ : ℝ → ℝ) (h t : ℝ) : ℝ → ℝ := (archTuple φ h t).1
noncomputable def lower (φ : ℝ → ℝ) (h t : ℝ) : ℝ := (archTuple φ h t).2.1
noncomputable def upper (φ : ℝ → ℝ) (h t : ℝ) : ℝ := (archTuple φ h t).2.2
noncomputable def width (φ : ℝ → ℝ) (h t : ℝ) : ℝ := (upper φ h t-lower φ h t)/2
noncomputable def midpoint (φ : ℝ → ℝ) (h t : ℝ) : ℝ :=
  (upper φ h t+lower φ h t)/2-φ h

end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ArcFamilies
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff

open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ArcFamilies
open PartialCalculus

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]

abbrev State (P : Type uP) := P × (ℝ × ℝ)

def field (Φ : P × ℝ → ℝ) (z : State P) : State P :=
  (0,(Φ (z.1,z.2.1)-z.2.2,1))

end QuinticLienard.ArcFamilies

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ArcEndpoints
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ArcEndpoints
open PartialCalculus ScalarArcs

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P]

noncomputable def lowerFamily (Φ : P × ℝ → ℝ) (q : (P × ℝ) × ℝ) : ℝ :=
  lower (fun x => Φ (q.1.1,x)) q.2 q.1.2
noncomputable def upperFamily (Φ : P × ℝ → ℝ) (q : (P × ℝ) × ℝ) : ℝ :=
  upper (fun x => Φ (q.1.1,x)) q.2 q.1.2

end QuinticLienard.ArcEndpoints

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PolynomialModel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PolynomialModel

abbrev ModelState := (ℝ × ℝ) × (ℝ × ℝ)

noncomputable def stateEquiv : ModelState ≃L[ℝ] (Fin 4 → ℝ) :=
  (show ModelState ≃ₗ[ℝ] (Fin 4 → ℝ) from
    { toFun := fun z => ![z.1.1,z.1.2,z.2.1,z.2.2]
      invFun := fun v => ((v 0,v 1),(v 2,v 3))
      left_inv := by intro z; rfl
      right_inv := by intro v; ext i; fin_cases i <;> rfl
      map_add' := by intros; ext i; fin_cases i <;> rfl
      map_smul' := by intros; ext i; fin_cases i <;> rfl }).toContinuousLinearEquiv

noncomputable def profile (q : (ℝ × ℝ) × ℝ) : ℝ :=
  q.1.1*q.2 + q.1.2/2*q.2^2

open MvPolynomial in
noncomputable def polynomials : Fin 4 → MvPolynomial (Fin 4) ℝ :=
  ![0,0,X 0*X 2+C (1/2)*(X 1*X 2^2)-X 3,1]

end QuinticLienard.PolynomialModel

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.WidthCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.WidthCoordinates
open ScalarArcs ArcEndpoints ArcFamilies

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

noncomputable def widthFamily (q : (P × ℝ) × ℝ) : ℝ :=
  width (fun u => Φ (q.1.1,u)) q.2 q.1.2
noncomputable def midpointFamily (q : (P × ℝ) × ℝ) : ℝ :=
  midpoint (fun u => Φ (q.1.1,u)) q.2 q.1.2

include hΦ hloc

noncomputable def peakAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  Classical.epsilon (fun t => q.1.2 < t ∧ widthFamily Φ ((q.1.1,t),q.1.2) = q.2)

noncomputable def baseAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  Classical.epsilon (fun h => h < q.1.2 ∧ widthFamily Φ (q.1,h) = q.2)

noncomputable def midpointAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  midpointFamily Φ ((q.1.1,peakAtWidth Φ q),q.1.2)

end QuinticLienard.WidthCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.WidthTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.WidthTransport
open ScalarArcs ArcEndpoints ArcFamilies WidthCoordinates PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ContDiff ℝ ω Φ)
    (hloc : ∀ x : State P, ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

noncomputable def M (p : P) (q : ℝ × ℝ) : ℝ := midpointAtWidth Φ ((p,q.1),q.2)
noncomputable def v (p : P) : ℝ × ℝ → ℝ := second (M Φ p)

end QuinticLienard.WidthTransport

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open ScalarArcs PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus

noncomputable def H (q : (ℝ × ℝ) × ℝ) : ℝ := midpointAtWidth profile ((q.1,0),q.2)
noncomputable def P : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) H
noncomputable def Q : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) H
noncomputable def Hr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) H
noncomputable def R : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) P
noncomputable def S : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) Q
noncomputable def G (q : (ℝ × ℝ) × ℝ) : ℝ := P q*S q-Q q*R q

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PolynomialModel PartialCalculus

noncomputable def Rr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) R
noncomputable def Sr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) S
noncomputable def W (q : (ℝ × ℝ) × ℝ) : ℝ := R q*Sr q-S q*Rr q

noncomputable def PN (q : (ℝ × ℝ) × ℝ) : ℝ := P ((q.1.1*q.2,q.1.2*q.2^3),1)
noncomputable def QN (q : (ℝ × ℝ) × ℝ) : ℝ := Q ((q.1.1*q.2,q.1.2*q.2^3),1)
noncomputable def PNr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) PN
noncomputable def QNr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) QN
noncomputable def PNrr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) PNr
noncomputable def QNrr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) QNr

noncomputable def WN (q : (ℝ × ℝ) × ℝ) : ℝ :=
  (2*PN q+q.2*PNr q)*(12*QN q+8*q.2*QNr q+q.2^2*QNrr q)-
  (4*QN q+q.2*QNr q)*(2*PN q+4*q.2*PNr q+q.2^2*PNrr q)

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ModelEndpoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open ScalarArcs ArcEndpoints PolynomialModel WidthCoordinates
  PartialCalculus QuadraticCoordinates

noncomputable def m (q : (ℝ × ℝ) × ℝ) : ℝ := q.2-H q
noncomputable def n (q : (ℝ × ℝ) × ℝ) : ℝ := q.2+H q
noncomputable def ell (q : (ℝ × ℝ) × ℝ) : ℝ := (1+Hr q)/(1-Hr q)

structure LowerChart (d k r : ℝ) where
  radius : ℝ → ℝ
  upper : ℝ → ℝ
  solution : ℝ × ℝ → ℝ
  radius_analytic : ContDiffAt ℝ ω radius (m ((d,k),r))
  radius_base : radius (m ((d,k),r)) = r
  radius_relation : ∀ᶠ s in 𝓝 (m ((d,k),r)), m ((d,k),radius s)=s
  radius_derivative : HasDerivAt radius (1/(1-Hr ((d,k),r))) (m ((d,k),r))
  upper_def : ∀ s, upper s=n ((d,k),radius s)
  upper_analytic : ContDiffAt ℝ ω upper (m ((d,k),r))
  upper_base : upper (m ((d,k),r)) = n ((d,k),r)
  upper_derivative : HasDerivAt upper (ell ((d,k),r)) (m ((d,k),r))
  solution_continuous : ∀ s, Continuous (fun y => solution (s,y))
  solution_analytic : ∀ y ∈ Icc (-m ((d,k),r)) (n ((d,k),r)),
    ContDiffAt ℝ ω solution (m ((d,k),r),y)
  equation : ∀ y ∈ Icc (-m ((d,k),r)) (n ((d,k),r)),
    ∀ᶠ q in 𝓝 (m ((d,k),r),y), HasDerivAt (fun s => solution (q.1,s))
      (d*solution q+(k/2)*(solution q)^2-q.2) q.2
  lower_zero : ∀ᶠ s in 𝓝 (m ((d,k),r)), solution (s,-s)=0
  upper_zero : ∀ᶠ s in 𝓝 (m ((d,k),r)), solution (s,upper s)=0

end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RiccatiJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.RiccatiJets
open PartialCalculus

noncomputable def logJet (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := first (first u) q/first u q
noncomputable def schwarzJet (u : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ :=
  first (first (first u)) q/first u q-(3/2)*(logJet u q)^2

end QuinticLienard.RiccatiJets

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RiccatiDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.RiccatiJets
open PartialCalculus

noncomputable def schwarzian (Y : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv (deriv (deriv Y)) t/deriv Y t-(3/2)*(deriv (deriv Y) t/deriv Y t)^2

end QuinticLienard.RiccatiJets

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Riccati
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter MeasureTheory
open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology ContDiff

open Set Filter MeasureTheory
open scoped Topology

namespace QuinticLienard.Riccati

noncomputable def multiplier (u : ℝ → ℝ) (b d c y : ℝ) : ℝ :=
  Real.exp (-(∫ s in c..y, b*u s+d/2))

@[simp] lemma multiplier_initial (u : ℝ → ℝ) (b d c : ℝ) : multiplier u b d c c = 1 := by
  simp [multiplier]

end QuinticLienard.Riccati

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticSlices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open ScalarArcs PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus

noncomputable def gap (q : (ℝ × ℝ) × ℝ) : ℝ := q.2^2-(H q)^2
noncomputable def alpha (q : (ℝ × ℝ) × ℝ) : ℝ := q.2/gap q
noncomputable def gamma (q : (ℝ × ℝ) × ℝ) : ℝ :=
  (q.2^2+(H q)^2+2*q.2*H q*Hr q)/(gap q)^2

noncomputable def Hrr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) Hr

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open ScalarArcs PolynomialModel WidthCoordinates
  WidthTransport PartialCalculus QuadraticCoordinates

noncomputable def base (q : (ℝ × ℝ) × ℝ) : ℝ :=
  baseAtWidth profile ((q.1,0),q.2)
noncomputable def J (q : (ℝ × ℝ) × ℝ) : ℝ := q.1.1+q.1.2*base q
noncomputable def A (q : (ℝ × ℝ) × ℝ) : ℝ := H ((J q,q.1.2),q.2)/q.2
noncomputable def D (q : (ℝ × ℝ) × ℝ) : ℝ := Hr ((J q,q.1.2),q.2)
noncomputable def Jz : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) J
noncomputable def Jk : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) J
noncomputable def Az : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) A
noncomputable def Ak : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) A
noncomputable def Dz : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) D
noncomputable def Dk : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) D

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CharacteristicJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ReferenceCharacteristic
open PartialCalculus QuadraticCoordinates

noncomputable def C (q : (ℝ × ℝ) × ℝ) : ℝ := -2*(J q*A q+1/q.2)
noncomputable def E (q : (ℝ × ℝ) × ℝ) : ℝ := 2*A q/(q.2*(1-(A q)^2))
noncomputable def K (q : (ℝ × ℝ) × ℝ) : ℝ := 2*(1+(A q)^2)/(q.2*(1-(A q)^2)^2)
noncomputable def U (q : (ℝ × ℝ) × ℝ) : ℝ := Dz q/(1-(D q)^2)
noncomputable def V (q : (ℝ × ℝ) × ℝ) : ℝ := Dk q/(1-(D q)^2)
noncomputable def T (q : (ℝ × ℝ) × ℝ) : ℝ := Ak q/Az q
noncomputable def B (q : (ℝ × ℝ) × ℝ) : ℝ := V q-T q*U q

end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RadiusLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates

noncomputable def RN (q : (ℝ × ℝ) × ℝ) : ℝ := 2*PN q+q.2*PNr q
noncomputable def GN (q : (ℝ × ℝ) × ℝ) : ℝ :=
  PN q*(4*QN q+q.2*QNr q)-QN q*(2*PN q+q.2*PNr q)

end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.HeightLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus
noncomputable def HN (q : (ℝ × ℝ) × ℝ) : ℝ := H ((q.1.1*q.2,q.1.2*q.2^3),1)
noncomputable def DN (q : (ℝ × ℝ) × ℝ) : ℝ :=
  HN q+q.1.1*q.2*PN q+3*q.1.2*q.2^3*QN q
end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Schwarzian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates RiccatiJets

noncomputable def w (q : (ℝ × ℝ) × ℝ) : ℝ :=
  2*Hrr q/((1-Hr q)^2*(1+Hr q))
noncomputable def sch (q : (ℝ × ℝ) × ℝ) : ℝ :=
  q.1.2*(m q+n q*(ell q)^2)+(q.1.1^2/2)*((ell q)^2-1)-
    q.1.1*(1/m q+(ell q)^2/n q)+(3/2)*((ell q)^2/(n q)^2-1/(m q)^2)

end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ModelAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.ModelAlgebra

noncomputable def wStar (m n l : ℝ) : ℝ :=
  2 * (l * m^4 - 2*l*m^3*n + 2*m*n^3 - n^4) / (m^2*n^2*(m+n))

noncomputable def dStar (m n l w S : ℝ) : ℝ :=
  (m-n)*S + (1-2*n/m+l*(2*m/n-1))*w + (m+n)/2*w^2

noncomputable def schwarzian (m n l b d : ℝ) : ℝ :=
  2*b*(m+n*l^2) + d^2/2*(l^2-1) - d*(1/m+l^2/n) +
    3/2*(l^2/n^2-1/m^2)

noncomputable def A (z l : ℝ) : ℝ := 2*l*z^3-3*l*z^2+3*z-2
noncomputable def T (z l : ℝ) : ℝ := 2*l*z^3-l*z^2-z+2
noncomputable def J (z l : ℝ) : ℝ := 2*l*z^4-2*l*z^3-l*z^2+z^2+2*z-2
noncomputable def S₀ (z l : ℝ) : ℝ := 3/2*(l^2-z⁻¹^2)

end QuinticLienard.ModelAlgebra

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.EndpointAlgebra
open ModelAlgebra
noncomputable def X (m n l : ℝ) : ℝ := (l/m-1/n)/(1+l)
noncomputable def Z (m n l : ℝ) : ℝ := (l*m-n)/(1+l)
noncomputable def gamma (m n l : ℝ) : ℝ := (l/m^2+1/n^2)/(1+l)
noncomputable def Z1 (m n l w : ℝ) : ℝ := l*w*(m+n)/(1+l)^2
noncomputable def Z2 (m n l w s : ℝ) : ℝ :=
  l*(s+3/2*w^2)*(m+n)/(1+l)^2+l*w/(1+l)-2*l^2*w^2*(m+n)/(1+l)^3
noncomputable def X1 (m n l w : ℝ) : ℝ := l*(1/n^2-1/m^2)/(1+l)+Z1 m n l w/(m*n)
noncomputable def X2 (m n l w s : ℝ) : ℝ :=
  l*w*(1/n^2-1/m^2)/(1+l)^2+l*(2/m^3-2*l/n^3)/(1+l)+
    Z2 m n l w s/(m*n)-Z1 m n l w*(n+m*l)/(m^2*n^2)
noncomputable def N0 (m n l : ℝ) : ℝ := l/m^2+1/n^2
noncomputable def N1 (m n l w : ℝ) : ℝ := l*w/m^2-2*l/m^3-2*l/n^3
noncomputable def N2 (m n l w s : ℝ) : ℝ :=
  l*(s+3/2*w^2)/m^2-4*l*w/m^3+6*l/m^4-2*l*w/n^3+6*l^2/n^4
noncomputable def gamma1 (m n l w : ℝ) : ℝ := N1 m n l w/(1+l)-N0 m n l*l*w/(1+l)^2
noncomputable def gamma2 (m n l w s : ℝ) : ℝ :=
  N2 m n l w s/(1+l)-2*N1 m n l w*l*w/(1+l)^2-
    N0 m n l*l*(s+3/2*w^2)/(1+l)^2+2*N0 m n l*(l*w)^2/(1+l)^3

end QuinticLienard.EndpointAlgebra

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.RealAnalysis
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology

namespace QuinticLienard.RealAnalysis

def IsIsolatedZeroOn (f : ℝ → ℝ) (J : Set ℝ) (x : ℝ) : Prop :=
  x ∈ J ∧ f x = 0 ∧ ∃ ε > 0, ∀ y ∈ Ioo (x-ε) (x+ε), y ∈ J → f y = 0 → y = x

end QuinticLienard.RealAnalysis

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.EndpointJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ModelEndpoint
open PartialCalculus QuadraticCoordinates
noncomputable def Xj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.X1 (m q) (n q) (ell q) (w q)
noncomputable def Xjj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.X2 (m q) (n q) (ell q) (w q) (sch q)
noncomputable def Zj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.Z1 (m q) (n q) (ell q) (w q)
noncomputable def Zjj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.Z2 (m q) (n q) (ell q) (w q) (sch q)
noncomputable def gj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.gamma1 (m q) (n q) (ell q) (w q)
noncomputable def gjj (q : (ℝ × ℝ) × ℝ) := EndpointAlgebra.gamma2 (m q) (n q) (ell q) (w q) (sch q)
noncomputable def gr := direction ((0,0),1) QuadraticCoordinates.gamma
noncomputable def grr := direction ((0,0),1) gr

end QuinticLienard.ModelEndpoint

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvatureJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus ModelEndpoint
noncomputable def ar := direction ((0,0),1) alpha
noncomputable def arr := direction ((0,0),1) ar
noncomputable def transport (f : (ℝ × ℝ) × ℝ → ℝ) (q : (ℝ × ℝ) × ℝ) : ℝ :=
  q.1.2*direction ((1,0),0) f q-alpha q*direction ((0,0),1) f q
end QuinticLienard.QuadraticCoordinates

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.QuadraticFit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open PartialCalculus QuadraticCoordinates ArcEndpoints

noncomputable def slope (q : (ℝ × ℝ) × ℝ) : ℝ := by
  classical
  exact if h : ∃ d, H ((d,q.1.1),q.1.2)=q.2 then h.choose else 0

end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SqrtPaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Filter Metric
open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.SmoothFlow
noncomputable def sqrtPath (u : Path ℝ) : Path ℝ where
  toFun t := Real.sqrt (u t)
  continuous_toFun := Real.continuous_sqrt.comp u.continuous
@[simp] lemma sqrtPath_apply (u : Path ℝ) (t : UnitInterval) : sqrtPath u t = Real.sqrt (u t) := rfl
@[simp] lemma sqrtPath_const (c : ℝ) : sqrtPath (constCLM c)=constCLM (Real.sqrt c) := rfl

end QuinticLienard.SmoothFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AlgebraicFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.SmoothFlow
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
noncomputable def pathMap {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) : Path E →L[ℝ] Path F :=
  ContinuousLinearMap.compLeftContinuous ℝ UnitInterval L
@[simp] lemma pathMap_apply {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (u : Path E) (s : UnitInterval) : pathMap L u s=L (u s) := rfl
@[simp] lemma pathMap_const {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x : E) : pathMap L (constCLM x)=constCLM (L x) := rfl
inductive AlgebraicExpr (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  | const : ℝ → AlgebraicExpr E
  | linear : (E →L[ℝ] ℝ) → AlgebraicExpr E
  | add : AlgebraicExpr E → AlgebraicExpr E → AlgebraicExpr E
  | mul : AlgebraicExpr E → AlgebraicExpr E → AlgebraicExpr E
  | inv : AlgebraicExpr E → AlgebraicExpr E
  | sqrt : AlgebraicExpr E → AlgebraicExpr E
namespace AlgebraicExpr
noncomputable def eval : AlgebraicExpr E → E → ℝ
  | const c, _ => c
  | linear L, x => L x
  | add p q,x => p.eval x+q.eval x
  | mul p q,x => p.eval x*q.eval x
  | inv p,x => (p.eval x)⁻¹
  | sqrt p,x => Real.sqrt (p.eval x)
def RegularAt : AlgebraicExpr E → E → Prop
  | const _,_ => True
  | linear _,_ => True
  | add p q,x => p.RegularAt x ∧ q.RegularAt x
  | mul p q,x => p.RegularAt x ∧ q.RegularAt x
  | inv p,x => p.RegularAt x ∧ p.eval x≠0
  | sqrt p,x => p.RegularAt x ∧ 0<p.eval x
noncomputable def onPaths : AlgebraicExpr E → Path E → Path ℝ
  | const c,_ => constCLM c
  | linear L,u => pathMap L u
  | add p q,u => p.onPaths u+q.onPaths u
  | mul p q,u => p.onPaths u*q.onPaths u
  | inv p,u => Ring.inverse (p.onPaths u)
  | sqrt p,u => sqrtPath (p.onPaths u)
end AlgebraicExpr

open ArcFamilies
end QuinticLienard.SmoothFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AlgebraicNotation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

namespace QuinticLienard.SmoothFlow.AlgebraicExpr
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
instance instAdd : Add (AlgebraicExpr E) := ⟨add⟩
instance instMul : Mul (AlgebraicExpr E) := ⟨mul⟩
instance instInv : Inv (AlgebraicExpr E) := ⟨inv⟩
instance instNeg : Neg (AlgebraicExpr E) := ⟨fun p => mul (const (-1)) p⟩
instance instSub : Sub (AlgebraicExpr E) := ⟨fun p q => p + -q⟩
instance instDiv : Div (AlgebraicExpr E) := ⟨fun p q => p*q⁻¹⟩
instance instOfNat (n : ℕ) : OfNat (AlgebraicExpr E) n := ⟨const n⟩
def pow (p : AlgebraicExpr E) : ℕ → AlgebraicExpr E
 | 0 => const 1
 | n+1 => pow p n*p
instance instPowNat : Pow (AlgebraicExpr E) ℕ := ⟨pow⟩
@[simp] lemma eval_const (c : ℝ) (x : E) : (const c : AlgebraicExpr E).eval x=c := rfl
@[simp] lemma eval_linear (L : E →L[ℝ] ℝ) (x : E) : (linear L).eval x=L x := rfl
@[simp] lemma eval_add (p q : AlgebraicExpr E) (x : E) : (p+q).eval x=p.eval x+q.eval x := rfl
@[simp] lemma eval_mul (p q : AlgebraicExpr E) (x : E) : (p*q).eval x=p.eval x*q.eval x := rfl
@[simp] lemma eval_inv (p : AlgebraicExpr E) (x : E) : p⁻¹.eval x=(p.eval x)⁻¹ := rfl
@[simp] lemma eval_neg (p : AlgebraicExpr E) (x : E) : (-p).eval x= -p.eval x := by change (-1:ℝ)*p.eval x= -p.eval x; ring
@[simp] lemma eval_sub (p q : AlgebraicExpr E) (x : E) : (p-q).eval x=p.eval x-q.eval x := by change (p+ -q).eval x=_; rw [eval_add,eval_neg,sub_eq_add_neg]
@[simp] lemma eval_div (p q : AlgebraicExpr E) (x : E) : (p/q).eval x=p.eval x/q.eval x := by change (p*q⁻¹).eval x=_; rw [eval_mul,eval_inv,div_eq_mul_inv]
@[simp] lemma eval_ofNat (n : ℕ) (x : E) : (OfNat.ofNat n : AlgebraicExpr E).eval x=n := rfl
@[simp] lemma eval_pow (p : AlgebraicExpr E) (n : ℕ) (x : E) : (p^n).eval x=(p.eval x)^n := by
  induction n with
  | zero =>
    rw [pow_zero]
    change (pow p 0).eval x=1
    rfl
  | succ n ih => change (p^n).eval x*p.eval x=_; rw [ih,pow_succ]
@[simp] lemma eval_sqrt (p : AlgebraicExpr E) (x : E) : (sqrt p).eval x=Real.sqrt (p.eval x) := rfl
@[simp] lemma regular_const (c : ℝ) (x : E) : (const c : AlgebraicExpr E).RegularAt x := trivial
@[simp] lemma regular_linear (L : E →L[ℝ] ℝ) (x : E) : (linear L).RegularAt x := trivial
@[simp] lemma regular_add (p q : AlgebraicExpr E) (x : E) : (p+q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x := Iff.rfl
@[simp] lemma regular_mul (p q : AlgebraicExpr E) (x : E) : (p*q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x := Iff.rfl
@[simp] lemma regular_inv (p : AlgebraicExpr E) (x : E) : p⁻¹.RegularAt x ↔ p.RegularAt x ∧ p.eval x≠0 := Iff.rfl
@[simp] lemma regular_neg (p : AlgebraicExpr E) (x : E) : (-p).RegularAt x ↔ p.RegularAt x := by change (True ∧ p.RegularAt x) ↔ p.RegularAt x; simp
@[simp] lemma regular_sub (p q : AlgebraicExpr E) (x : E) : (p-q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x := by change (p+ -q).RegularAt x ↔ _; rw [regular_add,regular_neg]
@[simp] lemma regular_div (p q : AlgebraicExpr E) (x : E) : (p/q).RegularAt x ↔ p.RegularAt x ∧ q.RegularAt x ∧ q.eval x≠0 := Iff.rfl
@[simp] lemma regular_ofNat (n : ℕ) (x : E) : (OfNat.ofNat n : AlgebraicExpr E).RegularAt x := trivial
@[simp] lemma regular_sqrt (p : AlgebraicExpr E) (x : E) : (sqrt p).RegularAt x ↔ p.RegularAt x ∧ 0<p.eval x := Iff.rfl
end QuinticLienard.SmoothFlow.AlgebraicExpr

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
open SmoothFlow SmoothFlow.AlgebraicExpr ArcFamilies
abbrev Params := (ℝ × ℝ) × ℝ
abbrev Dom := Params × ℝ
noncomputable def A : AlgebraicExpr Dom := linear
  ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ Params ℝ)))
noncomputable def ρ : AlgebraicExpr Dom := linear
  ((ContinuousLinearMap.snd ℝ ℝ ℝ).comp
    ((ContinuousLinearMap.fst ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ Params ℝ)))
noncomputable def ε : AlgebraicExpr Dom := linear
  ((ContinuousLinearMap.snd ℝ (ℝ×ℝ) ℝ).comp (ContinuousLinearMap.fst ℝ Params ℝ))
noncomputable def s : AlgebraicExpr Dom := linear (ContinuousLinearMap.snd ℝ Params ℝ)
noncomputable def X (c : ℝ) : AlgebraicExpr Dom := sqrt ((const 2)*(const c+A^2+ρ^2))
noncomputable def Z (c : ℝ) : AlgebraicExpr Dom := sqrt ((const 2)*(const c+A^2+ρ^2*s))
noncomputable def Δ : AlgebraicExpr Dom := ρ^2*(s-const 1)
noncomputable def C₁ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 1)+(const 2)*const (a 2)*x+(const 3)*const (a 3)*x^2+(const 4)*const (a 4)*x^3+(const 5)*const (a 5)*x^4
noncomputable def C₂ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 2)+(const 3)*const (a 3)*x+(const 6)*const (a 4)*x^2+(const 10)*const (a 5)*x^3
noncomputable def C₃ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 3)+(const 4)*const (a 4)*x+(const 10)*const (a 5)*x^2
noncomputable def C₄ (a : Fin 6 → ℝ) (x : AlgebraicExpr Dom) : AlgebraicExpr Dom :=
  const (a 4)+(const 5)*const (a 5)*x
noncomputable def K (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom := C₁ a (X c)/X c
noncomputable def B (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom :=
  (const 2)*C₂ a (X c)/(X c)^2-C₁ a (X c)/(X c)^3
noncomputable def Rem (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom :=
  -(const 2)*(C₂ a (X c)-C₁ a (X c)/((const 2)*X c))*(Z c+(const 3)*X c)/((X c)^2*(Z c+X c)^3)+
    (const 8)*C₃ a (X c)/(Z c+X c)^3+(const 16)*C₄ a (X c)*Δ/(Z c+X c)^4+
    (const 32)*const (a 5)*Δ^2/(Z c+X c)^5
noncomputable def η (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom := (s-const 1)^3*Rem a c
noncomputable def Expr (a : Fin 6 → ℝ) (c : ℝ) : AlgebraicExpr Dom :=
  ρ*K a c*(s-const 1)+ρ^3*B a c*(s-const 1)^2/(const 2)+ε*η a c
noncomputable def Φ (a : Fin 6 → ℝ) (c : ℝ) : Dom → ℝ := (Expr a c).eval

@[simp] lemma eval_A (q : Dom) : A.eval q=q.1.1.1 := rfl
@[simp] lemma eval_ρ (q : Dom) : ρ.eval q=q.1.1.2 := rfl
@[simp] lemma eval_ε (q : Dom) : ε.eval q=q.1.2 := rfl
@[simp] lemma eval_s (q : Dom) : s.eval q=q.2 := rfl
@[simp] lemma regular_A (q : Dom) : A.RegularAt q := trivial
@[simp] lemma regular_ρ (q : Dom) : ρ.RegularAt q := trivial
@[simp] lemma regular_ε (q : Dom) : ε.RegularAt q := trivial
@[simp] lemma regular_s (q : Dom) : s.RegularAt q := trivial
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
open SmoothFlow.AlgebraicExpr
noncomputable def poly (a : Fin 6 → ℝ) (x : ℝ) : ℝ :=
  a 0+a 1*x+a 2*x^2+a 3*x^3+a 4*x^4+a 5*x^5
noncomputable def c₁ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 1+2*a 2*x+3*a 3*x^2+4*a 4*x^3+5*a 5*x^4
noncomputable def c₂ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 2+3*a 3*x+6*a 4*x^2+10*a 5*x^3
noncomputable def c₃ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 3+4*a 4*x+10*a 5*x^2
noncomputable def c₄ (a : Fin 6 → ℝ) (x : ℝ) : ℝ := a 4+5*a 5*x
noncomputable def rem (a : Fin 6 → ℝ) (x z δ : ℝ) : ℝ :=
  -2*(c₂ a x-c₁ a x/(2*x))*(z+3*x)/(x^2*(z+x)^3)+8*c₃ a x/(z+x)^3+
    16*c₄ a x*δ/(z+x)^4+32*a 5*δ^2/(z+x)^5
@[simp] lemma eval_C₁ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₁ a x).eval q=c₁ a (x.eval q) := by simp [C₁,c₁]
@[simp] lemma eval_C₂ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₂ a x).eval q=c₂ a (x.eval q) := by simp [C₂,c₂]
@[simp] lemma eval_C₃ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₃ a x).eval q=c₃ a (x.eval q) := by simp [C₃,c₃]
@[simp] lemma eval_C₄ (a : Fin 6 → ℝ) (x : SmoothFlow.AlgebraicExpr Dom) (q : Dom) :
    (C₄ a x).eval q=c₄ a (x.eval q) := by simp [C₄,c₄]
@[simp] lemma eval_Rem (a : Fin 6 → ℝ) (c : ℝ) (q : Dom) :
    (Rem a c).eval q=rem a ((X c).eval q) ((Z c).eval q) (Δ.eval q) := by simp [Rem,rem]
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveWidth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcEndpoints ArcFamilies

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)

noncomputable def widthFamily (q : (P × ℝ) × ℝ) : ℝ :=
  width (fun u => Φ (q.1.1,u)) q.2 q.1.2
noncomputable def midpointFamily (q : (P × ℝ) × ℝ) : ℝ :=
  midpoint (fun u => Φ (q.1.1,u)) q.2 q.1.2

include hΦ hloc

noncomputable def peakAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  Classical.epsilon (fun t => q.1.2 < t ∧ widthFamily Φ ((q.1.1,t),q.1.2) = q.2)

noncomputable def midpointAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  midpointFamily Φ ((q.1.1,peakAtWidth Φ q),q.1.2)

end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveTransport
open ScalarArcs ArcEndpoints ArcFamilies PositiveWidth PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

noncomputable def M (p : P) (q : ℝ × ℝ) : ℝ := midpointAtWidth Φ ((p,q.1),q.2)
noncomputable def v (p : P) : ℝ × ℝ → ℝ := second (M Φ p)

end QuinticLienard.PositiveTransport

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ConditionalFit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open PartialCalculus QuadraticCoordinates ReferenceCharacteristic

noncomputable def conditionalV (q : (ℝ × ℝ) × ℝ) : ℝ := Hr ((slope q,q.1.1),q.1.2)

noncomputable def label (q : (ℝ × ℝ) × ℝ) : ℝ := by
  classical
  exact if h : ∃ z, A ((z,q.1.1),q.1.2)=q.2 then h.choose else 0

end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.HyperbolicCoordinate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
noncomputable def angle (x : ℝ) : ℝ := (Real.log (1+x)-Real.log (1-x))/2

@[simp] lemma angle_zero : angle 0=0 := by simp [angle]
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FitAngles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.ReferenceCharacteristic
open QuadraticCoordinates PartialCalculus
noncomputable def θ (q : (ℝ × ℝ) × ℝ) : ℝ := angle (A q)
noncomputable def L (q : (ℝ × ℝ) × ℝ) : ℝ := angle (D q)
end QuinticLienard.ReferenceCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.FitProperness
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open scoped Topology

open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic RealAnalysis

noncomputable def seqA (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := A ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqE (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := E ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqJ (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := J ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqL (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := L ((label ((((n:ℝ)+1),r),M),(n:ℝ)+1),s)
noncomputable def seqθ (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := angle (seqA r M n s)
noncomputable def seqg (r M : ℝ) (n : ℕ) (s : ℝ) : ℝ := s*(1-(seqA r M n s)^2)

end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.GlobalFit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open Set Filter
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticFit
open QuadraticCoordinates ReferenceCharacteristic

noncomputable def fitK (q : (ℝ × ℝ) × ℝ) : ℝ := by
  classical
  exact if h : ∃ k, conditionalV ((k,q.1.1),q.1.2)=q.2 then h.choose else 0
noncomputable def fitD (q : (ℝ × ℝ) × ℝ) : ℝ := slope ((fitK q,q.1.1),q.1.2)

end QuinticLienard.QuadraticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CubicVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveZero
open ScalarArcs ArcFamilies PositiveWidth PartialCalculus
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
include hΦ hloc

noncomputable def pathMidpoint (γ : ℝ → P) (h : ℝ) (q : ℝ × ℝ) : ℝ :=
  midpointAtWidth Φ ((γ q.1,h),q.2)
end QuinticLienard.PositiveZero

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveFit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveFit
open ScalarArcs ArcFamilies PositiveWidth PartialCalculus QuadraticFit
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0)=q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
noncomputable def m (h : ℝ) (q : P × ℝ) : ℝ := midpointAtWidth Φ ((q.1,h),q.2)
noncomputable def n (h : ℝ) : P × ℝ → ℝ := direction (0,1) (m Φ h)
noncomputable def d (h r : ℝ) (p : P) : ℝ := fitD ((r,m Φ h (p,r)),n Φ h (p,r))
noncomputable def k (h r : ℝ) (p : P) : ℝ := fitK ((r,m Φ h (p,r)),n Φ h (p,r))
end QuinticLienard.PositiveFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
open SmoothFlow.AlgebraicExpr PartialCalculus ArcFamilies
noncomputable def root (h : ℝ) : ℝ := Real.sqrt (2*h)
noncomputable def slope (a : Fin 6 → ℝ) (h : ℝ) : ℝ := c₁ a (root h)/root h
noncomputable def curvature (a : Fin 6 → ℝ) (h : ℝ) : ℝ :=
  2*c₂ a (root h)/(root h)^2-c₁ a (root h)/(root h)^3
noncomputable def third (a : Fin 6 → ℝ) (h : ℝ) : ℝ := 6*rem a (root h) (root h) 0
noncomputable def fitSlope (a : Fin 6 → ℝ) (c : ℝ) : Params → ℝ := PositiveFit.d (Φ a c) 1 1
noncomputable def fitCurvature (a : Fin 6 → ℝ) (c : ℝ) : Params → ℝ := PositiveFit.k (Φ a c) 1 1
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.OriginalProfile
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticProfile
open SmoothFlow SmoothFlow.AlgebraicExpr ArcFamilies ScaledProfile
noncomputable def xExpr : AlgebraicExpr (ℝ × ℝ) := sqrt (const 2*linear (ContinuousLinearMap.snd ℝ ℝ ℝ))
noncomputable def expr (a : Fin 6 → ℝ) : AlgebraicExpr (ℝ × ℝ) :=
  const (a 0)+const (a 1)*xExpr+const (a 2)*xExpr^2+const (a 3)*xExpr^3+
    const (a 4)*xExpr^4+const (a 5)*xExpr^5
noncomputable def profile (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := poly a (root q.2)
end QuinticLienard.QuinticProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter
open Set Filter Asymptotics
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.SmallWidth
open PartialCalculus
abbrev Space := (ℝ × ℝ) × ℝ
noncomputable def radial (F : Space → ℝ) : Space → ℝ := direction ((0,1),0) F
noncomputable def fiber (F : Space → ℝ) : Space → ℝ := direction ((0,0),1) F
noncomputable def correction (F : Space → ℝ) (q : ℝ × ℝ) : ℝ :=
  (F (q,q.2^5)-F (q,0))/q.2^3
end QuinticLienard.SmallWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ScaledActual
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticFit
open ScaledProfile
noncomputable def lambda (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := PositiveFit.d (QuinticProfile.profile a) q.1 q.2 0
noncomputable def kappa (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := PositiveFit.k (QuinticProfile.profile a) q.1 q.2 0
noncomputable def pull (_a : Fin 6 → ℝ) (c : ℝ) (q : SmallWidth.Space) : ScaledProfile.Params :=
  ((Real.sqrt (q.1.1-c-q.1.2^2),q.1.2),q.2)
noncomputable def pulledSlope (a : Fin 6 → ℝ) (c : ℝ) : SmallWidth.Space → ℝ := fitSlope a c ∘ pull a c
noncomputable def pulledCurvature (a : Fin 6 → ℝ) (c : ℝ) : SmallWidth.Space → ℝ := fitCurvature a c ∘ pull a c
end QuinticLienard.QuinticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualFitTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open scoped Topology
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticFit
open ScaledProfile PartialCalculus QuadraticCoordinates
noncomputable def M (a : Fin 6 → ℝ) : ℝ × ℝ → ℝ := PositiveTransport.M (QuinticProfile.profile a) 0
noncomputable def V (a : Fin 6 → ℝ) : ℝ × ℝ → ℝ := PositiveTransport.v (QuinticProfile.profile a) 0
noncomputable def fit (a : Fin 6 → ℝ) (q : ℝ × ℝ) : (ℝ × ℝ) × ℝ := ((lambda a q,kappa a q),q.2)
noncomputable def α (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ := q.2/(q.2^2-M a q^2)
noncomputable def D (a : Fin 6 → ℝ) (f : ℝ × ℝ → ℝ) (q : ℝ × ℝ) : ℝ := first f q-α a q*second f q
end QuinticLienard.QuinticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvatureTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuadraticCoordinates
open PartialCalculus
noncomputable def C (q : (ℝ × ℝ) × ℝ) : ℝ := R q/G q
noncomputable def Cr : (ℝ × ℝ) × ℝ → ℝ := direction ((0,0),1) C
noncomputable def Cd : (ℝ × ℝ) × ℝ → ℝ := direction ((1,0),0) C
noncomputable def Ck : (ℝ × ℝ) × ℝ → ℝ := direction ((0,1),0) C
end QuinticLienard.QuadraticCoordinates

namespace QuinticLienard.QuinticFit
open PartialCalculus QuadraticCoordinates
noncomputable def w (a : Fin 6 → ℝ) : ℝ × ℝ → ℝ := second (kappa a)
noncomputable def T (a : Fin 6 → ℝ) (q : ℝ × ℝ) : ℝ :=
  second (α a) q+C (fit a q)*Q (fit a q)/P (fit a q)-
    (Ck (fit a q)-Q (fit a q)/P (fit a q)*Cd (fit a q))*(lambda a q-ScaledProfile.slope a q.1)
end QuinticLienard.QuinticFit

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PositiveBase
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uP

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.PositiveWidth
open ScalarArcs ArcEndpoints ArcFamilies
variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
variable (Φ : P × ℝ → ℝ) (hΦ : ∀ q, 0<q.2 → ContDiffAt ℝ ω Φ q)
    (hloc : ∀ x : State P, 0<x.2.1 → ∃ f : State P × ℝ → State P,
      ContDiffAt ℝ ω f (x,0) ∧ ∀ᶠ q in 𝓝 (x,(0:ℝ)),
        f (q.1,0) = q.1 ∧ HasDerivAt (fun s => f (q.1,s)) (field Φ (f q)) q.2)
noncomputable def baseAtWidth (q : (P × ℝ) × ℝ) : ℝ :=
  Classical.epsilon (fun h => 0<h ∧ h<q.1.2 ∧ widthFamily Φ ((q.1.1,q.1.2),h)=q.2)
def Admissible (q : (P × ℝ) × ℝ) : Prop :=
  ∃ h, 0<h ∧ h<q.1.2 ∧ widthFamily Φ ((q.1.1,q.1.2),h)=q.2
end QuinticLienard.PositiveWidth

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualCharacteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuinticFit
noncomputable def b (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := PositiveWidth.baseAtWidth (QuinticProfile.profile a) ((0,t),s)
def Adm (a : Fin 6 → ℝ) (t s : ℝ) : Prop := PositiveWidth.Admissible (QuinticProfile.profile a) ((0,t),s)
noncomputable def point (a : Fin 6 → ℝ) (t s : ℝ) : ℝ × ℝ := (b a t s,s)
noncomputable def m (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := M a (point a t s)
noncomputable def v (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := V a (point a t s)
noncomputable def A (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := m a t s/s
noncomputable def g (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := s^2-(m a t s)^2
noncomputable def k (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := ScaledProfile.slope a (b a t s)
noncomputable def c (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := ScaledProfile.curvature a (b a t s)
noncomputable def L (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := angle (v a t s)
noncomputable def rate (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := 2*A a t s/(s*(1-(A a t s)^2))
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ActualError
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
noncomputable def j (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := QuadraticFit.slope ((κ,s),m a t s)
noncomputable def err (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := k a t s-j a t κ s
noncomputable def coeff (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := g a t s/(s*P ((j a t κ s,κ),s))
noncomputable def label (a : Fin 6 → ℝ) (t κ s : ℝ) : ℝ := QuadraticFit.label ((κ,s),A a t s)
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CurvaturePositive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
noncomputable def w (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := QuinticFit.w a (point a t s)
noncomputable def damp (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := g a t s/s*QuinticFit.T a (point a t s)
noncomputable def feed (a : Fin 6 → ℝ) (t s : ℝ) : ℝ := g a t s/s*Cr (QuinticFit.fit a (point a t s))*(QuinticFit.lambda a (point a t s)-k a t s)
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.Intercept
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.QuinticFit
open ScaledProfile QuadraticCoordinates PartialCalculus
noncomputable def intercept (a : Fin 6 → ℝ) (d : ℝ) (q : ℝ × ℝ) : ℝ := lambda a q-q.1*kappa a q-d
end QuinticLienard.QuinticFit
namespace QuinticLienard.ActualCharacteristic
open PartialCalculus QuadraticCoordinates
noncomputable def interceptRate (a : Fin 6 → ℝ) (t s : ℝ) : ℝ :=
  g a t s/s*((S (QuinticFit.fit a (point a t s))+b a t s*R (QuinticFit.fit a (point a t s)))/G (QuinticFit.fit a (point a t s)))*
    (QuinticFit.lambda a (point a t s)-k a t s)
end QuinticLienard.ActualCharacteristic

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs

noncomputable def axisLower (φ : ℝ → ℝ) (t : ℝ) : ℝ := sInf ((fun h=>lower φ h t) '' Ioo 0 t)
noncomputable def axisUpper (φ : ℝ → ℝ) (t : ℝ) : ℝ := sSup ((fun h=>upper φ h t) '' Ioo 0 t)
end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.BoundaryFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open Set Filter Metric
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter Metric
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open SmoothFlow SmoothFlow.AlgebraicExpr ScaledProfile
noncomputable def X : AlgebraicExpr (ℝ×ℝ) := linear (ContinuousLinearMap.fst ℝ ℝ ℝ)
noncomputable def Y : AlgebraicExpr (ℝ×ℝ) := linear (ContinuousLinearMap.snd ℝ ℝ ℝ)
noncomputable def polynomial (a : Fin 6 → ℝ) : AlgebraicExpr (ℝ×ℝ) :=
  const (a 0)+const (a 1)*X+const (a 2)*X^2+const (a 3)*X^3+const (a 4)*X^4+const (a 5)*X^5
noncomputable def rhs (a : Fin 6 → ℝ) : AlgebraicExpr (ℝ×ℝ) := X*(polynomial a+const (-1)*Y)⁻¹
noncomputable def field (a : Fin 6 → ℝ) (z : ℝ×ℝ) : ℝ×ℝ := (1,z.1/(poly a z.1-z.2))
def domain (a : Fin 6 → ℝ) : Set (ℝ×ℝ) := {z | poly a z.1-z.2≠0}
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisBranches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter
open Set Filter Metric
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScaledProfile ScalarArcs ArcFamilies PartialCalculus
noncomputable def φ (a : Fin 6 → ℝ) (h : ℝ) : ℝ := poly a (root h)
noncomputable def endpoint (a : Fin 6 → ℝ) (upper : Bool) (h t : ℝ) : ℝ :=
  if upper then ScalarArcs.upper (φ a) h t else lower (φ a) h t
noncomputable def branch (a : Fin 6 → ℝ) (upper : Bool) (q : ℝ×ℝ) : ℝ := endpoint a upper (q.2^2/2) q.1
noncomputable def axisEndpoint (a : Fin 6 → ℝ) (upper : Bool) (t : ℝ) : ℝ :=
  if upper then axisUpper (φ a) t else axisLower (φ a) t
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus

def transversePeaks (a : Fin 6 → ℝ) : Set ℝ :=
  {t | 0<t ∧ axisEndpoint a false t<poly a 0 ∧ poly a 0<axisEndpoint a true t}
noncomputable def axisWidth (a : Fin 6 → ℝ) (t : ℝ) : ℝ := (axisEndpoint a true t-axisEndpoint a false t)/2
noncomputable def axisCenter (a : Fin 6 → ℝ) (t : ℝ) : ℝ := (axisEndpoint a true t+axisEndpoint a false t)/2-poly a 0
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisWidthGerm
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth

def axisWidths (a : Fin 6 → ℝ) : Set ℝ := axisWidth a '' transversePeaks a
noncomputable def axisPeak (a : Fin 6 → ℝ) (r : ℝ) : ℝ :=
  Classical.epsilon (fun t=>t ∈ transversePeaks a ∧ axisWidth a t=r)
noncomputable def axisM (a : Fin 6 → ℝ) (r : ℝ) : ℝ := axisCenter a (axisPeak a r)
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisWidthRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth
noncomputable def axisV (a : Fin 6 → ℝ) (r : ℝ) : ℝ := deriv (axisM a) r
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisFit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs ScaledProfile PartialCalculus PositiveWidth QuadraticCoordinates
noncomputable def axisLambda (a : Fin 6 → ℝ) (r : ℝ) : ℝ := QuadraticFit.fitD ((r,axisM a r),axisV a r)
noncomputable def axisKappa (a : Fin 6 → ℝ) (r : ℝ) : ℝ := QuadraticFit.fitK ((r,axisM a r),axisV a r)
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisZeros
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open PartialCalculus QuadraticCoordinates QuadraticFit RealAnalysis

def matchingDomain (a b : Fin 6 → ℝ) : Set ℝ := axisWidths a ∩ axisWidths b
noncomputable def matchingDelta (a b : Fin 6 → ℝ) (r : ℝ) : ℝ := axisM a r-axisM b r
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisSecants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open PartialCalculus QuadraticFit QuadraticCoordinates RealAnalysis
noncomputable def Vm : (ℝ×ℝ)×ℝ → ℝ := direction ((0,0),1) conditionalV
noncomputable def Vk : (ℝ×ℝ)×ℝ → ℝ := direction ((1,0),0) conditionalV
noncomputable def mSegment (a b : Fin 6 → ℝ) (q : ℝ×ℝ) : (ℝ×ℝ)×ℝ :=
  ((axisKappa a q.1,q.1),axisM b q.1+q.2*(axisM a q.1-axisM b q.1))
noncomputable def kSegment (a b : Fin 6 → ℝ) (q : ℝ×ℝ) : (ℝ×ℝ)×ℝ :=
  ((axisKappa b q.1+q.2*(axisKappa a q.1-axisKappa b q.1),q.1),axisM b q.1)
noncomputable def secantA (a b : Fin 6 → ℝ) (r : ℝ) : ℝ := ∫ s : ℝ in (0:ℝ)..1,Vm (mSegment a b (r,s))
noncomputable def secantB (a b : Fin 6 → ℝ) (r : ℝ) : ℝ := ∫ s : ℝ in (0:ℝ)..1,Vk (kSegment a b (r,s))
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.AxisIntercept
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.AxisFlow
open ScalarArcs PositiveWidth ScaledProfile PartialCalculus QuadraticCoordinates
noncomputable def heightWidth (a : Fin 6 → ℝ) (t h : ℝ) : ℝ := widthFamily (QuinticProfile.profile a) ((0,t),h)
end QuinticLienard.AxisFlow

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CoefficientCases
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScaledProfile
noncomputable def reflectX (a : Fin 6 → ℝ) : Fin 6 → ℝ := ![a 0,-a 1,a 2,-a 3,a 4,-a 5]
@[simp] lemma reflectX_one (a : Fin 6 → ℝ) : reflectX a 1= -a 1 := rfl
@[simp] lemma reflectX_two (a : Fin 6 → ℝ) : reflectX a 2=a 2 := rfl
@[simp] lemma reflectX_three (a : Fin 6 → ℝ) : reflectX a 3= -a 3 := rfl
@[simp] lemma reflectX_four (a : Fin 6 → ℝ) : reflectX a 4=a 4 := rfl
@[simp] lemma reflectX_five (a : Fin 6 → ℝ) : reflectX a 5= -a 5 := rfl
end QuinticLienard.ScaledProfile

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SharpFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology NNReal

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open SmoothFlow SmoothFlow.AlgebraicExpr GlobalODE PartialCalculus
abbrev Space := ℝ × (Plane × ℝ)
noncomputable def f (x : ℝ) : ℝ := 4*x-(20/3)*x^3+(8/5)*x^5
noncomputable def V (z : Space) : Space := (0,((z.2.1.2-z.1*f z.2.1.1,-z.2.1.1),-z.2.1.1*f z.2.1.1))
noncomputable def X : AlgebraicExpr Space := linear ((ContinuousLinearMap.fst ℝ ℝ ℝ).comp ((ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ))))
noncomputable def Eps : AlgebraicExpr Space := linear (ContinuousLinearMap.fst ℝ ℝ (Plane × ℝ))
noncomputable def polynomial : AlgebraicExpr Space := const 4*X+const (-(20/3))*X^3+const (8/5)*X^5
noncomputable def I2 (t : ℝ) : ℝ := t/2-Real.sin t*Real.cos t/2
noncomputable def I4 (t : ℝ) : ℝ := (3/4)*I2 t-(Real.sin t)^3*Real.cos t/4
noncomputable def I6 (t : ℝ) : ℝ := (5/6)*I4 t-(Real.sin t)^5*Real.cos t/6
noncomputable def q (s t : ℝ) : ℝ := -4*s^2*I2 t+(20/3)*s^4*I4 t-(8/5)*s^6*I6 t
noncomputable def circle (s t : ℝ) : Space := (0,((s*Real.sin t,s*Real.cos t),q s t))
@[simp] lemma circle_zero (s : ℝ) : circle s 0=(0,((0,s),0)) := by simp [circle,q,I2,I4,I6]
end QuinticLienard.Sharpness

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SharpReturn
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open GlobalODE PartialCalculus
noncomputable def turn : ℝ := 2*Real.pi
noncomputable def initial (p : ℝ × ℝ) : Space := (p.1,((0,p.2),0))
structure ReturnFamily where
  W : Space → Space
  K : ℝ≥0
  L : ℝ≥0
  lip : LipschitzWith K W
  bound : ∀ x,‖W x‖≤L
  σ : (ℝ × ℝ) → ℝ
noncomputable def ReturnFamily.path (R : ReturnFamily) (p : ℝ × ℝ) (t : ℝ) : Space :=
  flow R.W R.lip R.bound (initial p) t
noncomputable def ReturnFamily.Q (R : ReturnFamily) (p : ℝ × ℝ) : ℝ := (R.path p (R.σ p)).2.2
@[simp] lemma ReturnFamily.path_zero (R : ReturnFamily) (p : ℝ × ℝ) : R.path p 0=initial p := by simp [ReturnFamily.path]
end QuinticLienard.Sharpness

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SharpPhysical
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open scoped Topology
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open GlobalODE PartialCalculus
noncomputable def F (ε : ℝ) : Polynomial ℝ := Polynomial.C ε *
  (Polynomial.C 4*Polynomial.X-Polynomial.C (20/3)*Polynomial.X^3+Polynomial.C (8/5)*Polynomial.X^5)
noncomputable def project : Space →L[ℝ] Plane := (ContinuousLinearMap.fst ℝ Plane ℝ).comp (ContinuousLinearMap.snd ℝ ℝ (Plane × ℝ))
end QuinticLienard.Sharpness

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ExcursionGraph
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology ContDiff
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open RealAnalysis ScaledProfile AxisFlow

structure IsRightExcursion (z : ℝ → Plane) (s t : ℝ) : Prop where
  lt : s<t
  left : (z s).1=0
  right : (z t).1=0
  positive : ∀ v ∈ Ioo s t,0<(z v).1
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.PeriodicSymmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
noncomputable def polynomialReflect (F : Polynomial ℝ) : Polynomial ℝ := F.comp (-Polynomial.X)
@[simp] lemma polynomialReflect_eval (F : Polynomial ℝ) (x : ℝ) : (polynomialReflect F).eval x=F.eval (-x) := by
  simp [polynomialReflect]
def reverseY (z : ℝ → Plane) (t : ℝ) : Plane := ((z (-t)).1,-(z (-t)).2)
def reverseX (z : ℝ → Plane) (t : ℝ) : Plane := (-(z (-t)).1,(z (-t)).2)
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.OpenArch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard.ScalarArcs

structure IsOpenArch (φ u : ℝ → ℝ) (A B : ℝ) : Prop where
  lt : A<B
  continuous : Continuous u
  left : u A=0
  right : u B=0
  positive : ∀ y ∈ Ioo A B,0<u y
  equation : ∀ y ∈ Ioo A B,HasDerivAt u (φ (u y)-y) y
end QuinticLienard.ScalarArcs

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.ReturnNeighborhood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard
open ScaledProfile GlobalODE PartialCalculus
structure ReturnFlow where
  W : Plane → Plane
  K : ℝ≥0
  L : ℝ≥0
  lip : LipschitzWith K W
  bound : ∀ x,‖W x‖≤L
  τ : ℝ → ℝ
  σ : ℝ → ℝ
noncomputable def ReturnFlow.path (R : ReturnFlow) (s t : ℝ) : Plane := flow R.W R.lip R.bound (0,s) t
@[simp] lemma ReturnFlow.path_zero (R : ReturnFlow) (s : ℝ) : R.path s 0=(0,s) := by simp [ReturnFlow.path]
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CaseOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff NNReal

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile ScalarArcs AxisFlow RealAnalysis
noncomputable def oddPart (a : Fin 6 → ℝ) (u : ℝ) : ℝ := a 1*root u+a 3*(root u)^3+a 5*(root u)^5
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.CycleTransform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology
namespace QuinticLienard
noncomputable def flipY : Plane ≃ₜ Plane where
  toFun p := (p.1,-p.2)
  invFun p := (p.1,-p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := continuous_fst.prodMk continuous_snd.neg
  continuous_invFun := continuous_fst.prodMk continuous_snd.neg
@[simp] lemma flipY_apply (p : Plane) : flipY p=(p.1,-p.2) := rfl
@[simp] lemma flipY_symm : flipY.symm=flipY := rfl
end QuinticLienard

end OAI
end

section
-- module Solutions.OAIQW_QuinticLienard.SharpCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology
open Set Filter
open scoped Topology ContDiff

open Set Filter
open scoped Topology ContDiff NNReal
namespace QuinticLienard.Sharpness
open GlobalODE PartialCalculus
noncomputable def average (s : ℝ) : ℝ := -Real.pi*s^2*(4-5*s^2+s^4)

def ReturnFamily.Good (R : ReturnFamily) (p : ℝ × ℝ) : Prop :=
  0<R.σ p ∧ (R.path p (R.σ p)).2.1.1=0 ∧
    0<(R.path p (R.σ p)).2.1.2 ∧ 0<p.2 ∧ R.σ p<turn+1 ∧
    ∀ t ∈ Icc (-1) (turn+1),R.W (R.path p t)=V (R.path p t)
end QuinticLienard.Sharpness

end OAI
end


