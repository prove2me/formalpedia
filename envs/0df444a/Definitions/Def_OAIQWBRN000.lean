-- Prove2me | Definitions.Def_OAIQWBRN000
-- name    : OAIQWBRN000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T20:25:42.060452+00:00
-- url     : https://prove2.me/theorems/6e0ca8b0-6a13-4ae2-818d-3d7ec46778ae
-- title:
--   OpenAI Brennan split: definitions bundle
-- statement:
--   The definitions bundle of the split of OpenAI's proof of `OAI.Brennan.main_theorem`. That theorem covers Brennan's conjecture, the uniform inverse-square integral-means bound and $B_{\mathcal S}(-2) = 1$ for the schlicht class, and the area integrability of $|f'|^t$ for $-2 < t < 2/3$. The bundle holds OpenAI's Lean definitions, structures and instances from `lean/OAI/Analysis/IntegralMeans` (OpenAI, *Brennan's conjecture and sharp inverse-square integral means*, OpenAI Math Release, September 24, 2026, result family 072, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with OpenAI's `@[simp]` lemmas about them. Among them:
--   - the compact class `DiskClass` of normalized univalent disk maps and its half-plane model `classFun`;
--   - the rebasings `rerootClass` and the weights `classWeight`;
--   - the dyadic `transferOperator`;
--   - the law condition `HasWeightedLaw`;
--   - the critical map `criticalMap` and `normalizedJacobian`.
--
--   The bundle also contains the lemmas those definitions use in their bodies. Several definitions (the transfer operator and the positive functionals on $C(\texttt{DiskClass}, \mathbb R)$) need the instance `CompactSpace DiskClass`. Its proof, `isCompact_diskSchlichtSet`, is the compactness of the class $\mathcal S$: Arzelà–Ascoli together with closedness under locally uniform limits. That proof rests on the Koebe distortion theorem, Bieberbach's $|a_2| \le 2$ in the form $|f''(0)| \le 4$, Gronwall's coefficient bound and the Koebe one-quarter theorem. All of these are published as standalone statements: `OAI.StrictInverseFirstPower.derivative_distortion`, `second_coefficient_le_two`, `pole_coefficient_le_one`, `koebe_quarter`, and `OAI.Brennan.isCompact_univalent_restrictions`.
--
--   A definitions bundle cannot import theorem statements, so this bundle re-proves them under OpenAI's own names, because the compactness instance of the definitions needs them: `schlicht_deriv_bounds`, `schlicht_second_deriv_bound`, `meromorphic_univalent_coefficient`, `schlicht_quarter` and `isCompact_diskSchlichtSet`, all in `OAI.Brennan`. None of these names is the name of a published statement, so the bundle and those statements can be imported together. The growth theorem is not needed by any definition: the proofs of this split import it as the published statement `OAI.Brennan.univalent_growth_upper`.
--
--   The definitions of the published goal (`disk`, `UnivalentOn`, `Schlicht`, `integralMean`, `beta`, `spectrum`, `SphericalBoundaryNontrivial`, `MainStatement`) are not repeated: the bundle imports them from the published bundle `Def_Brennan`. It also imports `diskExtend`, `diskSchlichtSet` and `ballNormalize` from the bundle `OAIQWBRNK000` of the classical Brennan statements, and no other bundle.
--
--   The theorems the definitions do not need are proved in the two solutions of this split. One proves the published intermediate statement `OAI.Brennan.jacobian_expectation_nonpos`, and the other proves `OAI.Brennan.main_theorem` from it. The split exists because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, Brennan's conjecture and sharp inverse-square integral means, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 072; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Brennans-conjecture-and-sharp-inverse-square-integral-means-September-24-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Analysis/IntegralMeans at commit adc7f12

import Mathlib
import Definitions.Def_Brennan
import Definitions.Def_OAIQWBRNK000

section
-- module Solutions.OAIQW_Brennan.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_Brennan.LogIncrement
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def HasLogIncrement (γ : C(unitInterval, ℂ)) (q : ℂ) : Prop :=
  ∃ T : C(unitInterval, ℂ), (∀ t, Complex.exp (T t) = γ t) ∧ T 1-T 0 = q

lemma HasLogIncrement.perturb {γ η : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0)
    (h : ∀ t, ‖η t-γ t‖ < ‖γ t‖) : HasLogIncrement η q := by
  obtain ⟨T,hT,hend⟩ := hγ
  have hn (t) : γ t ≠ 0 := (hT t ▸ Complex.exp_ne_zero (T t))
  have hratio (t) : η t / γ t ∈ Complex.slitPlane := by
    have he : η t / γ t = 1 + (η t-γ t)/γ t := by field_simp [hn t]; ring
    rw [he]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hn t))]
    exact h t
  let R : C(unitInterval, ℂ) := ⟨fun t => Complex.log (η t / γ t), by
    apply Continuous.clog
    · exact η.continuous.div γ.continuous hn
    · exact hratio⟩
  refine ⟨T+R, ?_, ?_⟩
  · intro t
    change Complex.exp (T t+Complex.log (η t/γ t)) = η t
    rw [Complex.exp_add, hT t, Complex.exp_log (Complex.slitPlane_ne_zero (hratio t))]
    field_simp [hn t]
  · change (T 1+Complex.log (η 1/γ 1))-(T 0+Complex.log (η 0/γ 0))=q
    rw [hloopγ,hloopη]
    linear_combination hend

def circleLoop : C(unitInterval, ℂ) :=
  ⟨fun t => Complex.exp ((2*Real.pi*(t : ℝ) : ℝ)*Complex.I), by fun_prop⟩

@[simp] lemma circleLoop_zero : circleLoop 0 = 1 := by simp [circleLoop]

@[simp] lemma circleLoop_one : circleLoop 1 = 1 := by
  simp [circleLoop, Complex.exp_two_pi_mul_I]

@[simp] lemma norm_circleLoop (t : unitInterval) : ‖circleLoop t‖ = 1 := by
  simp [circleLoop, Complex.norm_exp]

lemma circleLoop_logIncrement (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement (a • circleLoop) (2*Real.pi*Complex.I) := by
  refine ⟨⟨fun t => Complex.log a+(2*Real.pi*(t : ℝ) : ℝ)*Complex.I, by fun_prop⟩, ?_, ?_⟩
  · intro t
    simp [Complex.exp_add, Complex.exp_log ha, circleLoop]
  · simp

def linearPart (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1-Complex.I*A Complex.I)/2

def antiLinearPart (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1+Complex.I*A Complex.I)/2

lemma realLinear_decomposition (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = linearPart A*z+antiLinearPart A*conj z := by
  have he : z = z.re • (1 : ℂ)+z.im • Complex.I := by simp [Complex.real_smul]
  calc
    A z = z.re • A 1+z.im • A Complex.I := by
      conv_lhs => rw [he, map_add, map_smul, map_smul]
    _ = linearPart A*z+antiLinearPart A*conj z := by
      apply Complex.ext <;>
        simp [linearPart, antiLinearPart, Complex.mul_re, Complex.mul_im,
          Complex.real_smul] <;> ring

lemma determinant_complex_real (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re*(A Complex.I).im-(A Complex.I).re*(A 1).im := by
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]

lemma det_eq_linearParts (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det A.toLinearMap = ‖linearPart A‖^2-‖antiLinearPart A‖^2 := by
  rw [determinant_complex_real]
  simp only [← Complex.normSq_eq_norm_sq, linearPart, antiLinearPart,
    Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  ring

lemma HasLogIncrement.smul {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) {c : ℂ} (hc : c ≠ 0) :
    HasLogIncrement (c • γ) q := by
  obtain ⟨T,hT,hend⟩ := hγ
  refine ⟨T+ContinuousMap.const _ (Complex.log c), ?_, ?_⟩
  · intro t
    change Complex.exp (T t+Complex.log c) = c*γ t
    rw [Complex.exp_add, hT t, Complex.exp_log hc, mul_comm]
  · change (T 1+Complex.log c)-(T 0+Complex.log c)=q
    linear_combination hend

lemma exists_log_lift (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    ∃ T : C(unitInterval, ℂ), ∀ t, Complex.exp (T t) = γ t := by
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨T, ⟨-,hT⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    γ (Complex.exp_log (hγ 0)) hγ
  exact ⟨T, fun t => congrFun hT t⟩

lemma log_lifts_difference_constant.{u_1} {X : Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B : X → ℂ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, Complex.exp (A x) = Complex.exp (B x)) (x y : X) :
    A y - B y = A x - B x := by
  have hC : Continuous (fun z => B z + (A x - B x)) := hB.add continuous_const
  have he (z) : Complex.exp (A z) = Complex.exp (B z + (A x - B x)) := by
    rw [Complex.exp_add, Complex.exp_sub, h x, div_self (Complex.exp_ne_zero _), mul_one]
    exact h z
  have heq : A = fun z => B z + (A x - B x) :=
    Complex.isCoveringMap_exp.eq_of_comp_eq hA hC
      (by funext z; exact Subtype.ext (he z)) x (by ring)
  have hy := congrFun heq y
  linear_combination hy

lemma HasLogIncrement.unique {γ : C(unitInterval, ℂ)} {p q : ℂ}
    (hp : HasLogIncrement γ p) (hq : HasLogIncrement γ q) : p = q := by
  obtain ⟨A,hA,hp⟩ := hp
  obtain ⟨B,hB,hq⟩ := hq
  have he := log_lifts_difference_constant A.continuous B.continuous
    (fun t => (hA t).trans (hB t).symm) (0 : unitInterval) 1
  linear_combination hp.symm - hq.symm + he

lemma HasLogIncrement.mul {γ η : C(unitInterval, ℂ)} {p q : ℂ}
    (hγ : HasLogIncrement γ p) (hη : HasLogIncrement η q) :
    HasLogIncrement (γ * η) (p + q) := by
  obtain ⟨A,hA,hp⟩ := hγ
  obtain ⟨B,hB,hq⟩ := hη
  refine ⟨A+B, ?_, ?_⟩
  · intro t
    change Complex.exp (A t+B t) = γ t * η t
    rw [Complex.exp_add, hA t, hB t]
  · change (A 1+B 1)-(A 0+B 0)=p+q
    linear_combination hp+hq

lemma HasLogIncrement.inv {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => (γ t)⁻¹, by
      exact γ.continuous.inv₀ (fun t => by
        obtain ⟨A,hA,-⟩ := hγ
        exact (hA t ▸ Complex.exp_ne_zero (A t)))⟩ (-q) := by
  obtain ⟨A,hA,hq⟩ := hγ
  refine ⟨-A, ?_, ?_⟩
  · intro t
    change Complex.exp (-A t) = (γ t)⁻¹
    rw [Complex.exp_neg, hA t]
  · change -A 1-(-A 0) = -q
    linear_combination -hq

lemma HasLogIncrement.conj {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => conj (γ t), by fun_prop⟩ (conj q) := by
  obtain ⟨A,hA,hq⟩ := hγ
  refine ⟨⟨fun t => conj (A t), by fun_prop⟩, ?_, ?_⟩
  · intro t
    exact (Complex.exp_conj _).trans (congrArg conj (hA t))
  · change conj (A 1)-conj (A 0)=conj q
    rw [← map_sub, hq]

lemma HasLogIncrement.integer {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) (hloop : γ 1 = γ 0) :
    ∃ n : ℤ, q = n*(2*Real.pi*Complex.I) := by
  obtain ⟨A,hA,hq⟩ := hγ
  apply Complex.exp_eq_one_iff.mp
  rw [← hq, Complex.exp_sub, hA 1, hA 0, hloop,
    div_self (hA 0 ▸ Complex.exp_ne_zero _)]

lemma period_ne_zero : (2*Real.pi*Complex.I : ℂ) ≠ 0 := by
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero

lemma integer_period_injective : Function.Injective
    (fun n : ℤ => (n : ℂ)*(2*Real.pi*Complex.I)) := by
  intro n m h
  exact_mod_cast (mul_right_cancel₀ period_ne_zero h : (n : ℂ) = m)

lemma exists_integer_logIncrement (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ≠ 0) :
    ∃ n : ℤ, HasLogIncrement γ (n*(2*Real.pi*Complex.I)) := by
  obtain ⟨A, hA⟩ := exists_log_lift γ hγ
  have hi : HasLogIncrement γ (A 1-A 0) := ⟨A,hA,rfl⟩
  obtain ⟨n,hn⟩ := hi.integer hloop
  exact ⟨n, hn ▸ hi⟩

def windingNumber (γ : C(unitInterval, ℂ)) : ℤ := by
  classical
  exact if h : γ 1 = γ 0 ∧ ∀ t, γ t ≠ 0 then
    Classical.choose (exists_integer_logIncrement γ h.1 h.2)
  else 0

lemma windingNumber_spec (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ≠ 0) :
    HasLogIncrement γ ((windingNumber γ)*(2*Real.pi*Complex.I)) := by
  rw [windingNumber, dite_eq_left ⟨hloop,hγ⟩]
  exact Classical.choose_spec (exists_integer_logIncrement γ hloop hγ)

lemma windingNumber_eq_of_logIncrement {γ : C(unitInterval, ℂ)} {n : ℤ}
    (hloop : γ 1 = γ 0) (h : HasLogIncrement γ (n*(2*Real.pi*Complex.I))) :
    windingNumber γ = n := by
  have hn (t) : γ t ≠ 0 := by
    obtain ⟨A,hA,-⟩ := h
    exact hA t ▸ Complex.exp_ne_zero _
  exact integer_period_injective ((windingNumber_spec γ hloop hn).unique h)

lemma windingNumber_mul (γ η : C(unitInterval, ℂ))
    (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0)
    (hγ : ∀ t, γ t ≠ 0) (hη : ∀ t, η t ≠ 0) :
    windingNumber (γ*η) = windingNumber γ + windingNumber η := by
  apply windingNumber_eq_of_logIncrement (by simp [hloopγ,hloopη])
  convert (windingNumber_spec γ hloopγ hγ).mul (windingNumber_spec η hloopη hη) using 1
  push_cast
  ring

lemma windingNumber_perturb {γ η : C(unitInterval, ℂ)}
    (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0) (hγ : ∀ t, γ t ≠ 0)
    (h : ∀ t, ‖η t-γ t‖ < ‖γ t‖) : windingNumber η = windingNumber γ :=
  windingNumber_eq_of_logIncrement hloopη
    ((windingNumber_spec γ hloopγ hγ).perturb hloopγ hloopη h)

lemma exists_log_lift_of_simplyConnected.{u_1} {X : Type u_1} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocallyPathConnectedSpace X] (x : X)
    (f : C(X, ℂ)) (hf : ∀ y, f y ≠ 0) :
    ∃ A : C(X, ℂ), ∀ y, Complex.exp (A y) = f y := by
  obtain ⟨A, ⟨-,hA⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    f (Complex.exp_log (hf x)) hf
  exact ⟨A, fun y => congrFun hA y⟩

def loopIndex (γ : C(unitInterval, ℂ)) (a : ℂ) : ℤ :=
  windingNumber ⟨fun t => γ t-a, by fun_prop⟩

def windingInterior (γ : C(unitInterval, ℂ)) : Set ℂ :=
  {a | a ∉ range γ ∧ loopIndex γ a ≠ 0}

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Degree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def orientedDifference (positive : Bool) (a z : ℂ) : ℂ :=
  if positive then z-a else conj (z-a)

@[simp] lemma norm_orientedDifference (p : Bool) (a z : ℂ) :
    ‖orientedDifference p a z‖ = ‖z-a‖ := by cases p <;> simp only [orientedDifference, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]

@[simp] lemma orientedDifference_eq_zero (p : Bool) (a z : ℂ) :
    orientedDifference p a z = 0 ↔ z = a := by
  rw [← norm_eq_zero, norm_orientedDifference, norm_eq_zero, sub_eq_zero]

lemma continuous_orientedDifference (p : Bool) (a : ℂ) :
    Continuous (orientedDifference p a) := by
  unfold orientedDifference
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop

def radialCutoff (a : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 (2-2*‖z-a‖/r))

lemma continuous_radialCutoff (a : ℂ) (r : ℝ) : Continuous (radialCutoff a r) := by
  unfold radialCutoff
  fun_prop

lemma radialCutoff_one {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z-a‖ ≤ r/2) :
    radialCutoff a r z = 1 := by
  have hb : 2*‖z-a‖/r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
  simp [radialCutoff, min_eq_left (by linarith : 1 ≤ 2-2*‖z-a‖/r)]

lemma radialCutoff_zero {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z-a‖) :
    radialCutoff a r z = 0 := by
  rw [radialCutoff, max_eq_left]
  apply min_le_of_right_le
  rw [sub_nonpos, le_div_iff₀ hr]
  linarith

def surgeryLog (X : ℂ → ℂ) (p : Bool) (a c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (radialCutoff a r z : ℂ) * Complex.log (X z / (c*orientedDifference p a z))

lemma continuousAt_surgeryLog {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c z : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0) (hz : z ≠ a)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    ContinuousAt (surgeryLog X p a c r) z := by
  by_cases hb : ‖z-a‖ < 2*r
  · apply (Complex.continuous_ofReal.comp (continuous_radialCutoff a r)).continuousAt.mul
    apply ContinuousAt.clog
    · exact hX.continuousAt.div
        (continuous_const.mul (continuous_orientedDifference p a)).continuousAt
        (mul_ne_zero hc (mt (orientedDifference_eq_zero p a z).mp hz))
    · exact hlocal z hb hz
  · have hlt : r < ‖z-a‖ := by linarith
    have he : surgeryLog X p a c r =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [((show ContinuousAt (fun w : ℂ => ‖w-a‖) z by fun_prop).eventually
        (Ioi_mem_nhds hlt))] with w hw
      simp [surgeryLog, radialCutoff_zero hr (le_of_lt hw)]
    exact continuousAt_const.congr he.symm

lemma surgeryLog_eq_zero_eventually {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : r < ‖z-a‖) : surgeryLog X p a c r =ᶠ[𝓝 z] fun _ => 0 := by
  filter_upwards [((show ContinuousAt (fun w : ℂ => ‖w-a‖) z by fun_prop).eventually
    (Ioi_mem_nhds hz))] with w hw
  simp [surgeryLog, radialCutoff_zero hr (le_of_lt hw)]

def removeZero (X : ℂ → ℂ) (p : Bool) (a c : ℂ) (r : ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z = a then c else X z / orientedDifference p a z *
    Complex.exp (-surgeryLog X p a c r z)

lemma removeZero_eq_const_near {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : c ≠ 0) (hz : ‖z-a‖ < r/2)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    removeZero X p a c r z = c := by
  classical
  by_cases hza : z = a
  · simp [removeZero,hza]
  · have hd : orientedDifference p a z ≠ 0 := mt (orientedDifference_eq_zero p a z).mp hza
    have hslit := hlocal z (by linarith) hza
    have hx : X z ≠ 0 := by
      intro hx
      simpa [hx] using Complex.slitPlane_ne_zero hslit
    simp only [removeZero, ite_eq_right hza, surgeryLog, radialCutoff_one hr hz.le,
      Complex.ofReal_one, one_mul, Complex.exp_neg,
      Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
    field_simp

lemma continuous_removeZero {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    Continuous (removeZero X p a c r) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = a
  · subst z
    have he : removeZero X p a c r =ᶠ[𝓝 a] fun _ => c := by
      filter_upwards [Metric.ball_mem_nhds a (by positivity : 0 < r/2)] with w hw
      exact removeZero_eq_const_near hr hc (by simpa [Metric.mem_ball,dist_eq_norm] using hw) hlocal
    exact continuousAt_const.congr he.symm
  · have he : removeZero X p a c r =ᶠ[𝓝 z] fun w =>
        X w / orientedDifference p a w * Complex.exp (-surgeryLog X p a c r w) := by
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
      have hwn : w ≠ a := hw
      simp [removeZero,hwn]
    apply ContinuousAt.congr ?_ he.symm
    exact (hX.continuousAt.div (continuous_orientedDifference p a).continuousAt
      (mt (orientedDifference_eq_zero p a z).mp hz)).mul
      ((continuousAt_surgeryLog hX hr hc hz hlocal).neg.cexp)

lemma removeZero_eq_zero_iff {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hc : c ≠ 0) : removeZero X p a c r z = 0 ↔ X z = 0 ∧ z ≠ a := by
  classical
  by_cases hz : z = a
  · simp [removeZero,hz,hc]
  · simp [removeZero,hz,div_eq_zero_iff,
      mt (orientedDifference_eq_zero p a z).mp hz,Complex.exp_ne_zero]

lemma removeZero_factorization {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hz : z ≠ a) : X z = orientedDifference p a z * removeZero X p a c r z *
      Complex.exp (surgeryLog X p a c r z) := by
  classical
  have hd : orientedDifference p a z ≠ 0 := mt (orientedDifference_eq_zero p a z).mp hz
  simp only [removeZero,ite_eq_right hz,Complex.exp_neg]
  field_simp

lemma exists_slit_radius_of_derivative {X : ℂ → ℂ} {a c : ℂ} {A : ℂ →L[ℝ] ℂ}
    {p : Bool} (hzero : X a = 0) (hd : HasFDerivAt X A a)
    {b : ℝ} (hb : b < ‖c‖)
    (herr : ∀ w : ℂ, ‖A w-c*orientedDifference p 0 w‖ ≤ b*‖w‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane := by
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound
    (by linarith : 0 < (‖c‖-b)/2)
  obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp hrem
  refine ⟨δ/3, by positivity, fun w hw hwa => ?_⟩
  have hwn : 0 < ‖w-a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwa)
  have hremw := hbound (show dist (w-a) 0 < δ by simpa only [dist_zero_right] using (show ‖w-a‖ < δ by linarith))
  simp only [add_sub_cancel, hzero, sub_zero] at hremw
  have her := herr (w-a)
  have he : orientedDifference p 0 (w-a) = orientedDifference p a w := by
    simp [orientedDifference]
  rw [he] at her
  have hlt : ‖X w-c*orientedDifference p a w‖ < ‖c*orientedDifference p a w‖ := by
    calc
      ‖X w-c*orientedDifference p a w‖ =
          ‖(X w-A (w-a))+(A (w-a)-c*orientedDifference p a w)‖ := by congr 1; ring
      _ ≤ ‖X w-A (w-a)‖+‖A (w-a)-c*orientedDifference p a w‖ := norm_add_le _ _
      _ ≤ (‖c‖-b)/2*‖w-a‖+b*‖w-a‖ := add_le_add hremw her
      _ < ‖c*orientedDifference p a w‖ := by
        rw [norm_mul,norm_orientedDifference]
        nlinarith
  have hcn : c*orientedDifference p a w ≠ 0 :=
    norm_pos_iff.mp ((norm_nonneg _).trans_lt hlt)
  have hratio : X w/(c*orientedDifference p a w) =
      1 + (X w-c*orientedDifference p a w)/(c*orientedDifference p a w) := by
    field_simp [left_ne_zero_of_mul hcn, right_ne_zero_of_mul hcn]
    ring
  rw [hratio]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_div,div_lt_one (norm_pos_iff.mpr hcn)]
  exact hlt

lemma exists_slit_radius_pos {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hzero : X a = 0) (hd : HasFDerivAt X A a)
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    linearPart A ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (linearPart A*orientedDifference true a w) ∈ Complex.slitPlane := by
  have hn : ‖antiLinearPart A‖ < ‖linearPart A‖ := by
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A),norm_nonneg (antiLinearPart A)]
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    exists_slit_radius_of_derivative hzero hd hn ?_⟩
  intro w
  simp [realLinear_decomposition,orientedDifference]

lemma exists_slit_radius_neg {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hzero : X a = 0) (hd : HasFDerivAt X A a)
    (hdet : LinearMap.det A.toLinearMap < 0) :
    antiLinearPart A ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (antiLinearPart A*orientedDifference false a w) ∈ Complex.slitPlane := by
  have hn : ‖linearPart A‖ < ‖antiLinearPart A‖ := by
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A),norm_nonneg (antiLinearPart A)]
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    exists_slit_radius_of_derivative hzero hd hn ?_⟩
  intro w
  simp [realLinear_decomposition,orientedDifference]

lemma differentiable_orientedDifference (p : Bool) (a : ℂ) :
    Differentiable ℝ (orientedDifference p a) := by
  unfold orientedDifference
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Complex.conjCLE.differentiable.comp (differentiable_id.sub_const a)
  · exact differentiable_id.sub_const a

lemma hasFDerivAt_removeZero_other {X : ℂ → ℂ} {p : Bool} {a b c : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : b ≠ a) (hzero : X b = 0) {A : ℂ →L[ℝ] ℂ}
    (hX : HasFDerivAt X A b)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane) :
    HasFDerivAt (removeZero X p a c r) ((orientedDifference p a b)⁻¹ • A) b := by
  have hbfar : r < ‖b-a‖ := by
    by_contra hn
    have he := Complex.slitPlane_ne_zero (hlocal b (by linarith) hb)
    simp [hzero] at he
  have he : removeZero X p a c r =ᶠ[𝓝 b] fun w => X w * (orientedDifference p a w)⁻¹ := by
    filter_upwards [surgeryLog_eq_zero_eventually (X := X) (p := p) (c := c) hr hbfar,
      isClosed_singleton.isOpen_compl.mem_nhds hb] with w hw hwa
    have hwn : w ≠ a := hwa
    simp [removeZero,hwn,hw,div_eq_mul_inv]
  have hdn : orientedDifference p a b ≠ 0 := mt (orientedDifference_eq_zero p a b).mp hb
  have hinv := ((hasDerivAt_inv hdn).hasFDerivAt.restrictScalars ℝ).comp b
    ((differentiable_orientedDifference p a b).hasFDerivAt)
  have hm := hX.fun_mul hinv
  simp only [hzero,zero_smul,zero_add] at hm
  exact hm.congr_of_eventuallyEq he

lemma det_complex_smul (c : ℂ) (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det (c • A).toLinearMap = ‖c‖^2 * LinearMap.det A.toLinearMap := by
  rw [determinant_complex_real,determinant_complex_real,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,smul_apply,smul_eq_mul,
    Complex.mul_re,Complex.mul_im,Complex.normSq_apply]
  ring

lemma windingNumber_orientedDifference (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (p : Bool) (a : ℂ) (ha : ∀ t, γ t ≠ a) :
    windingNumber ⟨fun t => orientedDifference p a (γ t),
      (continuous_orientedDifference p a).comp γ.continuous⟩ =
      (if p then 1 else -1) * loopIndex γ a := by
  cases p
  · change windingNumber ⟨fun t => conj (γ t-a), by fun_prop⟩ = -1 * loopIndex γ a
    rw [neg_one_mul]
    apply windingNumber_eq_of_logIncrement (by simp [hloop])
    have hh := (windingNumber_spec ⟨fun t => γ t-a, by fun_prop⟩
      (by simp [hloop]) (fun t => sub_ne_zero.mpr (ha t))).conj
    convert hh using 1
    all_goals try rfl
    change ((-windingNumber ⟨fun t => γ t-a, by fun_prop⟩ : ℤ) : ℂ) *
      (2*Real.pi*Complex.I) = _
    simp only [Int.cast_neg, map_mul, map_intCast, map_ofNat,
      Complex.conj_ofReal, Complex.conj_I]
    ring
  · simp only [↓reduceIte, one_mul]
    rfl

lemma windingNumber_removeZero_add {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0)
    (hlocal : ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
      X w / (c*orientedDifference p a w) ∈ Complex.slitPlane)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (ha : ∀ t, γ t ≠ a) (hγ : ∀ t, X (γ t) ≠ 0) :
    windingNumber ((⟨X,hX⟩ : C(ℂ,ℂ)).comp γ) =
      (if p then 1 else -1)*loopIndex γ a +
      windingNumber ((⟨removeZero X p a c r,continuous_removeZero hX hr hc hlocal⟩ : C(ℂ,ℂ)).comp γ) := by
  let D : C(unitInterval, ℂ) := ⟨fun t => orientedDifference p a (γ t),
    (continuous_orientedDifference p a).comp γ.continuous⟩
  let Y : C(unitInterval, ℂ) :=
    (⟨removeZero X p a c r,continuous_removeZero hX hr hc hlocal⟩ : C(ℂ,ℂ)).comp γ
  let B : C(unitInterval, ℂ) := ⟨fun t => surgeryLog X p a c r (γ t), by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_surgeryLog hX hr hc (ha t) hlocal).comp γ.continuous.continuousAt⟩
  let E : C(unitInterval, ℂ) := ⟨fun t => Complex.exp (B t), by fun_prop⟩
  have hE : windingNumber E = 0 := by
    apply windingNumber_eq_of_logIncrement (by simp [E,B,hloop])
    simpa using (show HasLogIncrement E 0 from ⟨B,fun _ => rfl,by simp [B,hloop]⟩)
  have hD : ∀ t, D t ≠ 0 := fun t => mt (orientedDifference_eq_zero p a (γ t)).mp (ha t)
  have hY : ∀ t, Y t ≠ 0 := by
    intro t h
    exact hγ t ((removeZero_eq_zero_iff hc).mp (show removeZero X p a c r (γ t) = 0 from h)).1
  have hfact : (⟨X,hX⟩ : C(ℂ,ℂ)).comp γ = D*Y*E := by
    ext t
    exact removeZero_factorization (X := X) (c := c) (r := r) (p := p) (ha t)
  rw [hfact, windingNumber_mul _ _ (by simp [D,Y,hloop]) (by simp [E,B,hloop])
      (fun t => mul_ne_zero (hD t) (hY t)) (fun t => Complex.exp_ne_zero _),
    hE, add_zero, windingNumber_mul _ _ (by simp [D,hloop]) (by simp [Y,hloop]) hD hY]
  rw [show windingNumber D = (if p then 1 else -1)*loopIndex γ a from
    windingNumber_orientedDifference γ hloop p a ha]

lemma windingNumber_comp_zero_on_convex (X : C(ℂ,ℂ)) {K : Set ℂ}
    (hK : Convex ℝ K) (hX : ∀ z ∈ K, X z ≠ 0)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ K) :
    windingNumber (X.comp γ) = 0 := by
  let := hK.contractibleSpace ⟨γ 0,hγ 0⟩
  let := hK.locallyPathConnectedSpace
  let XK : C(K,ℂ) := ⟨fun z => X z, by fun_prop⟩
  obtain ⟨B,hB⟩ := exists_log_lift_of_simplyConnected (⟨γ 0,hγ 0⟩ : K) XK
    (fun z => hX z z.property)
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  refine ⟨⟨fun t => B ⟨γ t,hγ t⟩, by fun_prop⟩, ?_, ?_⟩
  · intro t
    exact hB ⟨γ t,hγ t⟩
  · simp only [Int.cast_zero,zero_mul]
    change B ⟨γ 1,hγ 1⟩-B ⟨γ 0,hγ 0⟩=0
    simp only [hloop,sub_self]

def planeIndex (A : ℂ →L[ℝ] ℂ) : ℤ :=
  if 0 < LinearMap.det A.toLinearMap then 1 else -1

lemma planeIndex_complex_smul {c : ℂ} (hc : c ≠ 0) (A : ℂ →L[ℝ] ℂ) :
    planeIndex (c • A) = planeIndex A := by
  have hp : 0 < ‖c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  simp only [planeIndex,det_complex_smul,mul_pos_iff_of_pos_left hp]

theorem windingNumber_finite_regular_zeros {K : Set ℂ} (hK : Convex ℝ K)
    (s : Finset ℂ) (X : C(ℂ,ℂ)) (A : ℂ → ℂ →L[ℝ] ℂ)
    (hsK : ∀ z ∈ s, z ∈ K) (hzero : ∀ z ∈ K, X z = 0 ↔ z ∈ s)
    (hD : ∀ z ∈ s, HasFDerivAt X (A z) z ∧ LinearMap.det (A z).toLinearMap ≠ 0)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγK : ∀ t, γ t ∈ K)
    (hγ : ∀ t, X (γ t) ≠ 0) :
    windingNumber (X.comp γ) = ∑ a ∈ s, planeIndex (A a)*loopIndex γ a := by
  classical
  induction s using Finset.induction_on generalizing X A with
  | empty =>
      simp only [Finset.sum_empty]
      apply windingNumber_comp_zero_on_convex X hK _ γ hloop hγK
      intro z hz h
      exact Finset.notMem_empty z ((hzero z hz).mp h)
  | @insert a s ha ih =>
      have ham : a ∈ insert a s := Finset.mem_insert_self a s
      have haz : X a = 0 := (hzero a (hsK a ham)).mpr ham
      obtain ⟨hDa,hdet⟩ := hD a ham
      obtain ⟨p,c,r,hr,hc,hsign,hlocal⟩ : ∃ (p : Bool) (c : ℂ) (r : ℝ),
          0 < r ∧ c ≠ 0 ∧ (if p then (1 : ℤ) else -1) = planeIndex (A a) ∧
          ∀ w : ℂ, ‖w-a‖ < 2*r → w ≠ a →
            X w/(c*orientedDifference p a w) ∈ Complex.slitPlane := by
        rcases lt_or_gt_of_ne hdet with hn | hp
        · obtain ⟨hc,r,hr,hl⟩ := exists_slit_radius_neg haz hDa hn
          exact ⟨false,antiLinearPart (A a),r,hr,hc,by simp [planeIndex,not_lt.mpr hn.le],hl⟩
        · obtain ⟨hc,r,hr,hl⟩ := exists_slit_radius_pos haz hDa hp
          exact ⟨true,linearPart (A a),r,hr,hc,by simp [planeIndex,hp],hl⟩
      let Y : C(ℂ,ℂ) := ⟨removeZero X p a c r,
        continuous_removeZero X.continuous hr hc hlocal⟩
      let D : ℂ → ℂ →L[ℝ] ℂ := fun b => (orientedDifference p a b)⁻¹ • A b
      have hbne (b : ℂ) (hb : b ∈ s) : b ≠ a := by
        intro he
        exact ha (he ▸ hb)
      have hdc (b : ℂ) (hb : b ∈ s) : (orientedDifference p a b)⁻¹ ≠ 0 :=
        inv_ne_zero (mt (orientedDifference_eq_zero p a b).mp (hbne b hb))
      have hsK' : ∀ z ∈ s, z ∈ K := fun z hz => hsK z (Finset.mem_insert_of_mem hz)
      have hYzero : ∀ z ∈ K, Y z = 0 ↔ z ∈ s := by
        intro z hz
        change removeZero X p a c r z = 0 ↔ _
        rw [removeZero_eq_zero_iff hc,hzero z hz,Finset.mem_insert]
        constructor
        · rintro ⟨h,hne⟩
          exact h.resolve_left hne
        · intro h
          exact ⟨Or.inr h,hbne z h⟩
      have hDY : ∀ z ∈ s, HasFDerivAt Y (D z) z ∧ LinearMap.det (D z).toLinearMap ≠ 0 := by
        intro z hz
        obtain ⟨hDz,hdz⟩ := hD z (Finset.mem_insert_of_mem hz)
        have hzz := (hzero z (hsK' z hz)).mpr (Finset.mem_insert_of_mem hz)
        refine ⟨hasFDerivAt_removeZero_other hr (hbne z hz) hzz hDz hlocal, ?_⟩
        dsimp only [D]
        rw [det_complex_smul]
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hdc z hz))) hdz
      have hγa : ∀ t, γ t ≠ a := by
        intro t ht
        exact hγ t (ht ▸ haz)
      have hγY : ∀ t, Y (γ t) ≠ 0 := by
        intro t ht
        exact hγ t ((removeZero_eq_zero_iff hc).mp
          (show removeZero X p a c r (γ t) = 0 from ht)).1
      have hi := ih Y D hsK' hYzero hDY hγY
      have hsigns : (∑ b ∈ s, planeIndex (D b)*loopIndex γ b) =
          ∑ b ∈ s, planeIndex (A b)*loopIndex γ b := by
        apply Finset.sum_congr rfl
        intro b hb
        dsimp only [D]
        rw [planeIndex_complex_smul (hdc b hb)]
      rw [Finset.sum_insert ha]
      have hrem := windingNumber_removeZero_add X.continuous hr hc hlocal γ hloop hγa hγ
      change windingNumber (X.comp γ) = (if p then (1 : ℤ) else -1)*loopIndex γ a +
        windingNumber (Y.comp γ) at hrem
      rw [hrem,hsign,hi,hsigns]

lemma exists_countable_injective_partition {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    ∃ p : ℕ → Set ℂ, (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧ (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n) := by
  classical
  have hlocal (z : s) : ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ InjOn f U := by
    let e : ℂ ≃L[ℝ] ℂ :=
      (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr (hreg z z.2))).toContinuousLinearEquiv
    have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
      ext v
      exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr (hreg z z.2)) v
    have hd := (hf z z.2).hasStrictFDerivAt (by norm_num)
    rw [← he] at hd
    let e' := hd.toOpenPartialHomeomorph f
    exact ⟨e'.source,e'.open_source,hd.mem_toOpenPartialHomeomorph_source,e'.injOn⟩
  choose U hUo hUz hUi using hlocal
  by_cases he : s = ∅
  · subst s
    exact ⟨fun _ => ∅,by simp,by simp [Pairwise],by simp,by simp⟩
  · have : Nonempty s := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j,hj⟩ := (show IsLindelof s from HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
      U hUo (fun z hz => mem_iUnion.mpr ⟨⟨z,hz⟩,hUz ⟨z,hz⟩⟩)
    let q : ℕ → Set ℂ := fun n => s ∩ U (j n)
    refine ⟨disjointed q,?_,?_,?_,?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => hs.inter (hUo (j n)).measurableSet) n
    · exact disjoint_disjointed q
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion,mem_inter_iff,q]
      exact ⟨fun ⟨_,hz,_⟩ => hz,fun hz => by obtain ⟨n,hn⟩ := mem_iUnion.mp (hj hz); exact ⟨n,hz,hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)

def fiberMultiplicity (f : ℂ → ℂ) (s : Set ℂ) (w : ℂ) : ℝ≥0∞ :=
  Measure.count {z | z ∈ s ∧ f z = w}

lemma fiber_subsingleton_of_injOn {f : ℂ → ℂ} {s : Set ℂ} (hf : InjOn f s) (w : ℂ) :
    ({z | z ∈ s ∧ f z = w} : Set ℂ).Subsingleton := by
  intro z hz z' hz'
  exact hf hz.1 hz'.1 (hz.2.trans hz'.2.symm)

lemma fiberMultiplicity_of_injOn {f : ℂ → ℂ} {s : Set ℂ} (hf : InjOn f s) (w : ℂ) :
    fiberMultiplicity f s w = (f '' s).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  classical
  by_cases hw : w ∈ f '' s
  · obtain ⟨z,hz,rfl⟩ := hw
    have he : {a | a ∈ s ∧ f a = f z} = {z} := by
      ext a
      exact ⟨fun h => hf h.1 hz h.2,fun h => by rcases h with rfl; exact ⟨hz,rfl⟩⟩
    rw [fiberMultiplicity,he,Measure.count_singleton,indicator_of_mem (mem_image_of_mem f hz)]
  · have he : {a | a ∈ s ∧ f a = w} = ∅ := by
      ext a
      exact ⟨fun h => (hw ⟨a,h.1,h.2⟩).elim,False.elim⟩
    simp [fiberMultiplicity,he,hw]

lemma fiberMultiplicity_partition {f : ℂ → ℂ} {s : Set ℂ} {p : ℕ → Set ℂ}
    (hd : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s) (hi : ∀ n, InjOn f (p n))
    (w : ℂ) : fiberMultiplicity f s w =
      ∑' n, (f '' p n).indicator (fun _ => (1 : ℝ≥0∞)) w := by
  have he : {z | z ∈ s ∧ f z = w} = ⋃ n, {z | z ∈ p n ∧ f z = w} := by
    rw [← hu]
    ext z
    simp only [mem_ofPred_eq,mem_iUnion]
    aesop
  rw [fiberMultiplicity,he,measure_iUnion]
  · exact tsum_congr (fun n => fiberMultiplicity_of_injOn (hi n) w)
  · exact pairwise_disjoint_mono hd (fun n => inter_subset_left)
  · intro n
    exact (fiber_subsingleton_of_injOn (hi n) w).finite.measurableSet

lemma area_formula_regular {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    Measurable (fiberMultiplicity f s) ∧
      (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume) =
        ∫⁻ w, fiberMultiplicity f s w ∂volume := by
  obtain ⟨p,hpm,hpd,hpu,hpi⟩ := exists_countable_injective_partition hs hf hreg
  have hps (n) : p n ⊆ s := hpu ▸ subset_iUnion p n
  have hder (n) (z) (hz : z ∈ p n) : HasFDerivWithinAt f (fderiv ℝ f z) (p n) z :=
    ((hf z (hps n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  have him (n) : MeasurableSet (f '' p n) :=
    measurable_image_of_fderivWithin (hpm n) (hder n) (hpi n)
  have he := funext (fiberMultiplicity_partition hpd hpu hpi)
  refine ⟨?_,?_⟩
  · rw [he]
    exact Measurable.tsum (fun n => measurable_const.indicator (him n))
  · calc
      (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume) =
          ∑' n, ∫⁻ z in p n, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| ∂volume := by
        conv_lhs => rw [← hpu]
        exact lintegral_iUnion hpm hpd _
      _ = ∑' n, volume (f '' p n) := tsum_congr (fun n =>
        lintegral_abs_det_fderiv_eq_addHaar_image volume (hpm n) (hder n) (hpi n))
      _ = ∫⁻ w, fiberMultiplicity f s w ∂volume := by
        rw [he,lintegral_tsum]
        · apply tsum_congr
          intro n
          rw [lintegral_indicator (him n)]
          simp
        · exact fun n => (measurable_const.indicator (him n)).aemeasurable

lemma lintegral_positive_part_eq {g : ℂ → ℝ} (hg : Measurable g) (s : Set ℂ) :
    (∫⁻ z in s, ENNReal.ofReal (g z) ∂volume) =
      ∫⁻ z in {z | z ∈ s ∧ 0 < g z}, ENNReal.ofReal |g z| ∂volume := by
  classical
  have hm : MeasurableSet {z | 0 < g z} := measurableSet_lt measurable_const hg
  have he : (fun z => ENNReal.ofReal (g z)) =
      {z | 0 < g z}.indicator (fun z => ENNReal.ofReal |g z|) := by
    funext z
    by_cases hz : 0 < g z
    · simp [hz,abs_of_pos hz]
    · simp [hz,ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hz)]
  rw [he,lintegral_indicator hm,Measure.restrict_restrict hm]
  exact congrArg (fun t : Set ℂ => ∫⁻ z in t, ENNReal.ofReal |g z| ∂volume) (inter_comm _ _)

lemma integral_det_nonpos_of_fiberMultiplicity {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ContDiff ℝ 1 f)
    (hj : IntegrableOn (fun z => LinearMap.det (fderiv ℝ f z).toLinearMap) s volume)
    (hcount : ∀ᵐ w ∂volume,
      fiberMultiplicity f {z | z ∈ s ∧ 0 < LinearMap.det (fderiv ℝ f z).toLinearMap} w ≤
      fiberMultiplicity f {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap < 0} w) :
    ∫ z in s, LinearMap.det (fderiv ℝ f z).toLinearMap ∂volume ≤ 0 := by
  let J : ℂ → ℝ := fun z => LinearMap.det (fderiv ℝ f z).toLinearMap
  have hJ : Continuous J := ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  have hp : MeasurableSet {z | z ∈ s ∧ 0 < J z} :=
    hs.inter (measurableSet_lt measurable_const hJ.measurable)
  have hm : MeasurableSet {z | z ∈ s ∧ J z < 0} :=
    hs.inter (measurableSet_lt hJ.measurable measurable_const)
  have hap := (area_formula_regular hp (fun z _ => hf.contDiffAt)
    (fun z hz => ne_of_gt hz.2)).2
  have ham := (area_formula_regular hm (fun z _ => hf.contDiffAt)
    (fun z hz => ne_of_lt hz.2)).2
  have hle : (∫⁻ z in s, ENNReal.ofReal (J z) ∂volume) ≤
      ∫⁻ z in s, ENNReal.ofReal (-J z) ∂volume := by
    rw [lintegral_positive_part_eq hJ.measurable,lintegral_positive_part_eq (g := fun z => -J z) hJ.neg.measurable]
    simp only [neg_pos,abs_neg]
    rw [hap,ham]
    exact lintegral_mono_ae hcount
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hj]
  exact sub_nonpos.mpr (ENNReal.toReal_mono (by
    exact (lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hj.neg.2).ne) hle)

lemma finite_regular_zeros_on_compact {K : Set ℂ} (hK : IsCompact K)
    {X : ℂ → ℂ} (hc : ContinuousOn X K)
    (hd : ∀ z ∈ K, X z = 0 → DifferentiableAt ℝ X z ∧
      LinearMap.det (fderiv ℝ X z).toLinearMap ≠ 0) :
    {z | z ∈ K ∧ X z = 0}.Finite := by
  have hZ : IsCompact {z | z ∈ K ∧ X z = 0} :=
    hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hZ.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  obtain ⟨hzD,hzd⟩ := hd z hz.1 hz.2
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hzd)).toContinuousLinearEquiv
  have he : (e : ℂ → ℂ) = fderiv ℝ X z := by
    funext w
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hzd) w
  have ha : ∃ C, AntilipschitzWith C (fderiv ℝ X z) := by
    rw [← he]
    exact ⟨_,e.antilipschitz⟩
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [hzD.hasFDerivAt.eventually_ne ha] with w hw
  exact fun h => hw (h.2.trans hz.2.symm)

lemma loopIndex_circle_inside {r : ℝ} (hr : 0 < r) {a : ℂ} (ha : ‖a‖ < r) :
    loopIndex ((r : ℂ) • circleLoop) a = 1 := by
  let γ : C(unitInterval,ℂ) := (r : ℂ) • circleLoop
  have hγloop : γ 1 = γ 0 := by simp [γ]
  have hγnorm (t) : ‖γ t‖ = r := by simp [γ,abs_of_pos hr]
  have hγne (t) : γ t ≠ 0 := norm_pos_iff.mp (by rw [hγnorm]; exact hr)
  have hwone : windingNumber γ = 1 := by
    apply windingNumber_eq_of_logIncrement hγloop
    simpa using circleLoop_logIncrement (r : ℂ) (by exact_mod_cast hr.ne')
  unfold loopIndex
  rw [← hwone]
  apply windingNumber_perturb hγloop (by simp) hγne
  intro t
  simpa [γ,sub_sub_cancel_left,abs_of_pos hr] using ha

lemma ae_regular_value {f : ℂ → ℂ} (hf : Differentiable ℝ f) :
    ∀ᵐ w ∂volume, ∀ z, f z = w → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 := by
  have hm : volume (f '' {z | LinearMap.det (fderiv ℝ f z).toLinearMap = 0}) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z _ => (hf z).hasFDerivAt.hasFDerivWithinAt) (fun _ h => h)
  have ha : ∀ᵐ w ∂volume, w ∉ f '' {z | LinearMap.det (fderiv ℝ f z).toLinearMap = 0} :=
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hm)
  filter_upwards [ha] with w hw z hz hd
  exact hw ⟨z,hd,hz⟩

lemma signed_sum_eq_card_sub (s : Finset ℂ) (J : ℂ → ℝ)
    (hJ : ∀ z ∈ s, J z ≠ 0) :
    (∑ z ∈ s, if 0 < J z then (1 : ℤ) else -1) =
      (s.filter (fun z => 0 < J z)).card - (s.filter (fun z => J z < 0)).card := by
  classical
  rw [← Finset.sum_boole (R := ℤ) (fun z => 0 < J z) s,
    ← Finset.sum_boole (R := ℤ) (fun z => J z < 0) s,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro z hz
  rcases lt_or_gt_of_ne (hJ z hz) with hn | hp
  · simp [hn,not_lt.mpr hn.le]
  · simp [hp,not_lt.mpr hp.le]

lemma integral_jacobian_nonpos_of_boundary_winding {f : ℂ → ℂ} (hf : ContDiff ℝ 1 f)
    {r : ℝ} (hr : 0 < r)
    (hw : ∀ ξ, ξ ∉ f '' Metric.sphere 0 r →
      windingNumber (⟨fun t => f ((r : ℂ)*circleLoop t)-ξ, by fun_prop⟩) ≤ 0) :
    ∫ z in Metric.closedBall 0 r, LinearMap.det (fderiv ℝ f z).toLinearMap ∂volume ≤ 0 := by
  classical
  let J : ℂ → ℝ := fun z => LinearMap.det (fderiv ℝ f z).toLinearMap
  have hJc : Continuous J := ContinuousLinearMap.continuous_det.comp
    (hf.continuous_fderiv (by norm_num))
  have hd := hf.differentiable (by norm_num)
  have hbnull : volume (f '' Metric.sphere 0 r) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      hd.differentiableOn (Measure.addHaar_sphere volume 0 r)
  apply integral_det_nonpos_of_fiberMultiplicity measurableSet_closedBall hf
    (hJc.continuousOn.integrableOn_compact (isCompact_closedBall 0 r))
  filter_upwards [ae_regular_value hd,show ∀ᵐ ξ ∂volume, ξ ∉ f '' Metric.sphere 0 r from
    ae_iff.mpr (by simpa only [not_not,Set.ofPred_mem_eq] using hbnull)] with ξ hξ hξb
  let X : C(ℂ,ℂ) := ⟨fun z => f z-ξ,by fun_prop⟩
  have hXD (z) : HasFDerivAt X (fderiv ℝ f z) z := (hd z).hasFDerivAt.sub_const ξ
  have hfinite : {z | z ∈ Metric.closedBall 0 r ∧ X z = 0}.Finite :=
    finite_regular_zeros_on_compact (isCompact_closedBall 0 r) X.continuous.continuousOn
      (fun z _ hz => ⟨(hXD z).differentiableAt,by
        rw [(hXD z).fderiv]; exact hξ z (sub_eq_zero.mp hz)⟩)
  let s := hfinite.toFinset
  have hs (z) : z ∈ s ↔ z ∈ Metric.closedBall 0 r ∧ f z = ξ := by
    simp [s,X,sub_eq_zero]
  have hinside (z) (hz : z ∈ s) : ‖z‖ < r := by
    have hz' := (hs z).mp hz
    have hle : ‖z‖ ≤ r := by simpa using hz'.1
    apply lt_of_le_of_ne hle
    intro he
    exact hξb ⟨z,by simpa using he,hz'.2⟩
  let γ : C(unitInterval,ℂ) := (r : ℂ) • circleLoop
  have hγnorm (t) : ‖γ t‖ = r := by simp [γ,abs_of_pos hr]
  have hγsphere (t) : γ t ∈ Metric.sphere 0 r := by simpa using hγnorm t
  have hγzero (t) : X (γ t) ≠ 0 := by
    intro he
    exact hξb ⟨γ t,hγsphere t,sub_eq_zero.mp he⟩
  have hreg (z) (hz : z ∈ s) : J z ≠ 0 := hξ z ((hs z).mp hz).2
  have hindex := windingNumber_finite_regular_zeros (convex_closedBall (0 : ℂ) r) s X
    (fun z => fderiv ℝ f z) (fun z hz => ((hs z).mp hz).1)
    (fun z hz => by simp [hs,hz,X,sub_eq_zero])
    (fun z hz => ⟨hXD z,hreg z hz⟩) γ (by simp [γ])
    (fun t => Metric.sphere_subset_closedBall (hγsphere t)) hγzero
  have hloopindex (z) (hz : z ∈ s) : loopIndex γ z = 1 :=
    loopIndex_circle_inside hr (hinside z hz)
  have hsign : (∑ z ∈ s, if 0 < J z then (1 : ℤ) else -1) ≤ 0 := by
    calc
      _ = windingNumber (X.comp γ) := by
        rw [hindex]
        apply Finset.sum_congr rfl
        intro z hz
        rw [hloopindex z hz,mul_one]
        rfl
      _ ≤ 0 := hw ξ hξb
  have hcard : (s.filter (fun z => 0 < J z)).card ≤ (s.filter (fun z => J z < 0)).card := by
    rw [signed_sum_eq_card_sub s J hreg] at hsign
    exact_mod_cast sub_nonpos.mp hsign
  have hp : {z | z ∈ {z | z ∈ Metric.closedBall 0 r ∧ 0 < J z} ∧ f z = ξ} =
      ↑(s.filter (fun z => 0 < J z)) := by ext z; simp [hs]; aesop
  have hn : {z | z ∈ {z | z ∈ Metric.closedBall 0 r ∧ J z < 0} ∧ f z = ξ} =
      ↑(s.filter (fun z => J z < 0)) := by ext z; simp [hs]; aesop
  change fiberMultiplicity f {z | z ∈ Metric.closedBall 0 r ∧ 0 < J z} ξ ≤
    fiberMultiplicity f {z | z ∈ Metric.closedBall 0 r ∧ J z < 0} ξ
  simp only [fiberMultiplicity,hp,hn,Measure.count_apply_finset]
  exact_mod_cast hcard

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.UnivalentArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1) ∧ ∀ z, χ z ∈ Icc 0 1 := by
  obtain ⟨L,hL,hLc,hKL,hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨χ,hχ1,hχ0,hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ,ℂ) hK.isClosed hKL (n := 2)
  have hs : tsupport (χ : ℂ → ℝ) ⊆ L := by
    apply closure_minimal _ hLc
    intro z hz
    by_contra hn
    exact hz (hχ0 z hn)
  refine ⟨χ,contMDiff_iff_contDiff.mp χ.contMDiff,
    hL.of_isClosed_subset (isClosed_tsupport _) hs,hs.trans hLU,?_,hχrange⟩
  intro z hz
  exact hχ1.filter_mono (nhds_le_nhdsSet hz)

lemma det_fderiv_complex {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2 := by
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,determinant_complex_real,
    ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    Complex.I_mul, Complex.normSq_apply]
  ring

lemma smooth_extension_near_compact {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {x : ℂ → ℂ}
    (hx : ∀ z ∈ U, ContDiffAt ℝ 2 x z) :
    ∃ X : ℂ → ℂ, ContDiff ℝ 2 X ∧ ∀ z ∈ K, X =ᶠ[𝓝 z] x := by
  obtain ⟨χ,hχc,_hχK,hχU,hχ1,_hχrange⟩ := exists_smooth_cutoff hK hU hKU
  let X := fun z => (χ z : ℂ)*x z
  have hX : ContDiff ℝ 2 X := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (Complex.ofRealCLM.contDiff.contDiffAt.comp z hχc.contDiffAt).mul (hx z (hχU hz))
    · have he : X =ᶠ[𝓝 z] fun _ => 0 := by
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X,hzero,Complex.ofReal_zero,zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  refine ⟨X,hX,?_⟩
  intro z hz
  filter_upwards [hχ1 z hz] with w hw
  simp only [X,hw,Complex.ofReal_one,one_mul]

lemma meromorphic_boundary_winding_le_zero {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹+h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) (ξ : ℂ)
    (hξ : ξ ∉ H '' Metric.sphere 0 r) :
    windingNumber (⟨fun t => H ((r : ℂ)*circleLoop t)-ξ, by
      refine Continuous.sub ?_ continuous_const
      apply hH.continuousOn.comp_continuous (by fun_prop)
      intro t
      have he : ‖(r : ℂ)*circleLoop t‖ = r := by simp [abs_of_pos hr]
      constructor
      · rw [Metric.mem_ball,dist_zero_right,he]
        exact hr1
      · change (r : ℂ)*circleLoop t ≠ 0
        exact norm_pos_iff.mp (by rw [he]; exact hr)⟩) ≤ 0 := by
  classical
  let U : Set ℂ := Metric.ball 0 1
  let K : Set ℂ := Metric.closedBall 0 r
  have hKU : K ⊆ U := Metric.closedBall_subset_ball hr1
  let x : ℂ → ℂ := fun z => 1+z*(h z-ξ)
  have hx (z) (hz : z ∈ U) : AnalyticAt ℂ x z := by
    exact analyticAt_const.add (analyticAt_id.mul ((hh.analyticOnNhd Metric.isOpen_ball z hz).sub analyticAt_const))
  obtain ⟨X,hXc,hX⟩ := smooth_extension_near_compact (isCompact_closedBall 0 r)
    Metric.isOpen_ball hKU (fun z hz => (hx z hz).contDiffAt.restrict_scalars ℝ)
  have hXval (z) (hz : z ∈ K) : X z = x z := (hX z hz).self_of_nhds
  have hxzero {z} (hz : z ∈ U) : x z = 0 ↔ z ≠ 0 ∧ H z = ξ := by
    by_cases hz0 : z = 0
    · simp [x,hz0]
    · rw [hdef z hz hz0]
      dsimp [x]
      field_simp
      constructor <;> intro he
      · exact ⟨hz0,by linear_combination he⟩
      · linear_combination he.2
  have hss : {z | z ∈ K ∧ X z = 0}.Subsingleton := by
    intro z hz w hw
    obtain ⟨hz0,hzξ⟩ := (hxzero (hKU hz.1)).mp ((hXval z hz.1) ▸ hz.2)
    obtain ⟨hw0,hwξ⟩ := (hxzero (hKU hw.1)).mp ((hXval w hw.1) ▸ hw.2)
    exact hHi ⟨hKU hz.1,hz0⟩ ⟨hKU hw.1,hw0⟩ (hzξ.trans hwξ.symm)
  let s := hss.finite.toFinset
  have hs (z) : z ∈ s ↔ z ∈ K ∧ X z = 0 := by simp [s]
  have hder (z) (hz : z ∈ s) : DifferentiableAt ℂ X z ∧ deriv X z ≠ 0 := by
    have hzK := ((hs z).mp hz).1
    have hzero := ((hs z).mp hz).2
    obtain ⟨hz0,hzξ⟩ := (hxzero (hKU hzK)).mp (by rwa [hXval z hzK] at hzero)
    have hUz : z ∈ Metric.ball (0 : ℂ) 1 \ {0} := ⟨hKU hzK,hz0⟩
    have hHd' := (hH z hUz).differentiableAt ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hUz)
    have heq : x =ᶠ[𝓝 z] fun w => w*(H w-ξ) := by
      filter_upwards [(Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds hUz] with w hw
      have hw0 : w ≠ 0 := hw.2
      rw [hdef w hw.1 hw0]
      dsimp [x]
      field_simp [hw0]
      ring
    have hD : HasDerivAt X (z*deriv H z) z := by
      have hD := (hasDerivAt_id z).mul (hHd'.hasDerivAt.sub_const ξ)
      simp only [hzξ,sub_self,mul_zero,zero_add] at hD
      exact hD.congr_of_eventuallyEq ((hX z hzK).trans heq)
    exact ⟨hD.differentiableAt,hD.deriv ▸ mul_ne_zero hz0 (hHd z hUz)⟩
  let γ : C(unitInterval,ℂ) := (r : ℂ) • circleLoop
  have hγnorm (t) : ‖γ t‖ = r := by simp [γ,abs_of_pos hr]
  have hγK (t) : γ t ∈ K := by simpa [K] using (hγnorm t).le
  have hγU (t) : γ t ∈ U := hKU (hγK t)
  have hγ0 (t) : γ t ≠ 0 := norm_pos_iff.mp (by rw [hγnorm]; exact hr)
  have hγξ (t) : H (γ t) ≠ ξ := fun he => hξ ⟨γ t,by simpa using hγnorm t,he⟩
  let Y : C(ℂ,ℂ) := ⟨X,hXc.continuous⟩
  have hXY (t) : Y (γ t) = γ t*(H (γ t)-ξ) := by
    rw [show Y (γ t) = X (γ t) from rfl,hXval _ (hγK t),hdef _ (hγU t) (hγ0 t)]
    dsimp only [x]
    field_simp [hγ0 t]
    ring
  have hγnonzero (t) : Y (γ t) ≠ 0 := by rw [hXY]; exact mul_ne_zero (hγ0 t) (sub_ne_zero.mpr (hγξ t))
  have hi := windingNumber_finite_regular_zeros (convex_closedBall (0 : ℂ) r) s Y
    (fun z => fderiv ℝ X z) (fun z hz => ((hs z).mp hz).1)
    (fun z hz => by simp [hs,show z ∈ K from hz,Y])
    (fun z hz => ⟨((hder z hz).1.restrictScalars ℝ).hasFDerivAt,by
      rw [det_fderiv_complex (hder z hz).1]
      exact pow_ne_zero _ (norm_ne_zero_iff.mpr (hder z hz).2)⟩)
    γ (by simp [γ]) hγK hγnonzero
  have hins (z) (hz : z ∈ s) : ‖z‖ < r := by
    have hzK := ((hs z).mp hz).1
    have hle : ‖z‖ ≤ r := by simpa [K] using hzK
    refine lt_of_le_of_ne hle ?_
    intro he
    have hzero := ((hs z).mp hz).2
    have hzξ := ((hxzero (hKU hzK)).mp (by rwa [hXval z hzK] at hzero)).2
    exact hξ ⟨z,by simpa using he,hzξ⟩
  have hi' : windingNumber (Y.comp γ) = (s.card : ℤ) := by
    rw [hi]
    calc
      _ = ∑ _z ∈ s, (1 : ℤ) := by
        apply Finset.sum_congr rfl
        intro z hz
        rw [loopIndex_circle_inside hr (hins z hz),mul_one]
        simp only [planeIndex,det_fderiv_complex (hder z hz).1,
          sq_pos_of_pos (norm_pos_iff.mpr (hder z hz).2),ite_true]
      _ = ↑s.card := by simp
  have hcard : s.card ≤ 1 := Finset.card_le_one.mpr (by
    intro z hz w hw
    exact hss ((hs z).mp hz) ((hs w).mp hw))
  let η : C(unitInterval,ℂ) := ⟨fun t => H (γ t)-ξ,by
    refine Continuous.sub ?_ continuous_const
    apply hH.continuousOn.comp_continuous γ.continuous
    exact fun t => ⟨hγU t,hγ0 t⟩⟩
  have he : Y.comp γ = γ*η := by ext t; exact hXY t
  have hwγ : windingNumber γ = 1 := by
    apply windingNumber_eq_of_logIncrement (by simp [γ])
    simpa [γ] using circleLoop_logIncrement (r : ℂ) (by exact_mod_cast hr.ne')
  rw [he,windingNumber_mul γ η (by simp [γ]) (by simp [η,γ]) hγ0
    (fun t => sub_ne_zero.mpr (hγξ t)),hwγ] at hi'
  change windingNumber η ≤ 0
  have hc : (s.card : ℤ) ≤ 1 := by exact_mod_cast hcard
  omega

lemma det_holomorphic_plus_conjugate {h : ℂ → ℂ} {z : ℂ}
    (hh : DifferentiableAt ℂ h z) (a : ℝ) :
    LinearMap.det (fderiv ℝ (fun w => a • conj w+h w) z).toLinearMap =
      ‖deriv h z‖^2-a^2 := by
  have hD := (Complex.conjCLE.hasFDerivAt.const_smul a).add
    (hh.hasDerivAt.hasFDerivAt.restrictScalars ℝ)
  change HasFDerivAt (fun w => a • conj w+h w) _ z at hD
  rw [hD.fderiv,determinant_complex_real,← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe,add_apply,
    smul_apply,ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul,one_mul,Complex.real_smul,Complex.normSq_apply]
  simp [Complex.add_re,Complex.add_im,Complex.mul_re,Complex.mul_im]
  ring

lemma meromorphic_univalent_area {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹+h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2 ∂volume ≤
      volume.real (Metric.closedBall (0 : ℂ) r) * (r^2)⁻¹^2 := by
  let K : Set ℂ := Metric.closedBall 0 r
  let x : ℂ → ℂ := fun z => (r^2)⁻¹ • conj z+h z
  have hKU : K ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hr1
  have hx (z) (hz : z ∈ Metric.ball (0 : ℂ) 1) : ContDiffAt ℝ 2 x z := by
    exact (Complex.conjCLE.contDiff.contDiffAt.const_smul (r^2)⁻¹).add
      ((hh.analyticOnNhd Metric.isOpen_ball z hz).contDiffAt.restrict_scalars ℝ)
  obtain ⟨X,hXc,hX⟩ := smooth_extension_near_compact (isCompact_closedBall 0 r)
    Metric.isOpen_ball hKU hx
  have hXval (z) (hz : z ∈ K) : X z = x z := (hX z hz).self_of_nhds
  have hb (z) (hz : z ∈ Metric.sphere (0 : ℂ) r) : X z = H z := by
    have hn : ‖z‖ = r := by simpa using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hn];exact hr)
    rw [hXval z (Metric.sphere_subset_closedBall hz),hdef z (hKU (Metric.sphere_subset_closedBall hz)) hz0]
    dsimp [x]
    rw [Complex.inv_def,Complex.normSq_eq_norm_sq,hn]
    congr 1
    simp [mul_comm]
  have hw (ξ) (hξ : ξ ∉ X '' Metric.sphere 0 r) :
      windingNumber (⟨fun t => X ((r : ℂ)*circleLoop t)-ξ,by fun_prop⟩) ≤ 0 := by
    have hξ' : ξ ∉ H '' Metric.sphere 0 r := by
      rintro ⟨z,hz,hzξ⟩
      exact hξ ⟨z,hz,(hb z hz).trans hzξ⟩
    have hw := meromorphic_boundary_winding_le_zero hh hH hdef hHd hHi hr hr1 ξ hξ'
    convert hw using 2
    ext t
    change X ((r : ℂ)*circleLoop t)-ξ = H ((r : ℂ)*circleLoop t)-ξ
    rw [hb _ (by simp [abs_of_pos hr])]
  have hi := integral_jacobian_nonpos_of_boundary_winding
    (hXc.of_le (by norm_num)) hr hw
  have hdet (z) (hz : z ∈ K) :
      LinearMap.det (fderiv ℝ X z).toLinearMap = ‖deriv h z‖^2-(r^2)⁻¹^2 := by
    rw [(hX z hz).fderiv_eq]
    exact det_holomorphic_plus_conjugate
      ((hh z (hKU hz)).differentiableAt (Metric.isOpen_ball.mem_nhds (hKU hz))) _
  have hdcont : ContinuousOn (deriv h) K :=
    (hh.deriv Metric.isOpen_ball).continuousOn.mono hKU
  have hint : IntegrableOn (fun z => ‖deriv h z‖^2) K :=
    (hdcont.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst : IntegrableOn (fun _ : ℂ => (r^2)⁻¹^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have he : (∫ z in K, LinearMap.det (fderiv ℝ X z).toLinearMap) =
      (∫ z in K, ‖deriv h z‖^2) - volume.real K * (r^2)⁻¹^2 := by
    rw [setIntegral_congr_fun measurableSet_closedBall hdet,
      integral_sub hint hconst]
    simp
  rw [he] at hi
  exact sub_nonpos.mp hi

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Distortion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma polar_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r,θ) = circleMap 0 r θ := by
  rw [Complex.polarCoord_symm_apply, circleMap, zero_add]
  congr 1
  rw [Complex.exp_mul_I]
  simp

lemma circleAverage_eq_integral_neg_pi (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r =
      (2*Real.pi)⁻¹ • ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))]
  congr 2 <;> ring

lemma integral_ball_polar {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (Metric.closedBall 0 R)) :
    ∫ z in Metric.ball (0 : ℂ) R, f z =
      ∫ r in (0 : ℝ)..R, (2*Real.pi*r) • Real.circleAverage f 0 r := by
  let g : ℝ × ℝ → ℂ := fun p => p.1 • f (Complex.polarCoord.symm p)
  have hg : IntegrableOn g (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) := by
    refine (show IntegrableOn g (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) from ?_).mono_set ?_
    · apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
        simp only [Complex.polarCoord_symm_apply]
        fun_prop
      apply continuousOn_fst.smul (hf.comp hpolar.continuousOn ?_)
      intro p hp
      simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
      exact (abs_of_nonneg hp.1.1).trans_le hp.1.2
    · exact prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self
  calc
    _ = ∫ p in polarCoord.target,
        p.1 • (Metric.ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p) := by
      rw [Complex.integral_comp_polarCoord_symm,
        integral_indicator Metric.isOpen_ball.measurableSet]
    _ = ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi, g p := by
      rw [polarCoord_target]
      have heq : (fun p : ℝ × ℝ => p.1 •
          (Metric.ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) =ᶠ[
          ae (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi))]
        (Iio R ×ˢ (univ : Set ℝ)).indicator g := by
        filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
        have hp0 : 0 < p.1 := hp.1
        have hn : ‖Complex.polarCoord.symm p‖ = p.1 := by
          rw [Complex.norm_polarCoord_symm,abs_of_pos hp0]
        by_cases hr : p.1 < R
        · rw [indicator_of_mem (by simpa [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hp0] using hr),
            indicator_of_mem (show p ∈ Iio R ×ˢ (univ : Set ℝ) from ⟨hr,mem_univ _⟩)]
        · rw [indicator_of_notMem (by simpa [Metric.mem_ball,dist_zero_right,Complex.norm_polarCoord_symm,abs_of_pos hp0] using hr),
            indicator_of_notMem (show p ∉ Iio R ×ˢ (univ : Set ℝ) from fun h => hr h.1),smul_zero]
      rw [integral_congr_ae heq,
        integral_indicator (measurableSet_Iio.prod MeasurableSet.univ)]
      rw [Measure.restrict_restrict (measurableSet_Iio.prod MeasurableSet.univ)]
      congr 2
      ext p
      simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Iio, mem_Ioo, mem_univ, and_true]
      tauto
    _ = ∫ r in Ioo (0 : ℝ) R, ∫ θ in Ioo (-Real.pi) Real.pi, g (r,θ) := by
      exact setIntegral_prod _ (by simpa only [← Measure.volume_eq_prod] using hg)
    _ = ∫ r in (0 : ℝ)..R, (2*Real.pi*r) • Real.circleAverage f 0 r := by
      rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro r hr
      dsimp only
      rw [circleAverage_eq_integral_neg_pi,
        intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
        integral_Ioc_eq_integral_Ioo, ← smul_assoc]
      have he : (2*Real.pi*r) * (2*Real.pi)⁻¹ = r := by
        field_simp
      rw [smul_eq_mul, he, ← integral_smul]
      apply setIntegral_congr_fun measurableSet_Ioo
      intro θ hθ
      simp only [g, polar_symm_eq_circleMap]

lemma ball_closedBall_ae_eq (r : ℝ) :
    Metric.ball (0 : ℂ) r =ᵐ[volume] Metric.closedBall 0 r := by
  apply ae_eq_set.mpr
  constructor
  · rw [sdiff_eq_empty.mpr Metric.ball_subset_closedBall,measure_empty]
  · rw [Metric.closedBall_sdiff_ball]
    exact Measure.addHaar_sphere volume 0 r

lemma integral_ball_holomorphic {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    ∫ z in Metric.ball (0 : ℂ) r, f z = volume.real (Metric.ball (0 : ℂ) r) • f 0 := by
  have hfc : ContinuousOn f (Metric.closedBall 0 r) :=
    hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  rw [integral_ball_polar hr hfc]
  have hm (t : ℝ) (ht : t ∈ Ioo 0 r) : Real.circleAverage f 0 t = f 0 := by
    apply DiffContOnCl.circleAverage
    rw [abs_of_pos ht.1]
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 ht.1.ne']
    exact hf.mono (Metric.closedBall_subset_ball (ht.2.trans hrR))
  have hc := integral_ball_polar (f := fun _ : ℂ => f 0) hr continuousOn_const
  rw [setIntegral_const] at hc
  rw [hc]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr.le] at ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have ht' : t ∈ Ioo 0 r ∨ t = r := by
    exact (lt_or_eq_of_le ht.2).elim (fun h => Or.inl ⟨htpos,h⟩) Or.inr
  have hmf : Real.circleAverage f 0 t = f 0 := by
    rcases ht' with ht' | rfl
    · exact hm t ht'
    · apply DiffContOnCl.circleAverage
      rw [abs_of_pos hr]
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 hr.ne']
      exact hf.mono (Metric.closedBall_subset_ball hrR)
  simp only [hmf,Real.circleAverage_const]

lemma integral_closedBall_holomorphic {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    ∫ z in Metric.closedBall (0 : ℂ) r, f z =
      volume.real (Metric.closedBall (0 : ℂ) r) • f 0 := by
  rw [← setIntegral_congr_set (ball_closedBall_ae_eq r),
    integral_ball_holomorphic hf hr hrR]
  congr 1
  exact congrArg ENNReal.toReal (measure_congr (ball_closedBall_ae_eq r))

lemma holomorphic_sq_submean {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    volume.real (Metric.closedBall (0 : ℂ) r) * ‖f 0‖^2 ≤
      ∫ z in Metric.closedBall (0 : ℂ) r, ‖f z‖^2 := by
  let K : Set ℂ := Metric.closedBall 0 r
  have hfc : ContinuousOn f K := hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  have hfi : IntegrableOn f K := hfc.integrableOn_compact (isCompact_closedBall 0 r)
  have hf2i : IntegrableOn (fun z => ‖f z‖^2) K :=
    (hfc.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst : IntegrableOn (fun _ : ℂ => ‖f 0‖^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have hnonneg : 0 ≤ ∫ z in K, ‖f z-f 0‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun z => ‖f z-f 0‖^2) =
      (fun z => ‖f z‖^2-2*inner ℝ (f 0) (f z)+‖f 0‖^2) := by
    funext z
    rw [norm_sub_sq_real,real_inner_comm]
  have hsub : IntegrableOn (fun z => ‖f z‖^2-2*inner ℝ (f 0) (f z)) K :=
    hf2i.sub ((hfi.const_inner (f 0)).const_mul 2)
  have hinner : IntegrableOn (fun z => 2*inner ℝ (f 0) (f z)) K :=
    (hfi.const_inner (f 0)).const_mul 2
  rw [he,integral_add hsub hconst,
    integral_sub hf2i hinner,
    integral_const_mul,integral_inner hfi,setIntegral_const,
    integral_closedBall_holomorphic hf hr hrR,real_inner_smul_right,
    real_inner_self_eq_norm_sq,smul_eq_mul] at hnonneg
  dsimp only [K] at hnonneg ⊢
  linarith

lemma meromorphic_univalent_coefficient {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹+h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0})) : ‖deriv h 0‖ ≤ 1 := by
  have hb (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ‖deriv h 0‖^2 ≤ (r^2)⁻¹^2 := by
    have hM : 0 < volume.real (Metric.closedBall (0 : ℂ) r) := by
      rw [measureReal_def,Complex.volume_closedBall,ENNReal.toReal_mul,ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le,ENNReal.coe_toReal]
      exact mul_pos (sq_pos_of_pos hr) Real.pi_pos
    have hle := (holomorphic_sq_submean (hh.deriv Metric.isOpen_ball) hr hr1).trans
      (meromorphic_univalent_area hh hH hdef hHd hHi hr hr1)
    nlinarith
  have ht : Tendsto (fun r : ℝ => (r^2)⁻¹^2) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun r : ℝ => (r^2)⁻¹^2) 1 :=
      ((continuousAt_id.pow 2).inv₀ (by norm_num)).pow 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsq : ‖deriv h 0‖^2 ≤ 1 := by
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r from
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ)<1)))] with r hr1 hr
    exact hb r hr hr1
  nlinarith [norm_nonneg (deriv h 0)]

lemma nonconstant_germ_of_injOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : Set.InjOn f U) {a : ℂ} (ha : a ∈ U) :
    ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
  intro hc
  have heq : ∀ᶠ z in 𝓝 a, z = a := by
    filter_upwards [hc, hU.mem_nhds ha] with z hz hzU
    exact hf hzU ha hz
  have heq' : ∀ᶠ z in 𝓝[≠] a, z = a := heq.filter_mono nhdsWithin_le_nhds
  have hne' : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
  obtain ⟨z, hz, hne⟩ := (heq'.and hne').exists
  exact hne hz

lemma univalent_inverse_continuousAt {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f a) := by
  have haan : AnalyticAt ℂ f a := (hf.1.analyticOnNhd hU) a ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    haan.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hl : ∀ᶠ z in 𝓝 a, Function.invFunOn f U (f z) = z := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have ht : Tendsto (Function.invFunOn f U ∘ f) (𝓝 a) (𝓝 a) :=
    tendsto_id.congr' (Filter.EventuallyEq.symm hl)
  rw [ContinuousAt, hf.2.leftInvOn_invFunOn ha]
  exact (tendsto_map'_iff.mpr ht).mono_left hopen

lemma univalent_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  have han : AnalyticAt ℂ f a := hf.1.analyticOnNhd hU a ha
  have hd_nonconst : ¬ ∀ᶠ z in 𝓝 a, deriv f z = 0 := by
    intro hc
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hc.and (hU.mem_nhds ha))
    have hfball : DifferentiableOn ℂ f (Metric.ball a r) :=
      hf.1.mono (fun z hz => (hball hz).2)
    have hcball : ∀ z ∈ Metric.ball a r, f z = f a := by
      intro z hz
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
        hfball (fun w hw => (hball hw).1) hz (Metric.mem_ball_self hr)
    apply nonconstant_germ_of_injOn hU hf.2 ha
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    exact hcball z hz
  have hd : ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 :=
    han.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left hd_nonconst
  let g := Function.invFunOn f U
  have hgc : ContinuousAt g (f a) := univalent_inverse_continuousAt hU hf ha
  have hga : g (f a) = a := hf.2.leftInvOn_invFunOn ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hright : ∀ᶠ w in 𝓝 (f a), g w ∈ U ∧ f (g w) = w := by
    apply (hopen (Filter.mem_map.mpr ?_))
    filter_upwards [hU.mem_nhds ha] with z hz
    exact ⟨Function.invFunOn_apply_mem hz, Function.invFunOn_apply_eq hz⟩
  have hgne : ∀ᶠ w in 𝓝[≠] (f a), g w ≠ a := by
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
      with w hw hwne
    intro heq
    exact hwne (hw.2.symm.trans (congrArg f heq))
  have hgt : Tendsto g (𝓝[≠] (f a)) (𝓝[≠] a) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hgne⟩
    simpa only [hga] using (hgc.tendsto.mono_left nhdsWithin_le_nhds :
      Tendsto g (𝓝[≠] (f a)) (𝓝 (g (f a))))
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
    filter_upwards [hgt.eventually hd, hright.filter_mono nhdsWithin_le_nhds]
      with w hwder hw
    have hwan : AnalyticAt ℂ f (g w) := hf.1.analyticOnNhd hU (g w) hw.1
    have hws : HasStrictDerivAt f (deriv f (g w)) (g w) :=
      (hwan.contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hl : ∀ᶠ z in 𝓝 (g w), g (f z) = z := by
      filter_upwards [hU.mem_nhds hw.1] with z hz
      exact hf.2.leftInvOn_invFunOn hz
    simpa [hw.2] using (hws.to_local_left_inverse hwder hl).hasDerivAt.differentiableAt
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hgd hgc
  have hcomp := hgan.differentiableAt.hasDerivAt.comp a han.differentiableAt.hasDerivAt
  have hid : (fun z => g (f z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  have hprod : deriv g (f a) * deriv f a = 1 := by
    simpa using (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod

lemma differentiableAt_of_continuous_root {q F : ℂ → ℂ} {z : ℂ}
    (hq : ContinuousAt q z) (hF : DifferentiableAt ℂ F z)
    (hroot : (fun w => q w^2) =ᶠ[𝓝 z] F) (hq0 : q z ≠ 0) :
    DifferentiableAt ℂ q z := by
  have hp : HasStrictDerivAt (fun w : ℂ => w^2) (2*q z) (q z) := by
    have hp := (hasStrictDerivAt_id (q z)).pow 2
    change HasStrictDerivAt (fun w : ℂ => w^2) _ (q z) at hp
    simpa only [id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] using hp
  have hn : 2*q z ≠ 0 := mul_ne_zero (by norm_num) hq0
  let p := hp.localInverse _ _ _ hn
  have hpD : DifferentiableAt ℂ p (F z) := by
    rw [← hroot.self_of_nhds]
    exact (hp.to_localInverse hn).hasDerivAt.differentiableAt
  have he : q =ᶠ[𝓝 z] fun w => p (F w) := by
    filter_upwards [hq.tendsto.eventually (hp.eventually_left_inverse hn),hroot] with w hw hwF
    exact (hwF ▸ hw).symm
  exact (hpD.comp z hF).congr_of_eventuallyEq he

lemma exists_holomorphic_sqrt_disk {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F disk) (hF0 : ∀ z ∈ disk, F z ≠ 0)
    (hFone : F 0 = 1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk, q z^2 = F z) ∧ ∀ z ∈ disk, q z ≠ 0 := by
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  have hsim : IsSimplyConnected disk := by
    have : ContractibleSpace disk := (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0,hdz⟩
    change SimplyConnectedSpace disk
    exact inferInstance
  obtain ⟨q,hqc,hq⟩ := Complex.exists_continuousOn_pow_eq hsim Metric.isOpen_ball hF.continuousOn
    (by rintro ⟨z,hz,he⟩;exact hF0 z hz he) (n := 2) (by norm_num)
  have hqn (z) (hz : z ∈ disk) : q z ≠ 0 := by
    intro he
    have := hq z
    rw [he,zero_pow (by norm_num)] at this
    exact hF0 z hz this.symm
  have hqd : DifferentiableOn ℂ q disk := by
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    apply differentiableAt_of_continuous_root
      (hqc.continuousAt (Metric.isOpen_ball.mem_nhds hz))
      ((hF z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      (Filter.Eventually.of_forall hq) (hqn z hz)
  let Q : ℂ → ℂ := fun z => q z / q 0
  refine ⟨Q,hqd.div_const _,by simp [Q,hqn 0 hdz],?_,?_⟩
  · intro z hz
    simp only [Q,div_pow,hq,hFone,div_one]
  · intro z hz
    exact div_ne_zero (hqn z hz) (hqn 0 hdz)

lemma dslope_factor (f : ℂ → ℂ) (z : ℂ) :
    z * dslope f 0 z = f z-f 0 := by
  simpa only [sub_zero,smul_eq_mul] using sub_smul_dslope f 0 z

lemma sq_mem_disk {z : ℂ} (hz : z ∈ disk) : z^2 ∈ disk := by
  have hn : ‖z‖ < 1 := by simpa [disk] using hz
  simpa [disk] using pow_lt_one₀ (norm_nonneg z) hn (by norm_num : 2 ≠ 0)

lemma exists_odd_transform {f : ℂ → ℂ} (hf : Schlicht f) :
    ∃ q g h H : ℂ → ℂ,
      DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk, q z ≠ 0) ∧
      (∀ z ∈ disk, q z^2 = dslope f 0 z) ∧
      (∀ z, g z = z*q (z^2)) ∧
      UnivalentOn g disk ∧ g 0 = 0 ∧
      DifferentiableOn ℂ h disk ∧ deriv h 0 = -deriv q 0 ∧
      (∀ z ∈ disk, z ≠ 0 → H z = z⁻¹+h z) ∧
      UnivalentOn H (disk \ {0}) ∧
      deriv (deriv f) 0 = 4*deriv q 0 := by
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  let F := dslope f 0
  have hFd : DifferentiableOn ℂ F disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hf.1.1
  have hFn (z) (hz : z ∈ disk) : F z ≠ 0 := by
    by_cases hz0 : z = 0
    · simpa [F,hz0] using (show deriv f 0 ≠ 0 by rw [hf.2.2];norm_num)
    · intro he
      have hfact := dslope_factor f z
      change z*F z = f z-f 0 at hfact
      rw [he,mul_zero] at hfact
      exact hz0 (hf.1.2 hz hdz (sub_eq_zero.mp hfact.symm))
  obtain ⟨q,hqd,hq0,hqs,hqn⟩ := exists_holomorphic_sqrt_disk hFd hFn (by simpa [F] using hf.2.2)
  let Q := dslope q 0
  have hQd : DifferentiableOn ℂ Q disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hqd
  let g : ℂ → ℂ := fun z => z*q (z^2)
  let h : ℂ → ℂ := fun z => -z*Q (z^2)/q (z^2)
  let H : ℂ → ℂ := fun z => (g z)⁻¹
  have hgd : DifferentiableOn ℂ g disk := by
    exact differentiableOn_id.mul (hqd.comp (differentiableOn_id.pow 2) (fun z hz => sq_mem_disk hz))
  have hgs (z) (hz : z ∈ disk) : g z^2 = f (z^2) := by
    dsimp only [g]
    rw [mul_pow,hqs _ (sq_mem_disk hz)]
    simpa [F,hf.2.1] using dslope_factor f (z^2)
  have hgn (z) (hz : z ∈ disk) (hz0 : z ≠ 0) : g z ≠ 0 :=
    mul_ne_zero hz0 (hqn _ (sq_mem_disk hz))
  have hgi : InjOn g disk := by
    intro z hz w hw he
    have hsq : z^2 = w^2 := hf.1.2 (sq_mem_disk hz) (sq_mem_disk hw)
      ((hgs z hz).symm.trans ((congrArg (fun t => t^2) he).trans (hgs w hw)))
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
    · exact heq
    · have hgneg : g z = -g w := by simp [g,heq]
      have hw0 : w = 0 := by
        by_contra hn
        exact hgn w hw hn (by linear_combination (he.symm+hgneg)/2)
      simpa [hw0] using heq
  have hhd : DifferentiableOn ℂ h disk := by
    exact (differentiableOn_id.neg.mul
      (hQd.comp (differentiableOn_id.pow 2) (fun z hz => sq_mem_disk hz))).div
      (hqd.comp (differentiableOn_id.pow 2) (fun z hz => sq_mem_disk hz))
      (fun z hz => hqn _ (sq_mem_disk hz))
  have hderh : deriv h 0 = -deriv q 0 := by
    have hqd0 := ((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hQd0 := ((hQd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => z^2) 0 0 := by
      have hp := (hasDerivAt_id (0 : ℂ)).pow 2
      change HasDerivAt (fun z : ℂ => z^2) _ 0 at hp
      simpa only [id_eq,Nat.reduceSub,pow_one,Nat.cast_ofNat,mul_one,mul_zero] using hp
    have hQcomp : HasDerivAt (fun z : ℂ => Q (z^2)) 0 0 := by
      have hQd0' : HasDerivAt Q (deriv Q 0) ((0 : ℂ)^2) := by simpa using hQd0
      convert hQd0'.comp (h := fun z : ℂ => z^2) 0 hp using 1 <;> first | rfl | simp
    have hqcomp : HasDerivAt (fun z : ℂ => q (z^2)) 0 0 := by
      have hqd0' : HasDerivAt q (deriv q 0) ((0 : ℂ)^2) := by simpa using hqd0
      convert hqd0'.comp (h := fun z : ℂ => z^2) 0 hp using 1 <;> first | rfl | simp
    have hD := ((hasDerivAt_id (0 : ℂ)).neg.mul hQcomp).div hqcomp
      (by simpa using hqn 0 hdz)
    change HasDerivAt h _ 0 at hD
    simpa [Q,hq0] using hD.deriv
  have hdef (z) (hz : z ∈ disk) (hz0 : z ≠ 0) : H z = z⁻¹+h z := by
    have hfact := dslope_factor q (z^2)
    rw [hq0] at hfact
    change z^2 * Q (z^2) = q (z^2)-1 at hfact
    dsimp only [H,g,h]
    field_simp [hz0,hqn _ (sq_mem_disk hz)]
    linear_combination hfact
  have hHu : UnivalentOn H (disk \ {0}) := by
    refine ⟨(hgd.mono sdiff_subset).inv (fun z hz => hgn z hz.1 hz.2),?_⟩
    intro z hz w hw he
    exact hgi hz.1 hw.1 (inv_inj.mp he)
  have hFq : deriv F 0 = 2*deriv q 0 := by
    have hD := (((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).pow 2
    have he : (fun z => q z^2) =ᶠ[𝓝 (0 : ℂ)] F := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      exact hqs z hz
    have := (hD.congr_of_eventuallyEq he.symm).deriv
    simpa [hq0] using this
  have hff : deriv (deriv f) 0 = 2*deriv F 0 := by
    have hidentity : f = fun z => z*F z := by
      funext z
      simpa [hf.2.1,F] using (dslope_factor f z).symm
    have he : deriv f =ᶠ[𝓝 (0 : ℂ)] fun z => F z+z*deriv F z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      have hD := (hasDerivAt_id z).mul
        (((hFd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt)
      rw [hidentity]
      change HasDerivAt (fun w => w*F w) _ z at hD
      simpa using hD.deriv
    have hD := (((hFd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).add
      ((hasDerivAt_id (0 : ℂ)).mul
        (((hFd.deriv Metric.isOpen_ball 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt))
    have := (hD.congr_of_eventuallyEq he).deriv
    simpa [two_mul] using this
  refine ⟨q,g,h,H,hqd,hq0,hqn,hqs,fun _ => rfl,⟨hgd,hgi⟩,by simp [g],hhd,hderh,hdef,hHu,?_⟩
  rw [hff,hFq]
  ring

lemma schlicht_second_deriv_bound {f : ℂ → ℂ} (hf : Schlicht f) :
    ‖deriv (deriv f) 0‖ ≤ 4 := by
  obtain ⟨q,g,h,H,hqd,hq0,hqn,hqs,hgd,hgu,hg0,hhd,hderh,hdef,hHu,hff⟩ :=
    exists_odd_transform hf
  have hbound : ‖deriv h 0‖ ≤ 1 :=
    meromorphic_univalent_coefficient hhd hHu.1 hdef
      (fun z hz => univalent_deriv_ne_zero
        (Metric.isOpen_ball.sdiff isClosed_singleton) hHu hz) hHu.2
  rw [hderh,norm_neg] at hbound
  rw [hff,norm_mul]
  norm_num
  linarith

def diskAutomorphism (a z : ℂ) : ℂ := (z+a)/(1+starRingEnd ℂ a*z)

lemma diskAutomorphism_den_ne_zero {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    1+starRingEnd ℂ a*z ≠ 0 := by
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hnz : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have hb : ‖starRingEnd ℂ a*z‖ < 1 := by
    rw [norm_mul,Complex.norm_conj]
    nlinarith [norm_nonneg a,norm_nonneg z]
  have he' : starRingEnd ℂ a*z = -1 := by linear_combination he
  rw [he'] at hb
  norm_num at hb

lemma diskAutomorphism_normSq_identity (a z : ℂ) :
    Complex.normSq (1+starRingEnd ℂ a*z)-Complex.normSq (z+a) =
      (1-Complex.normSq a)*(1-Complex.normSq z) := by
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring

lemma diskAutomorphism_mem {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    diskAutomorphism a z ∈ disk := by
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hnz : ‖z‖ < 1 := by simpa [disk] using hz
  have hpos : 0 < (1-Complex.normSq a)*(1-Complex.normSq z) := by
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    apply mul_pos <;> nlinarith [norm_nonneg a,norm_nonneg z]
  have hineq := diskAutomorphism_normSq_identity a z
  have hd := diskAutomorphism_den_ne_zero ha hz
  rw [disk,Metric.mem_ball,dist_zero_right,diskAutomorphism,norm_div,div_lt_one (norm_pos_iff.mpr hd)]
  rw [← Complex.sq_norm,← Complex.sq_norm] at hineq
  nlinarith [norm_nonneg (z+a),norm_nonneg (1+starRingEnd ℂ a*z)]

lemma diskAutomorphism_deriv {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskAutomorphism a)
      ((1-(‖a‖^2 : ℝ))/(1+starRingEnd ℂ a*z)^2) z := by
  have hd := ((hasDerivAt_id z).add_const a).div
    (((hasDerivAt_id z).const_mul (starRingEnd ℂ a)).const_add 1)
    (diskAutomorphism_den_ne_zero ha hz)
  convert hd using 1 <;> try rfl
  rw [Complex.sq_norm]
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [id_eq]
  ring

lemma diskAutomorphism_injOn {a : ℂ} (ha : a ∈ disk) : InjOn (diskAutomorphism a) disk := by
  intro z hz w hw he
  have he' := (div_eq_div_iff (diskAutomorphism_den_ne_zero ha hz)
    (diskAutomorphism_den_ne_zero ha hw)).mp he
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hd : (1-starRingEnd ℂ a*a) ≠ 0 := by
    rw [← Complex.normSq_eq_conj_mul_self,← Complex.ofReal_one,← Complex.ofReal_sub]
    apply Complex.ofReal_ne_zero.mpr
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  apply (mul_left_cancel₀ hd)
  linear_combination he'

lemma diskAutomorphism_zero (a : ℂ) : diskAutomorphism a 0 = a := by simp [diskAutomorphism]

lemma diskAutomorphism_differentiableOn {a : ℂ} (ha : a ∈ disk) :
    DifferentiableOn ℂ (diskAutomorphism a) disk :=
  fun _ hz => (diskAutomorphism_deriv ha hz).differentiableAt.differentiableWithinAt

def diskKoebe (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  (f (diskAutomorphism a z)-f a)/((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a)

lemma disk_coeff_ne_zero {a : ℂ} (ha : a ∈ disk) : 1-((‖a‖^2 : ℝ) : ℂ) ≠ 0 := by
  have hn : ‖a‖ < 1 := by simpa [disk] using ha
  rw [← Complex.ofReal_one,← Complex.ofReal_sub,Complex.ofReal_ne_zero]
  nlinarith [norm_nonneg a]

lemma diskKoebe_univalent {f : ℂ → ℂ} {a : ℂ} (hf : UnivalentOn f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) : UnivalentOn (diskKoebe f a) disk := by
  refine ⟨?_,?_⟩
  · exact ((hf.1.comp (diskAutomorphism_differentiableOn ha)
      (fun _ hz => diskAutomorphism_mem ha hz)).sub_const (f a)).div_const _
  · intro z hz w hw he
    have he' := (div_left_inj' (mul_ne_zero (disk_coeff_ne_zero ha) hfd)).mp he
    exact diskAutomorphism_injOn ha hz hw
      (hf.2 (diskAutomorphism_mem ha hz) (diskAutomorphism_mem ha hw) (sub_left_inj.mp he'))

lemma diskKoebe_deriv {f : ℂ → ℂ} {a z : ℂ} (hf : DifferentiableOn ℂ f disk)
    (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskKoebe f a)
      ((deriv f (diskAutomorphism a z)*((1-((‖a‖^2 : ℝ) : ℂ))/(1+starRingEnd ℂ a*z)^2))/
        ((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a)) z := by
  exact ((((hf _ (diskAutomorphism_mem ha hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (diskAutomorphism_mem ha hz))).hasDerivAt.comp z
    (diskAutomorphism_deriv ha hz)).sub_const (f a)).div_const _

lemma diskKoebe_schlicht {f : ℂ → ℂ} {a : ℂ} (hf : UnivalentOn f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) : Schlicht (diskKoebe f a) := by
  refine ⟨diskKoebe_univalent hf ha hfd, ?_, ?_⟩
  · simp [diskKoebe,diskAutomorphism_zero]
  · have hd := (diskKoebe_deriv hf.1 ha (by simp [disk] : (0 : ℂ) ∈ disk)).deriv
    rw [hd]
    simp only [diskAutomorphism_zero,mul_zero,add_zero,one_pow,div_one]
    rw [mul_comm (deriv f a),div_self (mul_ne_zero (disk_coeff_ne_zero ha) hfd)]

lemma diskKoebe_second_deriv {f : ℂ → ℂ} {a : ℂ} (hf : DifferentiableOn ℂ f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) :
    deriv (deriv (diskKoebe f a)) 0 =
      (1-((‖a‖^2 : ℝ) : ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have he : deriv (diskKoebe f a) =ᶠ[𝓝 (0 : ℂ)]
      fun z => (deriv f (diskAutomorphism a z)*
        ((1-((‖a‖^2 : ℝ) : ℂ))/(1+starRingEnd ℂ a*z)^2))/
        ((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (diskKoebe_deriv hf ha hz).deriv
  have hda := ((hf.deriv Metric.isOpen_ball a ha).differentiableAt
    (Metric.isOpen_ball.mem_nhds ha)).hasDerivAt
  have hda' : HasDerivAt (deriv f) (deriv (deriv f) a) (diskAutomorphism a 0) := by
    simpa [diskAutomorphism_zero] using hda
  have hcomp := hda'.comp 0 (diskAutomorphism_deriv ha hzero)
  have hrat := (hasDerivAt_const (0 : ℂ) (1-((‖a‖^2 : ℝ) : ℂ))).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (starRingEnd ℂ a)).const_add 1).pow 2)
    (by simp)
  have hd := ((hcomp.mul hrat).div_const
    ((1-((‖a‖^2 : ℝ) : ℂ))*deriv f a)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.div_apply,Pi.pow_apply,Function.comp_apply,diskAutomorphism_zero,
    mul_zero,add_zero,one_pow,div_one,zero_sub,id_eq,mul_one]
  have halg (A B C D : ℂ) (hB : B ≠ 0) (hC : C ≠ 0) :
      (A*C*C+B*(-(C*(2*D))))/(C*B) = C*A/B-2*D := by
    field_simp
    ring
  exact halg (deriv (deriv f) a) (deriv f a)
    (1-((‖a‖^2 : ℝ) : ℂ)) (starRingEnd ℂ a) hfd (disk_coeff_ne_zero ha)

def omittedTransform (f : ℂ → ℂ) (w z : ℂ) : ℂ := w*f z/(w-f z)

lemma omittedTransform_univalent {f : ℂ → ℂ} {w : ℂ}
    (hf : UnivalentOn f disk) (hw : w ∉ f '' disk) (hw0 : w ≠ 0) :
    UnivalentOn (omittedTransform f w) disk := by
  have hn (z) (hz : z ∈ disk) : w-f z ≠ 0 := by
    intro he
    exact hw ⟨z,hz,(sub_eq_zero.mp he).symm⟩
  refine ⟨(hf.1.const_mul w).div (hf.1.const_sub w) hn,?_⟩
  intro z hz v hv he
  apply hf.2 hz hv
  apply mul_left_cancel₀ (pow_ne_zero 2 hw0)
  have he' := (div_eq_div_iff (hn z hz) (hn v hv)).mp he
  linear_combination he'

lemma omittedTransform_deriv {f : ℂ → ℂ} {w z : ℂ}
    (hf : DifferentiableOn ℂ f disk) (hw : w ∉ f '' disk) (hz : z ∈ disk) :
    HasDerivAt (omittedTransform f w) (w^2*deriv f z/(w-f z)^2) z := by
  have hn : w-f z ≠ 0 := fun he => hw ⟨z,hz,(sub_eq_zero.mp he).symm⟩
  have hd := ((hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  convert (hd.const_mul w).div (hd.const_sub w) hn using 1 <;> try rfl
  ring

lemma omittedTransform_schlicht {f : ℂ → ℂ} {w : ℂ}
    (hf : Schlicht f) (hw : w ∉ f '' disk) : Schlicht (omittedTransform f w) := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0,hzero,hf.2.1.trans h.symm⟩
  refine ⟨omittedTransform_univalent hf.1 hw hw0,?_,?_⟩
  · simp [omittedTransform,hf.2.1]
  · rw [(omittedTransform_deriv hf.1.1 hw hzero).deriv,hf.2.1,hf.2.2]
    simp [hw0]

lemma omittedTransform_second_deriv {f : ℂ → ℂ} {w : ℂ}
    (hf : Schlicht f) (hw : w ∉ f '' disk) :
    deriv (deriv (omittedTransform f w)) 0 = deriv (deriv f) 0+2/w := by
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0,hzero,hf.2.1.trans h.symm⟩
  have he : deriv (omittedTransform f w) =ᶠ[𝓝 (0 : ℂ)]
      fun z => w^2*deriv f z/(w-f z)^2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz
    exact (omittedTransform_deriv hf.1.1 hw hz).deriv
  have hfd := ((hf.1.1 0 hzero).differentiableAt (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hfdd := ((hf.1.1.deriv Metric.isOpen_ball 0 hzero).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hd := ((hfdd.const_mul (w^2)).div ((hfd.const_sub w).pow 2)
    (by simpa [hf.2.1] using pow_ne_zero 2 hw0)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.pow_apply,hf.2.1,hf.2.2,sub_zero,mul_one]
  field_simp [hw0]
  ring

lemma schlicht_preSchwarzian_bound {f : ℂ → ℂ} (hf : Schlicht f) {a : ℂ} (ha : a ∈ disk) :
    ‖(1-((‖a‖^2 : ℝ) : ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a‖ ≤ 4 := by
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf.1 ha
  have hb := schlicht_second_deriv_bound (diskKoebe_schlicht hf.1 ha hn)
  rwa [diskKoebe_second_deriv hf.1.1 ha hn] at hb

lemma schlicht_quarter {f : ℂ → ℂ} (hf : Schlicht f) :
    Metric.ball (0 : ℂ) (1/4) ⊆ f '' disk := by
  intro w hw
  by_contra hnot
  have hz : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hnot ⟨0,hz,hf.2.1.trans h.symm⟩
  have hb := schlicht_second_deriv_bound (omittedTransform_schlicht hf hnot)
  rw [omittedTransform_second_deriv hf hnot] at hb
  have hdiff : ‖(2 : ℂ)/w‖ ≤ 8 := by
    have ht := norm_sub_le (deriv (deriv f) 0+2/w) (deriv (deriv f) 0)
    have hf2 := schlicht_second_deriv_bound hf
    simp only [add_sub_cancel_left] at ht
    linarith
  rw [norm_div] at hdiff
  norm_num at hdiff
  have hle := (div_le_iff₀ (norm_pos_iff.mpr hw0)).mp hdiff
  have hw' : ‖w‖ < 1/4 := by simpa using hw
  linarith

lemma hasDerivAt_log_norm_real {g : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hg : HasDerivAt g d x) (hn : g x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖g t‖) (d/g x).re x := by
  have heq : (fun t => Real.log ‖g t‖) =
      (fun t => (1/2 : ℝ)*Real.log (‖g t‖^2)) := by
    funext t
    rw [Real.log_pow]
    ring
  have hd := ((hg.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1/2 : ℝ)
  rw [heq]
  refine hd.congr_deriv ?_
  simp only [Complex.inner,Complex.conj_re,Complex.conj_im,Complex.mul_re,
    Complex.div_re,Complex.normSq_eq_norm_sq]
  ring

lemma logarithmic_distortion {L D : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hL : ∀ x ∈ Icc 0 r, HasDerivAt L (D x) x) (hL0 : L 0 = 0)
    (hbound : ∀ x ∈ Icc 0 r,
      (2*x-4)/(1-x^2) ≤ D x ∧ D x ≤ (2*x+4)/(1-x^2)) :
    Real.log (1-r)-3*Real.log (1+r) ≤ L r ∧
      L r ≤ Real.log (1+r)-3*Real.log (1-r) := by
  have hp (x : ℝ) (hx : x ∈ Icc 0 r) : 0 < 1-x ∧ 0 < 1+x ∧ 0 < 1-x^2 := by
    constructor
    · linarith [hx.2]
    constructor
    · linarith [hx.1]
    · have := hx.1
      nlinarith [hx.2]
  let U := fun x => L x-Real.log (1+x)+3*Real.log (1-x)
  let V := fun x => L x-Real.log (1-x)+3*Real.log (1+x)
  have hU (x) (hx : x ∈ Icc 0 r) : HasDerivAt U
      (D x-1/(1+x)-3/(1-x)) x := by
    have hlogp := ((hasDerivAt_id x).const_add 1).log (ne_of_gt (hp x hx).2.1)
    have hlogm := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt (hp x hx).1)
    convert ((hL x hx).sub hlogp).add (hlogm.const_mul 3) using 1 <;> try rfl
    simp
    ring
  have hV (x) (hx : x ∈ Icc 0 r) : HasDerivAt V
      (D x+1/(1-x)+3/(1+x)) x := by
    have hlogp := ((hasDerivAt_id x).const_add 1).log (ne_of_gt (hp x hx).2.1)
    have hlogm := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt (hp x hx).1)
    convert ((hL x hx).sub hlogm).add (hlogp.const_mul 3) using 1 <;> try rfl
    simp
    ring
  have halg (x) (hx : x ∈ Icc 0 r) :
      1/(1+x)+3/(1-x) = (2*x+4)/(1-x^2) ∧
      -(1/(1-x)+3/(1+x)) = (2*x-4)/(1-x^2) := by
    constructor <;> field_simp [(hp x hx).1.ne', (hp x hx).2.1.ne', (hp x hx).2.2.ne'] <;> ring
  have hUa : AntitoneOn U (Icc 0 r) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 r)
      (fun x hx => (hU x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hU x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hU x (interior_subset hx)).deriv]
    have hb := (hbound x (interior_subset hx)).2
    rw [← (halg x (interior_subset hx)).1] at hb
    linarith
  have hVm : MonotoneOn V (Icc 0 r) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
      (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hV x (interior_subset hx)).differentiableAt.differentiableWithinAt)
    intro x hx
    rw [(hV x (interior_subset hx)).deriv]
    have hb := (hbound x (interior_subset hx)).1
    rw [← (halg x (interior_subset hx)).2] at hb
    linarith
  have hu := hUa (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hv := hVm (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  dsimp [U,V] at hu hv
  simp only [hL0,add_zero,sub_zero,Real.log_one,mul_zero] at hu hv
  constructor <;> linarith

lemma radialDistortion_of_preSchwarzian {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f disk) (hf0 : deriv f 0 = 1)
    (hfn : ∀ a ∈ disk, deriv f a ≠ 0)
    (hps : ∀ a ∈ disk,
      ‖(1-((‖a‖^2 : ℝ) : ℂ))*deriv (deriv f) a/deriv f a-2*starRingEnd ℂ a‖ ≤ 4)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (1-r)/(1+r)^3 ≤ ‖deriv f ((r : ℂ)*ζ)‖ ∧
      ‖deriv f ((r : ℂ)*ζ)‖ ≤ (1+r)/(1-r)^3 := by
  let L : ℝ → ℝ := fun x => Real.log ‖deriv f ((x : ℂ)*ζ)‖
  let D : ℝ → ℝ := fun x => (deriv (deriv f) ((x : ℂ)*ζ)*ζ/deriv f ((x : ℂ)*ζ)).re
  have hn (x) (hx : x ∈ Icc 0 r) : ‖(x : ℂ)*ζ‖ = x := by
    rw [norm_mul,hζ,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hx.1]
  have hm (x) (hx : x ∈ Icc 0 r) : (x : ℂ)*ζ ∈ disk := by
    simp only [disk,Metric.mem_ball,dist_zero_right,hn x hx]
    exact hx.2.trans_lt hr1
  have hD (x) (hx : x ∈ Icc 0 r) : HasDerivAt L (D x) x := by
    have hd := ((hf.deriv Metric.isOpen_ball _ (hm x hx)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hm x hx))).hasDerivAt
    have hx' : HasDerivAt (fun t : ℝ => (t : ℂ)*ζ) ζ x := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun t : ℝ => Complex.ofRealCLM t*ζ) ((Complex.ofRealCLM (1 : ℝ))*ζ) x)
    have hdc : HasDerivAt (fun t : ℝ => deriv f ((t : ℂ)*ζ))
        (deriv (deriv f) ((x : ℂ)*ζ)*ζ) x := by
      convert HasDerivAt.comp (𝕜 := ℝ) x hd hx' using 1 <;> rfl
    exact hasDerivAt_log_norm_real hdc (hfn _ (hm x hx))
  have hb (x) (hx : x ∈ Icc 0 r) :
      (2*x-4)/(1-x^2) ≤ D x ∧ D x ≤ (2*x+4)/(1-x^2) := by
    let A : ℂ := (1-((x^2 : ℝ) : ℂ))*deriv (deriv f) ((x : ℂ)*ζ)/deriv f ((x : ℂ)*ζ)
      -2*starRingEnd ℂ ((x : ℂ)*ζ)
    have hA : ‖A*ζ‖ ≤ 4 := by
      rw [norm_mul,hζ,mul_one]
      simpa only [A,hn x hx] using hps _ (hm x hx)
    have he : (A*ζ).re = (1-x^2)*D x-2*x := by
      have hzz : starRingEnd ℂ ζ*ζ = 1 := by
        rw [← Complex.normSq_eq_conj_mul_self,← Complex.sq_norm,hζ]
        norm_num
      have heq : A*ζ = ((1-x^2 : ℝ) : ℂ)*
          (deriv (deriv f) ((x : ℂ)*ζ)*ζ/deriv f ((x : ℂ)*ζ))-2*(x : ℂ) := by
        dsimp only [A]
        rw [map_mul,Complex.conj_ofReal]
        rw [Complex.ofReal_sub,Complex.ofReal_one]
        linear_combination -2*(x : ℂ)*hzz
      rw [heq]
      simp only [D,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        zero_mul,sub_zero]
      norm_num
    have hreal := (Complex.abs_re_le_norm (A*ζ)).trans hA
    rw [he,abs_le] at hreal
    have hpos : 0 < 1-x^2 := by nlinarith [hx.1,hx.2]
    constructor
    · rw [div_le_iff₀ hpos]
      nlinarith [hreal.1]
    · rw [le_div_iff₀ hpos]
      nlinarith [hreal.2]
  have hbnd := logarithmic_distortion hr hr1 hD (by simp [L,hf0]) hb
  have hposm : 0 < 1-r := sub_pos.mpr hr1
  have hposp : 0 < 1+r := by linarith
  have hnorm : 0 < ‖deriv f ((r : ℂ)*ζ)‖ := norm_pos_iff.mpr (hfn _ (hm r (right_mem_Icc.mpr hr)))
  constructor
  · apply (Real.log_le_log_iff (div_pos hposm (pow_pos hposp 3)) hnorm).mp
    simpa only [Real.log_div hposm.ne' (pow_ne_zero 3 hposp.ne'),Real.log_pow,Nat.cast_ofNat] using hbnd.1
  · apply (Real.log_le_log_iff hnorm (div_pos hposp (pow_pos hposm 3))).mp
    simpa only [Real.log_div hposp.ne' (pow_ne_zero 3 hposm.ne'),Real.log_pow,Nat.cast_ofNat] using hbnd.2

lemma schlicht_deriv_bounds {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    (1-‖z‖)/(1+‖z‖)^3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1+‖z‖)/(1-‖z‖)^3 := by
  by_cases hzero : z = 0
  · simp [hzero,hf.2.2]
  have hn := norm_pos_iff.mpr hzero
  have hζ : ‖z/(‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg z),div_self hn.ne']
  have heq : (‖z‖ : ℂ)*(z/(‖z‖ : ℂ)) = z := by
    field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast hn.ne']
  have hb := radialDistortion_of_preSchwarzian hf.1.1 hf.2.2
    (fun _ ha => univalent_deriv_ne_zero Metric.isOpen_ball hf.1 ha)
    (fun _ ha => schlicht_preSchwarzian_bound hf ha) (norm_nonneg z)
    (show ‖z‖ < 1 by simpa [disk] using hz) hζ
  rwa [heq] at hb

lemma schlicht_deriv_compact_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖deriv f z‖ ≤ 2/(1-R)^3 := by
  have hzm : z ∈ disk := by simpa [disk] using hz.trans_lt hR
  apply (schlicht_deriv_bounds hf hzm).2.trans
  have hd : 0 < 1-R := sub_pos.mpr hR
  apply div_le_div₀ (by positivity) (by linarith [norm_nonneg z]) (by positivity)
  exact pow_le_pow_left₀ hd.le (by linarith) 3

lemma schlicht_lipschitz_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖f z-f w‖ ≤ (2/(1-R)^3)*‖z-w‖ := by
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Metric.closedBall 0 R)
    (𝕜 := ℂ) _ _ (convex_closedBall 0 R)
    (by simpa using hw) (by simpa using hz)
  · intro x hx
    apply (hf.1.1 x _).differentiableAt
      (Metric.isOpen_ball.mem_nhds (show x ∈ disk from ?_))
    all_goals simpa [disk] using (show ‖x‖ ≤ R by simpa using hx).trans_lt hR
  · intro x hx
    exact schlicht_deriv_compact_bound hf hR (by simpa using hx)

lemma schlicht_local_bound {f : ℂ → ℂ} (hf : Schlicht f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖f z‖ ≤ (2/(1-R)^3)*R := by
  have h := schlicht_lipschitz_bound hf hR hz
    (show ‖(0 : ℂ)‖ ≤ R by simpa using (norm_nonneg z).trans hz)
  simp only [hf.2.1,sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hz (by positivity))

lemma affine_disk_maps_ball (a : ℂ) {R : ℝ} (hR : 0 < R) :
    MapsTo (fun z : ℂ => a+(R : ℂ)*z) disk (Metric.ball a R) := by
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  simp only [Metric.mem_ball,dist_eq_norm,add_sub_cancel_left,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
  nlinarith

lemma ballNormalize_deriv {f : ℂ → ℂ} {a z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball a R)) (hz : z ∈ disk) :
    HasDerivAt (ballNormalize f a R)
      (deriv f (a+(R : ℂ)*z)/deriv f a) z := by
  have hmap := affine_disk_maps_ball a hR hz
  have hd := ((hf _ hmap).differentiableAt (Metric.isOpen_ball.mem_nhds hmap)).hasDerivAt
  have hdz := (((hd.comp z (((hasDerivAt_id z).const_mul (R : ℂ)).const_add a)).sub_const (f a)).div_const
    ((R : ℂ)*deriv f a))
  convert hdz using 1 <;> try rfl
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [mul_one]
  field_simp

lemma ballNormalize_schlicht {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) (hn : deriv f a ≠ 0) :
    Schlicht (ballNormalize f a R) := by
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hmap := affine_disk_maps_ball a hR
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (ballNormalize_deriv hR hf.1 hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    apply mul_left_cancel₀ hRc
    apply add_left_cancel (a := a)
    apply hf.2 (hmap hz) (hmap hw)
    have he' := (div_left_inj' (mul_ne_zero hRc hn)).mp he
    exact sub_left_inj.mp he'
  · simp [ballNormalize]
  · rw [(ballNormalize_deriv hR hf.1 (show (0 : ℂ) ∈ disk by simp [disk])).deriv]
    simp [hn]

lemma univalent_ball_quarter {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) :
    Metric.ball (f a) (R*‖deriv f a‖/4) ⊆ f '' Metric.ball a R := by
  have ha : a ∈ Metric.ball a R := Metric.mem_ball_self hR
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf ha
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hden := mul_ne_zero hRc hn
  intro w hw
  have hu : (w-f a)/((R : ℂ)*deriv f a) ∈ Metric.ball (0 : ℂ) (1/4) := by
    simp only [Metric.mem_ball,dist_zero_right,norm_div,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos hR]
    rw [div_lt_iff₀ (mul_pos hR (norm_pos_iff.mpr hn))]
    have hw' : ‖w-f a‖ < R*‖deriv f a‖/4 := by simpa [dist_eq_norm] using hw
    linarith
  obtain ⟨z,hz,he⟩ := schlicht_quarter (ballNormalize_schlicht hR hf hn) hu
  refine ⟨a+(R : ℂ)*z,affine_disk_maps_ball a hR hz,?_⟩
  have hes := (div_left_inj' hden).mp he
  exact sub_left_inj.mp hes

lemma schlicht_separation {f : ℂ → ℂ} (hf : Schlicht f)
    {z w : ℂ} (_hz : z ∈ disk) (hw : w ∈ disk) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.ball z R ⊆ disk) (hdist : R ≤ ‖w-z‖) :
    R*‖deriv f z‖/4 ≤ ‖f w-f z‖ := by
  by_contra! hlt
  have hm : f w ∈ Metric.ball (f z) (R*‖deriv f z‖/4) := by
    simpa [dist_eq_norm] using hlt
  obtain ⟨v,hv,he⟩ := univalent_ball_quarter hR ⟨hf.1.1.mono hsub,hf.1.2.mono hsub⟩ hm
  have hvw := hf.1.2 (hsub hv) hw he
  subst v
  have : ‖w-z‖ < R := by simpa [dist_eq_norm] using hv
  exact (not_lt_of_ge hdist) this

lemma schlicht_uniform_separation {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk)
    (hne : z ≠ w) : ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ, Schlicht f → c ≤ ‖f w-f z‖ := by
  have hz1 : ‖z‖ < 1 := by simpa [disk] using hz
  let R := min ((1-‖z‖)/2) (‖w-z‖/2)
  have hR : 0 < R := lt_min (by linarith)
    (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) (by norm_num))
  have hR1 : R ≤ (1-‖z‖)/2 := min_le_left _ _
  have hR2 : R ≤ ‖w-z‖/2 := min_le_right _ _
  have hsub : Metric.ball z R ⊆ disk := by
    intro v hv
    have hvR : ‖v-z‖ < R := by simpa [dist_eq_norm] using hv
    have ht := norm_add_le (v-z) z
    rw [sub_add_cancel] at ht
    simp only [disk,Metric.mem_ball,dist_zero_right]
    linarith
  refine ⟨R*((1-‖z‖)/(1+‖z‖)^3)/4,by positivity,?_⟩
  intro f hf
  have h := schlicht_separation hf hz hw hR hsub (by linarith [norm_nonneg (w-z)])
  apply le_trans _ h
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (schlicht_deriv_bounds hf hz).1 hR.le)
    (by norm_num)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CompactClass
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma compact_closure_of_disk_bounds (S : Set C(disk,ℂ))
    (hLip : ∀ R : ℝ, R < 1 → ∃ C : ℝ, ∀ g ∈ S, ∀ z w : disk,
      ‖(z : ℂ)‖ ≤ R → ‖(w : ℂ)‖ ≤ R → ‖g z-g w‖ ≤ C*‖(z : ℂ)-(w : ℂ)‖)
    (hBd : ∀ z : disk, ∃ C : ℝ, ∀ g ∈ S, ‖g z‖ ≤ C) :
    IsCompact (closure S) := by
  let : T2Space (UniformOnFun disk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have heq : Equicontinuous (fun g : S => fun z : disk => g.1 z) := by
    intro z
    obtain ⟨R,hzR,hR⟩ := exists_between (show ‖(z : ℂ)‖ < 1 by simpa [disk] using z.2)
    obtain ⟨C,hC⟩ := hLip R hR
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w : disk => C*dist (z : ℂ) (w : ℂ))
    · simpa using (tendsto_const_nhds (x := C)).mul
        ((tendsto_const_nhds (x := (z : ℂ))).dist (continuous_subtype_val.tendsto z))
    · have hn : ∀ᶠ w : disk in 𝓝 z, ‖(w : ℂ)‖ < R :=
        (continuous_norm.comp continuous_subtype_val).continuousAt (Iio_mem_nhds hzR)
      filter_upwards [hn] with w hw g
      simpa [dist_eq_norm] using hC g.1 g.2 z w hzR.le hw.le
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun g : C(disk,ℂ) => fun z : disk => g z)
    (𝔖 := {K | IsCompact K}) (fun _ h => h)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K _
    exact heq.equicontinuousOn K
  · intro K _ z _
    obtain ⟨C,hC⟩ := hBd z
    exact ⟨Metric.closedBall 0 C,isCompact_closedBall _ _,by simpa using hC⟩

lemma diskExtend_convergence.{u_1} {ι : Type u_1} {l : Filter ι}
    {g : ι → C(disk,ℂ)} {f : C(disk,ℂ)} (h : Tendsto g l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => diskExtend (g i)) (diskExtend f) l disk := by
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def,diskExtend_apply] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h

lemma isClosed_diskSchlichtSet : IsClosed diskSchlichtSet := by
  rw [isClosed_iff_forall_filter]
  intro g l hl hs hg
  let := hl
  have hS : ∀ᶠ f : C(disk,ℂ) in l, Schlicht (diskExtend f) :=
    le_principal_iff.mp hs
  have hc := diskExtend_convergence (g := id) hg
  have hhol : ∀ᶠ f : C(disk,ℂ) in l, DifferentiableOn ℂ (diskExtend f) disk :=
    hS.mono (fun _ h => h.1.1)
  have hgH := hc.differentiableOn hhol (show IsOpen disk from Metric.isOpen_ball)
  refine ⟨⟨hgH,?_⟩,?_,?_⟩
  · intro z hz w hw he
    by_contra hne
    obtain ⟨c,hc0,hs⟩ := schlicht_uniform_separation hz hw hne
    have hevent : ∀ᶠ f : C(disk,ℂ) in l, c ≤ ‖diskExtend f w-diskExtend f z‖ :=
      hS.mono (fun f hf => hs (diskExtend f) hf)
    have ht := ((hc.tendsto_at hw).sub (hc.tendsto_at hz)).norm
    have hc' := ge_of_tendsto ht hevent
    rw [he,sub_self,norm_zero] at hc'
    exact not_le_of_gt hc0 hc'
  · apply tendsto_nhds_unique (hc.tendsto_at (show (0 : ℂ) ∈ disk by simp [disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.1.symm))
  · apply tendsto_nhds_unique ((hc.deriv hhol (show IsOpen disk from Metric.isOpen_ball)).tendsto_at
      (show (0 : ℂ) ∈ disk by simp [disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.2.symm))

lemma isCompact_diskSchlichtSet : IsCompact diskSchlichtSet := by
  rw [← isClosed_diskSchlichtSet.closure_eq]
  apply compact_closure_of_disk_bounds
  · intro R hR
    refine ⟨2/(1-R)^3,?_⟩
    intro g hg z w hz hw
    simpa only [diskExtend_apply] using schlicht_lipschitz_bound hg hR hz hw
  · intro z
    refine ⟨(2/(1-‖(z : ℂ)‖)^3)*‖(z : ℂ)‖,?_⟩
    intro g hg
    simpa only [diskExtend_apply] using schlicht_local_bound hg
      (show ‖(z : ℂ)‖ < 1 by simpa [disk] using z.2) le_rfl

def DiskClass := diskSchlichtSet

instance instTopologicalSpaceElemContinuousMapComplexDiskDiskClass : TopologicalSpace DiskClass := inferInstanceAs (TopologicalSpace diskSchlichtSet)

instance instCompactSpaceElemContinuousMapComplexDiskDiskClass : CompactSpace DiskClass := isCompact_iff_compactSpace.mp isCompact_diskSchlichtSet

lemma differentiableOn_iteratedDeriv_disk {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    (n : ℕ) : DifferentiableOn ℂ (iteratedDeriv n f) disk := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv (show IsOpen disk from Metric.isOpen_ball)

lemma tendstoLocallyUniformlyOn_iteratedDeriv_disk.{u_1} {ι : Type u_1} {l : Filter ι}
    {f : ι → ℂ → ℂ} {g : ℂ → ℂ} (h : TendstoLocallyUniformlyOn f g l disk)
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) disk) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l disk := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hf.mono (fun i h => differentiableOn_iteratedDeriv_disk h n))
      (show IsOpen disk from Metric.isOpen_ball)

def diskClassJet (n : ℕ) (g : DiskClass) : C(disk,ℂ) :=
  ⟨fun z => iteratedDeriv n (diskExtend g.1) z,
    continuousOn_iff_continuous_domRestrict.mp
      (differentiableOn_iteratedDeriv_disk g.2.1.1 n).continuousOn⟩

lemma continuous_diskClassJet (n : ℕ) : Continuous (diskClassJet n) := by
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have h := tendstoLocallyUniformlyOn_iteratedDeriv_disk
    (diskExtend_convergence (continuous_subtype_val.tendsto g))
    (Eventually.of_forall (fun f : DiskClass => f.2.1.1)) n
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp h

lemma continuous_diskClassJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × disk => iteratedDeriv n (diskExtend p.1.1) p.2) :=
  continuous_eval.comp ((continuous_diskClassJet n).prodMap continuous_id)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.HalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def halfPlane : Set ℂ := {z | 0 < z.im}

lemma isOpen_halfPlane : IsOpen halfPlane :=
  isOpen_lt continuous_const Complex.continuous_im

def HalfPlaneSchlicht (f : ℂ → ℂ) : Prop :=
  UnivalentOn f halfPlane ∧ f Complex.I = 0 ∧ deriv f Complex.I = 1

def affine (z w : ℂ) : ℂ := (z.re : ℂ) + (z.im : ℂ) * w

@[simp] lemma affine_I (z : ℂ) : affine z Complex.I = z := by
  apply Complex.ext <;> simp [affine]

@[simp] lemma I_affine (w : ℂ) : affine Complex.I w = w := by
  simp [affine]

lemma affine_mem {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    affine z w ∈ halfPlane := by
  change 0 < (affine z w).im
  simpa [affine] using mul_pos hz hw

lemma affine_injective {z : ℂ} (hz : z ∈ halfPlane) : Function.Injective (affine z) := by
  intro u v h
  dsimp [affine] at h
  exact (mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))) (add_left_cancel h)

lemma hasDerivAt_affine (z w : ℂ) : HasDerivAt (affine z) (z.im : ℂ) w := by
  convert (hasDerivAt_const w (z.re : ℂ)).add
    ((hasDerivAt_id w).const_mul (z.im : ℂ)) using 1 <;> first | rfl | simp

def reroot (f : ℂ → ℂ) (z w : ℂ) : ℂ :=
  (f (affine z w) - f z) / ((z.im : ℂ) * deriv f z)

lemma hasDerivAt_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    HasDerivAt (reroot f z) (deriv f (affine z w) / deriv f z) w := by
  have hfd := (hf.1 (affine z w) (affine_mem hz hw)).differentiableAt
    (isOpen_halfPlane.mem_nhds (affine_mem hz hw))
  have h := ((hfd.hasDerivAt.comp w (hasDerivAt_affine z w)).sub_const (f z)).div_const
    ((z.im : ℂ) * deriv f z)
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  convert h using 1 <;> first | rfl | field_simp

lemma deriv_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    deriv (reroot f z) w = deriv f (affine z w) / deriv f z :=
  (hasDerivAt_reroot hf hz hw).deriv

lemma reroot_normalized {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) : HalfPlaneSchlicht (reroot f z) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hdf : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro w hw
    exact (hasDerivAt_reroot hf hz hw).differentiableAt.differentiableWithinAt
  · intro u hu v hv h
    apply affine_injective hz
    apply hf.2 (affine_mem hz hu) (affine_mem hz hv)
    have hh : f (affine z u) - f z = f (affine z v) - f z :=
      (div_left_inj' (mul_ne_zero hy hdf)).mp h
    exact sub_left_injective hh
  · simp [reroot]
  · rw [deriv_reroot hf hz (by simp [halfPlane]), affine_I, div_self hdf]

def reciprocalDeriv (f : ℂ → ℂ) (z : ℂ) : ℂ := (deriv f z)⁻¹

def diskCayley (z : ℂ) : ℂ := (z-Complex.I)/(z+Complex.I)

def halfCayley (z : ℂ) : ℂ := Complex.I*(1+z)/(1-z)

lemma cayley_den_ne_zero {z : ℂ} (hz : z ∈ halfPlane) : z+Complex.I ≠ 0 := by
  intro he
  have := congrArg Complex.im he
  simp only [Complex.add_im,Complex.I_im,Complex.zero_im] at this
  change 0 < z.im at hz
  linarith

lemma halfCayley_den_ne_zero {z : ℂ} (hz : z ∈ disk) : 1-z ≠ 0 := by
  intro he
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  rw [← sub_eq_zero.mp he] at hz'
  norm_num at hz'

lemma diskCayley_maps {z : ℂ} (hz : z ∈ halfPlane) : diskCayley z ∈ disk := by
  have hd := cayley_den_ne_zero hz
  simp only [disk,Metric.mem_ball,dist_zero_right,diskCayley,norm_div]
  rw [div_lt_one (norm_pos_iff.mpr hd)]
  have hsql : ‖z-Complex.I‖^2 = z.re^2+(z.im-1)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hsqr : ‖z+Complex.I‖^2 = z.re^2+(z.im+1)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hz' : 0 < z.im := hz
  nlinarith [norm_nonneg (z+Complex.I),norm_nonneg (z-Complex.I)]

lemma halfCayley_im {z : ℂ} (_hz : z ∈ disk) :
    (halfCayley z).im = (1-‖z‖^2)/‖1-z‖^2 := by
  simp only [halfCayley,Complex.div_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma halfCayley_maps {z : ℂ} (hz : z ∈ disk) : halfCayley z ∈ halfPlane := by
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  change 0 < (halfCayley z).im
  rw [halfCayley_im hz]
  exact div_pos (by nlinarith [norm_nonneg z])
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (halfCayley_den_ne_zero hz)))

lemma halfCayley_diskCayley {z : ℂ} (hz : z ∈ halfPlane) : halfCayley (diskCayley z) = z := by
  have hd := cayley_den_ne_zero hz
  have hd2 := halfCayley_den_ne_zero (diskCayley_maps hz)
  dsimp [halfCayley,diskCayley] at *
  field_simp
  ring_nf

lemma diskCayley_halfCayley {z : ℂ} (hz : z ∈ disk) : diskCayley (halfCayley z) = z := by
  have hd := halfCayley_den_ne_zero hz
  have hd2 := cayley_den_ne_zero (halfCayley_maps hz)
  dsimp [halfCayley,diskCayley] at *
  field_simp
  ring

lemma diskCayley_hasDerivAt {z : ℂ} (hz : z ∈ halfPlane) :
    HasDerivAt diskCayley (2*Complex.I/(z+Complex.I)^2) z := by
  convert ((hasDerivAt_id z).sub_const Complex.I).div
    ((hasDerivAt_id z).add_const Complex.I) (cayley_den_ne_zero hz) using 1 <;> try rfl
  simp only [id_eq,mul_one,one_mul]
  ring

lemma halfCayley_hasDerivAt {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt halfCayley (2*Complex.I/(1-z)^2) z := by
  convert (((hasDerivAt_id z).const_add 1).const_mul Complex.I).div
    ((hasDerivAt_id z).const_sub 1) (halfCayley_den_ne_zero hz) using 1 <;> try rfl
  simp only [id_eq,mul_one]
  ring

@[simp] lemma diskCayley_I : diskCayley Complex.I = 0 := by simp [diskCayley]

@[simp] lemma halfCayley_zero : halfCayley 0 = Complex.I := by simp [halfCayley]

def diskToHalf (f : ℂ → ℂ) (z : ℂ) : ℂ := 2*Complex.I*f (diskCayley z)

def halfToDisk (f : ℂ → ℂ) (z : ℂ) : ℂ := f (halfCayley z)/(2*Complex.I)

lemma hasDerivAt_diskToHalf {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    {z : ℂ} (hz : z ∈ halfPlane) : HasDerivAt (diskToHalf f)
      (-(4 : ℂ)*deriv f (diskCayley z)/(z+Complex.I)^2) z := by
  have hd := ((hf _ (diskCayley_maps hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (diskCayley_maps hz))).hasDerivAt
  convert (hd.comp z (diskCayley_hasDerivAt hz)).const_mul (2*Complex.I) using 1 <;> try rfl
  ring_nf
  simp [Complex.I_sq]

lemma hasDerivAt_halfToDisk {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f halfPlane)
    {z : ℂ} (hz : z ∈ disk) : HasDerivAt (halfToDisk f)
      (deriv f (halfCayley z)/(1-z)^2) z := by
  have hd := ((hf _ (halfCayley_maps hz)).differentiableAt
    (isOpen_halfPlane.mem_nhds (halfCayley_maps hz))).hasDerivAt
  convert (hd.comp z (halfCayley_hasDerivAt hz)).div_const (2*Complex.I) using 1 <;> try rfl
  field_simp

lemma diskToHalf_schlicht {f : ℂ → ℂ} (hf : Schlicht f) :
    HalfPlaneSchlicht (diskToHalf f) := by
  refine ⟨⟨fun z hz => (hasDerivAt_diskToHalf hf.1.1 hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    have hm := hf.1.2 (diskCayley_maps hz) (diskCayley_maps hw)
      ((mul_left_cancel₀ (by simp : (2 : ℂ)*Complex.I ≠ 0)) he)
    simpa only [halfCayley_diskCayley hz,halfCayley_diskCayley hw] using congrArg halfCayley hm
  · simp [diskToHalf,hf.2.1]
  · rw [(hasDerivAt_diskToHalf hf.1.1 (show Complex.I ∈ halfPlane by simp [halfPlane])).deriv]
    norm_num [hf.2.2,add_sq,mul_assoc,Complex.I_sq,Complex.I_mul_I]

lemma halfToDisk_schlicht {f : ℂ → ℂ} (hf : HalfPlaneSchlicht f) :
    Schlicht (halfToDisk f) := by
  refine ⟨⟨fun z hz => (hasDerivAt_halfToDisk hf.1.1 hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    have hm := hf.1.2 (halfCayley_maps hz) (halfCayley_maps hw)
      ((div_left_inj' (by simp : (2 : ℂ)*Complex.I ≠ 0)).mp he)
    simpa only [diskCayley_halfCayley hz,diskCayley_halfCayley hw] using congrArg diskCayley hm
  · simp [halfToDisk,hf.2.1]
  · rw [(hasDerivAt_halfToDisk hf.1.1 (show (0 : ℂ) ∈ disk by simp [disk])).deriv]
    simp [hf.2.2]

lemma diskToHalf_halfToDisk {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ halfPlane) :
    diskToHalf (halfToDisk f) z = f z := by
  simp only [diskToHalf,halfToDisk,halfCayley_diskCayley hz]
  field_simp

lemma halfToDisk_diskToHalf {f : ℂ → ℂ} {z : ℂ} (hz : z ∈ disk) :
    halfToDisk (diskToHalf f) z = f z := by
  simp [diskToHalf,halfToDisk,diskCayley_halfCayley hz]

def classFun (g : DiskClass) : ℂ → ℂ := diskToHalf (diskExtend g.1)

lemma classFun_schlicht (g : DiskClass) : HalfPlaneSchlicht (classFun g) :=
  diskToHalf_schlicht g.2

def classOfHalf (f : ℂ → ℂ) (hf : HalfPlaneSchlicht f) : DiskClass :=
  ⟨⟨fun z => halfToDisk f z, continuousOn_iff_continuous_domRestrict.mp
    (halfToDisk_schlicht hf).1.1.continuousOn⟩,by
      have he : EqOn (diskExtend (⟨fun z => halfToDisk f z,
        continuousOn_iff_continuous_domRestrict.mp
          (halfToDisk_schlicht hf).1.1.continuousOn⟩ : C(disk,ℂ))) (halfToDisk f) disk := by
        intro z hz
        exact diskExtend_apply _ ⟨z,hz⟩
      refine ⟨⟨(halfToDisk_schlicht hf).1.1.congr he,?_⟩,?_,?_⟩
      · intro z hz w hw h
        exact (halfToDisk_schlicht hf).1.2 hz hw ((he hz).symm.trans (h.trans (he hw)))
      · rw [he (by simp [disk])]
        exact (halfToDisk_schlicht hf).2.1
      · rw [he.deriv Metric.isOpen_ball (by simp [disk])]
        exact (halfToDisk_schlicht hf).2.2⟩

lemma classFun_classOfHalf {f : ℂ → ℂ} (hf : HalfPlaneSchlicht f) :
    EqOn (classFun (classOfHalf f hf)) f halfPlane := by
  intro z hz
  dsimp [classFun,diskToHalf,classOfHalf]
  rw [diskExtend_apply _ (⟨diskCayley z,diskCayley_maps hz⟩ : disk)]
  exact diskToHalf_halfToDisk hz

lemma continuous_classFun_eval : Continuous (fun p : DiskClass × halfPlane => classFun p.1 p.2) := by
  have hm' : Continuous (fun z : halfPlane => diskCayley z) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (diskCayley_hasDerivAt z.2).continuousAt.comp continuous_subtype_val.continuousAt
  have h := (continuous_diskClassJet_eval 0).comp
    (continuous_id.prodMap (hm'.subtype_mk (fun z => diskCayley_maps z.2)))
  simpa only [iteratedDeriv_zero,classFun,diskToHalf,Function.comp_def,Prod.map, id_eq] using h.const_mul (2*Complex.I)

instance instLocallyCompactSpaceElemComplexHalfPlane : LocallyCompactSpace halfPlane := isOpen_halfPlane.locallyCompactSpace

instance instT2SpaceElemContinuousMapComplexDiskDiskClass : T2Space DiskClass := inferInstanceAs (T2Space diskSchlichtSet)

instance instMeasurableSpaceElemContinuousMapComplexDiskDiskClass : MeasurableSpace DiskClass := borel DiskClass

instance instBorelSpaceElemContinuousMapComplexDiskDiskClass : BorelSpace DiskClass := ⟨rfl⟩

lemma differentiableOn_iteratedDeriv_open {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv hU

lemma tendstoLocallyUniformlyOn_iteratedDeriv_open.{u_1} {U : Set ℂ} (hU : IsOpen U)
    {ι : Type u_1} {l : Filter ι} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l U := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ,Function.comp_def] using ih.deriv
      (hf.mono (fun i h => differentiableOn_iteratedDeriv_open hU h n)) hU

def classJet (n : ℕ) (g : DiskClass) : C(halfPlane,ℂ) :=
  ⟨fun z => iteratedDeriv n (classFun g) z, continuousOn_iff_continuous_domRestrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_halfPlane (classFun_schlicht g).1.1 n).continuousOn⟩

lemma continuous_classJet (n : ℕ) : Continuous (classJet n) := by
  have hc : Continuous (classJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_classFun_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn classFun (classFun g) (𝓝 g) halfPlane :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_halfPlane h
      (Eventually.of_forall (fun f : DiskClass => (classFun_schlicht f).1.1)) n)

lemma continuous_classJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × halfPlane => iteratedDeriv n (classFun p.1) p.2) :=
  continuous_eval.comp ((continuous_classJet n).prodMap continuous_id)

def rerootClass (g : DiskClass) (z : halfPlane) : DiskClass :=
  classOfHalf (reroot (classFun g) z) (reroot_normalized (classFun_schlicht g).1 z.2)

lemma classFun_rerootClass (g : DiskClass) (z : halfPlane) :
    EqOn (classFun (rerootClass g z)) (reroot (classFun g) z) halfPlane :=
  classFun_classOfHalf _

lemma continuous_rerootClass : Continuous (fun p : DiskClass × halfPlane => rerootClass p.1 p.2) := by
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc : Continuous (fun p : (DiskClass × halfPlane) × disk =>
      (⟨halfCayley p.2,halfCayley_maps p.2.2⟩ : halfPlane)) := by
    apply Continuous.subtype_mk
    have hm : Continuous (fun z : disk => halfCayley z) := by
      apply continuous_iff_continuousAt.mpr
      intro z
      exact (halfCayley_hasDerivAt z.2).continuousAt.comp continuous_subtype_val.continuousAt
    exact hm.comp continuous_snd
  have ha : Continuous (fun p : (DiskClass × halfPlane) × disk =>
      (⟨affine p.1.2 (halfCayley p.2),affine_mem p.1.2.2 (halfCayley_maps p.2.2)⟩ : halfPlane)) := by
    apply Continuous.subtype_mk
    have hre : Continuous (fun p : (DiskClass × halfPlane) × disk => p.1.2.val.re) := Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    have him : Continuous (fun p : (DiskClass × halfPlane) × disk => p.1.2.val.im) := Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul (continuous_subtype_val.comp hc))
  have hvalue := continuous_classFun_eval.comp ((continuous_fst.comp continuous_fst).prodMk ha)
  have hroot : Continuous (fun p : (DiskClass × halfPlane) × disk => classFun p.1.1 p.1.2) :=
    continuous_classFun_eval.comp continuous_fst
  have hder : Continuous (fun p : (DiskClass × halfPlane) × disk => deriv (classFun p.1.1) p.1.2) := by
    simpa only [iteratedDeriv_one,Function.comp_def] using
      ((continuous_classJet_eval 1).comp (continuous_fst : Continuous (Prod.fst : (DiskClass × halfPlane) × disk → DiskClass × halfPlane)))
  have him : Continuous (fun p : (DiskClass × halfPlane) × disk => (p.1.2.val.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hdiv := (hvalue.sub hroot).div (him.mul hder) (fun p => mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt p.1.2.2))
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1.1).1 p.1.2.2))
  exact hdiv.div_const (2*Complex.I)

lemma class_ext {g h : DiskClass} (he : EqOn (classFun g) (classFun h) halfPlane) : g = h := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  have hx := congrArg (fun q : ℂ => q/(2*Complex.I)) (he (halfCayley_maps z.2))
  have hg : (classFun g) (halfCayley z)/(2*Complex.I) = g.1 z := by
    exact (halfToDisk_diskToHalf z.2).trans (diskExtend_apply _ z)
  have hh : (classFun h) (halfCayley z)/(2*Complex.I) = h.1 z := by
    exact (halfToDisk_diskToHalf z.2).trans (diskExtend_apply _ z)
  rwa [hg,hh] at hx

lemma reroot_congr {f g : ℂ → ℂ} (he : EqOn f g halfPlane) {z : ℂ} (hz : z ∈ halfPlane) :
    EqOn (reroot f z) (reroot g z) halfPlane := by
  intro w hw
  simp only [reroot,he (affine_mem hz hw),he hz,he.deriv isOpen_halfPlane hz]

def classWeight (g : DiskClass) (z : halfPlane) : ℝ := ‖reciprocalDeriv (classFun g) z‖^2

lemma classWeight_pos (g : DiskClass) (z : halfPlane) : 0 < classWeight g z := by
  apply sq_pos_of_ne_zero
  exact norm_ne_zero_iff.mpr (inv_ne_zero
    (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 z.2))

lemma continuous_classWeight : Continuous (fun p : DiskClass × halfPlane => classWeight p.1 p.2) := by
  have hd : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
  exact (hd.inv₀ (fun p => univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.2)).norm.pow 2

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def logarithmicJet (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * (z.im : ℂ) * deriv (reciprocalDeriv f) z / reciprocalDeriv f z

def criticalMap (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  f z - Complex.I / (k : ℂ) * (z.im : ℂ) * deriv f z

def normalizedJacobian (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℝ :=
  LinearMap.det (fderiv ℝ (criticalMap f k) z).toLinearMap / ‖deriv f z‖^2

lemma hasDerivAt_reciprocalDeriv {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) :
    HasDerivAt (reciprocalDeriv f) (deriv (reciprocalDeriv f) z) z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  exact (han.deriv.differentiableAt.inv
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)).hasDerivAt

def potential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal z.im) ^ k / ENNReal.ofReal ‖f z - ξ‖

def GoodPair (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Prop :=
  (∀ δ : ℝ, 0 < δ → IsCompact {z | z ∈ halfPlane ∧ ENNReal.ofReal δ ≤ potential f k ξ z}) ∧
  (∀ z ∈ halfPlane, criticalMap f k z = ξ → normalizedJacobian f k z ≠ 0)

def logPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  k * Real.log z.im - Real.log ‖f z - ξ‖

def targetRatio (f : ℂ → ℂ) (ξ z : ℂ) : ℂ := deriv f z / (f z - ξ)

def secondDirectional (u : ℂ → ℝ) (z v w : ℂ) : ℝ :=
  fderiv ℝ (fun t => fderiv ℝ u t v) z w

def realHessian (u : ℂ → ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![secondDirectional u z 1 1, secondDirectional u z 1 Complex.I;
    secondDirectional u z Complex.I 1, secondDirectional u z Complex.I Complex.I]

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def reciprocalPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  ‖f z-ξ‖ / z.im^k

def regularizedGradient (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℂ :=
  ((k : ℂ)*Complex.I/(z.im : ℂ))*(f z-ξ)*conj (criticalMap f k z-ξ)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Winding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def rectPath (r h : ℝ) : Path ((-r : ℂ)-(h : ℂ)*Complex.I)
    ((-r : ℂ)-(h : ℂ)*Complex.I) :=
  (((Path.segment ((-r : ℂ)-(h : ℂ)*Complex.I) ((r : ℂ)-(h : ℂ)*Complex.I)).trans
    (Path.segment ((r : ℂ)-(h : ℂ)*Complex.I) ((r : ℂ)+(h : ℂ)*Complex.I))).trans
    (Path.segment ((r : ℂ)+(h : ℂ)*Complex.I) ((-r : ℂ)+(h : ℂ)*Complex.I))).trans
    (Path.segment ((-r : ℂ)+(h : ℂ)*Complex.I) ((-r : ℂ)-(h : ℂ)*Complex.I))

def rectRegion (r h : ℝ) : Set ℂ := {z | |z.re| ≤ r ∧ |z.im| ≤ h}

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.LevelCurve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def periodicLoop {γ : ℝ → ℂ} (hc : Continuous γ) (s : ℝ) : C(unitInterval,ℂ) :=
  ⟨fun t => γ ((t : ℝ)+s),hc.comp (continuous_subtype_val.add continuous_const)⟩

def transverseCoordinate (p : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℝ :=
  (-p Complex.I) • Complex.reCLM + (p 1) • Complex.imCLM

def levelChartDerivative (p : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp p + Complex.I • (Complex.ofRealCLM.comp (transverseCoordinate p))

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Turning
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def secantTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

def averagedDerivative (γ : ℝ → ℂ) (s t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, deriv γ (s+u*(t-s))

@[simp] lemma averagedDerivative_diag (γ : ℝ → ℂ) (s : ℝ) :
    averagedDerivative γ s s = deriv γ s := by simp [averagedDerivative]

def extendedSecant (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (1-(p.2-p.1)) • averagedDerivative γ p.1 p.2 -
    (p.2-p.1) • averagedDerivative γ p.1 (p.2-1)

@[simp] lemma extendedSecant_diag (γ : ℝ → ℂ) (s : ℝ) :
    extendedSecant γ (s,s) = deriv γ s := by simp [extendedSecant]

@[simp] lemma extendedSecant_corner (γ : ℝ → ℂ) :
    extendedSecant γ (0,1) = -deriv γ 0 := by simp [extendedSecant]

def triangleOrigin : secantTriangle := ⟨(0,0), by simp [secantTriangle]⟩

def triangleCorner : secantTriangle := ⟨(0,1), by simp [secantTriangle]⟩

def triangleEnd : secantTriangle := ⟨(1,1), by simp [secantTriangle]⟩

def triangleLeft (t : unitInterval) : secantTriangle :=
  ⟨(0,t), by exact ⟨le_rfl, t.property.1, t.property.2⟩⟩

def triangleTop (t : unitInterval) : secantTriangle :=
  ⟨(t,1), by exact ⟨t.property.1, t.property.2, le_rfl⟩⟩

def triangleDiag (t : unitInterval) : secantTriangle :=
  ⟨(t,t), by exact ⟨t.property.1, le_rfl, t.property.2⟩⟩

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.LevelIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def tangentGradient (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (-(fderiv ℝ f z Complex.I) : ℂ) + Complex.I*(fderiv ℝ f z 1 : ℂ)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def squaredReciprocalPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  ‖f z-ξ‖^2 * z.im^(-2*k)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.RankPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

instance diskClassSecondCountable : SecondCountableTopology DiskClass := inferInstanceAs (SecondCountableTopology diskSchlichtSet)

def criticalHeight (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℝ :=
  k * z.im^(k-1) * ‖reciprocalDeriv f z‖

def affineHome (t : ℂ) (ht : t ∈ halfPlane) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (t.im : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))).trans
    (Homeomorph.addLeft (t.re : ℂ))

def rerootTarget (f : ℂ → ℂ) (t ξ : ℂ) : ℂ :=
  (ξ-f t)/((t.im : ℂ)*deriv f t)

def heightScaleInverse (f : ℂ → ℂ) (k : ℝ) (t : ℂ) : ℝ :=
  t.im^(k-1) / ‖deriv f t‖

def orderRank.{u_1} {α : Type u_1} [LinearOrder α] (S : Set α) (x : α) : ℕ := (S ∩ Iio x).ncard

def heightKey (H : ℂ → ℝ) (z : ℂ) : Lex (ℝ × Lex (ℝ × ℝ)) :=
  toLex (-H z,toLex (z.re,z.im))

lemma heightKey_injective (H : ℂ → ℝ) : Injective (heightKey H) := by
  intro z w he
  have he' := congrArg (fun a : Lex (ℝ × Lex (ℝ × ℝ)) => ofLex ((ofLex a).2)) he
  exact Complex.ext (congrArg Prod.fst he') (congrArg Prod.snd he')

@[instance_reducible] def heightOrder (H : ℂ → ℝ) : LinearOrder ℂ := LinearOrder.lift' (heightKey H) (heightKey_injective H)

def heightRank (H : ℂ → ℝ) (S : Set ℂ) (z : ℂ) : ℕ := @orderRank ℂ (heightOrder H) S z

def heightPrecedes (H : ℂ → ℝ) (z w : ℂ) : Prop :=
  H w < H z ∨ H z = H w ∧ (z.re < w.re ∨ z.re = w.re ∧ z.im < w.im)

def rankPartner (H : ℂ → ℝ) (A B : Set ℂ) (z : ℂ) : ℂ :=
  if h : ∃ w ∈ B, heightRank H B w = heightRank H A z then h.choose else z

def positiveFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z}

def negativeFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0}

def criticalPair (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  rankPartner (criticalHeight f k) (positiveFiber f k (criticalMap f k z))
    (negativeFiber f k (criticalMap f k z)) z

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.BorelPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

structure BorelBranches.{u_1, u_2} {X : Type u_1} {Y : Type u_2} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : Set X) where
  part : ℕ → Set X
  branch : ℕ → Y → X
  measurable_part : ∀ n, MeasurableSet (part n)
  disjoint : Pairwise (Disjoint on part)
  cover : (⋃ n, part n) = s
  injective : ∀ n, InjOn f (part n)
  measurable_branch : ∀ n, Measurable (branch n)
  measurable_image : ∀ n, MeasurableSet (f '' part n)
  right_inv : ∀ n y, y ∈ f '' part n → branch n y ∈ part n ∧ f (branch n y) = y
  left_inv : ∀ n x, x ∈ part n → branch n (f x) = x

instance instPolishSpaceElemContinuousMapComplexDiskDiskClass : PolishSpace DiskClass := by
  let := TopologicalSpace.metrizableSpaceMetric DiskClass
  infer_instance

instance instPolishSpaceElemComplexHalfPlane : PolishSpace halfPlane := isOpen_halfPlane.polishSpace

instance instNonemptyElemComplexHalfPlane : Nonempty halfPlane := ⟨⟨Complex.I,by simp [halfPlane]⟩⟩

def identityHalf (z : ℂ) : ℂ := z-Complex.I

lemma identityHalf_schlicht : HalfPlaneSchlicht identityHalf := by
  refine ⟨⟨(differentiable_id.sub_const Complex.I).differentiableOn,?_⟩,by simp [identityHalf],?_⟩
  · exact (sub_left_injective).injOn
  · exact (hasDerivAt_id Complex.I |>.sub_const Complex.I).deriv

def identityClass : DiskClass := classOfHalf identityHalf identityHalf_schlicht

instance instNonemptyElemContinuousMapComplexDiskDiskClass : Nonempty DiskClass := ⟨identityClass⟩

def jointCriticalMap (k : ℝ) (q : DiskClass × halfPlane) : DiskClass × ℂ :=
  (q.1,criticalMap (classFun q.1) k q.2)

def nonsingularClass (k : ℝ) : Set (DiskClass × halfPlane) :=
  {q | normalizedJacobian (classFun q.1) k q.2 ≠ 0}

def classPrecedes (k : ℝ) (q r : DiskClass × halfPlane) : Prop :=
  criticalHeight (classFun r.1) k r.2 < criticalHeight (classFun q.1) k q.2 ∨
  criticalHeight (classFun q.1) k q.2 = criticalHeight (classFun r.1) k r.2 ∧
    (q.2.val.re < r.2.val.re ∨ q.2.val.re = r.2.val.re ∧ q.2.val.im < r.2.val.im)

def classRankCount (k σ : ℝ) (q : DiskClass × halfPlane) : ℝ≥0∞ :=
  Measure.count {r | r ∈ nonsingularClass k ∧ jointCriticalMap k r = jointCriticalMap k q ∧
    0 < σ * normalizedJacobian (classFun r.1) k r.2 ∧ classPrecedes k r q}

def signedFiber (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) (σ : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ criticalMap f k z = ξ ∧ 0 < σ * normalizedJacobian f k z}

def halfOne : halfPlane := ⟨Complex.I,by simp [halfPlane]⟩

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.AreaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

def fiberSum.{u_1, u_2} {X : Type u_1} {Y : Type u_2} (f : X → Y) (s : Set X) (u : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∑' x : {x | x ∈ s ∧ f x = y}, u x

def jacobianRegion (g : DiskClass) (k σ : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ 0 < σ * normalizedJacobian (classFun g) k z}

def transportDensity (g : DiskClass) (β : ℝ) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im^(β-1)*‖reciprocalDeriv (classFun g) z‖^2)

def targetDensity (g : DiskClass) (β : ℝ) : ℂ → ℝ≥0∞ :=
  halfPlane.indicator (fun z => ENNReal.ofReal (z.im^(β-1)*‖reciprocalDeriv (classFun g) z‖^4))

attribute [local irreducible] classWeight

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.BoundaryTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight

def outsideCore : Set ℂ := {z | z ∈ halfPlane ∧ (1/2 : ℝ) ≤ ‖diskCayley z‖}

def planeClassValue (g : DiskClass) (z : ℂ) : ℂ :=
  by classical exact if z ∈ halfPlane then classFun g z else 0

attribute [local irreducible] classFun

def HasQuarticTail (F : ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
    z.im^a*‖F z‖⁻¹^4 < ε

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TraceIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def pairLaplacian (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ g) p (1,0) (1,0) + fderiv ℝ (fderiv ℝ g) p (0,1) (0,1)

def traceFluxX (g : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.2-ε)*fderiv ℝ g p (1,0)

def traceFluxY (g : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.2-ε)*fderiv ℝ g p (0,1)-g p

def secondReal (f : ℂ → ℝ) (z u v : ℂ) : ℝ := fderiv ℝ (fderiv ℝ f) z u v

def complexSecondReal (f : ℂ → ℂ) (z u v : ℂ) : ℂ := fderiv ℝ (fderiv ℝ f) z u v

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.BoundaryEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def closedPositiveSuperlevel (F : ℂ → ℂ) (k δ : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | 0 < z.im ∧ ‖F z-ξ‖ ≤ z.im^k/δ}

def realCell (h : ℝ) (j : ℤ) : Set ℝ := Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)

def dyadicHeight (n : ℕ) : ℝ := (1/2)^n

def omittedTargets (F : ℂ → ℂ) (k R δ h : ℝ) : Set ℂ :=
  {ξ | ξ ∉ F '' {z : ℂ | 0 < z.im} ∧ ‖ξ‖ ≤ R ∧
    ∃ x y : ℝ, h ≤ y ∧ y ≤ 2*h ∧ ‖F (x+y*Complex.I)-ξ‖ ≤ y^k/δ}

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.GoodPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def pairingDomain (k : ℝ) : Set (DiskClass × halfPlane) :=
  {q | 0 < normalizedJacobian (classFun q.1) k q.2 ∧
    GoodPair (classFun q.1) k (criticalMap (classFun q.1) k q.2)}

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TransportBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def displacementWindow (N : ℝ) (z w : ℂ) : Prop :=
  z.im ≤ N*w.im ∧ w.im ≤ N*z.im ∧ |w.re-z.re| ≤ N*z.im

def transportWindow (k N : ℝ) : Set (DiskClass × halfPlane) :=
  {q | q ∈ pairingDomain k ∧
    displacementWindow N q.2 (criticalPair (classFun q.1) k q.2)}

def transportSlice (g : DiskClass) (k N : ℝ) : Set ℂ :=
  {z | z ∈ halfPlane ∧ 0 < normalizedJacobian (classFun g) k z ∧
    GoodPair (classFun g) k (criticalMap (classFun g) k z) ∧
    displacementWindow N z (criticalPair (classFun g) k z)}

def transportBox (R a b : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ a ≤ z.im ∧ z.im ≤ b}

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TransferOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

def halfMul (z w : halfPlane) : halfPlane := ⟨affine z w,affine_mem z.2 w.2⟩

def halfPoint (x y : ℝ) (hy : 0 < y) : halfPlane :=
  ⟨(x : ℂ)+(y : ℂ)*Complex.I,by simpa [halfPlane]⟩

def horizontal (x : ℝ) : halfPlane := halfPoint x 1 zero_lt_one

lemma continuous_halfPoint.{u_1} {Y : Type u_1} [TopologicalSpace Y] {x y : Y → ℝ}
    (hx : Continuous x) (hy : Continuous y) (hp : ∀ a, 0 < y a) :
    Continuous (fun a => halfPoint (x a) (y a) (hp a)) :=
  ((Complex.continuous_ofReal.comp hx).add ((Complex.continuous_ofReal.comp hy).mul continuous_const)).subtype_mk _

attribute [local irreducible] rerootClass

def weightAt (z : halfPlane) : C(DiskClass,ℝ) :=
  ⟨fun g => classWeight g z,by
    have hc : Continuous (fun g : DiskClass => (g,z)) := continuous_id.prodMk continuous_const
    exact continuous_classWeight.comp hc⟩

def actionAt (z : halfPlane) : C(DiskClass,DiskClass) :=
  ⟨fun g => rerootClass g z,by
    have hc : Continuous (fun g : DiskClass => (g,z)) := continuous_id.prodMk continuous_const
    exact continuous_rerootClass.comp hc⟩

def affineOperator (z : halfPlane) : C(DiskClass,ℝ) →L[ℝ] C(DiskClass,ℝ) :=
  (ContinuousLinearMap.mul ℝ C(DiskClass,ℝ) (weightAt z)).comp (ContinuousMap.compCLM ℝ ℝ (actionAt z))

lemma affineOperator_apply (z : halfPlane) (f : C(DiskClass,ℝ)) (g : DiskClass) :
    affineOperator z f g = classWeight g z * f (rerootClass g z) := rfl

lemma affineOperator_pos (z : halfPlane) (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) :
    0 ≤ affineOperator z f := fun g => mul_nonneg (classWeight_pos g z).le (hf _)

lemma continuous_affineOperator_apply (f : C(DiskClass,ℝ)) :
    Continuous (fun z : halfPlane => affineOperator z f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hw : Continuous (fun p : halfPlane × DiskClass => classWeight p.2 p.1) :=
    continuous_classWeight.comp (continuous_swap : Continuous (Prod.swap : halfPlane × DiskClass → DiskClass × halfPlane))
  have ht : Continuous (fun p : halfPlane × DiskClass => rerootClass p.2 p.1) :=
    continuous_rerootClass.comp (continuous_swap : Continuous (Prod.swap : halfPlane × DiskClass → DiskClass × halfPlane))
  exact hw.mul (f.continuous.comp ht)

lemma classFun_identityClass : EqOn (classFun identityClass) identityHalf halfPlane :=
  classFun_classOfHalf identityHalf_schlicht

lemma classWeight_identityClass (z : halfPlane) : classWeight identityClass z = 1 := by
  have hd := classFun_identityClass.deriv isOpen_halfPlane z.2
  have hi : deriv identityHalf z = 1 := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).deriv
  simp [classWeight,reciprocalDeriv,hd,hi]

lemma reroot_identityClass (z : halfPlane) : rerootClass identityClass z = identityClass := by
  apply class_ext
  intro w hw
  rw [classFun_rerootClass _ _ hw,reroot_congr classFun_identityClass z.2 hw,classFun_identityClass hw]
  have hd : deriv identityHalf z = 1 := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).deriv
  have he : (z.val.re : ℂ)+(z.val.im : ℂ)*Complex.I = z := by apply Complex.ext <;> simp
  dsimp [reroot,identityHalf,affine]
  rw [hd,mul_one]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt z.2))).mpr
  linear_combination he

def dyadicLeft : halfPlane := halfPoint (-1/2) (1/2) (by norm_num)

def dyadicRight : halfPlane := halfPoint (1/2) (1/2) (by norm_num)

def transferOperator : C(DiskClass,ℝ) →L[ℝ] C(DiskClass,ℝ) :=
  (1/2 : ℝ) • (affineOperator dyadicLeft+affineOperator dyadicRight)

lemma transferOperator_identityClass (f : C(DiskClass,ℝ)) : transferOperator f identityClass = f identityClass := by
  change (1/2 : ℝ)*(affineOperator dyadicLeft f identityClass+affineOperator dyadicRight f identityClass) = _
  simp only [affineOperator_apply,classWeight_identityClass,reroot_identityClass,one_mul]
  ring

lemma transferOperator_pow_identityClass (n : ℕ) : (transferOperator^n) 1 identityClass = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',mul_apply_eq_comp,transferOperator_identityClass] using ih

lemma transferOperator_pow_norm_ge_one (n : ℕ) : 1 ≤ ‖transferOperator^n‖ := by
  have hv := (ContinuousMap.norm_coe_le_norm ((transferOperator^n) 1) identityClass).trans
    ((transferOperator^n).le_opNorm 1)
  simpa only [transferOperator_pow_identityClass,norm_one,mul_one] using hv

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Eigenmeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

lemma log_norm_pow_subadditive.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : Subadditive (fun n => Real.log ‖a^n‖) := by
  intro m n
  change Real.log ‖a^(m+n)‖ ≤ _
  rw [pow_add]
  calc
    Real.log ‖a^m*a^n‖ ≤ Real.log (‖a^m‖*‖a^n‖) :=
      Real.log_le_log (lt_of_lt_of_le zero_lt_one (by simpa [pow_add] using h (m+n))) (norm_mul_le _ _)
    _ = Real.log ‖a^m‖ + Real.log ‖a^n‖ := Real.log_mul (by linarith [h m]) (by linarith [h n])

def growthLog.{u_1} {A : Type u_1} [NormedRing A] (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : ℝ :=
  (log_norm_pow_subadditive a h).lim

def growthRate.{u_1} {A : Type u_1} [NormedRing A] (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : ℝ :=
  Real.exp (growthLog a h)

def positiveResolvent.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (τ : ℝ) : C(X,ℝ) →L[ℝ] C(X,ℝ) :=
  ∑' n : ℕ, (τ⁻¹)^n • L^n

lemma positive_functional_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ : C(X,ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(X,ℝ)) :
    ‖Λ f‖ ≤ Λ 1 * ‖f‖ := by
  have hlo : (-‖f‖) • (1 : C(X,ℝ)) ≤ f := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi : f ≤ ‖f‖ • (1 : C(X,ℝ)) := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1 := hp (f-(-‖f‖) • 1) (sub_nonneg.mpr hlo)
  have h2 := hp (‖f‖ • 1-f) (sub_nonneg.mpr hhi)
  simp only [map_sub,map_smul,smul_eq_mul,neg_mul] at h1 h2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.AffineLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

def positiveFunctionalCLM.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (Λ : C(X,ℝ) →ₗ[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(X,ℝ) →L[ℝ] ℝ :=
  Λ.mkContinuous (Λ 1) (positive_functional_bound Λ hp)

def intervalFunctional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) : C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ t in a..b, Λ (A t f)
      map_add' := by
        intro f g
        simp only [map_add]
        exact intervalIntegral.integral_add ((Λ.continuous.comp (hc f)).intervalIntegrable a b)
          ((Λ.continuous.comp (hc g)).intervalIntegrable a b)
      map_smul' := by
        intro c f
        simp only [map_smul,smul_eq_mul]
        exact intervalIntegral.integral_const_mul c _ }
    (by
      intro f hf
      exact intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf)))

def pointOperator (x y : ℝ) (hy : 0 < y) := affineOperator (halfPoint x y hy)

def probabilityFunctional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) : C(X,ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ x, f x ∂(μ : Measure X)
      map_add' := fun f g => integral_add (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    (fun _ hf => integral_nonneg hf)

lemma continuous_pointOperator_x (y : ℝ) (hy : 0 < y) (f : C(DiskClass,ℝ)) :
    Continuous (fun x : ℝ => pointOperator x y hy f) :=
  (continuous_affineOperator_apply f).comp (continuous_halfPoint continuous_id continuous_const (fun _ => hy))

lemma continuous_horizontalOperator (f : C(DiskClass,ℝ)) :
    Continuous (fun x : ℝ => affineOperator (horizontal x) f) := continuous_pointOperator_x 1 zero_lt_one f

def horizontalAverage (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) :
    C(DiskClass,ℝ) →L[ℝ] ℝ :=
  (1/2 : ℝ) • intervalFunctional (fun x => affineOperator (horizontal x)) continuous_horizontalOperator
    (fun _ => affineOperator_pos _) Λ hp 0 2 (by norm_num)

def logScaledOperator (β t : ℝ) : C(DiskClass,ℝ) →L[ℝ] C(DiskClass,ℝ) :=
  Real.exp (β*t) • pointOperator 0 (Real.exp t) (Real.exp_pos t)

lemma logScaledOperator_apply (β t : ℝ) (f : C(DiskClass,ℝ)) :
    logScaledOperator β t f = Real.exp (β*t) • pointOperator 0 (Real.exp t) (Real.exp_pos t) f := rfl

lemma continuous_logScaledOperator (β : ℝ) (f : C(DiskClass,ℝ)) :
    Continuous (fun t => logScaledOperator β t f) := by
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((continuous_affineOperator_apply f).comp
      (continuous_halfPoint continuous_const Real.continuous_exp Real.exp_pos))

lemma logScaledOperator_pos (β t : ℝ) (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) :
    0 ≤ logScaledOperator β t f := by
  rw [logScaledOperator_apply]
  exact smul_nonneg (Real.exp_pos _).le (affineOperator_pos _ f hf)

def scaleAverage (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(DiskClass,ℝ) →L[ℝ] ℝ :=
  intervalFunctional (logScaledOperator β) (continuous_logScaledOperator β) (logScaledOperator_pos β)
    Λ hp 0 (Real.log 2) (Real.log_nonneg (by norm_num))

def transferRho : ℝ := growthRate transferOperator transferOperator_pow_norm_ge_one

def transferBeta : ℝ := Real.log transferRho/Real.log 2

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.ExpectedDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

instance instPseudoMetrizableSpaceElemContinuousMapComplexDiskDiskClass : PseudoMetrizableSpace DiskClass := inferInstanceAs (PseudoMetrizableSpace diskSchlichtSet)

def halfRetract (z : ℂ) : halfPlane := if h : z ∈ halfPlane then ⟨z,h⟩ else halfOne

def averagedDensity (β : ℝ) (Φ : DiskClass → ℝ≥0∞) (p : DiskClass × ℂ) : ℝ≥0∞ :=
  {p : DiskClass × ℂ | p.2 ∈ halfPlane}.indicator
    (fun p => ENNReal.ofReal (p.2.im^(β-1)) * ENNReal.ofReal (classWeight p.1 (halfRetract p.2)) *
      Φ (rerootClass p.1 (halfRetract p.2))) p

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.InverseDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

def affineInverse (z : ℂ) : ℂ := (-(z.re : ℂ)+Complex.I)/(z.im : ℂ)

def planeClassDeriv (g : DiskClass) (z : ℂ) : ℂ :=
  by classical exact if z ∈ halfPlane then deriv (classFun g) z else 0

def inverseDensity (g : DiskClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖planeClassValue g z‖⁻¹^4)

def inverseJacDensity (g : DiskClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖planeClassDeriv g z‖^2*‖planeClassValue g z‖⁻¹^4)

def weightedInverseArea (β : ℝ) (g : DiskClass) : ℝ≥0∞ :=
  ∫⁻ z in outsideCore, ENNReal.ofReal (z.im^(β+1))*inverseDensity g z

def HasWeightedLaw (P : ProbabilityMeasure DiskClass) (β : ℝ) : Prop :=
  ∀ z : halfPlane, ∀ f : DiskClass → ℝ≥0∞, Measurable f →
    (∫⁻ g, ENNReal.ofReal (classWeight g z)*f (rerootClass g z) ∂(P : Measure DiskClass)) =
      ENNReal.ofReal (z.val.im^(-β))*(∫⁻ g, f g ∂(P : Measure DiskClass))

attribute [local irreducible] inverseDensity inverseJacDensity

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.ExpectedTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

def rootJac (k σ : ℝ) (g : DiskClass) : ℝ≥0∞ :=
  ENNReal.ofReal (σ * normalizedJacobian (classFun g) k Complex.I)

def rootWindow (k N : ℝ) : Set DiskClass := {g | (g,halfOne) ∈ transportWindow k N}

def windowTest (k N : ℝ) : DiskClass → ℝ≥0∞ := (rootWindow k N).indicator (rootJac k 1)

def rootException (k : ℝ) : Set DiskClass :=
  {g | ¬GoodPair (classFun g) k (criticalMap (classFun g) k Complex.I)}

def exceptionTest (k : ℝ) : DiskClass → ℝ≥0∞ := (rootException k).indicator (rootJac k 1)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma differentiableOn_classReciprocal (g : DiskClass) :
    DifferentiableOn ℂ (reciprocalDeriv (classFun g)) halfPlane :=
  fun _ hz => (hasDerivAt_reciprocalDeriv (classFun_schlicht g).1 hz).differentiableAt.differentiableWithinAt

def reciprocalJet (n : ℕ) (g : DiskClass) : C(halfPlane,ℂ) :=
  ⟨fun z => iteratedDeriv n (reciprocalDeriv (classFun g)) z, continuousOn_iff_continuous_domRestrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_halfPlane (differentiableOn_classReciprocal g) n).continuousOn⟩

def normFirst (q d v : ℂ) : ℝ := 2*inner ℝ q (d*v)

def normSecond (q d e v : ℂ) : ℝ :=
  2*(inner ℝ (d*v) (d*v)+inner ℝ q ((e*v)*v))

def complexLine (v : ℂ) (t : ℝ) : ℂ := Complex.I+(t : ℂ)*v

def lineDomain (v : ℂ) : Set ℝ := {t | 0 < 1+t*v.im}

@[simp] lemma complexLine_zero (v : ℂ) : complexLine v 0 = Complex.I := by simp [complexLine]

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CircleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

def circlePoint (r θ : ℝ) : ℂ := (r:ℂ)*Complex.exp ((θ:ℂ)*Complex.I)

def arcInterval : Set ℝ := Icc (-Real.pi/4) (Real.pi/4)

def arcD (r θ : ℝ) : ℝ := 1+2*r*Real.cos θ+r^2

def arcX (r θ : ℝ) : ℝ := 2*r*Real.sin θ/arcD r θ

def arcY (r θ : ℝ) : ℝ := (1-r^2)/arcD r θ

def arcXDeriv (r θ : ℝ) : ℝ := (4*r^2+2*r*(1+r^2)*Real.cos θ)/(arcD r θ)^2

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

attribute [local irreducible] classFun classWeight rerootClass

def horizontalMass (v : ℝ) (hv : 0 < v) : C(DiskClass,ℝ) :=
  ∫ x in (-1:ℝ)..1, weightAt (halfPoint x v hv)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

def rotateDisk (f : ℂ → ℂ) (α z : ℂ) : ℂ := f (α*z)/α

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Koebe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

def koebeMap (z : ℂ) : ℂ := z/(1-z)^2

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.SmoothMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

def logDisk (z : ℂ) : ℂ := Complex.exp (z*Complex.I)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology
namespace Brennan

def bracketSq (z : ℂ) : ℝ := 1+z.re^2+z.im^2

def smoothPower (q : ℝ) (z : ℂ) : ℝ := bracketSq z ^ q

def bracketSqDeriv (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (2*z.re) • Complex.reCLM + (2*z.im) • Complex.imCLM

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.DomainArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

def normalizeDisk (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z-f 0)/deriv f 0

end Brennan

end

end OAI
end


