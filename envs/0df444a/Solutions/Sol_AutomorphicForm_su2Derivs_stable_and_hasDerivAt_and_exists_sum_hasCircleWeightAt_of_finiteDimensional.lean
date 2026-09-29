-- Prove2me | solution 1 for AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/7e03574f-053c-5916-a413-5315b3c0874a

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.RealDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional.AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open Filter Topology Complex

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archComplexGLAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero_complex IsArchSmoothAtComplex ArchDirComplex splitTorusGL2Complex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex circleGL2 archCircleAt HasCircleWeightAt hasCircleWeightAt_zero glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving splitTorusGL2Complex_coe archDirMatrixComplex archComplexLiftAt_mul_archComplexGLAt hasDerivAt_of_symm_mul_archFlowMatrixComplex of_symm_mul_archFlowMatrixComplex_zero archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul circleGL2_coe"
namespace KStabAux
p2m_open "AutomorphicForm"

theorem hasDerivAt_const_mul_ofReal (μ : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => μ * (t : ℂ)) μ s := by
  simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).const_mul μ

theorem hasDerivAt_cexp_const_mul_ofReal (μ : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => exp (μ * (t : ℂ))) (exp (μ * (s : ℂ)) * μ) s :=
  (hasDerivAt_const_mul_ofReal μ s).cexp

theorem hasDerivAt_cexp_neg_const_mul_ofReal (μ : ℂ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => exp (-(μ * (t : ℂ)))) (exp (-(μ * (s : ℂ))) * (-μ)) s :=
  (hasDerivAt_const_mul_ofReal μ s).neg.cexp

theorem scalar_ode_forced (μ c : ℂ) (u : ℝ → ℂ)
    (hu : ∀ s : ℝ, HasDerivAt u (μ * u s + c * exp (μ * (s : ℂ))) s) (s : ℝ) :
    u s = exp (μ * (s : ℂ)) * (u 0 + c * (s : ℂ)) := by
  set v : ℝ → ℂ := fun t => exp (-(μ * (t : ℂ))) * u t - c * (t : ℂ) with hv
  have hv' : ∀ t : ℝ, HasDerivAt v 0 t := by
    intro t
    have key : exp (-(μ * (t : ℂ))) * exp (μ * (t : ℂ)) = 1 := by
      rw [← Complex.exp_add]; simp
    have h := ((hasDerivAt_cexp_neg_const_mul_ofReal μ t).mul (hu t)).sub (hasDerivAt_const_mul_ofReal c t)
    refine h.congr_deriv ?_
    linear_combination c * key
  have hconst := is_const_of_deriv_eq_zero (fun t => (hv' t).differentiableAt) (fun t => (hv' t).deriv) s 0
  have hv0 : v 0 = u 0 := by simp [hv]
  have key : exp (μ * (s : ℂ)) * exp (-(μ * (s : ℂ))) = 1 := by
    rw [← Complex.exp_add]; simp
  have e1 : exp (-(μ * (s : ℂ))) * u s = u 0 + c * (s : ℂ) := by
    rw [← hv0, ← hconst]
    simp only [hv]
    ring
  calc u s = (exp (μ * (s : ℂ)) * exp (-(μ * (s : ℂ)))) * u s := by rw [key, one_mul]
    _ = exp (μ * (s : ℂ)) * (exp (-(μ * (s : ℂ))) * u s) := by ring
    _ = exp (μ * (s : ℂ)) * (u 0 + c * (s : ℂ)) := by rw [e1]

theorem mem_of_tendsto_pointwise {G : Type*} (Y : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ Y]
    {ι : Type*} {l : Filter ι} [l.NeBot] {f : ι → G → ℂ} {g₀ : G → ℂ}
    (hf : ∀ᶠ i in l, f i ∈ Y) (hlim : ∀ g : G, Tendsto (fun i => f i g) l (𝓝 (g₀ g))) : g₀ ∈ Y := by
  have hc : IsClosed ((Y : Set (G → ℂ))) := Y.closed_of_finiteDimensional
  exact hc.mem_of_tendsto (tendsto_pi_nhds.2 hlim) hf

section Engine

variable {G : Type*} (Y : Submodule ℂ (G → ℂ)) (D : (G → ℂ) → (G → ℂ))
  (hD : ∀ y ∈ Y, D y ∈ Y)
  (hadd : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, D (y₁ + y₂) = D y₁ + D y₂)
  (hsmul : ∀ (c : ℂ), ∀ y ∈ Y, D (c • y) = c • D y)

def restr : Module.End ℂ Y where
  toFun y := ⟨D y, hD y y.2⟩
  map_add' y₁ y₂ := by
    apply Subtype.ext
    show D ((y₁ : G → ℂ) + y₂) = D y₁ + D y₂
    exact hadd _ y₁.2 _ y₂.2
  map_smul' c y := by
    apply Subtype.ext
    show D (c • (y : G → ℂ)) = c • D y
    exact hsmul c _ y.2

theorem restr_apply_coe (y : Y) : ((restr Y D hD hadd hsmul y : Y) : G → ℂ) = D y := rfl

theorem restr_sub_apply_coe (μ : ℂ) (y : Y) :
    (((restr Y D hD hadd hsmul - μ • (1 : Module.End ℂ Y)) y : Y) : G → ℂ) = D y - μ • (y : G → ℂ) := by
  simp [LinearMap.sub_apply, LinearMap.smul_apply, restr_apply_coe]

variable (T : ℝ → G → G)
  (hder : ∀ y ∈ Y, ∀ (g : G) (s : ℝ), HasDerivAt (fun t : ℝ => y (T t g)) (D y (T s g)) s)
  (hT0 : ∀ g : G, T 0 g = g) (hT2π : ∀ g : G, T (2 * Real.pi) g = g)

include hder hT0 in
theorem eigen_flow {μ : ℂ} {y : G → ℂ} (hy : y ∈ Y) (hμ : D y = μ • y) (g : G) (s : ℝ) :
    y (T s g) = exp (μ * (s : ℂ)) * y g := by
  have h := scalar_ode_forced μ 0 (fun t => y (T t g)) (fun t => by
    have := hder y hy g t
    rw [hμ] at this
    simpa using this) s
  simpa [hT0] using h

include hder hT0 in
theorem gen_flow {μ : ℂ} {y₁ y₂ : G → ℂ} (hy₁ : y₁ ∈ Y) (hy₂ : y₂ ∈ Y) (h₁ : D y₁ = μ • y₁)
    (h₂ : D y₂ = μ • y₂ + y₁) (g : G) (s : ℝ) :
    y₂ (T s g) = exp (μ * (s : ℂ)) * (y₂ g + y₁ g * (s : ℂ)) := by
  have h := scalar_ode_forced μ (y₁ g) (fun t => y₂ (T t g)) (fun t => by
    have hd := hder y₂ hy₂ g t
    rw [h₂] at hd
    have e := eigen_flow Y D T hder hT0 hy₁ h₁ g t
    convert hd using 1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, e]
    ring) s
  simpa [hT0] using h

include hder hT0 hT2π in
theorem exp_two_pi_eq_one {μ : ℂ} {y : G → ℂ} (hy : y ∈ Y) (hμ : D y = μ • y) (hy0 : y ≠ 0) :
    exp (μ * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
  obtain ⟨g, hg⟩ := Function.ne_iff.1 hy0
  have h := eigen_flow Y D T hder hT0 hy hμ g (2 * Real.pi)
  rw [hT2π] at h
  have : (exp (μ * ((2 * Real.pi : ℝ) : ℂ)) - 1) * y g = 0 := by linear_combination -h
  rcases mul_eq_zero.1 this with h1 | h1
  · exact sub_eq_zero.1 h1
  · exact absurd h1 hg

include hder hT0 hT2π in
theorem eigenvalue_eq_I_mul {μ : ℂ} {y : G → ℂ} (hy : y ∈ Y) (hμ : D y = μ • y) (hy0 : y ≠ 0) :
    ∃ m : ℤ, μ = I * (m : ℂ) := by
  have h := exp_two_pi_eq_one Y D T hder hT0 hT2π hy hμ hy0
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h
  refine ⟨n, ?_⟩
  have hπ : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
  have h2π : (2 * (Real.pi : ℂ)) ≠ 0 := mul_ne_zero two_ne_zero hπ
  push_cast at hn
  apply mul_right_cancel₀ h2π
  rw [hn]; ring

include hder hT0 hT2π in

theorem ker_sq_le (μ : ℂ) (y₂ : Y)
    (h : ((restr Y D hD hadd hsmul - μ • (1 : Module.End ℂ Y)) ^ 2) y₂ = 0) :
    (restr Y D hD hadd hsmul - μ • (1 : Module.End ℂ Y)) y₂ = 0 := by
  set A := restr Y D hD hadd hsmul with hA
  set y₁ : Y := (A - μ • (1 : Module.End ℂ Y)) y₂ with hy₁
  have hy₁c : ((y₁ : Y) : G → ℂ) = D y₂ - μ • (y₂ : G → ℂ) := by
    rw [hy₁, hA]; exact restr_sub_apply_coe Y D hD hadd hsmul μ y₂
  have hAy₁ : (A - μ • (1 : Module.End ℂ Y)) y₁ = 0 := by
    rw [hy₁, ← Module.End.mul_apply, ← pow_two]; exact h
  have f₁ : D (y₁ : G → ℂ) = μ • ((y₁ : Y) : G → ℂ) := by
    have := congrArg (fun z : Y => (z : G → ℂ)) hAy₁
    rw [hA, restr_sub_apply_coe] at this
    simpa [sub_eq_zero] using this
  have f₂ : D (y₂ : G → ℂ) = μ • ((y₂ : Y) : G → ℂ) + y₁ := by
    rw [hy₁c]; abel
  by_cases hz : ((y₁ : Y) : G → ℂ) = 0
  · exact (Submodule.coe_eq_zero).1 hz
  exfalso
  have hexp := exp_two_pi_eq_one Y D T hder hT0 hT2π y₁.2 f₁ hz
  apply hz
  funext g
  have hg := gen_flow Y D T hder hT0 y₁.2 y₂.2 f₁ f₂ g (2 * Real.pi)
  rw [hT2π, hexp, one_mul] at hg
  have h2 : (y₁ : G → ℂ) g * ((2 * Real.pi : ℝ) : ℂ) = 0 := by linear_combination -hg
  have hπ : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  simpa [hπ] using h2

include hder hT0 hT2π in
theorem maxGenEigenspace_le_eigenspace (μ : ℂ) :
    (restr Y D hD hadd hsmul).maxGenEigenspace μ ≤ (restr Y D hD hadd hsmul).eigenspace μ := by
  set A := restr Y D hD hadd hsmul with hA
  have key : ∀ k : ℕ, ∀ y : Y, ((A - μ • (1 : Module.End ℂ Y)) ^ (k + 1)) y = 0 →
      (A - μ • (1 : Module.End ℂ Y)) y = 0 := by
    intro k
    induction k with
    | zero => intro y hy; simpa using hy
    | succ k ih =>
      intro y hy
      rw [pow_succ, Module.End.mul_apply] at hy
      have h1 := ih _ hy
      exact ker_sq_le Y D hD hadd hsmul T hder hT0 hT2π μ y (by rw [pow_two, Module.End.mul_apply]; exact h1)
  intro y hy
  rw [Module.End.mem_maxGenEigenspace] at hy
  obtain ⟨k, hk⟩ := hy
  rw [Module.End.mem_eigenspace_iff]
  have h0 : (A - μ • (1 : Module.End ℂ Y)) y = 0 := by
    cases k with
    | zero =>
      simp only [pow_zero, Module.End.one_apply] at hk
      rw [hk, map_zero]
    | succ k => exact key k y hk
  rw [LinearMap.sub_apply, sub_eq_zero] at h0
  simpa using h0

variable [FiniteDimensional ℂ Y]

include hD hadd hsmul hder hT0 hT2π in

theorem exists_sum_eigen (y : G → ℂ) (hy : y ∈ Y) :
    ∃ (σ : Finset ℂ) (v : ℂ → G → ℂ), (∀ μ ∈ σ, v μ ∈ Y ∧ D (v μ) = μ • v μ) ∧ y = ∑ μ ∈ σ, v μ := by
  classical
  set A := restr Y D hD hadd hsmul with hA
  have htop : (⟨y, hy⟩ : Y) ∈ ⨆ μ : ℂ, A.eigenspace μ := by
    have h1 : (⨆ μ : ℂ, A.maxGenEigenspace μ) = ⊤ := Module.End.iSup_maxGenEigenspace_eq_top A
    have h2 : (⨆ μ : ℂ, A.maxGenEigenspace μ) ≤ ⨆ μ : ℂ, A.eigenspace μ :=
      iSup_mono fun μ => maxGenEigenspace_le_eigenspace Y D hD hadd hsmul T hder hT0 hT2π μ
    exact h2 (h1 ▸ Submodule.mem_top)
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 htop
  refine ⟨f.support, fun μ => ((f μ : Y) : G → ℂ), fun μ _ => ⟨(f μ).2, ?_⟩, ?_⟩
  · have h1 := Module.End.mem_eigenspace_iff.1 (hf μ)
    have h2 := congrArg (fun z : Y => (z : G → ℂ)) h1
    simpa [hA, restr_apply_coe] using h2
  · have h2 := congrArg (fun z : Y => (z : G → ℂ)) hsum
    simp only [Finsupp.sum] at h2
    rw [← h2]
    simp

include hD hadd hsmul hder hT0 hT2π in

theorem comp_mem (y : G → ℂ) (hy : y ∈ Y) (s : ℝ) : (fun g => y (T s g)) ∈ Y := by
  obtain ⟨σ, v, hv, rfl⟩ := exists_sum_eigen Y D hD hadd hsmul T hder hT0 hT2π y hy
  have : (fun g => (∑ μ ∈ σ, v μ) (T s g)) = ∑ μ ∈ σ, (exp (μ * (s : ℂ))) • v μ := by
    funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun μ hμ => eigen_flow Y D T hder hT0 (hv μ hμ).1 (hv μ hμ).2 g s
  rw [this]
  exact Y.sum_mem fun μ hμ => Y.smul_mem _ (hv μ hμ).1

end Engine

section EngineExtras

variable {G : Type*} (Y : Submodule ℂ (G → ℂ)) (D : (G → ℂ) → (G → ℂ))

theorem mem_of_hasDerivAt_zero [FiniteDimensional ℂ Y] (f : ℝ → G → ℂ) (Dy : G → ℂ)
    (hmem : ∀ t : ℝ, f t ∈ Y) (hder : ∀ g : G, HasDerivAt (fun t : ℝ => f t g) (Dy g) 0) : Dy ∈ Y := by
  refine mem_of_tendsto_pointwise Y (l := 𝓝[≠] (0 : ℝ)) (f := fun t : ℝ => t⁻¹ • (f t - f 0)) ?_ ?_
  · exact Eventually.of_forall fun t => Y.smul_of_tower_mem _ (Y.sub_mem (hmem t) (hmem 0))
  · intro g
    refine ((hasDerivAt_iff_tendsto_slope).1 (hder g)).congr fun t => ?_
    simp [slope_def_module]

theorem eigen_sum (hadd : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, D (y₁ + y₂) = D y₁ + D y₂)
    (hsmul : ∀ (c : ℂ), ∀ y ∈ Y, D (c • y) = c • D y)
    {ι : Type*} (μ : ℂ) (s : Finset ι) (v : ι → G → ℂ)
    (hv : ∀ i ∈ s, v i ∈ Y ∧ D (v i) = μ • v i) :
    (∑ i ∈ s, v i) ∈ Y ∧ D (∑ i ∈ s, v i) = μ • ∑ i ∈ s, v i := by
  classical
  have hD0 : D 0 = 0 := by
    have h := hsmul 0 0 Y.zero_mem
    simpa using h
  revert hv
  refine Finset.induction_on s (fun _ => ?_) (fun a s ha ih hv => ?_)
  · simp [hD0]
  · rw [Finset.sum_insert ha]
    obtain ⟨hmem, hDs⟩ := ih fun i hi => hv i (Finset.mem_insert_of_mem hi)
    obtain ⟨hva, hDa⟩ := hv a (Finset.mem_insert_self a s)
    refine ⟨Y.add_mem hva hmem, ?_⟩
    rw [hadd _ hva _ hmem, hDa, hDs, smul_add]

variable (T : ℝ → G → G)
  (hder : ∀ y ∈ Y, ∀ (g : G) (s : ℝ), HasDerivAt (fun t : ℝ => y (T t g)) (D y (T s g)) s)
  (hT0 : ∀ g : G, T 0 g = g)

include hder hT0 in
theorem D_mem [FiniteDimensional ℂ Y] (hmem : ∀ y ∈ Y, ∀ t : ℝ, (fun g => y (T t g)) ∈ Y)
    (y : G → ℂ) (hy : y ∈ Y) : D y ∈ Y :=
  mem_of_hasDerivAt_zero Y (fun t g => y (T t g)) (D y) (hmem y hy)
    (fun g => by have h := hder y hy g 0; rwa [hT0] at h)

end EngineExtras

end AutomorphicForm.KStabAux

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archComplexGLAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero_complex IsArchSmoothAtComplex ArchDirComplex splitTorusGL2Complex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex circleGL2 archCircleAt HasCircleWeightAt hasCircleWeightAt_zero glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving splitTorusGL2Complex_coe archDirMatrixComplex archComplexLiftAt_mul_archComplexGLAt hasDerivAt_of_symm_mul_archFlowMatrixComplex of_symm_mul_archFlowMatrixComplex_zero archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul circleGL2_coe"
namespace KStabAux
p2m_open "AutomorphicForm"

open Matrix AutomorphicForm.WindowedSiegel

section ComplexPlace

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

def rotR (s : ℝ) : Fin 2 → Fin 2 → ℂ :=
  !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]

def rotS (s : ℝ) : Fin 2 → Fin 2 → ℂ :=
  !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]

def rotR' (s : ℝ) : Fin 2 → Fin 2 → ℂ :=
  !![-(Real.sin s : ℂ), -(Real.cos s : ℂ); (Real.cos s : ℂ), -(Real.sin s : ℂ)]

def rotS' (s : ℝ) : Fin 2 → Fin 2 → ℂ :=
  !![-(Real.sin s : ℂ), (Real.cos s : ℂ) * Complex.I; (Real.cos s : ℂ) * Complex.I, -(Real.sin s : ℂ)]

omit hw in
theorem cos_sq_add_sin_sq_complex (s : ℝ) : (Real.cos s : ℂ) ^ 2 + (Real.sin s : ℂ) ^ 2 = 1 := by
  exact_mod_cast Real.cos_sq_add_sin_sq s

omit hw in
theorem det_rotR (s : ℝ) : (Matrix.of (rotR s)).det = 1 := by
  show Matrix.det !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)] = 1
  rw [Matrix.det_fin_two_of]
  linear_combination cos_sq_add_sin_sq_complex s

omit hw in
theorem det_rotS (s : ℝ) : (Matrix.of (rotS s)).det = 1 := by
  show Matrix.det !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)] = 1
  rw [Matrix.det_fin_two_of]
  linear_combination cos_sq_add_sin_sq_complex s - (Real.sin s : ℂ) ^ 2 * Complex.I_sq

omit hw in
theorem det_rotR_ne (s : ℝ) : (Matrix.of (rotR s)).det ≠ 0 := by rw [det_rotR]; exact one_ne_zero

omit hw in
theorem det_rotS_ne (s : ℝ) : (Matrix.of (rotS s)).det ≠ 0 := by rw [det_rotS]; exact one_ne_zero

omit hw in
theorem rotR_zero : rotR 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotR]

omit hw in
theorem rotS_zero : rotS 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotS]

omit hw in
theorem rotR_two_pi : rotR (2 * Real.pi) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotR]

omit hw in
theorem rotS_two_pi : rotS (2 * Real.pi) = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rotS]

theorem archComplexLiftAt_one : archComplexLiftAt hw (1 : Matrix (Fin 2) (Fin 2) ℂ) = 1 :=
  archComplexLiftAt_of_symm_one hw

omit hw in
theorem hasDerivAt_rotR (s : ℝ) :
    HasDerivAt (fun t : ℝ => rotR t) (rotR' s) s := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) (-(Real.sin s : ℂ)) s := by
    simpa using (Real.hasDerivAt_cos s).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ)) (Real.cos s : ℂ) s := (Real.hasDerivAt_sin s).ofReal_comp
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotR, rotR', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | exact hc | exact hs | exact hs.neg

omit hw in
theorem hasDerivAt_rotS (s : ℝ) :
    HasDerivAt (fun t : ℝ => rotS t) (rotS' s) s := by
  have hc : HasDerivAt (fun t : ℝ => (Real.cos t : ℂ)) (-(Real.sin s : ℂ)) s := by
    simpa using (Real.hasDerivAt_cos s).ofReal_comp
  have hs : HasDerivAt (fun t : ℝ => (Real.sin t : ℂ) * Complex.I) ((Real.cos s : ℂ) * Complex.I) s :=
    (Real.hasDerivAt_sin s).ofReal_comp.mul_const Complex.I
  rw [hasDerivAt_pi]; intro i; rw [hasDerivAt_pi]; intro j
  fin_cases i <;> fin_cases j <;>
    simp only [rotS, rotS', Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Fin.zero_eta, Fin.mk_one, Fin.isValue] <;>
    first | exact hc | exact hs

omit hw in
theorem rotR'_eq (s : ℝ) : rotR' s =
    Matrix.of.symm (Matrix.of (rotR s) * archDirMatrixComplex .Fm) -
      Matrix.of.symm (Matrix.of (rotR s) * archDirMatrixComplex .E) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotR, rotR', archDirMatrixComplex, Matrix.mul_apply, Fin.sum_univ_two]

omit hw in
theorem rotS'_eq (s : ℝ) : rotS' s =
    Matrix.of.symm (Matrix.of (rotS s) * archDirMatrixComplex .iE) +
      Matrix.of.symm (Matrix.of (rotS s) * archDirMatrixComplex .iFm) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotS, rotS', archDirMatrixComplex, Matrix.mul_apply, Fin.sum_univ_two, mul_assoc, Complex.I_mul_I]

theorem hasDerivAt_comp_archComplexLiftAt {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (g : AdelicGL2 (𝓞 F) F) {γ : ℝ → Fin 2 → Fin 2 → ℂ} {γ' : Fin 2 → Fin 2 → ℂ} {s : ℝ}
    (hγ : HasDerivAt γ γ' s) (hdet : (Matrix.of (γ s)).det ≠ 0) :
    HasDerivAt (fun t : ℝ => φ (g * archComplexLiftAt hw (γ t)))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e)) (γ s) γ') s := by
  have hd : HasFDerivAt (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e))
      (fderiv ℝ (fun e : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e)) (γ s)) (γ s) :=
    (((hφ g).contDiffAt (isOpen_setOf_det_ne_zero_complex.mem_nhds hdet)).differentiableAt (by simp)).hasFDerivAt
  simpa only [Function.comp_def] using hd.comp_hasDerivAt s hγ

theorem archDerivAtComplex_apply_mul_lift {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (d : ArchDirComplex) (g : AdelicGL2 (𝓞 F) F) {e : Fin 2 → Fin 2 → ℂ} (he : (Matrix.of e).det ≠ 0) :
    archDerivAtComplex hw d φ (g * archComplexLiftAt hw e) =
      fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e
        (Matrix.of.symm (Matrix.of e * archDirMatrixComplex d)) := by
  have hdiff : HasFDerivAt (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e'))
      (fderiv ℝ (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e')) e)
      (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d 0 : Matrix (Fin 2) (Fin 2) ℂ))) := by
    rw [of_symm_mul_archFlowMatrixComplex_zero]
    exact (((hφ g).contDiffAt (isOpen_setOf_det_ne_zero_complex.mem_nhds he)).differentiableAt (by simp)).hasFDerivAt
  have hfun : (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) =
      fun t : ℝ => (fun e' : Fin 2 → Fin 2 → ℂ => φ (g * archComplexLiftAt hw e'))
        (Matrix.of.symm (Matrix.of e * (archFlowMatrixComplex d t : Matrix (Fin 2) (Fin 2) ℂ))) := by
    funext t
    show _ = φ (g * archComplexLiftAt hw _)
    rw [archFlowAtComplex, mul_assoc, archComplexLiftAt_mul_archComplexGLAt hw he]
  show deriv (fun t : ℝ => φ (g * archComplexLiftAt hw e * archFlowAtComplex hw d t)) 0 = _
  rw [hfun]
  simpa only [Function.comp_def] using
    (hdiff.comp_hasDerivAt (0 : ℝ) (hasDerivAt_of_symm_mul_archFlowMatrixComplex e d)).deriv

theorem hasDerivAt_rotR_flow {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y)
    (g : AdelicGL2 (𝓞 F) F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => y (g * archComplexLiftAt hw (rotR t)))
      (archDerivAtComplex hw .Fm y (g * archComplexLiftAt hw (rotR s)) -
        archDerivAtComplex hw .E y (g * archComplexLiftAt hw (rotR s))) s := by
  have h := hasDerivAt_comp_archComplexLiftAt hw hy g (hasDerivAt_rotR s) (det_rotR_ne s)
  rw [archDerivAtComplex_apply_mul_lift hw hy .Fm g (det_rotR_ne s),
    archDerivAtComplex_apply_mul_lift hw hy .E g (det_rotR_ne s), ← map_sub, ← rotR'_eq]
  exact h

theorem hasDerivAt_rotS_flow {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y)
    (g : AdelicGL2 (𝓞 F) F) (s : ℝ) :
    HasDerivAt (fun t : ℝ => y (g * archComplexLiftAt hw (rotS t)))
      (archDerivAtComplex hw .iE y (g * archComplexLiftAt hw (rotS s)) +
        archDerivAtComplex hw .iFm y (g * archComplexLiftAt hw (rotS s))) s := by
  have h := hasDerivAt_comp_archComplexLiftAt hw hy g (hasDerivAt_rotS s) (det_rotS_ne s)
  rw [archDerivAtComplex_apply_mul_lift hw hy .iE g (det_rotS_ne s),
    archDerivAtComplex_apply_mul_lift hw hy .iFm g (det_rotS_ne s), ← map_add, ← rotS'_eq]
  exact h

theorem hasDerivAt_flow {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (d : ArchDirComplex)
    (g : AdelicGL2 (𝓞 F) F) (t : ℝ) :
    HasDerivAt (fun s : ℝ => φ (g * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d φ (g * archFlowAtComplex hw d t)) t := by
  have h0 : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d φ (g * archFlowAtComplex hw d t)) 0 :=
    (hφ.differentiableAt_flow d (g * archFlowAtComplex hw d t)).hasDerivAt
  have hsub : HasDerivAt (fun s : ℝ => s - t) 1 t := by simpa using (hasDerivAt_id t).sub_const t
  have h0' : HasDerivAt (fun s : ℝ => φ ((g * archFlowAtComplex hw d t) * archFlowAtComplex hw d s))
      (archDerivAtComplex hw d φ (g * archFlowAtComplex hw d t)) ((fun s : ℝ => s - t) t) := by
    simp only [sub_self]; exact h0
  have h1 := HasDerivAt.scomp (𝕜 := ℝ) t (h := fun s : ℝ => s - t) h0' hsub
  rw [one_smul] at h1
  refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  show φ (g * archFlowAtComplex hw d s) = φ (g * archFlowAtComplex hw d t * archFlowAtComplex hw d (s - t))
  have hst : t + (s - t) = s := by ring
  rw [mul_assoc, ← archFlowAtComplex_add, hst]

omit [NumberField F] in
theorem norm_ringEquivComplexOfIsComplex_symm (z : ℂ) : ‖(ringEquivComplexOfIsComplex hw).symm z‖ = ‖z‖ := by
  have h := (isometryEquivComplexOfIsComplex hw).symm.dist_eq z 0
  have h0 : (isometryEquivComplexOfIsComplex hw).symm 0 = 0 := map_zero (ringEquivComplexOfIsComplex hw).symm
  rw [h0, dist_zero_right, dist_zero_right] at h
  exact h

omit [NumberField F] in

theorem glEquiv_mem_rowIsometrySubgroup₀ (m : GL (Fin 2) ℂ) (hdet : (m : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (hrow : ∀ x y : ℂ,
      ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2) :
    glEquivOfRingEquiv (ringEquivComplexOfIsComplex hw).symm m ∈ rowIsometrySubgroup₀ w.Completion :=
  map_mem_rowIsometrySubgroup₀_of_normPreserving _ (norm_ringEquivComplexOfIsComplex_symm hw) m
    ((mem_rowIsometrySubgroup₀_iff ℂ).2 ⟨hdet, by rw [hdet, norm_one], hrow⟩)

theorem comp_archComplexGLAt_mem {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    (m : GL (Fin 2) ℂ) (hdet : (m : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (hrow : ∀ x y : ℂ,
      ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 0 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ^ 2 +
        ‖x * (m : Matrix (Fin 2) (Fin 2) ℂ) 0 1 + y * (m : Matrix (Fin 2) (Fin 2) ℂ) 1 1‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : y ∈ Y) :
    (fun g => y (g * archComplexGLAt hw m)) ∈ Y :=
  hYK ⟨_, glEquiv_mem_rowIsometrySubgroup₀ hw m hdet hrow⟩ y hy

omit hw in
theorem row_rotR (s : ℝ) (x y : ℂ) :
    ‖x * (Real.cos s : ℂ) + y * (Real.sin s : ℂ)‖ ^ 2 + ‖x * (-(Real.sin s : ℂ)) + y * (Real.cos s : ℂ)‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h := Real.cos_sq_add_sin_sq s
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  linear_combination (x.re ^ 2 + x.im ^ 2 + y.re ^ 2 + y.im ^ 2) * h

omit hw in
theorem row_rotS (s : ℝ) (x y : ℂ) :
    ‖x * (Real.cos s : ℂ) + y * ((Real.sin s : ℂ) * Complex.I)‖ ^ 2 +
        ‖x * ((Real.sin s : ℂ) * Complex.I) + y * (Real.cos s : ℂ)‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h := Real.cos_sq_add_sin_sq s
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  linear_combination (x.re ^ 2 + x.im ^ 2 + y.re ^ 2 + y.im ^ 2) * h

omit hw in
theorem row_splitTorus (s : ℝ) (x y : ℂ) :
    ‖x * Complex.exp ((s : ℂ) * Complex.I) + y * 0‖ ^ 2 + ‖x * 0 + y * Complex.exp (-((s : ℂ) * Complex.I))‖ ^ 2 =
      ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  have h1 : ‖Complex.exp ((s : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I s
  have h2 : ‖Complex.exp (-((s : ℂ) * Complex.I))‖ = 1 := by
    have : -((s : ℂ) * Complex.I) = ((-s : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [this]; exact Complex.norm_exp_ofReal_mul_I (-s)
  rw [mul_zero, add_zero, mul_zero, zero_add, norm_mul, norm_mul, h1, h2, mul_one, mul_one]

omit hw in
theorem det_splitTorus (z : ℂ) : ((splitTorusGL2Complex z : GL (Fin 2) ℂ) : Matrix (Fin 2) (Fin 2) ℂ).det = 1 := by
  rw [splitTorusGL2Complex_coe, Matrix.det_fin_two_of, ← Complex.exp_add]
  simp

theorem comp_Mrot_mem {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : y ∈ Y) (s : ℝ) :
    (fun g => y (g * archFlowAtComplex hw .iH s)) ∈ Y := by
  have h := comp_archComplexGLAt_mem hw hYK (splitTorusGL2Complex ((s : ℂ) * Complex.I)) (det_splitTorus _)
    (fun x y => by rw [splitTorusGL2Complex_coe]; simpa using row_splitTorus s x y) hy
  exact h

theorem comp_Rrot_mem {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : y ∈ Y) (s : ℝ) :
    (fun g => y (g * archComplexLiftAt hw (rotR s))) ∈ Y := by
  rw [archComplexLiftAt_of_det_ne_zero hw (det_rotR_ne s)]
  refine comp_archComplexGLAt_mem hw hYK _ ?_ (fun x y => ?_) hy
  · simpa using det_rotR s
  · simpa [rotR] using row_rotR s x y

theorem comp_Srot_mem {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : y ∈ Y) (s : ℝ) :
    (fun g => y (g * archComplexLiftAt hw (rotS s))) ∈ Y := by
  rw [archComplexLiftAt_of_det_ne_zero hw (det_rotS_ne s)]
  refine comp_archComplexGLAt_mem hw hYK _ ?_ (fun x y => ?_) hy
  · simpa using det_rotS s
  · simpa [rotS] using row_rotS s x y

omit hw in
theorem splitTorusGL2Complex_two_pi : splitTorusGL2Complex (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
  apply Units.ext
  rw [splitTorusGL2Complex_coe, Units.val_one, Matrix.one_fin_two]
  have h1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast; exact Complex.exp_two_pi_mul_I
  have h2 : Complex.exp (-(((2 * Real.pi : ℝ) : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, h1, inv_one]
  rw [h1, h2]

theorem archFlowAtComplex_iH_two_pi : archFlowAtComplex hw .iH (2 * Real.pi) = 1 := by
  show archComplexGLAt hw (splitTorusGL2Complex (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) = 1
  rw [splitTorusGL2Complex_two_pi, map_one]

omit hw in
theorem circleGL2_eq_splitTorusGL2Complex {ζ : ℂˣ} {θ : ℝ} (h : Complex.exp (θ * Complex.I) = ζ) :
    circleGL2 ζ = splitTorusGL2Complex ((θ : ℂ) * Complex.I) := by
  apply Units.ext
  rw [circleGL2_coe, splitTorusGL2Complex_coe]
  have h1 : ((ζ⁻¹ : ℂˣ) : ℂ) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    rw [Units.val_inv_eq_inv_val, ← h, Complex.exp_neg]
  rw [h1, ← h]

theorem archCircleAt_eq_archFlowAtComplex {ζ : ℂˣ} {θ : ℝ} (h : Complex.exp (θ * Complex.I) = ζ) :
    archCircleAt hw ζ = archFlowAtComplex hw .iH θ := by
  show archComplexGLAt hw (circleGL2 ζ) = archComplexGLAt hw (splitTorusGL2Complex ((θ : ℂ) * Complex.I))
  rw [circleGL2_eq_splitTorusGL2Complex h]

theorem hasCircleWeightAt_of_eigen {Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : y ∈ Y) {m : ℤ}
    (hμ : archDerivAtComplex hw .iH y = (Complex.I * (m : ℂ)) • y) : HasCircleWeightAt hw m y := by
  intro ζ hζ g
  obtain ⟨θ, hθ⟩ := (Complex.norm_eq_one_iff (ζ : ℂ)).1 hζ
  have hflow := eigen_flow Y (archDerivAtComplex hw .iH) (fun s g => g * archFlowAtComplex hw .iH s)
    (fun y hy g s => hasDerivAt_flow hw (hYs y hy) .iH g s)
    (fun g => by show g * archFlowAtComplex hw .iH 0 = g; rw [archFlowAtComplex_zero, mul_one]) hy hμ g θ
  rw [archCircleAt_eq_archFlowAtComplex hw hθ, hflow, ← hθ, ← Complex.exp_int_mul]
  congr 1
  congr 1
  ring

end ComplexPlace

end AutomorphicForm.KStabAux

end

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archComplexGLAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero_complex IsArchSmoothAtComplex ArchDirComplex splitTorusGL2Complex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex circleGL2 archCircleAt HasCircleWeightAt hasCircleWeightAt_zero glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving splitTorusGL2Complex_coe archDirMatrixComplex archComplexLiftAt_mul_archComplexGLAt hasDerivAt_of_symm_mul_archFlowMatrixComplex of_symm_mul_archFlowMatrixComplex_zero archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul circleGL2_coe"
namespace KStabAux
p2m_open "AutomorphicForm"

open Matrix AutomorphicForm.WindowedSiegel

theorem main (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    (∀ y ∈ Y, archDerivAtComplex hw .iH y ∈ Y ∧
      (archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y) ∈ Y ∧
      (archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y) ∈ Y) ∧
    (∀ y ∈ Y, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ),
      HasDerivAt (fun t : ℝ => y (g * archFlowAtComplex hw .iH t))
        (archDerivAtComplex hw .iH y (g * archFlowAtComplex hw .iH s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * archComplexLiftAt hw (rotR t)))
        ((archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y) (g * archComplexLiftAt hw (rotR s))) s ∧
      HasDerivAt (fun t : ℝ => y (g * archComplexLiftAt hw (rotS t)))
        ((archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y) (g * archComplexLiftAt hw (rotS s))) s) ∧
    (∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S ≤ Y →
      (∀ y ∈ S, archDerivAtComplex hw .iH y ∈ S ∧
        (archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y) ∈ S ∧
        (archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y) ∈ S) →
      ∀ y ∈ S, ∀ s : ℝ, (fun g => y (g * archFlowAtComplex hw .iH s)) ∈ S ∧
        (fun g => y (g * archComplexLiftAt hw (rotR s))) ∈ S ∧
        (fun g => y (g * archComplexLiftAt hw (rotS s))) ∈ S) ∧
    (∀ y ∈ Y, ∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧
        archDerivAtComplex hw .iH (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
      y = ∑ m ∈ ms, ys m) := by
  classical

  set D₀ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y => archDerivAtComplex hw .iH y with hD₀
  set D₁ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
    fun y => archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y with hD₁
  set D₂ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
    fun y => archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y with hD₂
  set T₀ : ℝ → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F := fun s g => g * archFlowAtComplex hw .iH s with hT₀
  set T₁ : ℝ → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F := fun s g => g * archComplexLiftAt hw (rotR s) with hT₁
  set T₂ : ℝ → AdelicGL2 (𝓞 F) F → AdelicGL2 (𝓞 F) F := fun s g => g * archComplexLiftAt hw (rotS s) with hT₂

  have hadd₀ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), Z ≤ Y →
      ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, D₀ (y₁ + y₂) = D₀ y₁ + D₀ y₂ := fun Z hZ y₁ h₁ y₂ h₂ =>
    archDerivAtComplex_add (hYs _ (hZ h₁)) (hYs _ (hZ h₂)) _
  have hsmul₀ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), ∀ (c : ℂ), ∀ y ∈ Z, D₀ (c • y) = c • D₀ y :=
    fun Z c y _ => archDerivAtComplex_smul hw _ c y
  have hadd₁ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), Z ≤ Y →
      ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, D₁ (y₁ + y₂) = D₁ y₁ + D₁ y₂ := by
    intro Z hZ y₁ h₁ y₂ h₂
    simp only [hD₁]
    rw [archDerivAtComplex_add (hYs _ (hZ h₁)) (hYs _ (hZ h₂)),
      archDerivAtComplex_add (hYs _ (hZ h₁)) (hYs _ (hZ h₂))]
    abel
  have hsmul₁ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), ∀ (c : ℂ), ∀ y ∈ Z, D₁ (c • y) = c • D₁ y := by
    intro Z c y _
    simp only [hD₁]
    rw [archDerivAtComplex_smul hw _ c y, archDerivAtComplex_smul hw _ c y, smul_sub]
  have hadd₂ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), Z ≤ Y →
      ∀ y₁ ∈ Z, ∀ y₂ ∈ Z, D₂ (y₁ + y₂) = D₂ y₁ + D₂ y₂ := by
    intro Z hZ y₁ h₁ y₂ h₂
    simp only [hD₂]
    rw [archDerivAtComplex_add (hYs _ (hZ h₁)) (hYs _ (hZ h₂)),
      archDerivAtComplex_add (hYs _ (hZ h₁)) (hYs _ (hZ h₂))]
    abel
  have hsmul₂ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), ∀ (c : ℂ), ∀ y ∈ Z, D₂ (c • y) = c • D₂ y := by
    intro Z c y _
    simp only [hD₂]
    rw [archDerivAtComplex_smul hw _ c y, archDerivAtComplex_smul hw _ c y, smul_add]

  have hder₀ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), Z ≤ Y →
      ∀ y ∈ Z, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ), HasDerivAt (fun t : ℝ => y (T₀ t g)) (D₀ y (T₀ s g)) s :=
    fun Z hZ y hy g s => hasDerivAt_flow hw (hYs y (hZ hy)) .iH g s
  have hder₁ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), Z ≤ Y →
      ∀ y ∈ Z, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ), HasDerivAt (fun t : ℝ => y (T₁ t g)) (D₁ y (T₁ s g)) s :=
    fun Z hZ y hy g s => hasDerivAt_rotR_flow hw (hYs y (hZ hy)) g s
  have hder₂ : ∀ Z : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), Z ≤ Y →
      ∀ y ∈ Z, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ), HasDerivAt (fun t : ℝ => y (T₂ t g)) (D₂ y (T₂ s g)) s :=
    fun Z hZ y hy g s => hasDerivAt_rotS_flow hw (hYs y (hZ hy)) g s

  have hT₀0 : ∀ g, T₀ 0 g = g := fun g => by simp only [hT₀]; rw [archFlowAtComplex_zero, mul_one]
  have hT₀π : ∀ g, T₀ (2 * Real.pi) g = g := fun g => by
    simp only [hT₀]; rw [archFlowAtComplex_iH_two_pi, mul_one]
  have hT₁0 : ∀ g, T₁ 0 g = g := fun g => by simp only [hT₁]; rw [rotR_zero, archComplexLiftAt_one, mul_one]
  have hT₁π : ∀ g, T₁ (2 * Real.pi) g = g := fun g => by
    simp only [hT₁]; rw [rotR_two_pi, archComplexLiftAt_one, mul_one]
  have hT₂0 : ∀ g, T₂ 0 g = g := fun g => by simp only [hT₂]; rw [rotS_zero, archComplexLiftAt_one, mul_one]
  have hT₂π : ∀ g, T₂ (2 * Real.pi) g = g := fun g => by
    simp only [hT₂]; rw [rotS_two_pi, archComplexLiftAt_one, mul_one]

  have hmem₀ : ∀ y ∈ Y, ∀ t : ℝ, (fun g => y (T₀ t g)) ∈ Y := fun y hy t => comp_Mrot_mem hw hYK hy t
  have hmem₁ : ∀ y ∈ Y, ∀ t : ℝ, (fun g => y (T₁ t g)) ∈ Y := fun y hy t => comp_Rrot_mem hw hYK hy t
  have hmem₂ : ∀ y ∈ Y, ∀ t : ℝ, (fun g => y (T₂ t g)) ∈ Y := fun y hy t => comp_Srot_mem hw hYK hy t

  have hDmem₀ : ∀ y ∈ Y, D₀ y ∈ Y := D_mem Y D₀ T₀ (hder₀ Y le_rfl) hT₀0 hmem₀
  have hDmem₁ : ∀ y ∈ Y, D₁ y ∈ Y := D_mem Y D₁ T₁ (hder₁ Y le_rfl) hT₁0 hmem₁
  have hDmem₂ : ∀ y ∈ Y, D₂ y ∈ Y := D_mem Y D₂ T₂ (hder₂ Y le_rfl) hT₂0 hmem₂
  refine ⟨fun y hy => ⟨hDmem₀ y hy, hDmem₁ y hy, hDmem₂ y hy⟩,
    fun y hy g s => ⟨hder₀ Y le_rfl y hy g s, hder₁ Y le_rfl y hy g s, hder₂ Y le_rfl y hy g s⟩, ?_, ?_⟩
  ·
    intro S hSY hS y hy s
    haveI : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSY
    exact ⟨comp_mem S D₀ (fun y hy => (hS y hy).1) (hadd₀ S hSY) (hsmul₀ S) T₀ (hder₀ S hSY) hT₀0 hT₀π y hy s,
      comp_mem S D₁ (fun y hy => (hS y hy).2.1) (hadd₁ S hSY) (hsmul₁ S) T₁ (hder₁ S hSY) hT₁0 hT₁π y hy s,
      comp_mem S D₂ (fun y hy => (hS y hy).2.2) (hadd₂ S hSY) (hsmul₂ S) T₂ (hder₂ S hSY) hT₂0 hT₂π y hy s⟩
  ·
    intro y hy
    obtain ⟨σ, v, hv, hsum⟩ :=
      exists_sum_eigen Y D₀ hDmem₀ (hadd₀ Y le_rfl) (hsmul₀ Y) T₀ (hder₀ Y le_rfl) hT₀0 hT₀π y hy
    have hint : ∀ μ ∈ σ.filter (fun μ => v μ ≠ 0), ∃ n : ℤ, μ = Complex.I * (n : ℂ) := fun μ hμ =>
      eigenvalue_eq_I_mul Y D₀ T₀ (hder₀ Y le_rfl) hT₀0 hT₀π (hv μ (Finset.mem_filter.1 hμ).1).1
        (hv μ (Finset.mem_filter.1 hμ).1).2 (Finset.mem_filter.1 hμ).2
    choose! n hn using hint
    refine ⟨(σ.filter (fun μ => v μ ≠ 0)).image n,
      fun k => ∑ μ ∈ (σ.filter (fun μ => v μ ≠ 0)).filter (fun μ => n μ = k), v μ, ?_, ?_⟩
    · intro k hk
      have hfib : ∀ μ ∈ (σ.filter (fun μ => v μ ≠ 0)).filter (fun μ => n μ = k),
          v μ ∈ Y ∧ D₀ (v μ) = (Complex.I * (k : ℂ)) • v μ := by
        intro μ hμ
        obtain ⟨hμ', hnk⟩ := Finset.mem_filter.1 hμ
        have h := hv μ (Finset.mem_filter.1 hμ').1
        rw [← hnk, ← hn μ hμ']
        exact h
      obtain ⟨hmemk, hDk⟩ := eigen_sum Y D₀ (hadd₀ Y le_rfl) (hsmul₀ Y) (Complex.I * (k : ℂ)) _ v hfib
      refine ⟨hmemk, ?_, hDk⟩
      exact Finset.sum_induction v (HasCircleWeightAt hw k) (fun a b ha hb => ha.add hb)
        (hasCircleWeightAt_zero hw k) (fun μ hμ => hasCircleWeightAt_of_eigen hw hYs (hfib μ hμ).1 (hfib μ hμ).2)
    · rw [Finset.sum_fiberwise_of_maps_to (fun μ hμ => Finset.mem_image_of_mem n hμ), Finset.sum_filter_ne_zero]
      exact hsum

end AutomorphicForm.KStabAux

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    let D₀ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) := fun y => archDerivAtComplex hw .iH y
    let D₁ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y
    let D₂ : (AdelicGL2 (𝓞 F) F → ℂ) → (AdelicGL2 (𝓞 F) F → ℂ) :=
      fun y => archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y
    let Mrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archFlowAtComplex hw .iH s
    let Rrot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), -(Real.sin s : ℂ); (Real.sin s : ℂ), (Real.cos s : ℂ)]
    let Srot : ℝ → AdelicGL2 (𝓞 F) F := fun s => archComplexLiftAt hw
      !![(Real.cos s : ℂ), (Real.sin s : ℂ) * Complex.I; (Real.sin s : ℂ) * Complex.I, (Real.cos s : ℂ)]
    (∀ y ∈ Y, D₀ y ∈ Y ∧ D₁ y ∈ Y ∧ D₂ y ∈ Y) ∧
    (∀ y ∈ Y, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ),
      HasDerivAt (fun t : ℝ => y (g * Mrot t)) (D₀ y (g * Mrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Rrot t)) (D₁ y (g * Rrot s)) s ∧
      HasDerivAt (fun t : ℝ => y (g * Srot t)) (D₂ y (g * Srot s)) s) ∧
    (∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S ≤ Y →
      (∀ y ∈ S, D₀ y ∈ S ∧ D₁ y ∈ S ∧ D₂ y ∈ S) →
      ∀ y ∈ S, ∀ s : ℝ, (fun g => y (g * Mrot s)) ∈ S ∧ (fun g => y (g * Rrot s)) ∈ S ∧
        (fun g => y (g * Srot s)) ∈ S) ∧
    (∀ y ∈ Y, ∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧ D₀ (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
      y = ∑ m ∈ ms, ys m) := by
  exact AutomorphicForm.KStabAux.main F hw Y hYs hYK

end S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
end P2MW
export P2MW.S_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional (solution)
