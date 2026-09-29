-- Prove2me | solution 1 for AutomorphicForm.exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:04.961684+00:00
-- url     : https://prove2.me/submissions/a8897159-fe68-5916-a9e7-a8df158cd632

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplex
import Definitions.Def_AutomorphicForm_ArchDerivCasimirComplexAPI
import Theorems.Thm_AutomorphicForm_su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional
import Theorems.Thm_AutomorphicForm_archDerivAtComplex_commutator_of_isArchSmoothAtComplex
import Theorems.Thm_Module_End_exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.Module
import Mathlib.Tactic.NoncommRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex

set_option autoImplicit false

p2m_open "NumberField AutomorphicForm P2MW.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex.AutomorphicForm NumberField.InfinitePlace NumberField.InfinitePlace.Completion"

open Filter Topology Complex

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archComplexGLAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero_complex IsArchSmoothAtComplex ArchDirComplex splitTorusGL2Complex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex circleGL2 archCircleAt HasCircleWeightAt glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving splitTorusGL2Complex_coe archDirMatrixComplex archComplexLiftAt_mul_archComplexGLAt hasDerivAt_of_symm_mul_archFlowMatrixComplex of_symm_mul_archFlowMatrixComplex_zero archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul circleGL2_coe su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional archDerivAtComplex_commutator_of_isArchSmoothAtComplex"
namespace RepCoreKS
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

end AutomorphicForm.RepCoreKS

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archComplexGLAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero_complex IsArchSmoothAtComplex ArchDirComplex splitTorusGL2Complex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex circleGL2 archCircleAt HasCircleWeightAt glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving splitTorusGL2Complex_coe archDirMatrixComplex archComplexLiftAt_mul_archComplexGLAt hasDerivAt_of_symm_mul_archFlowMatrixComplex of_symm_mul_archFlowMatrixComplex_zero archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul circleGL2_coe su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional archDerivAtComplex_commutator_of_isArchSmoothAtComplex"
namespace RepCoreKS
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

end AutomorphicForm.RepCoreKS

end

noncomputable section

namespace AutomorphicForm
p2m_export "AutomorphicForm" "rowIsometryInclAt₀ AdelicGL2 rowIsometrySubgroup₀ mem_rowIsometrySubgroup₀_iff archComplexGLAt archComplexLiftAt archComplexLiftAt_of_det_ne_zero isOpen_setOf_det_ne_zero_complex IsArchSmoothAtComplex ArchDirComplex splitTorusGL2Complex archFlowMatrixComplex archFlowAtComplex archFlowAtComplex_zero archFlowAtComplex_add archDerivAtComplex circleGL2 archCircleAt HasCircleWeightAt glEquivOfRingEquiv map_mem_rowIsometrySubgroup₀_of_normPreserving splitTorusGL2Complex_coe archDirMatrixComplex archComplexLiftAt_mul_archComplexGLAt hasDerivAt_of_symm_mul_archFlowMatrixComplex of_symm_mul_archFlowMatrixComplex_zero archComplexLiftAt_of_symm_one archDerivAtComplex_add archDerivAtComplex_smul circleGL2_coe su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional archDerivAtComplex_commutator_of_isArchSmoothAtComplex"
namespace RepCoreAux
p2m_open "AutomorphicForm"

open AutomorphicForm.RepCoreKS

variable {F : Type} [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)

def D0 (y : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := archDerivAtComplex hw .iH y

def D1 (y : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := archDerivAtComplex hw .Fm y - archDerivAtComplex hw .E y

def D2 (y : AdelicGL2 (𝓞 F) F → ℂ) : AdelicGL2 (𝓞 F) F → ℂ := archDerivAtComplex hw .iE y + archDerivAtComplex hw .iFm y

theorem archDerivAtComplex_sub' {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ)
    (hψ : IsArchSmoothAtComplex hw ψ) (d : ArchDirComplex) :
    archDerivAtComplex hw d (φ - ψ) = archDerivAtComplex hw d φ - archDerivAtComplex hw d ψ := by
  rw [sub_eq_add_neg, archDerivAtComplex_add hφ hψ.neg, ← neg_one_smul ℂ ψ, archDerivAtComplex_smul, neg_one_smul,
    ← sub_eq_add_neg]

theorem isArchSmoothAtComplex_D0 {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y) :
    IsArchSmoothAtComplex hw (D0 hw y) := hy.archDerivAtComplex _
theorem isArchSmoothAtComplex_D1 {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y) :
    IsArchSmoothAtComplex hw (D1 hw y) := (hy.archDerivAtComplex _).sub (hy.archDerivAtComplex _)
theorem isArchSmoothAtComplex_D2 {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y) :
    IsArchSmoothAtComplex hw (D2 hw y) := (hy.archDerivAtComplex _).add (hy.archDerivAtComplex _)

theorem D0_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) :
    D0 hw (φ + ψ) = D0 hw φ + D0 hw ψ := archDerivAtComplex_add hφ hψ _
theorem D0_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : D0 hw (c • φ) = c • D0 hw φ := archDerivAtComplex_smul hw _ c φ
theorem D1_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) :
    D1 hw (φ + ψ) = D1 hw φ + D1 hw ψ := by
  unfold D1; rw [archDerivAtComplex_add hφ hψ, archDerivAtComplex_add hφ hψ]; abel
theorem D1_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : D1 hw (c • φ) = c • D1 hw φ := by
  unfold D1; rw [archDerivAtComplex_smul, archDerivAtComplex_smul, smul_sub]
theorem D2_add {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsArchSmoothAtComplex hw φ) (hψ : IsArchSmoothAtComplex hw ψ) :
    D2 hw (φ + ψ) = D2 hw φ + D2 hw ψ := by
  unfold D2; rw [archDerivAtComplex_add hφ hψ, archDerivAtComplex_add hφ hψ]; abel
theorem D2_smul (c : ℂ) (φ : AdelicGL2 (𝓞 F) F → ℂ) : D2 hw (c • φ) = c • D2 hw φ := by
  unfold D2; rw [archDerivAtComplex_smul, archDerivAtComplex_smul, smul_add]

theorem comm01 {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y) :
    D0 hw (D1 hw y) - D1 hw (D0 hw y) = (-2 : ℂ) • D2 hw y := by
  obtain ⟨-, -, -, -, -, -, -, c8, c9, -, -, -, -, -, -⟩ :=
    AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw y hy
  unfold D0 D1 D2
  rw [archDerivAtComplex_sub' hw (hy.archDerivAtComplex _) (hy.archDerivAtComplex _)]
  funext g
  have h8 := congrFun c8 g
  have h9 := congrFun c9 g
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h8 h9 ⊢
  linear_combination h9 - h8

theorem comm02 {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y) :
    D0 hw (D2 hw y) - D2 hw (D0 hw y) = (2 : ℂ) • D1 hw y := by
  obtain ⟨-, -, -, -, -, -, -, -, -, c10, c11, -, -, -, -⟩ :=
    AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw y hy
  unfold D0 D1 D2
  rw [archDerivAtComplex_add (hy.archDerivAtComplex _) (hy.archDerivAtComplex _)]
  funext g
  have h10 := congrFun c10 g
  have h11 := congrFun c11 g
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h10 h11 ⊢
  linear_combination h10 + h11

theorem comm12 {y : AdelicGL2 (𝓞 F) F → ℂ} (hy : IsArchSmoothAtComplex hw y) :
    D1 hw (D2 hw y) - D2 hw (D1 hw y) = (-2 : ℂ) • D0 hw y := by
  obtain ⟨-, -, -, -, -, c6, c7, -, -, -, -, -, -, c14, c15⟩ :=
    AutomorphicForm.archDerivAtComplex_commutator_of_isArchSmoothAtComplex F hw y hy
  unfold D0 D1 D2
  rw [archDerivAtComplex_add (hy.archDerivAtComplex _) (hy.archDerivAtComplex _),
    archDerivAtComplex_add (hy.archDerivAtComplex _) (hy.archDerivAtComplex _),
    archDerivAtComplex_sub' hw (hy.archDerivAtComplex _) (hy.archDerivAtComplex _),
    archDerivAtComplex_sub' hw (hy.archDerivAtComplex _) (hy.archDerivAtComplex _)]
  funext g
  have h6 := congrFun c6 g
  have h7 := congrFun c7 g
  have h14 := congrFun c14 g
  have h15 := congrFun c15 g
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul] at h6 h7 h14 h15 ⊢
  linear_combination -h7 + h15 - h14 - h6

theorem main (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : Fin m → ℕ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ s p, x s p ∈ Y) ∧
      (∀ s p, n s < p → x s p = 0) ∧
      LinearIndependent ℂ (fun sp : (Σ s : Fin m, Fin (n s + 1)) => x sp.1 sp.2) ∧
      (∀ y ∈ Y, ∃ coef : (s : Fin m) → Fin (n s + 1) → ℂ, y = ∑ s, ∑ p : Fin (n s + 1), coef s p • x s p) ∧
      (∀ s p, D0 hw (x s p) = (Complex.I * ((n s : ℂ) - 2 * (p : ℂ))) • x s p) ∧
      (∀ s p, D1 hw (x s p) = x s (p + 1) - ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1)) ∧
      (∀ s p, D2 hw (x s p) = Complex.I • (x s (p + 1) + ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1))) ∧
      (∀ s p, p ≤ n s → HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℤ)) (x s p)) := by
  classical

  have hK : (∀ y ∈ Y, D0 hw y ∈ Y ∧ D1 hw y ∈ Y ∧ D2 hw y ∈ Y) ∧
      (∀ y ∈ Y, ∀ (g : AdelicGL2 (𝓞 F) F) (s : ℝ),
        HasDerivAt (fun t : ℝ => y (g * archFlowAtComplex hw .iH t)) (D0 hw y (g * archFlowAtComplex hw .iH s)) s ∧
        HasDerivAt (fun t : ℝ => y (g * archComplexLiftAt hw (rotR t))) (D1 hw y (g * archComplexLiftAt hw (rotR s))) s ∧
        HasDerivAt (fun t : ℝ => y (g * archComplexLiftAt hw (rotS t))) (D2 hw y (g * archComplexLiftAt hw (rotS s))) s) ∧
      (∀ S : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ), S ≤ Y →
        (∀ y ∈ S, D0 hw y ∈ S ∧ D1 hw y ∈ S ∧ D2 hw y ∈ S) →
        ∀ y ∈ S, ∀ s : ℝ, (fun g => y (g * archFlowAtComplex hw .iH s)) ∈ S ∧
          (fun g => y (g * archComplexLiftAt hw (rotR s))) ∈ S ∧
          (fun g => y (g * archComplexLiftAt hw (rotS s))) ∈ S) ∧
      (∀ y ∈ Y, ∃ (ms : Finset ℤ) (ys : ℤ → (AdelicGL2 (𝓞 F) F → ℂ)),
        (∀ m ∈ ms, ys m ∈ Y ∧ HasCircleWeightAt hw m (ys m) ∧ D0 hw (ys m) = (Complex.I * (m : ℂ)) • ys m) ∧
        y = ∑ m ∈ ms, ys m) :=
    AutomorphicForm.su2Derivs_stable_and_hasDerivAt_and_exists_sum_hasCircleWeightAt_of_finiteDimensional F hw Y hYs hYK
  obtain ⟨hstab, -, -, hdec⟩ := hK

  let r0 : Module.End ℂ Y := restr Y (D0 hw) (fun y hy => (hstab y hy).1)
    (fun y₁ h₁ y₂ h₂ => D0_add hw (hYs _ h₁) (hYs _ h₂)) (fun c y _ => D0_smul hw c y)
  let r1 : Module.End ℂ Y := restr Y (D1 hw) (fun y hy => (hstab y hy).2.1)
    (fun y₁ h₁ y₂ h₂ => D1_add hw (hYs _ h₁) (hYs _ h₂)) (fun c y _ => D1_smul hw c y)
  let r2 : Module.End ℂ Y := restr Y (D2 hw) (fun y hy => (hstab y hy).2.2)
    (fun y₁ h₁ y₂ h₂ => D2_add hw (hYs _ h₁) (hYs _ h₂)) (fun c y _ => D2_smul hw c y)
  have r0c : ∀ v : Y, ((r0 v : Y) : AdelicGL2 (𝓞 F) F → ℂ) = D0 hw v := fun v => rfl
  have r1c : ∀ v : Y, ((r1 v : Y) : AdelicGL2 (𝓞 F) F → ℂ) = D1 hw v := fun v => rfl
  have r2c : ∀ v : Y, ((r2 v : Y) : AdelicGL2 (𝓞 F) F → ℂ) = D2 hw v := fun v => rfl

  have R01 : r0 * r1 = r1 * r0 + (-2 : ℂ) • r2 := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      r0c, r1c, r2c]
    have h := comm01 hw (hYs _ v.2)
    rw [sub_eq_iff_eq_add'] at h
    rw [h]
  have R02 : r0 * r2 = r2 * r0 + (2 : ℂ) • r1 := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      r0c, r1c, r2c]
    have h := comm02 hw (hYs _ v.2)
    rw [sub_eq_iff_eq_add'] at h
    rw [h]
  have R12 : r1 * r2 = r2 * r1 + (-2 : ℂ) • r0 := by
    apply LinearMap.ext; intro v; apply Subtype.ext
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
      r0c, r1c, r2c]
    have h := comm12 hw (hYs _ v.2)
    rw [sub_eq_iff_eq_add'] at h
    rw [h]

  obtain ⟨hH, hHdef⟩ : ∃ T : Module.End ℂ Y, T = (-Complex.I) • r0 := ⟨_, rfl⟩
  obtain ⟨eE, eEdef⟩ : ∃ T : Module.End ℂ Y, T = (-(1 / 2 : ℂ)) • (r1 + Complex.I • r2) := ⟨_, rfl⟩
  obtain ⟨fF, fFdef⟩ : ∃ T : Module.End ℂ Y, T = (1 / 2 : ℂ) • (r1 + (-Complex.I) • r2) := ⟨_, rfl⟩
  have hhe : hH ∘ₗ eE - eE ∘ₗ hH = (2 : ℂ) • eE := by
    have key : hH * eE = (2 : ℂ) • eE + eE * hH := by
      rw [hHdef, eEdef]
      simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add, smul_smul, R01, R02]
      match_scalars <;> norm_num [Complex.ext_iff]
    apply LinearMap.ext; intro v; apply Subtype.ext
    have kv := congrArg (fun T : Module.End ℂ Y => ((T v : Y) : AdelicGL2 (𝓞 F) F → ℂ)) key
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul] at kv
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Submodule.coe_sub, Submodule.coe_smul]
    rw [kv]; module
  have hhf : hH ∘ₗ fF - fF ∘ₗ hH = -((2 : ℂ) • fF) := by
    have key : hH * fF = (-2 : ℂ) • fF + fF * hH := by
      rw [hHdef, fFdef]
      simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add, smul_smul, R01, R02]
      match_scalars <;> norm_num [Complex.ext_iff]
    apply LinearMap.ext; intro v; apply Subtype.ext
    have kv := congrArg (fun T : Module.End ℂ Y => ((T v : Y) : AdelicGL2 (𝓞 F) F → ℂ)) key
    simp only [Module.End.mul_apply, LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add,
      Submodule.coe_smul] at kv
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.neg_apply, Submodule.coe_sub,
      Submodule.coe_smul, Submodule.coe_neg]
    rw [kv]; module
  have hef : eE ∘ₗ fF - fF ∘ₗ eE = hH := by
    have key : eE * fF = hH + fF * eE := by
      rw [hHdef, eEdef, fFdef]
      simp only [smul_mul_assoc, mul_smul_comm, mul_add, add_mul, smul_add, smul_smul, R12]
      match_scalars <;> norm_num [Complex.ext_iff]
    apply LinearMap.ext; intro v; apply Subtype.ext
    have kv := congrArg (fun T : Module.End ℂ Y => ((T v : Y) : AdelicGL2 (𝓞 F) F → ℂ)) key
    simp only [Module.End.mul_apply, LinearMap.add_apply, Submodule.coe_add] at kv
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, Submodule.coe_sub]
    rw [kv]; module

  have hdiag : ⨆ μ : ℂ, Module.End.eigenspace hH μ = ⊤ := by
    rw [eq_top_iff]
    rintro v -
    obtain ⟨ms, ys, hys, hsum⟩ := hdec v v.2
    have hmem : ∀ m ∈ ms, ys m ∈ (⨆ μ : ℂ, Module.End.eigenspace hH μ).map Y.subtype := by
      intro m hm
      obtain ⟨hY, -, hD⟩ := hys m hm
      refine ⟨⟨ys m, hY⟩, ?_, rfl⟩
      apply Submodule.mem_iSup_of_mem (m : ℂ)
      rw [Module.End.mem_eigenspace_iff]
      apply Subtype.ext
      rw [hHdef]
      simp only [LinearMap.smul_apply, Submodule.coe_smul, r0c]
      rw [hD, smul_smul]
      congr 1
      rw [← mul_assoc, neg_mul, Complex.I_mul_I, neg_neg, one_mul]
    have hv : (v : AdelicGL2 (𝓞 F) F → ℂ) ∈ (⨆ μ : ℂ, Module.End.eigenspace hH μ).map Y.subtype := by
      rw [hsum]; exact Submodule.sum_mem _ hmem
    obtain ⟨v', hv', hvv⟩ := hv
    have : v' = v := Subtype.ext hvv
    rwa [this] at hv'

  obtain ⟨r, t, n, hprim, hlad, hli, hspan⟩ :=
    Module.End.exists_primitive_strings_basis_of_sl2_of_iSup_eigenspace_eq_top Y eE fF hH hhe hhf hef hdiag

  have er1 : r1 + eE = fF := by
    rw [eEdef, fFdef]
    simp only [smul_add, smul_smul]
    match_scalars <;> norm_num [Complex.ext_iff]
  have er2 : r2 = Complex.I • (fF + eE) := by
    rw [eEdef, fFdef]
    simp only [smul_add, smul_smul]
    match_scalars <;> norm_num [Complex.ext_iff]
  have er0 : ∀ v : Y, r0 v = Complex.I • hH v := by
    intro v
    rw [hHdef, LinearMap.smul_apply, smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]

  have hzero : ∀ s (p : ℕ), n s < p → (fF ^ p) (t s) = 0 := by
    intro s p hp
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hp
    rw [show n s + k + 1 = k + (n s + 1) by ring, pow_add, Module.End.mul_apply, (hprim s).2.2, map_zero]
  have hY0 : ∀ s (p : ℕ), r0 ((fF ^ p) (t s)) = (Complex.I * ((n s : ℂ) - 2 * (p : ℂ))) • (fF ^ p) (t s) := by
    intro s p
    by_cases hp : p ≤ n s
    · rw [er0, (hlad s p hp).1, smul_smul]
    · push Not at hp
      rw [hzero s p hp, map_zero, smul_zero]
  have hYe : ∀ s (p : ℕ), eE ((fF ^ p) (t s)) = ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • (fF ^ (p - 1)) (t s) := by
    intro s p
    rcases p with _ | q
    · simp [(hprim s).1]
    · by_cases hq : q ≤ n s
      · rw [(hlad s q hq).2, Nat.add_sub_cancel]
        congr 1; push_cast; ring
      · push Not at hq
        rw [hzero s (q + 1) (by omega), map_zero, Nat.add_sub_cancel, hzero s q hq, smul_zero]
  have hYf : ∀ s (p : ℕ), fF ((fF ^ p) (t s)) = (fF ^ (p + 1)) (t s) := by
    intro s p; rw [pow_succ', Module.End.mul_apply]
  have hY1 : ∀ s (p : ℕ), r1 ((fF ^ p) (t s)) =
      (fF ^ (p + 1)) (t s) - ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • (fF ^ (p - 1)) (t s) := by
    intro s p
    rw [show r1 ((fF ^ p) (t s)) = fF ((fF ^ p) (t s)) - eE ((fF ^ p) (t s)) from
      eq_sub_of_add_eq (by rw [← LinearMap.add_apply, er1]), hYf, hYe]
  have hY2 : ∀ s (p : ℕ), r2 ((fF ^ p) (t s)) =
      Complex.I • ((fF ^ (p + 1)) (t s) + ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • (fF ^ (p - 1)) (t s)) := by
    intro s p
    rw [show r2 ((fF ^ p) (t s)) = Complex.I • (fF ((fF ^ p) (t s)) + eE ((fF ^ p) (t s))) by
      rw [LinearMap.congr_fun er2 ((fF ^ p) (t s)), LinearMap.smul_apply, LinearMap.add_apply], hYf, hYe]

  refine ⟨r, n, fun s p => (((fF ^ p) (t s) : Y) : AdelicGL2 (𝓞 F) F → ℂ), fun s p => ((fF ^ p) (t s)).2,
    fun s p hp => by show (((fF ^ p) (t s) : Y) : AdelicGL2 (𝓞 F) F → ℂ) = 0; rw [hzero s p hp]; simp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    exact hli.map' Y.subtype (Submodule.ker_subtype Y)
  ·
    intro y hy
    have hmem : (⟨y, hy⟩ : Y) ∈ Submodule.span ℂ
        (Set.range (fun x : (Σ i : Fin r, Fin (n i + 1)) => (fF ^ (x.2 : ℕ)) (t x.1))) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hmem
    refine ⟨fun s p => c ⟨s, p⟩, ?_⟩
    have h := congrArg (Subtype.val : Y → (AdelicGL2 (𝓞 F) F → ℂ)) hc
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h
    rw [← h, Fintype.sum_sigma]
  · intro s p
    have h := congrArg (Subtype.val : Y → (AdelicGL2 (𝓞 F) F → ℂ)) (hY0 s p)
    simp only [Submodule.coe_smul] at h
    exact h
  · intro s p
    have h := congrArg (Subtype.val : Y → (AdelicGL2 (𝓞 F) F → ℂ)) (hY1 s p)
    simp only [Submodule.coe_smul, Submodule.coe_sub] at h
    exact h
  · intro s p
    have h := congrArg (Subtype.val : Y → (AdelicGL2 (𝓞 F) F → ℂ)) (hY2 s p)
    simp only [Submodule.coe_smul, Submodule.coe_add] at h
    exact h
  · intro s p hp
    refine hasCircleWeightAt_of_eigen hw hYs ((fF ^ p) (t s)).2 ?_
    have h := congrArg (Subtype.val : Y → (AdelicGL2 (𝓞 F) F → ℂ)) (hY0 s p)
    simp only [Submodule.coe_smul] at h
    rw [show ((((n s : ℤ) - 2 * (p : ℤ) : ℤ)) : ℂ) = (n s : ℂ) - 2 * (p : ℂ) by push_cast; ring]
    exact h

end AutomorphicForm.RepCoreAux

end

theorem solution
    (F : Type) [Field F] [NumberField F] {w : InfinitePlace F} (hw : w.IsComplex)
    (Y : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)) [FiniteDimensional ℂ Y]
    (hYs : ∀ y ∈ Y, IsArchSmoothAtComplex hw y)
    (hYK : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ y ∈ Y,
      (fun g => y (g * rowIsometryInclAt₀ F w k)) ∈ Y) :
    ∃ (m : ℕ) (n : Fin m → ℕ) (x : Fin m → ℕ → (AdelicGL2 (𝓞 F) F → ℂ)),
      (∀ s p, x s p ∈ Y) ∧
      (∀ s p, n s < p → x s p = 0) ∧
      LinearIndependent ℂ (fun sp : (Σ s : Fin m, Fin (n s + 1)) => x sp.1 sp.2) ∧
      (∀ y ∈ Y, ∃ coef : (s : Fin m) → Fin (n s + 1) → ℂ, y = ∑ s, ∑ p : Fin (n s + 1), coef s p • x s p) ∧
      (∀ s p, archDerivAtComplex hw .iH (x s p) = (Complex.I * ((n s : ℂ) - 2 * (p : ℂ))) • x s p) ∧
      (∀ s p, archDerivAtComplex hw .Fm (x s p) - archDerivAtComplex hw .E (x s p) =
        x s (p + 1) - ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1)) ∧
      (∀ s p, archDerivAtComplex hw .iE (x s p) + archDerivAtComplex hw .iFm (x s p) =
        Complex.I • (x s (p + 1) + ((p : ℂ) * ((n s : ℂ) + 1 - (p : ℂ))) • x s (p - 1))) ∧
      (∀ s p, p ≤ n s → HasCircleWeightAt hw ((n s : ℤ) - 2 * (p : ℤ)) (x s p)) := by
  exact AutomorphicForm.RepCoreAux.main F hw Y hYs hYK

end S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex
end P2MW
export P2MW.S_AutomorphicForm_exists_su2Strings_of_finiteDimensional_of_isArchSmoothAtComplex (solution)
