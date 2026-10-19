-- Prove2me | Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
-- name    : OAI_GroupTheory_Kervaire_SpectralMeasures
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T15:08:40.87636+00:00
-- url     : https://prove2.me/theorems/a098f6ea-6391-4cb2-88ef-e32647a02c56
-- title:
--   Vector spectral measures and the fractional phase
-- statement:
--   These notions belong to a formal proof of the Kervaire conjecture in its unimodular form. For a group $A$ and an element $w$ of the free product $A*\langle t\rangle$ whose exponent sum in $t$ is $\pm1$, the natural map from $A$ to $(A*\langle t\rangle)/\langle\!\langle w\rangle\!\rangle$ is injective, so adjoining one generator and one such relation never kills a nontrivial group. The proof writes $w$ with unit $t$-exponents and represents elements of the normal closure by planar ribbon diagrams. These are pairs of permutations of darts satisfying an Euler equation, whose disks read off copies of the relator. A capping induction removes cancelling pairs of darts. Its key rigidity step at relator corners is proved analytically, with the fractional spectral phase of unitary operators over the group von Neumann algebra of $A$, which is subadditive under a trace.
--
--   For a normal operator $U$ on a Hilbert space and a vector $\xi$:
--
--   1. **Vector functional and measure.** The positive functional $f\mapsto\mathrm{Re}\langle\xi,f(U)\xi\rangle$ on continuous real functions on the spectrum, and its Riesz measure $\mu_\xi$, a finite measure on $\operatorname{spec}U$.
--   2. **Fractional phase.** $\mathrm{ph}(z)$ is the fractional part of $\arg z/2\pi$, in $[0,1)$ with $\mathrm{ph}(1)=0$, and
--   $$
--   \mathrm{ph}_\xi(U)=\int\mathrm{ph}(z)\,d\mu_\xi(z).
--   $$
--   3. **Continuous approximations.** The triangular cutoffs $\min(x,n(1-x))$ of the phase, continuous on the circle and increasing to the phase, together with $|z-1|^2$ and exponentials of continuous functions.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean

-- Generated from openai/math@1581d4c lean/OAI/GroupTheory/Kervaire/SpectralMeasures.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the Kervaire mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits

namespace OAI

noncomputable section

open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology

namespace KervaireSpectral

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
abbrev Operator (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →L[ℂ] H

/-- Embed a real-valued function into complex-valued functions. -/
def complexify {X : Type*} [TopologicalSpace X] (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] theorem complexify_apply {X : Type*} [TopologicalSpace X]
    (f : C(X, ℝ)) (x : X) : complexify f x = (f x : ℂ) := rfl

@[simp] theorem complexify_add {X : Type*} [TopologicalSpace X]
    (f g : C(X, ℝ)) : complexify (f + g) = complexify f + complexify g := by ext; simp [complexify]

@[simp] theorem complexify_smul {X : Type*} [TopologicalSpace X]
    (r : ℝ) (f : C(X, ℝ)) : complexify (r • f) = (r : ℂ) • complexify f := by
  ext; simp [complexify]

/-- A vector functional restricted to the continuous calculus of a normal operator. -/
def vectorFunctional (U : Operator H) [hU : IsStarNormal U] (ξ : H) :
    C_c(spectrum ℂ U, ℝ) →ₚ[ℝ] ℝ := .mk₀ {
  toFun f := (inner ℂ ξ (cfcHom hU (complexify f.toContinuousMap) ξ)).re
  map_add' f g := by
    have hfg : (f + g).toContinuousMap = f.toContinuousMap + g.toContinuousMap := rfl
    rw [hfg, complexify_add, map_add]
    simp
  map_smul' r f := by
    have hrf : (r • f).toContinuousMap = r • f.toContinuousMap := rfl
    rw [hrf, complexify_smul, map_smul]
    simp
  } (by
    intro f hf
    have hfc : 0 ≤ complexify f.toContinuousMap := by
      intro x
      exact (Complex.zero_le_real).mpr (hf x)
    have hc : 0 ≤ cfcHom hU (complexify f.toContinuousMap) :=
      (cfcHom_nonneg_iff hU).mpr hfc
    exact ((ContinuousLinearMap.nonneg_iff_isPositive _).mp hc).re_inner_nonneg_right ξ)

/-- The finite scalar spectral measure of a vector, on the actual spectrum. -/
def vectorMeasure (U : Operator H) [IsStarNormal U] (ξ : H) : Measure (spectrum ℂ U) :=
  RealRMK.rieszMeasure (vectorFunctional U ξ)

instance vectorMeasure_finite (U : Operator H) [IsStarNormal U] (ξ : H) :
    IsFiniteMeasure (vectorMeasure U ξ) := by
  dsimp [vectorMeasure]
  infer_instance

/-- Squared modulus of a continuous complex function, kept real-valued. -/
def normSqMap {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) : C(X, ℝ) :=
  ⟨fun z => Complex.normSq (f z), Complex.continuous_normSq.comp f.continuous⟩

def phase (z : ℂ) : ℝ := Int.fract (z.arg / (2 * Real.pi))

@[simp] theorem phase_one : phase 1 = 0 := by simp [phase]

def vectorPhase (U : Operator H) [IsStarNormal U] (ξ : H) : ℝ :=
  ∫ z, phase z ∂vectorMeasure U ξ

/-- The continuous squared distance to one on the spectrum. -/
def distanceSq (U : Operator H) : C(spectrum ℂ U, ℝ) :=
  ⟨fun z => Complex.normSq ((z : ℂ) - 1),
    Complex.continuous_normSq.comp (continuous_subtype_val.sub continuous_const)⟩

theorem phase_exp (x : ℝ) :
    phase (Complex.exp (x * Complex.I)) = Int.fract (x / (2 * Real.pi)) := by
  rw [phase, Complex.arg_exp_mul_I]
  apply Int.fract_eq_fract.mpr
  refine ⟨-toIocDiv Real.two_pi_pos (-Real.pi) x, ?_⟩
  rw [← sub_div, toIocMod_sub_self]
  simp only [zsmul_eq_mul, Int.cast_neg]
  field_simp

/-- A continuous triangular cutoff on the chosen angle interval. -/
def phaseTriangle (n : ℕ) (x : ℝ) : ℝ := min x ((n : ℝ) * (1 - x))

theorem continuous_phaseTriangle (n : ℕ) : Continuous (phaseTriangle n) := by
  unfold phaseTriangle
  fun_prop

@[simp] theorem phaseTriangle_zero (n : ℕ) : phaseTriangle n 0 = 0 := by
  simp [phaseTriangle]

@[simp] theorem phaseTriangle_one (n : ℕ) : phaseTriangle n 1 = 0 := by
  simp [phaseTriangle]

/-- Although phase is discontinuous, this clipped phase is continuous on the circle. -/
theorem continuous_clippedPhase (n : ℕ) :
    Continuous (fun z : Circle => phaseTriangle n (phase z)) := by
  apply (Circle.isCoveringMap_exp.isQuotientMap Circle.exp_surjective).continuous_iff.mpr
  have hc : Continuous (phaseTriangle n ∘ Int.fract) :=
    (continuous_phaseTriangle n).continuousOn.comp_fract'' (by simp)
  simpa only [Function.comp_def, Circle.coe_exp, phase_exp, id_eq] using
    hc.comp (continuous_id.div_const (2 * Real.pi))

/-- Continuous lower approximations to phase on a unitary spectrum. -/
def phaseApprox (U : Operator H) (hU : U ∈ unitary (Operator H)) (n : ℕ) :
    C(spectrum ℂ U, ℝ) :=
  ⟨fun z => phaseTriangle n (phase z), by
    have hm : ∀ z : spectrum ℂ U, ‖(z : ℂ)‖ = 1 := fun z =>
      CStarRing.norm_of_mem_unitary (spectrum_subset_unitary_of_mem_unitary hU z.property)
    exact (continuous_clippedPhase n).comp (continuous_subtype_val.subtype_mk (fun z => mem_sphere_zero_iff_norm.mpr (hm z)))⟩

/-- Pointwise exponential of a continuous complex-valued function. -/
def expMap {X : Type*} [TopologicalSpace X] (f : C(X, ℂ)) : C(X, ℂ) :=
  ⟨fun z => Complex.exp (f z), Complex.continuous_exp.comp f.continuous⟩

end KervaireSpectral

end

end OAI


