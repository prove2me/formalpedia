-- Prove2me | Definitions.Def_OAIQ6El000
-- name    : OAIQ6El000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-26T10:20:41.537169+00:00
-- url     : https://prove2.me/theorems/df2d746d-737d-4903-9cb9-c8289f8986d5
-- title:
--   Definitions bundle OAIQ6El000 of the split of OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.Elasticity.global_uniqueness`, carved from OpenAI's openai/math development (OpenAI, *Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem*, OpenAI Math Release, September 24, 2026, result family 372, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 305 declarations of OpenAI's Lean: 160 definitions, 1 inductive type or structure, 2 instances and 142 theorems. The definitions and types are `OAI.Elasticity.BoundedCoefficient`, `OAI.Elasticity.BoundedCoefficient.mulL`, `OAI.Elasticity.CMatrix`, `OAI.Elasticity.ComplexTrial`, `OAI.Elasticity.H10Hilbert`, `OAI.Elasticity.H1Hilbert`, `OAI.Elasticity.JetH`, `OAI.Elasticity.ScalarL2`, `OAI.Elasticity.SourceDomain`, `OAI.Elasticity.SourceSmoothBoundary`, `OAI.Elasticity.ambientDensity`, `OAI.Elasticity.ambientEnergy`, `OAI.Elasticity.ambientExtend`, `OAI.Elasticity.ambientRestrict`, `OAI.Elasticity.ambientScalar`, `OAI.Elasticity.boundaryForcePair`, `OAI.Elasticity.chartDerivativeEquiv`, `OAI.Elasticity.complexDensity`, `OAI.Elasticity.complexFieldTrial`, `OAI.Elasticity.complexImagH1`, `OAI.Elasticity.complexRealH1`, `OAI.Elasticity.complexResidualSize`, `OAI.Elasticity.complexTrialEnergy`, `OAI.Elasticity.complexTrialSize`, `OAI.Elasticity.componentTest`, `OAI.Elasticity.coordinateFrame`, `OAI.Elasticity.coordinateNormal`, `OAI.Elasticity.elasticDensity`, `OAI.Elasticity.fieldGradient`, `OAI.Elasticity.gluedH1`, `OAI.Elasticity.gradient`, `OAI.Elasticity.h10Submodule`, `OAI.Elasticity.h1Distribution`, `OAI.Elasticity.h1Equiv`, `OAI.Elasticity.h1Extend`, `OAI.Elasticity.h1Global`, `OAI.Elasticity.h1GradientDistribution`, `OAI.Elasticity.h1Restrict`, `OAI.Elasticity.h1Submodule`, `OAI.Elasticity.imTest` and 121 more.
--
--   **Sources.** They come from these modules of lean/OAI/MathematicalPhysics, in whole or in part: `Elasticity_Augmented`, `Elasticity_Bessel`, `Elasticity_BoundaryCalculus`, `Elasticity_BoundaryCharts`, `Elasticity_BoundaryData`, `Elasticity_BoundaryEnergy`, `Elasticity_BoundaryPackets`, `Elasticity_CGO`, `Elasticity_Carleman`, `Elasticity_Recovery`, `Elasticity_Regularity`, `Elasticity_Restriction`, `Elasticity_Solvability`, `Elasticity_Transfer`, `Elasticity_Transport`, `Elasticity_TransportAlgebra`, `Elasticity_Variational`, `Elasticity_WeakSolutions`.
--
--   **Imports.** It imports the published bundle `Def_ElasticityUniqueness`.
--
--   **Imported by** (directly, in this split): the bundles `OAIQ6El004` and `OAIQ6El005`; the statements `OAI.ElasticityAugmented.exists_physical_forced_transport`, `OAI.ElasticityAugmented.exists_physical_leading_frame`, `OAI.ElasticityAugmented.exists_physical_recursion_step`, `OAI_ElasticityAugmented_residual_source_tangent`, `OAI.ElasticityBoundaryGradientMass.transferred_gradient_mass`, `OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass`, `OAI.ElasticityBoundaryPacket.boundary_jets_global`, `OAI.ElasticityBoundaryPacket.boundary_values_global`, `OAI_ElasticityCGO_physical_column_of_recursion` and `OAI.Elasticity.physicalResidual_sq_mass`; the proofs of `OAI_ElasticityAugmented_residual_source_tangent`, `OAI.ElasticityBoundaryPacket.Setup.boundary_normal_step`, `OAI.ElasticityBoundaryPacket.Setup.field_gradient_mass`, `OAI.ElasticityBoundaryPacket.boundary_jets_global`, `OAI.ElasticityBoundaryPacket.boundary_values_global`, `OAI_ElasticityCGO_physical_column_of_recursion`, `OAI.ElasticityGeneralSlicing.cylinder_weak_slices` and `OAI.Elasticity.physicalResidual_sq_mass`.
-- source:
--   OpenAI, Global Uniqueness for the Smooth Isotropic Elasticity Inverse Problem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 372; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Global-Uniqueness-for-the-Smooth-Isotropic-Elasticity-Inverse-Problem-September-24-2026/article.pdf; Apache License 2.0); definitions carved from lean/OAI/MathematicalPhysics at commit adc7f12

import Mathlib
import Definitions.Def_ElasticityUniqueness

section
-- module Solutions.OAIQ6_Elast.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Augmented
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact differential-algebra identities of the physical and normalized
augmented elasticity systems. Smooth derivatives are constructed below;
commutation and Leibniz are proved, not postulated for the physical operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented

abbrev X := EuclideanSpace ℝ (Fin 3)
def e (i : Fin 3) : X := EuclideanSpace.single i 1

def smoothAlgebra : Subalgebra ℂ (X → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f}
  add_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.add hg
  mul_mem' := by
    intro f g hf hg
    change ContDiff ℝ (⊤ : ℕ∞) f at hf
    change ContDiff ℝ (⊤ : ℕ∞) g at hg
    exact hf.mul hg
  zero_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : X => (0 : ℂ))
    exact contDiff_const
  one_mem' := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : X => (1 : ℂ))
    exact contDiff_const
  algebraMap_mem' a := by
    change ContDiff ℝ (⊤ : ℕ∞) (fun _ : X => a)
    exact contDiff_const

abbrev Smooth := smoothAlgebra

lemma smooth_coe (f : Smooth) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℂ) := f.property

/-- Actual coordinate derivative, as a derivation of the smooth function algebra. -/
def coord (i : Fin 3) : Derivation ℂ Smooth Smooth := Derivation.mk'
  { toFun := fun f => ⟨fun x => fderiv ℝ (f : X → ℂ) x (e i),
        by
          change ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ (f : X → ℂ) x (e i))
          exact ((smooth_coe f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const⟩
    map_add' := by
      intro f g
      apply Subtype.ext
      funext x
      exact congrArg (fun L : X →L[ℝ] ℂ => L (e i))
        (fderiv_add ((smooth_coe f).differentiable (by simp) x)
          ((smooth_coe g).differentiable (by simp) x))
    map_smul' := by
      intro a f
      apply Subtype.ext
      funext x
      exact congrArg (fun L : X →L[ℝ] ℂ => L (e i))
        (fderiv_const_smul ((smooth_coe f).differentiable (by simp) x) a) }
  (by
    intro f g
    apply Subtype.ext
    funext x
    exact congrArg (fun L : X →L[ℝ] ℂ => L (e i))
      (fderiv_mul ((smooth_coe f).differentiable (by simp) x)
        ((smooth_coe g).differentiable (by simp) x)))

lemma coord_apply (i : Fin 3) (f : Smooth) (x : X) :
    (coord i f : X → ℂ) x = fderiv ℝ (f : X → ℂ) x (e i) := rfl

section DifferentialAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A)

def lap (f : A) : A := ∑ i, D i (D i f)
def div (u : ι → A) : A := ∑ i, D i (u i)
def cm (m : A) (u : ι → A) (i : ι) : A :=
  ∑ j, D j m * (D j (u i) + D i (u j))
def R (lam m : A) (u : ι → A) (d : A) (i : ι) : A :=
  m * lap D (u i) + (lam+m)*D i d + cm D m u i + D i lam*d
def S (lam m : A) (u : ι → A) (d : A) : A :=
  (lam+m+m)*lap D d + 2*(∑ i, D i (lam+m)*D i d) +
  2*(∑ i, D i m*lap D (u i)) +
  2*(∑ i, ∑ j, D i (D j m)*D i (u j)) + lap D lam*d
def P (m : A) (f : A) : A := m*lap D f + ∑ i, D i m*D i f

end DifferentialAlgebra

section CovariantAlgebra
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable {ι : Type*} [Fintype ι]
variable (D : ι → Derivation ℂ A A) (T : ι → A →ₗ[ℂ] A)

def lapT (f : A) : A := ∑ i, T i (T i f)
def divT (u : ι → A) : A := ∑ i, T i (u i)
def cmT (m : A) (u : ι → A) (i : ι) : A :=
  ∑ j, D j m * (T j (u i) + T i (u j))
def RT (lam m : A) (u : ι → A) (d : A) (i : ι) : A :=
  m * lapT T (u i) + (lam+m)*T i d + cmT D T m u i + D i lam*d
def ST (lam m : A) (u : ι → A) (d : A) : A :=
  (lam+m+m)*lapT T d + 2*(∑ i, D i (lam+m)*T i d) +
  2*(∑ i, D i m*lapT T (u i)) +
  2*(∑ i, ∑ j, D i (D j m)*T i (u j)) + lap D lam*d
def PT (m : A) (f : A) : A := m*lapT T f + ∑ i, D i m*T i f

variable (hD : ∀ i j f, D i (D j f) = D j (D i f))
variable (hT : ∀ i j f, T i (T j f) = T j (T i f))
variable (hTD : ∀ i a b, T i (a*b) = D i a*b+a*T i b)

/-- The physical stress-divergence, using the conjugated coordinate derivative. -/
def LT (lam m : A) (u : ι → A) (i : ι) : A :=
  T i (lam * divT T u) + ∑ j, T j (m*(T j (u i)+T i (u j)))

end CovariantAlgebra

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Bessel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Concrete Fourier Bessel potentials for the required negative-order
supported Carleman estimate. All functions and operators are actual Schwartz
maps; no Sobolev-shift estimate is being assumed. -/
open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityBessel
abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev S := SchwartzMap X ℂ

def weight (h s : ℝ) (x : X) : ℝ := (1 + ‖(2*Real.pi*h) • x‖^2)^(s/2)

@[simp] lemma weight_zero (h : ℝ) (x : X) : weight h 0 x = 1 := by simp [weight]

def Q (v : X) : S →L[ℂ] S :=
  SchwartzMap.smulLeftCLM ℂ (fun x => (inner ℝ x v : ℂ))

@[simp] lemma Q_apply (v : X) (f : S) (x : X) :
    Q v f x = (inner ℝ x v : ℂ) * f x := by
  have ht : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  have hc := Complex.ofRealCLM.hasTemperateGrowth.comp ht
  exact SchwartzMap.smulLeftCLM_apply_apply hc f x

@[simp] lemma weight_two (h : ℝ) (x : X) :
    weight h 2 x = 1 + ‖(2*Real.pi*h) • x‖^2 := by
  simp [weight]

end ElasticityBessel

/-! Positive commutator algebra on actual Schwartz functions, allowing
nonlocal Bessel shifts without silently retaining compact support. -/
open MeasureTheory Complex SchwartzMap LineDeriv
open scoped BigOperators LineDeriv SchwartzMap

namespace ElasticityNegativeOrder
open ElasticityBessel

section
abbrev X := ElasticityBessel.X

end

def rot (A : X ≃ₗᵢ[ℝ] X) : S →L[ℂ] S :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A.toContinuousLinearEquiv

@[simp] lemma rot_apply (A : X ≃ₗᵢ[ℝ] X) (f : S) (x : X) : rot A f x = f (A x) := rfl

end ElasticityNegativeOrder

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Literal first and second coordinate chain rules. The maps are genuine
Frechet-smooth maps; a tensor pullback will use these identities, rather
than postulating a transformed elasticity operator. -/
noncomputable section
open scoped BigOperators
namespace ElasticityBoundaryChainRule
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def dd (f : E → ℂ) (v : E) (x : E) : ℂ := fderiv ℝ f x v

end ElasticityBoundaryChainRule

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-! Smooth boundary geometry in open partial homeomorphism charts. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

def SourceSmoothBoundary (Ω : Set X) : Prop :=
  ∀ x ∈ frontier Ω, ∃ e : OpenPartialHomeomorph X X,
    x ∈ e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e e.source ∧
    ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target ∧
    e x 0 = 0 ∧
    ∀ y ∈ e.source, y ∈ Ω ↔ 0 < e y 0

def SourceDomain (Ω : Set X) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧ SourceSmoothBoundary Ω

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x ∈ e.source)

include he hi hx

lemma chart_fderiv_left_inverse :
    (fderiv ℝ e.symm (e x)).comp (fderiv ℝ e x) = ContinuousLinearMap.id ℝ X := by
  have hd := (he.differentiableOn (by simp)).differentiableAt (e.open_source.mem_nhds hx)
  have hd' := (hi.differentiableOn (by simp)).differentiableAt
    (e.open_target.mem_nhds (e.map_source hx))
  have hEq : e.symm ∘ e =ᶠ[𝓝 x] id := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    exact e.left_inv hy
  rw [← fderiv_comp x hd' hd, hEq.fderiv_eq, fderiv_id]

lemma chart_fderiv_right_inverse :
    (fderiv ℝ e x).comp (fderiv ℝ e.symm (e x)) = ContinuousLinearMap.id ℝ X := by
  simpa only [OpenPartialHomeomorph.symm_symm, e.left_inv hx] using
    chart_fderiv_left_inverse e.symm hi he (e.map_source hx)

/-- The derivative of a smooth open boundary chart is continuously invertible. -/
def chartDerivativeEquiv : X ≃L[ℝ] X := {
  toLinearEquiv := {
    toLinearMap := (fderiv ℝ e x).toLinearMap
    invFun := fderiv ℝ e.symm (e x)
    left_inv := fun v => by
      have h := congrArg (fun J : X →L[ℝ] X => J v) (chart_fderiv_left_inverse e he hi hx)
      exact h
    right_inv := fun v => by
      have h := congrArg (fun J : X →L[ℝ] X => J v) (chart_fderiv_right_inverse e he hi hx)
      exact h }
  continuous_toFun := (fderiv ℝ e x).continuous
  continuous_invFun := (fderiv ℝ e.symm (e x)).continuous }

@[simp] lemma chartDerivativeEquiv_apply (v : X) :
    chartDerivativeEquiv e he hi hx v = fderiv ℝ e x v := rfl

end Elasticity

end
end
section
/-! Orthogonal normalization of an honest physical boundary chart. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

/-- Normal covector of a linear boundary-coordinate map, represented in the
fixed Euclidean coordinates by Riesz duality. -/
def coordinateNormal (B : X ≃L[ℝ] X) : X :=
  (InnerProductSpace.toDual ℝ X).symm
    ((EuclideanSpace.proj (0 : Fin 3)).comp B.toContinuousLinearMap)

/-- A physical orthogonal frame whose first vector is the inward normal. -/
def coordinateFrame (B : X ≃L[ℝ] X) : X ≃ₗᵢ[ℝ] X :=
  (ℝ ∙ (EuclideanSpace.single 2 1 - ‖coordinateNormal B‖⁻¹ • coordinateNormal B))ᗮ.reflection

end Elasticity

end
end
section
/-! Honest boundary coordinates with orthogonal physical derivative at the
base point. The inward normal is coordinate 2, matching the frozen physical
half-space ODE. -/
noncomputable section
open Set Filter
open scoped Topology
namespace Elasticity

variable (e : OpenPartialHomeomorph X X)
    (he : ContDiffOn ℝ (⊤ : ℕ∞) e e.source)
    (hi : ContDiffOn ℝ (⊤ : ℕ∞) e.symm e.target)
    {x : X} (hx : x ∈ e.source)

def normalizedLinear : X ≃L[ℝ] X :=
  (coordinateFrame (chartDerivativeEquiv e he hi hx)).toContinuousLinearEquiv.trans
    (chartDerivativeEquiv e he hi hx)

def normalizedAffine : X ≃ₜ X :=
  (normalizedLinear e he hi hx).toHomeomorph.trans (Homeomorph.addRight (e x))

def normalizedParam : OpenPartialHomeomorph X X :=
  (normalizedAffine e he hi hx).toOpenPartialHomeomorph.trans e.symm

@[simp] lemma normalizedAffine_apply (z : X) :
    normalizedAffine e he hi hx z = normalizedLinear e he hi hx z + e x := rfl

@[simp] lemma normalizedParam_apply (z : X) :
    normalizedParam e he hi hx z = e.symm (normalizedLinear e he hi hx z + e x) := rfl

@[simp] lemma normalizedParam_target :
    (normalizedParam e he hi hx).target = e.source := by
  ext z
  simp [normalizedParam]

@[simp] lemma normalizedParam_zero : normalizedParam e he hi hx 0 = x := by
  simp [e.left_inv hx]

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Variational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped BigOperators



namespace Elasticity
open scoped BigOperators

lemma coordDeriv_add {f g : X → V} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (i : Fin 3) :
    coordDeriv (f+g) i = coordDeriv f i + coordDeriv g i := by
  funext x
  exact congrArg (fun L : X →L[ℝ] V => L (coordVector i))
    (fderiv_add (hf x) (hg x))

lemma coordDeriv_smul (c : ℝ) {f : X → V} (hf : Differentiable ℝ f)
    (i : Fin 3) : coordDeriv (c • f) i = c • coordDeriv f i := by
  funext x
  exact congrArg (fun L : X →L[ℝ] V => L (coordVector i))
    (fderiv_const_smul (hf x) c)

lemma coordDeriv_zero (i : Fin 3) : coordDeriv (0 : X → V) i = 0 := by
  ext x j
  simp [coordDeriv]

def smoothJetSubmodule (Ω : Set X) : Submodule ℝ (Ambient Ω) where
  carrier := SmoothJets Ω
  zero_mem' := by
    refine ⟨0, MemLp.zero, fun i => ?_, contDiff_const, ?_, ?_⟩
    · simpa only [coordDeriv_zero] using (MemLp.zero : MemLp (0 : X → V) 2 (volume.restrict Ω))
    · simp
    · funext i
      change 0 = _
      simp only [coordDeriv_zero, MemLp.toLp_zero]
  add_mem' := by
    rintro u v ⟨f, hf, hd, hs, hu, hud⟩ ⟨g, hg, he, ht, hv, hvd⟩
    have hb (i) : MemLp (coordDeriv (f+g) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (hd i).add (he i)
    refine ⟨f+g, hf.add hg, hb, hs.add ht, ?_, ?_⟩
    · simpa [hu, hv] using (MemLp.toLp_add hf hg).symm
    · funext i
      simp only [Prod.snd_add, Pi.add_apply, hud, hvd]
      simp only [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (MemLp.toLp_add (hd i) (he i)).symm
  smul_mem' := by
    rintro c u ⟨f, hf, hd, hs, hu, hud⟩
    have hb (i) : MemLp (coordDeriv (c • f) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (hd i).const_smul c
    refine ⟨c • f, hf.const_smul c, hb, hs.const_smul c, ?_, ?_⟩
    · simpa [hu] using (MemLp.toLp_const_smul c hf).symm
    · funext i
      change c • u.2 i = _
      rw [hud]
      simp only [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (MemLp.toLp_const_smul c (hd i)).symm

/-- Compactly supported interior test jets, with the actual support condition. -/
def testJetSubmodule (Ω : Set X) : Submodule ℝ (Ambient Ω) where
  carrier := TestJets Ω
  zero_mem' := by
    refine ⟨0, MemLp.zero, fun i => ?_, contDiff_const, HasCompactSupport.zero, ?_, ?_, ?_⟩
    · simpa only [coordDeriv_zero] using (MemLp.zero : MemLp (0 : X → V) 2 (volume.restrict Ω))
    · simp
    · simp
    · funext i
      change 0 = _
      simp only [coordDeriv_zero, MemLp.toLp_zero]
  add_mem' := by
    rintro u v ⟨f, hf, hd, hs, hc, hsup, hu, hud⟩ ⟨g, hg, he, ht, hgc, hgsup, hv, hvd⟩
    have hb (i) : MemLp (coordDeriv (f+g) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (hd i).add (he i)
    refine ⟨f+g, hf.add hg, hb, hs.add ht, hc.add hgc,
      (tsupport_add f g).trans (union_subset hsup hgsup), ?_, ?_⟩
    · simpa [hu, hv] using (MemLp.toLp_add hf hg).symm
    · funext i
      simp only [Prod.snd_add, Pi.add_apply, hud, hvd]
      simp only [coordDeriv_add (hs.differentiable (by simp)) (ht.differentiable (by simp))]
      exact (MemLp.toLp_add (hd i) (he i)).symm
  smul_mem' := by
    rintro c u ⟨f, hf, hd, hs, hc, hsup, hu, hud⟩
    have hb (i) : MemLp (coordDeriv (c • f) i) 2 (volume.restrict Ω) := by
      rw [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (hd i).const_smul c
    refine ⟨c • f, hf.const_smul c, hb, hs.const_smul c, (hc.smul_left : HasCompactSupport ((fun _ : X => c) • f)),
      (tsupport_smul_subset_right (fun _ : X => c) f).trans hsup, ?_, ?_⟩
    · simpa [hu] using (MemLp.toLp_const_smul c hf).symm
    · funext i
      change c • u.2 i = _
      rw [hud]
      simp only [coordDeriv_smul c (hs.differentiable (by simp))]
      exact (MemLp.toLp_const_smul c (hd i)).symm

lemma testJetSubmodule_le (Ω : Set X) : testJetSubmodule Ω ≤ smoothJetSubmodule Ω := by
  rintro u ⟨f,hf,hd,hs,_,_,hu,hud⟩
  exact ⟨f,hf,hd,hs,hu,hud⟩

def h1Submodule (Ω : Set X) : Submodule ℝ (Ambient Ω) :=
  (smoothJetSubmodule Ω).topologicalClosure

def h10Submodule (Ω : Set X) : Submodule ℝ (Ambient Ω) :=
  (testJetSubmodule Ω).topologicalClosure

lemma h10Submodule_le (Ω : Set X) : h10Submodule Ω ≤ h1Submodule Ω :=
  Submodule.topologicalClosure_mono (testJetSubmodule_le Ω)

lemma sameTrace_refl (Ω : Set X) (u : H1 Ω) : SameTrace Ω u u := by
  exact show u.val - u.val ∈ h10Submodule Ω by rw [sub_self]; exact Submodule.zero_mem _

lemma sameTrace_symm (Ω : Set X) {u v : H1 Ω} (h : SameTrace Ω u v) :
    SameTrace Ω v u := by
  exact show v.val - u.val ∈ h10Submodule Ω by
    rw [← neg_sub]; exact Submodule.neg_mem _ h

lemma sameTrace_trans (Ω : Set X) {u v w : H1 Ω}
    (h : SameTrace Ω u v) (h' : SameTrace Ω v w) : SameTrace Ω u w := by
  exact show u.val - w.val ∈ h10Submodule Ω by
    convert Submodule.add_mem (h10Submodule Ω) h h' using 1; abel

abbrev JetH (Ω : Set X) := PiLp 2 (fun _ : Option (Fin 3) => Lp V 2 (volume.restrict Ω))

def jetEquiv (Ω : Set X) : JetH Ω ≃L[ℝ] Ambient Ω := by
  let e : (Option (Fin 3) → Lp V 2 (volume.restrict Ω)) ≃L[ℝ] Ambient Ω :=
    { toLinearEquiv := LinearEquiv.piOptionEquivProd ℝ
      continuous_toFun := (continuous_apply none).prodMk
        (continuous_pi fun i => continuous_apply (some i))
      continuous_invFun := continuous_pi fun i => by
        cases i with
        | none => exact continuous_fst
        | some i => exact (continuous_apply i).comp continuous_snd }
  exact (PiLp.continuousLinearEquiv 2 ℝ _).trans e

@[simp] lemma jetEquiv_apply (Ω : Set X) (u : JetH Ω) :
    jetEquiv Ω u = (u none, fun i => u (some i)) := rfl

def H1Hilbert (Ω : Set X) : Submodule ℝ (JetH Ω) :=
  (h1Submodule Ω).comap (jetEquiv Ω).toLinearMap

def H10Hilbert (Ω : Set X) : Submodule ℝ (JetH Ω) :=
  (h10Submodule Ω).comap (jetEquiv Ω).toLinearMap

lemma isClosed_H10Hilbert (Ω : Set X) : IsClosed (H10Hilbert Ω : Set (JetH Ω)) :=
  (testJetSubmodule Ω).isClosed_topologicalClosure.preimage (jetEquiv Ω).continuous

instance instCompleteSpaceSubtypeJetHMemSubmoduleRealH10Hilbert (Ω : Set X) : CompleteSpace (H10Hilbert Ω) := (isClosed_H10Hilbert Ω).completeSpace_coe

lemma H10Hilbert_le (Ω : Set X) : H10Hilbert Ω ≤ H1Hilbert Ω :=
  Submodule.comap_mono (h10Submodule_le Ω)

/-- The Hilbert version is exactly the H¹ jet closure, not an extra
regularity hypothesis or a replacement by a smaller test space. -/
def h1Equiv (Ω : Set X) : (H1Hilbert Ω) ≃ H1 Ω where
  toFun u := ⟨jetEquiv Ω u, u.property⟩
  invFun u := ⟨(jetEquiv Ω).symm u.val, by
    change jetEquiv Ω ((jetEquiv Ω).symm u.val) ∈ h1Submodule Ω
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact u.property⟩
  left_inv u := by apply Subtype.ext; exact (jetEquiv Ω).symm_apply_apply u.val
  right_inv u := by apply Subtype.ext; exact (jetEquiv Ω).apply_symm_apply u.val

end Elasticity

end
end
section
/-! The physical energy is a continuous bilinear form on the actual
Hilbert jet space. Bounded coefficients below are proved from admissibility
later, rather than added to the inverse theorem. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace Elasticity

abbrev ScalarL2 (Ω : Set X) := Lp ℝ 2 (volume.restrict Ω)

structure BoundedCoefficient (Ω : Set X) (a : X → ℝ) : Prop where
  measurable : AEStronglyMeasurable a (volume.restrict Ω)
  bound : ∃ C : ℝ, ∀ᵐ x ∂(volume.restrict Ω), ‖a x‖ ≤ C

namespace BoundedCoefficient
variable {Ω : Set X} {a : X → ℝ} (ha : BoundedCoefficient Ω a)

include ha in
lemma mul_memLp (f : ScalarL2 Ω) : MemLp (fun x => a x * f x) 2 (volume.restrict Ω) := by
  obtain ⟨C,hC⟩ := ha.bound
  apply (Lp.memLp f).of_le_mul (c := C) (ha.measurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [hC] with x hx
  simpa only [Pi.mul_apply, norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))

def mulL : ScalarL2 Ω →L[ℝ] ScalarL2 Ω := by
  let F : ScalarL2 Ω →ₗ[ℝ] ScalarL2 Ω :=
    { toFun f := (ha.mul_memLp f).toLp _
      map_add' f g := by
        apply Lp.ext
        filter_upwards [(ha.mul_memLp (f+g)).coeFn_toLp,
          (ha.mul_memLp f).coeFn_toLp, (ha.mul_memLp g).coeFn_toLp,
          Lp.coeFn_add f g, Lp.coeFn_add ((ha.mul_memLp f).toLp _) ((ha.mul_memLp g).toLp _)]
          with x hfg hf hg hadd he
        rw [hfg,he]
        simp only [Pi.add_apply]
        rw [hf,hg,hadd]
        exact mul_add ..
      map_smul' c f := by
        apply Lp.ext
        filter_upwards [(ha.mul_memLp (c • f)).coeFn_toLp,
          (ha.mul_memLp f).coeFn_toLp, Lp.coeFn_smul c f,
          Lp.coeFn_smul c ((ha.mul_memLp f).toLp _)] with x hcf hf hs ht
        simp only [RingHom.id_apply]
        rw [hcf,ht]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [hf,hs]
        simp only [Pi.smul_apply, smul_eq_mul]
        ring }
  let C := ha.bound.choose
  have hC := ha.bound.choose_spec
  exact F.mkContinuous C (fun f => by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [(ha.mul_memLp f).coeFn_toLp,hC] with x hx hb
    change ‖(ha.mul_memLp f).toLp _ x‖ ≤ _
    rw [hx,norm_mul]
    exact mul_le_mul_of_nonneg_right hb (norm_nonneg _))

lemma mulL_ae (f : ScalarL2 Ω) : ha.mulL f =ᵐ[volume.restrict Ω] fun x => a x*f x :=
  (ha.mul_memLp f).coeFn_toLp

lemma inner_mulL (f g : ScalarL2 Ω) :
    inner ℝ (ha.mulL f) g = ∫ x, a x*f x*g x ∂(volume.restrict Ω) := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ha.mulL_ae f] with x hx
  rw [hx,real_inner_comm]
  rfl
end BoundedCoefficient

variable {Ω : Set X}

lemma lp_sum_ae {ι : Type*} (s : Finset ι) (f : ι → ScalarL2 Ω) :
    ((∑ i ∈ s, f i : ScalarL2 Ω) : X → ℝ) =ᵐ[volume.restrict Ω] fun x => ∑ i ∈ s, f i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    filter_upwards [Lp.coeFn_zero ℝ 2 (volume.restrict Ω)] with x hx
    exact hx
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    filter_upwards [Lp.coeFn_add (f i) (∑ j ∈ s, f j), ih] with x hx hy
    simp only [Pi.add_apply] at hx
    exact hx.trans (congrArg (fun t => f i x+t) hy)

def jetEntry (Ω : Set X) (i j : Fin 3) : JetH Ω →L[ℝ] ScalarL2 Ω :=
  ((EuclideanSpace.proj i).compLpL 2 (volume.restrict Ω)).comp
    (PiLp.proj 2 (fun _ : Option (Fin 3) => Lp V 2 (volume.restrict Ω)) (some j))

def jetDiv (Ω : Set X) : JetH Ω →L[ℝ] ScalarL2 Ω := ∑ i, jetEntry Ω i i

def jetStrain (Ω : Set X) (i j : Fin 3) : JetH Ω →L[ℝ] ScalarL2 Ω :=
  (1/2 : ℝ) • (jetEntry Ω i j + jetEntry Ω j i)

lemma jetEntry_ae (u : JetH Ω) (i j : Fin 3) :
    jetEntry Ω i j u =ᵐ[volume.restrict Ω] fun x => (u (some j) x) i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma jetDiv_ae (u : JetH Ω) :
    jetDiv Ω u =ᵐ[volume.restrict Ω] fun x => ∑ i, (u (some i) x) i := by
  have hs := lp_sum_ae Finset.univ (fun i => jetEntry Ω i i u)
  have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, jetEntry Ω i i u x = (u (some i) x) i :=
    Filter.eventually_all.mpr (fun i => jetEntry_ae u i i)
  filter_upwards [hs,he] with x hx hy
  change (∑ i, jetEntry Ω i i) u x = _
  simpa only [sum_apply,hy] using hx

lemma jetStrain_ae (u : JetH Ω) (i j : Fin 3) :
    jetStrain Ω i j u =ᵐ[volume.restrict Ω]
      fun x => ((u (some j) x) i+(u (some i) x) j)/2 := by
  filter_upwards [Lp.coeFn_smul (1/2 : ℝ) (jetEntry Ω i j u+jetEntry Ω j i u),
    Lp.coeFn_add (jetEntry Ω i j u) (jetEntry Ω j i u),
    jetEntry_ae u i j, jetEntry_ae u j i] with x hs ha hi hj
  change ((1/2 : ℝ) • (jetEntry Ω i j u+jetEntry Ω j i u)) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [ha]
  simp only [Pi.add_apply,hi,hj]
  ring

def jetEnergy {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) : JetH Ω →L[ℝ] JetH Ω →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (hl.mulL.comp (jetDiv Ω)) (jetDiv Ω) +
    (2 : ℝ) • ∑ i, ∑ j, (innerSL ℝ).bilinearComp
      (hm.mulL.comp (jetStrain Ω i j)) (jetStrain Ω i j)

lemma jetEnergy_apply {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : JetH Ω) :
    jetEnergy hl hm u v = inner ℝ (hl.mulL (jetDiv Ω u)) (jetDiv Ω v) +
      2 * ∑ i, ∑ j, inner ℝ (hm.mulL (jetStrain Ω i j u)) (jetStrain Ω i j v) := by
  simp [jetEnergy,sum_apply,ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply]

end Elasticity

end
end
section
/-! Actual Korn and supported Poincaré identities, needed for variational
wellposedness of the physical DN map. No coercivity is assumed. -/
noncomputable section
open MeasureTheory SchwartzMap
open scoped BigOperators LineDeriv SchwartzMap
namespace ElasticityKorn
abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev S := SchwartzMap X ℝ
abbrev L2 : S →L[ℝ] Lp ℝ 2 (volume : Measure X) := SchwartzMap.toLpCLM ℝ ℝ 2 volume

def norm2 (f : S) := ‖L2 f‖
def pair (f g : S) : ℝ := inner ℝ (L2 f) (L2 g)
def e (i : Fin 3) : X := EuclideanSpace.single i 1
def d (v : X) : S →ₗ[ℝ] S := (LineDeriv.lineDerivOpCLM ℝ S v).toLinearMap
@[simp] lemma d_apply (v : X) (f : S) (x : X) :
    d v f x = fderiv ℝ (f : X → ℝ) x v := rfl
lemma smooth (f : S) : ContDiff ℝ (⊤ : ℕ∞) (f : X → ℝ) := f.smooth _
lemma pair_integral (f g : S) : pair f g = ∫ x : X, f x * g x := by
  rw [pair, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume, g.coeFn_toLp 2 volume] with x hx hy
  change inner ℝ (f.toLp 2 volume x) (g.toLp 2 volume x) = _
  rw [hx, hy]
  exact real_inner_comm _ _

lemma pair_self (f : S) : pair f f = norm2 f ^ 2 := real_inner_self_eq_norm_sq _
lemma pair_symm (f g : S) : pair f g = pair g f := real_inner_comm _ _
lemma pair_add_left (f g h : S) : pair (f+g) h = pair f h + pair g h := by
  simp only [pair, map_add, inner_add_left]
lemma pair_add_right (f g h : S) : pair f (g+h) = pair f g + pair f h := by
  simp only [pair, map_add, inner_add_right]
lemma pair_smul_left (c : ℝ) (f g : S) : pair (c • f) g = c * pair f g := by
  simp only [pair, map_smul, real_inner_smul_left]
lemma pair_smul_right (c : ℝ) (f g : S) : pair f (c • g) = c * pair f g := by
  simp only [pair, map_smul, real_inner_smul_right]
lemma pair_sum_left {ι : Type*} (s : Finset ι) (f : ι → S) (g : S) :
    pair (∑ i ∈ s, f i) g = ∑ i ∈ s, pair (f i) g := by
  simp only [pair, map_sum, sum_inner]
lemma pair_sum_right {ι : Type*} (s : Finset ι) (f : S) (g : ι → S) :
    pair f (∑ i ∈ s, g i) = ∑ i ∈ s, pair f (g i) := by
  simp only [pair, map_sum, inner_sum]
lemma pair_bound (f g : S) : |pair f g| ≤ norm2 f * norm2 g := abs_real_inner_le_norm _ _
lemma integrable_pair (f g : S) : Integrable (fun x : X => f x*g x) :=
  (SchwartzMap.pairing (ContinuousLinearMap.mul ℝ ℝ) f g).integrable
lemma pair_d (f g : S) (v : X) : pair f (d v g) = -pair (d v f) g := by
  simp only [pair_integral]
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (integrable_pair (d v f) g) (integrable_pair f (d v g)) (integrable_pair f g)
    (fun x _ => (smooth f).differentiable (by simp) x)
    (fun x _ => (smooth g).differentiable (by simp) x)
lemma d_d (v w : X) (f : S) (x : X) :
    d v (d w f) x = fderiv ℝ (fderiv ℝ (f : X → ℝ)) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ (f : X → ℝ)) :=
    ((smooth f).fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  change fderiv ℝ (fun y => fderiv ℝ (f : X → ℝ) y w) x v = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp
lemma d_comm (v w : X) (f : S) : d v (d w f) = d w (d v f) := by
  ext x
  rw [d_d, d_d]
  exact (smooth f).contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)) _ _
lemma cross (v w : X) (f g : S) : pair (d v f) (d w g) = pair (d w f) (d v g) := by
  have h := pair_d (d v f) g w
  have h' := pair_d (d w f) g v
  rw [d_comm] at h
  exact h.trans h'.symm

def divergence (u : Fin 3 → S) : S := ∑ i, d (e i) (u i)
def gradEnergy (u : Fin 3 → S) : ℝ := ∑ i, ∑ j, norm2 (d (e i) (u j)) ^ 2
def strainEnergy (u : Fin 3 → S) : ℝ :=
  ∑ i, ∑ j, norm2 ((1/2 : ℝ) • (d (e i) (u j) + d (e j) (u i))) ^ 2
lemma norm2_half_add_sq (f g : S) :
    norm2 ((1/2 : ℝ) • (f+g)) ^ 2 = (norm2 f ^ 2 + 2*pair f g + norm2 g ^ 2)/4 := by
  rw [← pair_self, pair_smul_left, pair_smul_right, pair_add_left,
    pair_add_right, pair_add_right, pair_self, pair_self, pair_symm g f]
  ring
lemma cross_sum (u : Fin 3 → S) :
    (∑ i, ∑ j, pair (d (e i) (u j)) (d (e j) (u i))) = norm2 (divergence u) ^ 2 := by
  rw [← pair_self, divergence, pair_sum_left]
  simp_rw [pair_sum_right]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cross]
  exact pair_symm _ _
/-- The classical exact whole-space Korn identity, by two integrations by parts. -/
theorem korn_identity (u : Fin 3 → S) :
    2*strainEnergy u = gradEnergy u + norm2 (divergence u)^2 := by
  simp only [strainEnergy, norm2_half_add_sq, add_div, mul_div_assoc]
  simp_rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.mul_sum]
  have hs : (∑ i, ∑ j, norm2 (d (e j) (u i))^2) = gradEnergy u := Finset.sum_comm
  simp_rw [← Finset.sum_div]
  rw [hs, cross_sum u]
  change 2*((gradEnergy u/4 + 2*(norm2 (divergence u)^2/4)) + gradEnergy u/4) = _
  ring

theorem korn (u : Fin 3 → S) : gradEnergy u ≤ 2*strainEnergy u := by
  rw [korn_identity]
  exact le_add_of_nonneg_right (sq_nonneg _)

def qCLM : X →L[ℝ] ℝ := EuclideanSpace.proj 0
def Q : S →ₗ[ℝ] S := (SchwartzMap.smulLeftCLM ℝ qCLM).toLinearMap
@[simp] lemma Q_apply (f : S) (x : X) : Q f x = x 0 * f x :=
  SchwartzMap.smulLeftCLM_apply_apply qCLM.hasTemperateGrowth f x
lemma d_Q (f : S) : d (e 0) (Q f) = f + Q (d (e 0) f) := by
  ext x
  rw [d_apply]
  have hc : (Q f : X → ℝ) = fun x => x 0 * f x := by ext x; exact Q_apply f x
  rw [hc]
  change _ = f x + Q (d (e 0) f) x
  rw [Q_apply, d_apply]
  have h := congrArg (fun L : X →L[ℝ] ℝ => L (e 0))
    (((EuclideanSpace.proj (𝕜 := ℝ) 0).hasFDerivAt (x := x)).mul
      ((smooth f).differentiable (by simp) x).hasFDerivAt).fderiv
  simpa [e, add_comm, Pi.mul_def] using h
lemma pair_Q (f g : S) : pair f (Q g) = pair (Q f) g := by
  simp only [pair_integral, Q_apply]
  congr 1
  ext x
  ring
lemma norm2_Q_supported {R : ℝ} (f : S) (hf : ∀ x, f x ≠ 0 → |x 0| ≤ R) :
    norm2 (Q f) ≤ R*norm2 f := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [(Q f).coeFn_toLp 2 volume, f.coeFn_toLp 2 volume] with x hx hy
  change ‖(Q f).toLp 2 volume x‖ ≤ R*‖f.toLp 2 volume x‖
  rw [hx, hy, Q_apply, norm_mul, Real.norm_eq_abs]
  by_cases hz : f x=0
  · simp [hz]
  · exact mul_le_mul_of_nonneg_right (hf x hz) (norm_nonneg _)
/-- Supported Poincaré with explicit constant; support is imposed on the actual
function, not on an abstract or assumed Sobolev norm. -/
theorem poincare {R : ℝ} (f : S) (hf : ∀ x, f x ≠ 0 → |x 0| ≤ R) :
    norm2 f ≤ 2*R*norm2 (d (e 0) f) := by
  have he := pair_d (Q f) f (e 0)
  rw [d_Q, pair_add_left, pair_self, pair_symm (Q (d (e 0) f)) f, pair_Q] at he
  have ht := pair_bound (Q f) (d (e 0) f)
  have hq := norm2_Q_supported f hf
  have hnn : 0 ≤ norm2 (d (e 0) f) := norm_nonneg _
  have hn : 0 ≤ norm2 f := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hq hnn
  by_cases hzero : norm2 f = 0
  · rw [hzero]
    by_cases hR : 0 ≤ R
    · positivity
    · have hz : f=0 := by
        apply SchwartzMap.injective_toLp 2 volume
        change L2 f = L2 0
        rw [map_zero]
        exact norm_eq_zero.mp hzero
      rw [hz, map_zero]
      change 0 ≤ 2*R*‖L2 0‖
      rw [map_zero, norm_zero, mul_zero]
  · have hp : 0 < norm2 f := lt_of_le_of_ne hn (Ne.symm hzero)
    have ha := neg_le_abs (pair (Q f) (d (e 0) f))
    nlinarith

end ElasticityKorn

end
end
section
noncomputable section
open MeasureTheory SchwartzMap Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

instance temperate_restrict_volume (Ω : Set X) : (volume.restrict Ω).HasTemperateGrowth :=
  ⟨⟨volume.integrablePower,
    (Measure.integrable_pow_neg_integrablePower (volume : Measure X)).mono_measure
      Measure.restrict_le_self⟩⟩

abbrev schwartzR (Ω : Set X) : SchwartzMap X ℝ →L[ℝ] ScalarL2 Ω :=
  SchwartzMap.toLpCLM ℝ ℝ 2 (volume.restrict Ω)

lemma schwartzR_norm_sq (f : SchwartzMap X ℝ) :
    ‖schwartzR Ω f‖^2 = ∫ x, (f x)^2 ∂(volume.restrict Ω) := by
  rw [← real_inner_self_eq_norm_sq,MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 (volume.restrict Ω)] with x hx
  change inner ℝ (f.toLp 2 (volume.restrict Ω) x) (f.toLp 2 (volume.restrict Ω) x) = _
  rw [hx,real_inner_comm]
  exact (sq _).symm

lemma schwartzR_supported_norm (f : SchwartzMap X ℝ) (hf : tsupport (f : X → ℝ) ⊆ Ω) :
    ‖schwartzR Ω f‖ = ElasticityKorn.norm2 f := by
  have hsq : ‖schwartzR Ω f‖^2 = ElasticityKorn.norm2 f^2 := by
    rw [schwartzR_norm_sq,← ElasticityKorn.pair_self,ElasticityKorn.pair_integral]
    simp only [← sq]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : f x=0 := image_eq_zero_of_notMem_tsupport (fun ht => hx (hf ht))
    simp [hz]
  have hnon : 0 ≤ ElasticityKorn.norm2 f := norm_nonneg _
  nlinarith [norm_nonneg (schwartzR Ω f)]

def jetScalar (Ω : Set X) (k : Option (Fin 3)) (i : Fin 3) :
    JetH Ω →L[ℝ] ScalarL2 Ω :=
  ((EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω)).comp
    (PiLp.proj 2 (fun _ : Option (Fin 3) => Lp V 2 (volume.restrict Ω)) k)

lemma jetScalar_ae (u : JetH Ω) (k : Option (Fin 3)) (i : Fin 3) :
    jetScalar Ω k i u =ᵐ[volume.restrict Ω] fun x => (u k x) i :=
  ContinuousLinearMap.coeFn_compLpL _ _

lemma scalar_projection_norm_sq (u : Lp V 2 (volume.restrict Ω)) :
    ‖u‖^2 = ∑ i, ‖(EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) u‖^2 := by
  let F (i : Fin 3) : ScalarL2 Ω := (EuclideanSpace.proj (𝕜 := ℝ) i).compLpL 2 (volume.restrict Ω) u
  have hmeas (i : Fin 3) : Integrable (fun x => (F i x)^2) (volume.restrict Ω) := by
    simpa only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs] using (L2.integrable_inner (𝕜 := ℝ) (F i) (F i))
  have hnorm (i : Fin 3) : ‖F i‖^2 = ∫ x, (F i x)^2 ∂(volume.restrict Ω) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]
  change ‖u‖^2 = ∑ i, ‖F i‖^2
  simp_rw [hnorm]
  rw [← integral_finsetSum Finset.univ (fun i _ => hmeas i),← real_inner_self_eq_norm_sq,
    L2.inner_def]
  have he : ∀ᵐ x ∂(volume.restrict Ω), ∀ i, F i x=(u x) i :=
    Filter.eventually_all.mpr (fun i => ContinuousLinearMap.coeFn_compLpL _ u)
  apply integral_congr_ae
  filter_upwards [he] with x hx
  simp only [hx,real_inner_self_eq_norm_sq,EuclideanSpace.real_norm_sq_eq]

def jetValueSq (Ω : Set X) (u : JetH Ω) : ℝ := ∑ i, ‖jetScalar Ω none i u‖^2
def jetGradSq (Ω : Set X) (u : JetH Ω) : ℝ := ∑ i, ∑ j, ‖jetEntry Ω i j u‖^2
def jetStrainSq (Ω : Set X) (u : JetH Ω) : ℝ := ∑ i, ∑ j, ‖jetStrain Ω i j u‖^2

lemma jet_norm_sq (u : JetH Ω) : ‖u‖^2 = jetValueSq Ω u+jetGradSq Ω u := by
  rw [PiLp.norm_sq_eq_of_L2,Fintype.sum_option]
  simp_rw [scalar_projection_norm_sq]
  change jetValueSq Ω u+ (∑ j, ∑ i, ‖jetEntry Ω i j u‖^2) = _
  rw [Finset.sum_comm]
  rfl

lemma continuous_jetValueSq : Continuous (jetValueSq Ω) := by
  unfold jetValueSq
  fun_prop
lemma continuous_jetGradSq : Continuous (jetGradSq Ω) := by
  unfold jetGradSq
  fun_prop
lemma continuous_jetStrainSq : Continuous (jetStrainSq Ω) := by
  unfold jetStrainSq
  fun_prop

/-- The scalar derivatives of an actual vector-valued smooth test field. -/
lemma coordDeriv_scalar (f : X → V) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (i j : Fin 3) (x : X) :
    fderiv ℝ (fun y => (f y) i) x (coordVector j) = (coordDeriv f j x) i := by
  have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := f x)).comp x
    ((hf.differentiable (by simp) x).hasFDerivAt)
  change fderiv ℝ ((EuclideanSpace.proj (𝕜 := ℝ) i) ∘ f) x (coordVector j) = _
  rw [h.fderiv]
  rfl

lemma scalar_test_support (f : X → V) (i : Fin 3) :
    tsupport (fun x => (f x) i) ⊆ tsupport f :=
  tsupport_comp_subset (g := fun y : V => y i) rfl f

lemma jet_test_representation (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    ∃ F : Fin 3 → SchwartzMap X ℝ,
      (∀ i, tsupport (F i : X → ℝ) ⊆ Ω) ∧
      (∀ i, jetScalar Ω none i u = schwartzR Ω (F i)) ∧
      ∀ i j, jetEntry Ω i j u = schwartzR Ω (ElasticityKorn.d (ElasticityKorn.e j) (F i)) := by
  obtain ⟨f,hf,hd,hs,hc,hsub,hu,hud⟩ := hu
  let F (i : Fin 3) : SchwartzMap X ℝ :=
    ((hc.comp_left (g := fun y : V => y i) rfl)).toSchwartzMap
      ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hs)
  have hF (i) (x : X) : F i x=(f x) i := rfl
  refine ⟨F,fun i => (scalar_test_support f i).trans hsub,?_,?_⟩
  · intro i
    apply Lp.ext
    have hv : (u none : X → V) =ᵐ[volume.restrict Ω] f := by
      change (jetEquiv Ω u).1 =ᵐ[volume.restrict Ω] f
      rw [hu]
      exact hf.coeFn_toLp
    filter_upwards [jetScalar_ae u none i,hv,(F i).coeFn_toLp 2 (volume.restrict Ω)] with x hx hy hz
    exact hx.trans ((congrArg (fun y : V => y i) hy).trans hz.symm)
  · intro i j
    apply Lp.ext
    have hv : (u (some j) : X → V) =ᵐ[volume.restrict Ω] coordDeriv f j := by
      change (jetEquiv Ω u).2 j =ᵐ[volume.restrict Ω] coordDeriv f j
      rw [hud]
      exact (hd j).coeFn_toLp
    filter_upwards [jetEntry_ae u i j,hv,
      (ElasticityKorn.d (ElasticityKorn.e j) (F i)).coeFn_toLp 2 (volume.restrict Ω)] with x hx hy hz
    change jetEntry Ω i j u x = (ElasticityKorn.d (ElasticityKorn.e j) (F i)).toLp 2 (volume.restrict Ω) x
    rw [hz,ElasticityKorn.d_apply]
    change jetEntry Ω i j u x = fderiv ℝ (fun y => (f y) i) x (coordVector j)
    rw [coordDeriv_scalar f hs i j x,hx,hy]

end Elasticity

end
end
section
noncomputable section
open MeasureTheory SchwartzMap Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}

lemma schwartz_d_support (f : SchwartzMap X ℝ) (v : X) :
    tsupport (ElasticityKorn.d v f : X → ℝ) ⊆ tsupport (f : X → ℝ) :=
  tsupport_fderiv_apply_subset ℝ v

lemma schwartz_strain_support (f g : SchwartzMap X ℝ) (v w : X)
    (hf : tsupport (f : X → ℝ) ⊆ Ω) (hg : tsupport (g : X → ℝ) ⊆ Ω) :
    tsupport (((1/2 : ℝ) • (ElasticityKorn.d v f+ElasticityKorn.d w g)) : X → ℝ) ⊆ Ω := by
  exact (tsupport_smul_subset_right (fun _ : X => (1/2 : ℝ)) _).trans
    ((tsupport_add _ _).trans (union_subset ((schwartz_d_support f v).trans hf)
      ((schwartz_d_support g w).trans hg)))

lemma jet_test_energies (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    ∃ F : Fin 3 → SchwartzMap X ℝ,
      (∀ i, tsupport (F i : X → ℝ) ⊆ Ω) ∧
      jetValueSq Ω u = ∑ i, ElasticityKorn.norm2 (F i)^2 ∧
      jetGradSq Ω u = ElasticityKorn.gradEnergy F ∧
      jetStrainSq Ω u = ElasticityKorn.strainEnergy F := by
  obtain ⟨F,hF,hval,hgrad⟩ := jet_test_representation u hu
  refine ⟨F,hF,?_,?_,?_⟩
  · unfold jetValueSq
    simp_rw [hval]
    congr 1
    funext i
    rw [schwartzR_supported_norm _ (hF i)]
  · unfold jetGradSq ElasticityKorn.gradEnergy
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hgrad,schwartzR_supported_norm _ ((schwartz_d_support _ _).trans (hF j))]
  · unfold jetStrainSq ElasticityKorn.strainEnergy
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    change ‖(1/2 : ℝ) • (jetEntry Ω i j u+jetEntry Ω j i u)‖^2 = _
    rw [hgrad,hgrad,← map_add,← map_smul]
    rw [schwartzR_supported_norm _ (schwartz_strain_support _ _ _ _ (hF i) (hF j)),add_comm]

lemma test_korn (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    jetGradSq Ω u ≤ 2*jetStrainSq Ω u := by
  obtain ⟨F,_,_,hg,hs⟩ := jet_test_energies u hu
  rw [hg,hs]
  exact ElasticityKorn.korn F

lemma test_poincare {R : ℝ} (hR : 0 < R) (hbound : ∀ x ∈ Ω, |x 0| ≤ R)
    (u : JetH Ω) (hu : jetEquiv Ω u ∈ TestJets Ω) :
    jetValueSq Ω u ≤ 4*R^2*jetGradSq Ω u := by
  obtain ⟨F,hF,hv,hg,_⟩ := jet_test_energies u hu
  rw [hv,hg,ElasticityKorn.gradEnergy,Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have hp := ElasticityKorn.poincare (F i) (fun x hx =>
    hbound x (hF i (subset_tsupport _ hx)))
  have hsq : ElasticityKorn.norm2 (F i)^2 ≤
      4*R^2*ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e 0) (F i))^2 := by
    have := sq_le_sq₀ (norm_nonneg (ElasticityKorn.L2 (F i)))
      (show 0 ≤ 2*R*ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e 0) (F i)) by
        exact mul_nonneg (by positivity) (norm_nonneg _))
    have ht : ElasticityKorn.norm2 (F i)^2 ≤
        (2*R*ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e 0) (F i)))^2 := this.mpr hp
    nlinarith [ht]
  refine hsq.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.single_le_sum
    (fun j _ => sq_nonneg (ElasticityKorn.norm2 (ElasticityKorn.d (ElasticityKorn.e j) (F i))))
    (Finset.mem_univ (0 : Fin 3))

lemma h10_induction_closed {P : JetH Ω → Prop} (hP : IsClosed {u | P u})
    (htest : ∀ u, jetEquiv Ω u ∈ TestJets Ω → P u)
    (u : H10Hilbert Ω) : P u := by
  have hclosed : IsClosed {v : Ambient Ω | P ((jetEquiv Ω).symm v)} :=
    hP.preimage (jetEquiv Ω).symm.continuous
  have hsubset : closure (TestJets Ω) ⊆ {v : Ambient Ω | P ((jetEquiv Ω).symm v)} :=
    closure_minimal (fun v hv => htest _ (by simpa using hv)) hclosed
  have h := hsubset u.property
  change P ((jetEquiv Ω).symm (jetEquiv Ω u.val)) at h
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h

lemma h10_korn (u : H10Hilbert Ω) : jetGradSq Ω u ≤ 2*jetStrainSq Ω u := by
  apply h10_induction_closed
    (isClosed_le continuous_jetGradSq (continuous_const.mul continuous_jetStrainSq))
    test_korn u

lemma h10_poincare {R : ℝ} (hR : 0 < R) (hbound : ∀ x ∈ Ω, |x 0| ≤ R)
    (u : H10Hilbert Ω) : jetValueSq Ω u ≤ 4*R^2*jetGradSq Ω u := by
  apply h10_induction_closed
    (isClosed_le continuous_jetValueSq (continuous_const.mul continuous_jetGradSq))
    (test_poincare hR hbound) u

lemma h10_norm_strain (hB : Bornology.IsBounded Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : H10Hilbert Ω, ‖u‖^2 ≤ C*jetStrainSq Ω u := by
  obtain ⟨R,hR,hbound⟩ := hB.exists_pos_norm_le
  have hb (x : X) (hx : x ∈ Ω) : |x 0| ≤ R := by
    have hn : |x 0| ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x 0
    exact hn.trans (hbound x hx)
  refine ⟨2*(4*R^2+1),by positivity,?_⟩
  intro u
  have hp := h10_poincare hR hb u
  have hk := h10_korn u
  have he := jet_norm_sq u.val
  have hh : 0 ≤ 4*R^2+1 := by positivity
  have := mul_le_mul_of_nonneg_left hk hh
  change ‖u.val‖^2 ≤ _
  nlinarith

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity

variable {Ω : Set X}

lemma SmoothUpTo.continuousOn_closure {a : X → ℝ} (ha : SmoothUpTo Ω a) :
    ContinuousOn a (closure Ω) := by
  obtain ⟨U,_,hs,hf⟩ := ha
  exact hf.continuousOn.mono hs

lemma SmoothUpTo.boundedCoefficient {a : X → ℝ} (ha : SmoothUpTo Ω a)
    (hO : IsOpen Ω) (hB : Bornology.IsBounded Ω) : BoundedCoefficient Ω a := by
  have hc := ha.continuousOn_closure
  refine ⟨(hc.mono subset_closure).aestronglyMeasurable hO.measurableSet, ?_⟩
  obtain ⟨C,hC⟩ := hB.isCompact_closure.bddAbove_image hc.norm
  refine ⟨C, ?_⟩
  filter_upwards [self_mem_ae_restrict hO.measurableSet] with x hx
  exact hC ⟨x,subset_closure hx,rfl⟩

lemma Admissible.uniform_positive {lam mu : X → ℝ} (ha : Admissible Ω lam mu)
    (hB : Bornology.IsBounded Ω) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ closure Ω, c ≤ mu x ∧ c ≤ 3*lam x+2*mu x := by
  have hl := ha.1.continuousOn_closure
  have hm := ha.2.1.continuousOn_closure
  have hp : ContinuousOn (fun x => min (mu x) (3*lam x+2*mu x)) (closure Ω) :=
    hm.inf ((hl.const_mul 3).add (hm.const_mul 2))
  obtain ⟨c,hc,hbound⟩ := hB.isCompact_closure.exists_forall_le' hp
    (fun x hx => lt_min (ha.2.2 x hx).1 (ha.2.2 x hx).2)
  exact ⟨c,hc,fun x hx => le_min_iff.mp (hbound x hx)⟩

lemma trace_sq_le (A : Fin 3 → Fin 3 → ℝ) :
    (∑ i, A i i)^2 ≤ 3*∑ i, ∑ j, A i j^2 := by
  have ht : (∑ i, A i i)^2 ≤ 3*∑ i, A i i^2 := by
    simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => A i i))
  refine ht.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  apply Finset.sum_le_sum
  intro i _
  exact Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)

/-- Pointwise strong convexity controls the full physical symmetric strain,
including negative lambda. This uses the exact hypothesis 3λ+2μ>0. -/
lemma elasticity_density_lower (lam mu c : ℝ) (hc : 0 ≤ c) (hm : c ≤ mu)
    (hlm : c ≤ 3*lam+2*mu) (A : Fin 3 → Fin 3 → ℝ) :
    c*(∑ i, ∑ j, A i j^2) ≤ lam*(∑ i, A i i)^2+2*mu*(∑ i, ∑ j, A i j^2) := by
  have hA : 0 ≤ ∑ i, ∑ j, A i j^2 :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (A i j)))
  by_cases hl : 0 ≤ lam
  · have h1 := mul_nonneg hl (sq_nonneg (∑ i, A i i))
    have h2 := mul_le_mul_of_nonneg_right hm hA
    have h3 := mul_nonneg (hc.trans hm) hA
    nlinarith
  · have ht := mul_le_mul_of_nonpos_left (trace_sq_le A) (le_of_not_ge hl)
    have hk := mul_le_mul_of_nonneg_right hlm hA
    nlinarith

lemma weighted_integrable {a : X → ℝ} (ha : BoundedCoefficient Ω a)
    (f g : ScalarL2 Ω) : Integrable (fun x => a x*f x*g x) (volume.restrict Ω) := by
  simpa only [Pi.mul_def] using (ha.mul_memLp f).integrable_mul (Lp.memLp g)

lemma jetEnergy_integral {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : JetH Ω) :
    jetEnergy hl hm u v = ∫ x, lam x*jetDiv Ω u x*jetDiv Ω v x+
      2*mu x*∑ i, ∑ j, jetStrain Ω i j u x*jetStrain Ω i j v x ∂(volume.restrict Ω) := by
  have hL := weighted_integrable hl (jetDiv Ω u) (jetDiv Ω v)
  have hS (i j) := weighted_integrable hm (jetStrain Ω i j u) (jetStrain Ω i j v)
  rw [jetEnergy_apply,BoundedCoefficient.inner_mulL]
  simp_rw [BoundedCoefficient.inner_mulL]
  have hsum : Integrable (fun x => ∑ i, ∑ j,
      mu x*jetStrain Ω i j u x*jetStrain Ω i j v x) (volume.restrict Ω) :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hS i j))
  calc
    _ = (∫ x, lam x*jetDiv Ω u x*jetDiv Ω v x ∂(volume.restrict Ω))+
        2*(∫ x, ∑ i, ∑ j, mu x*jetStrain Ω i j u x*jetStrain Ω i j v x
          ∂(volume.restrict Ω)) := by
      rw [integral_finsetSum _ (fun i _ =>
        integrable_finsetSum _ (fun j _ => hS i j))]
      simp_rw [integral_finsetSum _ (fun j _ => hS _ j)]
    _ = ∫ x, lam x*jetDiv Ω u x*jetDiv Ω v x+
        2*(∑ i, ∑ j, mu x*jetStrain Ω i j u x*jetStrain Ω i j v x)
          ∂(volume.restrict Ω) := by
      rw [integral_add hL (hsum.const_mul 2),integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        simp only [Finset.mul_sum,mul_assoc])

lemma jetEnergy_eq_energy {lam mu : X → ℝ} (hl : BoundedCoefficient Ω lam)
    (hm : BoundedCoefficient Ω mu) (u v : H1Hilbert Ω) :
    jetEnergy hl hm u v = energy Ω lam mu (h1Equiv Ω u) (h1Equiv Ω v) := by
  rw [jetEnergy_integral,energy]
  apply integral_congr_ae
  have hsu : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j,
      jetStrain Ω i j u.val x=((u.val (some j) x) i+(u.val (some i) x) j)/2 :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => jetStrain_ae u.val i j))
  have hsv : ∀ᵐ x ∂(volume.restrict Ω), ∀ i j,
      jetStrain Ω i j v.val x=((v.val (some j) x) i+(v.val (some i) x) j)/2 :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (fun j => jetStrain_ae v.val i j))
  filter_upwards [jetDiv_ae u.val,jetDiv_ae v.val,hsu,hsv] with x hu hv hsu hsv
  simp only [hu,hv,hsu,hsv,div,strain,h1Equiv,Equiv.coe_fn_mk,jetEquiv_apply]

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

lemma scalarL2_norm_sq (f : ScalarL2 Ω) :
    ‖f‖^2 = ∫ x, (f x)^2 ∂(volume.restrict Ω) := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs]

lemma scalarL2_integrable_sq (f : ScalarL2 Ω) :
    Integrable (fun x => (f x)^2) (volume.restrict Ω) := by
  simpa only [real_inner_self_eq_norm_sq,Real.norm_eq_abs,sq_abs] using
    L2.integrable_inner (𝕜 := ℝ) f f

lemma jetDiv_strain_ae (u : JetH Ω) :
    jetDiv Ω u =ᵐ[volume.restrict Ω] fun x => ∑ i, jetStrain Ω i i u x := by
  have hs : ∀ᵐ x ∂(volume.restrict Ω), ∀ i,
      jetStrain Ω i i u x=((u (some i) x) i+(u (some i) x) i)/2 :=
    Filter.eventually_all.mpr (fun i => jetStrain_ae u i i)
  filter_upwards [jetDiv_ae u,hs] with x hx hy
  rw [hx]
  apply Finset.sum_congr rfl
  intro i _
  rw [hy]
  ring

lemma jetStrainSq_integral (u : JetH Ω) :
    jetStrainSq Ω u = ∫ x, ∑ i, ∑ j, (jetStrain Ω i j u x)^2 ∂(volume.restrict Ω) := by
  unfold jetStrainSq
  simp_rw [scalarL2_norm_sq]
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => scalarL2_integrable_sq _))]
  simp_rw [integral_finsetSum _ (fun j _ => scalarL2_integrable_sq _)]

lemma jetEnergy_lower (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (hO : IsOpen Ω) {c : ℝ} (hc : 0 ≤ c)
    (hp : ∀ x ∈ Ω, c ≤ mu x ∧ c ≤ 3*lam x+2*mu x) (u : JetH Ω) :
    c*jetStrainSq Ω u ≤ jetEnergy hl hm u u := by
  rw [jetStrainSq_integral,jetEnergy_integral,← integral_const_mul]
  have hS : Integrable (fun x => ∑ i, ∑ j, (jetStrain Ω i j u x)^2)
      (volume.restrict Ω) :=
    integrable_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => scalarL2_integrable_sq _))
  have hR : Integrable (fun x => lam x*jetDiv Ω u x*jetDiv Ω u x+
      2*mu x*∑ i, ∑ j, jetStrain Ω i j u x*jetStrain Ω i j u x)
      (volume.restrict Ω) := by
    have hsum := (integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun j _ =>
        weighted_integrable hm (jetStrain Ω i j u) (jetStrain Ω i j u)))).const_mul 2
    convert (weighted_integrable hl (jetDiv Ω u) (jetDiv Ω u)).add hsum using 1
    all_goals try with_reducible_and_instances rfl
    ext point
    simp only [Finset.mul_sum,mul_assoc,Pi.add_apply]
  apply integral_mono_ae (hS.const_mul c) hR
  filter_upwards [self_mem_ae_restrict hO.measurableSet,jetDiv_strain_ae u] with x hx hd
  have h := elasticity_density_lower (lam x) (mu x) c hc (hp x hx).1 (hp x hx).2
    (fun i j => jetStrain Ω i j u x)
  simpa only [hd,sq,mul_assoc] using h

/-- The actual Dirichlet physical energy on the exact zero-trace Hilbert space. -/
def zeroTraceEnergy (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu) :
    H10Hilbert Ω →L[ℝ] H10Hilbert Ω →L[ℝ] ℝ :=
  (jetEnergy hl hm).bilinearComp (H10Hilbert Ω).subtypeL (H10Hilbert Ω).subtypeL

lemma zeroTraceEnergy_apply (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u v : H10Hilbert Ω) : zeroTraceEnergy hl hm u v = jetEnergy hl hm u.val v.val := rfl

/-- Korn, supported Poincare and the exact strong convexity yield coercivity;
there is no sign restriction on lambda beyond 3 lambda + 2 mu > 0. -/
theorem physical_coercive (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) :
    IsCoercive (zeroTraceEnergy (ha.1.boundedCoefficient hO hB)
      (ha.2.1.boundedCoefficient hO hB)) := by
  obtain ⟨c,hc,hp⟩ := ha.uniform_positive hB
  obtain ⟨C,hC,hbound⟩ := h10_norm_strain hB
  refine ⟨c/C,div_pos hc hC,?_⟩
  intro u
  have hlower := jetEnergy_lower (ha.1.boundedCoefficient hO hB)
    (ha.2.1.boundedCoefficient hO hB) hO hc.le (fun x hx => hp x (subset_closure hx)) u.val
  have hn := mul_le_mul_of_nonneg_left (hbound u) (div_pos hc hC).le
  rw [zeroTraceEnergy_apply]
  have he : c/C*C=c := div_mul_cancel₀ c (ne_of_gt hC)
  have hprod : c/C*‖u‖^2 ≤ c*jetStrainSq Ω u := by
    simpa only [← mul_assoc,he] using hn
  nlinarith

end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

def traceSetoid (Ω : Set X) : Setoid (H1 Ω) where
  r := SameTrace Ω
  iseqv := ⟨sameTrace_refl Ω,fun h => sameTrace_symm Ω h,fun h h' => sameTrace_trans Ω h h'⟩

lemma trace_eq_iff (u v : H1 Ω) : trace Ω u = trace Ω v ↔ SameTrace Ω u v := by
  exact ⟨fun h => Quotient.exact (s := traceSetoid Ω) h, Quot.sound⟩

lemma hasZeroTrace_h1Equiv (u : H1Hilbert Ω) :
    HasZeroTrace Ω (h1Equiv Ω u) ↔ u.val ∈ H10Hilbert Ω := Iff.rfl

lemma sameTrace_h1Equiv (u v : H1Hilbert Ω) :
    SameTrace Ω (h1Equiv Ω u) (h1Equiv Ω v) ↔ u.val-v.val ∈ H10Hilbert Ω := by
  change (jetEquiv Ω u.val-jetEquiv Ω v.val ∈ h10Submodule Ω) ↔
    jetEquiv Ω (u.val-v.val) ∈ h10Submodule Ω
  rw [map_sub]

lemma weakSolution_h1Equiv (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1Hilbert Ω) : WeakSolution Ω lam mu (h1Equiv Ω u) ↔
      ∀ v : H10Hilbert Ω, jetEnergy hl hm u.val v.val=0 := by
  constructor
  · intro h v
    let v' : H1Hilbert Ω := ⟨v.val,H10Hilbert_le Ω v.property⟩
    exact (jetEnergy_eq_energy hl hm u v').trans (h _ v.property)
  · intro h v hv
    let v' := (h1Equiv Ω).symm v
    have hz : v'.val ∈ H10Hilbert Ω := by
      rw [← hasZeroTrace_h1Equiv]
      simpa only [v',Equiv.apply_symm_apply] using hv
    have he := jetEnergy_eq_energy hl hm u v'
    simp only [v',Equiv.apply_symm_apply] at he
    rw [← he]
    exact h ⟨v'.val,hz⟩

/-- Lax--Milgram applied to the actual physical form and the exact jet
closures. The prescribed trace is arbitrary, not restricted to smooth data. -/
theorem dirichlet_exists (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) :
    ∃ u : H1 Ω, trace Ω u=f ∧ WeakSolution Ω lam mu u := by
  let hl := ha.1.boundedCoefficient hO hB
  let hm := ha.2.1.boundedCoefficient hO hB
  let w := (h1Equiv Ω).symm f.out
  let L : H10Hilbert Ω →L[ℝ] ℝ := -(jetEnergy hl hm w.val).comp (H10Hilbert Ω).subtypeL
  let F := (InnerProductSpace.toDual ℝ (H10Hilbert Ω)).symm L
  have hC : IsCoercive (zeroTraceEnergy hl hm) := physical_coercive ha hO hB
  let z := hC.continuousLinearEquivOfBilin.symm F
  have hz (v : H10Hilbert Ω) : jetEnergy hl hm z.val v.val = -jetEnergy hl hm w.val v.val := by
    rw [← zeroTraceEnergy_apply,← hC.continuousLinearEquivOfBilin_apply]
    change inner ℝ (hC.continuousLinearEquivOfBilin (hC.continuousLinearEquivOfBilin.symm F)) v = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
    exact InnerProductSpace.toDual_symm_apply
  let u : H1Hilbert Ω := ⟨w.val+z.val,
    (H1Hilbert Ω).add_mem w.property (H10Hilbert_le Ω z.property)⟩
  refine ⟨h1Equiv Ω u,?_,?_⟩
  · have ht : SameTrace Ω (h1Equiv Ω u) (h1Equiv Ω w) := by
      apply (sameTrace_h1Equiv u w).mpr
      change w.val+z.val-w.val ∈ H10Hilbert Ω
      simpa only [add_sub_cancel_left] using z.property
    calc
      trace Ω (h1Equiv Ω u) = trace Ω (h1Equiv Ω w) := Quot.sound ht
      _ = trace Ω f.out := by rw [Equiv.apply_symm_apply]
      _ = f := Quot.out_eq f
  · apply (weakSolution_h1Equiv hl hm u).mpr
    intro v
    change jetEnergy hl hm (w.val+z.val) v.val = 0
    rw [map_add,add_apply,hz]
    exact add_neg_cancel _

theorem dirichletSolution_spec (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (f : BoundaryData Ω) :
    trace Ω (dirichletSolution Ω lam mu f)=f ∧
      WeakSolution Ω lam mu (dirichletSolution Ω lam mu f) := by
  have hex := dirichlet_exists ha hO hB f
  simp only [dirichletSolution,dite_eq_left hex]
  exact Classical.choose_spec hex

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryPackets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
/-!
Exact physical-DN remainder identity needed for boundary high-frequency tests.
All objects below use the physical energy and full trace quotient.
There are no additional main hypotheses; the estimates hold for any trial field.
-/
noncomputable section
open Set MeasureTheory
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}

/-- The variational residual, acting on all zero-trace test fields. -/
def physicalResidual (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : H1Hilbert Ω) : H10Hilbert Ω →L[ℝ] ℝ :=
  (jetEnergy hl hm u.val).comp (H10Hilbert Ω).subtypeL

/-- The actual physical solution with the same trace as the trial field. -/
def physicalProjection (u : H1Hilbert Ω) : H1Hilbert Ω :=
  (h1Equiv Ω).symm (dirichletSolution Ω lam mu (trace Ω (h1Equiv Ω u)))

lemma physicalProjection_trace (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) :
    trace Ω (h1Equiv Ω (physicalProjection (lam := lam) (mu := mu) u)) =
      trace Ω (h1Equiv Ω u) := by
  simpa only [physicalProjection, Equiv.apply_symm_apply] using
    (dirichletSolution_spec ha hO hB (trace Ω (h1Equiv Ω u))).1

/-- The exact zero-trace correction, not an assumed quasimode remainder. -/
def physicalError (ha : Admissible Ω lam mu) (hO : IsOpen Ω)
    (hB : Bornology.IsBounded Ω) (u : H1Hilbert Ω) : H10Hilbert Ω :=
  ⟨u.val - (physicalProjection (lam := lam) (mu := mu) u).val,
    (sameTrace_h1Equiv u _).mp ((trace_eq_iff _ _).mp
      (physicalProjection_trace ha hO hB u).symm)⟩

end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Restriction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Elasticity
variable {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable (μ : Measure α) (s : Set α)
def lpRestrictCLM : Lp E 2 μ →L[ℝ] Lp E 2 (μ.restrict s) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp) (by simpa using Measure.restrict_le_self (μ := μ) (s := s))
lemma lpRestrict_coe (f : Lp E 2 μ) : (lpRestrictCLM μ s f : α → E)=ᵐ[μ.restrict s] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
variable (hs : MeasurableSet s)
def lpZeroValue (f : Lp E 2 (μ.restrict s)) : Lp E 2 μ :=
  ((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)
omit [NormedSpace ℝ E] in
lemma lpZeroValue_coe (f : Lp E 2 (μ.restrict s)) :
    (lpZeroValue μ s hs f : α → E)=ᵐ[μ] s.indicator f := by
  unfold lpZeroValue
  exact @MemLp.coeFn_toLp α E _ 2 μ _ (s.indicator (⇑f))
    ((memLp_indicator_iff_restrict (p := 2) (μ := μ) hs).mpr (Lp.memLp f))
omit [NormedSpace ℝ E] in
lemma lpZeroValue_add (f g : Lp E 2 (μ.restrict s)) :
    lpZeroValue μ s hs (f+g)=lpZeroValue μ s hs f+lpZeroValue μ s hs g := by
  apply Lp.ext
  filter_upwards [lpZeroValue_coe μ s hs (f+g),lpZeroValue_coe μ s hs f,
    lpZeroValue_coe μ s hs g,Lp.coeFn_add (lpZeroValue μ s hs f) (lpZeroValue μ s hs g),
    (ae_restrict_iff' hs).mp (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
  rw [h1,h4]
  change s.indicator (⇑(f+g)) x=lpZeroValue μ s hs f x+lpZeroValue μ s hs g x
  rw [h2,h3]
  by_cases hx : x∈s
  · simp only [indicator_of_mem hx,h5 hx,Pi.add_apply]
  · simp only [indicator_of_notMem hx,add_zero]
lemma lpZeroValue_smul (c : ℝ) (f : Lp E 2 (μ.restrict s)) :
    lpZeroValue μ s hs (c • f)=c • lpZeroValue μ s hs f := by
  apply Lp.ext
  filter_upwards [lpZeroValue_coe μ s hs (c • f),lpZeroValue_coe μ s hs f,
    Lp.coeFn_smul c (lpZeroValue μ s hs f),
    (ae_restrict_iff' hs).mp (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
  rw [h1,h3]
  change s.indicator (⇑(c • f)) x=c • lpZeroValue μ s hs f x
  rw [h2]
  by_cases hx : x∈s
  · simp only [indicator_of_mem hx,h4 hx,Pi.smul_apply]
  · simp only [indicator_of_notMem hx,smul_zero]
def lpZeroExtend : Lp E 2 (μ.restrict s) →ₗ[ℝ] Lp E 2 μ where
  toFun := lpZeroValue μ s hs
  map_add' := lpZeroValue_add μ s hs
  map_smul' := lpZeroValue_smul μ s hs
lemma lpZeroExtend_norm (f : Lp E 2 (μ.restrict s)) : ‖lpZeroExtend μ s hs f‖=‖f‖ := by
  change ‖((memLp_indicator_iff_restrict hs).mpr (Lp.memLp f)).toLp (s.indicator f)‖=‖f‖
  rw [Lp.norm_toLp,Lp.norm_def,eLpNorm_indicator_eq_eLpNorm_restrict hs]
def lpZeroExtendCLM : Lp E 2 (μ.restrict s) →L[ℝ] Lp E 2 μ :=
  (lpZeroExtend μ s hs).mkContinuous 1 (fun f => by rw [lpZeroExtend_norm,one_mul])
lemma lpZeroExtend_coe (f : Lp E 2 (μ.restrict s)) :
    (lpZeroExtendCLM μ s hs f : α → E)=ᵐ[μ] s.indicator f := lpZeroValue_coe μ s hs f
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
namespace Elasticity
variable {Ω B : Set X}
def lpRestrictBetween (h : Ω⊆B) : Lp V 2 (volume.restrict B) →L[ℝ] Lp V 2 (volume.restrict Ω) :=
  Lp.LpToLpOfMeasureLeSMul (c := 1) (by simp)
    (by simpa using Measure.restrict_mono h (le_refl (volume : Measure X)))
lemma lpRestrictBetween_coe (h : Ω⊆B) (f : Lp V 2 (volume.restrict B)) :
    (lpRestrictBetween h f : X → V)=ᵐ[volume.restrict Ω] f :=
  Lp.coeFn_LpToLpOfMeasureLeSMul _ _ f
lemma lpRestrictBetween_toLp (h : Ω⊆B) (f : X → V)
    (hf : MemLp f 2 (volume.restrict B)) (hg : MemLp f 2 (volume.restrict Ω)) :
    lpRestrictBetween h (hf.toLp f)=hg.toLp f := by
  apply Lp.ext
  exact (lpRestrictBetween_coe h (hf.toLp f)).trans
    ((Measure.absolutelyContinuous_of_le (Measure.restrict_mono h (le_refl (volume : Measure X)))).ae_eq hf.coeFn_toLp |>.trans hg.coeFn_toLp.symm)
def ambientRestrict (h : Ω⊆B) : Ambient B →L[ℝ] Ambient Ω :=
  (lpRestrictBetween h).prodMap (ContinuousLinearMap.pi
    (fun i : Fin 3 => (lpRestrictBetween h).comp (ContinuousLinearMap.proj i)))
lemma restrict_smoothJet (h : Ω⊆B) {u : Ambient B} (hu : u∈SmoothJets B) :
    ambientRestrict h u∈SmoothJets Ω := by
  obtain ⟨f,hf,hd,hsm,hval,hder⟩ := hu
  have hm : volume.restrict Ω≤volume.restrict B := Measure.restrict_mono h (le_refl (volume : Measure X))
  refine ⟨f,hf.mono_measure hm,(fun i => (hd i).mono_measure hm),hsm,?_,?_⟩
  · change lpRestrictBetween h u.1=_
    rw [hval,lpRestrictBetween_toLp]
  · funext i
    change lpRestrictBetween h (u.2 i)=_
    rw [hder,lpRestrictBetween_toLp]
lemma restrict_h1 (h : Ω⊆B) {u : Ambient B} (hu : u∈closure (SmoothJets B)) :
    ambientRestrict h u∈closure (SmoothJets Ω) := by
  exact (show MapsTo (ambientRestrict h) (SmoothJets B) (SmoothJets Ω) from
    fun _ hu => restrict_smoothJet h hu).closure (ambientRestrict h).continuous hu
def h1Restrict (h : Ω⊆B) (u : H1 B) : H1 Ω := ⟨ambientRestrict h u.val,restrict_h1 h u.property⟩
def lpExtendBetween (hΩ : MeasurableSet Ω) :
    Lp V 2 (volume.restrict Ω) →L[ℝ] Lp V 2 (volume.restrict B) :=
  (lpRestrictCLM volume B).comp (lpZeroExtendCLM volume Ω hΩ)
lemma lpExtendBetween_coe (hΩ : MeasurableSet Ω) (f : Lp V 2 (volume.restrict Ω)) :
    (lpExtendBetween (B := B) hΩ f : X → V)=ᵐ[volume.restrict B] Ω.indicator f :=
  (lpRestrict_coe volume B _).trans (ae_restrict_of_ae (lpZeroExtend_coe volume Ω hΩ f))
lemma lpExtendBetween_toLp (hΩ : MeasurableSet Ω) (f : X → V) (hf : MemLp f 2 (volume.restrict Ω))
    (hg : MemLp f 2 (volume.restrict B)) (hs : tsupport f⊆Ω) :
    lpExtendBetween hΩ (hf.toLp f)=hg.toLp f := by
  apply Lp.ext
  have hval : ∀ᵐ x ∂(volume : Measure X), x∈Ω → hf.toLp f x=f x := (ae_restrict_iff' hΩ).mp hf.coeFn_toLp
  filter_upwards [lpExtendBetween_coe (B := B) hΩ (hf.toLp f),
    ae_restrict_of_ae hval,hg.coeFn_toLp] with x h1 h2 h3
  rw [h1,h3]
  by_cases hx : x∈Ω
  · rw [indicator_of_mem hx,h2 hx]
  · rw [indicator_of_notMem hx,image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))]
def ambientExtend (hΩ : MeasurableSet Ω) : Ambient Ω →L[ℝ] Ambient B :=
  (lpExtendBetween hΩ).prodMap (ContinuousLinearMap.pi
    (fun i : Fin 3 => (lpExtendBetween hΩ).comp (ContinuousLinearMap.proj i)))
lemma extend_testJet (hΩ : MeasurableSet Ω) (h : Ω⊆B) {u : Ambient Ω} (hu : u∈TestJets Ω) :
    ambientExtend (B := B) hΩ u∈TestJets B := by
  obtain ⟨f,hf,hd,hsm,hc,hs,hval,hder⟩ := hu
  have hdf (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (coordDeriv f i) :=
    (hsm.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hcd (i : Fin 3) : HasCompactSupport (coordDeriv f i) := hc.fderiv_apply ℝ _
  have hsd (i : Fin 3) : tsupport (coordDeriv f i)⊆Ω :=
    (tsupport_fderiv_apply_subset ℝ (coordVector i)).trans hs
  have hfg : MemLp f 2 (volume.restrict B) := (hsm.continuous.memLp_of_hasCompactSupport hc).restrict B
  have hdg (i : Fin 3) : MemLp (coordDeriv f i) 2 (volume.restrict B) :=
    ((hdf i).continuous.memLp_of_hasCompactSupport (hcd i)).restrict B
  refine ⟨f,hfg,hdg,hsm,hc,hs.trans h,?_,?_⟩
  · change lpExtendBetween hΩ u.1=_
    rw [hval,lpExtendBetween_toLp hΩ f hf hfg hs]
  · funext i
    change lpExtendBetween hΩ (u.2 i)=_
    rw [hder,lpExtendBetween_toLp hΩ _ (hd i) (hdg i) (hsd i)]
lemma extend_h10 (hΩ : MeasurableSet Ω) (h : Ω⊆B) {u : Ambient Ω} (hu : u∈closure (TestJets Ω)) :
    ambientExtend (B := B) hΩ u∈closure (TestJets B) := by
  exact (show MapsTo (ambientExtend (B := B) hΩ) (TestJets Ω) (TestJets B) from
    fun _ hu => extend_testJet hΩ h hu).closure (ambientExtend hΩ).continuous hu
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω B : Set X}
def gradient (u : Ambient Ω) (x : X) : Fin 3 → V := fun i => u.2 i x
def elasticDensity (lam mu : ℝ) (P Q : Fin 3 → V) : ℝ :=
  lam*(∑ i, P i i)*(∑ i, Q i i)+2*mu*∑ i, ∑ j,
    ((P j i+P i j)/2)*((Q j i+Q i j)/2)
def ambientDensity (lam mu : X → ℝ) (u v : Ambient Ω) (x : X) : ℝ :=
  elasticDensity (lam x) (mu x) (gradient u x) (gradient v x)
def ambientEnergy (lam mu : X → ℝ) (u v : Ambient Ω) : ℝ :=
  ∫ x, ambientDensity lam mu u v x ∂(volume.restrict Ω)
@[simp] lemma elasticDensity_zero_right (a b : ℝ) (P : Fin 3 → V) :
    elasticDensity a b P 0=0 := by simp [elasticDensity]
lemma entry_memLp (u : Ambient Ω) (i j : Fin 3) :
    MemLp (fun x => u.2 j x i) 2 (volume.restrict Ω) :=
  (EuclideanSpace.proj i : V →L[ℝ] ℝ).comp_memLp (u.2 j)
lemma BoundedCoefficient.mul_memLp_fun {a f : X → ℝ} (ha : BoundedCoefficient Ω a)
    (hf : MemLp f 2 (volume.restrict Ω)) : MemLp (fun x => a x*f x) 2 (volume.restrict Ω) := by
  obtain ⟨C,hC⟩ := ha.bound
  apply hf.of_le_mul (c := C) (ha.measurable.mul hf.aestronglyMeasurable)
  filter_upwards [hC] with x hx
  simpa only [Pi.mul_apply,norm_mul] using mul_le_mul_of_nonneg_right hx (norm_nonneg (f x))
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
namespace Elasticity
variable {Ω B : Set X}
def h1Extend (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 Ω) (hu : HasZeroTrace Ω u) : H1 B :=
  ⟨ambientExtend hΩ u.val,h10Submodule_le B (extend_h10 hΩ h hu)⟩
def gluedH1 (hΩ : MeasurableSet Ω) (h : Ω⊆B) (u : H1 B) (v : H1 Ω)
    (ht : SameTrace Ω v (h1Restrict h u)) : H1 B :=
  ⟨u.val+ambientExtend hΩ (v.val-ambientRestrict h u.val),
    (h1Submodule B).add_mem u.property (h10Submodule_le B (extend_h10 hΩ h ht))⟩
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}
def ambientScalar (Ω : Set X) (k : Option (Fin 3)) (i : Fin 3) :
    Ambient Ω →L[ℝ] ScalarL2 Ω := (jetScalar Ω k i).comp (jetEquiv Ω).symm.toContinuousLinearMap

def weakDerivativePair (Ω : Set X) (g : SchwartzMap X ℝ) (i j : Fin 3) : Ambient Ω →L[ℝ] ℝ :=
  ((innerSL ℝ (schwartzR Ω (ElasticityKorn.d (coordVector j) g))).comp (ambientScalar Ω none i)) +
  ((innerSL ℝ (schwartzR Ω g)).comp (ambientScalar Ω (some j) i))
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X}
def testField (g : SchwartzMap X ℝ) (i : Fin 3) : X → V := fun x => g x • coordVector i
lemma testField_smooth (g : SchwartzMap X ℝ) (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (testField g i) :=
  (g.smooth _).smul contDiff_const
lemma testField_compact (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i : Fin 3) :
    HasCompactSupport (testField g i) := hc.comp_left (g := fun a : ℝ => a • coordVector i) (zero_smul ..)
lemma testField_support (g : SchwartzMap X ℝ) (i : Fin 3) :
    tsupport (testField g i) ⊆ tsupport (g : X → ℝ) :=
  tsupport_comp_subset (g := fun a : ℝ => a • coordVector i) (zero_smul ..) _
lemma testField_memLp (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i : Fin 3) :
    MemLp (testField g i) 2 (volume.restrict Ω) :=
  ((testField_smooth g i).continuous.memLp_of_hasCompactSupport (testField_compact g hc i)).restrict Ω
lemma testField_deriv_memLp (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i j : Fin 3) :
    MemLp (coordDeriv (testField g i) j) 2 (volume.restrict Ω) :=
  (((testField_smooth g i).continuous_fderiv (by simp)).clm_apply continuous_const
    |>.memLp_of_hasCompactSupport ((testField_compact g hc i).fderiv_apply ℝ (coordVector j))).restrict Ω
 def testFieldJet (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ)) (i : Fin 3) : Ambient Ω :=
  ((testField_memLp g hc i).toLp _,fun j => (testField_deriv_memLp g hc i j).toLp _)
lemma testFieldJet_mem (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) : testFieldJet (Ω := Ω) g hc i∈TestJets Ω := by
  refine ⟨testField g i,testField_memLp g hc i,testField_deriv_memLp g hc i,testField_smooth g i,testField_compact g hc i,
    (testField_support g i).trans hs,rfl,rfl⟩
def testH1 (g : SchwartzMap X ℝ) (hc : HasCompactSupport (g : X → ℝ))
    (hs : tsupport (g : X → ℝ)⊆Ω) (i : Fin 3) : H1 Ω :=
  ⟨testFieldJet g hc i,h10Submodule_le Ω (subset_closure (testFieldJet_mem g hc hs i))⟩
end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryData
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity

/-! Complex boundary tests use only the real physical DN map. The following
is derived from four real identities; no equality of an augmented or assumed
complex DN map is introduced. -/
open Set
variable {Ω : Set X}

abbrev ComplexTrial (Ω : Set X) := H1Hilbert Ω × H1Hilbert Ω

def complexTrialSize (u : ComplexTrial Ω) : ℝ := ‖u.1‖+‖u.2‖

def complexTrialEnergy (l m : X → ℝ) (u v : ComplexTrial Ω) : ℂ :=
  (energy Ω l m (h1Equiv Ω u.1) (h1Equiv Ω v.1):ℂ)+
  (energy Ω l m (h1Equiv Ω u.2) (h1Equiv Ω v.2):ℂ)+
  Complex.I*((energy Ω l m (h1Equiv Ω u.2) (h1Equiv Ω v.1):ℂ)-
    (energy Ω l m (h1Equiv Ω u.1) (h1Equiv Ω v.2):ℂ))

def complexResidualSize {l m : X → ℝ} (hl : BoundedCoefficient Ω l)
    (hm : BoundedCoefficient Ω m) (u : ComplexTrial Ω) : ℝ :=
  ‖physicalResidual hl hm u.1‖+‖physicalResidual hl hm u.2‖

end Elasticity
namespace Elasticity
/-! Genuine strong-to-variational residual estimate for boundary trial fields.
All pairings are on the actual physical H10 space, extended by its defining
density, not a separately assumed boundary test class. -/
open MeasureTheory Set
open scoped BigOperators
variable {Ω : Set X} {lam mu : X → ℝ}

def jetStress (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : JetH Ω) (i j : Fin 3) : ScalarL2 Ω :=
  (if i=j then hl.mulL (jetDiv Ω u) else 0) + (2 : ℝ) • hm.mulL (jetStrain Ω i j u)

/-- The actual L2 force pairing, with no regularity required of the test. -/
def boundaryForcePair (F : Fin 3 → ScalarL2 Ω) : JetH Ω →L[ℝ] ℝ :=
  ∑ i, (innerSL ℝ (F i)).comp (jetScalar Ω none i)

end Elasticity
namespace Elasticity
/-! Actual smooth physical displacements give the exact H1 trial objects used
 by the physical DN map. This is a constructor, not a trace assumption. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

def smoothTrial (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) : H1Hilbert Ω :=
  (h1Equiv Ω).symm ⟨(hf.toLp f,fun j => (hd j).toLp _),
    subset_closure ⟨f,hf,hd,hs,rfl,rfl⟩⟩

@[simp] lemma smoothTrial_value (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) :
    (smoothTrial f hs hf hd).val none=hf.toLp f := rfl

@[simp] lemma smoothTrial_deriv (f : X → V) (hs : ContDiff ℝ (⊤ : ℕ∞) f)
    (hf : MemLp f 2 (volume.restrict Ω))
    (hd : ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω)) (j : Fin 3) :
    (smoothTrial f hs hf hd).val (some j)=(hd j).toLp _ := rfl

lemma smooth_compact_coordDeriv {f : X → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (j : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (coordDeriv f j) ∧ HasCompactSupport (coordDeriv f j) := by
  exact ⟨(hf.fderiv_right (by simp)).clm_apply contDiff_const,hc.fderiv_apply ℝ _⟩

lemma smooth_compact_memLp {f : X → V} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    MemLp f 2 (volume.restrict Ω) ∧ ∀ j, MemLp (coordDeriv f j) 2 (volume.restrict Ω) := by
  refine ⟨(hf.continuous.memLp_of_hasCompactSupport hc).restrict _,fun j => ?_⟩
  obtain ⟨hs,hc'⟩ := smooth_compact_coordDeriv hf hc j
  exact (hs.continuous.memLp_of_hasCompactSupport hc').restrict _

end Elasticity
namespace Elasticity
/-! Exact agreement of the variational trial energy with classical smooth
physical fields and their literal derivatives. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

/-- Projection of a complex physical displacement to an actual real trial
field. The map `w` will be real or imaginary part. -/
def realField (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ) (x : X) : V :=
  WithLp.toLp 2 (fun i => w (u i x))

lemma smooth_realField (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) : ContDiff ℝ (⊤ : ℕ∞) (realField w u) := by
  exact PiLp.contDiff_toLp.comp (contDiff_pi.mpr (fun i => w.contDiff.comp (hu i)))

lemma realField_support (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ) {K : Set X}
    (hu : ∀ i, Function.support (u i)⊆K) : Function.support (realField w u)⊆K := by
  intro x hx
  by_contra hn
  apply hx
  ext i
  have hz : u i x=0 := Function.notMem_support.mp (fun h => hn (hu i h))
  simp [realField,hz]

lemma compact_realField (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ) {K : Set X}
    (hK : IsCompact K) (hu : ∀ i, Function.support (u i)⊆K) : HasCompactSupport (realField w u) := by
  exact hK.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (realField_support w u hu) hK.isClosed)

end Elasticity
/-! Squared physical H10-dual residual estimates in terms of the genuine
strong-force mass. This is the bridge from chart quasimodes to the DN map. -/
/-! Exact H1 masses of the physical complex trial projections, and bounds by
literal scalar component derivatives. -/
namespace Elasticity
/-! Complex geometric displacements as genuine pairs of real H1 trials. -/
open Set MeasureTheory
open scoped BigOperators
variable {Ω : Set X}

def projectedTrial (w : ℂ →L[ℝ] ℝ) (u : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) {K : Set X} (hK : IsCompact K)
    (hus : ∀ j, Function.support (u j)⊆K) : H1Hilbert Ω :=
  smoothTrial (realField w u) (smooth_realField w u hu)
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).1
    (smooth_compact_memLp (smooth_realField w u hu) (compact_realField w u hK hus)).2

def complexFieldTrial (u : Fin 3 → X → ℂ)
    (hu : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (u j)) {K : Set X} (hK : IsCompact K)
    (hus : ∀ j, Function.support (u j)⊆K) : ComplexTrial Ω :=
  (projectedTrial Complex.reCLM u hu hK hus,projectedTrial Complex.imCLM u hu hK hus)

def realMatrix (w : ℂ →L[ℝ] ℝ) (P : Fin 3 → Fin 3 → ℂ) : Fin 3 → V :=
  fun j => WithLp.toLp 2 (fun i => w (P i j))

def complexDensity (l m : ℝ) (P Q : Fin 3 → Fin 3 → ℂ) : ℂ :=
  (elasticDensity l m (realMatrix Complex.reCLM P) (realMatrix Complex.reCLM Q):ℂ)+
  (elasticDensity l m (realMatrix Complex.imCLM P) (realMatrix Complex.imCLM Q):ℂ)+
  Complex.I*((elasticDensity l m (realMatrix Complex.imCLM P) (realMatrix Complex.reCLM Q):ℂ)-
    (elasticDensity l m (realMatrix Complex.reCLM P) (realMatrix Complex.imCLM Q):ℂ))

def fieldGradient (u : Fin 3 → X → ℂ) (x : X) (i j : Fin 3) : ℂ :=
  ElasticityBoundaryChainRule.dd (u i) (coordVector j) x

end Elasticity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_BoundaryEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace Elasticity
/-! The complex physical variational density is exactly the Hermitian
contraction of the literal isotropic elasticity tensor. -/
open scoped BigOperators
abbrev CMatrix := Fin 3 → Fin 3 → ℂ

def tensorDensity (a : Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℂ) (P Q : CMatrix) : ℂ :=
  ∑ i, ∑ α, ∑ j, ∑ β, a i α j β*P i α*star (Q j β)

def sesquiDensity (l m : ℂ) (P Q : CMatrix) : ℂ :=
  l*(∑ i, P i i)*star (∑ i, Q i i)+
    (m/2)*∑ i, ∑ j, (P i j+P j i)*star (Q i j+Q j i)

end Elasticity

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Carleman
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

namespace ElasticityPhysicalAlgebra
open ElasticityBessel ElasticityNegativeOrder
abbrev X := ElasticityBessel.X
abbrev Smooth := ElasticityAugmented.Smooth

/-- The genuine embedding of Schwartz functions into the smooth differential algebra. -/
def toSmooth : S →ₗ[ℂ] Smooth where
  toFun f := ⟨f, f.smooth (⊤ : ℕ∞)⟩
  map_add' f g := by apply Subtype.ext; rfl
  map_smul' a f := by apply Subtype.ext; rfl

@[simp] lemma toSmooth_apply (f : S) (x : X) : (toSmooth f : X → ℂ) x = f x := rfl

end ElasticityPhysicalAlgebra

open scoped BigOperators
namespace ElasticityAugmented
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A) (T : Fin 3 → A →ₗ[ℂ] A)

def coeffA (lam m n o : A) (k : Fin 3) : Fin 4 → Fin 4 → A :=
  Fin.cons
    (Fin.cons (2*o*(D k (lam+m)-(lam+m)*n*D k m))
      (fun j => 2*o*(D k (D j m)-2*n*D k m*D j m)))
    (fun i => Fin.cons (if k=i then (lam+m)*n else 0)
      (fun j => (if j=i then n*D k m else 0) + (if k=i then n*D j m else 0)))

def coeffV (lam m n o : A) : Fin 4 → Fin 4 → A :=
  Fin.cons
    (Fin.cons (o*(lap D lam-2*n*(∑ i, D i m*D i lam))) (fun _ => 0))
    (fun i => Fin.cons (n*D i lam) (fun _ => 0))

end ElasticityAugmented

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
open Set MeasureTheory SchwartzMap
open scoped BigOperators SchwartzMap Topology

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Regularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! Actual distributional elliptic regularity dependencies of the physical and
planar weak-limit constructions. No regularity assumption on an L2 unknown is
used in the gain of Sobolev order below. -/
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal

open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
namespace ElasticityDistribution

open ElasticityAugmented TemperedDistribution
abbrev X := ElasticityAugmented.X
abbrev Dist := 𝓢'(X,ℂ)

/-- Smooth temperate coefficients act on actual tempered distributions. -/
def coefficientAlgebra : Subalgebra ℂ Smooth where
  carrier := {a | (a : X → ℂ).HasTemperateGrowth}
  add_mem' ha hb := ha.add hb
  mul_mem' ha hb := ha.mul hb
  zero_mem' := Function.HasTemperateGrowth.zero
  one_mem' := Function.HasTemperateGrowth.const 1
  algebraMap_mem' c := Function.HasTemperateGrowth.const c
abbrev Coeff := coefficientAlgebra

def eval (a : Coeff) : X → ℂ := a.val

@[simp] lemma eval_add (a b : Coeff) : eval (a+b) = eval a+eval b := rfl
@[simp] lemma eval_mul (a b : Coeff) : eval (a*b) = eval a*eval b := rfl
@[simp] lemma eval_one : eval (1 : Coeff) = fun _ => 1 := rfl

open ElasticityAugmented TrivSqZeroExt

end ElasticityDistribution

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap Real ENNReal
open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open scoped SchwartzMap LineDeriv BigOperators
open scoped SchwartzMap LineDeriv Laplacian BigOperators

open MeasureTheory FourierTransform TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian Real ENNReal BigOperators

open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators
open MeasureTheory TemperedDistribution
open scoped SchwartzMap LineDeriv Laplacian BigOperators ENNReal

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Solvability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/-! The Hahn--Banach / Riesz step used by the physical solvability argument.
This proves the functional-analytic implication, rather than postulating
existence of a right inverse. The physical test estimate is proved separately. -/

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal
namespace ElasticityPhysicalDual
open ElasticityBessel ElasticityNegativeOrder
open ElasticityPhysicalAlgebra
abbrev X := ElasticityBessel.X
abbrev H := PiLp 2 (fun _ : Fin 3 => Lp ℂ 2 (volume : Measure X))

end ElasticityPhysicalDual

open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
open scoped SchwartzMap LineDeriv BigOperators
open MeasureTheory Complex SchwartzMap
open scoped BigOperators SchwartzMap LineDeriv
namespace ElasticityDistribution

section

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder
abbrev S := 𝓢(X,ℂ)
def cj (φ : S) : S := φ.postcompCLM Complex.conjCLE.toContinuousLinearMap
@[simp] lemma cj_apply (φ : S) (x : X) : cj φ x = star (φ x) := rfl

open ElasticityAugmented TemperedDistribution

end

open ElasticityPhysicalAlgebra ElasticityPhysicalDual ElasticityNegativeOrder

end ElasticityDistribution

open scoped BigOperators

open MeasureTheory Complex SchwartzMap
open scoped BigOperators FourierTransform SchwartzMap LineDeriv ENNReal

open MeasureTheory TemperedDistribution
open scoped ENNReal SchwartzMap BigOperators

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_TransportAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section CGO
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
def normal (θ : Fin 3 → ℂ) (u : Fin 3 → A) : A := ∑ i, θ i • u i
def direction (θ : Fin 3 → ℂ) (a : A) : A := ∑ i, θ i • D i a
def leadingR (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A) (i : Fin 3) : A :=
  2*m*direction D θ (u i)+direction D θ m*u i+
    θ i • ((lam+m)*b+∑ j, D j m*u j)
def leadingS (θ : Fin 3 → ℂ) (lam m : A) (u : Fin 3 → A) (b : A) : A :=
  2*(lam+m+m)*direction D θ b+2*direction D θ (lam+m)*b+
    4*(∑ i, D i m*direction D θ (u i))+2*(∑ i, direction D θ (D i m)*u i)
def leadingP (θ : Fin 3 → ℂ) (m f : A) : A :=
  2*m*direction D θ f+direction D θ m*f

end CGO
end ElasticityAugmented

end
end
section
noncomputable section
open scoped BigOperators
namespace ElasticityAugmented
section PhysicalRecursion
variable {A : Type*} [CommRing A] [Algebra ℂ A]
variable (D : Fin 3 → Derivation ℂ A A)
abbrev Amplitude (A : Type*) := (Fin 3 → A) × A

def Rpair (lam m : A) : Amplitude A →ₗ[ℂ] (Fin 3 → A) where
  toFun a := R D lam m a.1 a.2
  map_add' a b := by
    funext i
    simp only [R,lap,cm,Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,Finset.sum_add_distrib,mul_add,add_mul]
    ring
  map_smul' c a := by
    funext i
    simp only [R,lap,cm,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Derivation.map_smul]
    simp only [Algebra.smul_def,Fin.sum_univ_three,RingHom.id_apply]
    ring

def divergenceDefect : Amplitude A →ₗ[ℂ] A where
  toFun a := div D a.1-a.2
  map_add' a b := by
    simp only [div,Prod.fst_add,Prod.snd_add,Pi.add_apply,map_add,Finset.sum_add_distrib]
    abel
  map_smul' c a := by
    simp only [div,Prod.smul_fst,Prod.smul_snd,Pi.smul_apply,Derivation.map_smul,Finset.smul_sum,smul_sub,
      RingHom.id_apply]

end PhysicalRecursion
end ElasticityAugmented

end
end
section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace ElasticityAugmented

def restriction (U : Set X) : Smooth →ₐ[ℂ] (U → ℂ) where
  toFun f x := (f : X → ℂ) x
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
abbrev LocalSmooth (U : Set X) := (restriction U).range
def restrictSmooth (U : Set X) : Smooth →ₐ[ℂ] LocalSmooth U := (restriction U).rangeRestrict
lemma restrictSmooth_surjective (U : Set X) : Function.Surjective (restrictSmooth U) :=
  (restriction U).rangeRestrict_surjective
lemma restrictSmooth_eq_iff (U : Set X) (f g : Smooth) :
    restrictSmooth U f=restrictSmooth U g ↔ EqOn (f : X → ℂ) (g : X → ℂ) U := by
  constructor
  · intro h x hx
    exact congrArg (fun v : LocalSmooth U => (v : U → ℂ) ⟨x,hx⟩) h
  · intro h
    apply Subtype.ext
    funext x
    exact h x.property
lemma restrictSmooth_zero_iff (U : Set X) (f : Smooth) :
    restrictSmooth U f=0 ↔ ∀ x∈U,(f : X → ℂ) x=0 := by
  rw [← map_zero (restrictSmooth U),restrictSmooth_eq_iff]
  rfl
lemma restrict_coord_zero {U : Set X} (hU : IsOpen U) (i : Fin 3) (f : Smooth)
    (hf : restrictSmooth U f=0) : restrictSmooth U (coord i f)=0 := by
  apply (restrictSmooth_zero_iff U _).mpr
  intro x hx
  have he : (f : X → ℂ)=ᶠ[𝓝 x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (restrictSmooth_zero_iff U f).mp hf y hy
  rw [coord_apply,he.fderiv_eq]
  simp

def localCoord {U : Set X} (hU : IsOpen U) (i : Fin 3) :
    Derivation ℂ (LocalSmooth U) (LocalSmooth U) :=
  Derivation.liftOfSurjective (restrictSmooth_surjective U) (restrict_coord_zero hU i)
end ElasticityAugmented

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented
open scoped BigOperators

def smoothInv (f : Smooth) (hf : ∀ x, (f : X → ℂ) x≠0) : Smooth :=
  ⟨fun x => ((f : X → ℂ) x)⁻¹,(smooth_coe f).inv hf⟩

def changeP (r : Smooth) (a : Fin 3 → Smooth) : Fin 3 → Smooth := fun i => r*a i
def logarithmicGrad (r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0) : Fin 3 → Smooth :=
  fun i => 2*smoothInv r hr*coord i r
def changeS (k r : Smooth) (hr : ∀ x, (r : X → ℂ) x≠0)
    (a : Fin 3 → Smooth) (b : Smooth) : Smooth :=
  -(1/2 : ℂ) • (k*smoothInv r hr*b+
    ∑ i, logarithmicGrad r hr i*changeP r a i)

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_CGO
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityAugmented
open Set
open scoped BigOperators

def localAmp (U : Set X) (a : Amplitude Smooth) : Amplitude (LocalSmooth U) :=
  ((fun i => restrictSmooth U (a.1 i)),restrictSmooth U a.2)
def CompatibleOn {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (lam m : Smooth)
    (a : Amplitude Smooth) : Prop :=
  normal θ (R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U m) (localAmp U a).1 (localAmp U a).2)=
    leadingP (localCoord hU) θ (restrictSmooth U m)
      (div (localCoord hU) (localAmp U a).1-(localAmp U a).2)

def RecursOn {U : Set X} (hU : IsOpen U) (θ : Fin 3 → ℂ) (lam m : Smooth)
    (a b : Amplitude Smooth) : Prop :=
  leadingR (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m) (localAmp U b).1 (localAmp U b).2=
    -R (localCoord hU) (restrictSmooth U lam) (restrictSmooth U m) (localAmp U a).1 (localAmp U a).2 ∧
  leadingS (localCoord hU) θ (restrictSmooth U lam) (restrictSmooth U m) (localAmp U b).1 (localAmp U b).2=
    -S (localCoord hU) (restrictSmooth U lam) (restrictSmooth U m) (localAmp U a).1 (localAmp U a).2 ∧
  normal θ b.1=-(div coord a.1-a.2)

end ElasticityAugmented

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Recovery
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped BigOperators Matrix

/-! Finite-type uniqueness used in the last step of the elasticity proof.
All spaces and coefficient fields below are actual functions, not axioms. -/
noncomputable section
open Set Filter Module
open scoped BigOperators Topology

namespace ElasticityRecovery
open Module

abbrev X := EuclideanSpace ℝ (Fin 3)

end ElasticityRecovery

end
end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakSolutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory SchwartzMap Set TemperedDistribution
open scoped SchwartzMap LineDeriv
namespace Elasticity
variable {Ω : Set X}
abbrev realTest (g : SchwartzMap X ℝ) : SchwartzMap X ℂ := g.postcompCLM Complex.ofRealCLM
abbrev reTest (g : SchwartzMap X ℂ) : SchwartzMap X ℝ := g.postcompCLM Complex.reCLM
abbrev imTest (g : SchwartzMap X ℂ) : SchwartzMap X ℝ := g.postcompCLM Complex.imCLM
def scalarDistribution (Ω : Set X) : ScalarL2 Ω →L[ℝ] ElasticityDistribution.Dist :=
  ((Lp.toTemperedDistributionCLM ℂ (volume.restrict Ω) 2).restrictScalars ℝ).comp
    (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω))
def h1Distribution (u : H1 Ω) (i : Fin 3) : ElasticityDistribution.Dist :=
  scalarDistribution Ω (ambientScalar Ω none i u.val)
def h1GradientDistribution (u : H1 Ω) (i j : Fin 3) : ElasticityDistribution.Dist :=
  scalarDistribution Ω (ambientScalar Ω (some j) i u.val)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace Elasticity
variable {Ω : Set X} {lam mu : X → ℝ}
def stressFun (lam mu : X → ℝ) (u : Ambient Ω) (i j : Fin 3) (x : X) : ℝ :=
  (if i=j then lam x*(∑ k, u.2 k x k) else 0)+mu x*(u.2 j x i+u.2 i x j)
lemma stress_memLp (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : MemLp (stressFun lam mu u i j) 2 (volume.restrict Ω) := by
  have hd : MemLp (fun x => ∑ k, u.2 k x k) 2 (volume.restrict Ω) :=
    memLp_finsetSum _ (fun k _ => entry_memLp u k k)
  have hs := hm.mul_memLp_fun ((entry_memLp u i j).add (entry_memLp u j i))
  change MemLp (fun x => (if i=j then lam x*(∑ k, u.2 k x k) else 0)+mu x*(u.2 j x i+u.2 i x j)) 2 (volume.restrict Ω)
  by_cases he : i=j
  · subst j
    simp only [ite_true]
    exact (hl.mul_memLp_fun hd).add hs
  · simp only [he,ite_false,zero_add]
    exact hs
 def stressL2 (hl : BoundedCoefficient Ω lam) (hm : BoundedCoefficient Ω mu)
    (u : Ambient Ω) (i j : Fin 3) : ScalarL2 Ω := (stress_memLp hl hm u i j).toLp _
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
def schwartzJet (F : SchwartzMap X V) : Ambient Ω :=
  (F.toLp 2 (volume.restrict Ω),fun j => (∂_{coordVector j} F).toLp 2 (volume.restrict Ω))
lemma schwartzJet_mem (F : SchwartzMap X V) : schwartzJet (Ω := Ω) F∈SmoothJets Ω := by
  refine ⟨F,F.memLp 2 (volume.restrict Ω),fun j => (∂_{coordVector j} F).memLp 2 (volume.restrict Ω),F.smooth _,?_,?_⟩
  · rfl
  · rfl
def schwartzH1 (F : SchwartzMap X V) : H1 Ω := ⟨schwartzJet F,subset_closure (schwartzJet_mem F)⟩
def componentTest (F : SchwartzMap X V) (i : Fin 3) : SchwartzMap X ℝ :=
  F.postcompCLM (EuclideanSpace.proj (𝕜 := ℝ) i)
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set SchwartzMap TemperedDistribution
open scoped BigOperators SchwartzMap LineDeriv
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X}
def realVectorTest (F : Fin 3 → SchwartzMap X ℝ) : SchwartzMap X V :=
  ∑ i, (F i).postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (coordVector i))
def complexRealH1 (F : Fin 3 → SchwartzMap X ℂ) : H1 Ω :=
  schwartzH1 (realVectorTest (fun i => reTest (F i)))
def complexImagH1 (F : Fin 3 → SchwartzMap X ℂ) : H1 Ω :=
  schwartzH1 (realVectorTest (fun i => imTest (F i)))
end Elasticity

end
end
section
noncomputable section
open MeasureTheory Set TemperedDistribution
open scoped BigOperators SchwartzMap
namespace Elasticity
open ElasticityDistribution
variable {Ω : Set X} {lam mu : X → ℝ}
def scalarGlobal (hs : MeasurableSet Ω) (f : ScalarL2 Ω) : Lp ℂ 2 (volume : Measure X) :=
  lpZeroExtendCLM volume Ω hs (Complex.ofRealCLM.compLpL 2 (volume.restrict Ω) f)
 def h1Global (hs : MeasurableSet Ω) (u : H1 Ω) : ElasticityPhysicalDual.H :=
  WithLp.toLp 2 (fun i => scalarGlobal hs (ambientScalar Ω none i u.val))
end Elasticity

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Transfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set MeasureTheory
open scoped BigOperators SchwartzMap
namespace ElasticityCGO
open ElasticityAugmented
open ElasticityPhysicalAlgebra (toSmooth toSmooth_apply )
abbrev S := SchwartzMap X ℂ

end ElasticityCGO

end
end
section
noncomputable section
open MeasureTheory Set
open scoped BigOperators FourierTransform

namespace ElasticityCarleman

abbrev X := EuclideanSpace ℝ (Fin 3)
abbrev Direction := Fin 3 → ℂ

/-- The real-linear complex phase functional. -/
def phaseCLM (θ : Direction) : X →L[ℝ] ℂ :=
  ∑ i, θ i • (Complex.ofRealCLM.comp (EuclideanSpace.proj i))

end ElasticityCarleman

end
end

end OAI
end


