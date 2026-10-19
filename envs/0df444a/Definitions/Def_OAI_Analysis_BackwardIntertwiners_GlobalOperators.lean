-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_GlobalOperators
-- name    : OAI_Analysis_BackwardIntertwiners_GlobalOperators
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T02:02:52.598423+00:00
-- url     : https://prove2.me/theorems/cf50aa79-d8fc-48bd-a0a0-15b55e70dc11
-- title:
--   Decomposable forward and backward operators on $L^2(\mathbb{Z}_2;\ell^2(\mathbb{Z}))$
-- statement:
--   This file constructs the global Hilbert space of the model and the two operators whose interplay produces a transitive commutant. Let $\mathcal{F}=\ell^2(\mathbb{Z})$ be the Hilbert space of square-summable two-sided complex sequences with standard basis $(e_j)_{j\in\mathbb{Z}}$.
--
--   **General decomposable operators.** Let $(X,\mu)$ be a measure space and $L^2(\mu;\mathcal{F})$ the space of (almost-everywhere classes of) square-integrable $\mathcal{F}$-valued functions.
--
--   1. **Scalar multipliers.** For $g\in L^\infty(\mu;\mathbb{C})$, $(M_gf)(x)=g(x)\,f(x)$; this is a bounded operator on $L^2(\mu;\mathcal{F})$ with $\|M_g\|\le\|g\|_\infty$.
--   2. **Field operators.** Let $x\mapsto A(x)$ be a family of bounded operators on $\mathcal{F}$ with $\|A(x)\|\le C$ for all $x$, for some $C\ge0$, such that $x\mapsto A(x)f(x)$ is almost everywhere strongly measurable whenever $f$ is. The decomposable operator
--   $$(\mathcal{A}f)(x)=A(x)\,f(x)$$
--   is a bounded operator on $L^2(\mu;\mathcal{F})$ with $\|\mathcal{A}f\|\le C\|f\|$. A field of weighted permutations $(W_xv)_j=a(x,e(j))\,v_{e(j)}$, with a fixed bijection $e$ of $\mathbb{Z}$, $|a(x,j)|\le C$ and $x\mapsto a(x,j)$ measurable for each $j$, satisfies this measurability hypothesis.
--   3. **Invariance.** A subspace $\mathcal{L}$ of a complex normed space is invariant under an operator $T$ if $Tv\in\mathcal{L}$ for every $v\in\mathcal{L}$.
--
--   **The model.** The base is the ring $\mathbb{Z}_2$ of 2-adic integers with its completed normalized Haar measure $\mu$. For $x\in\mathbb{Z}_2$ and $j\in\mathbb{Z}$, $\beta_x(j)\in(0,e^{-10}]$ are the explicit weight ratios and $c_x(j)\in[0,1]$ the backward coefficients, both determined by the residues of $x$ modulo powers of $2$ and measurable in $x$.
--
--   4. **Global Hilbert space.** $\mathcal{H}=L^2(\mathbb{Z}_2,\mu;\ell^2(\mathbb{Z}))$.
--   5. **Fiber operators.** $(S_xv)_j=\beta_x(j-1)\,v_{j-1}$ with $\|S_x\|\le e^{-10}$, and $(V_xv)_j=c_x(j+1)\,v_{j+1}$ with $\|V_x\|\le1$.
--   6. **Odometer and its inverse.** $x\mapsto x+1$ and $x\mapsto x-1$ are mutually inverse measurable bijections of the base, and $x\mapsto x-1$ preserves $\mu$.
--   7. **Forward and backward operators.** $S$ is the decomposable operator with fibers $S_x$, and $V$ is the decomposable operator with fibers $V_x$ followed by the unitary $f\mapsto f(\,\cdot\,-1)$:
--   $$(Sf)(x)_j=\beta_x(j-1)\,f(x)_{j-1},\qquad (Vf)(x)_j=c_{x-1}(j+1)\,f(x-1)_{j+1}.$$
--   8. **Constant basis vectors.** $\mathbf{e}_j\in\mathcal{H}$ is the constant function $x\mapsto e_j$.
--
--   The forward operator $S$ is the nonzero operator with $\|S^n\|^{1/n}\to0$ and transitive commutant that is afterwards transported to an arbitrary separable infinite-dimensional Hilbert space: it satisfies $SV=VS$ and $\|S^n\|\le e^{-10\lfloor(n+1)^2/4\rfloor}$, and the only closed subspaces of $\mathcal{H}$ invariant under $S$, $V$ and all scalar multipliers $M_g$ are $\{0\}$ and $\mathcal{H}$.
--
--   **Formalization Note** The names are `scalarMultiplier`, `fieldOperator` (built from `fieldVector` via `MemLp.toLp`), `GlobalHilbert := Lp Fiber 2 baseMeasure`, `OperatorInvariant`, `forwardFiber`, `backwardFiber`, `forwardOperator`, `inverseOdometer`, `odometerMeasurableEquiv`, `backwardFieldOperator`, `backwardOperator` and `constantBasis`. The field operator takes the bound $C$ and the measurability hypothesis as arguments. `backwardOperator` is `Lp.compMeasurePreservingₗᵢ` for `inverseOdometer` composed after `backwardFieldOperator`. Elements of `Lp` are almost-everywhere classes, so formulas such as $(Sf)(x)=S_xf(x)$ hold for almost every $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/GlobalOperators.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/GlobalOperators.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BackwardIntertwiners mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BackwardIntertwiners
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvexEnvelope
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ConvolutionBounds
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_CoefficientSupport
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_WeightSeparation
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberTails
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_ExplicitWeights
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_HaarBase
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
import Definitions.Def_OAI_Analysis_BackwardIntertwiners_BackwardWeights

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

section Fields
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

lemma weightedPermutation_stronglyMeasurable (e : ℤ ≃ ℤ) (a : X → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x j, ‖a x j‖ ≤ C)
    (hm : ∀ j, Measurable (fun x => a x j))
    {f : X → Fiber} (hf : StronglyMeasurable f) :
    StronglyMeasurable (fun x => fiberWeightedPermutation e (a x) C hC (ha x) (f x)) := by
  apply fiberCoordinates_stronglyMeasurable
  intro j
  exact (hm (e j)).mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 2 (e j)).continuous.comp_stronglyMeasurable hf).measurable)

lemma weightedPermutation_aestronglyMeasurable (e : ℤ ≃ ℤ) (a : X → ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C) (ha : ∀ x j, ‖a x j‖ ≤ C)
    (hm : ∀ j, Measurable (fun x => a x j))
    {f : X → Fiber} (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (fun x => fiberWeightedPermutation e (a x) C hC (ha x) (f x)) μ := by
  apply (weightedPermutation_stronglyMeasurable e a C hC ha hm hf.stronglyMeasurable_mk).aestronglyMeasurable.congr
  filter_upwards [hf.ae_eq_mk] with x hx
  rw [hx]

def scalarMultiplier (g : Lp ℂ ∞ μ) : Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  LinearMap.mkContinuous
    { toFun := fun f => g • f
      map_add' := Lp.add_smul g
      map_smul' := fun c f => (Lp.smul_comm c g f).symm }
    ‖g‖ (Lp.norm_smul_le g)

def fieldVector (A : X → Fiber →L[ℂ] Fiber) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : Lp Fiber 2 μ :=
  ((Lp.memLp f).of_le_mul (hm f (Lp.aestronglyMeasurable f))
    (Filter.Eventually.of_forall fun x =>
      (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _)))).toLp _

lemma fieldVector_ae (A : X → Fiber →L[ℂ] Fiber) (C : ℝ)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : fieldVector A C hA hm f =ᵐ[μ] fun x => A x (f x) :=
  MemLp.coeFn_toLp _

lemma fieldVector_norm (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ)
    (f : Lp Fiber 2 μ) : ‖fieldVector A C hA hm f‖ ≤ C*‖f‖ := by
  calc
    _ ≤ ‖(C:ℂ) • f‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [fieldVector_ae A C hA hm f, Lp.coeFn_smul (C:ℂ) f] with x hx hs
      rw [hx, hs, Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]
      exact (A x).le_opNorm (f x) |>.trans (mul_le_mul_of_nonneg_right (hA x) (norm_nonneg _))
    _ = C*‖f‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]

def fieldOperator (A : X → Fiber →L[ℂ] Fiber) (C : ℝ) (hC : 0 ≤ C)
    (hA : ∀ x, ‖A x‖ ≤ C)
    (hm : ∀ f : X → Fiber, AEStronglyMeasurable f μ → AEStronglyMeasurable (fun x => A x (f x)) μ) :
    Lp Fiber 2 μ →L[ℂ] Lp Fiber 2 μ :=
  LinearMap.mkContinuous
    { toFun := fieldVector A C hA hm
      map_add' := by
        intro f g
        apply Lp.ext
        filter_upwards [fieldVector_ae A C hA hm (f+g), fieldVector_ae A C hA hm f,
          fieldVector_ae A C hA hm g, Lp.coeFn_add f g,
          Lp.coeFn_add (fieldVector A C hA hm f) (fieldVector A C hA hm g)] with x h₁ h₂ h₃ h₄ h₅
        simp only [h₁,h₂,h₃,h₄,h₅,Pi.add_apply,map_add]
      map_smul' := by
        intro c f
        apply Lp.ext
        filter_upwards [fieldVector_ae A C hA hm (c • f), fieldVector_ae A C hA hm f,
          Lp.coeFn_smul c f, Lp.coeFn_smul c (fieldVector A C hA hm f)] with x h₁ h₂ h₃ h₄
        simp only [RingHom.id_apply, h₁,h₂,h₃,h₄,Pi.smul_apply,map_smul] }
    C (fieldVector_norm A C hC hA hm)

end Fields

abbrev GlobalHilbert := Lp Fiber 2 baseMeasure

def OperatorInvariant {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (L : Submodule ℂ H) (T : H →L[ℂ] H) : Prop := ∀ v ∈ L, T v ∈ L

def forwardFiber (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberWeightedPermutation (Equiv.subRight 1) (fun j => (explicitBeta x j:ℂ))
    (Real.exp (-10)) (Real.exp_pos _).le
    (fun j => by simpa only [Complex.norm_real, Real.norm_of_nonneg (explicitBeta_pos x j).le] using explicitBeta_le x j)
def backwardFiber (x : Base) : Fiber →L[ℂ] Fiber :=
  fiberWeightedPermutation (Equiv.addRight 1) (fun j => (backwardCoeff x j:ℂ)) 1 (by norm_num)
    (fun j => by simpa only [Complex.norm_real, Real.norm_of_nonneg (backwardCoeff_bounds x j).1] using (backwardCoeff_bounds x j).2)
@[simp] lemma forwardFiber_apply (x : Base) (v : Fiber) (j : ℤ) :
    forwardFiber x v j = (explicitBeta x (j-1):ℂ) * v (j-1) := rfl
@[simp] lemma backwardFiber_apply (x : Base) (v : Fiber) (j : ℤ) :
    backwardFiber x v j = (backwardCoeff x (j+1):ℂ) * v (j+1) := rfl
lemma forwardFiber_norm_le (x : Base) : ‖forwardFiber x‖ ≤ Real.exp (-10) :=
  fiberWeightedPermutation_norm_le _ _ _ _ _
lemma backwardFiber_norm_le (x : Base) : ‖backwardFiber x‖ ≤ 1 :=
  fiberWeightedPermutation_norm_le _ _ _ _ _
lemma forwardFiber_aestronglyMeasurable (f : Base → Fiber) (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => forwardFiber x (f x)) baseMeasure := by
  apply weightedPermutation_aestronglyMeasurable
  · exact fun j => Complex.measurable_ofReal.comp (measurable_explicitBeta j)
  · exact hf
lemma backwardFiber_aestronglyMeasurable (f : Base → Fiber) (hf : AEStronglyMeasurable f baseMeasure) :
    AEStronglyMeasurable (fun x => backwardFiber x (f x)) baseMeasure := by
  apply weightedPermutation_aestronglyMeasurable
  · exact fun j => Complex.measurable_ofReal.comp (measurable_backwardCoeff j)
  · exact hf

def forwardOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator forwardFiber (Real.exp (-10)) (Real.exp_pos _).le
    forwardFiber_norm_le forwardFiber_aestronglyMeasurable
def inverseOdometer (x : Base) : Base := (show PadicInt 2 from x)-1
@[simp] lemma inverseOdometer_odometer (x : Base) : inverseOdometer (odometer x) = x := by
  change ((show PadicInt 2 from x)+1)-1 = _
  exact add_sub_cancel_right _ _
@[simp] lemma odometer_inverseOdometer (x : Base) : odometer (inverseOdometer x) = x := by
  change ((show PadicInt 2 from x)-1)+1 = _
  exact sub_add_cancel _ _
lemma inverseOdometer_preserving : MeasurePreserving inverseOdometer baseMeasure baseMeasure := by
  have hh := measurePreserving_completion (α := PadicInt 2) (measurePreserving_add_right baseHaar (-1))
  have he : inverseOdometer = (show Base → Base from fun x : PadicInt 2 => x + (-1)) := by
    funext x
    exact @sub_eq_add_neg (PadicInt 2) _ (show PadicInt 2 from x) 1
  rw [he]
  exact hh

def odometerMeasurableEquiv : Base ≃ᵐ Base where
  toFun := odometer
  invFun := inverseOdometer
  left_inv := inverseOdometer_odometer
  right_inv := odometer_inverseOdometer
  measurable_toFun := odometer_ergodic.measurable
  measurable_invFun := inverseOdometer_preserving.measurable

def backwardFieldOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  fieldOperator backwardFiber 1 (by norm_num) backwardFiber_norm_le backwardFiber_aestronglyMeasurable

def backwardOperator : GlobalHilbert →L[ℂ] GlobalHilbert :=
  (Lp.compMeasurePreservingₗᵢ ℂ inverseOdometer inverseOdometer_preserving).toContinuousLinearMap.comp backwardFieldOperator

def constantBasis (j : ℤ) : GlobalHilbert := Lp.const 2 baseMeasure (lp.single 2 j (1:ℂ))
end
end BackwardIntertwiners

end OAI


