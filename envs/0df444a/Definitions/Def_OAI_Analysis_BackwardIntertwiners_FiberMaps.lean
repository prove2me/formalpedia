-- Prove2me | Definitions.Def_OAI_Analysis_BackwardIntertwiners_FiberMaps
-- name    : OAI_Analysis_BackwardIntertwiners_FiberMaps
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-18T01:59:49.746204+00:00
-- url     : https://prove2.me/theorems/ce791867-f50f-49a6-8ad1-d3f01032662b
-- title:
--   Weighted permutation operators and power costs on $\ell^2(\mathbb{Z})$
-- statement:
--   This file provides the bounded operators on the fiber space $\mathcal{F}=\ell^2(\mathbb{Z})$ (square-summable two-sided complex sequences, with standard basis $(e_j)_{j\in\mathbb{Z}}$) from which the model operators are assembled, together with two integer-valued cost functions.
--
--   1. **Coordinate distance and power cost.** For $j\in\mathbb{Z}$ and $n\in\mathbb{N}$,
--   $$d(j)=\max(j+1,\,-j),\qquad \kappa(n)=\Bigl\lfloor\frac{(n+1)^2}{4}\Bigr\rfloor.$$
--   So $d(j)=j+1$ for $j\ge0$ and $d(j)=-j$ for $j<0$; in particular $d(j)\ge1$.
--   2. **Reindexing.** For a bijection $e:\mathbb{Z}\to\mathbb{Z}$, $R_e v=v\circ e$, i.e. $(R_ev)_j=v_{e(j)}$. It is a linear isometric isomorphism of $\mathcal{F}$ onto itself with inverse $R_{e^{-1}}$.
--   3. **Diagonal multiplier.** For $a:\mathbb{Z}\to\mathbb{C}$ and a constant $C\ge0$ with $|a_j|\le C$ for all $j$, $(M_av)_j=a_j\,v_j$; it is a bounded linear operator with $\|M_av\|\le C\|v\|$.
--   4. **Weighted permutation.** With $e,a,C$ as above, $W_{e,a}=R_e\circ M_a$, that is
--   $$(W_{e,a}v)_j=a_{e(j)}\,v_{e(j)}\qquad(j\in\mathbb{Z}),$$
--   and its operator norm satisfies $\|W_{e,a}\|\le C$.
--   5. **Measurability criterion.** If $X$ is a measurable space and $f:X\to\mathcal{F}$ has measurable coordinates $x\mapsto f(x)_n$ for every $n\in\mathbb{Z}$, then $f$ is strongly measurable.
--
--   With $e(j)=j-1$ the weighted permutation is the forward weighted shift $(W v)_j=a_{j-1}v_{j-1}$, i.e. $e_j\mapsto a_j e_{j+1}$, and with $e(j)=j+1$ it is a backward weighted shift; these are the fiber operators of the model, and the measurability criterion lets fields of them act on vector-valued $L^2$ functions. The cost functions control powers of the forward shift: for every $j\in\mathbb{Z}$ and $n\in\mathbb{N}$ one has $\kappa(n)\le\sum_{r=0}^{n-1}d(j+r)$, so coefficients bounded by $e^{-10\,d(j)}$ give products of $n$ consecutive coefficients at most $e^{-10\,\kappa(n)}$, a quadratic-exponential decay.
--
--   **Formalization Note** The names are `coordinateDistance`, `powerCost` (natural-number division, which is the floor), `fiberReindex` (a linear isometry equivalence built from `fiberReindexVector`), `fiberMultiplier` (built from `fiberMultiplierVector`), `fiberWeightedPermutation` and `fiberCoordinates_stronglyMeasurable`. The multiplier and the weighted permutation take $C$, the proof of $0\le C$ and the coefficient bound as explicit arguments. The inequality between $\kappa$ and $d$ is a separate result.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BackwardIntertwiners/FiberMaps.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BackwardIntertwiners/FiberMaps.lean by skeleton subtraction
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

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

def coordinateDistance (j : ℤ) : ℤ := max (j+1) (-j)
def powerCost (n : ℕ) : ℕ := (n+1)^2/4

def fiberReindexVector (e : ℤ ≃ ℤ) (v : Fiber) : Fiber :=
  ⟨fun j => v (e j), by
    apply memℓp_gen
    exact ((lp.memℓp v).summable (by norm_num)).comp_injective e.injective⟩

lemma fiberReindex_norm (e : ℤ ≃ ℤ) (v : Fiber) : ‖fiberReindexVector e v‖ = ‖v‖ := by
  have he : ‖fiberReindexVector e v‖^2 = ‖v‖^2 := by
    have h₁ := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) (fiberReindexVector e v)
    have h₂ := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) v
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h₁ h₂
    rw [h₁, h₂]
    exact e.tsum_eq (fun j => ‖v j‖^2)
  nlinarith [norm_nonneg (fiberReindexVector e v), norm_nonneg v]

def fiberReindex (e : ℤ ≃ ℤ) : Fiber ≃ₗᵢ[ℂ] Fiber where
  toFun := fiberReindexVector e
  invFun := fiberReindexVector e.symm
  left_inv v := by ext j; exact congrArg v (e.apply_symm_apply j)
  right_inv v := by ext j; exact congrArg v (e.symm_apply_apply j)
  map_add' v z := by ext j; rfl
  map_smul' c v := by ext j; rfl
  norm_map' := fiberReindex_norm e

@[simp] lemma fiberReindex_apply (e : ℤ ≃ ℤ) (v : Fiber) (j : ℤ) :
    (fiberReindex e v) j = v (e j) := rfl

lemma fiberMultiplier_mem {a : ℤ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) (v : Fiber) : Memℓp (fun j => a j*v j) 2 := by
  apply ((lp.memℓp v).const_smul (C:ℂ)).mono'
  intro j
  simp only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC, norm_mul]
  exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)

def fiberMultiplierVector (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C)
    (v : Fiber) : Fiber := ⟨fun j => a j*v j, fiberMultiplier_mem hC ha v⟩

lemma fiberMultiplierVector_bound (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C)
    (v : Fiber) : ‖fiberMultiplierVector a C hC ha v‖ ≤ C*‖v‖ := by
  calc
    _ ≤ ‖(C:ℂ) • v‖ := by
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      change ‖a j*v j‖ ≤ ‖(C:ℂ)*v j‖
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)
    _ = C*‖v‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]

def fiberMultiplier (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C) :
    Fiber →L[ℂ] Fiber :=
  LinearMap.mkContinuous
    { toFun := fiberMultiplierVector a C hC ha
      map_add' := by intro v z; ext j; exact mul_add _ _ _
      map_smul' := by intro c v; ext j; exact mul_left_comm _ _ _ }
    C (fiberMultiplierVector_bound a C hC ha)

@[simp] lemma fiberMultiplier_apply (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C)
    (v : Fiber) (j : ℤ) : fiberMultiplier a C hC ha v j = a j*v j := rfl

def fiberWeightedPermutation (e : ℤ ≃ ℤ) (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) : Fiber →L[ℂ] Fiber :=
  (fiberReindex e).toLinearIsometry.toContinuousLinearMap.comp (fiberMultiplier a C hC ha)

@[simp] lemma fiberWeightedPermutation_apply (e : ℤ ≃ ℤ) (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) (v : Fiber) (j : ℤ) :
    fiberWeightedPermutation e a C hC ha v j = a (e j)*v (e j) := rfl

lemma fiberWeightedPermutation_norm_le (e : ℤ ≃ ℤ) (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) : ‖fiberWeightedPermutation e a C hC ha‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  change ‖fiberReindex e (fiberMultiplier a C hC ha v)‖ ≤ _
  rw [(fiberReindex e).norm_map]
  exact fiberMultiplierVector_bound a C hC ha v

lemma fiberCoordinates_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (f : X → Fiber) (hf : ∀ n : ℤ, Measurable (fun x => f x n)) : StronglyMeasurable f := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, lp.single 2 n (f x n))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => (lp.single 2 n (f x n) : Fiber)) :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp_stronglyMeasurable
        (hf n).stronglyMeasurable
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ∞) (f x)

end
end BackwardIntertwiners

end OAI


