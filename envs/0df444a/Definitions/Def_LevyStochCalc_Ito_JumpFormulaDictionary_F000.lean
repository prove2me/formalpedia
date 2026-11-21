-- Prove2me | Definitions.Def_LevyStochCalc_Ito_JumpFormulaDictionary_F000
-- name    : LevyStochCalc_Ito_JumpFormulaDictionary_F000
-- status  : Definition
-- author  : @WillR
-- created : 2026-11-20T23:14:49.236992+00:00
-- url     : https://prove2.me/theorems/ca841eae-17ee-43f4-95d9-6fd46158018d
-- title:
--   Source declarations: LevyStochCalc.Ito.JumpFormulaDictionary
-- statement:
--   Source-preserving extracted declarations from LevyStochCalc.Ito.JumpFormulaDictionary. Existing definitions, lemmas, instances, proofs and elaboration context are retained; generated import closure remains under review.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_LevyStochCalc_Ito_ItoFormulaTimeUnbounded_F000
import Definitions.Def_LevyStochCalc_Ito_JumpFormula_F000
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

/-!
# Time-augmented coordinates for the Itô–Lévy integrands

The integrands of the Itô–Lévy formula are built from the gradient, the Hessian and the time
derivative of a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state, while Itô's formula for a
time-dependent function is stated with the coordinate partial derivatives `coordDeriv` and
`coordDeriv₂` of a function on `Fin (n + 1) → ℝ` carrying time as its zeroth coordinate. For the
representative `z ↦ u (z 0) (fun q => z q.succ)` the two families of derivatives agree
coordinatewise, and the drift, diffusion and compensator-drift integrands assembled from them
coincide.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.timeAugFun` — the representative of `u` on the state space with
  a time coordinate prepended.
* `LevyStochCalc.Ito.JumpFormula.coordDeriv_succ_cons_eq_gradient`,
  `coordDeriv_zero_cons_eq_timeDeriv`, `coordDeriv₂_succ_succ_cons_eq_hessian` — the
  coordinatewise dictionary between the two families of derivatives.
* `LevyStochCalc.Ito.JumpFormula.diffusionIntegrand_dictionary`,
  `levyGenerator_dictionary`, `driftIntegrand_dictionary`,
  `compensatorDriftIntegrand_dictionary` — the integrands.
* `LevyStochCalc.Ito.JumpFormula.multidimStochasticIntegral_eq_sum` — the multidimensional Itô
  integral as the sum of the one-dimensional integrals of its components.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_Icc_eq_setIntegral_Ioc` — the integrals over the
  two windows `Set.Icc 0 T` and `Set.Ioc 0 T` agree.
-/

namespace LevyStochCalc.Ito.JumpFormula

open MeasureTheory
open scoped NNReal ENNReal

section Augmentation

variable {n : ℕ}

/-- The continuous linear embedding `v ↦ Fin.cons 0 v` of the state space into the state space
with a time coordinate prepended. -/
noncomputable def consEmbed (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi
    (Fin.cons (0 : (Fin n → ℝ) →L[ℝ] ℝ) fun q : Fin n => ContinuousLinearMap.proj q)
@[simp]
theorem consEmbed_apply (v : Fin n → ℝ) : consEmbed n v = Fin.cons 0 v := by
  funext i
  induction i using Fin.cases with
  | zero => simp [consEmbed, ContinuousLinearMap.pi_apply]
  | succ p => simp [consEmbed, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply]
/-- A point of the state space with a time coordinate prepended is its zeroth coordinate
consed onto its remaining coordinates. -/
theorem cons_zero_succ (z : Fin (n + 1) → ℝ) : (Fin.cons (z 0) fun p => z p.succ) = z := by
  funext i
  induction i using Fin.cases with
  | zero => simp
  | succ p => simp
/-- The embedding carries the `q`-th standard basis vector to the `q.succ`-th one. -/
theorem consEmbed_single (q : Fin n) :
    consEmbed n (Pi.single q (1 : ℝ)) = Pi.single q.succ (1 : ℝ) := by
  classical
  rw [consEmbed_apply]
  funext i
  induction i using Fin.cases with
  | zero =>
    have h : (0 : Fin (n + 1)) ≠ q.succ := fun hz => (Fin.succ_ne_zero q) hz.symm
    simp [h]
  | succ p => simp [Pi.single_apply, Fin.succ_inj]
/-- The map `y ↦ Fin.cons s y` is affine with linear part the embedding of the state space. -/
theorem hasFDerivAt_cons (s : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => (Fin.cons s y : Fin (n + 1) → ℝ)) (consEmbed n) x := by
  have hbase : HasFDerivAt
      (fun y : Fin n → ℝ => (Fin.cons s (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) + consEmbed n y)
      (consEmbed n) x := by
    simpa using (hasFDerivAt_const (Fin.cons s (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) x).add
      (consEmbed n).hasFDerivAt
  have heq : (fun y : Fin n → ℝ =>
        (Fin.cons s (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) + consEmbed n y)
      = fun y : Fin n → ℝ => (Fin.cons s y : Fin (n + 1) → ℝ) := by
    funext y i
    induction i using Fin.cases with
    | zero => simp
    | succ p => simp
  rwa [heq] at hbase
/-- The map `t ↦ Fin.cons t x` has unit velocity in the prepended coordinate. -/
theorem hasDerivAt_consTime (x : Fin n → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => (Fin.cons t x : Fin (n + 1) → ℝ))
      (Pi.single (0 : Fin (n + 1)) 1) s := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 s := hasDerivAt_id' s
  have hsmul : HasDerivAt (fun t : ℝ => t • (Pi.single (0 : Fin (n + 1)) (1 : ℝ)))
      ((1 : ℝ) • Pi.single (0 : Fin (n + 1)) (1 : ℝ)) s :=
    hid.smul_const _
  have hbase : HasDerivAt
      (fun t : ℝ => (Fin.cons (0 : ℝ) x : Fin (n + 1) → ℝ)
        + t • (Pi.single (0 : Fin (n + 1)) (1 : ℝ)))
      (0 + (1 : ℝ) • Pi.single (0 : Fin (n + 1)) (1 : ℝ)) s :=
    (hasDerivAt_const s (Fin.cons (0 : ℝ) x : Fin (n + 1) → ℝ)).add hsmul
  have heq : (fun t : ℝ => (Fin.cons (0 : ℝ) x : Fin (n + 1) → ℝ)
        + t • (Pi.single (0 : Fin (n + 1)) (1 : ℝ)))
      = fun t : ℝ => (Fin.cons t x : Fin (n + 1) → ℝ) := by
    funext t i
    induction i using Fin.cases with
    | zero => simp
    | succ p => simp [Fin.succ_ne_zero p]
  rw [heq] at hbase
  simpa using hbase
/-- The representative `z ↦ u (z 0) (fun q => z q.succ)` of a function of time and state on the
state space with a time coordinate prepended. -/
def timeAugFun (u : ℝ → (Fin n → ℝ) → ℝ) : (Fin (n + 1) → ℝ) → ℝ :=
  fun z => u (z 0) fun q => z q.succ
@[simp]
theorem timeAugFun_cons (u : ℝ → (Fin n → ℝ) → ℝ) (s : ℝ) (x : Fin n → ℝ) :
    timeAugFun u (Fin.cons s x) = u s x := by
  simp [timeAugFun]
/-- The time-augmented path is the time consed onto the path. -/
theorem timeAugProcess_eq_cons {Ω : Type*} (X : ℝ → Ω → Fin n → ℝ) (s : ℝ) (ω : Ω) :
    LevyStochCalc.Brownian.Ito.timeAugProcess X s ω = Fin.cons s (X s ω) := rfl
/-- The representative evaluated along the time-augmented path is `u` along the path. -/
theorem timeAugFun_timeAugProcess {Ω : Type*} (u : ℝ → (Fin n → ℝ) → ℝ)
    (X : ℝ → Ω → Fin n → ℝ) (s : ℝ) (ω : Ω) :
    timeAugFun u (LevyStochCalc.Brownian.Ito.timeAugProcess X s ω) = u s (X s ω) := by
  rw [timeAugProcess_eq_cons, timeAugFun_cons]
end Augmentation

section Derivatives

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

/-- The section of the representative at a fixed time is differentiable with derivative the
derivative of the representative composed with the embedding of the state space. -/
theorem hasFDerivAt_section (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (s : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (u s) ((f' (Fin.cons s x)).comp (consEmbed n)) x := by
  have hsec : u s = fun y : Fin n → ℝ => f (Fin.cons s y) := by
    funext y
    rw [hfu, timeAugFun_cons]
  rw [hsec]
  exact HasFDerivAt.comp x (hf (Fin.cons s x)) (hasFDerivAt_cons s x)
/-- The partial derivatives of the representative in the prepended coordinates are the
components of the gradient of `u`. -/
theorem coordDeriv_succ_cons_eq_gradient (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (s : ℝ) (x : Fin n → ℝ) (q : Fin n) :
    coordDeriv f' q.succ (Fin.cons s x) = gradient u s x q := by
  have hd := hasFDerivAt_section hfu hf s x
  simp only [gradient, hd.fderiv, coordDeriv, ContinuousLinearMap.comp_apply, consEmbed_single]
/-- The partial derivatives of the representative in the prepended coordinates, at an arbitrary
point of the augmented state space. -/
theorem coordDeriv_succ_eq_gradient (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (z : Fin (n + 1) → ℝ) (q : Fin n) :
    coordDeriv f' q.succ z = gradient u (z 0) (fun p => z p.succ) q := by
  have h := coordDeriv_succ_cons_eq_gradient hfu hf (z 0) (fun p => z p.succ) q
  rwa [cons_zero_succ z] at h
/-- The partial derivative of the representative in the zeroth coordinate is the time
derivative of `u`. -/
theorem coordDeriv_zero_cons_eq_timeDeriv (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (s : ℝ) (x : Fin n → ℝ) :
    coordDeriv f' 0 (Fin.cons s x) = timeDeriv u s x := by
  have hsec : (fun t : ℝ => u t x) = fun t : ℝ => f (Fin.cons t x) := by
    funext t
    rw [hfu, timeAugFun_cons]
  have hd : HasDerivAt (fun t : ℝ => u t x)
      (f' (Fin.cons s x) (Pi.single (0 : Fin (n + 1)) 1)) s := by
    rw [hsec]
    exact HasFDerivAt.comp_hasDerivAt s (hf (Fin.cons s x)) (hasDerivAt_consTime x s)
  simp only [timeDeriv, coordDeriv, hd.deriv]
/-- The partial derivative of the representative in the zeroth coordinate, at an arbitrary
point of the augmented state space. -/
theorem coordDeriv_zero_eq_timeDeriv (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (z : Fin (n + 1) → ℝ) :
    coordDeriv f' 0 z = timeDeriv u (z 0) (fun p => z p.succ) := by
  have h := coordDeriv_zero_cons_eq_timeDeriv hfu hf (z 0) (fun p => z p.succ)
  rwa [cons_zero_succ z] at h
/-- The second partial derivatives of the representative in the prepended coordinates are the
entries of the Hessian of `u`, read with the two indices exchanged. -/
theorem coordDeriv₂_succ_succ_cons_eq_hessian_comm (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (s : ℝ) (x : Fin n → ℝ) (p q : Fin n) :
    coordDeriv₂ f'' p.succ q.succ (Fin.cons s x) = hessian u s x q p := by
  have hgrad : (fun y : Fin n → ℝ => fderiv ℝ (u s) y (Pi.single q 1))
      = fun y : Fin n → ℝ => f' (Fin.cons s y) (Pi.single q.succ (1 : ℝ)) := by
    funext y
    have h := coordDeriv_succ_cons_eq_gradient hfu hf s y q
    simp only [coordDeriv, gradient] at h
    exact h.symm
  have hev0 := HasFDerivAt.comp (Fin.cons s x : Fin (n + 1) → ℝ)
      (ContinuousLinearMap.apply ℝ ℝ (Pi.single q.succ (1 : ℝ))).hasFDerivAt
      (hf' (Fin.cons s x))
  have hev : HasFDerivAt (fun w : Fin (n + 1) → ℝ => f' w (Pi.single q.succ (1 : ℝ)))
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single q.succ (1 : ℝ))).comp
        (f'' (Fin.cons s x))) (Fin.cons s x) := hev0
  have hcomp0 := HasFDerivAt.comp x hev (hasFDerivAt_cons s x)
  have hcomp : HasFDerivAt
      (fun y : Fin n → ℝ => f' (Fin.cons s y) (Pi.single q.succ (1 : ℝ)))
      (((ContinuousLinearMap.apply ℝ ℝ (Pi.single q.succ (1 : ℝ))).comp
        (f'' (Fin.cons s x))).comp (consEmbed n)) x := hcomp0
  simp only [hessian, hgrad, hcomp.fderiv, coordDeriv₂, ContinuousLinearMap.comp_apply,
    consEmbed_single, ContinuousLinearMap.apply_apply]
/-- The second partial derivatives of the representative in the prepended coordinates are the
entries of the Hessian of `u`. -/
theorem coordDeriv₂_succ_succ_cons_eq_hessian (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (s : ℝ) (x : Fin n → ℝ) (p q : Fin n) :
    coordDeriv₂ f'' p.succ q.succ (Fin.cons s x) = hessian u s x p q := by
  rw [← coordDeriv₂_succ_succ_cons_eq_hessian_comm hfu hf hf' s x q p]
  simp only [coordDeriv₂]
  exact second_derivative_symmetric hf (hf' (Fin.cons s x)) _ _
/-- The second partial derivatives of the representative in the prepended coordinates, at an
arbitrary point of the augmented state space. -/
theorem coordDeriv₂_succ_succ_eq_hessian (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (z : Fin (n + 1) → ℝ) (p q : Fin n) :
    coordDeriv₂ f'' p.succ q.succ z = hessian u (z 0) (fun r => z r.succ) p q := by
  have h := coordDeriv₂_succ_succ_cons_eq_hessian hfu hf hf' (z 0) (fun r => z r.succ) p q
  rwa [cons_zero_succ z] at h
end Derivatives

section Integrands

variable {n d : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

/-- The row of the diffusion matrix weighted by the partial derivatives of the representative is
the diffusion integrand of the Itô–Lévy formula. -/
theorem diffusionIntegrand_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) (s : ℝ) (x : Fin n → ℝ) (j : Fin d) :
    (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s x) * σ s x q j)
      = diffusionIntegrand u σ s x j := by
  simp only [diffusionIntegrand]
  exact Finset.sum_congr rfl fun q _ => by
    rw [coordDeriv_succ_cons_eq_gradient hfu hf s x q]
/-- The drift and quadratic-variation terms of Itô's formula in the prepended coordinates make
up the Lévy generator of `u`. -/
theorem levyGenerator_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)) (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ))
    (s : ℝ) (x : Fin n → ℝ) :
    (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s x) * μ s x q)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s x)
              * ∑ k : Fin d, σ s x p k * σ s x q k
      = levyGenerator u μ σ s x := by
  have h1 : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s x) * μ s x q)
      = ∑ i : Fin n, μ s x i * gradient u s x i :=
    Finset.sum_congr rfl fun q _ => by
      rw [coordDeriv_succ_cons_eq_gradient hfu hf s x q, mul_comm]
  have h2 : (∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s x)
        * ∑ k : Fin d, σ s x p k * σ s x q k)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin d,
          σ s x i k * σ s x j k * hessian u s x i j := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv₂_succ_succ_cons_eq_hessian hfu hf hf' s x p q, ← Finset.sum_mul]
    ring
  simp only [levyGenerator]
  rw [h1, h2]
/-- The three non-stochastic terms of Itô's formula in the prepended coordinates make up the
drift integrand of the Itô–Lévy formula. -/
theorem driftIntegrand_dictionary {E : Type*} (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (s : ℝ) (x : Fin n → ℝ) :
    coordDeriv f' 0 (Fin.cons s x)
        + (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s x) * coeffs.μ s x q)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s x)
              * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k
      = driftIntegrand u coeffs s x := by
  simp only [driftIntegrand]
  rw [add_assoc, levyGenerator_dictionary hfu hf hf' coeffs.μ coeffs.σ s x,
    coordDeriv_zero_cons_eq_timeDeriv hfu hf s x]
/-- The compensator-drift integrand of the Itô–Lévy formula written with the representative and
its partial derivatives in the prepended coordinates. -/
theorem compensatorDriftIntegrand_dictionary {E : Type*} (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E) :
    compensatorDriftIntegrand u γ s x e
      = f (Fin.cons s (x + γ s x e)) - f (Fin.cons s x)
        - ∑ i : Fin n, γ s x e i * coordDeriv f' i.succ (Fin.cons s x) := by
  have hcons : ∀ (t : ℝ) (y : Fin n → ℝ), f (Fin.cons t y) = u t y := fun t y => by
    rw [hfu, timeAugFun_cons]
  simp only [compensatorDriftIntegrand, hcons,
    coordDeriv_succ_cons_eq_gradient hfu hf s x]
end Integrands

section BrownianSum

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The multidimensional Brownian Itô integral is the sum over the components of the
one-dimensional Itô integrals against the component Brownian motions. -/
theorem multidimStochasticIntegral_eq_sum
    (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ i : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hq : ∀ (i : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (ω : Ω) :
    MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq T ω
      = ∑ i : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱ i)
          (fun ω' s => Z s ω' i) (hm i) (hp i) (hq i) T ω :=
  rfl
/-- The components of the multidimensional Brownian Itô integral may be replaced by any
integrands equal to them as functions of the sample point and the time. -/
theorem multidimStochasticIntegral_eq_sum_congr
    (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ i : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hq : ∀ (i : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (F : Fin d → Ω → ℝ → ℝ) (hZF : ∀ i : Fin d, (fun ω' s => Z s ω' i) = F i)
    (hmF : ∀ i : Fin d, Measurable (Function.uncurry (F i)))
    (hpF : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (F i))
    (hqF : ∀ (i : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (ω : Ω) :
    MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq T ω
      = ∑ i : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱ i)
          (F i) (hmF i) (hpF i) (hqF i) T ω := by
  rw [multidimStochasticIntegral_eq_sum]
  exact Finset.sum_congr rfl fun i _ =>
    congrFun (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_fun (W.W i) ℱ (hℱ i)
      (hZF i) (hm i) (hp i) (hq i) (hmF i) (hpF i) (hqF i) T) ω
end BrownianSum

section Window

/-- The integral of a function of time over `Set.Icc 0 T` agrees with its integral over
`Set.Ioc 0 T`. -/
theorem setIntegral_Icc_eq_setIntegral_Ioc {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (g : ℝ → F) (T : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T, g s = ∫ s in Set.Ioc (0 : ℝ) T, g s :=
  (MeasureTheory.setIntegral_congr_set MeasureTheory.Ioc_ae_eq_Icc).symm
end Window

end LevyStochCalc.Ito.JumpFormula


