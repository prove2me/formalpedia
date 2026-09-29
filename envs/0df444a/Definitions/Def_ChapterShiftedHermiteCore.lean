-- Prove2me | Definitions.Def_ChapterShiftedHermiteCore
-- name    : ChapterShiftedHermiteCore
-- status  : Definition
-- author  : @leonardopedro
-- created : 2026-09-15T20:18:01.59586+00:00
-- url     : https://prove2.me/theorems/c6c62b6f-1e33-4357-ab1e-73ed7d3fbe6a
-- title:
--   The translated, modulated Gauss–polynomial core of `L²(ℝᵈ)` What is proved
-- statement:
--   Formal definitions for the timepiece Lean 4 formalization (module `BookProof.ShiftedHermiteCore`, source chapter `BookProof/ChapterShiftedHermiteCore.lean`): The translated, modulated Gauss–polynomial core of `L²(ℝᵈ)` What is proved
--
--   `BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial (product Hermite) core `polyGaussCore = { p · e^{-‖x‖²/4} }` of `L²(ℝᵈ)` and proves it dense, and `BookProof.ChapterHyperbolicQuadraticEsa` uses it to diagonalize the diagonal quadratic Hamiltonians `H_c = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4)`.
--
--   This module builds the **phase-space translate** of that core: for a translation vector `a ∈ ℝᵈ` and a wave vector `k ∈ ℝᵈ`,
--
--   `D_{a,k} = { x ↦ p(x − a) · e^{-‖x−a‖²/4} · e^{i⟨k,x⟩} : p ∈ ℂ[X₀,…,X_{d-1}] }`.
--
--   This is the image of `polyGaussCore` under the Weyl (phase-space translation) unitary `f ↦ e^{i⟨k,x⟩} f(x − a)`, and it is the natural core for a quadratic Hamiltonian that has been *completed to a square*: it is the Hermite core recentred at the classical equilibrium `x = a` and boosted to the classical momentum `k`.
--
--   * `pgFunT`, `memLp_pgFunT`, `pgLpT`, `pgMapT`, `pgMapT_injective` — the translated, modulated Gauss–polynomial functions are square integrable and depend injectively on the polynomial; * `inner_pgLpT` — the map is **isometric**: `⟪pgLpT a k p, pgLpT a k q⟫ = ⟪pgLp p, pgLp q⟫` (translation invariance of Lebesgue measure and `|e^{i⟨k,x⟩}| = 1`); * `polyGaussCoreT`, `polyGaussCoreT_dense` — the resulting core is dense in `L²(ℝᵈ)`; * `hermiteTLp`, `orthonormal_hermiteTLp`, `span_hermiteTLp`, `hermiteTLp_total` — the translated, modulated product Hermite functions are an orthonormal family spanning the core, and total in `L²(ℝᵈ)`; * `coreEquivT`, `coreOpT` — the core coordinatized by polynomials, and operators on it given by operators on the polynomial coordinates; * `mulXTPoly`, `momTPoly`, `pgFunT_mulXTPoly`, `pgFunT_momTPoly` — **the canonical pair in the translated frame**: on `D_{a,k}` multiplication by `xᵢ` is `Xᵢ + aᵢ` and the momentum `πᵢ = −i∂/∂xᵢ` is `momPolyᵢ + kᵢ` in the polynomial coordinates, the second identity being an honest statement about Mathlib's `deriv` along the `i`-th coordinate line.
--
--   Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`).
-- source:
--   https://github.com/leonardopedro/timepiece/blob/61595bc/BookProof/ChapterShiftedHermiteCore.lean

import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesDifferentialL2

import Mathlib

/-!
# The translated, modulated Gauss–polynomial core of `L²(ℝᵈ)`

`BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial (product Hermite) core
`polyGaussCore = { p · e^{-‖x‖²/4} }` of `L²(ℝᵈ)` and proves it dense, and
`BookProof.ChapterHyperbolicQuadraticEsa` uses it to diagonalize the diagonal quadratic
Hamiltonians `H_c = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4)`.

This module builds the **phase-space translate** of that core: for a translation vector
`a ∈ ℝᵈ` and a wave vector `k ∈ ℝᵈ`,

`D_{a,k} = { x ↦ p(x − a) · e^{-‖x−a‖²/4} · e^{i⟨k,x⟩} : p ∈ ℂ[X₀,…,X_{d-1}] }`.

This is the image of `polyGaussCore` under the Weyl (phase-space translation) unitary
`f ↦ e^{i⟨k,x⟩} f(x − a)`, and it is the natural core for a quadratic Hamiltonian that has
been *completed to a square*: it is the Hermite core recentred at the classical
equilibrium `x = a` and boosted to the classical momentum `k`.

## What is proved

* `pgFunT`, `memLp_pgFunT`, `pgLpT`, `pgMapT`, `pgMapT_injective` — the translated,
  modulated Gauss–polynomial functions are square integrable and depend injectively on the
  polynomial;
* `inner_pgLpT` — the map is **isometric**: `⟪pgLpT a k p, pgLpT a k q⟫ = ⟪pgLp p, pgLp q⟫`
  (translation invariance of Lebesgue measure and `|e^{i⟨k,x⟩}| = 1`);
* `polyGaussCoreT`, `polyGaussCoreT_dense` — the resulting core is dense in `L²(ℝᵈ)`;
* `hermiteTLp`, `orthonormal_hermiteTLp`, `span_hermiteTLp`, `hermiteTLp_total` — the
  translated, modulated product Hermite functions are an orthonormal family spanning the
  core, and total in `L²(ℝᵈ)`;
* `coreEquivT`, `coreOpT` — the core coordinatized by polynomials, and operators on it
  given by operators on the polynomial coordinates;
* `mulXTPoly`, `momTPoly`, `pgFunT_mulXTPoly`, `pgFunT_momTPoly` — **the canonical pair in
  the translated frame**: on `D_{a,k}` multiplication by `xᵢ` is `Xᵢ + aᵢ` and the momentum
  `πᵢ = −i∂/∂xᵢ` is `momPolyᵢ + kᵢ` in the polynomial coordinates, the second identity
  being an honest statement about Mathlib's `deriv` along the `i`-th coordinate line.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ShiftedHermiteCore

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore
open BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow.DifferentialL2

noncomputable section

variable {d : ℕ}

/-! ## The unimodular phase -/

/-- The linear phase argument `⟨k, x⟩ = ∑ᵢ kᵢxᵢ`. -/
def phaseArg (k x : Vd d) : ℝ := ∑ i, k i * x i

/-- The unimodular phase `e^{i⟨k,x⟩}`. -/
def phaseFun (k x : Vd d) : ℂ := Complex.exp (Complex.I * ((phaseArg k x : ℝ) : ℂ))

theorem norm_phaseFun (k x : Vd d) : ‖phaseFun k x‖ = 1 := by
  rw [phaseFun, Complex.norm_exp]
  simp [Complex.mul_re]



theorem continuous_phaseFun (k : Vd d) : Continuous (phaseFun k : Vd d → ℂ) := by
  refine Complex.continuous_exp.comp (continuous_const.mul ?_)
  exact Complex.continuous_ofReal.comp (by unfold phaseArg; fun_prop)



theorem conj_mul_phaseFun (k x : Vd d) :
    (starRingEnd ℂ) (phaseFun k x) * phaseFun k x = 1 := by
  have hz : (starRingEnd ℂ) (Complex.I * ((phaseArg k x : ℝ) : ℂ))
      = -(Complex.I * ((phaseArg k x : ℝ) : ℂ)) := by
    simp [Complex.conj_I]
  rw [phaseFun, ← Complex.exp_conj, hz, ← Complex.exp_add]
  simp

/-! ## The translated, modulated Gauss–polynomial functions -/

/-- `pgFunT a k p x = p(x − a) · e^{-‖x−a‖²/4} · e^{i⟨k,x⟩}`. -/
def pgFunT (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) : ℂ :=
  pgFun p (x - a) * phaseFun k x

theorem continuous_pgFunT (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    Continuous (pgFunT a k p) :=
  ((continuous_pgFun p).comp (continuous_id.sub continuous_const)).mul (continuous_phaseFun k)

theorem norm_pgFunT (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    ‖pgFunT a k p x‖ = ‖pgFun p (x - a)‖ := by
  rw [pgFunT, norm_mul, norm_phaseFun, mul_one]

theorem pgFunT_add (a k : Vd d) (p q : MvPolynomial (Fin d) ℂ) :
    pgFunT a k (p + q) = pgFunT a k p + pgFunT a k q := by
  funext x; simp [pgFunT, HermiteProductCore.pgFun_add, add_mul]

theorem pgFunT_smul (a k : Vd d) (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    pgFunT a k (c • p) = c • pgFunT a k p := by
  funext x; simp [pgFunT, HermiteProductCore.pgFun_smul, mul_assoc]

/-- Translation invariance of the `MemLp` condition. -/
theorem memLp_comp_sub {f : Vd d → ℂ} (hf : MemLp f 2 (volume : Measure (Vd d))) (a : Vd d) :
    MemLp (fun x : Vd d => f (x - a)) 2 (volume : Measure (Vd d)) :=
  hf.comp_measurePreserving (measurePreserving_sub_right (volume : Measure (Vd d)) a)

theorem memLp_pgFunT (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    MemLp (pgFunT a k p) 2 (volume : Measure (Vd d)) := by
  refine (memLp_comp_sub (memLp_pgFun p) a).mono
    (continuous_pgFunT a k p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_pgFunT]

/-- The element of `L²(ℝᵈ)` given by the translated, modulated Gauss–polynomial. -/
def pgLpT (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) : L2d d := (memLp_pgFunT a k p).toLp _

theorem pgLpT_coeFn (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    (pgLpT a k p : Vd d → ℂ) =ᵐ[volume] pgFunT a k p := (memLp_pgFunT a k p).coeFn_toLp

/-- The translated, modulated Gauss–polynomial map `ℂ[X₀,…,X_{d-1}] →ₗ[ℂ] L²(ℝᵈ)`. -/
def pgMapT (a k : Vd d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] L2d d where
  toFun := pgLpT a k
  map_add' p q := by
    simp only [pgLpT]
    rw [← MemLp.toLp_add (memLp_pgFunT a k p) (memLp_pgFunT a k q)]
    congr 1
    exact pgFunT_add a k p q
  map_smul' c p := by
    simp only [pgLpT, RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (memLp_pgFunT a k p)]
    congr 1
    exact pgFunT_smul a k c p

@[simp] theorem pgMapT_apply (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    pgMapT a k p = pgLpT a k p := rfl

/-! ## The map is an isometry of the core -/

/-- **The translated, modulated map preserves inner products.**  Translation invariance of
Lebesgue measure and `|e^{i⟨k,x⟩}| = 1`. -/
theorem inner_pgLpT (a k : Vd d) (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLpT a k p) (pgLpT a k q) : ℂ) = inner ℂ (pgLp p) (pgLp q) := by
  have hleft : (inner ℂ (pgLpT a k p) (pgLpT a k q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFunT a k p x) * pgFunT a k q x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [pgLpT_coeFn a k p, pgLpT_coeFn a k q] with x hx hy
    rw [hx, hy, RCLike.inner_apply, mul_comm]
  have hright : (inner ℂ (pgLp p) (pgLp q) : ℂ)
      = ∫ x : Vd d, (starRingEnd ℂ) (pgFun p x) * pgFun q x := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [pgLp_coeFn p, pgLp_coeFn q] with x hx hy
    rw [hx, hy, RCLike.inner_apply, mul_comm]
  rw [hleft, hright]
  have hpt : ∀ x : Vd d, (starRingEnd ℂ) (pgFunT a k p x) * pgFunT a k q x
      = ((fun y : Vd d => (starRingEnd ℂ) (pgFun p y) * pgFun q y) (x - a)) := by
    intro x
    simp only [pgFunT, map_mul]
    calc (starRingEnd ℂ) (pgFun p (x - a)) * (starRingEnd ℂ) (phaseFun k x)
          * (pgFun q (x - a) * phaseFun k x)
        = ((starRingEnd ℂ) (phaseFun k x) * phaseFun k x)
          * ((starRingEnd ℂ) (pgFun p (x - a)) * pgFun q (x - a)) := by ring
      _ = (starRingEnd ℂ) (pgFun p (x - a)) * pgFun q (x - a) := by
          rw [conj_mul_phaseFun, one_mul]
  simp_rw [hpt]
  exact integral_sub_right_eq_self (fun y : Vd d => (starRingEnd ℂ) (pgFun p y) * pgFun q y) a

theorem norm_pgLpT (a k : Vd d) (p : MvPolynomial (Fin d) ℂ) :
    ‖pgLpT a k p‖ = ‖pgLp p‖ := by
  have h := inner_pgLpT a k p p
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : (‖pgLpT a k p‖ : ℝ) ^ 2 = (‖pgLp p‖ : ℝ) ^ 2 := by exact_mod_cast h
  have h3 := congrArg Real.sqrt h2
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at h3

theorem pgMapT_injective (a k : Vd d) : Function.Injective (pgMapT a k) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have h0 : ‖pgLp p‖ = 0 := by
    rw [← norm_pgLpT a k p]
    simp only [pgMapT_apply] at hp
    rw [hp, norm_zero]
  have hz : pgMap (d := d) p = 0 := by
    simpa [HermiteProductCore.pgMap_apply] using norm_eq_zero.mp h0
  exact (injective_iff_map_eq_zero _).mp HermiteProductCore.pgMap_injective p hz

/-- **The translated, modulated Gauss–polynomial core** `D_{a,k}` of `L²(ℝᵈ)`. -/
def polyGaussCoreT (a k : Vd d) : Submodule ℂ (L2d d) := LinearMap.range (pgMapT a k)





/-! ## The core is dense -/





/-! ## The translated, modulated product Hermite functions -/

/-- The translated, modulated product Hermite function
`ψ_α(x − a) e^{i⟨k,x⟩}`, normalized in `L²`. -/
def hermiteTLp (a k : Vd d) (α : Fin d →₀ ℕ) : L2d d :=
  ((hermiteMvNorm α : ℝ) : ℂ)⁻¹ • pgLpT a k (hermiteMv α)













/-! ## The core coordinatized by polynomials -/

/-- The translated, modulated core, coordinatized by polynomials. -/
def coreEquivT (a k : Vd d) : MvPolynomial (Fin d) ℂ ≃ₗ[ℂ] (polyGaussCoreT a k) :=
  LinearEquiv.ofInjective (pgMapT a k) (pgMapT_injective a k)



/-- An operator on the translated core, given by an operator on the polynomial
coordinates. -/
def coreOpT (a k : Vd d) (T : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ) :
    (polyGaussCoreT a k) →ₗ[ℂ] (polyGaussCoreT a k) :=
  (coreEquivT a k).toLinearMap ∘ₗ T ∘ₗ (coreEquivT a k).symm.toLinearMap





/-! ## The canonical pair in the translated, modulated frame -/















/-- **Multiplication by the coordinate `xᵢ` in the translated frame**: `Xᵢ + aᵢ`. -/
def mulXTPoly (a : Vd d) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  mulXPoly i + ((a i : ℝ) : ℂ) • LinearMap.id

/-- **The momentum `πᵢ = −i∂ᵢ` in the translated, modulated frame**: `momPolyᵢ + kᵢ`. -/
def momTPoly (k : Vd d) (i : Fin d) : MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  momPoly i + ((k i : ℝ) : ℂ) • LinearMap.id









end

end BookProof.ShiftedHermiteCore


