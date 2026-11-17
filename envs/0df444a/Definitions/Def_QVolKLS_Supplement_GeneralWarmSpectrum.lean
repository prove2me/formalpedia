-- Prove2me | Definitions.Def_QVolKLS_Supplement_GeneralWarmSpectrum
-- name    : QVolKLS_Supplement_GeneralWarmSpectrum
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T03:32:07.264951+00:00
-- url     : https://prove2.me/theorems/9c3f71e4-5f53-4792-ad81-d44f69501407
-- title:
--   General reversible Markov operators and slow spectral projections
-- statement:
--   Let $P$ be a Markov kernel on an arbitrary measurable space with stationary probability measure $\pi$. This definition module supplies the kernel action on complex-valued functions, iterated laws, total variation over measurable sets, $M$-warm starts, and mixing-time predicates without using a default-valued infimum. It also defines positivity and ergodicity of the induced Markov operator.
--
--   For a vector field $\Psi$ taking values in a complex normed space, its homogeneous second- and fourth-moment quantities are
--   $$
--   \|\Psi\|_{2,\pi}=\left(\int\|\Psi(x)\|^2\,d\pi(x)\right)^{1/2},\qquad
--   \|\Psi\|_{4,\pi}=\left(\int\|\Psi(x)\|^4\,d\pi(x)\right)^{1/4},
--   $$
--   valued in $[0,+\infty]$. A slow spectral projection is represented axiomatically as an orthogonal projection commuting with $P$, annihilating constants, and separating the nonstationary spectrum at $1-1/(2t)$; its tensor extension is characterized by all continuous scalar functionals.
--
--   These objects provide the general-measure-space interface used by Theorem 3.1.
--
--   **Formalization Note** Nonintegrable moments are $+\infty$, not the default zero of a Bochner integral. The fast complement is centered by subtracting the $\pi$-mean, so the excluded stationary eigenvalue cannot make the spectral predicate inconsistent.
-- source:
--   R. Zhang, Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation, arXiv:2610.04987 (held version, sha256 eee7a45e7117af08035a8d75fd6f145fa82ddade51ad87a6507911b6a0aa4f80), §2.3, pp.22-23; Theorem 3.1, pp.24-26

import Mathlib

set_option autoImplicit false

namespace QVolKLS.Supplement

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-!
# General reversible Markov operators, warm starts, and slow spectral projections

R. Zhang, *Improved Upper and Lower Bounds for Quantum Convex-Body Volume Estimation*,
arXiv:2610.04987 (held version, sha256 eee7a45e…), §2.3, pp.22–23 and Theorem 3.1,
pp.24–26.

**Formalization Note.** This interface is deliberately not finite-state. A Markov kernel acts on
scalar functions by integration and on measures by kernel composition. Total variation is the
supremum over measurable sets, and `GeneralMixTimeLe` quantifies over all warm probability starts.

Mathlib does not provide the Borel spectral projection of a general bounded self-adjoint operator.
`IsSlowProjection` therefore characterizes the relevant projection by its operator-theoretic
properties: complex linearity, orthogonal projection, commutation with the Markov operator,
annihilation of constants, and the slow/fast quadratic-form split at `1 - 1/(2t)`. This permits any
orthogonal projection realizing that split (including a choice on the threshold eigenspace); the
canonical projection `E_P([1-1/(2t),1))` is included. `IsTensorExtension` characterizes `Π ⊗ I_A` by
commutation with every continuous scalar functional on the auxiliary Hilbert space.

Positivity, ergodicity, and the projection mapping property are imposed on `L²(π)`, exactly as in
the paper; in particular, a purported projection cannot evade the spectral inequalities by sending
an `L²` function to a nonintegrable representative.

`generalJointL2` and `generalJointL4` use nonnegative integrals and take values in `ℝ≥0∞`, so a
nonintegrable fourth moment is `+∞`, never the Bochner integral's default zero.
-/

/-- The action of a Markov kernel on complex-valued functions. -/
noncomputable def kernelApply {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    (f : X → ℂ) (x : X) : ℂ :=
  ∫ y, f y ∂(P x)

/-- The law after `n` applications of a Markov kernel. -/
noncomputable def kernelLawAfter {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    (nu : Measure X) : ℕ → Measure X
  | 0 => nu
  | n + 1 => P ∘ₘ kernelLawAfter P nu n

/-- Total variation on a general measurable space. -/
noncomputable def generalTV {X : Type*} [MeasurableSpace X] (mu nu : Measure X) : ℝ :=
  ⨆ A : {A : Set X // MeasurableSet A}, |(mu A.1).toReal - (nu A.1).toReal|

/-- `nu` is an `M`-warm probability start for `pi`. -/
def IsWarmStart {X : Type*} [MeasurableSpace X] (M : ℝ) (nu pi : Measure X) : Prop :=
  nu Set.univ = 1 ∧ nu ≤ ENNReal.ofReal M • pi

/-- `τ_mix(η,ν,π;P) ≤ t`, without an `sInf` default-value convention. -/
def GeneralMixTimeLe {X : Type*} [MeasurableSpace X] (eta : ℝ) (nu pi : Measure X)
    (P : Kernel X X) (t : ℕ) : Prop :=
  ∃ j ≤ t, generalTV (kernelLawAfter P nu j) pi ≤ eta

/-- Uniform mixing by time `t` from every two-warm start. -/
def GeneralMixTimeTwoLe {X : Type*} [MeasurableSpace X] (eta : ℝ) (pi : Measure X)
    (P : Kernel X X) (t : ℕ) : Prop :=
  ∀ nu : Measure X, IsWarmStart 2 nu pi → GeneralMixTimeLe eta nu pi P t

/-- Positivity of the Markov operator on `L²(π)`, expressed by its quadratic form. -/
def IsPositiveMarkovOperator {X : Type*} [MeasurableSpace X] (pi : Measure X)
    (P : Kernel X X) : Prop :=
  ∀ f : X → ℂ, MemLp f 2 pi → MemLp (kernelApply P f) 2 pi →
    Integrable (fun x ↦ star (f x) * kernelApply P f x) pi →
    0 ≤ (∫ x, star (f x) * kernelApply P f x ∂pi).re

/-- Ergodicity: the integrable fixed functions are almost everywhere constant. -/
def IsErgodicMarkovOperator {X : Type*} [MeasurableSpace X] (pi : Measure X)
    (P : Kernel X X) : Prop :=
  ∀ f : X → ℂ, MemLp f 2 pi →
    (∀ᵐ x ∂pi, kernelApply P f x = f x) → ∃ c : ℂ, ∀ᵐ x ∂pi, f x = c

/-- The nonnegative `L²(π;H)` norm of a vector field. -/
noncomputable def generalJointL2 {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    (pi : Measure X) (Psi : X → H) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal ‖Psi x‖ ^ 2 ∂pi) ^ (1 / 2 : ℝ)

/-- The homogeneous vector-valued fourth-moment norm `( ∫ ‖Ψ(x)‖⁴ dπ )¹ᐟ⁴`. -/
noncomputable def generalJointL4 {X H : Type*} [MeasurableSpace X] [NormedAddCommGroup H]
    (pi : Measure X) (Psi : X → H) : ℝ≥0∞ :=
  (∫⁻ x, ENNReal.ofReal ‖Psi x‖ ^ 4 ∂pi) ^ (1 / 4 : ℝ)

/-- A scalar projection realizing a (possibly smaller) slow spectral subspace above
`1 - 1/(2t)` and below the stationary eigenvalue `1`. -/
def IsSlowProjection {X : Type*} [MeasurableSpace X] (pi : Measure X) (P : Kernel X X)
    (t : ℕ) (S : (X → ℂ) → X → ℂ) : Prop :=
  (∀ a b : ℂ, ∀ f g, ∀ᵐ x ∂pi,
      S (fun y ↦ a * f y + b * g y) x = a * S f x + b * S g x) ∧
  (∀ f, MemLp f 2 pi → MemLp (S f) 2 pi) ∧
  (∀ f, ∀ᵐ x ∂pi, S (S f) x = S f x) ∧
  (∀ f g, Integrable f pi → Integrable g pi → Integrable (S f) pi → Integrable (S g) pi →
    ∫ x, star (S f x) * g x ∂pi = ∫ x, star (f x) * S g x ∂pi) ∧
  (∀ f, ∀ᵐ x ∂pi, S (kernelApply P f) x = kernelApply P (S f) x) ∧
  (∀ c : ℂ, ∀ᵐ x ∂pi, S (fun _ ↦ c) x = 0) ∧
  (∀ f, Integrable f pi → Integrable (S f) pi → Integrable (kernelApply P (S f)) pi →
    Integrable (fun x ↦ star (S f x) * kernelApply P (S f) x) pi →
    (1 - 1 / (2 * (t : ℝ))) * ∫ x, ‖S f x‖ ^ 2 ∂pi ≤
      (∫ x, star (S f x) * kernelApply P (S f) x ∂pi).re) ∧
  (∀ f, Integrable f pi →
    let g := fun x ↦ f x - S f x - ∫ y, f y ∂pi
    Integrable g pi → Integrable (kernelApply P g) pi →
    Integrable (fun x ↦ star (g x) * kernelApply P g x) pi →
    (∫ x, star (g x) * kernelApply P g x ∂pi).re ≤
      (1 - 1 / (2 * (t : ℝ))) * ∫ x, ‖g x‖ ^ 2 ∂pi)

/-- `SA` is the tensor extension `S ⊗ I_H`, characterized by scalar continuous functionals. -/
def IsTensorExtension {X H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    [MeasurableSpace X] (pi : Measure X)
    (S : (X → ℂ) → X → ℂ) (SA : (X → H) → X → H) : Prop :=
  ∀ (Psi : X → H) (ell : H →L[ℂ] ℂ), ∀ᵐ x ∂pi,
    ell (SA Psi x) = S (fun y ↦ ell (Psi y)) x

/-- The general-space Markov data to which the slow-spectrum theorem applies. -/
structure GeneralWarmSpectrum (X : Type*) [MeasurableSpace X] where
  pi : Measure X
  P : Kernel X X
  invariant : Kernel.Invariant P pi
  reversible : Kernel.IsReversible P pi
  positive : IsPositiveMarkovOperator pi P
  ergodic : IsErgodicMarkovOperator pi P

end QVolKLS.Supplement


