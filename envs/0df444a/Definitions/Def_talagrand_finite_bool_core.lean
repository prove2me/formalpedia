-- Prove2me | Definitions.Def_talagrand_finite_bool_core
-- name    : talagrand_finite_bool_core
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-08-13T04:40:28.608524+00:00
-- url     : https://prove2.me/theorems/2475ffc2-08bf-4f62-85b6-629c90d51cf7
-- title:
--   Finite Boolean product processes for Talagrand and Klein–Rio concentration
-- statement:
--   This module defines the finite Boolean product-space notation used to formalize Talagrand–Ledoux and Klein–Rio concentration inequalities. It includes the product Bernoulli expectation and one-coordinate conditional expectation, finite supremum processes, the centered linear process $Z$, its absolute counterpart $\bar Z$, the random variance process $\Sigma^2$, truncation and symmetrization processes, and the compensated process used for lower-tail estimates.\n\nThese definitions provide a shared interface for separately stated entropy, moment-generating-function, upper-tail, lower-tail, and two-sided concentration theorems.\n\n**Formalization Note** The probability space is the finite Boolean cube $\kappa\to\{0,1\}$ with Bernoulli parameter $p$; expectations are represented as exact finite weighted sums.
-- source:
--   Ledoux, On Talagrand’s deviation inequalities for product measures, ESAIM Probability and Statistics 1 (1996), pp. 63–87; Klein and Rio, Concentration around the mean for maxima of empirical processes, Annals of Probability 33 (2005), Sections 2–4, pp. 1060–1077; Candès and Romberg, Sparsity and Incoherence in Compressive Sampling, Theorem 3.2 and equation (3.9), PDF p. 12.

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Order.Lattice

open MeasureTheory
open scoped Classical BigOperators

namespace TalagrandCore

variable {κ ι : Type} [DecidableEq κ] [Fintype κ]
variable [DecidableEq ι] [Fintype ι] [Nonempty ι]

noncomputable def hBen (u : ℝ) : ℝ := (1 + u) * Real.log (1 + u) - u

/-- `h(u) ≥ (u/2)·log(1+u)` for `u ≥ 0`. -/

noncomputable def bernPi (κ : Type) [Fintype κ] (p : NNReal) (hp : p ≤ 1) :
    Measure (κ → Bool) :=
  Measure.pi (fun _ : κ => (PMF.bernoulli p hp).toMeasure)

instance (p : NNReal) (hp : p ≤ 1) :
    IsProbabilityMeasure (bernPi κ p hp) := by
  unfold bernPi; infer_instance

/-- On the finite Boolean cube every real-valued function is integrable. -/

def bw (p : ℝ) : Bool → ℝ := fun b => cond b p (1 - p)

/-- Product Bernoulli weight of a point of the Boolean cube. -/

noncomputable def W {κ : Type} [Fintype κ] (p : ℝ) (ω : κ → Bool) : ℝ :=
  ∏ x : κ, bw p (ω x)

/-- Expectation (finite sum) against the product Bernoulli weights. -/

noncomputable def Ex {κ : Type} [DecidableEq κ] [Fintype κ] (p : ℝ) (f : (κ → Bool) → ℝ) : ℝ :=
  ∑ ω : κ → Bool, W p ω * f ω

variable {κ : Type} [DecidableEq κ] [Fintype κ] {p : ℝ}

noncomputable def condEx (p : ℝ) (x : κ) (f : (κ → Bool) → ℝ) (ω : κ → Bool) : ℝ :=
  bw p true * f (Function.update ω x true) +
    bw p false * f (Function.update ω x false)

noncomputable def Wrest (p : ℝ) (x : κ) (ω : κ → Bool) : ℝ :=
  ∏ y ∈ Finset.univ.erase x, bw p (ω y)

noncomputable def psi (u : ℝ) : ℝ := Real.exp (-u) - 1 + u

/-- A function is `x`-fiber constant if it does not depend on coordinate `x`. -/

def FiberConst (x : κ) (c : (κ → Bool) → ℝ) : Prop :=
  ∀ ω t, c (Function.update ω x t) = c ω

/-- Two-point variational entropy bound (the fiber ψ-inequality), proved from
`log x ≤ x − 1`:  for weights `a + b = 1`, `a, b ≥ 0`, values `Z₁ Z₂` and any
constant `c₀`,

  lam(a Z₁ G₁ + b Z₂ G₂) − S log S ≤ a G₁ ψ(lam(Z₁−c₀)) + b G₂ ψ(lam(Z₂−c₀))

where `Gᵢ = e^{lam Zᵢ}` and `S = a G₁ + b G₂`. -/

noncomputable def supProc (g : ι → κ → Bool → ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι => ∑ x : κ, g a x (ω x))

/-- Leave-one-out supremum process (coordinate `x₀` removed). -/

noncomputable def supProcErase (g : ι → κ → Bool → ℝ) (x₀ : κ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => ∑ x ∈ Finset.univ.erase x₀, g a x (ω x))

def linSummand (coeff : ι → κ → ℝ) (p : ℝ) : ι → κ → Bool → ℝ :=
  fun a x b => (cond b (1 : ℝ) 0 - p) * coeff a x

/-- `Z = max_a ∑_x ((ω x) − p) c_a(x)`. -/

noncomputable def Zproc (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) : ℝ :=
  supProc (linSummand coeff p) ω

/-- `Z̄ = max_a |∑_x ((ω x) − p) c_a(x)|`. -/

noncomputable def Zbar (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => |∑ x : κ, (cond (ω x) (1 : ℝ) 0 - p) * coeff a x|)

/-- The random variance process `Σ² = max_a ∑_x c_a(x)²((ω x) − p)²`. -/

noncomputable def Sigma2 (coeff : ι → κ → ℝ) (p : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => ∑ x : κ, coeff a x ^ 2 * (cond (ω x) (1 : ℝ) 0 - p) ^ 2)

/-- One-coordinate two-argmax Lipschitz bound for the linear supremum:
changing coordinate `x` from `ω` to `ω' = update ω x t` moves `Z` by at most
`|ωx − t|·max(|c_{a*(ω)}(x)|, |c_{a*(ω')}(x)|)`, and in particular the move is
bounded by the coefficient of the argmax at either endpoint. -/

def sg (b : Bool) : ℝ := cond b (-1) 1

def mix (s ω ω' : κ → Bool) : κ → Bool := fun x => cond (s x) (ω' x) (ω x)

noncomputable def Vsup (coeff : ι → κ → ℝ) (P : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      P * (1 - P) * coeff a x ^ 2))

/-- Doubled (two-copy) squares-difference process. -/

noncomputable def Dsq (coeff : ι → κ → ℝ) (P : ℝ) (ω ω' : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2))

/-- Signed doubled squares-difference process. -/

noncomputable def Hsq (coeff : ι → κ → ℝ) (P : ℝ) (s ω ω' : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, sg (s x) * (((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2 -
      ((cond (ω' x) (1:ℝ) 0 - P) * coeff a x) ^ 2))

/-- Rademacher squares process. -/

noncomputable def Asq (coeff : ι → κ → ℝ) (P : ℝ) (s ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x) ^ 2)

/-- Rademacher linear process. -/

noncomputable def Alin (coeff : ι → κ → ℝ) (P : ℝ) (s ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun a : ι =>
    ∑ x : κ, sg (s x) * ((cond (ω x) (1:ℝ) 0 - P) * coeff a x))

noncomputable def psiKR (t : ℝ) : ℝ := (Real.exp (2*t) + 1) / 2

/-- Klein–Rio §4.2: `φ(t) = ψ(t)·log ψ(t)`. -/

noncomputable def phiKR (t : ℝ) : ℝ := psiKR t * Real.log (psiKR t)

noncomputable def gKR (x : ℝ) : ℝ :=
  if x = 0 then 1/2 else (1 + (x - 1) * Real.exp x) / x^2

noncomputable def linSum (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (ω : κ → Bool) : ℝ :=
  ∑ x : κ, linSummand coeff p a x (ω x)

/-- Per-coordinate mgf of the negated summand. -/

noncomputable def krM (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  bw p true * Real.exp (-(t * linSummand coeff p a x true)) +
    bw p false * Real.exp (-(t * linSummand coeff p a x false))

/-- Its explicit `t`-derivative. -/

noncomputable def krMd (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  bw p true * (-linSummand coeff p a x true) *
      Real.exp (-(t * linSummand coeff p a x true)) +
    bw p false * (-linSummand coeff p a x false) *
      Real.exp (-(t * linSummand coeff p a x false))

/-- Per-coordinate cgf `krl = log krM`. -/

noncomputable def krl (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  Real.log (krM coeff p a x t)

/-- Its derivative `krld = krMd / krM`. -/

noncomputable def krld (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  krMd coeff p a x t / krM coeff p a x t

/-- Branch cgf `L_a(t) = ∑_x krl a x t = log E e^{−t·S_a}`. -/

noncomputable def krL (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (t : ℝ) : ℝ :=
  ∑ x : κ, krl coeff p a x t

/-- Its derivative. -/

noncomputable def krLd (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (t : ℝ) : ℝ :=
  ∑ x : κ, krld coeff p a x t

/-! ### Two-point averages of the linear summand -/

noncomputable def trSmall (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) (b : Bool) : ℝ :=
  if |linSummand coeff p a x b| ≤ θ then linSummand coeff p a x b else 0

noncomputable def trBig (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) (b : Bool) : ℝ :=
  linSummand coeff p a x b - trSmall coeff p θ a x b

noncomputable def trZ (coeff : ι → κ → ℝ) (p θ : ℝ) (ω : κ → Bool) : ℝ :=
  supProc (trSmall coeff p θ) ω

noncomputable def trW (coeff : ι → κ → ℝ) (p θ : ℝ) (ω : κ → Bool) : ℝ :=
  supProc (fun a x b => |trBig coeff p θ a x b|) ω

noncomputable def trC (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) (x : κ) : ℝ :=
  trSmall coeff p θ a x true - trSmall coeff p θ a x false

noncomputable def trShift (coeff : ι → κ → ℝ) (p θ : ℝ) (a : ι) : ℝ :=
  ∑ x : κ, (bw p true * trSmall coeff p θ a x true + bw p false * trSmall coeff p θ a x false)

/-! ### Basic facts about the big part -/

noncomputable def argmaxFun (F : ι → ℝ) : ι :=
  Classical.choose (Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := ι)) F)

noncomputable def krComp (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => t * linSum coeff p a ω + krL coeff p a t)

/-- `f_t = e^{−M_t}`. -/

noncomputable def krf (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) : ℝ :=
  Real.exp (-(krComp coeff p t ω))

/-- `F(t) = Ex f_t`. -/

noncomputable def krF (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) : ℝ :=
  Ex p (krf coeff p t)

/-- The (first) argmax branch. -/

noncomputable def krTau (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (ω : κ → Bool) : ι :=
  argmaxFun (fun a : ι => t * linSum coeff p a ω + krL coeff p a t)

noncomputable def linSumErase (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ)
    (ω : κ → Bool) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, linSummand coeff p a y (ω y)

/-- `L_a` without coordinate `x`. -/

noncomputable def krLErase (coeff : ι → κ → ℝ) (p : ℝ) (a : ι) (x : κ) (t : ℝ) : ℝ :=
  ∑ y ∈ Finset.univ.erase x, krl coeff p a y t

/-- Leave-one-out compensated maximum. -/

noncomputable def krCompErase (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : ι => t * linSumErase coeff p a x ω + krLErase coeff p a x t)

/-- Leave-one-out argmax. -/

noncomputable def krTauE (coeff : ι → κ → ℝ) (p : ℝ) (x : κ) (t : ℝ)
    (ω : κ → Bool) : ι :=
  argmaxFun (fun a : ι => t * linSumErase coeff p a x ω + krLErase coeff p a x t)

noncomputable def krEta (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (x : κ) (ω : κ → Bool) : ℝ :=
  t * linSummand coeff p (krTau coeff p t ω) x (ω x) +
    krl coeff p (krTau coeff p t ω) x t

/-- Second half of Lemma 4.2: `e^{−krCompErase} ≤ f_t·e^{η_x}`. -/

noncomputable def krFrozen (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (s : ℝ) : ℝ :=
  Ex p (fun ω => Real.exp (-(s * linSum coeff p (krTau coeff p t ω) ω +
    krL coeff p (krTau coeff p t ω) s)))

/-- Its derivative at `s = t`. -/

noncomputable def krFrozenD (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) : ℝ :=
  Ex p (fun ω => -(linSum coeff p (krTau coeff p t ω) ω +
    krLd coeff p (krTau coeff p t ω) t) * krf coeff p t ω)

noncomputable def krInd (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (a : ι)
    (ω : κ → Bool) : ℝ :=
  if krTau coeff p t ω = a then 1 else 0

noncomputable def krC (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (x : κ) (a : ι)
    (ω : κ → Bool) : ℝ :=
  Real.exp (-(t * linSumErase coeff p a x ω + krLErase coeff p a x t))

noncomputable def krg (coeff : ι → κ → ℝ) (p : ℝ) (t : ℝ) (x : κ)
    (ω : κ → Bool) : ℝ :=
  ∑ a : ι, condEx p x (krInd coeff p t a) ω *
    Real.exp (-(t * linSum coeff p a ω + krL coeff p a t))

end TalagrandCore


