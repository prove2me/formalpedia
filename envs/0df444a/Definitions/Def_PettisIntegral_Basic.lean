-- Prove2me | Definitions.Def_PettisIntegral_Basic
-- name    : PettisIntegral_Basic
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T10:48:46.381818+00:00
-- url     : https://prove2.me/theorems/0be7dfa8-5a89-4cff-8a17-624e6d827edb
-- title:
--   Weak integrals and integration in the sense of Pettis (Gelfand–Pettis integral) for functions with values in a topological vector space
-- statement:
--   This file defines **weak integrals** and **integration in the sense of Pettis** (the Gelfand–Pettis integral) for functions with values in a topological vector space.
--
--   Let $\mathbb k$ be $\mathbb R$ or $\mathbb C$, let $E$ be a topological vector space over $\mathbb k$ (in the applications a Hausdorff locally convex space) with continuous dual $E'$, let $(X,\mu)$ be a measure space ($\mu$ a positive measure) and let $f\colon X\to E$ be a function.
--
--   1. $f$ is *weakly measurable* (`PettisIntegral.WeaklyMeasurable 𝕜 μ f`) if $\varphi\circ f\colon X\to\mathbb k$ is $\mu$-measurable for every $\varphi\in E'$.
--   2. $f$ is *weakly $\mu$-integrable* (`PettisIntegral.WeaklyIntegrable 𝕜 μ f`) if $\varphi\circ f$ is $\mu$-integrable for every $\varphi\in E'$. The *weak integral* of $f$ (`PettisIntegral.weakIntegral 𝕜 μ f`) is then the linear form $\int_X f\,d\mu$ on $E'$ given by
--   $$\Bigl\langle\int_X f\,d\mu,\ \varphi\Bigr\rangle=\int_X\langle f(x),\varphi\rangle\,d\mu(x),\qquad\varphi\in E'.$$
--   It is an element of the algebraic dual $(E')^*$ of $E'$.
--   3. The canonical map $\iota_E\colon E\to(E')^*$ (`PettisIntegral.toWeakCompletion 𝕜`) sends $u\in E$ to the linear form $\varphi\mapsto\varphi(u)$. A vector $a\in E$ is a *Pettis integral* of $f$ (`PettisIntegral.HasPettisIntegral 𝕜 μ f a`) if $f$ is weakly $\mu$-integrable and $\iota_E(a)=\int_X f\,d\mu$, that is,
--   $$\varphi(a)=\int_X\varphi(f(x))\,d\mu(x)\qquad\text{for all }\varphi\in E'.$$
--   The function $f$ is *$\mu$-integrable in the sense of Pettis* (`PettisIntegral.PettisIntegrable 𝕜 μ f`) if such a vector $a$ exists, and `PettisIntegral.pettisIntegral 𝕜 μ f` denotes it; it is unique as soon as $E'$ separates the points of $E$, for instance when $E$ is Hausdorff and locally convex. As in the source, only the weak integral over the whole space $X$ is required to be represented by a vector of $E$; some authors call $f$ Pettis integrable only if this holds for the weak integral over every measurable subset of $X$, a stronger condition that is not part of this definition.
--
--   The space $(E')^*$ with the topology $\sigma((E')^*,E')$ of pointwise convergence on $E'$ is called the *weak completion* of $E$. A priori the weak integral only lives there; the theorems of the Pettis theory (the mean value theorem, the integrability of continuous compactly supported functions with values in a quasi-complete space, reflexive targets) decide when it comes from a vector of $E$. The paper specializes these integrals to functions with values in Hilbert spaces and in the space of bounded operators on a Hilbert space with the strong operator topology or the operator-norm topology (Remark C.4.3.13); for non-normable targets Bochner's theory is not available.
--
--   **Formalization Note.** The weak completion is represented inside the product space $\mathbb k^{E'}$: `weakIntegral 𝕜 μ f` and `toWeakCompletion 𝕜 u` are plain functions `StrongDual 𝕜 E → 𝕜`, and the topological notions for the weak completion (closure, compactness, completeness) are those of the function space `StrongDual 𝕜 E → 𝕜` with the product topology. The linear forms on $E'$ are a closed subspace of this product, on which the product topology is $\sigma((E')^*,E')$. "$\mu$-measurable" is `AEMeasurable` and "$\mu$-integrable" is Mathlib's `Integrable` (which includes almost everywhere measurability). If $\varphi\circ f$ is not integrable then `weakIntegral 𝕜 μ f φ` is the junk value $0$ of the Bochner integral, and if $f$ is not Pettis integrable then `pettisIntegral 𝕜 μ f = 0`. The definitions are given on an arbitrary measure space and over `[RCLike 𝕜]`; the source takes $X$ locally compact Hausdorff, $\mu$ a Radon measure and $\mathbb k=\mathbb C$. Only positive measures are covered (the source also integrates against finite complex Radon measures).
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, pp. 709-710, (C.4.1.1), Remark C.4.1.3 and Definition C.4.2.1; classical reference: for the weak completion, A. Grothendieck, Sur certains espaces de fonctions holomorphes. I, J. reine angew. Math. 192 (1953), pp. 35-64, §2 (as cited by the paper in Remark C.4.1.3)

import Mathlib

/-!
# Weak integrals and integration in the sense of Pettis (Gelfand–Pettis integral)

Let `𝕜` be `ℝ` or `ℂ`, let `E` be a topological vector space over `𝕜` (in the applications a
Hausdorff locally convex space) with continuous dual `E' = StrongDual 𝕜 E`, let `(X, μ)` be a
measure space and `f : X → E` a function.

* `PettisIntegral.WeaklyMeasurable 𝕜 μ f`: `φ ∘ f` is `μ`-measurable for every `φ ∈ E'`.
* `PettisIntegral.WeaklyIntegrable 𝕜 μ f`: `φ ∘ f` is `μ`-integrable for every `φ ∈ E'`.
* `PettisIntegral.weakIntegral 𝕜 μ f`: the weak integral `φ ↦ ∫ φ (f x) ∂μ`, a function on `E'`
  (a linear form on `E'`, i.e. an element of the algebraic dual `(E')^*`, when `f` is weakly
  integrable).
* `PettisIntegral.toWeakCompletion 𝕜 u`: the linear form `φ ↦ φ u` on `E'` attached to `u : E`.
* `PettisIntegral.HasPettisIntegral 𝕜 μ f a`: `f` is weakly integrable and
  `φ a = ∫ φ (f x) ∂μ` for every `φ ∈ E'`.
* `PettisIntegral.PettisIntegrable 𝕜 μ f`: some `a : E` is a Pettis integral of `f`.
* `PettisIntegral.pettisIntegral 𝕜 μ f`: a Pettis integral of `f` (`0` if there is none).

The *weak completion* of `E` is the algebraic dual `(E')^*` with the topology `σ((E')^*, E')` of
pointwise convergence on `E'`. It is the closed subspace of linear maps in the product space
`StrongDual 𝕜 E → 𝕜` (product topology), and this is how it is represented here: elements of the
weak completion are functions `StrongDual 𝕜 E → 𝕜`, and closures, compactness, completeness are
taken in the function space `StrongDual 𝕜 E → 𝕜` with its product topology and uniformity.
-/

open MeasureTheory

namespace PettisIntegral

variable (𝕜 : Type*) [RCLike 𝕜] {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
  {X : Type*} [MeasurableSpace X]

/-- `f : X → E` is *weakly measurable* (scalarly measurable) for `μ` if `φ ∘ f : X → 𝕜` is
`μ`-measurable, i.e. almost everywhere equal to a measurable function, for every continuous linear
form `φ` on `E`. -/
def WeaklyMeasurable (μ : Measure X) (f : X → E) : Prop :=
  ∀ φ : StrongDual 𝕜 E, AEMeasurable (fun x => φ (f x)) μ

/-- `f : X → E` is *weakly integrable* (scalarly integrable) for `μ` if `φ ∘ f : X → 𝕜` is
`μ`-integrable for every continuous linear form `φ` on `E`. (Integrability includes
`μ`-measurability.) -/
def WeaklyIntegrable (μ : Measure X) (f : X → E) : Prop :=
  ∀ φ : StrongDual 𝕜 E, Integrable (fun x => φ (f x)) μ

/-- The canonical map `ι_E` of `E` into its weak completion: `u : E` is sent to the linear form
`φ ↦ φ u` on the continuous dual of `E`, regarded as a function `StrongDual 𝕜 E → 𝕜`. -/
def toWeakCompletion (u : E) : StrongDual 𝕜 E → 𝕜 :=
  fun φ => φ u

/-- The *weak integral* of `f : X → E` with respect to `μ`: the function
`φ ↦ ∫ φ (f x) ∂μ` on the continuous dual of `E`. When `f` is weakly integrable it is a linear
form on the continuous dual, i.e. an element of the weak completion of `E`. (If `φ ∘ f` is not
integrable, the value at `φ` is the junk value `0` of the Bochner integral.) -/
noncomputable def weakIntegral (μ : Measure X) (f : X → E) : StrongDual 𝕜 E → 𝕜 :=
  fun φ => ∫ x, φ (f x) ∂μ

/-- `a : E` is a *Pettis integral* (Gelfand–Pettis integral, weak integral with value in `E`) of
`f : X → E` with respect to `μ`: `f` is weakly integrable and `φ a = ∫ φ (f x) ∂μ` for every
continuous linear form `φ` on `E`. -/
def HasPettisIntegral (μ : Measure X) (f : X → E) (a : E) : Prop :=
  WeaklyIntegrable 𝕜 μ f ∧ ∀ φ : StrongDual 𝕜 E, φ a = ∫ x, φ (f x) ∂μ

/-- `f : X → E` is *integrable in the sense of Pettis* for `μ` if it has a Pettis integral in
`E`. Only the weak integral over the whole space `X` is required to be represented by a vector of
`E`; some authors call `f` Pettis integrable only if this holds for the weak integral over every
measurable subset of `X`, a stronger condition that is not part of this definition. -/
def PettisIntegrable (μ : Measure X) (f : X → E) : Prop :=
  ∃ a : E, HasPettisIntegral 𝕜 μ f a

open Classical in
/-- The *Pettis integral* `∫ f dμ ∈ E` of a Pettis integrable function `f : X → E`; by convention
it is `0` when `f` is not Pettis integrable. (When the continuous dual separates the points of
`E`, e.g. when `E` is a Hausdorff locally convex space, the Pettis integral is unique.) -/
noncomputable def pettisIntegral (μ : Measure X) (f : X → E) : E :=
  if h : PettisIntegrable 𝕜 μ f then Classical.choose h else 0

@[simp] theorem toWeakCompletion_apply (u : E) (φ : StrongDual 𝕜 E) :
    toWeakCompletion 𝕜 u φ = φ u := rfl

@[simp] theorem weakIntegral_apply (μ : Measure X) (f : X → E) (φ : StrongDual 𝕜 E) :
    weakIntegral 𝕜 μ f φ = ∫ x, φ (f x) ∂μ := rfl

end PettisIntegral


