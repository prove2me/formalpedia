-- Prove2me | Definitions.Def_ConservativeAD_GradAE_ConservativeField
-- name    : ConservativeAD_GradAE_ConservativeField
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:16.248624+00:00
-- url     : https://prove2.me/theorems/acc0520f-55f6-45cd-b1df-e3c2b18c3e61
-- title:
--   Definitions 1–2: circulation integrands, conservative set-valued fields on $\mathbb R^p$ and their potentials
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a set-valued map, i.e. a map assigning to each $x\in\mathbb R^p$ a subset $D(x)\subseteq\mathbb R^p$, and let $\gamma:[0,1]\to\mathbb R^p$ be a path with derivative $\dot\gamma$. The **max-circulation integrand** and **min-circulation integrand** of $D$ along $\gamma$ are
--
--   $$
--   t\mapsto \max_{v\in D(\gamma(t))}\langle\dot\gamma(t),v\rangle,\qquad t\mapsto \min_{v\in D(\gamma(t))}\langle\dot\gamma(t),v\rangle .
--   $$
--
--   **Definition 1 (conservative field).** $D$ is a *conservative (set-valued) field* if
--
--   1. its graph $\{(x,z): z\in D(x)\}$ is closed in $\mathbb R^p\times\mathbb R^p$;
--   2. every value $D(x)$ is nonempty and compact;
--   3. for every absolutely continuous loop $\gamma:[0,1]\to\mathbb R^p$ (that is, $\gamma(0)=\gamma(1)$) the max-circulation integrand is Lebesgue integrable on $[0,1]$ and
--   $$
--   \int_0^1\max_{v\in D(\gamma(t))}\langle\dot\gamma(t),v\rangle\,dt=0 .
--   $$
--
--   **Definition 2 (potential).** A function $f:\mathbb R^p\to\mathbb R$ is a *potential* for $D$ (equivalently, $D$ is a *conservative field for $f$*) if $D$ is a conservative field and, for every $x\in\mathbb R^p$ and every absolutely continuous path $\gamma:[0,1]\to\mathbb R^p$ joining $0$ to $x$, the max-circulation integrand along $\gamma$ is Lebesgue integrable and
--
--   $$
--   f(x)=f(0)+\int_0^1\max_{v\in D(\gamma(t))}\langle\dot\gamma(t),v\rangle\,dt .
--   $$
--
--   These are the central objects of the conservative-field calculus of Bolte and Pauwels: conservative fields generalize gradients and Clarke subdifferentials of locally Lipschitz functions and model the outputs of nonsmooth automatic differentiation.
--
--   **Formalization Note** $\mathbb R^p$ is `EuclideanSpace ℝ (Fin p)`. A path is a function `ℝ → ℝ^p` that is `AbsolutelyContinuousOnInterval` on $[0,1]$ (Mathlib's $\varepsilon$–$\delta$ definition, equivalent on a compact interval to the paper's "continuous, a.e. differentiable, and the integral of its derivative"); its values outside $[0,1]$ play no role, and $\dot\gamma$ is `deriv γ`, which exists almost everywhere on $[0,1]$. The maximum (minimum) is `sSup` (`sInf`) of the image of the compact nonempty set $D(\gamma(t))$, hence an attained maximum (minimum). Because Lean's integral of a non-integrable function is $0$, the integrability of the circulation is required explicitly in both definitions; the paper's phrase "the integral is understood in the Lebesgue sense" presupposes it. Definition 2 is stated in the paper's form (2) with base point $0$; the equivalent forms (3)–(4) and the min-form of Definition 1 are results (Remarks 1 and 3(a)), not part of the definitions.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 4, §2 Notations; p. 5, Lemma 1; p. 6, Definition 1; p. 7, Definition 2, eq. (2)

import Mathlib
open MeasureTheory

namespace ConservativeAD.GradAE

/-- The max-circulation integrand of a set-valued map `D : ℝ^p ⇒ ℝ^p` along a path `γ`:
`t ↦ max_{v ∈ D(γ t)} ⟨γ̇ t, v⟩` (Bolte–Pauwels, Lemma 1 / Definition 1). The maximum is
written as `sSup` of the image of the compact set `D (γ t)` under the continuous map
`v ↦ ⟪γ̇ t, v⟫`; `γ̇` is `deriv γ`, which exists for almost every `t ∈ [0, 1]` when `γ` is
absolutely continuous. -/
noncomputable def circ {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (γ : ℝ → EuclideanSpace ℝ (Fin p)) (t : ℝ) : ℝ :=
  sSup ((fun v => inner ℝ (deriv γ t) v) '' D (γ t))

/-- The min-circulation integrand `t ↦ min_{v ∈ D(γ t)} ⟨γ̇ t, v⟩` (Definition 1, Remark 3(a)). -/
noncomputable def circMin {p : ℕ}
    (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (γ : ℝ → EuclideanSpace ℝ (Fin p)) (t : ℝ) : ℝ :=
  sInf ((fun v => inner ℝ (deriv γ t) v) '' D (γ t))

/-- Definition 1 (conservative set-valued field). `D` has closed graph in `ℝ^p × ℝ^p`,
nonempty compact values, and along every absolutely continuous loop `γ : [0, 1] → ℝ^p`
(`γ 0 = γ 1`) the max-circulation is Lebesgue integrable on `[0, 1]` with integral `0`. -/
def IsConservative {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p))) :
    Prop :=
  IsClosed {z : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin p) | z.2 ∈ D z.1} ∧
  (∀ x, (D x).Nonempty ∧ IsCompact (D x)) ∧
  ∀ γ : ℝ → EuclideanSpace ℝ (Fin p), AbsolutelyContinuousOnInterval γ 0 1 → γ 0 = γ 1 →
    IntervalIntegrable (circ D γ) volume 0 1 ∧ ∫ t in (0:ℝ)..1, circ D γ t = 0

/-- Definition 2, form (2) (potential of a conservative field). `D` is a conservative field and
for every `x` and every absolutely continuous path `γ : [0, 1] → ℝ^p` joining `0` to `x`,
the max-circulation along `γ` is integrable and `f x = f 0 + ∫₀¹ max_{v ∈ D(γ t)} ⟨γ̇ t, v⟩ dt`. -/
def IsPotential {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) : Prop :=
  IsConservative D ∧
  ∀ (x : EuclideanSpace ℝ (Fin p)) (γ : ℝ → EuclideanSpace ℝ (Fin p)),
    AbsolutelyContinuousOnInterval γ 0 1 → γ 0 = 0 → γ 1 = x →
      IntervalIntegrable (circ D γ) volume 0 1 ∧ f x = f 0 + ∫ t in (0:ℝ)..1, circ D γ t

end ConservativeAD.GradAE


