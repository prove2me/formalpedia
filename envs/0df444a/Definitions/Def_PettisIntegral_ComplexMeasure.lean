-- Prove2me | Definitions.Def_PettisIntegral_ComplexMeasure
-- name    : PettisIntegral_ComplexMeasure
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-22T15:22:25.699997+00:00
-- url     : https://prove2.me/theorems/9c808f62-2451-46ec-b68f-13903358369d
-- title:
--   Weak integrals and Pettis integrals against a complex measure
-- statement:
--   This file defines **weak integrals** and **Pettis integrals against a complex measure**, extending the definitions for positive measures of `Def_PettisIntegral_Basic`.
--
--   Let $E$ be a topological vector space over $\mathbb C$ (in the applications a Hausdorff locally convex space) with continuous dual $E'$, let $X$ be a measurable space, $\mu$ a complex measure on $X$ (a countably additive $\mathbb C$-valued set function) with total variation $|\mu|$, and $f\colon X\to E$ a function.
--
--   1. $f$ is *weakly $\mu$-integrable* (`PettisIntegral.ComplexWeaklyIntegrable μ f`) if $\varphi\circ f\colon X\to\mathbb C$ is $|\mu|$-integrable for every $\varphi\in E'$.
--   2. The *weak integral* of $f$ (`PettisIntegral.complexWeakIntegral μ f`) is the function on $E'$
--   $$\Bigl\langle\int_X f\,d\mu,\ \varphi\Bigr\rangle=\int_X\langle f(x),\varphi\rangle\,d\mu(x),\qquad\varphi\in E' ,$$
--   a linear form on $E'$, i.e. an element of the algebraic dual $(E')^*$ (the weak completion of $E$), when $f$ is weakly $\mu$-integrable. Here $\int_X g\,d\mu$, for $g\in L^1(|\mu|)$, is the integral of a scalar function against the complex measure $\mu$: the unique continuous linear form on $L^1(|\mu|)$ with $\int_X 1_A\,d\mu=\mu(A)$ (equivalently $\int_X g\,h\,d|\mu|$ for the polar decomposition $d\mu=h\,d|\mu|$, $|h|=1$).
--   3. A vector $a\in E$ is a *Pettis integral* of $f$ against $\mu$ (`PettisIntegral.HasComplexPettisIntegral μ f a`) if $f$ is weakly $\mu$-integrable and
--   $$\varphi(a)=\int_X\varphi(f(x))\,d\mu(x)\qquad\text{for all }\varphi\in E'.$$
--
--   The source develops integration in the sense of Pettis for finite complex Radon measures $\mu$ on a locally compact Hausdorff space (Definition C.4.2.1, with $\|\mu\|=|\mu|(X)$), and uses it for contour integrals of vector-valued holomorphic functions, where the measure $d\xi$ on a curve is complex. These definitions allow the complex-measure forms of the mean value theorem, of Pettis' integrability criterion and of the description of closed absolutely convex hulls by integrals to be stated.
--
--   **Formalization Note.** `μ : MeasureTheory.ComplexMeasure X` is Mathlib's `VectorMeasure X ℂ`, and $|\mu|$ is `μ.variation` (the supremum over finite measurable partitions of $\sum_i|\mu(A_i)|$). The scalar integral against $\mu$ is Mathlib's integral against a vector measure, `MeasureTheory.VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ)` (the pairing $\mathbb C\times\mathbb C\to\mathbb C$ is multiplication); it has the junk value $0$ when $g$ is not integrable for $|\mu|$, so `complexWeakIntegral μ f φ = 0` when $\varphi\circ f\notin L^1(|\mu|)$. As in `Def_PettisIntegral_Basic`, the weak integral is a plain function `StrongDual ℂ E → ℂ`, an element of the product space in which the weak completion is represented; `ComplexWeaklyIntegrable μ f` is by definition `WeaklyIntegrable ℂ μ.variation f`. The definitions are given on an arbitrary measurable space; no topology on $X$ and no regularity of $\mu$ enter the definitions.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 710, §C.4.2 and Definition C.4.2.1 (for a complex Radon measure)

import Mathlib
import Definitions.Def_PettisIntegral_Basic

/-!
# Weak integrals and Pettis integrals against a complex measure

`Def_PettisIntegral_Basic` defines weak integrals and integration in the sense of Pettis against a
positive measure. Here the measure is a complex measure `μ : MeasureTheory.ComplexMeasure X`
(a countably additive `ℂ`-valued set function), `E` is a topological vector space over `ℂ` with
continuous dual `E' = StrongDual ℂ E`, and `f : X → E`.

* `PettisIntegral.ComplexWeaklyIntegrable μ f`: `φ ∘ f` is integrable for the total variation
  `|μ| = μ.variation` for every `φ ∈ E'`.
* `PettisIntegral.complexWeakIntegral μ f`: the weak integral `φ ↦ ∫ φ (f x) dμ(x)`, a function on
  `E'` (an element of the algebraic dual `(E')^*` when `f` is weakly integrable).
* `PettisIntegral.HasComplexPettisIntegral μ f a`: `f` is weakly integrable for `μ` and
  `φ a = ∫ φ (f x) dμ(x)` for every `φ ∈ E'`.

The scalar integral `∫ g dμ` of `g : X → ℂ` against the complex measure `μ` is Mathlib's integral
against a vector measure, `MeasureTheory.VectorMeasure.integral μ g (ContinuousLinearMap.mul ℝ ℂ)`:
the continuous linear extension to `L¹(|μ|)` of `1_A ↦ μ(A)`, with the junk value `0` when `g` is
not integrable for `|μ|`.
-/

open MeasureTheory

namespace PettisIntegral

variable {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E] {X : Type*}
  [MeasurableSpace X]

/-- `f : X → E` is *weakly integrable* for the complex measure `μ` if `φ ∘ f : X → ℂ` is integrable
for the total variation `μ.variation` of `μ`, for every continuous linear form `φ` on `E`. -/
def ComplexWeaklyIntegrable (μ : ComplexMeasure X) (f : X → E) : Prop :=
  WeaklyIntegrable ℂ μ.variation f

/-- The *weak integral* of `f : X → E` against the complex measure `μ`: the function
`φ ↦ ∫ φ (f x) dμ(x)` on the continuous dual of `E`, where the scalar integral against `μ` is
`MeasureTheory.VectorMeasure.integral` for the pairing `ℂ × ℂ → ℂ` given by multiplication. (If
`φ ∘ f` is not integrable for `μ.variation`, the value at `φ` is the junk value `0`.) -/
noncomputable def complexWeakIntegral (μ : ComplexMeasure X) (f : X → E) : StrongDual ℂ E → ℂ :=
  fun φ => VectorMeasure.integral μ (fun x => φ (f x)) (ContinuousLinearMap.mul ℝ ℂ)

/-- `a : E` is a *Pettis integral* of `f : X → E` against the complex measure `μ`: `f` is weakly
integrable for `μ` and `φ a = ∫ φ (f x) dμ(x)` for every continuous linear form `φ` on `E`. -/
def HasComplexPettisIntegral (μ : ComplexMeasure X) (f : X → E) (a : E) : Prop :=
  ComplexWeaklyIntegrable μ f ∧ ∀ φ : StrongDual ℂ E, φ a = complexWeakIntegral μ f φ

@[simp] theorem complexWeakIntegral_apply (μ : ComplexMeasure X) (f : X → E)
    (φ : StrongDual ℂ E) :
    complexWeakIntegral μ f φ =
      VectorMeasure.integral μ (fun x => φ (f x)) (ContinuousLinearMap.mul ℝ ℂ) := rfl

end PettisIntegral


