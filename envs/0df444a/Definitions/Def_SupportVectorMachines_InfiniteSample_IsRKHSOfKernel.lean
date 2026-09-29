-- Prove2me | Definitions.Def_SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
-- name    : SupportVectorMachines_InfiniteSample_IsRKHSOfKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:03:15.149978+00:00
-- url     : https://prove2.me/theorems/18e0a06d-8fca-4b01-acae-176dd51a465a
-- title:
--   H is the reproducing kernel Hilbert space of the kernel k
-- statement:
--   Let $X \ne \emptyset$ and let $H$ be a real Hilbert space realized concretely as a space of
--   functions on $X$ via an injective linear evaluation map $\mathrm{toFun} : H \to (X \to
--   \mathbb R)$ (Steinwart & Christmann, *Support Vector Machines*, Springer 2008,
--   Definition 4.18, p. 118: "$H$ is a $\mathbb K$-Hilbert function space over $X$"). A function
--   $k : X \times X \to \mathbb R$ is a **reproducing kernel** of $H$ if $k(\cdot,x) \in H$ for
--   every $x \in X$ and the **reproducing property**
--
--   $$
--   f(x) = \langle f, k(\cdot,x) \rangle_H
--   $$
--
--   holds for all $f \in H$, $x \in X$. $H$ **is the RKHS of the kernel $k$** here means: $H$
--   consists of functions (the evaluation map is injective) and $k$ is a reproducing kernel of
--   $H$ in this sense.
--
--   By Lemma 4.19 of the book, any Hilbert function space with a reproducing kernel is
--   automatically a reproducing kernel Hilbert space in the book's own sense (Definition
--   4.18(ii): every point-evaluation functional $f \mapsto f(x)$ is continuous, which follows
--   from the reproducing property via Cauchy–Schwarz), so this reproducing-kernel formulation is
--   an equivalent, operative rendering of "$H$ is an RKHS with kernel $k$" — exactly the form used
--   throughout Section 5.1–5.2.
--
--   **Formalization Note** $H$ is existentially quantified as an arbitrary real Hilbert space
--   (`NormedAddCommGroup`, `InnerProductSpace ℝ`, `CompleteSpace`) together with the linear
--   evaluation map `toFun : H →ₗ[ℝ] (X → ℝ)`; injectivity of `toFun` is the Lean rendering of "$H$
--   consists of functions" (distinct elements of $H$ are distinct functions on $X$). Restated
--   locally rather than imported from the `Kernels` chapter draft, per this series' cross-chapter
--   rule.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 119, Definition 4.18 (via Lemma 4.19, p. 120)

import Mathlib

namespace SupportVectorMachines.InfiniteSample

/-- `H` (with evaluation map `toFun : H →ₗ[ℝ] (X → ℝ)`, realizing `H` concretely as a Hilbert
space of functions on `X`, Definition 4.18, p. 118, restated locally per Hard Rule 9) **is the
RKHS of the kernel `k`** if `toFun` is injective (distinct elements of `H` are distinct
functions, i.e. `H` genuinely "consists of functions", Definition 4.18's standing hypothesis) and
`k` is a reproducing kernel of `H` (Definition 4.18(i)): for every `x`, the function `k(·,x)` lies
in `H` (via some `kAt x : H` with `toFun (kAt x) = k(·,x)`), and the reproducing property
`f(x) = ⟨f, k(·,x)⟩` holds for every `f ∈ H` and `x ∈ X`. By Lemma 4.19, a Hilbert function space
with a reproducing kernel is automatically an RKHS (Definition 4.18(ii): every Dirac functional
`f ↦ f(x)` is continuous, via Cauchy-Schwarz applied to the reproducing property), so this
reproducing-kernel formulation is an equivalent, operative rendering of "`H` is an RKHS with
kernel `k`" — the form Theorem 5.5 and its neighbors actually use. -/
def IsRKHSOfKernel {X : Type*} (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (toFun : H →ₗ[ℝ] (X → ℝ)) (k : X → X → ℝ) : Prop :=
  Function.Injective toFun ∧
    ∃ kAt : X → H, (∀ x x' : X, toFun (kAt x) x' = k x x') ∧
      ∀ (f : H) (x : X), toFun f x = inner (𝕜 := ℝ) f (kAt x)

end SupportVectorMachines.InfiniteSample


