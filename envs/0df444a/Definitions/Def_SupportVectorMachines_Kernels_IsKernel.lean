-- Prove2me | Definitions.Def_SupportVectorMachines_Kernels_IsKernel
-- name    : SupportVectorMachines_Kernels_IsKernel
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T22:57:54.842187+00:00
-- url     : https://prove2.me/theorems/673f8b92-5907-498c-aef4-705ccc355c44
-- title:
--   A kernel via a feature map
-- statement:
--   A function $k : X \times X \to \mathbb R$ is a **kernel** on a non-empty set $X$ (Steinwart &
--   Christmann, *Support Vector Machines*, Springer 2008, Definition 4.1, p. 112, real case) if
--   there is a real Hilbert space $H$ and a **feature map** $\Phi : X \to H$ with
--
--   $$
--   k(x,x') = \langle \Phi(x), \Phi(x') \rangle_H \qquad \text{for all } x, x' \in X.
--   $$
--
--   Neither the feature map nor the feature space are uniquely determined by $k$: the book
--   illustrates this with $X := \mathbb R$, $k(x,x') := xx'$, which admits both the identity
--   feature map on $\mathbb R$ and $\Phi(x) := (x/\sqrt2, x/\sqrt2) \in \mathbb R^2$.
--
--   Kernels are the basic object of the chapter: every reproducing kernel Hilbert space (RKHS)
--   used later in the book is built from a kernel, and a support vector machine is specified by
--   choosing one.
--
--   **Formalization Note** The book states Definition 4.1 for a general field $\mathbb K$ (real
--   or complex), with $k(x,x') = \langle \Phi(x'),\Phi(x)\rangle$ — an order convention needed
--   only because the complex inner product is sesquilinear rather than symmetric. This mission
--   concerns only the real case (Theorem 4.16 itself is real-valued only), and the book notes
--   explicitly, immediately after Definition 4.1, that in the real case the equivalent, more
--   natural order $k(x,x') = \langle \Phi(x),\Phi(x')\rangle$ may be used instead — the order
--   adopted here.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 112, Definition 4.1 (real case)

import Mathlib

open MeasureTheory

namespace SupportVectorMachines.Kernels

/-- A function `k : X × X → ℝ` is a **kernel** on `X` (Steinwart & Christmann, *Support Vector
Machines*, Springer 2008, Definition 4.1, p. 112, real case) if there is a real Hilbert space `H`
and a **feature map** `Φ : X → H` with `k(x,x') = ⟪Φ(x), Φ(x')⟫` for all `x, x' ∈ X`. (The book
states this as `k(x,x') = ⟪Φ(x'),Φ(x)⟫`, sesquilinear-order convention that also covers the
complex case; it notes explicitly, right after Definition 4.1, that in the real case this is
equivalent to the more natural `k(x,x') = ⟪Φ(x),Φ(x')⟫` used here, since the real inner product is
symmetric.) -/
def IsKernel {X : Type*} (k : X → X → ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
    (Φ : X → H), ∀ x x' : X, k x x' = inner (𝕜 := ℝ) (Φ x) (Φ x')

end SupportVectorMachines.Kernels


