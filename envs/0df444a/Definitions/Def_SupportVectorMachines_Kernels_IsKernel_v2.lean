-- Prove2me | Definitions.Def_SupportVectorMachines_Kernels_IsKernel_v2
-- name    : SupportVectorMachines_Kernels_IsKernel_v2
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-10-06T05:19:01.620381+00:00
-- url     : https://prove2.me/theorems/b1ba7d66-2659-4928-b6a7-765f4b71dc1e
-- title:
--   Kernel via a feature map (Definition 4.1, real case) — feature space in the universe of $X$
-- statement:
--   A function $k : X \times X \to \mathbb R$ is a **kernel** on $X$ (Definition 4.1, p. 112, real case) if there are a real Hilbert space $H$ and a **feature map** $\Phi : X \to H$ with $k(x,x') = \langle \Phi(x), \Phi(x')\rangle_H$ for all $x,x' \in X$.
--
--   **Formalization Note.** The retired definition fixed the feature space to Lean's universe $0$ while $X$ ranged over every universe, a Lean artefact that made Theorem 4.16 refutable for an $X$ too large to embed in universe $0$ (the Kronecker kernel on `Ordinal.{0}`). The corrected definition quantifies $H$ over the universe of $X$: the Hilbert space built in the proof of Theorem 4.16 (the completion of the span of the $k(\cdot,x)$) lives there, and any feature space in a larger universe can be replaced by the closed span of $\Phi(X)$, which is isometric to one in the universe of $X$. The book's order $k(x,x') = \langle \Phi(x'),\Phi(x)\rangle$ is the sesquilinear convention for the complex case; the book notes that in the real case the order used here is equivalent.
-- source:
--   Steinwart & Christmann, Support Vector Machines, Springer 2008, p. 112, Definition 4.1 (real case)

import Mathlib

open MeasureTheory

universe u

namespace SupportVectorMachines.Kernels

/-- A function `k : X × X → ℝ` is a **kernel** on `X` (Steinwart & Christmann, *Support Vector
Machines*, Springer 2008, Definition 4.1, p. 112, real case) if there is a real Hilbert space `H`
and a **feature map** `Φ : X → H` with `k(x,x') = ⟪Φ(x), Φ(x')⟫` for all `x, x' ∈ X`. (The book
states this as `k(x,x') = ⟪Φ(x'),Φ(x)⟫`, a sesquilinear-order convention that also covers the
complex case; it notes explicitly, right after Definition 4.1, that in the real case this is
equivalent to the more natural `k(x,x') = ⟪Φ(x),Φ(x')⟫` used here, since the real inner product is
symmetric.) The feature space `H` is quantified over the **same universe as `X`**: the book puts
no size restriction on `H` relative to `X`, and the Hilbert space the book builds in the proof of
Theorem 4.16 (the completion of the span of the functions `k(·,x)`, `x ∈ X`) lives in the universe
of `X`, while any feature space in a larger universe can be replaced by the closed span of
`Φ(X)`, which is isometric to one in the universe of `X`. (The retired module
`Def_SupportVectorMachines_Kernels_IsKernel` fixed `H : Type`, universe `0`, for an `X` of
arbitrary universe, a Lean universe artefact that made Theorem 4.16 refutable for a large `X`.) -/
def IsKernel {X : Type u} (k : X → X → ℝ) : Prop :=
  ∃ (H : Type u) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
    (Φ : X → H), ∀ x x' : X, k x x' = inner (𝕜 := ℝ) (Φ x) (Φ x')

end SupportVectorMachines.Kernels


