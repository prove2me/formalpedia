-- Prove2me | Definitions.Def_ScutaruFid_IsKernelOperator
-- name    : ScutaruFid_IsKernelOperator
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T17:56:51.029689+00:00
-- url     : https://prove2.me/theorems/2c2846db-b498-48c2-9e1e-15a948fba3e4
-- title:
--   Integral operator with kernel $K(x,y)=\langle x|T|y\rangle$
-- statement:
--   Let $T$ be a bounded operator on $L^2(\mathbb R)$ and $K:\mathbb R\times\mathbb R\to\mathbb C$ a function. $T$ is the **integral operator with kernel** $K$, written $\langle x|T|y\rangle=K(x,y)$, if for every $\psi\in L^2(\mathbb R)$
--
--   $$
--   (T\psi)(x)=\int_{-\infty}^{+\infty}K(x,y)\,\psi(y)\,dy\qquad\text{for almost every }x\in\mathbb R .
--   $$
--
--   This is the paper's coordinate representation (2) of a density operator; every state, square root and product in the paper is described by its kernel.
--
--   **Formalization Note** The definition is a property of $T$, not a construction: it determines $T$ uniquely when it holds. Theorems "for every $T$ with kernel $K$" are paired in the mission with an existence statement (`displaced_state_kernel`, clause 1). The integral is the Lebesgue (Bochner) integral.
-- source:
--   Scutaru, Fidelity for displaced squeezed thermal states and the oscillator semigroup, arXiv:quant-ph/9708013v1, eq. (2), p.1

import Mathlib
import Definitions.Def_ScutaruFid_L2R

open MeasureTheory

namespace ScutaruFid

/-- **Integral operator with kernel `K`**, eq. (2). Scutaru, arXiv:quant-ph/9708013v1, eq. (2),
p.1: "The most general Gaussian density operator in coordinate representation is an integral
operator: (ρψ)(x) = ∫_{−∞}^{+∞} <x|ρ|y> ψ(y) dy".

`IsKernelOperator T K` says that the bounded operator `T` on `L²(ℝ)` acts on every `ψ ∈ L²(ℝ)`
by `(Tψ)(x) = ∫ K(x, y) ψ(y) dy` for almost every `x`. The function `K(x, y)` is the paper's
`<x|T|y>`.

**Formalization Note** A characterization by an almost-everywhere formula: it determines `T`
uniquely, and it is a property of `T` (not a construction), so a theorem "for every `T` realizing
`K`" is accompanied in this mission by an existence clause (`displaced_state_kernel` (i)). The
integral is Lebesgue's (Bochner) integral over `ℝ`. -/
def IsKernelOperator (T : L2R →L[ℂ] L2R) (K : ℝ → ℝ → ℂ) : Prop :=
  ∀ ψ : L2R, (T ψ : ℝ → ℂ) =ᵐ[volume] fun x => ∫ y, K x y * ψ y

end ScutaruFid


