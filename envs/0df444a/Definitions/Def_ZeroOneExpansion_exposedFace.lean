-- Prove2me | Definitions.Def_ZeroOneExpansion_exposedFace
-- name    : ZeroOneExpansion_exposedFace
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T20:20:18.882196+00:00
-- url     : https://prove2.me/theorems/8256fb93-68f4-474a-80a0-62428401acf6
-- title:
--   Face $F_c(P)$ exposed by a linear functional
-- statement:
--   For a set $P$ and a linear functional $\ell$, the **face exposed by** $\ell$ is the set of maximizers of $\ell$ on $P$:
--   $$F_\ell(P)=\{x\in P:\ \ell(y)\le \ell(x)\ \text{for all } y\in P\}.$$
--   For $P\subseteq\mathbb R^d$ and $c\in\mathbb R^d$ the paper writes $F_c(P)=\{x\in P: c\cdot x=\max_{y\in P}c\cdot y\}$, the case $\ell(x)=c\cdot x$. A face of $P$ is any set of this form.
--
--   **Formalization Note** On a product $\prod_i\mathbb R^{d_i}$ the functional of $c=(c_1,\dots,c_n)$ is $x\mapsto\sum_i c_i\cdot x_i$. The two descriptions of the maximizer set agree whenever the maximum is attained, as on every polytope.
-- source:
--   Yang, 0/1-Polytopes with Exponentially Small Edge Expansion, arXiv:2608.01870 (pdf sha256 53e57bdc2a5505f50b990dfb27d47df0f7d5e2feffc89b808f29d40cff38be53), §2.1, p.3, "the face exposed by c"

import Mathlib

set_option autoImplicit false

namespace ZeroOneExpansion

/-- The **face exposed by a linear functional** `ℓ` (arXiv:2608.01870, §2.1, p.3:
"the face exposed by c is Fc(P) := {x ∈ P : c · x = max_{y∈P} c · y}"): the set of maximizers of
`ℓ` on `P`.

**Formalization Note** `F_c(P)` is `exposedFace P (fun x => c ⬝ᵥ x)` on `ℝ^d`, and
`exposedFace P (fun x => ∑ i, c i ⬝ᵥ x i)` on a product `∏ ℝ^{d_i}`. The set of maximizers is written
`{x ∈ P | ∀ y ∈ P, ℓ y ≤ ℓ x}`, which equals `{x ∈ P : ℓ x = max_P ℓ}` whenever the maximum exists, as
it does for the polytopes of the paper. -/
def exposedFace {E : Type*} (P : Set E) (ℓ : E → ℝ) : Set E :=
  {x | x ∈ P ∧ ∀ y ∈ P, ℓ y ≤ ℓ x}

end ZeroOneExpansion


