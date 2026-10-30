-- Prove2me | Definitions.Def_NemirovskiProx_IsProxPointOn
-- name    : NemirovskiProx_IsProxPointOn
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-30T01:43:59.103987+00:00
-- url     : https://prove2.me/theorems/a4b95da3-4e9d-45fd-a262-dd4e6ecff66f
-- title:
--   Prox point $P_z(\xi)$ over a set $U$
-- statement:
--   Let $U\subset E$, $\omega:E\to\mathbb R$, $\omega':E\to E$ and $z,\xi\in E$. A point $p$ is the **prox point of $\xi$ at $z$ over $U$** if
--   $$p\in U\quad\text{and}\quad \omega(p)+\langle p,\xi-\omega'(z)\rangle\le \omega(v)+\langle v,\xi-\omega'(z)\rangle\quad\forall v\in U,$$
--   that is, $p=\operatorname{argmin}_{w\in U}\,[\omega(w)+\langle w,\xi-\omega'(z)\rangle]$.
--
--   With $U=Z$ this is the **prox-mapping** $P_z(\xi)$ of the paper. With $U\subset Z$ and $\xi$ replaced by $\gamma\xi$ it gives the points $w$ and $z_+$ of (3.6) in Lemma 3.1.
--
--   **Formalization Note** The argmin is a predicate. Under the standing assumptions (compact convex $Z$, closed convex nonempty $U\subset Z$, $\omega$ continuous and strongly convex on $Z$) the minimizer exists and is unique.
-- source:
--   Nemirovski, Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems, SIAM J. Optim. 15(1) (2004), 229–251, doi:10.1137/S1052623403425629, §2.2, definition of the prox-mapping P_z, p. 232; eq. (3.6), p. 237

import Mathlib

open scoped InnerProductSpace

namespace NemirovskiProx

/-- **`p` is the prox point of `ξ` at `z` over `U`.**
Nemirovski, *Prox-Method with Rate of Convergence O(1/t) for Variational Inequalities with
Lipschitz Continuous Monotone Operators and Smooth Convex-Concave Saddle Point Problems*,
SIAM J. Optim. 15(1) (2004), §2.2, p. 232: "Given γ and z ∈ Z, let us define the prox-mapping
Pz : E → Z : Pz(ξ) = argmin_{w∈Z} [ω(w) + ⟨w, ξ − ω′(z)⟩]"; and (3.6), p. 237:
"w = argmin_{y∈U} [⟨γξ − ω′(z), y⟩ + ω(y)]".

`IsProxPointOn U ω ω' z ξ p` says `p ∈ U` minimizes `w ↦ ω w + ⟨w, ξ − ω' z⟩` over `U`.
With `U = Z` it says `p = P_z(ξ)`; the points of (3.6) are `IsProxPointOn U ω ω' z (γ • ξ) w`.

**Formalization Note.** The argmin is a predicate. For `U` nonempty, convex and closed inside
the convex compact `Z`, with `ω` continuous and strongly convex on `Z`, the minimizer exists
and is unique, so the predicate determines the paper's point. -/
def IsProxPointOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (U : Set E) (ω : E → ℝ) (ω' : E → E) (z ξ p : E) : Prop :=
  p ∈ U ∧ ∀ v ∈ U, ω p + ⟪p, ξ - ω' z⟫_ℝ ≤ ω v + ⟪v, ξ - ω' z⟫_ℝ

end NemirovskiProx


