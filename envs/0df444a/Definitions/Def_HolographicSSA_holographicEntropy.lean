-- Prove2me | Definitions.Def_HolographicSSA_holographicEntropy
-- name    : HolographicSSA_holographicEntropy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T05:32:55.340507+00:00
-- url     : https://prove2.me/theorems/8fb7f487-c26b-4f67-aa25-bb724f96f9a0
-- title:
--   Holographic entanglement entropy $S(A)=\frac{1}{4G_N}\min_{m}a(m)$ with the homology rule
-- statement:
--   Let $X$ be a topological space carrying a measure $\mu$; $X$ plays the role of the constant-time slice of the bulk, cut off at a finite value of the holographic coordinate, and $\mu$ the role of the area functional $a$. Let $\Gamma\subseteq X$ be the conformal-boundary part of $X$ (the cutoff surface), on which the field theory lives, let $G>0$ be Newton's constant $G_N$, and let $\mathcal R$ be a class of subsets of $X$, the admissible **bulk regions**.
--
--   For a set $A\subseteq X$ (a boundary region), a region $r\in\mathcal R$ is **homologous to $A$** when it meets the boundary exactly in $A$, i.e. $r\cap\Gamma=A$; its surface is its topological frontier $\partial r$ in $X$, which is $A$'s boundary $\partial A$ together with the bulk hypersurface $m$ with $\partial r=A\cup m$. The **holographic entanglement entropy** of $A$ is
--   $$
--   S(A)=\frac{1}{4G}\,\inf\bigl\{\mu(\partial r)\;:\;r\in\mathcal R,\ r\cap\Gamma=A\bigr\}\in[0,\infty],
--   $$
--   with $S(A)=\infty$ when no admissible region is homologous to $A$.
--
--   This is the Ryu–Takayanagi formula (2.1) with Fursaev's homology rule, the object whose strong subadditivity the paper proves.
--
--   **Formalization Note** The bulk is an arbitrary topological space and the area an arbitrary measure; the intended instance is a static Riemannian slice with the Riemannian area, a constant multiple of the $(d-1)$-dimensional Hausdorff measure $\mu_H^{d-1}$. The paper's minimum is the infimum in $[0,\infty]$, which is the minimum whenever a minimizer exists. The full frontier in $X$ is charged, not only its part off $\Gamma$; charging only the part off $\Gamma$ would let $r=A$ cost nothing. The coefficient $1/(4G_N)$ is `ENNReal.ofReal (1 / (4 * G))`.
-- source:
--   Headrick, Takayanagi, A holographic proof of the strong subadditivity of entanglement entropy, arXiv:0704.3719v1, eq. (2.1), p.3 (PDF p.4), and the homology rule, p.5 (PDF p.6)

import Mathlib

open MeasureTheory
open scoped ENNReal

namespace HolographicSSA

/-- **Holographic entanglement entropy** (Headrick, Takayanagi, *A holographic proof of the strong
subadditivity of entanglement entropy*, arXiv:0704.3719v1, eq. (2.1), p.3, and the homology rule,
p.5).

Eq. (2.1), p.3: "We consider all hypersurfaces m in the bulk that end on ∂A, and ask for the one
with minimal area. (See Figure 1.) We then have S(A) = 1/4GN min m:∂m=∂A a(m) , (2.1) where a(m)
is the area of m."

Homology rule, p.5: "Fursaev's derivation of (2.1) then tells us that we should minimize a not over
all hypersurfaces ending on ∂A but only over those that are homologous to A; that is, there should
exist a region r of the bulk such that ∂r = A∪m."

For a set `A ⊆ X`,
`holographicEntropy Γ μ G 𝓡 A = (1/(4G)) · inf { μ (frontier r) | r ∈ 𝓡, r ∩ Γ = A }`,
with the infimum taken in `[0, ∞]` (it is `∞` when no admissible region `r` has `r ∩ Γ = A`).

**Formalization Note**
* `X` is the cut-off constant-time slice of the bulk (pp.3–5), as an arbitrary topological space,
  and `Γ ⊆ X` is its conformal-boundary (cutoff) part, on which the boundary regions `A` live.
* A bulk region `r` is a member of the admissible class `𝓡 : Set (Set X)` (left arbitrary; the
  theorems state the closure properties they use). The surface of `r` is its topological
  `frontier r` in `X`, and the homology rule `∂r = A ∪ m` is encoded by `r ∩ Γ = A`: the region
  meets the boundary exactly in `A`, and the bulk surface `m` of `r` is the rest of its frontier.
  The full frontier in `X` is charged (it differs from `m` by `∂A ⊆ Γ`, which has zero area in the
  intended instance).
* The area `a` is an arbitrary measure `μ` on `X`; the intended instance is the Riemannian area of
  the slice, a constant multiple of the `(d-1)`-dimensional Hausdorff measure `μH[d-1]`. Theorems
  about it assume `[OpensMeasurableSpace X]`, so that frontiers (closed sets) are measurable.
* The paper's `min` is the infimum `⨅` in `ℝ≥0∞`, which equals the minimum whenever a minimizer
  exists.
* The coefficient `1/(4G_N)` is `ENNReal.ofReal (1 / (4 * G))`; theorems assume `0 < G`. -/
noncomputable def holographicEntropy {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (Γ : Set X) (μ : Measure X) (G : ℝ) (𝓡 : Set (Set X)) (A : Set X) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (4 * G)) * ⨅ r ∈ 𝓡, ⨅ (_ : r ∩ Γ = A), μ (frontier r)

end HolographicSSA


