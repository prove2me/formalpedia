-- Prove2me | Definitions.Def_SilverRateSC_envSupp
-- name    : SilverRateSC_envSupp
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T03:44:59.161916+00:00
-- url     : https://prove2.me/theorems/6f67bc39-2ffd-4d5a-bf8d-2be0f9ba65d4
-- title:
--   Moreau envelope of a support function, max form
-- statement:
--   For a compact convex set $K\subset\mathbb R^2$ with $0\in K$, the Moreau envelope with parameter $1$ of its support function $\sigma_K$ is
--   $$(\mathrm{env}_1\sigma_K)(x)=\max_{g\in K}\Bigl\{\langle g,x\rangle-\tfrac12\|g\|^2\Bigr\}.$$
--   This definition records the right-hand side. All local hard functions of the paper are of this form, translated.
--
--   **Formalization Note** The value is the real supremum over $K$; every statement using it assumes $K$ compact and nonempty, so the supremum is a maximum and no junk value arises.
-- source:
--   Liu, Ye, Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case, arXiv:2609.26873 (sha256 1e325f28…), Fact A.1, p.29

import Mathlib

open scoped InnerProductSpace

namespace SilverRateSC

/-- **Moreau envelope of a support function, in max form** (Fact A.1):
`(env₁ σ_K)(x) = max_{g ∈ K} {⟨g, x⟩ − ½‖g‖²}` for a compact convex `K ⊂ ℝ²` containing `0`.

Liu, Ye, *Silver Rate Is (Almost) Optimal for Gradient Descent: The Strongly Convex Case*,
arXiv:2609.26873, Fact A.1, p. 29.

**Formalization Note** The value is the real supremum of `g ↦ ⟨g, x⟩ − ½‖g‖²` over `K`. Every
statement using it assumes `K` compact and nonempty (it contains `0`), so the image is a nonempty
compact set of reals and the supremum is the maximum; no junk value arises. -/
noncomputable def envSupp (K : Set (EuclideanSpace ℝ (Fin 2))) (x : EuclideanSpace ℝ (Fin 2)) :
    ℝ :=
  sSup ((fun g => ⟪g, x⟫_ℝ - ‖g‖ ^ 2 / 2) '' K)

end SilverRateSC


