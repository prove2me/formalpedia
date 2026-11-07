-- Prove2me | Definitions.Def_QuasiStrictNE_simplicialExt
-- name    : QuasiStrictNE_simplicialExt
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T13:06:56.407726+00:00
-- url     : https://prove2.me/theorems/12719530-4178-42cb-a53e-e4c2da6ea1c2
-- title:
--   Simplicial map on $K(C,p)$ induced by a vertex map
-- statement:
--   Let $C$ be a collection of polytopes, $p$ a selection of points $p_F$, and $f$ a vertex map assigning a point $f(F)$ to every vertex $p_F$. The **simplicial map** induced by $f$ is defined on each simplex by
--   $$
--   g\Bigl(\sum_{t=0}^r \lambda_t\, p_{F_t}\Bigr)=\sum_{t=0}^r \lambda_t\, f(F_t),\qquad \lambda_t\ge 0,\ \sum_t\lambda_t=1,
--   $$
--   for chains $F_0\subsetneq\cdots\subsetneq F_r$ of $C$.
--
--   **Formalization Note** The definition evaluates the formula on one representation of $x$, chosen among all chains and barycentric weights, and returns $0$ if $x$ has none. That the value does not depend on the representation and that $g$ is continuous are theorems (Propositions 1–2 and the four-maps milestone), not part of the definition.
-- source:
--   Hansen & Nie, On Existence and Computational Complexity of Quasi-strict Equilibria, arXiv:2611.06350 (preprint, sha256 c265dace…), Definition 5, p.7

import Mathlib
import Definitions.Def_QuasiStrictNE_IsFaceChain

namespace QuasiStrictNE

open Classical in
/-- **The simplicial map induced by a vertex map on `K(C, p)`** (Hansen & Nie, *On Existence and
Computational Complexity of Quasi-strict Equilibria*, arXiv:2611.06350, Definition 5, p.7: "Define
g : |K| → |L| on each simplex by g(∑ ti vi) = ∑ ti f(vi), ti ≥ 0, ∑ ti = 1").

The vertices of `K(C, p)` are the points `p F`, `F ∈ C`, and the vertex map is given as a function
`f` of the face `F`. If `x = ∑_{F ∈ σ} λ_F p F` for a chain `σ` of members of `C` and barycentric
weights `λ ≥ 0` summing to `1`, then `simplicialExt C p f x = ∑_{F ∈ σ} λ_F f F` for one such
representation (chosen); otherwise the value is `0`.

**Formalization Note** The definition carries no proof obligation: that the value does not depend on
the chosen representation, and that the map is continuous, are theorems (`vertex_maps_extend`,
through Propositions 1–2). The value `0` off `|K(C, p)|` is never used by the theorems, which
evaluate the map on the simplex `Δk = |K(C, p)|`. -/
noncomputable def simplicialExt {d e : ℕ} (C : Set (Set (Fin d → ℝ)))
    (p : Set (Fin d → ℝ) → (Fin d → ℝ)) (f : Set (Fin d → ℝ) → (Fin e → ℝ)) (x : Fin d → ℝ) :
    Fin e → ℝ :=
  if h : ∃ (σ : Finset (Set (Fin d → ℝ))) (w : Set (Fin d → ℝ) → ℝ), IsFaceChain C σ ∧
      (∀ F ∈ σ, 0 ≤ w F) ∧ ∑ F ∈ σ, w F = 1 ∧ x = ∑ F ∈ σ, w F • p F then
    ∑ F ∈ h.choose, h.choose_spec.choose F • f F
  else 0

end QuasiStrictNE


