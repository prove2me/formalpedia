-- Prove2me | Definitions.Def_IntConeFPT_fracMerge
-- name    : IntConeFPT_fracMerge
-- status  : Definition
-- author  : @ohnesorgefelix
-- created : 2026-11-26T13:23:33.235679+00:00
-- url     : https://prove2.me/theorems/93bfbc74-cd5a-4871-b2c6-dc65f86c0c99
-- title:
--   Merging a fractional representation by integer coordinates (proof of Lemma 5)
-- statement:
--   Let $L=((x_1,u_1,\theta_1),\dots,(x_m,u_m,\theta_m))$ be a list of weighted generators with $x_i\in\mathbb Z^d$, $u_i\in\mathbb Q^k$ and $\theta_i\in\mathbb Q$. The list $\mathrm{fracMerge}(L)$ combines all entries with the same integer coordinates. For each integer vector $x$ that occurs in $L$, with index set $J_x=\{i : x_i=x\}$, it contains the single entry
--   $$\Bigl(x,\ \frac{\sum_{i\in J_x}\theta_i u_i}{\sum_{i\in J_x}\theta_i},\ \sum_{i\in J_x}\theta_i\Bigr).$$
--   This is the averaging step in the proof of Lemma 5: "Combine generators with the same integer coordinates by averaging their continuous coordinates with their fractional multiplicities as weights."
--
--   The list is computed by folding `fracMergeInsert` from the right. `fracMergeInsert` $(x,u,\theta)$ either merges the entry into an existing entry $(x,u',\theta')$, replacing it by $(x,(\theta'u'+\theta u)/(\theta'+\theta),\theta'+\theta)$, or appends it. Repeated pairwise averaging gives the weighted average displayed above. The formula is meaningful when all multiplicities are positive, which is the case where it is used.
-- source:
--   Jansen–Ohnesorge–Schumacher, A Constructive FPT Algorithm for Integer Cone Optimization with Convex Costs, arXiv:2609.31328 (preprint), proof of Lemma 5, Section B.1, p.36

import Mathlib

namespace IntConeFPT

/-- **Insert one weighted generator `(x, u, θ)` into a merged list** (proof of Lemma 5, p.36:
"Combine generators with the same integer coordinates by averaging their continuous coordinates
with their fractional multiplicities as weights").

If the list already has an entry `(x, u', θ')` with the same integer coordinates `x`, that entry
becomes `(x, (θ' u' + θ u) / (θ' + θ), θ' + θ)`; otherwise `(x, u, θ)` is appended at the end. -/
def fracMergeInsert {d k : ℕ} (e : (Fin d → ℤ) × (Fin k → ℚ) × ℚ) :
    List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ) → List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)
  | [] => [e]
  | h :: l =>
    if h.1 = e.1 then
      (h.1, (fun j => (h.2.2 * h.2.1 j + e.2.2 * e.2.1 j) / (h.2.2 + e.2.2)), h.2.2 + e.2.2) :: l
    else h :: fracMergeInsert e l

/-- **Merging a fractional representation by integer coordinates** (proof of Lemma 5, p.36).
`fracMerge L` folds `fracMergeInsert` over `L` (from the right). For positive multiplicities the
result has one entry per distinct integer coordinate vector `x` occurring in `L`: its multiplicity
is the total multiplicity `Σ θ_i` of the entries with that `x`, and its continuous coordinates are
the weighted average `Σ θ_i u_i / Σ θ_i`. -/
def fracMerge {d k : ℕ} (L : List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ)) :
    List ((Fin d → ℤ) × (Fin k → ℚ) × ℚ) :=
  L.foldr fracMergeInsert []

end IntConeFPT


