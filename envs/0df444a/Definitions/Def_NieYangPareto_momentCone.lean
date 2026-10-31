-- Prove2me | Definitions.Def_NieYangPareto_momentCone
-- name    : NieYangPareto_momentCone
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:02:00.635793+00:00
-- url     : https://prove2.me/theorems/cfe913c9-3a47-4849-a439-c95eaa1c9a84
-- title:
--   The moment cone $\mathscr R_d(K)$ of (2.2)
-- statement:
--   For a set $K\subseteq\mathbb R^n$ and a degree $d$, the **moment cone** is
--
--   $$
--   \mathscr R_d(K):=\Big\{y\in\mathbb R^{\mathbb N^n_d}:\ \exists\,\mu,\ y=\int[x]_d\,\mathrm d\mu,\ \operatorname{supp}(\mu)\subseteq K\Big\},
--   $$
--
--   where $\mu$ ranges over Borel measures on $\mathbb R^n$. A vector $y$ in this cone is the list of moments up to degree $d$ of a measure carried by $K$; $y_0$ is its mass.
--
--   **Formalization Note** The equation $y=\int[x]_d\,\mathrm d\mu$ is stated as: every monomial of degree at most $d$ is $\mu$-integrable and $y_\alpha=\int x^\alpha\,\mathrm d\mu$. The clause for $\alpha=0$ makes $\mu$ finite.
-- source:
--   Nie–Yang, The multi-objective polynomial optimization, arXiv:2108.04336v2, eq. (2.2), p.5

import Mathlib
import Definitions.Def_NieYangPareto_Tms

namespace NieYangPareto

open MeasureTheory

/-- **The moment cone (2.2).** Nie–Yang, arXiv:2108.04336v2, eq. (2.2), p.5:
`ℛ_d(K) = {y ∈ ℝ^{ℕⁿ_d} : ∃ μ, y = ∫ [x]_d dμ, supp(μ) ⊆ K}`, with `μ` a Borel measure on `ℝⁿ`.

**Formalization Note** The σ-algebra of `Fin n → ℝ` is the product one, which is the Borel one. "`y =
∫ [x]_d dμ`" means that each monomial of degree at most `d` is `μ`-integrable with integral `y_α`;
the `Integrable` clause is what stops Lean's junk value `∫ = 0` from entering. Taking `α = 0` makes
`μ` finite. -/
def momentCone {n : ℕ} (K : Set (Fin n → ℝ)) (d : ℕ) : Set (Tms n d) :=
  {y | ∃ μ : Measure (Fin n → ℝ), μ.support ⊆ K ∧
    ∀ α : TmsIndex n d,
      Integrable (fun x => monomialValue x α.1) μ ∧ y α = ∫ x, monomialValue x α.1 ∂μ}

end NieYangPareto


