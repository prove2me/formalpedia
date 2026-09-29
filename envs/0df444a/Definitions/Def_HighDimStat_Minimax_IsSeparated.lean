-- Prove2me | Definitions.Def_HighDimStat_Minimax_IsSeparated
-- name    : HighDimStat_Minimax_IsSeparated
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-19T23:32:46.305448+00:00
-- url     : https://prove2.me/theorems/3a9802bf-5eb6-4492-8cde-3b309051d0ac
-- title:
--   A 2-delta-separated set in the semi-metric rho
-- statement:
--   This predicate says $\{\theta_1,\dots,\theta_M\}$ is a **`2δ`-separated set** in the
--   semi-metric $\rho$, the packing-set condition underlying every lower-bound technique of
--   Chapter 15.
--
--   For $\rho:\Omega\times\Omega\to[0,\infty)$, $\theta_1,\dots,\theta_M \in \Omega$, and
--   $\delta \in \mathbb R$,
--
--   $$
--   \{\theta_1,\dots,\theta_M\} \text{ is } 2\delta\text{-separated} \;:\Longleftrightarrow\;
--   \forall j\ne k,\ \rho(\theta_j,\theta_k) \ge 2\delta.
--   $$
--
--   **Formalization Note** Matches the book's own footnote convention exactly: only the
--   non-strict inequality `≥ 2δ` is required (not the strict inequality of a packing set in the
--   usual sense), "convenient in later calculations" per the book's own remark.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 487 (PDF p. 507)

import Mathlib

namespace HighDimStat.Minimax

/-- `{θ₁,…,θ_M}` is a **`2δ`-separated set** in the semi-metric `ρ`, Wainwright,
*High-Dimensional Statistics* (2019), p. 487: every pair of distinct elements is at
`ρ`-distance at least `2δ`. -/
def IsSeparated {Ω : Type*} {M : ℕ} (ρ : Ω → Ω → ℝ) (θs : Fin M → Ω) (δ : ℝ) : Prop :=
  ∀ j k : Fin M, j ≠ k → 2 * δ ≤ ρ (θs j) (θs k)

end HighDimStat.Minimax


