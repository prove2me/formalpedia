-- Prove2me | Definitions.Def_CompOT_SinkhornConv_birkhoffEta
-- name    : CompOT_SinkhornConv_birkhoffEta
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T18:54:00.002174+00:00
-- url     : https://prove2.me/theorems/2c869ebc-7c80-45d8-8927-e885616d43e2
-- title:
--   Birkhoff's constant $\eta(K)$ of a positive matrix
-- statement:
--   For an $n\times m$ matrix $K$ with positive entries,
--   $$\eta(K) = \max_{i,j,k,\ell} \frac{K_{i,k}\,K_{j,\ell}}{K_{j,k}\,K_{i,\ell}},$$
--   the maximum running over row indices $i,j$ and column indices $k,\ell$.
--
--   Taking $i=j$ shows $\eta(K)\ge 1$; $\eta(K)=1$ exactly when $K$ has rank one. The constant enters Birkhoff's contraction ratio $\lambda(K)$.
--
--   **Formalization Note** The maximum is a real supremum over the finite index set; every statement of the mission uses $\eta(K)$ for positive $K$ with at least one row and one column, where it is the paper's maximum.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, Theorem 4.1, p. 440 (definition of η(K))

import Mathlib

namespace CompOT.SinkhornConv

/-- **Birkhoff's constant `η(K) = max_{i,j,k,ℓ} (K_{i,k} K_{j,ℓ})/(K_{j,k} K_{i,ℓ})`.**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), Theorem 4.1, p. 440: "η(K) := max_{i,j,k,ℓ} (Ki,kKj,ℓ)/(Kj,kKi,ℓ)".

For `K : Matrix (Fin n) (Fin m) ℝ`, `birkhoffEta K` is the maximum over `i, j ∈ Fin n` and
`k, l ∈ Fin m` of `K i k * K j l / (K j k * K i l)`.

**Formalization Note.** The paper uses `η(K)` only for entrywise positive `K` with `n, m ≥ 1`;
every statement of this mission that uses it assumes or guarantees this, and then the real
supremum over the finite index set is the paper's maximum. -/
noncomputable def birkhoffEta {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) : ℝ :=
  ⨆ i, ⨆ j, ⨆ k, ⨆ l, K i k * K j l / (K j k * K i l)

end CompOT.SinkhornConv


