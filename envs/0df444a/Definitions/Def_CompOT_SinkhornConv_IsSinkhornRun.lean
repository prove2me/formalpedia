-- Prove2me | Definitions.Def_CompOT_SinkhornConv_IsSinkhornRun
-- name    : CompOT_SinkhornConv_IsSinkhornRun
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-29T23:21:13.269316+00:00
-- url     : https://prove2.me/theorems/f10dad8e-f52c-4931-a197-1f3a4b223c0b
-- title:
--   A run of Sinkhorn's iterations (4.15)
-- statement:
--   Let $K\in\mathbb R^{n\times m}$, $a\in\mathbb R^n$, $b\in\mathbb R^m$. Sequences $(u^{(\ell)})_{\ell\ge0}$ in $\mathbb R^n$ and $(v^{(\ell)})_{\ell\ge0}$ in $\mathbb R^m$ form a **run of Sinkhorn's iterations** if $v^{(0)} = \mathbb 1_m$ and, for every $\ell\ge 0$,
--   $$u^{(\ell+1)} = \frac{a}{K v^{(\ell)}}, \qquad v^{(\ell+1)} = \frac{b}{K^\top u^{(\ell+1)}},$$
--   where the divisions are entrywise.
--
--   Each half-step rescales the coupling $\mathrm{diag}(u)K\mathrm{diag}(v)$ so that one of its two marginals is exact: after the $u$-update the row sums equal $a$, after the $v$-update the column sums equal $b$.
--
--   **Formalization Note** The paper never defines $u^{(0)}$, so the predicate leaves it unconstrained; every statement of the mission about $u^{(\ell)}$ or $P^{(\ell)}$ is for $\ell\ge 1$.
-- source:
--   Peyré, Cuturi, Computational Optimal Transport, Found. Trends Mach. Learn. 11(5–6) (2019), doi:10.1561/2200000073, §4.2, eq. (4.15), pp. 432–433

import Mathlib

open Matrix

namespace CompOT.SinkhornConv

/-- **A run of Sinkhorn's iterations (4.15).**
Peyré, Cuturi, *Computational Optimal Transport*, Found. Trends Mach. Learn. 11(5–6) (2019), §4.2, eq. (4.15), pp. 432–433: "u(ℓ+1) := a/(Kv(ℓ)) and v(ℓ+1) := b/(KTu(ℓ+1)),
initialized with an arbitrary positive vector v(0) = 1m. The division operator used above between
two vectors is to be understood entrywise."

`IsSinkhornRun K a b u v` says: `v 0 = 1` and, for every `ℓ`,
`u (ℓ+1) = a / (K v(ℓ))` and `v (ℓ+1) = b / (Kᵀ u(ℓ+1))`, with entrywise division.

**Formalization Note.** `u 0` is left unconstrained: the paper never defines `u^(0)`, and no
statement of the mission uses it (every statement about `u^(ℓ)` or `P^(ℓ)` is for `ℓ ≥ 1`).
`/` on `Fin n → ℝ` is entrywise division; `1` is the all-ones vector `1_m`. -/
def IsSinkhornRun {n m : ℕ} (K : Matrix (Fin n) (Fin m) ℝ) (a : Fin n → ℝ) (b : Fin m → ℝ)
    (u : ℕ → Fin n → ℝ) (v : ℕ → Fin m → ℝ) : Prop :=
  v 0 = 1 ∧ ∀ ℓ : ℕ, u (ℓ + 1) = a / (K *ᵥ v ℓ) ∧ v (ℓ + 1) = b / (Kᵀ *ᵥ u (ℓ + 1))

end CompOT.SinkhornConv


