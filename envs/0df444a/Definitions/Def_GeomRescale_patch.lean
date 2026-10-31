-- Prove2me | Definitions.Def_GeomRescale_patch
-- name    : GeomRescale_patch
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T04:13:50.43385+00:00
-- url     : https://prove2.me/theorems/99722174-7e21-4b3f-8824-6c4892c087bf
-- title:
--   Line 9 of Algorithm 1
-- statement:
--   Line 9 adds $\delta$ to $g_k(v_1)$ and subtracts $\delta$ from $g_k(v_n)$, where $v_1$ and $v_n$ are the first and last elements of the order. The patched vector is the extreme base of $B(f_{\mu + \delta})$ for the same order.
--
--   The two assignments are sequential, so for $n = 1$ they cancel.
-- source:
--   Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, line 9, p.8

import Mathlib

namespace GeomRescale

/-- Line 9 of Algorithm 1 (Dadush, Végh & Zambelli, Geometric Rescaling Algorithms for Submodular Function Minimization, arXiv:1707.05065v4, Algorithm 1, p.8): `g_k(v₁) := g_k(v₁) + δ`,
`g_k(v_n) := g_k(v_n) − δ`, where `v₁`, `v_n` are the first and last elements of the order `σ`.

**Formalization Note.** The two assignments are sequential, so for `n = 1`, where `v₁ = v_n`, they
cancel. The formula gives that. -/
def patch {n : ℕ} (σ : Equiv.Perm (Fin n)) (δ : ℝ) (g : Fin n → ℝ) : Fin n → ℝ :=
  fun v => g v + (if (σ v : ℕ) = 0 then δ else 0) - (if (σ v : ℕ) + 1 = n then δ else 0)

end GeomRescale


