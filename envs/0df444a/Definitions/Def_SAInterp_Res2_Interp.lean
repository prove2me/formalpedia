-- Prove2me | Definitions.Def_SAInterp_Res2_Interp
-- name    : SAInterp_Res2_Interp
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:35:45.096751+00:00
-- url     : https://prove2.me/theorems/f72e6cc2-8c39-454b-9c9d-4a400142a96b
-- title:
--   Lagrange basis polynomials and the interpolation weights ω_k^{(m)} = ℓ_k(0) (Theorem 3.1)
-- statement:
--   For distinct real nodes $t_1,\dots,t_m$, the **Lagrange basis polynomial** is
--   $$\ell_i(x)=\prod_{j\in[m],\,j\neq i}\frac{x-t_j}{t_i-t_j}.$$
--   For the nodes $t_k=k$ ($k=1,\dots,m$), the **interpolation weight** is
--   $$\omega^{(m)}_k:=\ell_k(0)=\prod_{j\in[m],\,j\neq k}\frac{-j}{k-j}.$$
--   Theorem 3.1 uses $m=d+1$, and Definition 6.1 uses $m=d+2$.
--
--   **Formalization Note.** `lagrangeBasis t i` takes nodes `t : Fin m → ℝ`, so node $i\in[m]$ is `i - 1`. `omega m k` is the product over `j ∈ [1, m] \ {k}` for a natural number `k`. Division by zero (`a/0 = 0`) can only occur for coinciding nodes, which Theorem 3.1 excludes.
-- source:
--   Acheampong, Davis, Robere, Polynomial Interpolation for Sherali-Adams Lower Bounds, STOC 2027 submission (manuscript sha256 8de0a787…), p. 23, Theorem 3.1 (definitions of ℓ_i and ω_k^{(d+1)})

import Mathlib

namespace SAInterp.Res2

/-!
# Lagrange basis polynomials and the interpolation weights `ω_k^{(m)}`

Acheampong, Davis, Robere, *Polynomial Interpolation for Sherali-Adams Lower Bounds*,
STOC 2027 submission (manuscript sha256 8de0a787…), Theorem 3.1 (p. 23).
Nodes are indexed by `Fin m` (the paper's `i ∈ [m]` is `i − 1`).
-/

open Polynomial

/-- The Lagrange basis polynomial `ℓᵢ(x) = ∏_{j ≠ i} (x − t_j) / (t_i − t_j)` for the nodes
`t : Fin m → ℝ`. -/
noncomputable def lagrangeBasis {m : ℕ} (t : Fin m → ℝ) (i : Fin m) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase i, (X - C (t j)) * C (1 / (t i - t j))

/-- The interpolation weight `ω_k^{(m)} = ℓ_k(0) = ∏_{j ∈ [m], j ≠ k} −j / (k − j)` for the nodes
`t_j = j`, `j = 1, …, m` (Theorem 3.1, with `m = d + 1`). -/
noncomputable def omega (m k : ℕ) : ℝ :=
  ∏ j ∈ (Finset.Icc 1 m).erase k, (-(j : ℝ)) / ((k : ℝ) - j)

end SAInterp.Res2


