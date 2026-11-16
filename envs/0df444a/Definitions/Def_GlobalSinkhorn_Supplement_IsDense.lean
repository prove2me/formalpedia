-- Prove2me | Definitions.Def_GlobalSinkhorn_Supplement_IsDense
-- name    : GlobalSinkhorn_Supplement_IsDense
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T05:55:33.354573+00:00
-- url     : https://prove2.me/theorems/a0a24d0c-6b06-40b1-a578-a02cf8c7c5c9
-- title:
--   $(\gamma,\rho)$-dense matrix
-- statement:
--   Let $\gamma,\rho\in(0,1]$. An $n\times n$ matrix $D$ is **$(\gamma,\rho)$-dense** if every row and every column of $D$ contains at least $\lceil\gamma n\rceil$ entries of value at least $\rho$:
--   $$
--   \#\{j: D_{ij}\ge\rho\}\ge\lceil\gamma n\rceil\ \ \forall i,\qquad \#\{i: D_{ij}\ge\rho\}\ge\lceil\gamma n\rceil\ \ \forall j.
--   $$
--   This is the density notion of the dense-input results (Theorems 1.7 and 1.8): above density $1/2$ Sinkhorn–Knopp converges in $O(\log n+\log(1/\varepsilon))$ iterations.
--
--   **Formalization Note** Indices are `Fin n`; $\lceil\gamma n\rceil$ is `Nat.ceil (γ * n)`. The ranges $\gamma,\rho\in(0,1]$ and the entry range ($D\in[0,1]^{n\times n}$ in Theorem 1.7, $(0,1]^{n\times n}$ in Theorem 1.8) are hypotheses or conclusions of the theorems that use the predicate, not part of it.
-- source:
--   He, Global Sinkhorn Convergence and Spectral Stability of Matrix Scaling, manuscript (STOC 2027 submission, sha256 b452ef1311fa669023fddd0c074df8a61571bf17b5712615c09d1495a34034ad), definition of (γ, ρ)-dense, p.4 (used in Theorems 1.7, 1.8, pp.8–9)

import Mathlib

open Matrix

namespace GlobalSinkhorn.Supplement

/-- A matrix `D` is `(γ, ρ)`-dense if every row and every column contains at least `⌈γ n⌉`
entries of value at least `ρ`. He, Global Sinkhorn Convergence and Spectral Stability of Matrix
Scaling, manuscript (STOC 2027 submission, sha256 b452ef13…34ad), p.4 (used in Theorems 1.7
and 1.8, pp.8–9).

**Formalization Note.** Indices `[n]` are `Fin n` (0-based); `⌈γ n⌉` is `Nat.ceil (γ * n)`.
The paper defines density for fixed `γ, ρ ∈ (0, 1]` and `D ∈ [0, 1]^{n×n}`; the parameter range
and the entry range (`[0, 1]` in Theorem 1.7, `(0, 1]` in Theorem 1.8) are stated as hypotheses
or conclusions of each theorem, not inside this predicate. -/
def IsDense {n : ℕ} (γ ρ : ℝ) (D : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  (∀ i, ⌈γ * n⌉₊ ≤ (Finset.univ.filter fun j => ρ ≤ D i j).card) ∧
  (∀ j, ⌈γ * n⌉₊ ≤ (Finset.univ.filter fun i => ρ ≤ D i j).card)

end GlobalSinkhorn.Supplement


