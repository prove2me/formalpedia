-- Prove2me | Definitions.Def_SmoothedSimplex_Shadow_rotTo
-- name    : SmoothedSimplex_Shadow_rotTo
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T12:47:23.616252+00:00
-- url     : https://prove2.me/theorems/8d74670e-b970-4d44-bb8e-a74aec908b4b
-- title:
--   §2.5 — the rotation $R_\omega$ taking $q$ to $\omega$
-- statement:
--   Fix a reference unit vector $q\in\mathbb R^d$. For a unit vector $\omega\neq -q$, $R_\omega$ is the linear transformation that rotates $q$ to $\omega$ in the two-dimensional subspace through $q$ and $\omega$ and is the identity on the orthogonal complement of that subspace. Explicitly,
--
--   $$
--   R_\omega x = x-\frac{\langle q+\omega\,|\,x\rangle}{1+\langle q|\omega\rangle}\,(q+\omega)+2\langle q|x\rangle\,\omega .
--   $$
--
--   Together with a coordinatization of $q^\perp\cong\mathbb R^{d-1}$, $R_\omega$ places points $b\in\mathbb R^{d-1}$ on the hyperplane with normal $\omega$; it is the basis of the Blaschke change of variables $a_i=R_\omega b_i+sq$ used throughout Section 4.
--
--   **Formalization Note** The formula is the composition of the reflections in $(q+\omega)^\perp$ and $\omega^\perp$. At $\omega=-q$ (excluded by the paper, a set of measure zero) the division takes Lean's default value $0$.
-- source:
--   Spielman & Teng, Smoothed Analysis of Algorithms, arXiv:cs/0111050v7, §2.5, printed p. 25 (PDF p. 25)

import Mathlib

namespace SmoothedSimplex.Shadow

open scoped RealInnerProductSpace

/-- The rotation `R_ω` (Spielman & Teng, arXiv:cs/0111050v7, §2.5, printed p. 25, PDF p. 25):
for a reference unit vector `q` and a unit vector `ω ≠ −q`, `R_ω` is the linear map that rotates
`q` to `ω` in the two-dimensional subspace through `q` and `ω` and is the identity on its
orthogonal complement. Explicitly,
`R_ω x = x − (⟨q + ω, x⟩ / (1 + ⟨q, ω⟩)) (q + ω) + 2⟨q, x⟩ ω`.

**Formalization Note.** The formula is the composition of the reflections in `(q + ω)^⊥` and
`ω^⊥`; for unit `q, ω` with `ω ≠ −q` it maps `q ↦ ω`, `ω ↦ 2⟨q,ω⟩ω − q`, and fixes every vector
orthogonal to both, which is the paper's description. At `ω = −q` (excluded by the paper, a
measure-zero set) the division returns Lean's junk value `0`. -/
noncomputable def rotTo {d : ℕ} (q ω : EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) :=
  x - (⟪q + ω, x⟫ / (1 + ⟪q, ω⟫)) • (q + ω) + (2 * ⟪q, x⟫) • ω

end SmoothedSimplex.Shadow


