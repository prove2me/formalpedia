-- Prove2me | Definitions.Def_PolySphereLP_V0
-- name    : PolySphereLP_V0
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:56:26.014221+00:00
-- url     : https://prove2.me/theorems/e834df4d-c125-4fe8-9a48-3c703411fc59
-- title:
--   The paired isotropic embedding $V_0:\mathbb C^m\to\mathbb C^n$
-- statement:
--   With $m=\lfloor n/2\rfloor$,
--   $$V_0z=\frac1{\sqrt2}\,(z_1,\,iz_1,\,z_2,\,iz_2,\,\dots,\,z_m,\,iz_m,\,0,\dots,0).$$
--   It satisfies $V_0^*V_0=I_m$ and $V_0^\top V_0=0$ (57), so its image lies in the complex null cone.
--
--   **Formalization Note** As a matrix: column $l$ has $1/\sqrt2$ in row $2l$ and $i/\sqrt2$ in row $2l+1$ (indices from $0$), and zeros elsewhere; for odd $n$ the last row is zero.
-- source:
--   Ghosh, Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation Hierarchy (manuscript, sha256 b9e9c812…), (56)–(57), p.28

import Mathlib

namespace PolySphereLP

/-- **The paired isotropic embedding `V₀ : ℂ^m → ℂⁿ`, `m = ⌊n/2⌋`.** Ghosh, *Hardness of Approximation for Polynomial Optimization over Sphere for LP Relaxation
Hierarchy* (manuscript, sha256 b9e9c812…), (56), p.28:
`V₀z = (1/√2)(z₁, iz₁, z₂, iz₂, …, z_m, iz_m, 0, …, 0)`, so that `V₀*V₀ = I_m` and `V₀ᵀV₀ = 0` (57).

As an `n × m` matrix: column `l` has `1/√2` in row `2l`, `i/√2` in row `2l+1`, and `0` elsewhere
(0-based indices).

**Formalization Note.** `m = n / 2` is natural-number division, i.e. `⌊n/2⌋`; for odd `n` the last
row is zero. -/
noncomputable def V0 (n : ℕ) : Matrix (Fin n) (Fin (n / 2)) ℂ :=
  Matrix.of fun i l =>
    if (i : ℕ) = 2 * (l : ℕ) then ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else if (i : ℕ) = 2 * (l : ℕ) + 1 then Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)
    else 0

end PolySphereLP


