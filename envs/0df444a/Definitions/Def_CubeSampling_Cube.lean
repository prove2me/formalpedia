-- Prove2me | Definitions.Def_CubeSampling_Cube
-- name    : CubeSampling_Cube
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T12:14:06.32333+00:00
-- url     : https://prove2.me/theorems/f486e003-def1-4e9f-848e-24c9619fd05b
-- title:
--   The Boolean cube $\{-1,1\}^d$
-- statement:
--   The **Boolean cube** $\{-1,1\}^d$ is the set of sign vectors $x = (x_1,\dots,x_d)$ with $x_i \in \{-1, 1\}$. All functions, measures and subspaces of the mission live on it.
--
--   **Formalization Note** A point is a map $\mathrm{Fin}\,d \to \mathrm{Bool}$; the value `true` encodes $x_i = 1$ and `false` encodes $x_i = -1$ (see the coordinate map).
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Section 1.1, p.3

import Mathlib

namespace CubeSampling

/-- The Boolean cube `{−1, 1}^d` (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), §1.1, p.3).

**Formalization Note** A point is a map `Fin d → Bool`; the coordinate `x_i ∈ {−1, 1}` is
`+1` when `x i = true` and `−1` when `x i = false` (see `coord`). -/
abbrev Cube (d : ℕ) : Type := Fin d → Bool

end CubeSampling


