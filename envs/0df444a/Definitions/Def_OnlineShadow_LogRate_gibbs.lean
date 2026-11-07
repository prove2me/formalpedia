-- Prove2me | Definitions.Def_OnlineShadow_LogRate_gibbs
-- name    : OnlineShadow_LogRate_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T04:04:26.166546+00:00
-- url     : https://prove2.me/theorems/31aaedf6-d4e4-41c0-bc9f-8bc5ecba755c
-- title:
--   Gibbs hypothesis $\rho_H=e^{-H}/\mathrm{Tr}(e^{-H})$
-- statement:
--   For a Hermitian $d\times d$ matrix $H$, the Gibbs state
--   $$\rho_H=\frac{e^{-H}}{\mathrm{Tr}(e^{-H})}$$
--   is the matrix multiplicative weights hypothesis maintained by Algorithm 1 (line 8). It is a density matrix when $d\ge1$.
--
--
--   **Formalization Note** $e^{-H}$ is the functional calculus of $\exp$ at $-H$; every $H$ in this mission is Hermitian (a real combination of effects), where this is the matrix exponential.
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Algorithm 1, line 8, p. 11

import Mathlib

namespace OnlineShadow.LogRate

/-- The Gibbs (matrix multiplicative weights) hypothesis `ρ_H = e^{−H} / Tr(e^{−H})`
(Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Algorithm 1, line 8, p.11).

**Formalization Note** `e^{−H}` is the functional calculus `cfc Real.exp (−H)`; every `H` in this
mission is Hermitian (a real combination of effects), where this is the matrix exponential. -/
noncomputable def gibbs {d : ℕ} (H : Matrix (Fin d) (Fin d) ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  ((cfc Real.exp (-H)).trace)⁻¹ • cfc Real.exp (-H)

end OnlineShadow.LogRate


