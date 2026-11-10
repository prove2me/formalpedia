-- Prove2me | Definitions.Def_QThermalClassical_gibbs
-- name    : QThermalClassical_gibbs
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:11:30.198647+00:00
-- url     : https://prove2.me/theorems/ed63b5d6-86bf-4f95-a841-5e7f3be45059
-- title:
--   Gibbs state $\rho_\beta(H)=e^{-\beta H}/\mathrm{Tr}\,e^{-\beta H}$
-- statement:
--   For an operator $H$ and a real inverse temperature $\beta$, the **Gibbs state** is
--   $$
--   \rho_\beta(H)=\frac{e^{-\beta H}}{\mathrm{Tr}\left(e^{-\beta H}\right)}
--   $$
--   (eq. (6)), with $e^{-\beta H}$ the matrix exponential.
--
--   **Formalization Note** For Hermitian $H$ the trace is a positive real, so the normalization never divides by zero.
-- source:
--   J. Cotler, H. Putterman, A. Zlokapa, When quantum thermal states look classical, arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (6), p.11

import Mathlib
import Definitions.Def_QThermalClassical_pauliOp

set_option autoImplicit false

namespace QThermalClassical

/-- The Gibbs state `ρ_β(H) = e^{−βH} / Tr(e^{−βH})` of eq. (6).

Source: J. Cotler, H. Putterman, A. Zlokapa, *When quantum thermal states look classical*,
arXiv:2607.28536 (held version, sha256 7491d0b2…), §2.1, eq. (6), p.11.

**Formalization Note.** `e^{−βH}` is `NormedSpace.exp` of the matrix `(−β) • H`. For a
Hermitian `H` the trace of `e^{−βH}` is a positive real, so the inverse is never the junk
value `0⁻¹`. -/
noncomputable def gibbs {Q : Type} [Fintype Q] [DecidableEq Q] (H : Op Q) (β : ℝ) : Op Q :=
  let E := NormedSpace.exp (((-β : ℝ) : ℂ) • H)
  E.trace⁻¹ • E

end QThermalClassical


