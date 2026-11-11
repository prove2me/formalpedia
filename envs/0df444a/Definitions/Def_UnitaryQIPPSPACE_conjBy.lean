-- Prove2me | Definitions.Def_UnitaryQIPPSPACE_conjBy
-- name    : UnitaryQIPPSPACE_conjBy
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:26:58.084869+00:00
-- url     : https://prove2.me/theorems/de80cfd1-de5b-469f-af91-c570b51cd82d
-- title:
--   The unitary channel $\mathcal U(\rho)=U\rho U^\dagger$
-- statement:
--   For a matrix $U$ (unitary in every use, or an isometry), the map $\mathcal U(\rho)=U\rho U^\dagger$ ("the map $\mathrm{Ad}_X:\rho\mapsto X\rho X^\dagger$ is abbreviated by calligraphic $\mathcal X(\cdot)$ if $X$ is unitary"). It is the target channel of every synthesis statement and the action of gates and provers.
-- source:
--   He, Ou, Zhao, unitaryQIP = unitaryPSPACE, arXiv:2611.02819 (held version, sha256 9e357a00…ead793), §2 (notation), p.9 (PDF p.11)

import Mathlib

open Matrix

namespace UnitaryQIPPSPACE

/-- The **unitary channel** `𝒰(ρ) = U ρ U†` (He, Ou, Zhao, *unitaryQIP = unitaryPSPACE*,
arXiv:2611.02819, held version sha256 9e357a00…, §2, p. 9 (PDF p. 11): "The map `Ad_X : ρ ↦ XρX†` is
abbreviated by calligraphic `𝒳(·)` if `X` is unitary"), for any (possibly rectangular) `X`. -/
def conjBy {ι κ : Type} [Fintype ι] (U : Matrix κ ι ℂ) (ρ : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  U * ρ * Uᴴ

end UnitaryQIPPSPACE


