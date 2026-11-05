-- Prove2me | Definitions.Def_FractionalSpectralGP_opT
-- name    : FractionalSpectralGP_opT
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:25:55.717838+00:00
-- url     : https://prove2.me/theorems/021dd1dc-42d4-4a28-904e-b5f9179dc080
-- title:
--   The operator $T=WM_uW^*$ on $L^2(\mathbb R,dx)$ (5.1)
-- statement:
--   For a spectral setting and an orthonormal basis $(h_n)$ of $L^2(\mathbb R,dx)$,
--
--   $$
--   T=W\,M_u\,W^*
--   $$
--
--   is the bounded self-adjoint operator on $L^2(\mathbb R,dx)$ obtained by transporting the multiplication operator $M_u$ of $L^2(d\sigma)$ along the unitary $W$ (5.1). The operator $Q_\sigma$ is defined through the functional calculus of $T$.
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, (5.1), p.12

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_unitaryW
import Definitions.Def_FractionalSpectralGP_multU

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- The operator `T = W M_u W*` on `L²(ℝ, dx)` (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, (5.1), p.12), a bounded
self-adjoint operator. -/
noncomputable def opT (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
    Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ((unitaryW S h).toContinuousLinearEquiv.toContinuousLinearMap.comp (multU S.σ)).comp
    (unitaryW S h).symm.toContinuousLinearEquiv.toContinuousLinearMap

end FractionalSpectralGP


