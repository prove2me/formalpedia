-- Prove2me | Definitions.Def_GeoSemialgCSP_noiseOpV
-- name    : GeoSemialgCSP_noiseOpV
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:37.141617+00:00
-- url     : https://prove2.me/theorems/2e706d7a-a277-47d1-ba35-c4c62c2cdacb
-- title:
--   Noise operator on vector-valued maps
-- statement:
--   For $F:W^R\to\mathbb R^q$, the noise operator acts coordinatewise: $(T_\sigma F)(z)_a=(T_\sigma F_a)(z)$. On a fractional solution $\xi$ it averages distributions, $(T_\rho\xi)(z)=\mathbb E_{\tilde z\sim N_\eta(z)}\xi(\tilde z)$ with $\rho=1-\eta$; it maps $\mathcal P_q$-valued maps to $\mathcal P_q$-valued maps.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, p.8 (PDF p.9); §4.4, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_GeoSemialgCSP_noiseOp

namespace GeoSemialgCSP

/-- **Noise operator on vector-valued maps.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), §3, printed p.8 (PDF p.9) ("when
applied coordinatewise") and §4.4, printed p.13 (PDF p.14): `(T_ρξ)(z) = E_{z̃ ∼ N_η(z)} ξ(z̃)`,
componentwise. -/
noncomputable def noiseOpV {W : Type*} [Fintype W] {R q : ℕ} (σ : ℝ)
    (F : (Fin R → W) → Fin q → ℝ) (z : Fin R → W) : Fin q → ℝ :=
  fun a => noiseOp σ (fun z' => F z' a) z

end GeoSemialgCSP


