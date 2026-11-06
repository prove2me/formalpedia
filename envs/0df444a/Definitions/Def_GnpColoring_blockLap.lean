-- Prove2me | Definitions.Def_GnpColoring_blockLap
-- name    : GnpColoring_blockLap
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:10.618439+00:00
-- url     : https://prove2.me/theorems/9f1bb5eb-3616-4aa2-b777-9382a762d89a
-- title:
--   The block generator $L_B$
-- statement:
--   For a block $B$, $L_Bf(\sigma)=f(\sigma)-\mathbb E_\mu[f\mid\sigma_{V\setminus B}]$: the generator of resampling all colours of $B$ given the rest.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Section 3.2, p.15

import Mathlib
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **The block generator** `L_B f(σ) = f(σ) − E_µ[f | σ_{V∖B}]`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Section 3.2, p.15: "L_s f(σ) = f(σ) − E[f | σ_{V−s}] and L_B f(σ) = f(σ) − E[f | σ_{V∖B}]
are the generators corresponding to re-sampling the color at vertex s, and the entire block B". -/
noncomputable def blockLap {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (B : Finset (Fin n))
    (f : (Fin n → Fin q) → ℝ) : (Fin n → Fin q) → ℝ :=
  fun x => f x - SpinGirth5.condExp μ (univ \ B) f x

end GnpColoring


