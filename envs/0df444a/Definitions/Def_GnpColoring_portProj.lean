-- Prove2me | Definitions.Def_GnpColoring_portProj
-- name    : GnpColoring_portProj
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:31:28.676214+00:00
-- url     : https://prove2.me/theorems/3e0e8e85-f72f-4a2f-8f70-c25bc6e2096d
-- title:
--   The port projection $\Pi_\rho$ (Definition 3.7)
-- statement:
--   For a block $B$ and a port $\rho$ of $B$, $\Pi_\rho f(\sigma)=\mathbb E_\mu[f\mid\sigma_{(V\setminus B)+\rho}]$: the average of $f$ over the colours of $B-\rho$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.7, p.18

import Mathlib
import Definitions.Def_SpinGirth5_heatBath

open scoped Classical
open Finset

namespace GnpColoring

/-- **The port projection** `Π_ρ f(σ) = E_µ[f | σ_{(V∖B)+ρ}]` (Definition 3.7).

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.7, p.18. -/
noncomputable def portProj {n q : ℕ} (μ : (Fin n → Fin q) → ℝ) (B : Finset (Fin n)) (ρ : Fin n)
    (f : (Fin n → Fin q) → ℝ) : (Fin n → Fin q) → ℝ :=
  SpinGirth5.condExp μ (insert ρ (univ \ B)) f

end GnpColoring


