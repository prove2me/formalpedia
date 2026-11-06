-- Prove2me | Definitions.Def_GnpColoring_portGrad
-- name    : GnpColoring_portGrad
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T02:32:44.769931+00:00
-- url     : https://prove2.me/theorems/4421537b-c0a6-4e11-b4f2-8b5e1b716c30
-- title:
--   The port gradient $\tilde\nabla^c_{B,\sigma}f$ (Definition 3.8)
-- statement:
--   For a block $B$, a port $\rho$, a colour $c$ and a colouring $\sigma$,
--
--   $$\tilde\nabla^c_{B,\sigma}f(\rho)=q\,p^\sigma_\rho(c)\big(\Pi_\rho f(\sigma_{\rho\leftarrow c})-\Pi_\rho f(\sigma)\big),$$
--
--   for $\mu$ the uniform measure on proper $q$-colourings. The literal recolouring may be improper, but $\Pi_\rho f(\sigma_{\rho\leftarrow c})$ only depends on the exterior and the colour at $\rho$.
-- source:
--   Schiller, Sampling Colorings on G(n, d/n) via Glauber Dynamics, STOC 2027 submission (manuscript sha256 da44ff7b…), Definition 3.8, p.18

import Mathlib
import Definitions.Def_GnpColoring_portProj
import Definitions.Def_GnpColoring_cavityProb
import Definitions.Def_mm_transport

open scoped Classical
open Finset

namespace GnpColoring

/-- **The port gradient** `∇̃^c_{B,σ} f(ρ) = q p^σ_ρ(c) (Π_ρ f(σ_{ρ←c}) − Π_ρ f(σ))` (Definition 3.8),
for the uniform measure `µ` on proper `q`-colourings of `G`.

Schiller, *Sampling Colorings on G(n, d/n) via Glauber Dynamics*, STOC 2027 submission manuscript (sha256 da44ff7b…), Definition 3.8, p.18: "Note that, even if p^σ_ρ(c) > 0, the literal recoloring σ_{ρ←c} may
be improper. However, the projected value Π_ρ f(σ_{ρ←c}) still averages f over feasible colorings
with exterior σ_{V∖B} and color c at ρ." -/
noncomputable def portGrad {n : ℕ} (G : SimpleGraph (Fin n)) (q : ℕ) (B : Finset (Fin n))
    (f : (Fin n → Fin q) → ℝ) (c : Fin q) (σ : Fin n → Fin q) (ρ : Fin n) : ℝ :=
  (q : ℝ) * cavityProb (MarkovMixing.properColoringDist G q) B ρ c σ *
    (portProj (MarkovMixing.properColoringDist G q) B ρ f (Function.update σ ρ c) -
      portProj (MarkovMixing.properColoringDist G q) B ρ f σ)

end GnpColoring


