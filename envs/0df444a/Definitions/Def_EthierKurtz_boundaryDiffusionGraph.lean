-- Prove2me | Definitions.Def_EthierKurtz_boundaryDiffusionGraph
-- name    : EthierKurtz_boundaryDiffusionGraph
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-21T06:07:45.724931+00:00
-- url     : https://prove2.me/theorems/8586a6f6-c0cf-4e7e-b32f-10179c456a50
-- title:
--   One-dimensional diffusion generator graph with Feller boundary conditions
-- statement:
--   The exact graph of the scalar diffusion operator on twice continuously differentiable interior functions with continuous endpoint extensions and the source's exit or regular boundary condition at each accessible endpoint.
-- source:
--   Stewart N. Ethier and Thomas G. Kurtz, Markov Processes: Characterization and Convergence, Wiley, 1986, Chapter 8, Section 1, equations (1.2), (1.7)–(1.11), printed pp. 366–367 (PDF pp. 375–376).

import Definitions.Def_EthierKurtz_intervalRealRestriction
import Definitions.Def_EthierKurtz_boundaryDriftPrimitive
import Definitions.Def_EthierKurtz_diffusionBoundaryTests

open Filter MeasureTheory
open scoped Topology ENNReal

namespace EthierKurtz

/-- The exact graph {(f,Gf): f ∈ D₀ ∩ D₁}, (1.8)–(1.11).
No boundary condition is imposed when u=∞ (entrance or natural).
For regular endpoints the finite scale-derivative limit is explicit. -/
def boundaryDiffusionGraph (r₀ r₁ : EReal) (a b : ℝ → ℝ)
    (r : ℝ) (q : Fin 2 → ℝ) :
    Set (C(Set.Icc r₀ r₁, ℝ) × C(Set.Icc r₀ r₁, ℝ)) :=
  let J := {x : ℝ | r₀ < (x : EReal) ∧ (x : EReal) < r₁}
  {fg | let f := intervalRealRestriction fg.1
        let g := intervalRealRestriction fg.2
        ContDiffOn ℝ 2 f J ∧
        (∀ x ∈ J, g x = (a x / 2) * deriv (deriv f) x + b x * deriv f x) ∧
        ∀ i : Fin 2,
          let e := if i = 0 then r₀ else r₁
          let uv := diffusionBoundaryTests a b r e
          let F := Filter.comap (fun x : ℝ => (x : EReal))
            (𝓝[Set.Ioo r₀ r₁] e)
          (uv.1 < ∞ → uv.2 = ∞ → Tendsto g F (𝓝 0)) ∧
          (uv.1 < ∞ → uv.2 < ∞ → ∃ L H : ℝ,
            Tendsto g F (𝓝 H) ∧
            Tendsto (fun x => Real.exp (boundaryDriftPrimitive a b r x) * deriv f x)
              F (𝓝 L) ∧
            q i * H = (if i = 0 then 1 else -1) * (1 - q i) * L)}

end EthierKurtz


