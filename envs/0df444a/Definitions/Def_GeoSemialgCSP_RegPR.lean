-- Prove2me | Definitions.Def_GeoSemialgCSP_RegPR
-- name    : GeoSemialgCSP_RegPR
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T16:49:52.742586+00:00
-- url     : https://prove2.me/theorems/46e57e41-16d6-4d98-884c-0baa27e55f12
-- title:
--   Pseudorandomness with respect to a region family
-- statement:
--   For a family $\mathcal C$ of regions, the region influence of a fractional solution is $\mathrm{Inf}^{\mathcal C}_r(\xi)=\sup_{A\in\mathcal C}\mathrm{Inf}_r(\xi_A)$ (4). The solution is **$\tau$-pseudorandom with respect to $\mathcal C$** if $\mathrm{Inf}_r(\xi_A)\le\tau$ for every coordinate $r$ and every $A\in\mathcal C$.
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Eq. (4), p.14 (PDF p.15)

import Mathlib
import Definitions.Def_GeoSemialgCSP_regMass
import Definitions.Def_GeoSemialgCSP_infl

namespace GeoSemialgCSP

/-- **Pseudorandomness with respect to a region family.** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Eq. (4), printed p.14
(PDF p.15): `Inf^C_r(ξ) = sup_{S ∈ C} Inf_r(ξ_S)`, and `ξ` is `τ`-pseudorandom with respect to `C`
if `Inf^C_r(ξ) ≤ τ` for every coordinate `r`. -/
def RegPR {U W : Type*} [Fintype W] {R n : ℕ} (C : Set (Set U)) (τ : ℝ) (x : Fin n → U)
    (G : (Fin R → W) → Fin n → ℝ) : Prop :=
  ∀ r : Fin R, ∀ A ∈ C, infl (regMass x G A) r ≤ τ

end GeoSemialgCSP


