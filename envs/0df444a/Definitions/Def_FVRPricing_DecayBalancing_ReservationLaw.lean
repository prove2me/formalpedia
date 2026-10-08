-- Prove2me | Definitions.Def_FVRPricing_DecayBalancing_ReservationLaw
-- name    : FVRPricing_DecayBalancing_ReservationLaw
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T06:45:06.54244+00:00
-- url     : https://prove2.me/theorems/649019e7-2236-4829-b2eb-9cfef6937cfc
-- title:
--   Reservation-price law: tail $\bar F$, hazard rate $\rho$, Assumption 1, exponential density, static revenue
-- statement:
--   Customers' reservation prices are i.i.d. with a density $f$ on $\mathbb R$. This file fixes the objects of §2 that depend on $f$ only.
--
--   1. The **tail probability** $\bar F(p) = 1 - F(p) = \int_{(p,\infty)} f(s)\,ds$.
--   2. The **hazard rate** $\rho(p) = f(p)/\bar F(p)$.
--   3. **Assumption 1** (p. 5): $f$ is a probability density ($f$ integrable, $\int f = 1$) with support $\mathbb R_+$ ($f(p) = 0$ for $p<0$, $f(p)>0$ for $p>0$, $f(0)\ge 0$), $f$ is differentiable on $[0,\infty)$, and $\rho$ is non-decreasing on $[0,\infty)$.
--   4. The **exponential density with mean $r$** (§6.3, p. 23),
--   $$f_r(p) = \tfrac1r e^{-p/r}\ (p\ge 0),\qquad f_r(p)=0\ (p<0),$$
--   so that $\bar F(p) = e^{-p/r}$ for $p \ge 0$, $\rho \equiv 1/r$ and the static revenue-maximizing price is $p^* = r$.
--   5. A **static revenue-maximizing price** is a $q\ge 0$ maximizing $p\,\bar F(p)$ over $p\ge 0$; the **static revenue** is
--   $$\sup_{p\ge 0} p\,\bar F(p) \in [0,\infty],$$
--   which equals $\bar F(p^*)p^*$ when the maximizer $p^*$ exists (under Assumption 1 it exists and is unique, pp. 8, 12).
--
--   These are the primitives of every statement of the mission: the sales intensity at price $p$ is $\lambda\bar F(p)$, and $\bar F/\rho$ enters the balance equations.
--
--   **Formalization Note** Differentiability is required within $[0,\infty)$ (one-sided at $0$), which the exponential density satisfies although it is discontinuous at $0$ as a function on $\mathbb R$. The static revenue is a supremum in $[0,\infty]$, so no junk value of a real supremum can arise; the exponential density is a plain function, and its satisfying Assumption 1 is a fact, not a hypothesis of the exponential statements.
-- source:
--   Farias, Van Roy, Dynamic Pricing with a Prior on Market Response, manuscript of January 20, 2009 (sha256 a64048ac…), p. 5, §2 and Assumption 1; p. 8 and p. 12 (static revenue-maximizing price p*); p. 23, §6.3 (exponential reservation prices)

import Mathlib

namespace FVRPricing.DecayBalancing

open MeasureTheory

/-- Tail probability `F̄(p) = 1 − F(p) = ∫_{(p,∞)} f` of the reservation-price law with density `f`. -/
noncomputable def Fbar (f : ℝ → ℝ) (p : ℝ) : ℝ := ∫ s in Set.Ioi p, f s

/-- Hazard rate `ρ(p) = f(p) / F̄(p)`. -/
noncomputable def hazard (f : ℝ → ℝ) (p : ℝ) : ℝ := f p / Fbar f p

/-- Assumption 1 (p. 5): `f` is a probability density with support `ℝ₊`, differentiable on `ℝ₊`,
with non-decreasing hazard rate on `ℝ₊`. -/
structure Assumption1 (f : ℝ → ℝ) : Prop where
  eq_zero_of_neg : ∀ p : ℝ, p < 0 → f p = 0
  pos_of_pos : ∀ p : ℝ, 0 < p → 0 < f p
  nonneg_zero : 0 ≤ f 0
  integrable : Integrable f
  integral_eq_one : ∫ p, f p = 1
  differentiableOn : DifferentiableOn ℝ f (Set.Ici 0)
  hazard_monotoneOn : MonotoneOn (hazard f) (Set.Ici 0)

/-- Exponential reservation-price density with mean `r`: `f(p) = (1/r) e^{−p/r}` for `p ≥ 0`, `0` otherwise
(§6.3, p. 23: `F̄(p) = exp(−p/r)`). -/
noncomputable def expDensity (r : ℝ) (p : ℝ) : ℝ :=
  if 0 ≤ p then r⁻¹ * Real.exp (-(p / r)) else 0

/-- `q` is a static revenue-maximizing price: it maximizes `p F̄(p)` over `p ≥ 0`. -/
def IsStaticMaximizer (f : ℝ → ℝ) (q : ℝ) : Prop :=
  0 ≤ q ∧ ∀ p : ℝ, 0 ≤ p → p * Fbar f p ≤ q * Fbar f q

/-- The maximal static revenue rate per unit arrival rate, `sup_{p ≥ 0} p F̄(p)`; it equals `F̄(p*) p*`
when the static revenue-maximizing price `p*` exists. Valued in `ℝ≥0∞`, so no junk value arises. -/
noncomputable def staticRevenue (f : ℝ → ℝ) : ENNReal :=
  ⨆ p ∈ Set.Ici (0 : ℝ), ENNReal.ofReal (p * Fbar f p)

end FVRPricing.DecayBalancing


