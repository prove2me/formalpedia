-- Prove2me | Definitions.Def_InfHorizonVP_HypH7
-- name    : InfHorizonVP_HypH7
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:16:25.970268+00:00
-- url     : https://prove2.me/theorems/7bb672fb-f47f-4738-9182-a83dfb179d18
-- title:
--   Hypothesis (H7): integrability of the moduli
-- statement:
--   **(H7)** The moduli of (H3) and (H6) satisfy
--   $$
--   \int_0^\infty\Bigl[\exp\Bigl(\int_0^s\gamma(\tau)\,d\tau\Bigr)\Bigl(1+\int_0^s\gamma(\tau)\,d\tau\Bigr)\bigl(l_1(s)+l_2(s)\gamma(s)\bigr)\Bigr]ds<\infty .
--   $$
--
--   **Formalization Note** Since the integrand is nonnegative, finiteness is integrability on $[0,\infty)$.
-- source:
--   Frankowska, Sagara, Value Functions and Optimality Conditions for Nonconvex Variational Problems with an Infinite Horizon in Banach Spaces, arXiv:1801.00400v3, §3.2, p.9, (H7)

import Mathlib
open MeasureTheory Filter Topology Set
open scoped Pointwise

namespace InfHorizonVP

/-- **Hypothesis (H7).**
Frankowska, Sagara, arXiv:1801.00400v3, §3.2, p.9: "(H7) The Lipschitz modulus functions satisfy
the integrability conditions:
∫_0^∞ [exp(∫_0^s γ(τ)dτ)(1 + ∫_0^s γ(τ)dτ)(l1(s) + l2(s)γ(s))] ds < ∞."

**Formalization Note.** The integrand is nonnegative (for the nonnegative moduli of (H3), (H6)),
so "`∫_0^∞ … < ∞`" is Lebesgue integrability on `[0, ∞)`. The `l₁, l₂, γ` are those of (H3) and
(H6). -/
def HypH7 (l₁ l₂ γ : ℝ → ℝ) : Prop :=
  IntegrableOn (fun s => Real.exp (∫ τ in (0 : ℝ)..s, γ τ) * (1 + ∫ τ in (0 : ℝ)..s, γ τ) *
    (l₁ s + l₂ s * γ s)) (Ici 0)

end InfHorizonVP


