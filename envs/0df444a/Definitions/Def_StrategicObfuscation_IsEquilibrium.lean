-- Prove2me | Definitions.Def_StrategicObfuscation_IsEquilibrium
-- name    : StrategicObfuscation_IsEquilibrium
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:50:07.134769+00:00
-- url     : https://prove2.me/theorems/ec278b4f-50b8-4671-8a9e-d155fc8e755a
-- title:
--   Equilibrium $(e^*,\alpha^*,Q^*)$ at resources $\sigma$
-- statement:
--   A triple $(e,\alpha,Q)$ is an **equilibrium** at $\sigma$ when:
--
--   1. applicants with bad ideas obfuscate optimally: $e=E(\alpha,\sigma)$;
--   2. $Q\in[0,1]$ is consistent with Bayes' rule:
--
--   $$Q\,\bigl[(1-\pi(\sigma,0))p+(1-\pi(\sigma,e))(1-p)\bigr]=(1-\pi(\sigma,0))p;$$
--
--   3. $\alpha\in[0,1]$ maximizes $a\,(QV-c)$ over $a\in[0,1]$.
--
--   Here $p$ is the prior probability that the idea is good, $V$ its value and $c$ the funding cost. Good applicants do not obfuscate, which is why $\pi(\sigma,0)$ appears in the numerator.
--
--   **Formalization Note** Bayes' rule (2) is cross-multiplied. At $\sigma=1$, $e=0$ the denominator vanishes, the report is off path and a perfect Bayesian equilibrium leaves $Q$ free in $[0,1]$.
-- source:
--   Figueroa & Lemus, The Benefit of the Doubt: Decision Making under Strategic Obfuscation, SSRN 3840423 (version of April 4, 2022), Definition 1 and eq. (2), pp.10–11

import Mathlib

open Set

namespace StrategicObfuscation

/-- **An equilibrium `(e*, α*, Q*)` at resources `σ`.**
Figueroa & Lemus, *The Benefit of the Doubt: Decision Making under Strategic Obfuscation*,
SSRN 3840423 (version of April 4, 2022), Definition 1 and eq. (2), pp.10–11 (PDF pp.10–11).

1. Applicants with bad ideas obfuscate optimally: `e = E α σ`, where `E` is the effort selection.
2. The posterior `Q` is consistent with Bayes' rule (2).
3. The funding probability `α ∈ [0, 1]` maximizes `a · (Q V - c)` over `a ∈ [0, 1]`.

**Formalization Note** Bayes' rule (2) is cross-multiplied: `Q * D = N`, with `D` the denominator of
(2). At `σ = 1`, `e = 0` we have `D = 0`: the report is off path and a perfect Bayesian equilibrium
leaves `Q` free in `[0, 1]`, whereas Lean's `0 / 0 = 0` would pin it. Whenever `D ≠ 0` this is (2). -/
structure IsEquilibrium (π : ℝ → ℝ → ℝ) (V c p : ℝ) (E : ℝ → ℝ → ℝ) (σ e α Q : ℝ) : Prop where
  /-- Clause 1 of Definition 1: `e* = e(α*, σ)`. -/
  effort : e = E α σ
  /-- `α* ∈ [0, 1]`. -/
  mem_alpha : α ∈ Icc (0 : ℝ) 1
  /-- `Q*` is a probability. -/
  mem_belief : Q ∈ Icc (0 : ℝ) 1
  /-- Clause 2 of Definition 1: Bayes' rule (2), cross-multiplied. -/
  bayes : Q * ((1 - π σ 0) * p + (1 - π σ e) * (1 - p)) = (1 - π σ 0) * p
  /-- Clause 3 of Definition 1: `α*` maximizes `a · (Q* V - c)` on `[0, 1]`. -/
  optimal : ∀ a ∈ Icc (0 : ℝ) 1, a * (Q * V - c) ≤ α * (Q * V - c)

end StrategicObfuscation


