-- Prove2me | Definitions.Def_RamanujanNotebooks_ch41_ch41HardyClass
-- name    : RamanujanNotebooks_ch41_ch41HardyClass
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-10-07T15:52:59.649462+00:00
-- url     : https://prove2.me/theorems/4f97d607-348f-45e1-aab5-7bf296ee5580
-- title:
--   Ramanujan's Notebooks, Part I, Ch. 41: ch41HardyClass
-- statement:
--   Hardy's conditions on a function `ψ` (Quarterly Reports, §1.3, p. 299, with (1.3)): `ψ` is
--   analytic on the closed half-plane `H(δ) = {s : Re s ≥ -δ}`, written as "complex differentiable
--   on some open set containing `H(δ)`", and there is a constant `C` with
--   `|ψ(s)| ≤ C exp(P σ + A |t|)` for every `s = σ + i t` in `H(δ)`.
--   The numbers `δ`, `P`, `A` are parameters; the book's further requirements `0 < δ < 1` and
--   `A < π` are NOT part of this predicate and are separate hypotheses of each statement.
--   A proposition: no junk value.
--   Reference: `ψ(s) = 1` satisfies it with every `δ`, `P = 0`, `A = 0`; `ψ(s) = 1/Γ(s + 1)`
--   satisfies it for `0 < δ < 1` with `P = 0` and any `π/2 < A < π`.
-- source:
--   Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 41.

import Mathlib

namespace RamanujanNotebooks

/-- Hardy's conditions on a function `ψ` (Quarterly Reports, §1.3, p. 299, with (1.3)): `ψ` is
analytic on the closed half-plane `H(δ) = {s : Re s ≥ -δ}`, written as "complex differentiable
on some open set containing `H(δ)`", and there is a constant `C` with
`|ψ(s)| ≤ C exp(P σ + A |t|)` for every `s = σ + i t` in `H(δ)`.
The numbers `δ`, `P`, `A` are parameters; the book's further requirements `0 < δ < 1` and
`A < π` are NOT part of this predicate and are separate hypotheses of each statement.
A proposition: no junk value.
Reference: `ψ(s) = 1` satisfies it with every `δ`, `P = 0`, `A = 0`; `ψ(s) = 1/Γ(s + 1)`
satisfies it for `0 < δ < 1` with `P = 0` and any `π/2 < A < π`. -/
def ch41HardyClass (ψ : ℂ → ℂ) (δ P A : ℝ) : Prop :=
  (∃ U : Set ℂ, IsOpen U ∧ {s : ℂ | -δ ≤ s.re} ⊆ U ∧ DifferentiableOn ℂ ψ U) ∧
    ∃ C : ℝ, ∀ s : ℂ, -δ ≤ s.re → ‖ψ s‖ ≤ C * Real.exp (P * s.re + A * |s.im|)

end RamanujanNotebooks


