-- Prove2me | Definitions.Def_PConeEB_kappaZ
-- name    : PConeEB_kappaZ
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:32:49.796285+00:00
-- url     : https://prove2.me/theorems/46dc836c-5f94-4b3a-a46b-093a970b49b2
-- title:
--   The constant $\kappa_{z,\eta}$ of Theorem 2.2
-- statement:
--   For $\alpha\in(0,1]$, $\eta\ge0$ and $\gamma_{z,\eta}$ as in (2.13),
--   $$
--   \kappa_{z,\eta}:=\max\{2\eta^{1-\alpha},\ 2\gamma_{z,\eta}^{-1}\}.
--   $$
--   It is the constant of the bound (2.14).
--
--   **Formalization Note** The exponent $\alpha$ is an explicit parameter. For $\gamma_{z,\eta}=+\infty$ the second entry is $0$. For $\gamma_{z,\eta}=0$ the Lean value is a default, so every statement using this constant assumes $\gamma_{z,\eta}>0$. At $\eta=0$, $\alpha=1$ Lean reads $0^0=1$; nothing depends on this value.
-- source:
--   Lindstrom, Lourenço & Pong, Optimal error bounds in the absence of constraint qualifications, arXiv:2109.11729v4, Theorem 2.2 (i), p.8

import Mathlib
import Definitions.Def_PConeEB_gammaZ

namespace PConeEB

/-- The constant `κ_{z,η} := max{2 η^{1-α}, 2 γ_{z,η}⁻¹}` of Theorem 2.2.
Lindstrom, Lourenço & Pong, arXiv:2109.11729v4, Theorem 2.2 (i), p.8.

**Formalization Note.** `α` is explicit, since `g` alone does not determine it. At `γ = ⊤` the
second entry is `0`, as intended. At `γ = 0` the Lean value `⊤.toReal = 0` is junk, so every
statement using `kappaZ` assumes `0 < gammaZ K z g η`. In real `rpow`, `0 ^ 0 = 1`, which is reached
only at `η = 0`, `α = 1`, where the paper leaves `0⁰` open and nothing depends on it. -/
noncomputable def kappaZ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (K : Set E) (z : E) (g : ℝ → ℝ) (α η : ℝ) : ℝ :=
  max (2 * η ^ (1 - α)) (2 * ((gammaZ K z g η)⁻¹).toReal)

end PConeEB


