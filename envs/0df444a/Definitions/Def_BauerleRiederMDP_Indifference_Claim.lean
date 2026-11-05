-- Prove2me | Definitions.Def_BauerleRiederMDP_Indifference_Claim
-- name    : BauerleRiederMDP_Indifference_Claim
-- status  : Definition
-- author  : @iris
-- created : 2026-11-04T06:27:12.487861+00:00
-- url     : https://prove2.me/theorems/c63edca3-4aca-49fe-9693-39417f3165d1
-- title:
--   Contingent claim $H=h(S_N,\hat S_N)$
-- statement:
--   A contingent claim of Section 4.9 is a non-negative random variable of the form $H=h(S_N,\hat S_N)$, given by a measurable payoff function $h$ of the terminal prices of the traded and the non-traded asset with $h\ge 0$ on $\mathbb R_+^2$. The claim $H\equiv 0$ is the reference case: its value function is written $V^0_n$.
--
--   **Formalization Note** The function $h$ lives on $\mathbb R^2$; only its values on $\mathbb R_+^2$ are reached from the state space. Measurability is required because the terminal reward of a Markov Decision Model is measurable (Definition 2.1.1).
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, p.135 and p.138

import Mathlib

namespace BauerleRiederMDP.Indifference

/-- A contingent claim `H = h(S_N, Ŝ_N)` of §4.9 (Bäuerle & Rieder, Markov Decision Processes with
Applications to Finance (2011), §4.9, p.135, PDF 149 and p.138, PDF 152): a measurable payoff
function `h` of the two prices with `H ≥ 0`.

**Formalization Note.** `h` is a function on `ℝ²`, measurable because `g_N` must be measurable in a
Markov Decision Model (Definition 2.1.1), and non-negative on `ℝ₊²`, the price part of the book's
state space `E = ℝ × ℝ₊²`. Its values outside `ℝ₊²` are never reached from `E`. -/
structure Claim where
  /-- The payoff function `h`. -/
  h : ℝ → ℝ → ℝ
  measurable : Measurable (Function.uncurry h)
  nonneg : ∀ s ŝ, 0 ≤ s → 0 ≤ ŝ → 0 ≤ h s ŝ

instance : CoeFun Claim (fun _ => ℝ → ℝ → ℝ) := ⟨Claim.h⟩

/-- The claim `H ≡ 0`, whose value function the book writes `V⁰_n` (p.138, PDF 152). -/
def Claim.zero : Claim where
  h := fun _ _ => 0
  measurable := measurable_const
  nonneg := fun _ _ _ _ => le_rfl

end BauerleRiederMDP.Indifference


