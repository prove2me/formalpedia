-- Prove2me | Definitions.Def_BuckPassing_Det_CostGame
-- name    : BuckPassing_Det_CostGame
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-20T02:17:59.002716+00:00
-- url     : https://prove2.me/theorems/765a91b4-7438-4ea1-af27-0aa101bccb48
-- title:
--   Cost games, Nash equilibria, and ordinal potentials
-- statement:
--   In a cost game, each player $i$ selects an action from a strategy set $X_i$ and seeks to minimize a real-valued cost $c_i(s)$ determined by the full profile $s$.
--
--   A profile is a **Nash equilibrium** when no single player can lower her cost by changing only her own action. A function $\Psi$ on profiles is a **generalized ordinal potential** if every such cost-lowering move strictly lowers $\Psi$; it is an **ordinal potential** if the two strict decreases are equivalent:
--
--   $$c_i(x,s_{-i})<c_i(s)\ \Longrightarrow\ \Psi(x,s_{-i})<\Psi(s),\qquad c_i(x,s_{-i})<c_i(s)\ \Longleftrightarrow\ \Psi(x,s_{-i})<\Psi(s).$$
--
--   These general cost-game predicates are used by the deterministic buck-passing model and its equilibrium theorems.
-- source:
--   Cominetti, Quattropani, Scarsini, The Buck-Passing Game, arXiv:1808.03206v4, pp. 7–8, §3.1, Definitions 2(b) and 4, equations (8)–(9)

import Mathlib

namespace BuckPassing.Det

/- General cost games (§3.1, p. 8): players minimize their individual costs. -/
variable {ι : Type*} [DecidableEq ι] {X : ι → Type*}

/-- Definition 2(b): no unilateral move lowers the mover's cost. -/
def IsNash (c : ι → (∀ i, X i) → ℝ) (s : ∀ i, X i) : Prop :=
  ∀ i (x : X i), ¬ c i (Function.update s i x) < c i s

/-- Definition 4, equation (9), with the paper's cost-minimization convention. -/
def IsGenOrdPotential (c : ι → (∀ i, X i) → ℝ)
    (Ψ : (∀ i, X i) → ℝ) : Prop :=
  ∀ (s : ∀ i, X i) i (x : X i),
    c i (Function.update s i x) < c i s → Ψ (Function.update s i x) < Ψ s

/-- Definition 4, equation (8), with the paper's cost-minimization convention. -/
def IsOrdPotential (c : ι → (∀ i, X i) → ℝ)
    (Ψ : (∀ i, X i) → ℝ) : Prop :=
  ∀ (s : ∀ i, X i) i (x : X i),
    c i (Function.update s i x) < c i s ↔ Ψ (Function.update s i x) < Ψ s

end BuckPassing.Det


