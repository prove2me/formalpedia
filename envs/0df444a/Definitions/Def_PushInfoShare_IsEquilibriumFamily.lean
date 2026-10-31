-- Prove2me | Definitions.Def_PushInfoShare_IsEquilibriumFamily
-- name    : PushInfoShare_IsEquilibriumFamily
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T19:48:53.835822+00:00
-- url     : https://prove2.me/theorems/aae19085-a30b-419f-bd4c-19b380554227
-- title:
--   Equilibria indexed by $\phi$ and the sharing decision
-- statement:
--   A family of profiles indexed by $\phi$ and $\delta$ is an **equilibrium family** if each member is a linear separating equilibrium at every $\phi\ge0$ and for every sharing decision. By Proposition 1 the family exists and is unique for $\phi\ge0$, so statements about it are statements about the equilibrium profits.
-- source:
--   Jain, Sharing Demand Information with Retailer under Upstream Competition, SSRN:3388957 (PDF of 2021-04-25), §3, p.9; Proposition 1, p.11

import Mathlib
import Definitions.Def_PushInfoShare_IsLinearSeparatingEq

open MeasureTheory

namespace PushInfoShare

/-- `str φ δ` is a linear separating equilibrium at every substitution level `φ ≥ 0`
(Jain, SSRN:3388957, PDF of 2021-04-25, p.7) and for all four sharing decisions `δ` (p.9).

**Formalization Note.** Proposition 1 of the paper, `proposition_1` here, says each such equilibrium
exists and is unique, so a family exists. -/
def IsEquilibriumFamily {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (θ : Ω → ℝ)
    (Y : Fin 2 → Ω → ℝ) (σ a : ℝ) (str : ℝ → (Fin 2 → Bool) → Profile) : Prop :=
  ∀ φ, 0 ≤ φ → ∀ δ, IsLinearSeparatingEq μ θ Y σ a φ δ (str φ δ)

end PushInfoShare


