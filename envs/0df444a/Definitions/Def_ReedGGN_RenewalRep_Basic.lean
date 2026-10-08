-- Prove2me | Definitions.Def_ReedGGN_RenewalRep_Basic
-- name    : ReedGGN_RenewalRep_Basic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:19:33.9965+00:00
-- url     : https://prove2.me/theorems/db5eda92-f96d-49e5-a8dc-2daa1671d9e0
-- title:
--   Local boundedness on [0, ∞) (p. 29): bounded on every interval [0, T]
-- statement:
--   A function $f:\mathbb R\to\mathbb R$ is **locally bounded** (on $[0,\infty)$) if for every $T\ge 0$ there is a constant $C$ with
--   $$|f(t)|\le C\qquad\text{for all } t\in[0,T].$$
--
--   This is the class in which the paper (p. 29, proof of Corollary 5.2) asserts uniqueness for the renewal-type equation (5.42), citing Karlin and Taylor; the mission uses the same class for the uniqueness half of the renewal equation (5.39).
--
--   **Formalization Note** Paths are total functions $\mathbb R\to\mathbb R$; values at negative times are unconstrained and never read. "Locally bounded" is read explicitly as bounded on every $[0,T]$, $T\ge 0$. The càdlàg predicate and the equilibrium distribution $F_e$ (5.4) used by this mission are the shared definitions `ReedGGN.Regulator.IsCadlag` and `ReedGGN.Regulator.Fe`, which this file imports.
-- source:
--   Reed, The G/GI/N Queue in the Halfin–Whitt Regime, arXiv:0912.2837v1, p. 29, proof of Corollary 5.2 (locally bounded)

import Mathlib
import Definitions.Def_ReedGGN_Regulator_FluidInput
import Definitions.Def_ReedGGN_Regulator_PathSpace

namespace ReedGGN.RenewalRep

open MeasureTheory Filter Topology

/-- "Locally bounded" on `[0, ∞)` (p. 29): `f` is bounded on every interval `[0, T]`. -/
def IsLocallyBounded (f : ℝ → ℝ) : Prop :=
  ∀ T, 0 ≤ T → ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T, |f t| ≤ C

end ReedGGN.RenewalRep


