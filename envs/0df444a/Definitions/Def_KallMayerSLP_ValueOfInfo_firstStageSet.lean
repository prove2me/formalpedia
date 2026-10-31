-- Prove2me | Definitions.Def_KallMayerSLP_ValueOfInfo_firstStageSet
-- name    : KallMayerSLP_ValueOfInfo_firstStageSet
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T22:13:15.701764+00:00
-- url     : https://prove2.me/theorems/9aa3e0ae-0d9f-47d3-b58f-02c6a24828a2
-- title:
--   First-stage feasible set $\mathcal B_1=\{x: Ax=b,\ x\ge 0\}$
-- statement:
--   For a two-stage problem with first-stage data $A$, $b$, the set of first-stage decisions satisfying the first-stage constraints of (2.66),
--
--   $$
--   \mathcal B_1=\{x\in\mathbb R^{n_1} : Ax=b,\ x\ge 0\}.
--   $$
--
--   The recourse problem minimizes over this set.
-- source:
--   Kall & Mayer, Stochastic Linear Programming (2005), Chapter 3, eq. (2.66), p.243 (PDF 252); the name B₁, p.201 (PDF 210)

import Mathlib
import Definitions.Def_KallMayerSLP_ValueOfInfo_TwoStageSLP

open Matrix

namespace KallMayerSLP.ValueOfInfo

/-- **First-stage feasible set `B₁ = {x | Ax = b, x ≥ 0}`.**
Kall & Mayer, *Stochastic Linear Programming* (2005), Chapter 3, constraints of (2.66), p.243
(PDF 252); the set is named `B₁` on p.201 (PDF 210). -/
def firstStageSet {r n₁ m₁ n₂ m₂ : ℕ} (P : TwoStageSLP r n₁ m₁ n₂ m₂) : Set (Fin n₁ → ℝ) :=
  {x | P.A *ᵥ x = P.b ∧ 0 ≤ x}

end KallMayerSLP.ValueOfInfo


