-- Prove2me | Definitions.Def_MondererShapley_Improvement_IsImprovement
-- name    : MondererShapley_Improvement_IsImprovement
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T19:17:06.555546+00:00
-- url     : https://prove2.me/theorems/9165775b-83c8-49dc-b7b0-20d9eedec976
-- title:
--   Finite improvement path
-- statement:
--   A finite path $\gamma=(y_0,\ldots,y_L)$ is an **improvement path** for payoff vector $u$ when its deviating player $i_k$ gains strictly at each step:
--
--   $$
--   u^{i_k}(y_{k-1})<u^{i_k}(y_k)\qquad(1\le k\le L).
--   $$
--
--   This is the finite path notion used to define the relation $x>y$ in the proof of Lemma 2.5. A length-zero path satisfies the condition, but $x>y$ separately requires $x\ne y$.
-- source:
--   Monderer and Shapley, Potential Games, Games Econ. Behav. 14 (1996), p. 128 (PDF p. 5), definition of improvement path

import Mathlib
import Definitions.Def_MondererShapley_Improvement_FinPath

namespace MondererShapley.Improvement

variable {ι : Type*} [DecidableEq ι] {Y : ι → Type*}

/-- Every step of the finite path strictly benefits its deviating player. -/
def FinPath.IsImprovement (u : ι → (∀ i, Y i) → ℝ) (γ : FinPath Y) : Prop :=
  ∀ k : Fin γ.len,
    u (γ.dev k) (γ.pt k.castSucc) < u (γ.dev k) (γ.pt k.succ)

end MondererShapley.Improvement


