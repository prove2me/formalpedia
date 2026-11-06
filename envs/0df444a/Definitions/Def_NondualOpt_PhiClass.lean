-- Prove2me | Definitions.Def_NondualOpt_PhiClass
-- name    : NondualOpt_PhiClass
-- status  : Definition
-- author  : @iris
-- created : 2026-11-05T23:57:42.870279+00:00
-- url     : https://prove2.me/theorems/ee0e8caf-85f3-4a62-a29f-ca39220b1799
-- title:
--   The class $\Phi$ of offset envelopes
-- statement:
--   The class
--   $$
--   \Phi=\{\phi:[-1,1]\to[0,2]:\ \phi(-1)=0,\ \phi\ge0,\ \phi\text{ nondecreasing and 1-Lipschitz}\}.
--   $$
--   Its compositions with the affine class form the offset envelope class of Lemma 5 and Lemma 22.
-- source:
--   Bullins–Guzmán–Martínez-Rubio–Molina, The First-Order Oracle Complexity of Lipschitz Convex Optimization in Nondual Settings, arXiv:2609.20687, Definition 21, p.30

import Mathlib

namespace NondualOpt

/-- The class `Φ = {ϕ : [−1, 1] → [0, 2] : ϕ(−1) = 0, ϕ ≥ 0, ϕ nondecreasing and 1-Lipschitz}`.
Bullins–Guzmán–Martínez-Rubio–Molina, arXiv:2609.20687, Definition 21, p.30. -/
def PhiClass : Set (Set.Icc (-1 : ℝ) 1 → ℝ) :=
  {ϕ | ϕ ⟨-1, Set.left_mem_Icc.2 (by norm_num)⟩ = 0 ∧ (∀ z, 0 ≤ ϕ z ∧ ϕ z ≤ 2) ∧
    Monotone ϕ ∧ LipschitzWith 1 ϕ}

end NondualOpt


