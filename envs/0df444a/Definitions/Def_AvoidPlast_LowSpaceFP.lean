-- Prove2me | Definitions.Def_AvoidPlast_LowSpaceFP
-- name    : AvoidPlast_LowSpaceFP
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:49:39.844608+00:00
-- url     : https://prove2.me/theorems/aa959aa7-ed6d-40e4-83fc-9aea759785ee
-- title:
--   Item 1 of Theorem 5.14
-- statement:
--   For every $f\in\mathrm{FP}$ and every constant $\gamma>0$ there is a deterministic space-$n^\gamma$ machine $M_f$ such that, for every sufficiently large $n$,
--
--   $$\Pr_{x\in\{0,1\}^n}[M_f(x)=f(x)]\ge 1-n^{-\omega(1)}.$$
--
--   This is the simulation of polynomial time in small space on average.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorem 5.14, item 1, p.29

import Mathlib
import Definitions.Def_QuantumPRC_Negligible
import Definitions.Def_AvoidPlast_Machine
import Definitions.Def_AvoidPlast_output
import Definitions.Def_AvoidPlast_prob
import Definitions.Def_AvoidPlast_InFP
import Definitions.Def_AvoidPlast_SpaceO

namespace AvoidPlast

/-- Item 1 of Theorem 5.14 (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), p.29): for every `f ∈ FP` and every constant `γ > 0` there is a
deterministic space-`n^γ` machine `M_f` such that for every sufficiently large `n`,
`Pr_x[M_f(x) = f(x)] ≥ 1 - n^{-ω(1)}`. -/
def LowSpaceFP : Prop :=
  ∀ f : List Bool → List Bool, InFP f → ∀ γ : ℝ, 0 < γ →
    ∃ M : Machine 1, SpaceO M (fun n => (n : ℝ) ^ γ) ∧
      ∃ ν : ℕ → ℝ, QuantumPRC.Negligible ν ∧ ∀ᶠ n : ℕ in Filter.atTop,
        1 - ν n ≤ prob n (fun x => output M ![x] = f x)

end AvoidPlast


