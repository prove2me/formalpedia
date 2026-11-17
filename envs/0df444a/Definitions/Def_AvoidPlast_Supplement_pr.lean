-- Prove2me | Definitions.Def_AvoidPlast_Supplement_pr
-- name    : AvoidPlast_Supplement_pr
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T08:56:01.485069+00:00
-- url     : https://prove2.me/theorems/c7ad8887-0d25-4a20-94f1-b01102b6efec
-- title:
--   Probability of an event under a distribution
-- statement:
--   For a probability mass function $\mu$ and an event $P$, $\Pr_{a\sim\mu}[P(a)]$ as a real number.
-- source:
--   Li–Tell, Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance, STOC 2027 submission (manuscript sha256 e1ff3a9e…), Theorems 5.1, 5.4, pp.21–23

import Mathlib

namespace AvoidPlast.Supplement

/-- The probability of an event under a probability mass function (Li–Tell, *Trading Time, Space, and Alternations: General Plasticity for Algorithms from Hardness of Range Avoidance*, STOC 2027 submission manuscript (sha256 e1ff3a9e…d6728), Theorems 5.1, 5.4,
pp.21–23, `Pr_{x∼D_n}`). -/
noncomputable def pr {α : Type} (μ : PMF α) (P : α → Prop) : ℝ :=
  (μ.toOuterMeasure {a | P a}).toReal

end AvoidPlast.Supplement


