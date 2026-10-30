-- Prove2me | Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12W
-- name    : RamanujanLostNotebook_PartII_ch12_ch12W
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-08T21:22:40.085992+00:00
-- url     : https://prove2.me/theorems/7038d28d-6f7f-4db4-bb01-ec7d8138c03c
-- title:
--   Ramanujan's Lost Notebook Part II, Ch. 12: ch12W
-- statement:
--   The weight W_μ(n) of the reciprocal-R expansion. W₁(n)=1 and W₂(n)=(-1)^n, the μ=2
--   value of (11.10.31), printed p.306.
--   Differs from the printed source: Entry 12.1.1 takes W from (11.5.5) and (11.5.7), whose
--   μ=2 value, fixed in (11.5.6), printed p.280, is −(-1)^n; that sign does not give the
--   coefficients of 1/R. For μ≥5 the sum runs once over each class of primitive solutions
--   of c²+d²=μ up to signs and interchange (Definition 11.4.1), represented by c>d>0, with
--   phase (ac+bd)·2πn/μ+8 arctan(c/d). At μ=5 the multiplier ac+bd is 2, not the 1 of the
--   manuscript formula that the editors reject on pp.324–325.
-- source:
--   G. E. Andrews and B. C. Berndt, Ramanujan's Lost Notebook, Part II, Springer 2009, Chapter 12.

import Mathlib
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Phase
import Definitions.Def_RamanujanLostNotebook_PartII_ch12_ch12Reps

namespace RamanujanLostNotebook.PartII

/-- The weight W_μ(n) of the reciprocal-R expansion. W₁(n)=1 and W₂(n)=(-1)^n, the μ=2
value of (11.10.31), printed p.306.
Differs from the printed source: Entry 12.1.1 takes W from (11.5.5) and (11.5.7), whose
μ=2 value, fixed in (11.5.6), printed p.280, is −(-1)^n; that sign does not give the
coefficients of 1/R. For μ≥5 the sum runs once over each class of primitive solutions
of c²+d²=μ up to signs and interchange (Definition 11.4.1), represented by c>d>0, with
phase (ac+bd)·2πn/μ+8 arctan(c/d). At μ=5 the multiplier ac+bd is 2, not the 1 of the
manuscript formula that the editors reject on pp.324–325. -/
noncomputable def ch12W (n mu : ℕ) : ℝ :=
  if mu = 1 then 1 else if mu = 2 then (-1 : ℝ) ^ n else
    2 * ∑ cd ∈ ch12Reps mu,
      Real.cos ((ch12Phase cd.1 cd.2 : ℝ) * (2 * (n : ℝ) * Real.pi / mu) +
        8 * Real.arctan ((cd.1 : ℝ) / cd.2))

end RamanujanLostNotebook.PartII


