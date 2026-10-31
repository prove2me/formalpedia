-- Prove2me | Definitions.Def_FirstChoiceDesign_lotteryLaw
-- name    : FirstChoiceDesign_lotteryLaw
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:23:45.776471+00:00
-- url     : https://prove2.me/theorems/2f7ede27-f013-4ac7-9916-d4711bfe1eb8
-- title:
--   The law of the random lottery profile $R$
-- statement:
--   Each $R_{is}$ is $U[0,1]$ and, at each school, the $R_{is}$ are iid across students. Under MTB all numbers are independent, and the law of $R$ is the product of $U[0,1]$ over all pairs $(i,s)$. Under STB each student draws one independent $U[0,1]$ number that all schools use, and the law of $R$ is the image of the product over students under the map copying a student's number to every school.
--
--   **Formalization Note** The source states independence across schools for each student and iid-ness within a school; "an independent lottery number at each school" is read as mutual independence of all $R_{is}$. The map used for STB is measurable and both laws are probability measures; both facts are proved in the mission's verification file.
-- source:
--   Narita, (Non)Randomization: A Theory of Quasi-Experimental Evaluation of School Quality, Cowles Foundation Discussion Paper No. 2056R (rev. Aug. 2017), pp.6–7

import Definitions.Def_FirstChoiceDesign_Lottery

namespace FirstChoiceDesign

open MeasureTheory

/-- The law `U[0, 1]` of one lottery number, p.6. -/
noncomputable def unitLaw : Measure ℝ := volume.restrict (Set.Icc 0 1)

/-- The law of the random profile `R = (R_is)`, pp.6–7. Under MTB every number is an independent
`U[0, 1]`: the product over all pairs `(i, s)`. Under STB each student draws one independent
`U[0, 1]`, and all schools use it: the image of the product over students under the map, measurable
(a product of coordinates), that copies a student's number to every school.

**Formalization Note** The page states independence across schools for each student and iid-ness
within a school. Footnote 7 and "an independent lottery number at each school" are read as mutual
independence of all `R_is`. -/
noncomputable def lotteryLaw {n m : ℕ} : Regime → Measure (Lottery n m)
  | .MTB => Measure.pi fun _ => Measure.pi fun _ => unitLaw
  | .STB => (Measure.pi fun _ : Fin n => unitLaw).map fun u i _ => u i

end FirstChoiceDesign


