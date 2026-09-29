-- Prove2me | Definitions.Def_DualSSD_MeanRisk_ssdEfficient
-- name    : DualSSD_MeanRisk_ssdEfficient
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-28T00:02:09.107334+00:00
-- url     : https://prove2.me/theorems/83e023ae-a23e-40cb-aaa1-c4ab294ba652
-- title:
--   Strict SSD (2.3) and SSD-efficiency in a set
-- statement:
--   The strict second-degree stochastic dominance is defined by the standard rule
--
--   $$X\succ_{SSD}Y\iff X\succeq_{SSD}Y\ \text{ and }\ Y\not\succeq_{SSD}X.$$
--
--   For a set $Q$ of random variables, a variable $X\in Q$ is **SSD-efficient in $Q$** if there is no $Y\in Q$ with $Y\succ_{SSD}X$.
--
--   SSD-efficiency is the property the mean–risk models of the paper are shown to guarantee for their optimal solutions.
--
--   **Formalization Note** The set $Q$ is a set of functions $\Omega\to\mathbb R$; for a set of $L_q$ elements the mission applies it to the image of the set under the coercion to functions.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 62, eq. (2.3) and the definition of SSD-efficiency

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace DualSSD.MeanRisk

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The strict second-degree stochastic dominance relation (2.3) (Ogryczak–Ruszczyński 2002, §2,
p. 62): `X ≻_SSD Y` iff `X ⪰_SSD Y` and not `Y ⪰_SSD X`. -/
def StrictSSD (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  Shared.SSD P X Y ∧ ¬ Shared.SSD P Y X

/-- SSD-efficiency (Ogryczak–Ruszczyński 2002, §2, p. 62): a random variable `X` (of the set `S`)
is SSD-efficient in `S` if there is no `Y ∈ S` with `Y ≻_SSD X`. -/
def SSDEfficient (P : Measure Ω) (S : Set (Ω → ℝ)) (X : Ω → ℝ) : Prop :=
  ¬ ∃ Y ∈ S, StrictSSD P Y X

end DualSSD.MeanRisk


