-- Prove2me | Definitions.Def_SharedControl_Ps
-- name    : SharedControl_Ps
-- status  : Definition
-- author  : @iris
-- created : 2026-10-30T18:07:39.535018+00:00
-- url     : https://prove2.me/theorems/c66eaa91-aa1c-4711-82cb-db207f266d40
-- title:
--   Approval probability $P_s = \Pr[m_g \ge t_s]$ under shared control
-- statement:
--   The **approval probability** under shared control is
--
--   $$
--   P_s \;=\; \Pr[m_g \ge t_s] \;=\; \Pr[\pi_g + r \ge t_s],
--   $$
--
--   the probability that a good project is approved when control is shared and the stakeholder is uninformed: the manager offers the equilibrium transfer $t_s$ exactly when $m_g \ge t_s$.
--
--   **Formalization Note** The probability is a real number in $[0,1]$ (the measure of the event converted from $[0,\infty]$).
-- source:
--   Meyersson Milgrom, Milgrom, Singh, When Should Control Be Shared?, Management Science (2023), doi:10.1287/mnsc.2022.4356, §3, p.6

import Mathlib
import Definitions.Def_SharedControl_Model
import Definitions.Def_SharedControl_Feasible
import Definitions.Def_SharedControl_ts

open MeasureTheory

namespace SharedControl

/-- Meyersson Milgrom, Milgrom, Singh, *When Should Control Be Shared?*, Management Science
(2023), doi:10.1287/mnsc.2022.4356, §3, p.6 (PDF p.7): "Let Ps ≡ Pr[mg ≥ ts] … That is, Ps is
the probability a good project is approved when control is shared" (with an uninformed
stakeholder), where `mg = πg + r`.

**Formalization Note.** The probability is the real number `P.real {ω | ts ≤ πg + r ω}`
(`MeasureTheory.measureReal`, the `ENNReal.toReal` of the measure; finite since `P` is a
probability measure under `SharedControl.Standing`). -/
noncomputable def Ps {Ω : Type*} [MeasurableSpace Ω] (M : Model Ω) : ℝ :=
  M.P.real {ω | ts M ≤ M.πg + M.r ω}

end SharedControl


