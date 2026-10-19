-- Prove2me | Definitions.Def_ImperfReport_Regulator_Report
-- name    : ImperfReport_Regulator_Report
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T22:16:38.167391+00:00
-- url     : https://prove2.me/theorems/8a944bcc-edc1-40f5-919d-2ce726eea4ed
-- title:
--   Reporting systems and the firm's greatest best response
-- statement:
--   A reporting system is a pair of posterior probabilities $(\hat\alpha_G,\hat\alpha_B)$ for the reportable binary value after good and bad reports. It is feasible when $0\le\hat\alpha_B\le\alpha\le\hat\alpha_G\le1$ and $\hat\alpha_B<\hat\alpha_G$. Bayes' rule determines the good-report probability. The perfect system is $(1,0)$; the conservative comparison system is $(1,k)$.
--
--   For each system, the firm chooses an information-acquisition probability $q\in[0,1]$ to maximize its probability of meeting the payoff threshold $k$. After learning the continuous component it discloses exactly when its value exceeds the cutoff; otherwise investors use the nondisclosure mean. Among tied maximizers, the firm chooses the greatest $q$.
--
--   These definitions make the firm's induced information gathering part of the regulator's comparison. **Formalization Note** The separated posterior pair excludes an uninformative report whose conditional posterior is undefined.
-- source:
--   Friedman, Hughes, Michaeli, A Rationale for Imperfect Reporting Standards, SSRN 3636995 (version of November 24, 2020), pp. 10, 12–15, reporting system and firm objective

import Definitions.Def_ImperfReport_Regulator_Model

set_option autoImplicit false
open MeasureTheory Set

namespace ImperfReport.Regulator

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020), p. 10, reporting posteriors.
Formalization Note: the regulator chooses posterior probabilities directly. -/
structure Report where
  aG : ℝ
  aB : ℝ

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 10, feasible posterior pairs. Formalization Note: strict separation excludes
the uninformative pair, for which one of the paper's conditional posteriors is
undefined and the Bayes weight below would have zero denominator. -/
def Report.Valid (r : Report) (M : Model) : Prop :=
  0 ≤ r.aB ∧ r.aB ≤ M.alpha ∧ M.alpha ≤ r.aG ∧ r.aG ≤ 1 ∧ r.aB < r.aG

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 10, Bayes probability of a good report from its two posteriors. -/
noncomputable def pG (M : Model) (r : Report) : ℝ :=
  (M.alpha - r.aB) / (r.aG - r.aB)

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 16, the perfectly informative reporting system. -/
def perfect : Report := ⟨1, 0⟩

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 34, Proof of Proposition 1, the candidate conservative reporting system. -/
def rk (M : Model) : Report := ⟨1, M.k⟩

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
pp. 12–15, probability of clearing the payoff threshold after a report with
posterior `a`. Formalization Note: the firm chooses `q`; `tdag M q` is the
resulting cutoff. It discloses precisely when `s > t`; otherwise investors use
the nondisclosure mean `t`. -/
noncomputable def succ (M : Model) (a q : ℝ) : ℝ :=
  let t := tdag M q
  q * M.mu.real {s : ℝ | t < s ∧ M.k ≤ a + s} +
    (1 - q * M.mu.real (Set.Ioi t)) * (if M.k ≤ a + t then 1 else 0)

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
p. 13, the firm's unconditional probability of meeting the threshold. -/
noncomputable def pass (M : Model) (r : Report) (q : ℝ) : ℝ :=
  pG M r * succ M r.aG q + (1 - pG M r) * succ M r.aB q

/-- Friedman, Hughes, Michaeli, *A Rationale for Imperfect Reporting Standards*,
SSRN 3636995 (version of November 24, 2020),
pp. 10, 13, the firm's best response. Formalization Note: among all probability
maximizers in `[0,1]`, the firm takes the greatest `q` as the paper specifies. -/
noncomputable def FirmBR (M : Model) (r : Report) (q : ℝ) : Prop :=
  q ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ q' ∈ Set.Icc (0 : ℝ) 1, pass M r q' ≤ pass M r q) ∧
  (∀ q' ∈ Set.Icc (0 : ℝ) 1, pass M r q' = pass M r q → q' ≤ q)

end ImperfReport.Regulator


