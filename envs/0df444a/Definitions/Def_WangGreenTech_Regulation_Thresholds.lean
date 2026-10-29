-- Prove2me | Definitions.Def_WangGreenTech_Regulation_Thresholds
-- name    : WangGreenTech_Regulation_Thresholds
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-29T02:33:12.642232+00:00
-- url     : https://prove2.me/theorems/f469ab81-eafb-49cf-aa1e-7b4abf698c3e
-- title:
--   Competition bounds and the appendix branch conditions
-- statement:
--   For $C\ge0$, define
--   $$B(\epsilon,C,r)=\inf\left(\left\{\frac{2\epsilon+Ct^r}{t}:0<t\le1\right\}\cup\left\{\frac{2\epsilon+C(1-s^r)}{1-s}:0\le s<1\right\}\right).$$
--   Write $b^{(2)}=B(\epsilon,(1-q)(f_H-m_L),r)$ and $b^{(1)}=B(\epsilon,(1-q)(m_H-m_L),r)$.
--
--   The bundle also defines the increasing-branch root condition
--   $$(1-r)C^{-1/(r-1)}(B/r)^{r/(r-1)}+B=2\epsilon+C,\qquad B>rC.$$
--   For a candidate competition intensity $b$, the printed admissibility test is separated into $C=0$ ($b\le2\epsilon$), $r=1$ ($b\le2\epsilon+C$), and the positive-$C$, nonunit-$r$ cases. If $r<\min\{1,b/C\}$ use the preceding expression with $b$ on the left and $\le$ on the right; if $r>\max\{1,b/C\}$ use
--   $$b\le r\left(\frac{2\epsilon}{r-1}\right)^{1-1/r}C^{1/r};$$
--   otherwise use $b\le2\epsilon+C$.
--
--   The bundle also proves the structural identity $B(0,0,r)=0$ for every real $r$: both ratio families then consist of zero. This concerns total definitions outside the positive-noise economic domain.
--
--   The intrinsic bound records the two derivative constraints without an implicit choice of branch. The separate source-threshold characterization item asks for their equivalence to the printed tests and for the root characterization.
--
--   **Formalization Note** This is a real infimum. Nonemptiness and lower boundedness, including the value $B(\epsilon,0,r)=2\epsilon$, are theorem conclusions. The $C=0$ and $r=1$ guards prevent evaluating singular printed branches in valid uses. No formula agreement or monotonicity is assumed.
-- source:
--   Wang, Cho and Scheller-Wolf, Green Technology Development and Adoption: Competition, Regulation, and Uncertainty—A Global Game Approach, Management Science forthcoming artifact, https://doi.org/10.1287/mnsc.2019.3538, Appendix A pp. 2–3, 9, 11–12 (PDF 35–36, 42, 44–45), equations (6)–(7), (13), (16)

import Definitions.Def_WangGreenTech_Regulation_Model

set_option autoImplicit false

namespace WangGreenTech.Regulation

open Set
noncomputable section

/-- The two derivative constraints from Appendix A, pp. 2–3 and 11–12. -/
def thresholdRatios (ε C r : ℝ) : Set ℝ :=
  ((fun t : ℝ => (2 * ε + C * t ^ r) / t) '' Ioc 0 1) ∪
  ((fun s : ℝ => (2 * ε + C * (1 - s ^ r)) / (1 - s)) '' Ico 0 1)

/-- Intrinsic competition bound; its agreement with (7)/(13) is a theorem obligation. -/
def competitionBound (ε C r : ℝ) : ℝ := sInf (thresholdRatios ε C r)

def followerBound (p : Model) : ℝ :=
  competitionBound p.ε ((1 - p.q) * (p.fH - p.mL)) p.r

def leaderBound (p : Model) : ℝ :=
  competitionBound p.ε ((1 - p.q) * (p.mH - p.mL)) p.r

/-- Equation (6), used only when 0 < r < 1 and C > 0. -/
def lowerBranch (ε C r B : ℝ) : Prop :=
  r * C < B ∧ (1 - r) * C ^ (-(1 / (r - 1))) * (B / r) ^ (r / (r - 1)) + B =
    2 * ε + C

/-- Candidate-b tests as printed in (7)/(13), with zero C and unit r separated. -/
def sourceCompetitionCondition (ε C r b : ℝ) : Prop :=
  if C = 0 then b ≤ 2 * ε
  else if r = 1 then b ≤ 2 * ε + C
  else if r < min 1 (b / C) then
    (1 - r) * C ^ (-(1 / (r - 1))) * (b / r) ^ (r / (r - 1)) + b ≤ 2 * ε + C
  else if max 1 (b / C) < r then
    b ≤ r * (2 * ε / (r - 1)) ^ (1 - 1 / r) * C ^ (1 / r)
  else b ≤ 2 * ε + C

/-- Zero can be an attained infimum, not only a total-function default. -/
lemma competitionBound_zero (r : ℝ) : competitionBound 0 0 r = 0 := by
  simp [competitionBound, thresholdRatios, Set.Nonempty.image_const, Set.nonempty_Ioc, Set.nonempty_Ico]

end
end WangGreenTech.Regulation


