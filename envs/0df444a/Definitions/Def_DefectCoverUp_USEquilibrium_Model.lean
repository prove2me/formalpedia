-- Prove2me | Definitions.Def_DefectCoverUp_USEquilibrium_Model
-- name    : DefectCoverUp_USEquilibrium_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T01:16:47.473068+00:00
-- url     : https://prove2.me/theorems/5c97f0f1-8bbb-4ba9-a8a0-bdccdf44c010
-- title:
--   §3–§5, pp. 7–15 — U.S. recall/cover-up game: posterior, demand, profits (1), (3), (5), surplus (6), (7), welfare, tie-broken SPNE
-- statement:
--   A manufacturer who receives a private defect signal chooses whether to report it. After a report, a welfare-maximizing regulator chooses whether to investigate immediately. The parameter record contains price $p$, maximum valuation $\bar v$, maximum harm $\bar h$, recall cost $r$, penalties $K_1,K_2$, discovery probability $\theta$, liability fraction $\alpha$, investigation cost $C$, mean investigation duration $l$, and defect prior $P_D$. The standing conditions include $0<r<p$, $0<l<1$, $\bar v>p+\bar h$, and $0<P_D<1$.
--
--   For harm $h\in(0,\bar h]$ and signal reliability $\rho\in[0,1]$, the posterior and demand rates are
--
--   $$
--   P(D\mid\widetilde D)=\rho+(1-\rho)P_D,\qquad d(p)=1-\frac p{\bar v},\qquad d(p,h)=1-\frac{p+h}{\bar v}.
--   $$
--
--   The definitions retain the paper's interval-integral formulas for manufacturer profit under report and immediate investigation, report without immediate investigation, and no report; the corresponding consumer surpluses; and welfare as profit plus surplus minus investigation cost. The closed-form polynomials $\chi_1$ and $\Omega_1$ are also named for the subsequent identities. The regulator investigates on a welfare tie, and the manufacturer reports on a profit tie. The equilibrium predicate records these two sequential best responses with the regulator's action after no report fixed to no immediate investigation.
--
--   **Formalization Note** The strict condition $0<P_D<1$ makes the paper's reliability normalization and posterior threshold fractions well-defined. The signal's joint distribution and lead-time distribution are represented through the posterior and the mean $l$ used in the paper's expected-payoff equations.
-- source:
--   Cho, DeMiguel & Hwang, Cover-up of vehicle defects: the role of regulator investigation announcements, accepted manuscript (Management Science 67(6), 2021; LBS Research Online eprint 1396), §3–§5, pp. 7–15 (PDF 8–16); Appendix A, (10), p. 28 (PDF 29), and (16)–(17), p. 30 (PDF 31)

import Mathlib

noncomputable section

namespace DefectCoverUp.USEquilibrium

/-- Model parameters other than the harm `h` and the signal reliability `ρ`:
price `p`, maximal valuation `vbar` (valuations uniform on `[0, vbar]`), maximal
harm `hbar`, unit recall cost `r`, penalty coefficients `K1`, `K2` (penalty
`K1 * h + K2`), probability `th` that a later voluntary investigation discovers a
cover-up, liability fraction `al`, investigation cost `C`, mean investigation lead
time `l`, and prior defect probability `PD`. -/
structure Params where
  p : ℝ
  vbar : ℝ
  hbar : ℝ
  r : ℝ
  K1 : ℝ
  K2 : ℝ
  th : ℝ
  al : ℝ
  C : ℝ
  l : ℝ
  PD : ℝ

/-- The paper's standing assumptions (§3), plus `0 < PD < 1`. -/
def Params.Standing (P : Params) : Prop :=
  0 < P.p ∧ 0 < P.r ∧ P.r < P.p ∧ 0 < P.hbar ∧ P.p + P.hbar < P.vbar ∧
  0 < P.C ∧ 0 < P.l ∧ P.l < 1 ∧ 0 ≤ P.th ∧ P.th ≤ 1 ∧
  0 ≤ P.al ∧ P.al ≤ 1 ∧ 0 ≤ P.K1 ∧ 0 ≤ P.K2 ∧ 0 < P.PD ∧ P.PD < 1

/-- Posterior probability of a defect given the defect signal: `ρ + (1 - ρ) * PD`. -/
def post (P : Params) (ρ : ℝ) : ℝ := ρ + (1 - ρ) * P.PD
/-- Demand rate `d(p) = 1 - p / vbar` outside an announced investigation. -/
def d (P : Params) : ℝ := 1 - P.p / P.vbar
/-- Demand rate `d(p,h) = 1 - (p + h) / vbar` during an announced investigation. -/
def dh (P : Params) (h : ℝ) : ℝ := 1 - (P.p + h) / P.vbar
/-- Density of the voluntary-investigation time on `[0, 1 - l]` given a defect. -/
def g (P : Params) (h : ℝ) : ℝ := h / ((1 - P.l) * P.hbar)
/-- Probability that no voluntary investigation happens (time `1`) given a defect. -/
def atom (P : Params) (h : ℝ) : ℝ := 1 - h / P.hbar
/-- Consumer surplus `∫_a^vbar (v - a) / vbar dv` at effective price `a`. -/
def CS (P : Params) (a : ℝ) : ℝ :=
  ∫ v in a..P.vbar, (v - a) * (1 / P.vbar)

/-- Manufacturer's expected profit when she reports and the regulator investigates
immediately, display (1). -/
def piRI (P : Params) (h ρ : ℝ) : ℝ :=
  P.p * (P.l * dh P h + (1 - P.l) * d P) -
    post P ρ * (P.r + h) * P.l * dh P h

/-- Manufacturer's expected profit when she reports and the regulator does not
investigate immediately, display (3). -/
def piRNI (P : Params) (h ρ : ℝ) : ℝ :=
  P.p * d P - post P ρ *
    ((∫ t in (0 : ℝ)..(1 - P.l), P.l * P.p * (d P - dh P h) * g P h) +
      (∫ t in (0 : ℝ)..(1 - P.l), (P.r + h) * (d P * t + dh P h * P.l) * g P h) +
      P.al * h * d P * atom P h)

/-- Manufacturer's expected profit when she does not report, display (5). -/
def piNR (P : Params) (h ρ : ℝ) : ℝ :=
  piRNI P h ρ - post P ρ * P.th * (P.K1 * h + P.K2) *
    ∫ t in (0 : ℝ)..(1 - P.l), g P h

/-- Expected consumer surplus after a report and immediate investigation, display (6). -/
def SRI (P : Params) (h : ℝ) : ℝ :=
  P.l * CS P (P.p + h) + (1 - P.l) * CS P P.p

/-- Expected consumer surplus after a report without immediate investigation,
display (7). -/
def SRNI (P : Params) (h ρ : ℝ) : ℝ :=
  post P ρ *
    ((∫ t in (0 : ℝ)..(1 - P.l), g P h) *
        ((1 - P.l) * CS P P.p + P.l * CS P (P.p + h)) +
      atom P h * (CS P P.p - (1 - P.al) * h * d P)) +
    (1 - ρ) * (1 - P.PD) * CS P P.p

/-- Social welfare (profit + surplus − cost) after report and immediate investigation. -/
def WRI (P : Params) (h ρ : ℝ) : ℝ := piRI P h ρ + SRI P h - P.C
/-- Social welfare after a report without immediate investigation; the regulator
pays `C` only if a later voluntary investigation happens. -/
def WRNI (P : Params) (h ρ : ℝ) : ℝ :=
  piRNI P h ρ + SRNI P h ρ - post P ρ *
    (∫ t in (0 : ℝ)..(1 - P.l), g P h) * P.C

/-- The polynomial `χ₁(h)` of display (10). -/
def chi1 (P : Params) (h : ℝ) : ℝ :=
  h / P.hbar * P.C +
    (P.r + h) / (2 * P.vbar * P.hbar) *
      ((P.vbar - P.p) * (h * (1 + P.l) - 2 * P.hbar * P.l) +
        2 * P.l * h * (P.hbar - h)) +
    P.l * h ^ 2 / (P.vbar * P.hbar) * (P.vbar - h / 2) +
    h * (P.hbar - h) * (P.vbar - P.p) / (P.vbar * P.hbar)

/-- `χ̂₁(h) = χ₁(h) - (l h / vbar)(vbar - h/2) - C`. -/
def chi1hat (P : Params) (h : ℝ) : ℝ :=
  chi1 P h - P.l * h / P.vbar * (P.vbar - h / 2) - P.C

/-- The reliability threshold `ρ'` of display (11). -/
def rhoPrime (P : Params) (h : ℝ) : ℝ :=
  ((P.l * h * (P.vbar - h / 2) / P.vbar + P.C) / chi1 P h - P.PD) /
    (1 - P.PD)

/-- The cubic `Ω₁(h)` of display (16). -/
def Omega1 (P : Params) (h : ℝ) : ℝ :=
  -P.l / (P.hbar * P.vbar) * h ^ 3 +
    (P.K1 * P.th / P.hbar +
      (1 - 2 * P.al + P.l) * (1 - P.p / P.vbar) / (2 * P.hbar) +
      P.l / P.vbar + P.l * (P.p - P.r) / (P.hbar * P.vbar)) * h ^ 2 +
    (P.K2 * P.th / P.hbar +
      (2 * P.al * P.hbar + (1 + P.l) * P.r) * (1 - P.p / P.vbar) / (2 * P.hbar) +
      P.l * P.r / P.vbar - P.l * (1 - P.p / P.vbar)) * h -
    P.l * P.r * (1 - P.p / P.vbar)

/-- `Ω̂₁(h) = Ω₁(h) - p l h / vbar`. -/
def Omega1hat (P : Params) (h : ℝ) : ℝ :=
  Omega1 P h - P.p * P.l * h / P.vbar

/-- The reliability threshold `ρ₁` of display (17). -/
def rho1 (P : Params) (h : ℝ) : ℝ :=
  (P.p * P.l * h / P.vbar / Omega1 P h - P.PD) / (1 - P.PD)

/-- Manufacturer's action after a defect signal: `R` report, `NR` do not report. -/
inductive MAct | R | NR
/-- Regulator's action after a report: `I` investigate immediately, `NI` do not.
(After no report the regulator never investigates immediately.) -/
inductive RAct | I | NI

/-- The regulator investigates a report immediately iff welfare weakly increases
(ties broken toward investigating). -/
def investigates (P : Params) (h ρ : ℝ) : Prop := WRNI P h ρ ≤ WRI P h ρ

/-- Manufacturer's profit from reporting, given the regulator's response to a report. -/
def piReport (P : Params) (h ρ : ℝ) : RAct → ℝ
  | .I => piRI P h ρ
  | .NI => piRNI P h ρ

/-- `σ = (A1, A2)` is the subgame perfect equilibrium: `A2` is the regulator's best
response to a report, and `A1` is the manufacturer's best response to `A2` (ties
broken toward reporting). -/
def IsSPNE (P : Params) (h ρ : ℝ) (σ : MAct × RAct) : Prop :=
  (σ.2 = RAct.I ↔ investigates P h ρ) ∧
    (σ.1 = MAct.R ↔ piNR P h ρ ≤ piReport P h ρ σ.2)

end DefectCoverUp.USEquilibrium


