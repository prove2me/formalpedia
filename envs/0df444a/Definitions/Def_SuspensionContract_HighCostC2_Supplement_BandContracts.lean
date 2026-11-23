-- Prove2me | Definitions.Def_SuspensionContract_HighCostC2_Supplement_BandContracts
-- name    : SuspensionContract_HighCostC2_Supplement_BandContracts
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T21:00:39.146272+00:00
-- url     : https://prove2.me/theorems/c6eafae1-2125-40f6-9d2b-135b7c90de3a
-- title:
--   Definition 1 contracts, their initial transfer extension and the two special contracts
-- statement:
--   A band has suspension thresholds $\underline\theta,\bar\theta$, a random-switch boundary $\check w$, and a payment cutoff $\hat w$. Its bank account is driven by the actual event streams, using (11)–(14); it is not defined as the agent's conditional utility. While working its deterministic drift is $-\rho(\bar w-W_{t-})$ above $\check w$. Arrivals increase the account by $\min(\hat w-W_{t-},\beta)$ and pay any excess above $\hat w$. A random switch reduces the account by $\check w-\underline\theta$.
--
--   The random-switch rate is
--   $$q_t=\frac{\rho(\bar w-\check w)}{\check w-\underline\theta}\,\mathbf1_{W_{t-}=\check w,E_{t-}=I}$$
--   when $\check w>\underline\theta$, and zero when the two thresholds coincide. Deterministic switching uses the upper and lower hitting boundaries of (14), with zero utility absorbing under the source's termination convention. Initial utility below $\check w$ uses the public lottery of endnote 7, and initial utility above $\hat w$ pays the excess immediately. The corrected Lemma 1 excludes reachable positive coincident suspension thresholds because they require instantaneous cycling; zero initial utility, the absorbing always-work top state, and all-zero termination are retained.
--
--   The always-work contract uses $(0,0,\bar w,\bar w)$ and initial utility $\bar w$. Never hiring means zero payments and no switches. These are actual process specifications, not arbitrary payoff labels.
--
--   The effort reimbursement $b\,dt$ of (13) is recorded as a flow density equal to $b$ while the current state is working. It differs from $b\mathbf 1_{E_{t-}=I}$ only at the countably many switching times, so the payment measure is (13)'s. Using the current state keeps the pathwise limited-liability constraint (LL) $\ell_t\ge b\mathbf 1_{E_t=I}$ satisfiable at restart times.
-- source:
--   Cao, Sun, Tian, Punish Underperformance with Suspension: Optimal Dynamic Contracts in the Presence of Switching Cost, Management Science (2024), doi:10.1287/mnsc.2023.4845, authors' manuscript (2023-03-15), SHA-256 39e9a1afe4665462f93250c221173be577581eb346a2679660d4de54a49b3304, Definition 1 pp.12–15, (11)–(16); termination discussion p.15; endnote 7 p.34

import Mathlib
import Definitions.Def_SuspensionContract_HighCostC2_Supplement_Verification

namespace SuspensionContract.HighCostC2.Supplement

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

/-- Definition 1's four thresholds: payment cutoff wHi, random-switch boundary wLo,
and lower/upper suspension thresholds thLo/thHi. These are distinct from the analytic hats. -/
structure Band where
  thLo : ℝ
  wLo : ℝ
  thHi : ℝ
  wHi : ℝ

/-- The printed weak ordering in Definition 1 and Lemma 1. -/
def Band.Ordered (B : Band) (P : Params) : Prop :=
  0 ≤ B.thLo ∧ B.thLo ≤ B.wLo ∧ B.wLo ≤ B.thHi ∧ B.thHi ≤ B.wHi ∧ B.wHi ≤ P.wbar

/-- Exclude a zero-duration positive suspension, for which (14) would require an accumulation
of switches. The all-zero (permanent termination) case is retained. -/
def Band.NoInstantCycle (B : Band) : Prop := B.thHi = 0 ∨ B.thLo < B.thHi

/-- The source's restricted initial domain, prior to the endnote-7 extension. -/
def Band.InitialDomain (B : Band) (w : ℝ) : Prop := w = 0 ∨ w ∈ Icc B.wLo B.wHi

open Classical in
/-- The predictable intensity (12); the equal-threshold branch has no random switches. -/
noncomputable def bandIntensity (P : Params) (B : Band) (x : ℝ) : ℝ :=
  if B.thLo < B.wLo ∧ x = B.wLo then P.ρ * (P.wbar - B.wLo) / (B.wLo - B.thLo) else 0

open Classical in
/-- The bank-account drift of (11), before events. -/
noncomputable def bankDrift (P : Params) (B : Band) (x : ℝ) (e : Prop) : ℝ :=
  if e then (if x ∈ Ioc B.wLo B.wHi then P.ρ * (x - P.wbar) else 0) else P.ρ * x

open Classical in
/-- Equations (11)–(14) for an actual contract. X is a bank-account process computed from
observable events, not the conditional promised utility. Equating it to that utility is Lemma 1.
The initial transfer/randomization follows endnote 7. -/
def IsBandContract (P : Params) (B : Band) (w : ℝ) (G : Contract) : Prop :=
  WellFormed P G ∧ ∃ X : ℝ≥0 → G.Ω → ℝ,
    (∀ t, Measurable[G.data.F t] (X t)) ∧
    (∀ ω, CadlagOnHalfLine (fun t => X t ω)) ∧
    (∀ ω, 0 ≤ X 0 ω ∧ X 0 ω ≤ B.wHi) ∧
    (∀ ν, AdmissibleEffort P G ν → ∀ᵐ ω ∂G.data.law ν,
      -- The ordinary initial domain is deterministic. Below it, randomize between 0 and wLo.
      (if w = 0 then X 0 ω = 0 ∧ G.data.payment ω {0} = 0
       else if w < B.wLo then
         (X 0 ω = 0 ∨ X 0 ω = B.wLo) ∧ G.data.payment ω {0} = 0
       else X 0 ω = min w B.wHi ∧ G.data.payment ω {0} = ENNReal.ofReal (max 0 (w - B.wHi))) ∧
      G.data.D.jump 0 ω = (if 0 < X 0 ω then 1 else 0) ∧
      -- The event equations govern the entire half-line, not just until the first switch.
      (∀ T : ℝ≥0,
        let Xm := preValue X (X 0)
        X T ω = X 0 ω +
          (∫ t in Ioc 0 T, bankDrift P B (Xm t ω) (workingBefore G.data t ω) ∂timeMeasure) +
          (∫ t in Ioc 0 T,
            if workingBefore G.data t ω then min (B.wHi - Xm t ω) P.β else 0 ∂G.data.N.measure ω) -
          ∫ t in Ioc 0 T,
            if workingBefore G.data t ω then B.wLo - B.thLo else 0 ∂G.data.Q.measure ω) ∧
      (∀ t : ℝ≥0, 0 < t →
        let Xm := preValue X (X 0)
        G.data.q t ω = (if workingBefore G.data t ω then bandIntensity P B (Xm t ω) else 0) ∧
        -- The flow is a dt-density: (13)'s b dt 1{E_{t-}=I} is represented by the current
        -- state, which differs only at countably many switching times and keeps (LL) pathwise.
        G.data.flow t ω = (if working G.data t ω then P.b else 0) ∧
        (G.data.payment ω {t}).toReal =
          (if workingBefore G.data t ω then max 0 (Xm t ω + P.β - B.wHi) * G.data.N.jump t ω else 0) ∧
        G.data.D.jump t ω =
          (if (¬workingBefore G.data t ω ∧ 0 < B.thHi ∧ X t ω = B.thHi) ∨
              (workingBefore G.data t ω ∧ B.thLo = B.wLo ∧ X t ω = B.wLo) then 1 else 0))) ∧
    (∀ ν, AdmissibleEffort P G ν →
      (∫⁻ ω, ENNReal.ofReal (X 0 ω) ∂G.data.law ν) = ENNReal.ofReal (min w B.wHi))

/-- The special always-work contract (15), with β paid at each arrival plus cost reimbursement. -/
noncomputable def alwaysBand (P : Params) : Band := ⟨0, 0, P.wbar, P.wbar⟩

/-- Never hire: zero payments and no state switches under every admissible effort law. -/
def IsNeverHire (P : Params) (G : Contract) : Prop :=
  WellFormed P G ∧ ∀ ν, AdmissibleEffort P G ν →
    ∀ᵐ ω ∂G.data.law ν, G.data.payment ω = 0 ∧ G.data.D.measure ω = 0 ∧ G.data.Q.measure ω = 0

/-- The special always-work contract (15), constructed by the same event equations. -/
def IsAlwaysWork (P : Params) (G : Contract) : Prop :=
  IsBandContract P (alwaysBand P) P.wbar G

end SuspensionContract.HighCostC2.Supplement


