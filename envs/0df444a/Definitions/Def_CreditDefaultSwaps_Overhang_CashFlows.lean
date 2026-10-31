-- Prove2me | Definitions.Def_CreditDefaultSwaps_Overhang_CashFlows
-- name    : CreditDefaultSwaps_Overhang_CashFlows
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:03:34.53799+00:00
-- url     : https://prove2.me/theorems/136ffd18-d9cb-4a95-8ed0-eff0479c4198
-- title:
--   Discounted equity, firm, debt and CDS cash-flow values
-- statement:
--   For controlled productivity $X$, the running firm cash flow is
--   $$(1-\tau)\Pi X_t-\varphi a_tX_t+\mathbf 1_{\{q_t=\mathrm{false}\}}\tau C.$$
--   Equity receives this flow minus actual service, debt receives service, and the CDS has no running payment. Each flow is discounted by $e^{-rt}$ and is zero at and after bankruptcy. At finite bankruptcy, firm assets and actual debt receive $LX_T$, equity receives zero, and CDS protection receives $\theta\max(C/r-LX_T,0)$. At infinite bankruptcy all terminal payments are defined to be zero before evaluating any terminal state.
--
--   For each of the four claims, the value is the expectation of its discounted running payments and terminal payment. Conditional continuation values at time $t$ use the same remaining payments, conditioned on the filtration, and are multiplied by $e^{rt}$. Admissibility requires integrable running payments on time times the probability space, integrable terminal payments, and integrable remaining payments at every nonnegative time. The fair up-front premium equals the protection value. The creditor portfolio $b$ is actual debt plus protection; firm value uses actual debt, so $V=E+D$ and $b=D+\mathcal C$.
--
--   Differences from the source:
--   - reading: equation (9) writes $(1-\tau)(\Pi x-s)$ in every regime → firm cash flow minus service, with the coupon tax shield only outside workouts; reason: §2 and Appendix A.2 explicitly suspend the shield in workouts (finding I3).
--   - encoding: finite expected discounted values → Bochner and conditional expectations with integrability in admissibility; reason: prevent non-integrable cash flows from silently having value zero.
--   - encoding: stopped equity and a non-occurring bankruptcy → zero running cash after stopping, zero equity terminal cash and zero terminal cash at infinity; reason: preserve limited liability and never-default policies.
-- source:
--   Wong and Yu, Credit Default Swaps and Debt Overhang, Management Science (2021), DOI 10.1287/mnsc.2020.3953, supplied source.pdf, §2, equation (2), printed pp. 7–8 (PDF pp. 8–9); §3.1.1–3.1.3, printed pp. 9–11 (PDF pp. 10–12); Appendix A.2, printed p. 40 (PDF p. 41)

import Definitions.Def_CreditDefaultSwaps_Overhang_Controls

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace CreditDefaultSwaps.Overhang

/-- Firm cash flow: the tax shield is suspended while in a workout. -/
def firmFlow (p : Primitives) (x a : ℝ) (workout : Bool) : ℝ :=
  (1 - p.tax) * p.capacity * x - p.cost * a * x +
    if workout then 0 else p.tax * p.coupon

/-- The four claims: firm assets, equity, actual debt, and CDS protection. -/
inductive Claim where
  | firm | equity | debt | protection
  deriving DecidableEq

def running {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (x : ℝ) (c : Control Ω) (k : Claim) (t : ℝ) (ω : Ω) : ℝ :=
  if 0 ≤ t ∧ (t : WithTop ℝ) < c.bankruptcy ω then
    Real.exp (-p.r * t) *
      match k with
      | .firm => firmFlow p (productivity p N x c t ω) (c.investment t ω) (c.workout t ω)
      | .equity => firmFlow p (productivity p N x c t ω) (c.investment t ω)
          (c.workout t ω) - c.service t ω
      | .debt => c.service t ω
      | .protection => 0
  else 0

/-- An infinite bankruptcy time gives zero terminal cash, without evaluating a
discount factor or productivity at infinity. Equity gets zero at any bankruptcy. -/
def terminal {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) (k : Claim) (ω : Ω) : ℝ :=
  if c.bankruptcy ω = ⊤ then 0 else
    let t := (c.bankruptcy ω).untopD 0
    Real.exp (-p.r * t) *
      match k with
      | .firm | .debt => liquidationCoefficient p * productivity p N x c t ω
      | .equity => 0
      | .protection => defaultProtection p theta (productivity p N x c t ω)

/-- Remaining payments in time-zero units, including a terminal payment at `t`. -/
def futureCash {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) (k : Claim) (t : ℝ) (ω : Ω) : ℝ :=
  (∫ u in Ici t, running p N x c k u ω) +
    if (t : WithTop ℝ) ≤ c.bankruptcy ω then terminal p N theta x c k ω else 0

def value {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) (k : Claim) : ℝ :=
  ∫ ω, futureCash p N theta x c k 0 ω ∂N.law

/-- Time-t value conditional on the current information, in time-t units. -/
def continuation {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) (k : Claim) (t : ℝ) (ω : Ω) : ℝ :=
  Real.exp (p.r * t) * N.law[futureCash p N theta x c k t | N.filtration t] ω

/-- Finiteness conditions keep both Bochner and conditional expectations from
using their non-integrable default value. -/
def CashIntegrable {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) : Prop :=
  ∀ k : Claim,
    Integrable (fun z : ℝ × Ω => running p N x c k z.1 z.2) (volume.prod N.law) ∧
    Integrable (terminal p N theta x c k) N.law ∧
    ∀ t : ℝ, 0 ≤ t → Integrable (futureCash p N theta x c k t) N.law

/-- The up-front fair premium is the protection leg; it is not an equity running cost. -/
def premium {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) : ℝ := value p N theta x c .protection

def creditorPortfolio {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) : ℝ :=
  value p N theta x c .debt + value p N theta x c .protection

end CreditDefaultSwaps.Overhang


