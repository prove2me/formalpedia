-- Prove2me | Definitions.Def_CreditDefaultSwaps_Overhang_Optimality
-- name    : CreditDefaultSwaps_Overhang_Optimality
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-30T15:04:13.895546+00:00
-- url     : https://prove2.me/theorems/981d98f1-3da0-470a-939f-1e42e183b707
-- title:
--   Nash-consistent admissibility, global dividend optimality and threshold realizations
-- statement:
--   At every nonnegative time, on the event that the firm is alive and in a workout, the actual conditional continuation values must satisfy the individually rational weighted Nash split. The total available value is firm value plus the surviving protection leg; the equity outside option is zero and the creditor outside option is liquidation plus the positive-part CDS payoff. Debt including protection receives the complementary share. Contractual service outside workouts, measurability, stopping-time constraints and finite cash-flow expectations complete admissibility.
--
--   An optimal control is admissible and has at least as much expected discounted equity cash as every admissible control from the same positive initial productivity. The competing controls can change investment, workout, bankruptcy and the service implementation of the Nash split.
--
--   A threshold triple $(x_d,x_i,x_n)$ satisfies $0\le x_d\le x_i\le x_n$. To be optimal it must have, for every $x>0$, an admissible globally optimal realization. That realization stops at the first time productivity is at or below $x_d$, invests at rate $i$ on the surviving states at or above $x_i$, and enters a workout on the surviving states at or below $x_n$. Workouts are reversible. Hitting is specified by its events: $T\le t$ exactly when some $u\in[0,t]$ has $X_u\le x_d$. There is no infimum of an empty set and no optimizer selected by a default value.
--
--   Differences from the source:
--   - encoding: the shareholders' stochastic optimization with Nash renegotiation → comparison over all admissible adapted controls, with the split imposed on actual conditional continuation values; reason: gives an operational meaning to global optimality without assuming first-order equations or comparative statics.
--   - encoding: optimal thresholds → explicitly realized threshold policies for every positive initial state; reason: keeps existence obligations visible and compares all choices satisfying optimality.
--   - encoding: threshold ties and zero boundaries → stop at or below $x_d$, invest at or above $x_i$ while alive, and work out at or below $x_n$; reason: preserve stopping priority, investment at the boundary, and the non-CDS zero-threshold benchmark.
-- source:
--   Wong and Yu, Credit Default Swaps and Debt Overhang, Management Science (2021), DOI 10.1287/mnsc.2020.3953, supplied source.pdf, §3.1.2–3.1.3, equations (5)–(11), printed pp. 10–13 (PDF pp. 11–14); §3.3 and Appendix A.3, printed pp. 16, 46–47 (PDF pp. 17, 47–48)

import Definitions.Def_CreditDefaultSwaps_Overhang_NashSplit
import Definitions.Def_CreditDefaultSwaps_Overhang_CashFlows

open MeasureTheory ProbabilityTheory Set
noncomputable section

namespace CreditDefaultSwaps.Overhang

/-- Renegotiation is individually rational and splits the actual joint
continuation value, including the CDS that survives a successful workout. -/
def BargainingConsistent {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂N.law,
    (t : WithTop ℝ) < c.bankruptcy ω → c.workout t ω = true →
    NashSplit p.weight
      (continuation p N theta x c .firm t ω + continuation p N theta x c .protection t ω)
      0 (reservation p theta (productivity p N x c t ω))
      (continuation p N theta x c .equity t ω)
      (continuation p N theta x c .debt t ω + continuation p N theta x c .protection t ω)

def Admissible {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) : Prop :=
  ControlRegular p N c ∧ CashIntegrable p N theta x c ∧
    BargainingConsistent p N theta x c

/-- Global dividend maximization over adapted investment, workout, service and
bankruptcy decisions satisfying the debt contract and the Nash bargaining rule. -/
def Optimal {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta x : ℝ) (c : Control Ω) : Prop :=
  Admissible p N theta x c ∧
  ∀ other : Control Ω, Admissible p N theta x other →
    value p N theta x other .equity ≤ value p N theta x c .equity

structure Thresholds where
  bankruptcy : ℝ
  investment : ℝ
  renegotiation : ℝ

/-- Stopping is the first passage at or below the bankruptcy boundary. The
event characterization handles an empty hitting set as never stopping, and
does not take a real infimum. Stopping takes precedence over investment ties. -/
def Realizes {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (x : ℝ) (b : Thresholds) (c : Control Ω) : Prop :=
  ∀ᵐ ω ∂N.law, (∀ t : ℝ, 0 ≤ t →
    (c.bankruptcy ω ≤ (t : WithTop ℝ) ↔
      ∃ s ∈ Icc 0 t, productivity p N x c s ω ≤ b.bankruptcy)) ∧
    (∀ t : ℝ, 0 ≤ t → (t : WithTop ℝ) < c.bankruptcy ω →
      c.investment t ω = (if b.investment ≤ productivity p N x c t ω
        then p.improvement else 0) ∧
      (c.workout t ω = true ↔ productivity p N x c t ω ≤ b.renegotiation))

/-- A genuine optimal threshold policy has a controlled realization that
maximizes actual dividends at every positive initial productivity. Existence
is explicit; no arbitrary optimizer selection or first-order root is used. -/
def OptimalThresholds {Ω : Type*} [MeasurableSpace Ω] (p : Primitives) (N : Noise Ω)
    (theta : ℝ) (b : Thresholds) : Prop :=
  0 ≤ b.bankruptcy ∧ b.bankruptcy ≤ b.investment ∧ b.investment ≤ b.renegotiation ∧
  ∀ x : ℝ, 0 < x → ∃ c : Control Ω,
    Realizes p N x b c ∧ Optimal p N theta x c

end CreditDefaultSwaps.Overhang


