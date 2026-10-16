-- Prove2me | Definitions.Def_BatteryLease_WinWin_Setting
-- name    : BatteryLease_WinWin_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T06:19:33.154737+00:00
-- url     : https://prove2.me/theorems/5df53752-5f0e-4828-8952-0fd6c9985e9f
-- title:
--   §3–§4 — battery leasing with uniform needs: Table 1 costs, simple leasing (benchmark), flexible leasing with up/downgrade rates, acquisition Q_h, (1)–(2), equilibria, total customer cost and capacity
-- statement:
--   This file fixes the base model of Shi and Hu's *Battery as a Service* (§3–§4): an electric-vehicle manufacturer leases batteries to a unit mass of customers, first under **simple battery leasing** (the benchmark) and then under **flexible battery leasing**, where customers may up- or downgrade their battery for peak usage.
--
--   **Parameters.** $a$ is the upper end of the peak need for range, $\rho$ the share of regular usage time, $r_h$ the range of a high-capacity battery and $c_h$ its acquisition cost. The low-capacity battery has range $r_l=0$, lease rate $p_l=0$ and acquisition cost $c_l=0$; these normalizations are built into every formula below. The **standing assumptions** of §3 are
--   $$a>1,\qquad \frac{a}{2+a}<\rho<1,\qquad 0<r_h\le a,\qquad 0\le c_h\le(1-\rho)a .$$
--
--   **Needs.** A customer's regular need for range is $d\sim\mathcal U[0,1]$, known when leasing; the peak need is $D\sim\mathcal U[0,a]$, independent of $d$ and learned later. $\mathbb E[f(D)]=\frac1a\int_0^a f(D)\,dD$, and the *volume* of the customers with a property is the Lebesgue measure of the corresponding set of $d\in[0,1]$. Write $x^+=\max(x,0)$.
--
--   **Costs (Table 1).** Leasing type $i$ for regular usage costs $(d-r_i)^++p_i$ per unit time. With upgrade rate $\bar p_h$ and downgrade rate $\bar p_l$, the peak-usage cost is $(D-r_h)^++p_h$ (primary $h$, keep), $D+\bar p_l$ (primary $h$, downgrade), $(D-r_h)^++\bar p_h$ (primary $l$, upgrade), $D$ (primary $l$, keep).
--
--   **Simple leasing (§3.4).** At lease rate $p_h$ a customer leases low capacity iff
--   $$\rho d+(1-\rho)\mathbb E[D]\le p_h+\rho(d-r_h)^++(1-\rho)\mathbb E[(D-r_h)^+].$$
--   $\tau^b(p_h)$ is the volume of these customers; the profit is $\Pi^b(p_h)=(1-\tau^b)(p_h-c_h)$; the total customer cost $CT^b$ is $\int_0^1$ of the smaller of the two costs; the total capacity is $BT^b=(1-\tau^b)r_h$. A benchmark optimum is any $p_h\in\mathbb R$ maximizing $\Pi^b$.
--
--   **Flexible leasing (§4).** Given $\tau$ low lessees, a low lessee upgrades iff $(D-r_h)^++\bar p_h\le D$ and a high lessee downgrades iff $(D-r_h)^++p_h>D+\bar p_l$; the upgrade and downgrade volumes $U,V$ are $\tau$ resp. $1-\tau$ times the probability of these events. The extra acquisition is $Q_h=[U-V]^+$ and the peak-period objective (1) is
--   $$(1-\tau)p_h+V(\bar p_l-p_h)+U\bar p_h-c_hQ_h/(1-\rho),$$
--   maximized over the rates with $\bar p_h\le a$, $p_h-a\le\bar p_l\le p_h$ (p. 13). Customers anticipate the rates: with $\mathbb E[c_l(D)]=\mathbb E\min(D,(D-r_h)^++\bar p_h)$ and $\mathbb E[c_h(D)]=\mathbb E\min((D-r_h)^++p_h,D+\bar p_l)$, a customer leases low iff
--   $$\rho d+(1-\rho)\mathbb E[c_l(D)]\le\rho\,(p_h+(d-r_h)^+)+(1-\rho)\mathbb E[c_h(D)].$$
--   A **continuation** at $p_h$ is $(\tau,\bar p_h,\bar p_l)$ with feasible rates that maximize (1) given $\tau$, and $\tau$ equal to the low-lease volume these rates induce (rational expectations). Its total profit (2) is $\Pi^f=\rho(1-\tau)p_h+(1-\rho)\cdot(1)-(1-\tau)c_h$. A **flexible equilibrium** is a continuation at some $p_h$ whose profit is at least that of every continuation at every lease rate. $CT^f$ is $\int_0^1$ of the smaller of the two expected costs, and $BT^f=(1-\tau+Q_h)r_h$.
--
--   These objects carry every statement of the mission: Lemmas 1–4 and Propositions 1, 2, 4, 5 and 6 are all stated about them.
--
--   **Formalization Note** Every volume, expected cost and equilibrium is defined from Table 1 and the timeline, never by the paper's closed forms; those are the theorems. Ties follow the proofs (Online Appendix pp. 1–3): low lease when indifferent, upgrade on $\le$, downgrade on $>$. The lease rate ranges over all of $\mathbb R$; the paper's remark "we require $p_h<\min(1,r_h)$" (p. 9) is not imposed. The flexible equilibrium asks the chosen continuation to beat every continuation at every lease rate, which is the subgame-perfect notion when continuations are unique, and is not vacuous where some lease rate has no continuation. `pbh`, `pbl` denote $\bar p_h$, $\bar p_l$; `EU a f` is $\mathbb E f(D)$; `custVol` is the volume of customers.
-- source:
--   Shi, Hu, Battery as a Service: Flexible Electric Vehicle Battery Leasing, M&SOM (2024), doi:10.1287/msom.2022.0587, authors' manuscript of 13 January 2024, pp. 7–14, §3.1–§3.4, Table 1, §4, (1)–(2); Online Appendix pp. 1–5 (PDF 33–37)

import Mathlib

open MeasureTheory

namespace BatteryLease.WinWin

/-! Shi–Hu, *Battery as a Service* (M&SOM 2024), §3–§4: the base model.
Parameters: `a` (peak need `D ~ U[0,a]`), `ρ` (regular-usage time share), `rh` (high-capacity
range `r_h`), `ch` (high-capacity acquisition cost `c_h`). Normalizations `r_l = 0`, `p_l = 0`,
`c_l = 0` are built in. `pbh`, `pbl` are the up/downgrade rates `p̄_h`, `p̄_l`. -/

/-- Standing assumptions of §3: `a > 1`, `ρ ∈ (a/(2+a), 1)`, `0 < r_h ≤ a`, `0 ≤ c_h ≤ (1-ρ)a`. -/
def Standing (a ρ rh ch : ℝ) : Prop :=
  1 < a ∧ (a / (2 + a) < ρ ∧ ρ < 1) ∧ (0 < rh ∧ rh ≤ a) ∧ (0 ≤ ch ∧ ch ≤ (1 - ρ) * a)

/-- Positive part `(x)⁺`. -/
def pos (x : ℝ) : ℝ := max x 0

/-- Expectation of `f D` for `D ~ U[0,a]`. -/
noncomputable def EU (a : ℝ) (f : ℝ → ℝ) : ℝ := (∫ D in (0:ℝ)..a, f D) / a

/-- Mass of the customers `d ∈ [0,1]` (`d ~ U[0,1]`) with property `P`. -/
noncomputable def custVol (P : ℝ → Prop) : ℝ :=
  (volume {d : ℝ | d ∈ Set.Icc (0:ℝ) 1 ∧ P d}).toReal

/-! ### Simple battery leasing (benchmark, §3.4) -/

/-- Under simple leasing, a customer with regular need `d` leases low capacity (ties included). -/
def benchLow (a ρ rh ph d : ℝ) : Prop :=
  ρ * d + (1 - ρ) * EU a (fun D => D) ≤
    ph + ρ * pos (d - rh) + (1 - ρ) * EU a (fun D => pos (D - rh))

/-- Low-capacity lease volume `τ` under simple leasing at lease rate `p_h`. -/
noncomputable def tauB (a ρ rh ph : ℝ) : ℝ := custVol (benchLow a ρ rh ph)

/-- Manufacturer profit `(1-τ)(p_h - c_h)` under simple leasing. -/
noncomputable def benchProfit (a ρ rh ch ph : ℝ) : ℝ := (1 - tauB a ρ rh ph) * (ph - ch)

/-- Total customer cost `CT^b` under simple leasing (each customer pays the cheaper option). -/
noncomputable def benchCC (a ρ rh ph : ℝ) : ℝ :=
  ∫ d in (0:ℝ)..1, min (ρ * d + (1 - ρ) * EU a (fun D => D))
    (ph + ρ * pos (d - rh) + (1 - ρ) * EU a (fun D => pos (D - rh)))

/-- Total battery capacity `BT^b = (1-τ) r_h` under simple leasing. -/
noncomputable def benchCap (a ρ rh ph : ℝ) : ℝ := (1 - tauB a ρ rh ph) * rh

/-- `p_h` is an optimal simple lease rate (maximizes profit over all real `p`). -/
def IsBenchOpt (a ρ rh ch ph : ℝ) : Prop := ∀ p : ℝ, benchProfit a ρ rh ch p ≤ benchProfit a ρ rh ch ph

/-! ### Flexible battery leasing (§4) -/

/-- Peak upgrade volume (Table 1): a low-capacity customer upgrades iff `(D-r_h)⁺ + p̄_h ≤ D`. -/
noncomputable def upVol (a rh τ pbh : ℝ) : ℝ :=
  τ * (volume {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ pos (D - rh) + pbh ≤ D}).toReal / a

/-- Peak downgrade volume (Table 1): a high-capacity customer downgrades iff
`(D-r_h)⁺ + p_h > D + p̄_l`. -/
noncomputable def downVol (a rh τ ph pbl : ℝ) : ℝ :=
  (1 - τ) * (volume {D : ℝ | D ∈ Set.Icc (0:ℝ) a ∧ D + pbl < pos (D - rh) + ph}).toReal / a

/-- Additional high-capacity acquisition `Q_h = [upgrades - downgrades]⁺`. -/
noncomputable def acq (a rh τ ph pbh pbl : ℝ) : ℝ :=
  max (upVol a rh τ pbh - downVol a rh τ ph pbl) 0

/-- Peak-period objective (1), with the Table-1 volumes. -/
noncomputable def peakObj (a ρ rh ch τ ph pbh pbl : ℝ) : ℝ :=
  (1 - τ) * ph + downVol a rh τ ph pbl * (pbl - ph) + upVol a rh τ pbh * pbh
    - ch * acq a rh τ ph pbh pbl / (1 - ρ)

/-- The rate set required on p. 13: `p̄_h ≤ a` and `p_h - a ≤ p̄_l ≤ p_h`. -/
def RateFeasible (a ph pbh pbl : ℝ) : Prop := pbh ≤ a ∧ ph - a ≤ pbl ∧ pbl ≤ ph

/-- Expected peak cost `E[c_l(D)]` of a low-capacity lessee who upgrades optimally. -/
noncomputable def ECl (a rh pbh : ℝ) : ℝ := EU a (fun D => min D (pos (D - rh) + pbh))

/-- Expected peak cost `E[c_h(D)]` of a high-capacity lessee who downgrades optimally. -/
noncomputable def ECh (a rh ph pbl : ℝ) : ℝ := EU a (fun D => min (pos (D - rh) + ph) (D + pbl))

/-- Under flexible leasing, a customer with regular need `d` leases low capacity (ties included). -/
def flexLow (a ρ rh ph pbh pbl d : ℝ) : Prop :=
  ρ * d + (1 - ρ) * ECl a rh pbh ≤ ρ * (ph + pos (d - rh)) + (1 - ρ) * ECh a rh ph pbl

/-- Low-capacity lease volume under flexible leasing, given anticipated rates `p̄_h, p̄_l`. -/
noncomputable def tauF (a ρ rh ph pbh pbl : ℝ) : ℝ := custVol (flexLow a ρ rh ph pbh pbl)

/-- A continuation at `p_h`: feasible rates optimal in (1) given `τ`, and `τ` the volume those
rates induce (rational expectations). -/
def IsContinuation (a ρ rh ch ph τ pbh pbl : ℝ) : Prop :=
  RateFeasible a ph pbh pbl ∧
  (∀ q r : ℝ, RateFeasible a ph q r → peakObj a ρ rh ch τ ph q r ≤ peakObj a ρ rh ch τ ph pbh pbl) ∧
  τ = tauF a ρ rh ph pbh pbl

/-- Total profit (2): `ρ(1-τ)p_h + (1-ρ)·(1) - (1-τ)c_h`. -/
noncomputable def flexProfit (a ρ rh ch ph τ pbh pbl : ℝ) : ℝ :=
  ρ * (1 - τ) * ph + (1 - ρ) * peakObj a ρ rh ch τ ph pbh pbl - (1 - τ) * ch

/-- Flexible equilibrium: a continuation whose profit is at least that of every continuation at
every lease rate. -/
def IsFlexEq (a ρ rh ch ph τ pbh pbl : ℝ) : Prop :=
  IsContinuation a ρ rh ch ph τ pbh pbl ∧
  ∀ ph' τ' q r : ℝ, IsContinuation a ρ rh ch ph' τ' q r →
    flexProfit a ρ rh ch ph' τ' q r ≤ flexProfit a ρ rh ch ph τ pbh pbl

/-- Total customer cost `CT^f` under flexible leasing. -/
noncomputable def flexCC (a ρ rh ph pbh pbl : ℝ) : ℝ :=
  ∫ d in (0:ℝ)..1, min (ρ * d + (1 - ρ) * ECl a rh pbh)
    (ρ * (ph + pos (d - rh)) + (1 - ρ) * ECh a rh ph pbl)

/-- Total battery capacity `BT^f = (1 - τ + Q_h) r_h` under flexible leasing. -/
noncomputable def flexCap (a rh τ ph pbh pbl : ℝ) : ℝ := (1 - τ + acq a rh τ ph pbh pbl) * rh

end BatteryLease.WinWin


