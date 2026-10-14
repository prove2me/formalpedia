-- Prove2me | Definitions.Def_BBDisclosure_Stage2_Model
-- name    : BBDisclosure_Stage2_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-13T23:32:04.939569+00:00
-- url     : https://prove2.me/theorems/ab07ff3a-d8e3-4cf3-848c-c5dce401ea54
-- title:
--   §2–§4, pp. 8514–8518 — Hotelling duopoly with BBP: turf price games, threshold disclosure (uniform and BBD), second-period equilibrium and ex ante profit
-- statement:
--   This file sets up the second period of the two-firm model of Zhang and Li (2025).
--
--   **Market.** Firm A sits at $0$ and firm B at $1$ of a Hotelling line carrying a unit mass of consumers, with unit transportation cost and full market coverage; the products' base value cancels from every comparison and is omitted. The first-period purchase splits the line at $x_1$ into A's turf $[0,x_1]$ (A's old customers, B's new prospects) and B's turf $[x_1,1]$. In period 2 firm $i\in\{a,b\}$ launches a product of quality $q_i$; $q_a,q_b$ are independent and uniform on $[0,1]$.
--
--   **Beliefs.** A firm discloses its quality to a segment iff it exceeds the segment's threshold $\hat q$. The segment's updated belief is
--   $$\operatorname{bel}(\hat q,q)=\begin{cases} q & \text{if } q>\hat q,\\ \hat q/2 & \text{otherwise,}\end{cases}$$
--   since $E[q\mid q\le\hat q]=\hat q/2$.
--
--   **Turf price games.** On A's turf, with beliefs $(u,w)$ about A and B held by A's old customers, A charges $p_{ao}\ge0$ and B charges $p_{bn}\ge 0$; the stayers with A are $[0,x_a]$ with
--   $$x_a=\min\Big\{x_1,\max\Big\{0,\tfrac{1+p_{bn}-p_{ao}+u-w}{2}\Big\}\Big\},$$
--   A earns $p_{ao}x_a$ and B earns $p_{bn}(x_1-x_a)$. On B's turf, with beliefs $(u,w)$ held by B's old customers, A charges $p_{an}\ge0$, B charges $p_{bo}\ge0$, the switchers to A are $[x_1,x_b]$ with $x_b=\min\{1,\max\{x_1,(1+p_{bo}-p_{an}+u-w)/2\}\}$, A earns $p_{an}(x_b-x_1)$ and B earns $p_{bo}(1-x_b)$. A price pair is a Nash equilibrium of a turf game if both prices are nonnegative and each is a best reply among nonnegative prices.
--
--   **Profiles and equilibrium.** A profile under behavior-based disclosure (BBD) consists of four thresholds $\hat q_{ao},\hat q_{an},\hat q_{bo},\hat q_{bn}$ (own and new segments of each firm) and a price strategy for each turf mapping beliefs to prices. Under uniform disclosure there is one threshold $\hat q_a,\hat q_b$ per firm. A profile is a second-period equilibrium at share $x_1$ and unit disclosure cost $c$ when
--   1. every threshold lies in $[0,1]$;
--   2. for every belief pair in $[0,1]^2$, each turf's price strategy is a Nash equilibrium of that turf's game;
--   3. every threshold is a best response: holding the rival's thresholds, the price strategies and the nondisclosure belief $\hat q/2$ fixed, disclosing is optimal for every quality above the threshold and withholding for every quality below it. Disclosure payoffs are expected over the rival's quality. Disclosing to A's turf costs $x_1c$ and to B's turf $(1-x_1)c$ under BBD; under uniform disclosure one decision covers both turfs and costs $c$.
--
--   **Ex ante profit.** $E(\pi_{a2})$ is the expectation over $(q_a,q_b)$ of firm A's revenues on both turfs at the equilibrium prices and beliefs, minus its disclosure costs; $E(\pi_{b2})$ likewise. Two support conditions are also recorded: under BBD, $1/2-\hat q_{bn}/8<x_1<1/2+\hat q_{an}/8$; under uniform disclosure, $1/2-\hat q_b/8<x_1<1/2+\hat q_a/8$. They say that every belief pair with positive density lies in region 1 of Lemmas 1 and 2.
--
--   This is the model on which every statement of the mission is posed.
--
--   **Formalization Note** Expectations are iterated interval integrals over $[0,1]$. Thresholds are defined by the best-response property, never as roots of the indifference equation, and prices are the Nash equilibria of the clamped turf games, never the closed forms of Lemma 2. Prices are nonnegative, which is how the corner solution $p^*_{bn}=0$ of Lemmas 1–2 arises.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, pp. 8514–8518, §2 Model Setup, §3.1–3.2, §4.1–4.2, (1), (10), Table 1 Notes

import Mathlib

namespace BBDisclosure.Stage2

/-! Zhang and Li, *Retention or Acquisition? Behavior-Based Quality Disclosure*,
Management Sci. 71(10) (2025), §2, §3.1–3.2, §4.1–4.2, pp. 8514–8518.

Second period of the Hotelling duopoly: firm A at 0, firm B at 1, unit mass of consumers,
transportation cost `t = 1`, full coverage (the base value `v` cancels and is omitted),
zero marginal cost. The first-period purchase splits the line at `x1` into A's turf `[0, x1]`
and B's turf `[x1, 1]`. Qualities `qa, qb` are i.i.d. uniform on `[0, 1]`. -/

/-- Consumers' updated belief about a firm's quality `q` in a segment where the firm's
disclosure threshold is `qh`: the true quality if it is disclosed (`qh < q`), otherwise
`E[q | q ≤ qh] = qh / 2` (p. 8515). -/
noncomputable def bel (qh q : ℝ) : ℝ := if qh < q then q else qh / 2

/-- A's turf `[0, x1]`: the stayers with A are `[0, xa]`, where `xa` is the indifferent
consumer `(1 + p_bn − p_ao + u − w) / 2` clamped to the turf. Here `u` (resp. `w`) is the
belief of A's old customers about A's (resp. B's) quality. -/
noncomputable def xaTurf (x1 pao pbn u w : ℝ) : ℝ :=
  min x1 (max 0 ((1 + pbn - pao + u - w) / 2))

/-- B's turf `[x1, 1]`: the switchers to A are `[x1, xb]`, where `xb` is the indifferent
consumer `(1 + p_bo − p_an + u − w) / 2` clamped to the turf. Here `u` (resp. `w`) is the
belief of B's old customers about A's (resp. B's) quality. -/
noncomputable def xbTurf (x1 pan pbo u w : ℝ) : ℝ :=
  min 1 (max x1 ((1 + pbo - pan + u - w) / 2))

/-- A's revenue on A's turf at prices `p = (p_ao, p_bn)`. -/
noncomputable def revAturfA (x1 u w : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * xaTurf x1 p.1 p.2 u w

/-- B's revenue on A's turf at prices `p = (p_ao, p_bn)`. -/
noncomputable def revBturfA (x1 u w : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 * (x1 - xaTurf x1 p.1 p.2 u w)

/-- A's revenue on B's turf at prices `p = (p_an, p_bo)`. -/
noncomputable def revAturfB (x1 u w : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (xbTurf x1 p.1 p.2 u w - x1)

/-- B's revenue on B's turf at prices `p = (p_an, p_bo)`. -/
noncomputable def revBturfB (x1 u w : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.2 * (1 - xbTurf x1 p.1 p.2 u w)

/-- `p = (p_ao, p_bn)` is a Nash equilibrium of the price game on A's turf with beliefs
`(u, w)`: both prices are nonnegative and each is a best reply among nonnegative prices. -/
def IsTurfNashA (x1 u w : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧
  (∀ p' : ℝ, 0 ≤ p' → revAturfA x1 u w (p', p.2) ≤ revAturfA x1 u w p) ∧
  (∀ p' : ℝ, 0 ≤ p' → revBturfA x1 u w (p.1, p') ≤ revBturfA x1 u w p)

/-- `p = (p_an, p_bo)` is a Nash equilibrium of the price game on B's turf with beliefs
`(u, w)`: both prices are nonnegative and each is a best reply among nonnegative prices. -/
def IsTurfNashB (x1 u w : ℝ) (p : ℝ × ℝ) : Prop :=
  0 ≤ p.1 ∧ 0 ≤ p.2 ∧
  (∀ p' : ℝ, 0 ≤ p' → revAturfB x1 u w (p', p.2) ≤ revAturfB x1 u w p) ∧
  (∀ p' : ℝ, 0 ≤ p' → revBturfB x1 u w (p.1, p') ≤ revBturfB x1 u w p)

/-- A second-period profile under behavior-based disclosure (BBD): disclosure thresholds
for A's old (`qao`) and new (`qan`) customers and for B's old (`qbo`) and new (`qbn`)
customers, and a price strategy for each turf mapping the segment's beliefs `(u, w)` to
prices (`σA u w = (p_ao, p_bn)`, `σB u w = (p_an, p_bo)`). -/
structure ProfileBBD where
  qao : ℝ
  qan : ℝ
  qbo : ℝ
  qbn : ℝ
  σA : ℝ → ℝ → ℝ × ℝ
  σB : ℝ → ℝ → ℝ × ℝ

/-- A second-period profile under uniform disclosure: one threshold per firm (`qa`, `qb`)
and the two turf price strategies. -/
structure ProfileU where
  qa : ℝ
  qb : ℝ
  σA : ℝ → ℝ → ℝ × ℝ
  σB : ℝ → ℝ → ℝ × ℝ

/-- `qh` is a best-response disclosure threshold: given the disclosure payoff `D q` at quality
`q` and the nondisclosure payoff `N`, disclosing is optimal for every quality above `qh` and
withholding is optimal for every quality below `qh`. -/
def IsThresholdBR (qh : ℝ) (D : ℝ → ℝ) (N : ℝ) : Prop :=
  ∀ q ∈ Set.Icc (0 : ℝ) 1, (qh < q → N ≤ D q) ∧ (q < qh → D q ≤ N)

/-- Second-period equilibrium under BBD at first-period share `x1` and unit disclosure cost
`c`: thresholds in `[0, 1]`; the price strategies are Nash equilibria of the turf games for
every belief pair in `[0, 1]²`; each threshold is a best response, with the rival's threshold,
the price strategies and the nondisclosure belief `q̂/2` held fixed. Disclosing to A's turf
costs `x1 * c`, to B's turf `(1 - x1) * c` (p. 8517, (10)). -/
def IsStage2EqBBD (c x1 : ℝ) (e : ProfileBBD) : Prop :=
  e.qao ∈ Set.Icc (0 : ℝ) 1 ∧ e.qan ∈ Set.Icc (0 : ℝ) 1 ∧
  e.qbo ∈ Set.Icc (0 : ℝ) 1 ∧ e.qbn ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1, IsTurfNashA x1 u w (e.σA u w)) ∧
  (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1, IsTurfNashB x1 u w (e.σB u w)) ∧
  -- A, own customers (turf A)
  IsThresholdBR e.qao
    (fun q => (∫ qb in (0 : ℝ)..1,
      revAturfA x1 q (bel e.qbn qb) (e.σA q (bel e.qbn qb))) - x1 * c)
    (∫ qb in (0 : ℝ)..1,
      revAturfA x1 (e.qao / 2) (bel e.qbn qb) (e.σA (e.qao / 2) (bel e.qbn qb))) ∧
  -- A, new customers (turf B)
  IsThresholdBR e.qan
    (fun q => (∫ qb in (0 : ℝ)..1,
      revAturfB x1 q (bel e.qbo qb) (e.σB q (bel e.qbo qb))) - (1 - x1) * c)
    (∫ qb in (0 : ℝ)..1,
      revAturfB x1 (e.qan / 2) (bel e.qbo qb) (e.σB (e.qan / 2) (bel e.qbo qb))) ∧
  -- B, own customers (turf B)
  IsThresholdBR e.qbo
    (fun q => (∫ qa in (0 : ℝ)..1,
      revBturfB x1 (bel e.qan qa) q (e.σB (bel e.qan qa) q)) - (1 - x1) * c)
    (∫ qa in (0 : ℝ)..1,
      revBturfB x1 (bel e.qan qa) (e.qbo / 2) (e.σB (bel e.qan qa) (e.qbo / 2))) ∧
  -- B, new customers (turf A)
  IsThresholdBR e.qbn
    (fun q => (∫ qa in (0 : ℝ)..1,
      revBturfA x1 (bel e.qao qa) q (e.σA (bel e.qao qa) q)) - x1 * c)
    (∫ qa in (0 : ℝ)..1,
      revBturfA x1 (bel e.qao qa) (e.qbn / 2) (e.σA (bel e.qao qa) (e.qbn / 2)))

/-- Second-period equilibrium under uniform disclosure at share `x1` and unit cost `c`:
one threshold per firm covers both turfs, so the disclosure payoff adds the firm's revenues
on both turfs and the disclosure cost is `c` (the whole line, p. 8515, (1)). -/
def IsStage2EqU (c x1 : ℝ) (e : ProfileU) : Prop :=
  e.qa ∈ Set.Icc (0 : ℝ) 1 ∧ e.qb ∈ Set.Icc (0 : ℝ) 1 ∧
  (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1, IsTurfNashA x1 u w (e.σA u w)) ∧
  (∀ u ∈ Set.Icc (0 : ℝ) 1, ∀ w ∈ Set.Icc (0 : ℝ) 1, IsTurfNashB x1 u w (e.σB u w)) ∧
  IsThresholdBR e.qa
    (fun q => (∫ qb in (0 : ℝ)..1,
      (revAturfA x1 q (bel e.qb qb) (e.σA q (bel e.qb qb)) +
        revAturfB x1 q (bel e.qb qb) (e.σB q (bel e.qb qb)))) - c)
    (∫ qb in (0 : ℝ)..1,
      (revAturfA x1 (e.qa / 2) (bel e.qb qb) (e.σA (e.qa / 2) (bel e.qb qb)) +
        revAturfB x1 (e.qa / 2) (bel e.qb qb) (e.σB (e.qa / 2) (bel e.qb qb)))) ∧
  IsThresholdBR e.qb
    (fun q => (∫ qa in (0 : ℝ)..1,
      (revBturfA x1 (bel e.qa qa) q (e.σA (bel e.qa qa) q) +
        revBturfB x1 (bel e.qa qa) q (e.σB (bel e.qa qa) q))) - c)
    (∫ qa in (0 : ℝ)..1,
      (revBturfA x1 (bel e.qa qa) (e.qb / 2) (e.σA (bel e.qa qa) (e.qb / 2)) +
        revBturfB x1 (bel e.qa qa) (e.qb / 2) (e.σB (bel e.qa qa) (e.qb / 2))))

/-- Firm A's ex ante second-period profit `E(π_a2)` under BBD (p. 8518, (10)): the expectation
over independent uniform qualities of A's revenue on both turfs minus its disclosure costs. -/
noncomputable def exAnteA_BBD (c x1 : ℝ) (e : ProfileBBD) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (revAturfA x1 (bel e.qao qa) (bel e.qbn qb) (e.σA (bel e.qao qa) (bel e.qbn qb))
      - (if e.qao < qa then x1 * c else 0)
      + revAturfB x1 (bel e.qan qa) (bel e.qbo qb) (e.σB (bel e.qan qa) (bel e.qbo qb))
      - (if e.qan < qa then (1 - x1) * c else 0))

/-- Firm B's ex ante second-period profit `E(π_b2)` under BBD (p. 8517, (10)). -/
noncomputable def exAnteB_BBD (c x1 : ℝ) (e : ProfileBBD) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (revBturfA x1 (bel e.qao qa) (bel e.qbn qb) (e.σA (bel e.qao qa) (bel e.qbn qb))
      - (if e.qbn < qb then x1 * c else 0)
      + revBturfB x1 (bel e.qan qa) (bel e.qbo qb) (e.σB (bel e.qan qa) (bel e.qbo qb))
      - (if e.qbo < qb then (1 - x1) * c else 0))

/-- Firm A's ex ante second-period profit `E(π_a2)` under uniform disclosure (p. 8516, (1)). -/
noncomputable def exAnteA_U (c x1 : ℝ) (e : ProfileU) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (revAturfA x1 (bel e.qa qa) (bel e.qb qb) (e.σA (bel e.qa qa) (bel e.qb qb))
      + revAturfB x1 (bel e.qa qa) (bel e.qb qb) (e.σB (bel e.qa qa) (bel e.qb qb))
      - (if e.qa < qa then c else 0))

/-- Firm B's ex ante second-period profit `E(π_b2)` under uniform disclosure (p. 8515, (1)). -/
noncomputable def exAnteB_U (c x1 : ℝ) (e : ProfileU) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (revBturfA x1 (bel e.qa qa) (bel e.qb qb) (e.σA (bel e.qa qa) (bel e.qb qb))
      + revBturfB x1 (bel e.qa qa) (bel e.qb qb) (e.σB (bel e.qa qa) (bel e.qb qb))
      - (if e.qb < qb then c else 0))

/-- Under BBD, every belief pair on the support lies in Lemma 2's region 1:
`1/2 − q̂_bn/8 < x1 < 1/2 + q̂_an/8`. -/
def SupportRegion1BBD (x1 : ℝ) (e : ProfileBBD) : Prop :=
  1 / 2 - e.qbn / 8 < x1 ∧ x1 < 1 / 2 + e.qan / 8

/-- Under uniform disclosure, every belief pair on the support lies in Lemma 1's region 1:
`1/2 − q̂_b/8 < x1 < 1/2 + q̂_a/8`. -/
def SupportRegion1U (x1 : ℝ) (e : ProfileU) : Prop :=
  1 / 2 - e.qb / 8 < x1 ∧ x1 < 1 / 2 + e.qa / 8

end BBDisclosure.Stage2


