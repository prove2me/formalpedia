-- Prove2me | Definitions.Def_BBDisclosure_Total_Game
-- name    : BBDisclosure_Total_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T01:23:36.100208+00:00
-- url     : https://prove2.me/theorems/077ac4b1-8c2d-4793-ba41-6d4f89b506a7
-- title:
--   §3.3, §4.3, pp. 8515–8519 — first-period share (6)/(15), two-period profits (8), symmetric subgame-perfect equilibrium and its outcomes
-- statement:
--   This file adds the first period to the second-period model `BBDisclosure.Total.Stage2` of Zhang and Li, *Retention or Acquisition? Behavior-Based Quality Disclosure*, §3.3 and §4.3.
--
--   **First period.** Each firm charges one price, $p_{a1},p_{b1}\ge0$. Customers are forward looking with rational expectations and discount factor $1$: the first-period share $x_1$ is the location of the marginal consumer, who anticipates the second-period equilibrium played at that share. Under BBD the defining condition is (15),
--   $$-x_1-p_{a1}+\max\{-(1-x_1)+E(\tilde q_{bn}-p^*_{bn}),\,-x_1+E(\tilde q_{ao}-p^*_{ao})\}=-(1-x_1)-p_{b1}+\max\{-x_1+E(\tilde q_{an}-p^*_{an}),\,-(1-x_1)+E(\tilde q_{bo}-p^*_{bo})\},$$
--   where each expectation is over $(q_a,q_b)\sim U[0,1]^2$ of the belief the relevant segment will hold minus the price it will pay, under the second-period profile selected at $x_1$. Under uniform disclosure the condition is (6), the same with the uniform beliefs $\tilde q_a,\tilde q_b$. A share is **consistent** with prices $(p_{a1},p_{b1})$ if $x_1\in[0,1]$ and: for $0<x_1<1$ the equation holds at $x_1$; $x_1=0$ is consistent when, for some $\delta>0$, at every share $x\in(0,\delta)$ the left side is at most the right side (the marginal consumer of any small positive share weakly prefers B); $x_1=1$ is consistent when, for some $\delta>0$, at every $x\in(1-\delta,1)$ the right side is at most the left side.
--
--   **Two-period profits** (8):
--   $$\Pi_a(p_{a1},p_{b1})=p_{a1}x_1+E(\pi_{a2}),\qquad \Pi_b(p_{a1},p_{b1})=p_{b1}(1-x_1)+E(\pi_{b2}),$$
--   with $x_1$ the selected share at $(p_{a1},p_{b1})$ and $E(\pi_{i2})$ the ex ante second-period profit of the second-period profile selected at $x_1$.
--
--   **Symmetric subgame-perfect equilibrium.** A candidate consists of a common first-period price $p^*$, a second-period profile for every share, and a share for every price pair. It is a symmetric subgame-perfect equilibrium at cost $c$ when
--   1. $p^*\ge 0$;
--   2. at every share $x_1\in[0,1]$ the selected profile is a second-period equilibrium;
--   3. at every nonnegative price pair the selected share is consistent with it;
--   4. no price $p_{a1}\ge0$ gives A a higher two-period profit against $p_{b1}=p^*$;
--   5. no price $p_{b1}\ge0$ gives B a higher two-period profit against $p_{a1}=p^*$.
--
--   The equilibrium outcomes are the total profits $\Pi^*_a=\Pi_a(p^*,p^*)$, $\Pi^*_b=\Pi_b(p^*,p^*)$ and the first-period profits $p^*x_1^*$, $p^*(1-x_1^*)$.
--
--   These are the objects of Propositions 2 and 3 and of (7), (9), (16), (17) and Table 1.
--
--   **Formalization Note.** The base value $v$ appears twice on each side of (6)/(15) and is dropped. First-period prices are nonnegative and deviations range over *all* nonnegative prices, as the paper's verification of deviations to regions 2 and 3 (Online Appendix) implies; the second-period profile is required to be an equilibrium at every share, including shares reached only after a deviation. The maximum in (6)/(15) is a maximum of two expectations, as printed. The share and the second-period profile are selections that are part of the equilibrium object. The corner conditions are read through interior shares: at $x_1\in\{0,1\}$ one turf is empty, every price pair is a Nash equilibrium of its (zero-revenue) game, and evaluating (6)/(15) there would let an arbitrary selection of those prices make a corner share consistent with any prices.
-- source:
--   Zhang and Li, Retention or Acquisition? Behavior-Based Quality Disclosure, Management Sci. 71(10) (2025) 8510–8525, DOI 10.1287/mnsc.2022.01081, pp. 8515–8519, §2 (timing, rational expectations), §3.3 (6), (8), §4.3 (15), endnote 5 (p. 8523)

import Mathlib
import Definitions.Def_BBDisclosure_Total_Stage2

namespace BBDisclosure.Total

/-!
# Zhang and Li, *Retention or Acquisition? Behavior-Based Quality Disclosure*, §3.3 and §4.3
(pp. 8516–8519): the first period and the two-period game

Each firm charges one first-period price (`pa1`, `pb1`, nonnegative). Customers are forward
looking: the first-period share `x1` is the location of the marginal consumer of (6) (uniform) or
(15) (BBD), who anticipates the second-period equilibrium played at that share. Firms maximize the
two-period profits (8). Discount factors are `1`; `v` cancels from both sides of (6)/(15) and is
omitted.
-/

/-! ## The expected surplus terms of (6) and (15) -/

/-- `E(q̃_bn − p*_bn)` under the BBD profile `e`. -/
noncomputable def EsurBn (e : BBDisclosure.Stage2.ProfileBBD) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qbn qb - (e.σA (BBDisclosure.Stage2.bel e.qao qa) (BBDisclosure.Stage2.bel e.qbn qb)).2)

/-- `E(q̃_ao − p*_ao)` under the BBD profile `e`. -/
noncomputable def EsurAo (e : BBDisclosure.Stage2.ProfileBBD) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qao qa - (e.σA (BBDisclosure.Stage2.bel e.qao qa) (BBDisclosure.Stage2.bel e.qbn qb)).1)

/-- `E(q̃_an − p*_an)` under the BBD profile `e`. -/
noncomputable def EsurAn (e : BBDisclosure.Stage2.ProfileBBD) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qan qa - (e.σB (BBDisclosure.Stage2.bel e.qan qa) (BBDisclosure.Stage2.bel e.qbo qb)).1)

/-- `E(q̃_bo − p*_bo)` under the BBD profile `e`. -/
noncomputable def EsurBo (e : BBDisclosure.Stage2.ProfileBBD) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qbo qb - (e.σB (BBDisclosure.Stage2.bel e.qan qa) (BBDisclosure.Stage2.bel e.qbo qb)).2)

/-- `E(q̃_b − p*_bn)` under the uniform profile `e`. -/
noncomputable def EsurBnU (e : BBDisclosure.Stage2.ProfileU) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qb qb - (e.σA (BBDisclosure.Stage2.bel e.qa qa) (BBDisclosure.Stage2.bel e.qb qb)).2)

/-- `E(q̃_a − p*_ao)` under the uniform profile `e`. -/
noncomputable def EsurAoU (e : BBDisclosure.Stage2.ProfileU) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qa qa - (e.σA (BBDisclosure.Stage2.bel e.qa qa) (BBDisclosure.Stage2.bel e.qb qb)).1)

/-- `E(q̃_a − p*_an)` under the uniform profile `e`. -/
noncomputable def EsurAnU (e : BBDisclosure.Stage2.ProfileU) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qa qa - (e.σB (BBDisclosure.Stage2.bel e.qa qa) (BBDisclosure.Stage2.bel e.qb qb)).1)

/-- `E(q̃_b − p*_bo)` under the uniform profile `e`. -/
noncomputable def EsurBoU (e : BBDisclosure.Stage2.ProfileU) : ℝ :=
  ∫ qa in (0 : ℝ)..1, ∫ qb in (0 : ℝ)..1,
    (BBDisclosure.Stage2.bel e.qb qb - (e.σB (BBDisclosure.Stage2.bel e.qa qa) (BBDisclosure.Stage2.bel e.qb qb)).2)

/-! ## The first-period share -/

/-- Left side of (15) with `v` dropped, for the marginal consumer at `x` under the second-period
profile `e`: `−x − pa1 + max{−(1 − x) + E(q̃_bn − p*_bn), −x + E(q̃_ao − p*_ao)}`. -/
noncomputable def lhs15 (e : BBDisclosure.Stage2.ProfileBBD) (pa1 x : ℝ) : ℝ :=
  -x - pa1 + max (-(1 - x) + EsurBn e) (-x + EsurAo e)

/-- Right side of (15) with `v` dropped:
`−(1 − x) − pb1 + max{−x + E(q̃_an − p*_an), −(1 − x) + E(q̃_bo − p*_bo)}`. -/
noncomputable def rhs15 (e : BBDisclosure.Stage2.ProfileBBD) (pb1 x : ℝ) : ℝ :=
  -(1 - x) - pb1 + max (-x + EsurAn e) (-(1 - x) + EsurBo e)

/-- Left side of (6) with `v` dropped (uniform disclosure). -/
noncomputable def lhs6 (e : BBDisclosure.Stage2.ProfileU) (pa1 x : ℝ) : ℝ :=
  -x - pa1 + max (-(1 - x) + EsurBnU e) (-x + EsurAoU e)

/-- Right side of (6) with `v` dropped (uniform disclosure). -/
noncomputable def rhs6 (e : BBDisclosure.Stage2.ProfileU) (pb1 x : ℝ) : ℝ :=
  -(1 - x) - pb1 + max (-x + EsurAnU e) (-(1 - x) + EsurBoU e)

/-- `x1` is a first-period share consistent with (15) at first-period prices `(pa1, pb1)`, when the
second period at share `x` is played according to `stage2 x`. An interior share makes the marginal
consumer indifferent (`lhs15 = rhs15` at `x1`). The corner `x1 = 0` (resp. `1`) requires every
marginal consumer at a share `x` close to `0` from above (resp. to `1` from below) to weakly prefer
B (resp. A). The corners are read through interior shares because at `x1 ∈ {0, 1}` one turf is
empty and its second-period prices are not pinned down by the turf game. -/
def IsShareBBD (stage2 : ℝ → BBDisclosure.Stage2.ProfileBBD) (pa1 pb1 x1 : ℝ) : Prop :=
  x1 ∈ Set.Icc (0 : ℝ) 1 ∧
  (0 < x1 → x1 < 1 → lhs15 (stage2 x1) pa1 x1 = rhs15 (stage2 x1) pb1 x1) ∧
  (x1 = 0 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) δ, lhs15 (stage2 x) pa1 x ≤ rhs15 (stage2 x) pb1 x) ∧
  (x1 = 1 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Set.Ioo (1 - δ) 1, rhs15 (stage2 x) pb1 x ≤ lhs15 (stage2 x) pa1 x)

/-- `x1` is a first-period share consistent with (6) at prices `(pa1, pb1)`, when the second
period at share `x` is played according to `stage2 x` (uniform disclosure); same reading as
`IsShareBBD`. -/
def IsShareU (stage2 : ℝ → BBDisclosure.Stage2.ProfileU) (pa1 pb1 x1 : ℝ) : Prop :=
  x1 ∈ Set.Icc (0 : ℝ) 1 ∧
  (0 < x1 → x1 < 1 → lhs6 (stage2 x1) pa1 x1 = rhs6 (stage2 x1) pb1 x1) ∧
  (x1 = 0 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Set.Ioo (0 : ℝ) δ, lhs6 (stage2 x) pa1 x ≤ rhs6 (stage2 x) pb1 x) ∧
  (x1 = 1 → ∃ δ : ℝ, 0 < δ ∧
    ∀ x ∈ Set.Ioo (1 - δ) 1, rhs6 (stage2 x) pb1 x ≤ lhs6 (stage2 x) pa1 x)

/-! ## Symmetric subgame-perfect equilibria of the two-period game -/

/-- A candidate symmetric equilibrium under BBD: the common first-period price `pStar`, a
second-period profile for every share (`stage2`), and a first-period share for every price pair
(`share`). -/
structure SPE_BBD where
  pStar : ℝ
  stage2 : ℝ → BBDisclosure.Stage2.ProfileBBD
  share : ℝ → ℝ → ℝ

/-- A candidate symmetric equilibrium under uniform disclosure. -/
structure SPE_U where
  pStar : ℝ
  stage2 : ℝ → BBDisclosure.Stage2.ProfileU
  share : ℝ → ℝ → ℝ

/-- Firm A's two-period profit (8) under BBD at first-period prices `(pa1, pb1)`:
`Π_a = pa1·x1 + E(π_a2)`. -/
noncomputable def PiA_BBD (c : ℝ) (s : SPE_BBD) (pa1 pb1 : ℝ) : ℝ :=
  pa1 * s.share pa1 pb1 + BBDisclosure.Stage2.exAnteA_BBD c (s.share pa1 pb1) (s.stage2 (s.share pa1 pb1))

/-- Firm B's two-period profit (8) under BBD: `Π_b = pb1·(1 − x1) + E(π_b2)`. -/
noncomputable def PiB_BBD (c : ℝ) (s : SPE_BBD) (pa1 pb1 : ℝ) : ℝ :=
  pb1 * (1 - s.share pa1 pb1) + BBDisclosure.Stage2.exAnteB_BBD c (s.share pa1 pb1) (s.stage2 (s.share pa1 pb1))

/-- Firm A's two-period profit (8) under uniform disclosure. -/
noncomputable def PiA_U (c : ℝ) (s : SPE_U) (pa1 pb1 : ℝ) : ℝ :=
  pa1 * s.share pa1 pb1 + BBDisclosure.Stage2.exAnteA_U c (s.share pa1 pb1) (s.stage2 (s.share pa1 pb1))

/-- Firm B's two-period profit (8) under uniform disclosure. -/
noncomputable def PiB_U (c : ℝ) (s : SPE_U) (pa1 pb1 : ℝ) : ℝ :=
  pb1 * (1 - s.share pa1 pb1) + BBDisclosure.Stage2.exAnteB_U c (s.share pa1 pb1) (s.stage2 (s.share pa1 pb1))

/-- `s` is a symmetric subgame-perfect equilibrium of the two-period BBD game at cost `c`:
1. the common first-period price is nonnegative;
2. at every share `x1 ∈ [0,1]` the selected second-period profile is a second-period equilibrium;
3. at every nonnegative price pair the selected share satisfies (15);
4. no first-period price `pa1 ≥ 0` gives A a higher two-period profit against `pStar`;
5. no first-period price `pb1 ≥ 0` gives B a higher two-period profit against `pStar`. -/
def IsSymSPE_BBD (c : ℝ) (s : SPE_BBD) : Prop :=
  0 ≤ s.pStar ∧
  (∀ x1 ∈ Set.Icc (0 : ℝ) 1, BBDisclosure.Stage2.IsStage2EqBBD c x1 (s.stage2 x1)) ∧
  (∀ pa1 pb1 : ℝ, 0 ≤ pa1 → 0 ≤ pb1 → IsShareBBD s.stage2 pa1 pb1 (s.share pa1 pb1)) ∧
  (∀ pa1 : ℝ, 0 ≤ pa1 → PiA_BBD c s pa1 s.pStar ≤ PiA_BBD c s s.pStar s.pStar) ∧
  (∀ pb1 : ℝ, 0 ≤ pb1 → PiB_BBD c s s.pStar pb1 ≤ PiB_BBD c s s.pStar s.pStar)

/-- `s` is a symmetric subgame-perfect equilibrium of the two-period uniform-disclosure game at
cost `c` (same five conditions, with (6) for the share). -/
def IsSymSPE_U (c : ℝ) (s : SPE_U) : Prop :=
  0 ≤ s.pStar ∧
  (∀ x1 ∈ Set.Icc (0 : ℝ) 1, BBDisclosure.Stage2.IsStage2EqU c x1 (s.stage2 x1)) ∧
  (∀ pa1 pb1 : ℝ, 0 ≤ pa1 → 0 ≤ pb1 → IsShareU s.stage2 pa1 pb1 (s.share pa1 pb1)) ∧
  (∀ pa1 : ℝ, 0 ≤ pa1 → PiA_U c s pa1 s.pStar ≤ PiA_U c s s.pStar s.pStar) ∧
  (∀ pb1 : ℝ, 0 ≤ pb1 → PiB_U c s s.pStar pb1 ≤ PiB_U c s s.pStar s.pStar)

/-! ## Equilibrium outcomes -/

/-- Firm A's equilibrium total profit `Π*_a` under BBD. -/
noncomputable def totalA_BBD (c : ℝ) (s : SPE_BBD) : ℝ := PiA_BBD c s s.pStar s.pStar

/-- Firm B's equilibrium total profit `Π*_b` under BBD. -/
noncomputable def totalB_BBD (c : ℝ) (s : SPE_BBD) : ℝ := PiB_BBD c s s.pStar s.pStar

/-- Firm A's equilibrium total profit `Π*_a` under uniform disclosure. -/
noncomputable def totalA_U (c : ℝ) (s : SPE_U) : ℝ := PiA_U c s s.pStar s.pStar

/-- Firm B's equilibrium total profit `Π*_b` under uniform disclosure. -/
noncomputable def totalB_U (c : ℝ) (s : SPE_U) : ℝ := PiB_U c s s.pStar s.pStar

/-- Firm A's equilibrium first-period profit `p*_a1 x*_1` under BBD. -/
noncomputable def firstProfitA_BBD (s : SPE_BBD) : ℝ := s.pStar * s.share s.pStar s.pStar

/-- Firm B's equilibrium first-period profit `p*_b1 (1 − x*_1)` under BBD. -/
noncomputable def firstProfitB_BBD (s : SPE_BBD) : ℝ := s.pStar * (1 - s.share s.pStar s.pStar)

/-- Firm A's equilibrium first-period profit under uniform disclosure. -/
noncomputable def firstProfitA_U (s : SPE_U) : ℝ := s.pStar * s.share s.pStar s.pStar

/-- Firm B's equilibrium first-period profit under uniform disclosure. -/
noncomputable def firstProfitB_U (s : SPE_U) : ℝ := s.pStar * (1 - s.share s.pStar s.pStar)

end BBDisclosure.Total


