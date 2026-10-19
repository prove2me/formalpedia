-- Prove2me | Definitions.Def_OppReturns_Menu_Model
-- name    : OppReturns_Menu_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:01.953465+00:00
-- url     : https://prove2.me/theorems/aa667a52-8f32-41c7-8bba-ce3f975d63c5
-- title:
--   §3–§6, pp. 8–16 — honest returners and renters, N, M^u, M^t, M^m, programs (3), (9), (11) and their optimal profits
-- statement:
--   The model of Altug, Aydinliyim and Jain (§3, pp. 8–10) and the retailer's three programs (§4–§6, pp. 10–16).
--
--   **Data.** A retailer buys at unit cost $c$, sells at price $p$ and refunds $r$ per returned unit; leftover units are salvaged at $s$, with $s < c$. Aggregate demand $D$ has law $F$. A fraction $X \in (0,1)$ of customers are *renters*, the rest are *honest returners*.
--
--   1. An honest returner has long-term valuation $u_L \sim G_L$, supported on $[0, V_L]$. He buys if $\mathbb E\max\{u_L, r\} - p \ge 0$, learns $u_L$, keeps the product iff $u_L - r \ge 0$, and returns it otherwise. The fraction of honest buyers who return is $G_L(r) = P(u_L < r)$.
--   2. A renter has short-term valuation $u_S \sim G_S$, supported on $[0, V_S]$. He rents (buys and returns) iff $u_S - (p - r) \ge 0$; the **rental fee** is $p - r$. The fraction of renters who do not transact is $G_S(p - r) = P(u_S < p - r)$.
--
--   **Derived quantities.** For a refund $r$, $\mathbb E\max\{u_L, r\}$ is the honest returner's expected value of buying. The fraction of transacting customers is
--   $$N(p, r) = 1 - X G_S(p - r).$$
--   The marginal net revenues of the three proposals are
--   $$M^u(p,r) = (p-r)\bigl(1 - XG_S(p-r)\bigr) + (r-s)(1-X)\bigl(1-G_L(r)\bigr),$$
--   $$M^t(p, r_R, r_H) = X(p - r_R)\bigl(1 - G_S(p - r_R)\bigr) + (1-X)\bigl((p-s) - (r_H - s)G_L(r_H)\bigr),$$
--   $$M^m(p_R, r_R, p_H, r_H) = X(p_R - r_R)\bigl(1 - G_S(p_R - r_R)\bigr) + (1-X)\bigl((p_H-s) - (r_H - s)G_L(r_H)\bigr),$$
--   and a decision with margin $M$, transacting fraction $N$ and stock $Q$ earns, as in (1),
--   $$M\, \mathbb E\min\Bigl\{\frac{Q}{N}, D\Bigr\} - (c - s)Q.$$
--
--   **Programs.**
--
--   1. *Uniform refunds* (3): choose $Q \ge 0$, $p$ and $r$ with $0 \le r \le p$ and $\mathbb E\max\{u_L, r\} - p \ge 0$, profit with $M^u(p,r)$ and $N(p,r)$.
--   2. *Targeted refunds* (9): choose $Q \ge 0$, $p$, $r_R \ge 0$, $r_H \ge 0$ with $0 \le p - r_R \le V_S$ and $\mathbb E\max\{u_L, r_H\} - p = 0$, profit with $M^t(p, r_R, r_H)$ and $N(p, r_R)$.
--   3. *Menu of refunds* (11): choose $Q \ge 0$ and pairs $(p_H, r_H)$, $(p_R, r_R)$ with $0 \le r_H \le p_H$, $0 \le r_R \le p_R$,
--   $$\mathbb E\max\{u_L, r_H\} - p_H \ge \max\{\mathbb E\max\{u_L, r_R\} - p_R,\ 0\}, \qquad p_R - r_R \le \min\{p_H - r_H,\ V_S\},$$
--   profit with $M^m(p_R, r_R, p_H, r_H)$ and $N(p_R, r_R)$.
--
--   The optimal profits $\Pi^u, \Pi^t, \Pi^m$ are the suprema of the profit over the feasible decisions of each program, and an optimal uniform (targeted) decision is a feasible one whose profit is at least that of every feasible decision. The paper's main body (p. 11) treats the case where the honest returners' constraint of (3) *binds*: every optimal uniform decision has $p = \mathbb E\max\{u_L, r\}$.
--
--   **Standing assumptions.** $0 < X < 1$, $0 < s < c$, $V_L, V_S > 0$; $G_L$ and $G_S$ are probability laws with support exactly $[0, V_L]$ and $[0, V_S]$, each with a density and the increasing generalized failure rate (IGFR) property (p. 10); demand is a probability law on $(0, \infty)$ with finite mean; and $c < \mathbb E\max\{u_L, s\}$.
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note**
--   1. Tie rules are the paper's (keep iff $u_L \ge r$, rent iff $u_S \ge p - r$), so $G_L, G_S$ are read with strict inequalities; since both laws have densities, the choice is immaterial.
--   2. Program (3) keeps its participation constraint as an inequality; the main body's restriction to the case where it binds (p. 11, "we will limit our presentation within the main body of this paper to the case where the said constraint binds") is the predicate `UniformBinds` (every optimal uniform decision has $p = \mathbb E\max\{u_L, r\}$), carried as a hypothesis by the statements about $r^u$ whose content depends on it (Proposition 4's last sentence, Propositions 5 and 6). The cap $p - r \le V_S$ is dropped: Proposition 1's (5d) sets $r^u = r^b = s$ with rental fee $p^b - s$, which can exceed $V_S$; above $V_S$ the cap is immaterial because no renter transacts ($G_S = 1$). Programs (9) and (11) keep the cap as printed.
--   3. Refunds are nonnegative in all three programs ((5d) writes $\max\{\hat r, 0\}$; Figure 1(b) has a region "$r^u = 0$"), and $r \le p$ for both menu pairs (p. 8, "offering refund $r$ ($r \le p$)").
--   4. Added to the page: $0 < s$ (at $s = 0$ the constraint $r \ge 0$ breaks Proposition 6), $c < \mathbb E\max\{u_L, s\}$ (the page's "$p > c$" at the benchmark price; without it every proposal may earn $0$), and demand that is positive almost surely with finite mean (so that $\mathbb E\min\{Q/N, D\}$ is finite and every program earns a positive profit at a small stock). "Stochastically increasing" (p. 10) has no meaning for one law and is not encoded. Proposition 1's hypothesis "$xG_S'(x)$ is decreasing" is not encoded: no law with a density on $[0, V_S]$ satisfies it.
--   5. IGFR is `LariviereIGFR.Char.IsIGFR` for a regular density (`IsRegDensity`), from the published `LariviereIGFR_Char_Setting`; $\mathbb E\min\{Q, D\}$ is the published `SupplyChainTheory.expSales`. The division $Q/N$ is safe because $N \ge 1 - X > 0$. The optimal profits are `sSup`s of real sets; their boundedness above is a milestone, not an assumption. All quantities are real numbers.
-- source:
--   Altug, Aydinliyim & Jain, Managing Opportunistic Consumer Returns in Retail Operations, SSRN working paper 3283334 (revision of June 26, 2020), pp. 8–16, §3–§6, (1), (3), (9), (11), M^u p. 10, M^t p. 14, M^m p. 16

import Mathlib
import Definitions.Def_SupplyChainTheory_contracts
import Definitions.Def_LariviereIGFR_Char_Setting

namespace OppReturns.Menu

open MeasureTheory

/-- The data of the model of §3 (Altug–Aydinliyim–Jain, pp. 8–10): fraction `X` of renters, unit
cost `c`, salvage value `s`, the upper ends `VL`, `VS` of the valuation supports, the law `νL` of an
honest returner's long-term valuation `u_L`, the law `νS` of a renter's short-term valuation `u_S`,
and the law `D` of aggregate demand (cdf `F`). -/
structure Params where
  X : ℝ
  c : ℝ
  s : ℝ
  VL : ℝ
  VS : ℝ
  νL : Measure ℝ
  νS : Measure ℝ
  D : Measure ℝ

/-- `G_L(r) = P(u_L < r)`: the fraction of honest returners who return at refund `r`
(an honest returner keeps iff `u_L − r ≥ 0`). -/
noncomputable def GLf (P : Params) (r : ℝ) : ℝ := (P.νL (Set.Iio r)).toReal

/-- `G_S(f) = P(u_S < f)`: the fraction of renters who do not rent at rental fee `f = p − r`
(a renter rents iff `u_S − (p − r) ≥ 0`). -/
noncomputable def GSf (P : Params) (f : ℝ) : ℝ := (P.νS (Set.Iio f)).toReal

/-- `E max{u_L, r}`: an honest returner's expected value of buying at refund `r`. -/
noncomputable def Emax (P : Params) (r : ℝ) : ℝ := ∫ u, max u r ∂P.νL

/-- `N(p, r) = 1 − X G_S(p − r)`, the fraction of transacting customers, as a function of the
rental fee `f = p − r`. -/
noncomputable def Nf (P : Params) (f : ℝ) : ℝ := 1 - P.X * GSf P f

/-- The margin per honest customer at price `p` and refund `r`: `(p − s) − (r − s) G_L(r)`. -/
noncomputable def honestMargin (P : Params) (p r : ℝ) : ℝ := (p - P.s) - (r - P.s) * GLf P r

/-- `M^u(p, r) = (p − r)(1 − X G_S(p − r)) + (r − s)(1 − X)(1 − G_L(r))` (p. 10). -/
noncomputable def Mu (P : Params) (p r : ℝ) : ℝ :=
  (p - r) * (1 - P.X * GSf P (p - r)) + (r - P.s) * (1 - P.X) * (1 - GLf P r)

/-- `M^t(p, r_R, r_H) = X(p − r_R)(1 − G_S(p − r_R)) + (1 − X)((p − s) − (r_H − s)G_L(r_H))`
(p. 14). -/
noncomputable def Mt (P : Params) (p rR rH : ℝ) : ℝ :=
  P.X * (p - rR) * (1 - GSf P (p - rR)) + (1 - P.X) * honestMargin P p rH

/-- `M^m = X(p_R − r_R)(1 − G_S(p_R − r_R)) + (1 − X)((p_H − s) − (r_H − s)G_L(r_H))` (p. 16). -/
noncomputable def Mm (P : Params) (pR rR pH rH : ℝ) : ℝ :=
  P.X * (pR - rR) * (1 - GSf P (pR - rR)) + (1 - P.X) * honestMargin P pH rH

/-- Expected profit `M · E min{Q/N, D} − (c − s) Q`, as in (1), (3), (9), (11). -/
noncomputable def profit (P : Params) (M N Q : ℝ) : ℝ :=
  M * SupplyChainTheory.expSales P.D (Q / N) - (P.c - P.s) * Q

/-- Feasible uniform-refunds decisions: program (3), `E max{u_L, r} − p ≥ 0`, with `Q ≥ 0`,
`0 ≤ r ≤ p`. The cap `p − r ≤ V_S` of (3) is not imposed (see the Formalization Note). -/
def FeasU (P : Params) (Q p r : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ r ∧ r ≤ p ∧ p ≤ Emax P r

/-- The uniform-refunds profit, (3). -/
noncomputable def profitU (P : Params) (Q p r : ℝ) : ℝ :=
  profit P (Mu P p r) (Nf P (p - r)) Q

/-- Feasible targeted-refunds decisions, program (9): `0 ≤ p − r_R ≤ V_S`,
`E max{u_L, r_H} − p = 0`, with `Q ≥ 0` and nonnegative refunds. -/
def FeasT (P : Params) (Q p rR rH : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ rR ∧ 0 ≤ rH ∧ 0 ≤ p - rR ∧ p - rR ≤ P.VS ∧ Emax P rH - p = 0

/-- The targeted-refunds profit, (9). -/
noncomputable def profitT (P : Params) (Q p rR rH : ℝ) : ℝ :=
  profit P (Mt P p rR rH) (Nf P (p - rR)) Q

/-- Feasible menu-of-refunds decisions, program (11):
`E max{u_L, r_H} − p_H ≥ max{E max{u_L, r_R} − p_R, 0}` and `p_R − r_R ≤ min{p_H − r_H, V_S}`,
with `Q ≥ 0`, nonnegative refunds, and `r_H ≤ p_H`, `r_R ≤ p_R`. -/
def FeasM (P : Params) (Q pH rH pR rR : ℝ) : Prop :=
  0 ≤ Q ∧ 0 ≤ rH ∧ 0 ≤ rR ∧ rH ≤ pH ∧ rR ≤ pR ∧
    max (Emax P rR - pR) 0 ≤ Emax P rH - pH ∧ pR - rR ≤ min (pH - rH) P.VS

/-- The menu-of-refunds profit, (11). -/
noncomputable def profitM (P : Params) (Q pH rH pR rR : ℝ) : ℝ :=
  profit P (Mm P pR rR pH rH) (Nf P (pR - rR)) Q

/-- `Π^u`: the optimal uniform-refunds profit (supremum over feasible decisions). -/
noncomputable def PiU (P : Params) : ℝ :=
  sSup {π | ∃ Q p r, FeasU P Q p r ∧ π = profitU P Q p r}

/-- `Π^t`: the optimal targeted-refunds profit. -/
noncomputable def PiT (P : Params) : ℝ :=
  sSup {π | ∃ Q p rR rH, FeasT P Q p rR rH ∧ π = profitT P Q p rR rH}

/-- `Π^m`: the optimal menu-of-refunds profit. -/
noncomputable def PiM (P : Params) : ℝ :=
  sSup {π | ∃ Q pH rH pR rR, FeasM P Q pH rH pR rR ∧ π = profitM P Q pH rH pR rR}

/-- `(Q, p, r)` is an optimal uniform-refunds decision `(Q^u, p^u, r^u)`. -/
def IsOptU (P : Params) (Q p r : ℝ) : Prop :=
  FeasU P Q p r ∧ ∀ Q' p' r', FeasU P Q' p' r' → profitU P Q' p' r' ≤ profitU P Q p r

/-- The case the paper's main body treats (p. 11): the honest returners' participation
constraint `E max{u_L, r} − p ≥ 0` of (3) binds at every optimal uniform-refunds decision. -/
def UniformBinds (P : Params) : Prop :=
  ∀ Q p r, IsOptU P Q p r → p = Emax P r

/-- `(Q, p, r_R, r_H)` is an optimal targeted-refunds decision `(Q^t, p^t, r^t_R, r^t_H)`. -/
def IsOptT (P : Params) (Q p rR rH : ℝ) : Prop :=
  FeasT P Q p rR rH ∧
    ∀ Q' p' rR' rH', FeasT P Q' p' rR' rH' → profitT P Q' p' rR' rH' ≤ profitT P Q p rR rH

/-- `(Q, p_H, r_H, p_R, r_R)` is an optimal menu-of-refunds decision. -/
def IsOptM (P : Params) (Q pH rH pR rR : ℝ) : Prop :=
  FeasM P Q pH rH pR rR ∧
    ∀ Q' pH' rH' pR' rR', FeasM P Q' pH' rH' pR' rR' →
      profitM P Q' pH' rH' pR' rR' ≤ profitM P Q pH rH pR rR

/-- `ν` is concentrated on `[0, V]` and charges every open subinterval: its support is `[0, V]`. -/
def FullSupport (ν : Measure ℝ) (V : ℝ) : Prop :=
  ν (Set.Icc 0 V)ᶜ = 0 ∧ ∀ a b, 0 ≤ a → a < b → b ≤ V → 0 < ν (Set.Ioo a b)

/-- `ν` has a (regular) density and the increasing generalized failure rate property (p. 10),
in the sense of `LariviereIGFR.Char`. -/
def IGFR (ν : Measure ℝ) : Prop :=
  ∃ ψ : ℝ → ℝ, LariviereIGFR.Char.IsRegDensity ν ψ ∧ LariviereIGFR.Char.IsIGFR ν ψ

/-- The standing assumptions of §3 (pp. 8–10) and the disclosed regularity additions. -/
def Standing (P : Params) : Prop :=
  0 < P.X ∧ P.X < 1 ∧ 0 < P.s ∧ P.s < P.c ∧ 0 < P.VL ∧ 0 < P.VS ∧
    IsProbabilityMeasure P.νL ∧ IsProbabilityMeasure P.νS ∧ IsProbabilityMeasure P.D ∧
    FullSupport P.νL P.VL ∧ FullSupport P.νS P.VS ∧
    IGFR P.νL ∧ IGFR P.νS ∧
    P.D (Set.Iic 0) = 0 ∧ Integrable (fun x => x) P.D ∧
    P.c < Emax P P.s

end OppReturns.Menu


