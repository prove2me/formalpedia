-- Prove2me | Definitions.Def_QualityEncroach_Uniform_Game
-- name    : QualityEncroach_Uniform_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:29.449024+00:00
-- url     : https://prove2.me/theorems/98a3f32b-74f3-4f72-9f6f-3323e8df8c66
-- title:
--   §3.1–§4.1, pp. 7–10 — the benchmark game and the encroachment game with uniform quality, their subgame-perfect equilibria, and the closed forms (1)–(5) and Π_M(u)
-- statement:
--   This file sets up the basic model of Ha, Long & Nasiry, *Quality in Supply Chain Encroachment*, §3.1–§4.1.
--
--   **Market.** Consumers have a quality sensitivity $\theta$ uniformly distributed on $[0,1]$; a consumer buying a product of quality $u>0$ at price $p$ obtains surplus $\theta u - p$. When a single product of quality $u$ is sold in total quantity $q$, the market-clearing price is
--   $$p = u(1-q).$$
--   The manufacturer's unit production cost for quality $u$ is $ku^2$ with $k>0$. She pays a selling cost $c\ge 0$ per unit sold through her own direct channel; the retailer's selling cost is $0$.
--
--   **Benchmark game (no direct channel, §3.2).** The manufacturer chooses a wholesale price $w$ and a quality $u>0$; after observing them, the retailer orders $q_R\ge 0$. Profits are
--   $$\Pi^N_R = (u(1-q_R)-w)\,q_R,\qquad \Pi^N_M = (w-ku^2)\,q_R .$$
--   A strategy profile consists of the manufacturer's choice $(w,u)$ and the retailer's ordering rule $(w,u)\mapsto q_R$. It is a **subgame perfect equilibrium** if (i) at every $(w,u)$ with $u>0$ the rule picks an order $q_R\ge 0$ that no other order $q_R'\ge 0$ beats for the retailer, and (ii) $u>0$ and no other $(w',u')$ with $u'>0$, followed by the retailer's rule, gives the manufacturer a strictly larger profit.
--
--   **Encroachment with uniform quality (§4.1).** The manufacturer chooses $(w,u)$ with $u>0$; the retailer, having observed them, orders $q_R\ge 0$; then the manufacturer, having observed $q_R$, sells $q_M\ge 0$ directly. Both channels face the market-clearing price $u(1-q_R-q_M)$, so
--   $$\Pi_R = (u(1-q_R-q_M)-w)\,q_R,\qquad \Pi_M = (w-ku^2)\,q_R + (u-uq_M-uq_R-c-ku^2)\,q_M .$$
--   A strategy profile has the manufacturer's stage-1 choice $(w,u)$, the retailer's rule $(w,u)\mapsto q_R$ and the manufacturer's stage-3 rule $(w,u,q_R)\mapsto q_M$. It is a **subgame perfect equilibrium** when at every decision node, on or off the equilibrium path, the mover's rule picks a feasible action that no feasible alternative (followed by play according to the profile) beats strictly. The manufacturer **encroaches** when $q_M>0$ on the equilibrium path. A number $\tilde c>0$ is an **encroachment threshold** for $k$ if, in every equilibrium at every $c\ge0$, the manufacturer encroaches when $c<\tilde c$ and does not when $c>\tilde c$.
--
--   **Closed forms.** The file also records the formulas the paper derives by backward induction:
--   1. $q^N_R(w,u)=\tfrac12-\tfrac{w}{2u}$, $w^N(u)=\tfrac{ku^2}{2}+\tfrac u2$, $\Pi^N_M(u)=\tfrac{u(1-ku)^2}{8}$, $\Pi^N_R(u)=\tfrac{u(1-ku)^2}{16}$ (p. 9);
--   2. $q^U_M(q_R,w,u)=\big(\tfrac12-\tfrac{q_R}{2}-\tfrac{c}{2u}-\tfrac{ku}{2}\big)^+$ (p. 10);
--   3. $q^U_R(w,u)=\tfrac12-\tfrac wu+\tfrac{ku}{2}+\tfrac{c}{2u}$ and $q^U_M(w,u)=\tfrac14+\tfrac{w}{2u}-\tfrac{3ku}{4}-\tfrac{3c}{4u}$, equation (3);
--   4. $w^U(u)=\tfrac{ku^2}{2}+\tfrac u2-\tfrac c6$, equation (4);
--   5. $\Pi^U_M(u)=\tfrac{k^2u^3}{4}+\tfrac{kcu}{2}+\tfrac{7c^2}{12u}-\tfrac{ku^2}{2}+\tfrac u4-\tfrac c2$ and $\Pi^U_R(u)=\tfrac{2c^2}{9u}$, equation (5);
--   6. $\Pi^{UZ}_M(u)=\big(\tfrac12ku^2-\tfrac12u+\tfrac32c\big)\big(1-\tfrac cu-ku\big)$ and the three-case function
--   $$\Pi_M(u)=\begin{cases}\Pi^U_M(u) & c\le \tfrac{3u(1-ku)}{5},\\ \Pi^{UZ}_M(u) & \tfrac{3u(1-ku)}{5}\le c\le \tfrac{5u(1-ku)}{6},\\ \Pi^N_M(u) & c\ge\tfrac{5u(1-ku)}{6}\end{cases}$$
--   of the proof of Proposition 1(i) (p. 27).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** The wholesale price $w$ ranges over all reals (the paper states no sign restriction); qualities are $u>0$ and quantities are $\ge 0$. The inverse demand $u(1-q_R-q_M)$ is used for all nonnegative quantities, as in the paper. Subgame perfection is written in one-shot-deviation form at every history; in this three-stage game with perfect information that is subgame perfection. The closed forms are plain real functions; a formula with $u$ in a denominator is meaningful only for $u>0$, which every theorem using it assumes. The page writes $q^U_M(q_R,w,u)$ with an argument $w$ on which it does not depend; the Lean function keeps that argument.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 7–10, §3.1 (consumers, costs, timeline), §3.2 (benchmark, (1)–(2)), §4.1 ((3)–(5)), and p. 27, proof of Proposition 1(i) (Π_M(u))

import Mathlib

namespace QualityEncroach.Uniform

/-!
# Ha, Long & Nasiry, *Quality in Supply Chain Encroachment*, §3.1–§4.1 (pp. 7–10)

Consumers have types `θ ~ U[0,1]` and surplus `θu − p`, so one product of quality `u > 0`
sold in total quantity `q` clears at the price `u(1 − q)` (p. 7). The manufacturer's unit
cost of quality `u` is `k u²` with `k > 0`; she pays `c ≥ 0` per unit sold through her direct
channel; the retailer's selling cost is `0` (p. 8).

Two games are defined, both with perfect information and solved by backward induction
(pp. 8–10):

* the **benchmark** (no direct channel, §3.2): the manufacturer picks `(w, u)`, then the
  retailer orders `q_R`;
* **encroachment with uniform quality** (§4.1): the manufacturer picks `(w, u)`, the retailer
  orders `q_R`, then the manufacturer sells `q_M` directly; both firms face the
  market-clearing price `u(1 − q_R − q_M)`.

Action sets: `w ∈ ℝ` (no sign restriction is stated), `u > 0`, quantities `≥ 0`.
Subgame perfection is stated in one-shot-deviation form at every history, on or off the path.

The file also holds the closed forms the paper derives by backward induction (pp. 9–10, 27),
as plain functions of the parameters.
-/

/-! ## The benchmark game (no direct channel), §3.2 -/

/-- A terminal history of the benchmark game: wholesale price `w`, quality `u`, order `qR`. -/
structure BenchOutcome where
  w : ℝ
  u : ℝ
  qR : ℝ

/-- The retailer's benchmark profit `Π^N_R(q_R, w, u) = (u(1 − q_R) − w) q_R` (p. 9). -/
def benchRetailerPayoff (o : BenchOutcome) : ℝ :=
  (o.u * (1 - o.qR) - o.w) * o.qR

/-- The manufacturer's benchmark profit `(w − k u²) q_R` (p. 9). -/
def benchMfrPayoff (k : ℝ) (o : BenchOutcome) : ℝ :=
  (o.w - k * o.u ^ 2) * o.qR

/-- A pure strategy profile of the benchmark game: the manufacturer's choice `(w, u)` and the
retailer's ordering rule `order w u = q_R`, a function of the observed `(w, u)`. -/
structure BenchProfile where
  w : ℝ
  u : ℝ
  order : ℝ → ℝ → ℝ

/-- The outcome after the manufacturer chooses `(w, u)` and the retailer follows `τ.order`. -/
def BenchProfile.outcomeAt (τ : BenchProfile) (w u : ℝ) : BenchOutcome :=
  ⟨w, u, τ.order w u⟩

/-- The equilibrium path of the benchmark profile `τ`. -/
def BenchProfile.path (τ : BenchProfile) : BenchOutcome :=
  τ.outcomeAt τ.w τ.u

/-- `τ` is a subgame perfect equilibrium of the benchmark game with quality cost `k`:
* at every `(w, u)` with `u > 0` the retailer orders `τ.order w u ≥ 0`, and no order
  `q_R ≥ 0` gives him a strictly higher profit;
* the manufacturer chooses `τ.u > 0`, and no `(w, u)` with `u > 0`, followed by the retailer's
  rule, gives her a strictly higher profit. -/
def IsBenchSPE (k : ℝ) (τ : BenchProfile) : Prop :=
  (∀ w u : ℝ, 0 < u →
      0 ≤ τ.order w u ∧
      ∀ qR : ℝ, 0 ≤ qR → benchRetailerPayoff ⟨w, u, qR⟩ ≤ benchRetailerPayoff (τ.outcomeAt w u)) ∧
  0 < τ.u ∧
  ∀ w u : ℝ, 0 < u → benchMfrPayoff k (τ.outcomeAt w u) ≤ benchMfrPayoff k τ.path

/-! ## The encroachment game with uniform quality, §4.1 -/

/-- A terminal history of the encroachment game with uniform quality: wholesale price `w`,
quality `u`, the retailer's order `qR` and the manufacturer's direct quantity `qM`. -/
structure Outcome where
  w : ℝ
  u : ℝ
  qR : ℝ
  qM : ℝ

/-- The retailer's profit `(u(1 − q_R − q_M) − w) q_R` (p. 10). -/
def retailerPayoff (o : Outcome) : ℝ :=
  (o.u * (1 - o.qR - o.qM) - o.w) * o.qR

/-- The manufacturer's profit `(w − k u²) q_R + (u − u q_M − u q_R − c − k u²) q_M` (p. 9):
wholesale margin on the retailer's order plus the direct-channel margin at the common
market-clearing price `u(1 − q_M − q_R)`, net of the selling cost `c` and the production
cost `k u²`. -/
def mfrPayoff (k c : ℝ) (o : Outcome) : ℝ :=
  (o.w - k * o.u ^ 2) * o.qR + (o.u * (1 - o.qM - o.qR) - c - k * o.u ^ 2) * o.qM

/-- A pure strategy profile of the encroachment game:
* `w`, `u` — the manufacturer's stage-1 choice;
* `order w u = q_R` — the retailer's rule, a function of the observed `(w, u)`;
* `direct w u qR = q_M` — the manufacturer's stage-3 rule, a function of `(w, u, q_R)`. -/
structure Profile where
  w : ℝ
  u : ℝ
  order : ℝ → ℝ → ℝ
  direct : ℝ → ℝ → ℝ → ℝ

/-- The outcome after the history `(w, u, q_R)` when the manufacturer then follows
`σ.direct`. -/
def Profile.outcomeAtDirect (σ : Profile) (w u qR : ℝ) : Outcome :=
  ⟨w, u, qR, σ.direct w u qR⟩

/-- The outcome after the manufacturer chooses `(w, u)` and play then follows `σ`. -/
def Profile.outcomeAtOrder (σ : Profile) (w u : ℝ) : Outcome :=
  σ.outcomeAtDirect w u (σ.order w u)

/-- The equilibrium path of the profile `σ`. -/
def Profile.path (σ : Profile) : Outcome :=
  σ.outcomeAtOrder σ.w σ.u

/-- Stage 3 (the manufacturer's direct quantity) is optimal at every history `(w, u, q_R)` with
`u > 0` and `q_R ≥ 0`: `σ.direct w u qR ≥ 0`, and no `q_M ≥ 0` gives her a strictly higher
profit. -/
def Stage3Optimal (k c : ℝ) (σ : Profile) : Prop :=
  ∀ w u qR : ℝ, 0 < u → 0 ≤ qR →
    0 ≤ σ.direct w u qR ∧
    ∀ qM : ℝ, 0 ≤ qM → mfrPayoff k c ⟨w, u, qR, qM⟩ ≤ mfrPayoff k c (σ.outcomeAtDirect w u qR)

/-- Stage 2 (the retailer's order) is optimal at every `(w, u)` with `u > 0`:
`σ.order w u ≥ 0`, and no order `q_R ≥ 0`, followed by the manufacturer's rule
`σ.direct`, gives the retailer a strictly higher profit. -/
def Stage2Optimal (σ : Profile) : Prop :=
  ∀ w u : ℝ, 0 < u →
    0 ≤ σ.order w u ∧
    ∀ qR : ℝ, 0 ≤ qR → retailerPayoff (σ.outcomeAtDirect w u qR) ≤ retailerPayoff (σ.outcomeAtOrder w u)

/-- Stage 1 (the manufacturer's quality and wholesale price) is optimal: `σ.u > 0`, and no
`(w, u)` with `u > 0`, followed by play according to `σ`, gives her a strictly higher profit. -/
def Stage1Optimal (k c : ℝ) (σ : Profile) : Prop :=
  0 < σ.u ∧ ∀ w u : ℝ, 0 < u → mfrPayoff k c (σ.outcomeAtOrder w u) ≤ mfrPayoff k c σ.path

/-- `σ` is a subgame perfect equilibrium of the encroachment game with uniform quality,
quality cost `k` and direct selling cost `c`: the one-shot-deviation condition holds at every
decision node, on or off the path. -/
def IsSPE (k c : ℝ) (σ : Profile) : Prop :=
  Stage3Optimal k c σ ∧ Stage2Optimal σ ∧ Stage1Optimal k c σ

/-- **Encroachment** (p. 11): the manufacturer actually sells through her direct channel on the
equilibrium path, `q^U_M > 0`. -/
def Encroaches (σ : Profile) : Prop :=
  0 < σ.path.qM

/-- `ct` is an **encroachment threshold** for quality cost `k` (Proposition 1(i), p. 11):
`ct > 0`, and for every selling cost `c ≥ 0` and every subgame perfect equilibrium `σ` at
`(k, c)`, the manufacturer encroaches if `c < ct` and does not if `c > ct`. The boundary point
`c = ct` is left open. -/
def IsEncroachThreshold (k ct : ℝ) : Prop :=
  0 < ct ∧ ∀ c : ℝ, 0 ≤ c → ∀ σ : Profile, IsSPE k c σ →
    (c < ct → 0 < σ.path.qM) ∧ (ct < c → σ.path.qM = 0)

/-! ## Closed forms derived by backward induction (pp. 9–10, 27) -/

/-- The benchmark retailer's order formula `q^N_R(w, u) = 1/2 − w/(2u)` (p. 9). -/
noncomputable def qRN (w u : ℝ) : ℝ := 1 / 2 - w / (2 * u)

/-- The benchmark wholesale price given quality, `w^N(u) = k u²/2 + u/2`, equation (1), p. 9. -/
noncomputable def wN (k u : ℝ) : ℝ := k * u ^ 2 / 2 + u / 2

/-- The benchmark manufacturer's profit given quality, `Π^N_M(u) = u(1 − ku)²/8`, (2), p. 9. -/
noncomputable def PiNM (k u : ℝ) : ℝ := u * (1 - k * u) ^ 2 / 8

/-- The benchmark retailer's profit given quality, `Π^N_R(u) = u(1 − ku)²/16`, (2), p. 9. -/
noncomputable def PiNR (k u : ℝ) : ℝ := u * (1 - k * u) ^ 2 / 16

/-- The manufacturer's stage-3 best response
`q^U_M(q_R, w, u) = (1/2 − q_R/2 − c/(2u) − ku/2)⁺` (p. 10). It does not depend on `w`. -/
noncomputable def qUM_br (k c qR _w u : ℝ) : ℝ :=
  max 0 (1 / 2 - qR / 2 - c / (2 * u) - k * u / 2)

/-- The retailer's quantity in the quantity subgame, `q^U_R(w, u) = 1/2 − w/u + ku/2 + c/(2u)`,
equation (3), p. 10. -/
noncomputable def qUR (k c w u : ℝ) : ℝ := 1 / 2 - w / u + k * u / 2 + c / (2 * u)

/-- The manufacturer's direct quantity in the quantity subgame,
`q^U_M(w, u) = 1/4 + w/(2u) − 3ku/4 − 3c/(4u)`, equation (3), p. 10. -/
noncomputable def qUM (k c w u : ℝ) : ℝ := 1 / 4 + w / (2 * u) - 3 * k * u / 4 - 3 * c / (4 * u)

/-- The wholesale price given quality under encroachment, `w^U(u) = ku²/2 + u/2 − c/6`,
equation (4), p. 10. -/
noncomputable def wU (k c u : ℝ) : ℝ := k * u ^ 2 / 2 + u / 2 - c / 6

/-- The manufacturer's profit given quality under encroachment,
`Π^U_M(u) = k²u³/4 + kcu/2 + 7c²/(12u) − ku²/2 + u/4 − c/2`, equation (5), p. 10. -/
noncomputable def PiUM (k c u : ℝ) : ℝ :=
  k ^ 2 * u ^ 3 / 4 + k * c * u / 2 + 7 * c ^ 2 / (12 * u) - k * u ^ 2 / 2 + u / 4 - c / 2

/-- The retailer's profit given quality under encroachment, `Π^U_R(u) = 2c²/(9u)`,
equation (5), p. 10. -/
noncomputable def PiUR (c u : ℝ) : ℝ := 2 * c ^ 2 / (9 * u)

/-- The manufacturer's profit given quality when the retailer orders exactly enough to deter
direct sales, `Π^UZ_M(u) = (ku²/2 − u/2 + 3c/2)(1 − c/u − ku)` (proof of Proposition 1(i),
p. 27). -/
noncomputable def PiUZM (k c u : ℝ) : ℝ := (k * u ^ 2 / 2 - u / 2 + 3 * c / 2) * (1 - c / u - k * u)

/-- The manufacturer's optimal profit given quality, the three-case function `Π_M(u)` of the
proof of Proposition 1(i), p. 27:
`Π^U_M(u)` if `c ≤ 3u(1 − ku)/5`; `Π^UZ_M(u)` if `3u(1 − ku)/5 ≤ c ≤ 5u(1 − ku)/6`;
`Π^N_M(u)` if `c ≥ 5u(1 − ku)/6`. (The three pieces agree at the two boundaries.) -/
noncomputable def PiM (k c u : ℝ) : ℝ :=
  if c ≤ 3 * u * (1 - k * u) / 5 then PiUM k c u
  else if c ≤ 5 * u * (1 - k * u) / 6 then PiUZM k c u
  else PiNM k u

end QualityEncroach.Uniform


