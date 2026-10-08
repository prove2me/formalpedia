-- Prove2me | Definitions.Def_QualityEncroach_NoCommit_Game
-- name    : QualityEncroach_NoCommit_Game
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:57.640842+00:00
-- url     : https://prove2.me/theorems/0527a05b-54b3-428a-b532-6a6be68a9a55
-- title:
--   §3.1, §5, §6.3, pp. 7–8, 15, 21, 37 — two-quality demand, the game without quality commitment for the direct channel, its SPE, and the reduced forms Π^HF_M, Π^LF_M
-- statement:
--   This file sets up the model of §6.3 of Ha, Long & Nasiry, *Quality in Supply Chain Encroachment*: a manufacturer sells through a retailer and may also sell directly ("encroach"), but cannot commit in advance to the quality of the product she sells directly.
--
--   **Consumers and demand.** Consumers have quality sensitivity $\theta$ uniformly distributed on $[0,1]$ and obtain surplus $\theta u - p$ from a product of quality $u>0$ at price $p$. The manufacturer sells $q_M$ units of quality $u_M$ directly, the retailer sells $q_R$ units of quality $u_R$. The market-clearing prices depend on which product is the higher quality:
--
--   1. if $u_R \le u_M$ (direct product high): $p_M = u_M(1-q_M) - u_R q_R$ and $p_R = u_R(1-q_M-q_R)$;
--   2. if $u_M < u_R$ (retailer product high): $p_M = u_M(1-q_M-q_R)$ and $p_R = u_R(1-q_R) - u_M q_M$.
--
--   When $u_M = u_R = u$ both reduce to the single price $u(1-q_M-q_R)$.
--
--   **Costs and payoffs.** The unit cost of quality $v$ is $kv^2$ with $k>0$; the manufacturer pays a selling cost $c\ge0$ per unit sold directly; the retailer's selling cost is $0$. For a wholesale price $w$,
--   $$
--   \Pi_R = (p_R - w)\,q_R, \qquad \Pi_M = (w - k u_R^2)\,q_R + (p_M - c - k u_M^2)\,q_M .
--   $$
--
--   **Timing.** (i) The manufacturer announces the retailer's quality $u_R$ and the wholesale price $w$; (ii) the retailer orders $q_R$; (iii) the manufacturer chooses the direct-channel quality $u_M$ and the direct quantity $q_M$. A strategy profile consists of the manufacturer's stage-1 choice $(w,u_R)$, the retailer's rule $(w,u_R)\mapsto q_R$ and the manufacturer's stage-3 rule $(w,u_R,q_R)\mapsto(u_M,q_M)$. It is a **subgame perfect equilibrium** when at every history, on or off the equilibrium path, the mover picks a feasible action ($u_R,u_M>0$, $q_R,q_M\ge0$, $w$ unrestricted) and no feasible alternative, followed by play according to the profile, gives the mover a strictly higher profit. The manufacturer **encroaches** when $q_M>0$ on the equilibrium path.
--
--   **Reduced forms (p. 37).** Writing $u_M = \tau u_R$ with $\tau>0$, the file defines
--   $$
--   q_M^{HF}(\tau,q_R,u_R) = \Big(\tfrac{-c - q_R u_R - k\tau^2u_R^2 + \tau u_R}{2\tau u_R}\Big)^{+},\qquad
--   q_M^{LF}(\tau,q_R,u_R) = \Big(\tfrac{-c - \tau u_R(q_R + k\tau u_R - 1)}{2\tau u_R}\Big)^{+},
--   $$
--   $$
--   \Pi^{HF}_M(\tau,q_R,u_R,w) = \frac{(c + u_R(q_R + \tau(k\tau u_R - 1)))^2}{4\tau u_R} + q_R(w-ku_R^2),\qquad
--   \Pi^{LF}_M(\tau,q_R,u_R,w) = \frac{(c + \tau u_R(q_R + k\tau u_R - 1))^2}{4\tau u_R} + q_R(w-ku_R^2).
--   $$
--
--   These objects are shared by every statement of the mission: Proposition 7 and the three steps of its proof.
--
--   **Formalization Note.** The paper states the demand only for the direct product high and says the other case is "derived similarly" (p. 15); the second branch is that derivation. The inverse demand is used for all nonnegative quantities, as in the paper. The paper never defines $\tau$ in words; its formulas read $u_M=\tau u_R$, with HF for $\tau\ge1$ and LF for $\tau\le1$. The page writes only the HF quantity; $q_M^{LF}$ is the "similarly" case. The divisions are junk at $\tau u_R = 0$; every statement using them assumes $\tau>0$, $u_R>0$. Subgame perfection is stated in one-shot-deviation form, which coincides with subgame perfection in this finite three-stage game.
-- source:
--   Ha, Long & Nasiry, Quality in Supply Chain Encroachment, authors' manuscript, SSRN 3970373, pp. 7–8 §3.1 (consumers, costs), p. 15 §5 (two-quality demand), p. 21 §6.3 (timeline without quality commitment), p. 37 proof of Proposition 7 (q_M, Π^HF_M, Π^LF_M)

import Mathlib

namespace QualityEncroach.NoCommit

/-!
# Ha, Long & Nasiry, *Quality in Supply Chain Encroachment*, §6.3 (pp. 7–8, 15, 21, 37)

Consumers have types `θ ~ U[0,1]` and surplus `θu − p` (p. 7). The manufacturer's unit cost
of quality `u` is `k u²` with `k > 0`; she pays `c ≥ 0` per unit sold through her direct
channel; the retailer's selling cost is `0` (p. 8).

**No quality commitment for the direct channel** (§6.3, p. 21), a three-stage game with
perfect information:
1. the manufacturer announces the retailer's product quality `u_R` and the wholesale price `w`;
2. the retailer chooses the order quantity `q_R`;
3. the manufacturer chooses the direct-channel product quality `u_M` and the direct selling
   quantity `q_M`.

With two qualities on the market the inverse demand depends on which product is the higher
quality (p. 15).

Action sets: `w ∈ ℝ` (no sign restriction is stated), qualities `u_R, u_M > 0`, quantities
`≥ 0`. Subgame perfection is stated in one-shot-deviation form at every history, on or off
the path.

The file also holds the reduced forms of the stage-3 problem used in the proof of
Proposition 7 (p. 37), written with `u_M = τ u_R`.
-/

/-! ## Demand -/

/-- The direct-channel market-clearing price when the manufacturer sells `qM` units of quality
`uM` directly and the retailer sells `qR` units of quality `uR` (p. 15, with `u = u_M`,
`tu = u_R`):
* if `uR ≤ uM` (the direct product is the higher quality): `uM (1 − qM) − uR qR`;
* otherwise (the retailer's product is the higher quality): `uM (1 − qM − qR)`.
Both branches agree when `uM = uR`. -/
noncomputable def priceM (uM uR qM qR : ℝ) : ℝ :=
  if uR ≤ uM then uM * (1 - qM) - uR * qR else uM * (1 - qM - qR)

/-- The retailer-channel market-clearing price (p. 15, with `u = u_M`, `tu = u_R`):
* if `uR ≤ uM` (the direct product is the higher quality): `uR (1 − qM − qR)`;
* otherwise (the retailer's product is the higher quality): `uR (1 − qR) − uM qM`.
Both branches agree when `uM = uR`. -/
noncomputable def priceR (uM uR qM qR : ℝ) : ℝ :=
  if uR ≤ uM then uR * (1 - qM - qR) else uR * (1 - qR) - uM * qM

/-! ## The game without quality commitment, §6.3 -/

/-- A terminal history of the game: the wholesale price `w`, the retailer's product quality
`uR`, the retailer's order `qR`, the direct-channel product quality `uM` and the direct selling
quantity `qM`. -/
structure Outcome where
  w : ℝ
  uR : ℝ
  qR : ℝ
  uM : ℝ
  qM : ℝ

/-- The retailer's profit `(p_R − w) q_R`. -/
noncomputable def retailerPayoff (o : Outcome) : ℝ :=
  (priceR o.uM o.uR o.qM o.qR - o.w) * o.qR

/-- The manufacturer's profit `(w − k u_R²) q_R + (p_M − c − k u_M²) q_M`: the wholesale margin
on the retailer's order of the product of quality `u_R` (unit cost `k u_R²`), plus the
direct-channel margin net of the selling cost `c` and the unit cost `k u_M²`. -/
noncomputable def mfrPayoff (k c : ℝ) (o : Outcome) : ℝ :=
  (o.w - k * o.uR ^ 2) * o.qR + (priceM o.uM o.uR o.qM o.qR - c - k * o.uM ^ 2) * o.qM

/-- A pure strategy profile:
* `w`, `uR` — the manufacturer's stage-1 choice;
* `order w uR = q_R` — the retailer's rule, a function of the observed `(w, u_R)`;
* `stage3 w uR qR = (u_M, q_M)` — the manufacturer's stage-3 rule, a function of
  `(w, u_R, q_R)`. -/
structure Profile where
  w : ℝ
  uR : ℝ
  order : ℝ → ℝ → ℝ
  stage3 : ℝ → ℝ → ℝ → ℝ × ℝ

/-- The outcome after the history `(w, u_R, q_R)` when the manufacturer then follows
`σ.stage3`. -/
def Profile.outcomeAtStage3 (σ : Profile) (w uR qR : ℝ) : Outcome :=
  ⟨w, uR, qR, (σ.stage3 w uR qR).1, (σ.stage3 w uR qR).2⟩

/-- The outcome after the manufacturer announces `(w, u_R)` and play then follows `σ`. -/
def Profile.outcomeAtOrder (σ : Profile) (w uR : ℝ) : Outcome :=
  σ.outcomeAtStage3 w uR (σ.order w uR)

/-- The equilibrium path of the profile `σ`. -/
def Profile.path (σ : Profile) : Outcome :=
  σ.outcomeAtOrder σ.w σ.uR

/-- Stage 3 is optimal at every history `(w, u_R, q_R)` with `u_R > 0` and `q_R ≥ 0`: the rule
picks `u_M > 0` and `q_M ≥ 0`, and no pair `(u_M', q_M')` with `u_M' > 0`, `q_M' ≥ 0` gives the
manufacturer a strictly higher profit. -/
def Stage3Optimal (k c : ℝ) (σ : Profile) : Prop :=
  ∀ w uR qR : ℝ, 0 < uR → 0 ≤ qR →
    0 < (σ.stage3 w uR qR).1 ∧ 0 ≤ (σ.stage3 w uR qR).2 ∧
    ∀ uM qM : ℝ, 0 < uM → 0 ≤ qM →
      mfrPayoff k c ⟨w, uR, qR, uM, qM⟩ ≤ mfrPayoff k c (σ.outcomeAtStage3 w uR qR)

/-- Stage 2 is optimal at every `(w, u_R)` with `u_R > 0`: `σ.order w u_R ≥ 0`, and no order
`q_R ≥ 0`, followed by the manufacturer's rule `σ.stage3`, gives the retailer a strictly
higher profit. -/
def Stage2Optimal (σ : Profile) : Prop :=
  ∀ w uR : ℝ, 0 < uR →
    0 ≤ σ.order w uR ∧
    ∀ qR : ℝ, 0 ≤ qR →
      retailerPayoff (σ.outcomeAtStage3 w uR qR) ≤ retailerPayoff (σ.outcomeAtOrder w uR)

/-- Stage 1 is optimal: `σ.uR > 0`, and no `(w, u_R)` with `u_R > 0`, followed by play
according to `σ`, gives the manufacturer a strictly higher profit. -/
def Stage1Optimal (k c : ℝ) (σ : Profile) : Prop :=
  0 < σ.uR ∧ ∀ w uR : ℝ, 0 < uR → mfrPayoff k c (σ.outcomeAtOrder w uR) ≤ mfrPayoff k c σ.path

/-- `σ` is a subgame perfect equilibrium of the game without quality commitment, with quality
cost `k` and direct selling cost `c`: the one-shot-deviation condition holds at every decision
node, on or off the path. -/
def IsSPE (k c : ℝ) (σ : Profile) : Prop :=
  Stage3Optimal k c σ ∧ Stage2Optimal σ ∧ Stage1Optimal k c σ

/-- **Encroachment** (p. 11): the manufacturer actually sells through her direct channel on
the equilibrium path, `q_M > 0`. -/
def Encroaches (σ : Profile) : Prop :=
  0 < σ.path.qM

/-! ## Reduced forms of the stage-3 problem, proof of Proposition 7 (p. 37)

Here `u_M = τ u_R` with `τ > 0`: `τ ≥ 1` is a direct product of (weakly) higher quality
(superscript `HF`), `τ ≤ 1` one of (weakly) lower quality (superscript `LF`). -/

/-- The manufacturer's optimal direct quantity for `τ ≥ 1` (p. 37):
`q_M(τ, q_R, u_R) = ((−c − q_R u_R − k τ² u_R² + τ u_R) / (2 τ u_R))⁺`. -/
noncomputable def qMHF (k c τ qR uR : ℝ) : ℝ :=
  max 0 ((-c - qR * uR - k * τ ^ 2 * uR ^ 2 + τ * uR) / (2 * τ * uR))

/-- The manufacturer's optimal direct quantity for `τ ≤ 1`, obtained "similarly" (p. 37):
`((−c − τ u_R (q_R + k τ u_R − 1)) / (2 τ u_R))⁺`. -/
noncomputable def qMLF (k c τ qR uR : ℝ) : ℝ :=
  max 0 ((-c - τ * uR * (qR + k * τ * uR - 1)) / (2 * τ * uR))

/-- `Π^HF_M(τ, q_R, u_R, w) = (c + u_R(q_R + τ(kτu_R − 1)))² / (4τu_R) + q_R(w − k u_R²)`
(p. 37). -/
noncomputable def PiHF (k c τ qR uR w : ℝ) : ℝ :=
  (c + uR * (qR + τ * (k * τ * uR - 1))) ^ 2 / (4 * τ * uR) + qR * (w - k * uR ^ 2)

/-- `Π^LF_M(τ, q_R, u_R, w) = (c + τu_R(q_R + kτu_R − 1))² / (4τu_R) + q_R(w − k u_R²)`
(p. 37). -/
noncomputable def PiLF (k c τ qR uR w : ℝ) : ℝ :=
  (c + τ * uR * (qR + k * τ * uR - 1)) ^ 2 / (4 * τ * uR) + qR * (w - k * uR ^ 2)

end QualityEncroach.NoCommit


