-- Prove2me | Definitions.Def_AcquihiringMonopsony_Bargaining_NashSplit
-- name    : AcquihiringMonopsony_Bargaining_NashSplit
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:04.853052+00:00
-- url     : https://prove2.me/theorems/4ed7aa91-0fa2-435e-927f-bcee150499e9
-- title:
--   pp. 7–9 — threat points $t_a, t_s$, the Nash split with bargaining power $\alpha$, acquihiring payoffs, and the thresholds $\overline{v}_a, \underline{v}_a$
-- statement:
--   This file defines the acquihiring branch of the bargaining extension (§4) of the acquihiring model.
--
--   The acquirer may try to buy the startup. The acquirer and the startup bargain over the acquisition price, the acquirer having bargaining power $\alpha$. If the bid fails, with probability $\delta$ the acquirer competes for the employee in the direct-hiring subgame (whose continuation profile we call $\sigma_F$); with probability $1-\delta$ the acquirer is absent and the startup keeps the employee at the floor wage $\underline{w}$. The **threat points** are the firms' expected continuation payoffs after a failed bid:
--
--   $$t_a = \delta\,\pi_a(\sigma_F), \qquad t_s = \delta\,\pi_s(\sigma_F) + (1-\delta)(v_s - \underline{w}),$$
--
--   where $\pi_a(\sigma_F)$, $\pi_s(\sigma_F)$ are the acquirer's and the startup's payoffs on the path of $\sigma_F$. An acquisition yields the two firms the joint payoff $v_a - \underline{w}$, since the acquirer, then a monopsonist, pays the employee $\underline{w}$. Nash bargaining makes the **acquisition occur** exactly when the surplus $v_a - \underline{w} - (t_a + t_s)$ is positive, and then the price is
--
--   $$p = t_s + (1-\alpha)\bigl[v_a - \underline{w} - (t_a + t_s)\bigr].$$
--
--   The acquirer's expected payoff from choosing acquihiring is $v_a - \underline{w} - p$ if the acquisition occurs and $t_a$ otherwise. The employee's expected payoff from acquihiring is $\underline{w}$ if the acquisition occurs; otherwise it is $\delta$ times her payoff on the path of $\sigma_F$ plus $(1-\delta)(\underline{w} + b)$ (retained at the floor wage, with her private benefit).
--
--   Finally, the thresholds of Proposition 2 are
--
--   $$\overline{v}_a = v_s + b + \frac{\alpha}{(1-\alpha)(1-\delta)}\bigl[\delta(v_s - \underline{w}) + b\bigr], \qquad \underline{v}_a = \frac{v_s + \delta(\underline{w} + b)}{1+\delta}.$$
--
--   **Formalization Note** The Nash split is defined in closed form, as the paper uses it in the proof of Lemma 3; the paper never writes the (asymmetric) Nash product, and the platform's symmetric Nash-bargaining items are a different object. The threat points are defined from the *equilibrium payoffs* of an arbitrary direct-hiring profile $\sigma_F$, not from Lemma 1's formulas; that they equal those formulas is a theorem. In Lean $x/0 = 0$, so $\overline{v}_a$ is meaningful only for $\alpha < 1$ and $\delta < 1$; every theorem using it assumes both.
-- source:
--   Bar-Isaac, Johnson, Nocke, Acquihiring for Monopsony Power, CRC TR 224 DP No. 500 (Jan. 2024), pp. 7–8 (PDF 8–9), §4 setup; p. 8 (PDF 9), proof of Lemma 3 (price display); p. 9 (PDF 10), Proposition 2 (definitions of v̄_a, v̲_a)

import Mathlib
import Definitions.Def_AcquihiringMonopsony_Baseline_Model

namespace AcquihiringMonopsony.Bargaining

/-- The acquirer's threat point t_a (pp. 7–8): after a failed bid, with probability `δ` the direct-hiring
subgame is played (continuation `σF`), otherwise the acquirer gets nothing. -/
def threatA (P : Baseline.Params) (δ : ℝ) (σF : Baseline.DHProfile) : ℝ := δ * Baseline.dhPayoffA P σF.acceptA σF.wa σF.ws

/-- The startup's threat point t_s (pp. 7–8): with probability `δ` the direct-hiring subgame is played
(continuation `σF`), otherwise the startup retains the employee at the wage floor w̲. -/
def threatS (P : Baseline.Params) (δ : ℝ) (σF : Baseline.DHProfile) : ℝ :=
  δ * Baseline.dhPayoffS P σF.acceptA σF.wa σF.ws + (1 - δ) * (P.vs - P.wl)

/-- Nash bargaining: the acquisition occurs whenever the surplus v_a − w̲ − (t_a + t_s) is positive (p. 8). -/
def AcquisitionOccurs (P : Baseline.Params) (δ : ℝ) (σF : Baseline.DHProfile) : Prop :=
  threatA P δ σF + threatS P δ σF < P.va - P.wl

/-- The Nash-bargaining acquisition price with acquirer bargaining power `α` (proof of Lemma 3, p. 8):
p = t_s + (1 − α)[v_a − w̲ − (t_a + t_s)]. -/
def price (P : Baseline.Params) (α δ : ℝ) (σF : Baseline.DHProfile) : ℝ :=
  threatS P δ σF + (1 - α) * (P.va - P.wl - (threatA P δ σF + threatS P δ σF))

open Classical in
/-- the acquirer's expected payoff from choosing acquihiring -/
noncomputable def ahPayoffA (P : Baseline.Params) (α δ : ℝ) (σF : Baseline.DHProfile) : ℝ :=
  if AcquisitionOccurs P δ σF then P.va - P.wl - price P α δ σF else threatA P δ σF

open Classical in
/-- the employee's expected payoff from acquihiring: w̲ after an acquisition (monopsony wage, as in Lemma 2);
  after a failed bid, direct hiring with probability δ, else w̲ + b at the startup -/
noncomputable def ahPayoffE (P : Baseline.Params) (δ : ℝ) (σF : Baseline.DHProfile) : ℝ :=
  if AcquisitionOccurs P δ σF then P.wl
  else δ * Baseline.dhPayoffE P σF.acceptA σF.wa σF.ws + (1 - δ) * (P.wl + P.b)

/-- The threshold v̄_a of Proposition 2 (p. 9). -/
noncomputable def vUpper (P : Baseline.Params) (α δ : ℝ) : ℝ :=
  P.vs + P.b + α / ((1 - α) * (1 - δ)) * (δ * (P.vs - P.wl) + P.b)

/-- The threshold v̲_a of Proposition 2 (p. 9). -/
noncomputable def vLower (P : Baseline.Params) (δ : ℝ) : ℝ := (P.vs + δ * (P.wl + P.b)) / (1 + δ)

end AcquihiringMonopsony.Bargaining


