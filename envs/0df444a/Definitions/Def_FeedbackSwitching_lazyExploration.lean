-- Prove2me | Definitions.Def_FeedbackSwitching_lazyExploration
-- name    : FeedbackSwitching_lazyExploration
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T00:43:35.157416+00:00
-- url     : https://prove2.me/theorems/c33a1cbc-0929-44eb-b600-bf863f119ceb
-- title:
--   LazyExploration (Algorithm 4) and the estimate (40), as a policy
-- statement:
--   Given an observing set $D$, an exploration rate $\kappa$ and a learning rate $\eta$, with $D_i=\{s\in D:(s,i)\in E\}$:
--
--   1. Set $\pi_1$ uniform on $[K]$ and draw $\tilde I_1\sim\pi_1$.
--   2. In round $t$ toss a coin $c_t$ with success probability $\kappa$. On success play $I^\circ_t$ uniform on $D$; otherwise play $\tilde I_t$.
--   3. Form
--   $$
--   \hat\ell_t(i)=\frac{|D|}{\kappa|D_i|}\,c_t\,\mathbf 1\{I^\circ_t\in D_i\}\,\ell_t(i)
--   $$
--   and update $\pi_{t+1,i}\propto\pi_{t,i}e^{-\eta\hat\ell_t(i)}$.
--   4. Keep $\tilde I_{t+1}=\tilde I_t$ with probability $e^{-\eta\hat\ell_t(\tilde I_t)}$; otherwise draw $\tilde I_{t+1}\sim\pi_{t+1}$.
--
--   **Formalization Note** The policy reads only the feedback vectors of its history; on exploration rounds the played action $I^\circ_t$ observes $i$ whenever $I^\circ_t\in D_i$. Four coins per round. The module also names the parameters of Theorem 3: `lzKappa` is $\kappa=(|D|\log K/(9T))^{1/3}$ and `lzEta` is $\eta=\sqrt{\kappa\log K/(T|D|)}$.
-- source:
--   Cesa-Bianchi, Cesari, Colomboni, Esposito, Fusco, Koren, The Price of Partial Information with Switching Costs, arXiv:2606.03851 (held version, sha256 ded8f8bc…), Algorithm 4 and Eq. (40), pp.34–35 (PDF pp.36–37)

import Mathlib
import Definitions.Def_UnderstandingML_Online
import Definitions.Def_FeedbackSwitching_Policy
import Definitions.Def_FeedbackSwitching_sampleFin
import Definitions.Def_FeedbackSwitching_tournamentSteering
open scoped Classical

namespace FeedbackSwitching

/-- Cesa-Bianchi et al., arXiv:2606.03851 (held version, sha256 ded8f8bc…).

`D_i = {s ∈ D : (s, i) ∈ E}` (§6.1, p.34). -/
noncomputable def observersIn {K : ℕ} (G : FeedbackGraph K) (D : Finset (Fin K)) (i : Fin K) :
    Finset (Fin K) :=
  D.filter (fun s => G s i)

/-- The uniform law on `D` as a vector. -/
noncomputable def unifOn {K : ℕ} (D : Finset (Fin K)) : Fin K → ℝ :=
  fun s => if s ∈ D then 1 / (D.card : ℝ) else 0

/-- Exploration coin `c_t` of round `t` (success iff the coin is below `κ`). -/
def lzExplore (κ : ℝ) (ω : Coins) (t : ℕ) : Prop :=
  (ω (4 * t + 1) : ℝ) < κ

/-- Exploration draw `I°_t`, uniform on `D`. -/
noncomputable def lzProbe {K : ℕ} [NeZero K] (D : Finset (Fin K)) (ω : Coins) (t : ℕ) : Fin K :=
  sampleFin (unifOn D) (ω (4 * t + 2))

/-- The estimate (40), p.34: `ℓ̂_t(i) = |D| / (κ|D_i|) · c_t 1{I°_t ∈ D_i} ℓ_t(i)`, computed from the
observed vector `fb t` of round `t` (on exploration rounds the played action is `I°_t`, which
observes `i` whenever `I°_t ∈ D_i`). -/
noncomputable def lzEst {K : ℕ} [NeZero K] (G : FeedbackGraph K) (D : Finset (Fin K)) (κ : ℝ)
    (fb : ℕ → Fin K → ℝ) (ω : Coins) (t : ℕ) (i : Fin K) : ℝ :=
  if lzExplore κ ω t ∧ lzProbe D ω t ∈ observersIn G D i then
    (D.card : ℝ) / (κ * (observersIn G D i).card) * fb t i
  else 0

/-- The dartboard arm `Ĩ_t` of Algorithm 4: `Ĩ_1 ∼ π_1` (coin `ω 0`); after round `t` keep it with
probability `e^{−η ℓ̂_t(Ĩ_t)}` (coin `ω (4t + 3)`), otherwise draw `Ĩ_{t+1} ∼ π_{t+1}`
(coin `ω (4t + 4)`), where `π_t = wmWeights η ℓ̂ t` is exponential weights on the estimates. -/
noncomputable def lzArm {K : ℕ} [NeZero K] (G : FeedbackGraph K) (D : Finset (Fin K)) (κ η : ℝ)
    (fb : ℕ → Fin K → ℝ) (ω : Coins) : ℕ → Fin K
  | 0 => sampleFin (UnderstandingML.wmWeights η (lzEst G D κ fb ω) 0) (ω 0)
  | t + 1 =>
      if (ω (4 * t + 3) : ℝ) < Real.exp (-η * lzEst G D κ fb ω t (lzArm G D κ η fb ω t)) then
        lzArm G D κ η fb ω t
      else sampleFin (UnderstandingML.wmWeights η (lzEst G D κ fb ω) (t + 1)) (ω (4 * t + 4))

/-- **LazyExploration** (Algorithm 4, p.35 = PDF p.37) with observing set `D`, exploration rate `κ`
and learning rate `η`, as a policy on i.i.d. uniform coins: in round `t` play `I°_t` (uniform on
`D`) if the exploration coin succeeds, and the dartboard arm `Ĩ_t` otherwise.

**Formalization Note.** The policy reads only the recorded feedback vectors of the history. The
estimate of round `t` uses only the coins of round `t` and the feedback of round `t`. -/
noncomputable def lazyExploration {K : ℕ} [NeZero K] (G : FeedbackGraph K) (D : Finset (Fin K))
    (κ η : ℝ) : Policy K where
  Ω := Coins
  μ := coinLaw
  act := fun t h ω =>
    if lzExplore κ ω t then lzProbe D ω t else lzArm G D κ η (histFeedback h) ω t

/-- The exploration rate of Theorem 3 (p.34): `κ = (|D| log K/(9T))^{1/3}`, with `d = |D|`. -/
noncomputable def lzKappa (K T d : ℕ) : ℝ :=
  ((d : ℝ) * Real.log K / (9 * T)) ^ ((1 : ℝ) / 3)

/-- The learning rate of Theorem 3 (p.34): `η = √(κ log K/(T|D|))`, with `d = |D|`. -/
noncomputable def lzEta (K T d : ℕ) : ℝ :=
  Real.sqrt (lzKappa K T d * Real.log K / (T * d))

end FeedbackSwitching


