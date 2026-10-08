-- Prove2me | Definitions.Def_SchmidliRuin_Verif_Model
-- name    : SchmidliRuin_Verif_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T01:11:10.499735+00:00
-- url     : https://prove2.me/theorems/e4ac636c-9816-4aef-aa2a-4a62b85ec305
-- title:
--   §1, pp. 890–891 — classical risk model, Black–Scholes investment, proportional reinsurance, surplus X^{Ab}, ruin, survival probability δ^{Ab}(u) and value function δ(u)
-- statement:
--   This file sets up the stochastic control model of §1 of Schmidli (2002).
--
--   **The basis.** On a probability space $(\Omega,\mathcal F,\mathbb P)$ there are i.i.d. exponential interarrival times $E_1,E_2,\dots$ with rate $\lambda>0$, i.i.d. claim sizes $Y_1,Y_2,\dots$ with law $\nu$ (where $G(0)=0$ and $G$ is continuous), and a standard Brownian motion $W$; the three families are mutually independent. The claim times are $T_i=E_1+\dots+E_i$, the number of claims is $N_t=\#\{i:T_i\le t\}$ (a Poisson process with rate $\lambda$), and the aggregate claims are $S_t=\sum_{i=1}^{N_t}Y_i$. The classical risk process is $X^{01}_t=u+ct-S_t$.
--
--   **The filtration.** $\mathcal F_t=\bigcap_{s>t}\sigma(S_r,W_r:r\le s)$, the smallest right-continuous filtration to which $(X^{01},W)$ is adapted. It is not completed.
--
--   **Admissible strategies.** A pair $(A,b)$ — $A_t$ the amount invested in the risky asset $Z_t=\exp\{\sigma W_t+(\mu-\frac12\sigma^2)t\}$, $b_t\in[0,1]$ the retention level of proportional reinsurance, at premium rate $c(b_t)$ — is admissible from initial capital $u$, with surplus process $X$, if $A$ and $b$ are $\{\mathcal F_t\}$-predictable, $A$ is locally bounded, the Itô integral $J_t=\int_0^t\sigma A_s\,dW_s$ exists with continuous paths, and
--   $$X_t=u+\int_0^t\big(c-c(b_s)+\mu A_s\big)\,ds+\int_0^t\sigma A_s\,dW_s-\sum_{i=1}^{N_t}b_{T_i}Y_i ,$$
--   which is the solution of $dX_t=(c-c(b_t)+\mu A_t)\,dt+\sigma A_t\,dW_t-b_t\,dS_t$, $X_0=u$.
--
--   **Ruin and value.** The ruin time is $\tau=\inf\{t\ge0:X_t<0\}$; the survival probability is $\delta^{Ab}(u)=\mathbb P[\tau=\infty]$, and the value function is
--   $$\delta(u)=\sup_{A,b}\delta^{Ab}(u),$$
--   the supremum over all admissible strategies from $u$. The stopped process is $X_{t\wedge\tau}$, and $X_{t-}$ denotes the left limit (with $X_{0-}=u$). A strategy **follows the feedback rule** $(A^*,b^*)$ if $A_t=A^*(X_{t-})$ and $b_t=b^*(X_{t-})$ whenever $X_{t-}>0$.
--
--   This is the model in which Theorem 1 identifies the maximal survival probability and the optimal strategy.
--
--   **Formalization Note** The Poisson process is realised through its i.i.d. exponential interarrival times. The paper states only that $\{N_t\}$ and $\{Y_i\}$ are independent; independence of $W$ from the claims is not printed but is used by (1) and the proof of Theorem 1, so it is part of the basis. The Itô integral is `EthierKurtz.HasBrownianItoIntegral` (limit in probability of predictable step sums), and continuous paths of $J$ are required so that the pathwise ruin event does not depend on a bad modification. $N_t$ is computed as the least $n$ with $t<T_{n+1}$, which is the count whenever the claim times increase to infinity (almost surely). The investment $A_t$ is not restricted in sign, as in the paper. The retention applied to the $i$-th claim is $b_{T_i}$, which, by predictability, is the pre-jump value. Controls at non-positive pre-jump surplus are left free in the feedback rule.
-- source:
--   Schmidli, On minimizing the ruin probability by investment and reinsurance, Ann. Appl. Probab. 12 (2002), pp. 890–891, §1

import Mathlib
import Definitions.Def_EthierKurtz_HasBrownianItoIntegral
import Definitions.Def_SchmidliRuin_Verif_Setting

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal

namespace SchmidliRuin.Verif

/-- The random data of the model of §1, pp. 890–891, on a measurable space `Ω`: a measure `P`,
the claim intensity `lam`, the claim-size law `ν`, the interarrival times `E i`
(`E 0 = T₁`, `E i = T_{i+1} - T_i`), the claim sizes `Y i` (`Y i` is the paper's `Y_{i+1}`)
and the Brownian motion `W`. -/
structure RiskBasis (Ω : Type*) [MeasurableSpace Ω] where
  P : Measure Ω
  lam : ℝ
  ν : Measure ℝ
  E : ℕ → Ω → ℝ
  Y : ℕ → Ω → ℝ
  W : ℝ≥0 → Ω → ℝ

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The probabilistic assumptions of §1: `P` is a probability measure; `lam > 0`; the
interarrival times are i.i.d. exponential with rate `lam` (so the claim counting process is a
Poisson process with rate `lam`); the claim sizes are i.i.d. with law `ν`, where `ν` is a
`ClaimLaw` (`G(0) = 0`, `G` continuous); `W` is a standard Brownian motion; and the three
families `(E i)`, `(Y i)`, `W` are mutually independent. -/
def RiskBasis.IsValid (B : RiskBasis Ω) : Prop :=
  IsProbabilityMeasure B.P ∧ 0 < B.lam ∧
  (∀ i, Measurable (B.E i)) ∧ iIndepFun B.E B.P ∧
    (∀ i, B.P.map (B.E i) = expMeasure B.lam) ∧
  (∀ i, Measurable (B.Y i)) ∧ iIndepFun B.Y B.P ∧ (∀ i, B.P.map (B.Y i) = B.ν) ∧
  ClaimLaw B.ν ∧
  IsBrownianReal B.W B.P ∧
  IndepFun (fun ω (i : ℕ) => B.E i ω) (fun ω (i : ℕ) => B.Y i ω) B.P ∧
  IndepFun (fun ω => ((fun i : ℕ => B.E i ω), (fun i : ℕ => B.Y i ω)))
    (fun ω (t : ℝ≥0) => B.W t ω) B.P

/-- The claim times: `T n = E 0 + ⋯ + E n` is the time of the `(n+1)`-st claim. -/
noncomputable def RiskBasis.T (B : RiskBasis Ω) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), B.E k ω

/-- The claim counting process `N_t = #{n : T n ≤ t}`, computed as the least `n` with
`t < T n` (this is the count whenever the claim times increase to infinity, which holds
almost surely). -/
noncomputable def RiskBasis.N (B : RiskBasis Ω) (t : ℝ≥0) (ω : Ω) : ℕ :=
  sInf {n : ℕ | (t : ℝ) < B.T n ω}

/-- The aggregate claims process `S_t = ∑_{i ≤ N_t} Y_i`. -/
noncomputable def RiskBasis.S (B : RiskBasis Ω) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range (B.N t ω), B.Y i ω

/-- The classical risk process `X_t^{01} = u + ct - S_t`. -/
noncomputable def RiskBasis.X01 (B : RiskBasis Ω) (c u : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  u + c * t - B.S t ω

/-- The σ-algebra `σ(S_r, W_r : r ≤ s)` generated by the claims process and the Brownian motion
up to time `s` (equal to `σ(X^{01}_r, W_r : r ≤ s)`, since `X^{01} = u + ct - S`). -/
noncomputable def RiskBasis.natGen (B : RiskBasis Ω) (s : ℝ≥0) : MeasurableSpace Ω :=
  ⨆ r ≤ s, (MeasurableSpace.comap (B.S r) inferInstance ⊔
    MeasurableSpace.comap (B.W r) inferInstance)

/-- `𝓕_t = ⋂_{s > t} σ(S_r, W_r : r ≤ s)`: the smallest right-continuous filtration to which
`(X^{01}, W)` is adapted (p. 891). It is not completed. -/
noncomputable def RiskBasis.filt (B : RiskBasis Ω) (t : ℝ≥0) : MeasurableSpace Ω :=
  ⨅ s > t, B.natGen s

/-- The filtration `{𝓕_t}` as a Mathlib filtration (on the σ-algebra `⋁_t 𝓕_t`). -/
noncomputable def RiskBasis.filtration (B : RiskBasis Ω) : Filtration ℝ≥0 (⨆ t, B.filt t) where
  seq := B.filt
  mono' _ _ hst := biInf_mono fun _ hs => lt_of_le_of_lt hst hs
  le' t := le_iSup B.filt t

/-- `(A, b, X)` is an admissible strategy with surplus process from initial capital `u`
(p. 891 and p. 896): `A` (the amount invested in the risky asset) and `b` (the retention
level) are predictable with respect to `{𝓕_t}`; `b_t ∈ [0, 1]`; `A` is locally bounded; the
Itô integral `J = ∫_0^· σ A_s dW_s` exists with continuous paths; and `X` solves
`dX_t = (c - c(b_t) + µA_t) dt + σA_t dW_t - b_t dS_t`, `X_0 = u`, i.e. for all `t` and `ω`
`X_t = u + ∫_0^t (c - c(b_s) + µA_s) ds + J_t - ∑_{i ≤ N_t} b_{T_i} Y_i`. -/
def IsAdmissible (B : RiskBasis Ω) (c mu sigma : ℝ) (cb : ℝ → ℝ) (u : ℝ)
    (A b X : ℝ≥0 → Ω → ℝ) : Prop :=
  IsStronglyPredictable B.filtration A ∧ IsStronglyPredictable B.filtration b ∧
  (∀ t ω, b t ω ∈ Icc (0 : ℝ) 1) ∧
  (∀ ω (T : ℝ≥0), ∃ C : ℝ, ∀ t ≤ T, |A t ω| ≤ C) ∧
  ∃ J : ℝ≥0 → Ω → ℝ,
    EthierKurtz.HasBrownianItoIntegral B.P B.filt B.W (fun t ω => sigma * A t ω) J ∧
    (∀ ω, Continuous (fun t => J t ω)) ∧
    ∀ (t : ℝ≥0) (ω : Ω),
      X t ω = u + (∫ s in (0 : ℝ)..(t : ℝ),
          (c - cb (b s.toNNReal ω) + mu * A s.toNNReal ω))
        + J t ω
        - ∑ i ∈ Finset.range (B.N t ω), b (B.T i ω).toNNReal ω * B.Y i ω

/-- The surplus path never becomes negative: `τ = ∞`. -/
def survives (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : Prop := ∀ t, 0 ≤ X t ω

/-- The ruin time `τ = inf {t ≥ 0 : X_t < 0}` in `[0, ∞]` (`inf ∅ = ∞`). -/
noncomputable def ruinTime (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0∞ :=
  ⨅ (t : ℝ≥0) (_ : X t ω < 0), (t : ℝ≥0∞)

/-- The stopped process `X_{t ∧ τ}`. -/
noncomputable def stopped (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  X (if ruinTime X ω < ⊤ then min t (ruinTime X ω).toNNReal else t) ω

/-- The survival probability `δ^{Ab}(u) = ℙ[τ^{Ab} = ∞]` of a surplus process. -/
noncomputable def survivalProb (B : RiskBasis Ω) (X : ℝ≥0 → Ω → ℝ) : ℝ :=
  (B.P {ω | survives X ω}).toReal

/-- The value function `δ(u) = sup_{A,b} δ^{Ab}(u)`, the supremum over all admissible
strategies from `u`. -/
noncomputable def valueFn (B : RiskBasis Ω) (c mu sigma : ℝ) (cb : ℝ → ℝ) (u : ℝ) : ℝ :=
  sSup {p | ∃ A b X : ℝ≥0 → Ω → ℝ, IsAdmissible B c mu sigma cb u A b X ∧
    p = survivalProb B X}

/-- The left limit `X_{t-}`, with `X_{0-} = u`. -/
noncomputable def leftVal (u : ℝ) (X : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  if t = 0 then u else Function.leftLim (fun s => X s ω) t

/-- `(A, b)` is the feedback strategy `A_t = A*(X_{t-})`, `b_t = b*(X_{t-})` of Theorem 1,
whenever `X_{t-} > 0` (the controls at non-positive surplus are left free). -/
def FollowsFeedback (mu sigma : ℝ) (f bstar : ℝ → ℝ) (u : ℝ) (A b X : ℝ≥0 → Ω → ℝ) : Prop :=
  ∀ t ω, 0 < leftVal u X t ω →
    A t ω = Astar mu sigma f (leftVal u X t ω) ∧ b t ω = bstar (leftVal u X t ω)

end SchmidliRuin.Verif


