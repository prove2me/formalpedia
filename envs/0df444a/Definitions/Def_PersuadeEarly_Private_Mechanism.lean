-- Prove2me | Definitions.Def_PersuadeEarly_Private_Mechanism
-- name    : PersuadeEarly_Private_Mechanism
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:26:49.052561+00:00
-- url     : https://prove2.me/theorems/76cc15e3-7460-40d3-bf53-48343446e56c
-- title:
--   App. A.2.2, pp. 6–8, 39–40 — straightforward Buy/Wait/No mechanisms, rationing, revenue (3), obedience (Buy-1)–(No), public signaling, $R^*_\phi$ (11)
-- statement:
--   This file defines the class of signaling mechanisms over which the paper's optimality results are stated, in the form its proofs use: straightforward mechanisms that recommend *Buy*, *Wait* or *No* to each customer and are obeyed.
--
--   **Rationing.** A customer who requests the product in a period in which $s$ units are left and the other customers' demand has mass $D$ gets it with probability
--   $$\mathrm{avail}(s,D)=\begin{cases}0 & s\le 0,\\ 1 & 0<s,\ D\le s,\\ s/D & \text{otherwise.}\end{cases}$$
--   With stock $q$ and period-1 and period-2 demands $D_1,D_2$, the availabilities are $\alpha_1=\mathrm{avail}(q,D_1)$ and $\alpha_2=\mathrm{avail}((q-D_1)^+,D_2)$, and the sales revenue at prices $p_1,p_2$ is $p_1\min\{D_1,q\}+p_2\min\{D_2,(q-D_1)^+\}$.
--
--   **Mechanisms.** A mechanism consists of prices $p_1,p_2$, a finite latent index $k\in\{0,\dots,n-1\}$ with laws $\pi_H,\pi_L$ in the two inventory states, and recommendation probabilities: in state $\theta\in\{H,L\}$ with index $k$, each $v$-customer is independently told *Buy* with probability $b_{\theta,k}(v)$, *Wait* with probability $w_{\theta,k}(v)$, and *No* otherwise. It is *valid* when $p_1,p_2\ge 0$, $\pi_H,\pi_L$ are probability vectors, and the $b_{\theta,k},w_{\theta,k}$ are measurable with $b,w\ge0$, $b+w\le1$. The masses told *Buy* and *Wait* are $D_{1,\theta,k}=\int b_{\theta,k}\,dF$ and $D_{2,\theta,k}=\int w_{\theta,k}\,dF$, facing stock $q_H=1$ or $q_L$.
--
--   **Revenue** (3) is the expected rationed sales revenue:
--   $$R=P(H)\sum_k\pi_H(k)\,\mathrm{sales}_{1}(D_{1,H,k},D_{2,H,k})+P(L)\sum_k \pi_L(k)\,\mathrm{sales}_{q_L}(D_{1,L,k},D_{2,L,k}).$$
--
--   **Obedience** ((Buy-1)–(No), p. 40). For $F$-almost every $v$, with all sums over both states and all $k$ weighted by $P(\theta)\pi_\theta(k)$:
--   1. (Buy-1) $\sum b_{\theta,k}(v)\big[(v-p_1)\alpha_1-(v-p_2)\alpha_2\big]\ge0$;
--   2. (Buy-2) $\sum b_{\theta,k}(v)(v-p_1)\alpha_1\ge0$;
--   3. (Wait-1) $\sum w_{\theta,k}(v)\big[(v-p_2)\alpha_2-(v-p_1)\alpha_1\big]\ge0$;
--   4. (Wait-2) $\sum w_{\theta,k}(v)(v-p_2)\alpha_2\ge0$;
--   5. (No) $\sum (1-b-w)_{\theta,k}(v)(v-p_1)\alpha_1\le0$ and $\sum (1-b-w)_{\theta,k}(v)(v-p_2)\alpha_2\le0$.
--
--   Each is the paper's conditional inequality multiplied by the probability of the recommendation.
--
--   **Public signaling.** A mechanism is *public* when the index $k$ is a public signal: the recommendations depend on $(k,v)$ only, $b_{H,k}=b_{L,k}$ and $w_{H,k}=w_{L,k}$, and the obedience constraints hold for each realized $k$ separately.
--
--   **Benchmark** (11). $R^*_\phi=P(L)\,\bar p_1\bar F(\bar p_1)+P(H)\,p^m\bar F(p^m)$ with $\bar p_1=\max\{\bar F^{-1}(q_L),p^m\}$.
--
--   **Formalization Note** The paper's game (Definitions 1–2: a continuum of customers, Bayesian Nash equilibria, sender-preferred selection) is replaced by the class its proofs reduce to by the revelation principle (p. 39, footnote 5): obedient straightforward mechanisms with aggregate masses (continuum law of large numbers). The finite latent index carries the correlation between customers' signals, which public signals need; it is a disclosed restriction to finitely many latent signals (every $n$ is allowed). Availability at zero demand is $1$ with stock left and $0$ without, where the paper's ratio is undefined.
-- source:
--   Drakopoulos, Jain, Randhawa, Persuading Customers to Buy Early: The Value of Personalized Information Provisioning, SSRN 3191629 (version of April 17, 2020), pp. 6–8, (1)–(4); p. 32, Definition 3; p. 35, (A.5); pp. 39–40, (Buy-1)–(No); p. 15, (11)

import Mathlib
import Definitions.Def_PersuadeEarly_Private_Valuation

open MeasureTheory Set

namespace PersuadeEarly.Private

/-- Availability under random rationing (pp. 6–7; (A.5), p. 35): the probability that a customer
who requests the product in a period gets it, when `s` units are left in that period and the
other customers' demand in that period has mass `D`. With no stock left (`s ≤ 0`) she gets
nothing; if the demand does not exceed the stock she gets it for sure; otherwise the stock is
shared proportionally, `s / D`.

**Formalization Note** This agrees with the paper's `min{s / D, 1}` and `min{max{·, 0}, 1}` of
(A.5) whenever `D > 0`; at `D = 0` it is `1` if stock is left and `0` otherwise (the paper's
expression is then undefined). -/
noncomputable def avail (s D : ℝ) : ℝ :=
  if s ≤ 0 then 0 else if D ≤ s then 1 else s / D

/-- Period-1 availability with stock `q` and period-1 demand `D1`. -/
noncomputable def alpha1 (q D1 : ℝ) : ℝ := avail q D1

/-- Period-2 availability with stock `q`, period-1 demand `D1` and period-2 demand `D2`: the stock
left after period 1 is `(q - D1)⁺`. -/
noncomputable def alpha2 (q D1 D2 : ℝ) : ℝ := avail (max (q - D1) 0) D2

/-- The firm's (rationed) sales revenue in one inventory state with stock `q`, when masses `D1`
and `D2` of customers request the product in periods 1 and 2: `p1 min{D1, q} + p2 min{D2, (q − D1)⁺}`
— the integrand of (3), p. 7. -/
noncomputable def sales (p1 p2 q D1 D2 : ℝ) : ℝ :=
  p1 * min D1 q + p2 * min D2 (max (q - D1) 0)

/-- A straightforward (Buy/Wait/No) signaling mechanism with posted prices, in the aggregate form
used by the proofs of App. A.2 (pp. 39–40), with a finite latent index `k ∈ Fin n`.

Before the inventory is drawn the firm commits to prices `p1, p2`. In state `H` (resp. `L`) a latent
index `k` is drawn with probability `piH k` (resp. `piL k`); given the state and `k`, each
`v`-customer is independently told *Buy* with probability `buyH k v` (resp. `buyL k v`), *Wait*
with probability `waitH k v` (resp. `waitL k v`), and *No* otherwise.

**Formalization Note** This replaces the continuum game of Definitions 1–2 and App. C by the class
the proofs reduce to (the revelation principle, p. 39 and footnote 5): straightforward mechanisms
whose recommendations are obeyed. The finite latent index carries the correlation between the
customers' signals (it is what makes public signals expressible); it is a disclosed restriction to
finitely many latent signals, for every `n`. -/
structure Mech (M : Model) (n : ℕ) where
  p1 : ℝ
  p2 : ℝ
  piH : Fin n → ℝ
  piL : Fin n → ℝ
  buyH : Fin n → ℝ → ℝ
  buyL : Fin n → ℝ → ℝ
  waitH : Fin n → ℝ → ℝ
  waitL : Fin n → ℝ → ℝ

namespace Mech

variable {M : Model} {n : ℕ} (N : Mech M n)

/-- Well-formedness: nonnegative prices, probability vectors `piH`, `piL`, and measurable
recommendation probabilities with `0 ≤ buy`, `0 ≤ wait`, `buy + wait ≤ 1`. -/
structure Valid : Prop where
  p1_nonneg : 0 ≤ N.p1
  p2_nonneg : 0 ≤ N.p2
  piH_nonneg : ∀ k, 0 ≤ N.piH k
  piL_nonneg : ∀ k, 0 ≤ N.piL k
  piH_sum : ∑ k, N.piH k = 1
  piL_sum : ∑ k, N.piL k = 1
  buyH_meas : ∀ k, Measurable (N.buyH k)
  buyL_meas : ∀ k, Measurable (N.buyL k)
  waitH_meas : ∀ k, Measurable (N.waitH k)
  waitL_meas : ∀ k, Measurable (N.waitL k)
  buyH_nonneg : ∀ k v, 0 ≤ N.buyH k v
  buyL_nonneg : ∀ k v, 0 ≤ N.buyL k v
  waitH_nonneg : ∀ k v, 0 ≤ N.waitH k v
  waitL_nonneg : ∀ k v, 0 ≤ N.waitL k v
  sumH_le_one : ∀ k v, N.buyH k v + N.waitH k v ≤ 1
  sumL_le_one : ∀ k v, N.buyL k v + N.waitL k v ≤ 1

/-- Probability of a *No* recommendation in state `H` with latent index `k`. -/
def noH (k : Fin n) (v : ℝ) : ℝ := 1 - N.buyH k v - N.waitH k v

/-- Probability of a *No* recommendation in state `L` with latent index `k`. -/
def noL (k : Fin n) (v : ℝ) : ℝ := 1 - N.buyL k v - N.waitL k v

/-- Mass of customers told *Buy* in state `H`, index `k` (law of large numbers). -/
noncomputable def D1H (k : Fin n) : ℝ := ∫ v, N.buyH k v ∂M.mu
/-- Mass of customers told *Buy* in state `L`, index `k`. -/
noncomputable def D1L (k : Fin n) : ℝ := ∫ v, N.buyL k v ∂M.mu
/-- Mass of customers told *Wait* in state `H`, index `k`. -/
noncomputable def D2H (k : Fin n) : ℝ := ∫ v, N.waitH k v ∂M.mu
/-- Mass of customers told *Wait* in state `L`, index `k`. -/
noncomputable def D2L (k : Fin n) : ℝ := ∫ v, N.waitL k v ∂M.mu

/-- Period-1 availability in state `H` (stock `qH = 1`), index `k`. -/
noncomputable def a1H (k : Fin n) : ℝ := alpha1 1 (N.D1H k)
/-- Period-2 availability in state `H`, index `k`. -/
noncomputable def a2H (k : Fin n) : ℝ := alpha2 1 (N.D1H k) (N.D2H k)
/-- Period-1 availability in state `L` (stock `qL`), index `k`. -/
noncomputable def a1L (k : Fin n) : ℝ := alpha1 M.qL (N.D1L k)
/-- Period-2 availability in state `L`, index `k`. -/
noncomputable def a2L (k : Fin n) : ℝ := alpha2 M.qL (N.D1L k) (N.D2L k)

/-- The firm's expected revenue (3), p. 7, when every customer obeys: `E[p1 D1 + p2 D2]` where
`D1`, `D2` are the masses of customers who *get* the product (rationed sales). -/
noncomputable def revenue : ℝ :=
  M.pH * ∑ k, N.piH k * sales N.p1 N.p2 1 (N.D1H k) (N.D2H k) +
    M.pL * ∑ k, N.piL k * sales N.p1 N.p2 M.qL (N.D1L k) (N.D2L k)

/-- For a set `S` of latent indices, the sum over both states and `k ∈ S` of
`P(θ) π_θ(k) r_{θ,k}(v) g(α1_{θ,k}, α2_{θ,k})`. With `r` a recommendation probability this is
`P(S_v = r, k ∈ S)` times the conditional expectation of `g(α1, α2)` given the recommendation. -/
noncomputable def wsum (S : Finset (Fin n)) (rH rL : Fin n → ℝ → ℝ) (g : ℝ → ℝ → ℝ) (v : ℝ) : ℝ :=
  ∑ k ∈ S, (M.pH * N.piH k * rH k v * g (N.a1H k) (N.a2H k) +
    M.pL * N.piL k * rL k v * g (N.a1L k) (N.a2L k))

/-- The obedience constraints (Buy-1), (Buy-2), (Wait-1), (Wait-2), (No), p. 40, for `M.mu`-almost
every valuation `v`, conditioning on the event that the latent index lies in `S`. Each constraint
is the printed conditional inequality multiplied by the probability of the recommendation, so it
is never divided by a zero probability. -/
def ObedientOn (S : Finset (Fin n)) : Prop :=
  ∀ᵐ v ∂M.mu,
    0 ≤ N.wsum S N.buyH N.buyL (fun a1 a2 => (v - N.p1) * a1 - (v - N.p2) * a2) v ∧
    0 ≤ N.wsum S N.buyH N.buyL (fun a1 _ => (v - N.p1) * a1) v ∧
    0 ≤ N.wsum S N.waitH N.waitL (fun a1 a2 => (v - N.p2) * a2 - (v - N.p1) * a1) v ∧
    0 ≤ N.wsum S N.waitH N.waitL (fun _ a2 => (v - N.p2) * a2) v ∧
    N.wsum S N.noH N.noL (fun a1 _ => (v - N.p1) * a1) v ≤ 0 ∧
    N.wsum S N.noH N.noL (fun _ a2 => (v - N.p2) * a2) v ≤ 0

/-- The mechanism is obedient: every customer weakly prefers to follow her recommendation
((Buy-1)–(No), p. 40), the latent index being unobserved. -/
def Obedient : Prop := N.ObedientOn Finset.univ

/-- Public signaling (§3.2; Definition 3, p. 32): the latent index `k` is the public signal, seen by
every customer. Recommendations depend on `(k, v)` only, not on the state, and obedience holds
for each realized `k` separately. -/
def IsPublic : Prop :=
  (∀ k, N.buyH k = N.buyL k) ∧ (∀ k, N.waitH k = N.waitL k) ∧ ∀ k, N.ObedientOn {k}

end Mech

/-- The optimal public-signaling revenue (11), p. 15:
`R*_ϕ = P(L) p1 F̄(p1) + P(H) p2 F̄(p2)` with `p1 = max{F̄^{-1}(qL), p^m}` and `p2 = p^m`. -/
noncomputable def Rphi (M : Model) : ℝ :=
  M.pL * max (M.FbarInv M.qL) M.pm * M.Fbar (max (M.FbarInv M.qL) M.pm) + M.pH * M.pm * M.Fbar M.pm

end PersuadeEarly.Private


