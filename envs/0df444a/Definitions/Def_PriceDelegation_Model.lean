-- Prove2me | Definitions.Def_PriceDelegation_Model
-- name    : PriceDelegation_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T07:49:42.875863+00:00
-- url     : https://prove2.me/theorems/3d7f4927-1111-43f5-b06a-25a7e0ebef4e
-- title:
--   Fluid multiple-customer model: policies, $I$, Rev, $C$, $P$, (IC-multi), first best, the dual (9), the policies of Proposition 4, the contracts $t^M_{\lambda,\mu}$
-- statement:
--   This file fixes the fluid model of §4 for $N$ customers and $K$ units of inventory, with $\rho=K/N$.
--
--   **Contracts.** A static contract $t\in\mathcal T$ is non-decreasing on $[0,\infty)$, nonnegative, has $t(0)=0$ and $E[t(V)]<\infty$; the separable contract $T=\{t\}$ pays $\sum_i t(Y_i)$ for sale revenues $Y_1,\dots,Y_N$.
--
--   **Policies.** A policy $\pi=(q_i,\theta_i(\cdot),\varphi_i)_{i=1}^N$ gives each customer a learning probability $q_i\in[0,1]$, a measurable informed price policy $\theta_i$ and an uninformed price $\varphi_i$, prices lying in $[0,\infty]$ (the price $\infty$ never sells). With $\bar F(\infty)=0$,
--   $$
--   \begin{aligned}
--   I(\pi)&=\sum_i q_i\,E[1\{V\ge\theta_i(V)\}]+(1-q_i)\bar F(\varphi_i),\\
--   \mathrm{Rev}(\pi)&=\sum_i q_i\,E[\theta_i(V)1\{V\ge\theta_i(V)\}]+(1-q_i)\varphi_i\bar F(\varphi_i),\\
--   C(\pi)&=\sum_i q_i\psi,\\
--   P(\pi,T)&=\sum_i q_i\,E[t(\theta_i(V))1\{V\ge\theta_i(V)\}]+(1-q_i)t(\varphi_i)\bar F(\varphi_i),
--   \end{aligned}
--   $$
--   and $U(\pi,T)=P(\pi,T)-C(\pi)$. A policy is inventory feasible when $I(\pi)\le K$. It is a best response to $T$ (IC-multi) when it is feasible and maximizes $U(\cdot,T)$ over all feasible policies, and it satisfies (participation-multi) when $U(\pi,T)\ge0$.
--
--   **First best.** $J^{FB-MC}=\sup\{\mathrm{Rev}(\pi)-C(\pi): I(\pi)\le K\}$. For a multiplier $\lambda$, the Lagrangian objective (7) is
--   $$\sum_i q_i\big(E[(\theta_i(V)-\lambda)1\{V\ge\theta_i(V)\}]-\psi\big)+(1-q_i)(\varphi_i-\lambda)\bar F(\varphi_i)+K\lambda,$$
--   and with $A(\lambda)=E[(V-\lambda)^+]-\psi$ and $B(\lambda)=\sup_{\varphi>0}(\varphi-\lambda)\bar F(\varphi)$ one sets
--   $$J_\lambda=N\max\{A(\lambda),B(\lambda)\}+K\lambda,\quad f(\lambda)=NA(\lambda)+K\lambda,\quad g(\lambda)=NB(\lambda)+K\lambda,\quad \Delta(\lambda)=NA(\lambda)-NB(\lambda).$$
--   $\varphi^*(\lambda)$ denotes a maximizer of $(\varphi-\lambda)\bar F(\varphi)$ over $\varphi>0$, and the informed policy with reservation price $\lambda$ is $\theta(V)=V\cdot1\{V\ge\lambda\}+\infty\cdot1\{V<\lambda\}$.
--
--   **First-best policies (Proposition 4).** With $\lambda^{p-l}\ge0$ a zero of $\Delta$ and $\varphi^{p-l}=\varphi^*(\lambda^{p-l})$, a policy is first best when it is one of:
--
--   1. $\pi^{n-l}$ if $\rho\le\bar F(\varphi^{p-l})$: $q_i=0$, $\varphi_i=\varphi^*(\lambda^{n-l})$ for a minimizer $\lambda^{n-l}\ge0$ of $g$;
--   2. $\pi^{p-l}$ if $\bar F(\varphi^{p-l})\le\rho\le\bar F(\lambda^{p-l})$: $q_i=\eta$ with $\eta\bar F(\lambda^{p-l})+(1-\eta)\bar F(\varphi^{p-l})=\rho$, reservation price $\lambda^{p-l}$, $\varphi_i=\varphi^{p-l}$;
--   3. $\pi^{f-l}$ if $\rho\ge\bar F(\lambda^{p-l})$: $q_i=1$, reservation price $\lambda^{f-l}$, the minimizer over $\lambda\ge0$ of $f$.
--
--   The coordinates the paper calls arbitrary ($\theta_i$ when $q_i=0$, $\varphi_i$ when $q_i=1$) are free.
--
--   **Contracts with reservation.** For $M>0$ and $\mu\ge\lambda$,
--   $$t^M_{\lambda,\mu}(p)=\begin{cases}0,&p\le\lambda,\\ \min\{M\bar F(\mu)/\bar F(p),\,M\},&p>\lambda.\end{cases}$$
--   A contract solves the single-customer problem with reservation when it maximizes $E[V-t(V)]$ among non-decreasing $t$ with $E[t(V)]<\infty$ subject to (participation) $E[t(V)]\ge\psi$, (IC) $E[t(V)]-\psi\ge t(\varphi)\bar F(\varphi)+t(0)F(\varphi)$ for every $\varphi>0$, (limited liability) $t\ge0$, (M-bounded) $t\le M$, and (reservation) $t(p)=0$ for $p\le\lambda$.
--
--   **Formalization Note** Prices are elements of $[0,\infty]$; $\infty$ is the no-sale price and every price is multiplied by its own sale indicator or sale probability, so the value assigned to $\infty$ as a real number never matters. The suprema $J^{FB-MC}$ and $B(\lambda)$ are real suprema, shown attained in the theorems of the mission. $\lambda^{n-l}$ is any minimizer, because the printed uniqueness fails for a discontinuous failure rate. $t^M_{\lambda,\mu}$ takes the value $0$ at $p=\lambda$, as (reservation) and the proof of Lemma 6 require, where (10) prints $M\bar F(\mu)/\bar F(\lambda)$.
-- source:
--   Atasu–Ciocan–Désir, Price Delegation with Learning Agents, SSRN 3931055 (version of Sept. 22, 2021), §4.1–§4.2, pp.20–22; (6)–(9), pp.23–25; Lemma 4, p.25; Proposition 4 and the policies, pp.26–27; §4.4 and (10), pp.28–30; proof of Lemma 6, p.ec10

import Mathlib
import Definitions.Def_PriceDelegation_Valuation

open MeasureTheory Set
open scoped ENNReal

namespace PriceDelegation

/-- The inventory scarcity ratio `ρ = K/N` (Atasu–Ciocan–Désir, Price Delegation with Learning
Agents, SSRN 3931055 (version of Sept. 22, 2021), p.24). -/
noncomputable def ratio (N K : ℕ) : ℝ := (K : ℝ) / N

/-- A static single-customer contract `t ∈ 𝒯` (SSRN 3931055, p.9 and p.28): `t` is non-decreasing on
`[0, ∞)`, `t ≥ 0` (limited liability), `t(0) = 0` (no payment without a sale) and `E[t(V)] < ∞`.
The separable multiple-customer contract `T = {t}` pays `T(Y₁, …, Y_N) = Σᵢ t(Yᵢ)` (p.28).

**Formalization Note** `t` is a function `ℝ → ℝ` read on sale revenues `p ≥ 0`; its values on
negative reals are never used. -/
def IsStaticContract (V : Valuation) (t : ℝ → ℝ) : Prop :=
  MonotoneOn t (Ici 0) ∧ (∀ p, 0 ≤ p → 0 ≤ t p) ∧ t 0 = 0 ∧
    IntegrableOn (fun v => t v * V.f v) (Ioi 0)

/-- A fluid agent policy `π = (qᵢ, θᵢ(·), φᵢ)_{i=1}^N` (SSRN 3931055, §4.1, p.21): for each customer
`i`, a learning probability `qᵢ`, an informed price policy `θᵢ(·)` used after learning the value, and
an uninformed price `φᵢ`.

**Formalization Note** Customers are indexed by `Fin N`. Prices are in `[0, ∞]` (`ℝ≥0∞`), with `⊤`
the price `∞` at which no sale happens (p.9, footnote 4). -/
structure Policy (N : ℕ) where
  /-- The learning probability `qᵢ`. -/
  q : Fin N → ℝ
  /-- The informed price policy `θᵢ(·)`, a function of the learned value. -/
  θ : Fin N → ℝ → ℝ≥0∞
  /-- The uninformed price `φᵢ`. -/
  φ : Fin N → ℝ≥0∞

/-- The sale indicator `1{v ≥ p}` for a price `p ∈ [0, ∞]` (SSRN 3931055, p.9). It is `0` at `p = ∞`. -/
noncomputable def saleInd (p : ℝ≥0∞) (v : ℝ) : ℝ := if p ≤ ENNReal.ofReal v then 1 else 0

/-- The sale probability `F̄(φ)` of a constant price `φ ∈ [0, ∞]`, with `F̄(∞) = 0` (SSRN 3931055,
p.9). -/
noncomputable def Fext (V : Valuation) (p : ℝ≥0∞) : ℝ := if p = ⊤ then 0 else Fbar V p.toReal

/-- The policy set `Π` (SSRN 3931055, p.21): `qᵢ ∈ [0, 1]`; the informed price policies are
measurable.

**Formalization Note** Prices range over `[0, ∞]` rather than `(0, ∞)` (p.21) or `[0, ∞)` ((6),
p.23). Measurability of `θᵢ` makes `E[1{Vᵢ ≥ θᵢ(Vᵢ)}]` meaningful. -/
def InPi {N : ℕ} (π : Policy N) : Prop :=
  ∀ i, π.q i ∈ Icc (0 : ℝ) 1 ∧ Measurable (π.θ i)

/-- The expected inventory consumption (SSRN 3931055, p.22):
`I(π) = Σᵢ qᵢ · E[1{Vᵢ ≥ θᵢ(Vᵢ)}] + (1 − qᵢ) · F̄(φᵢ)`. -/
noncomputable def invUse (V : Valuation) {N : ℕ} (π : Policy N) : ℝ :=
  ∑ i, (π.q i * expect V (fun v => saleInd (π.θ i v) v) + (1 - π.q i) * Fext V (π.φ i))

/-- The firm's expected revenue (SSRN 3931055, p.22):
`Rev(π) = Σᵢ qᵢ · E[θᵢ(Vᵢ) · 1{Vᵢ ≥ θᵢ(Vᵢ)}] + Σᵢ (1 − qᵢ) · φᵢ · F̄(φᵢ)`.

**Formalization Note** `ENNReal.toReal ⊤ = 0` never matters: each price is multiplied by its own
sale indicator or sale probability, which is `0` at the price `∞`. -/
noncomputable def Rev (V : Valuation) {N : ℕ} (π : Policy N) : ℝ :=
  ∑ i, (π.q i * expect V (fun v => (π.θ i v).toReal * saleInd (π.θ i v) v) +
    (1 - π.q i) * ((π.φ i).toReal * Fext V (π.φ i)))

/-- The expected learning cost `C(π) = Σᵢ qᵢ · ψ` (SSRN 3931055, p.22). -/
noncomputable def cost (ψ : ℝ) {N : ℕ} (π : Policy N) : ℝ := ∑ i, π.q i * ψ

/-- The expected payment `P(π, T) = E[T]` of the separable contract `T = {t}` under the policy `π`
(SSRN 3931055, p.30):
`P(π, T) = Σᵢ qᵢ · E[t(θᵢ(Vᵢ)) · 1{Vᵢ ≥ θᵢ(Vᵢ)}] + (1 − qᵢ) · t(φᵢ) · F̄(φᵢ)`. -/
noncomputable def pay (V : Valuation) {N : ℕ} (π : Policy N) (t : ℝ → ℝ) : ℝ :=
  ∑ i, (π.q i * expect V (fun v => t (π.θ i v).toReal * saleInd (π.θ i v) v) +
    (1 - π.q i) * (t (π.φ i).toReal * Fext V (π.φ i)))

/-- The agent's expected utility `U(π, T) = T − C(π)` under the separable contract `T = {t}`
(SSRN 3931055, p.22), i.e. `P(π, T) − C(π)`. -/
noncomputable def util (V : Valuation) (ψ : ℝ) {N : ℕ} (π : Policy N) (t : ℝ → ℝ) : ℝ :=
  pay V π t - cost ψ π

/-- An inventory-feasible policy: `π ∈ Π` and (inventory) `I(π) ≤ K` (SSRN 3931055, p.22). -/
def Feasible (V : Valuation) (K : ℕ) {N : ℕ} (π : Policy N) : Prop :=
  InPi π ∧ invUse V π ≤ K

/-- (IC-multi), SSRN 3931055, p.22: `π` is a best response to the separable contract `T = {t}`,
i.e. `π ∈ argmax_{π' ∈ Π} {U(π', T) : π' satisfies (inventory)}`. -/
def IsBestResponse (V : Valuation) (ψ : ℝ) (K : ℕ) {N : ℕ} (π : Policy N) (t : ℝ → ℝ) : Prop :=
  Feasible V K π ∧ ∀ π' : Policy N, Feasible V K π' → util V ψ π' t ≤ util V ψ π t

/-- (participation-multi), SSRN 3931055, p.22: `E[T − C(π)] ≥ 0`. -/
def Participates (V : Valuation) (ψ : ℝ) {N : ℕ} (π : Policy N) (t : ℝ → ℝ) : Prop :=
  0 ≤ util V ψ π t

/-- The first-best payoff `J^{FB−MC}` (SSRN 3931055, p.23): the supremum of `Rev(π) − C(π)` over
the inventory-feasible policies, the expected payment `E[T]` having been replaced by `C(π)` through
(participation-multi) as on p.23.

**Formalization Note** A real `sSup`; it is attained (`proposition_4`). The constraint is the
(inventory) inequality `I(π) ≤ K` of the definition on p.23; (6) writes `= K` after a
"without loss of generality", and `proposition_4` shows the optimum has `I = K`. -/
noncomputable def firstBestValue (V : Valuation) (ψ : ℝ) (N K : ℕ) : ℝ :=
  sSup {x | ∃ π : Policy N, Feasible V K π ∧ x = Rev V π - cost ψ π}

/-- The objective of the Lagrangian relaxation (7) (SSRN 3931055, p.24), for a multiplier `λ`:
`Σᵢ qᵢ · (E[(θᵢ(Vᵢ) − λ) · 1{Vᵢ ≥ θᵢ(Vᵢ)}] − ψ) + (1 − qᵢ) · (φᵢ − λ) · F̄(φᵢ) + K · λ`. -/
noncomputable def lagObj (V : Valuation) (ψ : ℝ) (K : ℕ) (lam : ℝ) {N : ℕ} (π : Policy N) : ℝ :=
  (∑ i, (π.q i * (expect V (fun v => ((π.θ i v).toReal - lam) * saleInd (π.θ i v) v) - ψ) +
    (1 - π.q i) * (((π.φ i).toReal - lam) * Fext V (π.φ i)))) + K * lam

/-- The learning branch of (9), `E[(V − λ)⁺] − ψ` (SSRN 3931055, p.25). -/
noncomputable def Aterm (V : Valuation) (ψ lam : ℝ) : ℝ :=
  expect V (fun v => max (v - lam) 0) - ψ

/-- The no-learning branch of (9), `max_{φ>0} {(φ − λ) · F̄(φ)}` (SSRN 3931055, p.25).

**Formalization Note** A real `sSup` over `φ ∈ (0, ∞)`; for `λ ≥ 0` the set is bounded above by
`E[V]` and the supremum is attained (`uninformed_price`, `eq_9`). -/
noncomputable def Bterm (V : Valuation) (lam : ℝ) : ℝ :=
  sSup ((fun φ => (φ - lam) * Fbar V φ) '' Ioi 0)

/-- The dual function (9) (SSRN 3931055, p.25):
`J_λ = N · max{E[(V − λ)⁺] − ψ, max_{φ>0} (φ − λ) F̄(φ)} + K · λ`. -/
noncomputable def Jdual (V : Valuation) (ψ : ℝ) (N K : ℕ) (lam : ℝ) : ℝ :=
  N * max (Aterm V ψ lam) (Bterm V lam) + K * lam

/-- The full-learning function `N · (E[(V − λ)⁺] − ψ) + K · λ` whose minimizer is `λ^{f-l}`
(SSRN 3931055, p.25; `f(λ)` in the proof of Lemma 5, p.ec8). -/
noncomputable def Fl (V : Valuation) (ψ : ℝ) (N K : ℕ) (lam : ℝ) : ℝ :=
  N * Aterm V ψ lam + K * lam

/-- The no-learning function `N · max_{φ>0} (φ − λ) F̄(φ) + K · λ` whose minimizer is `λ^{n-l}`
(SSRN 3931055, p.25; `g(λ)` in the proof of Lemma 5, p.ec8). -/
noncomputable def Gl (V : Valuation) (N K : ℕ) (lam : ℝ) : ℝ :=
  N * Bterm V lam + K * lam

/-- `∆(λ) = N · (E[(V − λ)⁺] − ψ) − N · max_{φ>0} (φ − λ) F̄(φ)` (SSRN 3931055, Lemma 4, p.25). -/
noncomputable def Delta (V : Valuation) (ψ : ℝ) (N : ℕ) (lam : ℝ) : ℝ :=
  N * Aterm V ψ lam - N * Bterm V lam

/-- `φ` is the uninformed price `φ*(λ)`, a maximizer over `φ > 0` of `(φ − λ) · F̄(φ)`
(SSRN 3931055, p.25). -/
def IsUninf (V : Valuation) (lam φ : ℝ) : Prop :=
  0 < φ ∧ IsMaxOn (fun x => (x - lam) * Fbar V x) (Ioi 0) φ

/-- The informed price policy with reservation price `λ` (SSRN 3931055, p.24):
`θ(V) = V · 1{V ≥ λ} + ∞ · 1{V < λ}`. -/
noncomputable def reserve (lam : ℝ) : ℝ → ℝ≥0∞ :=
  fun v => if lam ≤ v then ENNReal.ofReal v else ⊤

/-- `π` is one of the three first-best policies of Proposition 4 (SSRN 3931055, pp.26–27), in its
regime of `ρ = K/N`. Here `λ^{p-l} ≥ 0` is the zero of `∆` (Lemma 4) and `φ^{p-l} = φ*(λ^{p-l})`.
1. no learning, `ρ ≤ F̄(φ*(λ^{p-l}))`: `π^{n-l} = (0, θᵢ(·), φ*(λ^{n-l}))`, with `λ^{n-l}` a
   minimizer over `λ ≥ 0` of `N · max_{φ>0}(φ − λ)F̄(φ) + K λ`;
2. partial learning, `F̄(φ*(λ^{p-l})) ≤ ρ ≤ F̄(λ^{p-l})`:
   `π^{p-l} = (η, V·1{V ≥ λ^{p-l}} + ∞·1{V < λ^{p-l}}, φ*(λ^{p-l}))` with
   `η F̄(λ^{p-l}) + (1 − η) F̄(φ*(λ^{p-l})) = ρ`;
3. full learning, `ρ ≥ F̄(λ^{p-l})`: `π^{f-l} = (1, V·1{V ≥ λ^{f-l}} + ∞·1{V < λ^{f-l}}, φᵢ)`, with
   `λ^{f-l}` the minimizer over `λ ≥ 0` of `N · (E[(V − λ)⁺] − ψ) + K λ`.

**Formalization Note** The coordinates the paper calls arbitrary (`θᵢ` when `qᵢ = 0`, `φᵢ` when
`qᵢ = 1`, p.26) are unconstrained beyond `π ∈ Π`. `λ^{n-l}` is any minimizer, since the printed
uniqueness fails for a discontinuous hazard rate. -/
def IsFirstBestPolicy (V : Valuation) (ψ : ℝ) (N K : ℕ) (π : Policy N) : Prop :=
  InPi π ∧ ∃ lp φp : ℝ, 0 ≤ lp ∧ Delta V ψ N lp = 0 ∧ IsUninf V lp φp ∧
    ((ratio N K ≤ Fbar V φp ∧
        ∃ ln φn : ℝ, 0 ≤ ln ∧ IsMinOn (Gl V N K) (Ici 0) ln ∧ IsUninf V ln φn ∧
          ∀ i, π.q i = 0 ∧ π.φ i = ENNReal.ofReal φn) ∨
      (Fbar V φp ≤ ratio N K ∧ ratio N K ≤ Fbar V lp ∧
        ∃ η : ℝ, η ∈ Icc (0 : ℝ) 1 ∧ η * Fbar V lp + (1 - η) * Fbar V φp = ratio N K ∧
          ∀ i, π.q i = η ∧ π.θ i = reserve lp ∧ π.φ i = ENNReal.ofReal φp) ∨
      (Fbar V lp ≤ ratio N K ∧
        ∃ lf : ℝ, 0 ≤ lf ∧ IsMinOn (Fl V ψ N K) (Ici 0) lf ∧
          ∀ i, π.q i = 1 ∧ π.θ i = reserve lf))

/-- The bounded contract with reservation price `t^M_{λ,µ}` (SSRN 3931055, (10), p.29, and the proof
of Lemma 6, p.ec10): `t(p) = 0` for `p ≤ λ`, and `t(p) = min{M · F̄(µ)/F̄(p), M}` otherwise, which is
`M · F̄(µ)/F̄(p)` for `λ < p ≤ µ` and `M` for `p > µ`.

**Formalization Note** The value at `p = λ` is `0`, as in the proof of Lemma 6 (p.ec10) and as
(reservation) requires; (10) prints `M · F̄(µ)/F̄(λ)` there. In particular `t(0) = 0` (pp.13, 28). -/
noncomputable def tRes (V : Valuation) (M lam μ : ℝ) (p : ℝ) : ℝ :=
  if p ≤ lam then 0 else min (M * Fbar V μ / Fbar V p) M

/-- The constraints of the single-customer problem with reservation price `λ` and bound `M`
(SSRN 3931055, Lemma 6, p.29; (IC), (participation), (limited liability) p.10, (M-bounded) p.14,
(reservation) p.29), for a contract `t ∈ 𝒯` (non-decreasing, `E[t(V)] < ∞`, p.9):
1. (participation) `E[t(V)] − ψ ≥ 0`;
2. (IC) `E[t(V)] − ψ ≥ t(φ) · F̄(φ) + t(0) · F(φ)` for every `φ > 0`;
3. (limited liability) `t(p) ≥ 0`;
4. (M-bounded) `t(p) ≤ M`;
5. (reservation) `t(p) = 0` for `p ≤ λ`.

**Formalization Note** The maximum over `φ > 0` in (IC) is a bound at every `φ > 0`. All
constraints are read on prices `p ≥ 0`. -/
def IsResContract (V : Valuation) (ψ M lam : ℝ) (t : ℝ → ℝ) : Prop :=
  MonotoneOn t (Ici 0) ∧ IntegrableOn (fun v => t v * V.f v) (Ioi 0) ∧
    ψ ≤ expect V t ∧
    (∀ φ, 0 < φ → t φ * Fbar V φ + t 0 * Fcdf V φ ≤ expect V t - ψ) ∧
    (∀ p, 0 ≤ p → 0 ≤ t p) ∧ (∀ p, 0 ≤ p → t p ≤ M) ∧
    (∀ p, 0 ≤ p → p ≤ lam → t p = 0)

/-- `t` solves the single-customer problem with reservation (SSRN 3931055, Lemma 6, p.29):
`max_{t ∈ 𝒯} {E[V − t(V)] : t satisfies (participation), (IC), (limited liability), (M-bounded),
(reservation)}`. -/
def SolvesRes (V : Valuation) (ψ M lam : ℝ) (t : ℝ → ℝ) : Prop :=
  IsResContract V ψ M lam t ∧
    ∀ t', IsResContract V ψ M lam t' → expect V (fun v => v - t' v) ≤ expect V (fun v => v - t v)

end PriceDelegation


