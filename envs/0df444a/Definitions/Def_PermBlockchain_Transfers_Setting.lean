-- Prove2me | Definitions.Def_PermBlockchain_Transfers_Setting
-- name    : PermBlockchain_Transfers_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T22:57:42.664991+00:00
-- url     : https://prove2.me/theorems/f9aa83cf-935a-4e8a-8850-7628d6aa97ce
-- title:
--   §3, §4.2, proof of Prop. 4.9 — reduced-form blockchain supply chain with consumer access fee κ and manufacturer transfers τ_i
-- statement:
--   This definition fixes the reduced-form model of Iyengar, Saleh, Sethuraman and Wang in which a consumer access fee finances payments to manufacturers who join a permissioned blockchain.
--
--   **Manufacturers.** There are $4m$ manufacturers. Each has a horizontal type $q_i\in\{A,B\}$ and a vertical type $\xi_i\in\{h,l\}$, and each of the four type classes has exactly $m$ members. Manufacturer $i$ pays an adoption cost $\chi_i>0$ to join the blockchain; $a_i\in\{0,1\}$ records whether it joins.
--
--   **Parameters and standing assumptions.** The model carries a low horizontal match utility $L$, vendor qualities $h$ and $l$, the high-type vendor's marginal cost $\gamma$ (so $c_h(x)=\gamma x$), the adoption costs $\chi_i$, and the law $\mu$ of a consumer's outside option $\phi_k$, with cumulative distribution function $G$. The high horizontal match utility is $H=L+\Delta$, where the degree of horizontal differentiation $\Delta=H-L$ is the parameter that varies and $L$ is held fixed. The standing assumptions are:
--   1. $m\ge 2$, $0\le L$, $h>l\ge 0$ and $\gamma>0$;
--   2. $\chi_i>0$ for every manufacturer $i$;
--   3. $G$ is a continuous distribution supported on $[0,\infty)$: $\mu$ is a probability measure with no atoms, $\mu((-\infty,0))=0$, and every open interval $(a,b)$ with $0\le a<b$ has positive probability.
--
--   **Consumers' access decision.** Under full adoption, the best product utility available to a consumer is
--   $$u^{\mathrm{pay}}(\Delta)=\Delta+L+h-\gamma,\qquad u^{\mathrm{free}}(\Delta)=\frac{\Delta}{2}+L+h-\gamma,$$
--   with and without access to the information on the blockchain. A consumer with outside option $\phi_k$ facing an access fee $\kappa$ compares
--   $$g(1,\phi_k)=\max\{u^{\mathrm{pay}}(\Delta),\phi_k\}-\kappa,\qquad g(0,\phi_k)=\max\{u^{\mathrm{free}}(\Delta),\phi_k\},$$
--   and pays ($b_k=1$) exactly when $g(1,\phi_k)\ge g(0,\phi_k)$. The measure of paying consumers is $\mu_\kappa=\mu(\{\phi_k : g(0,\phi_k)\le g(1,\phi_k)\})$.
--
--   With the fee $\kappa=\sum_{i\in M}\chi_i/G(\phi)$ used in the paper's proof, the difference of the two objectives is
--   $$h(\phi_k;\phi)=\max\{\Delta+L+h-\gamma,\phi_k\}-\frac{\sum_{i\in M}\chi_i}{G(\phi)}-\max\Big\{\frac{\Delta}{2}+L+h-\gamma,\phi_k\Big\}.$$
--
--   **Manufacturers' adoption game with transfers.** Given transfers $\tau_i$, manufacturer $i$'s payoff in the profile $a$ is
--   $$\Pi(a_i,a_{-i})-\chi_i a_i+\tau_i a_i,$$
--   where the gross profit $\Pi$ is zero in every profile because of price competition. An equilibrium is a profile from which no manufacturer gains by switching its own $a_i$.
--
--   **Overcoming adoption failures.** A system of transfers $(\kappa,\{\tau_i\}_{i\in M})$ overcomes adoption failures when $\tau_i\ge 0$ for every $i$, it is self-financing,
--   $$\kappa\cdot\mu_\kappa=\sum_{i\in M}\tau_i,$$
--   with $\mu_\kappa$ the measure of paying consumers defined above, and full adoption ($a_i=1$ for all $i$) is an equilibrium of the adoption game.
--
--   These objects are shared by Proposition 4.9 and Lemma B.1 of the paper.
--
--   **Formalization Note** The paper's full model is a signal game whose equilibrium concept is never defined; its proofs work with the closed-form outcome of Proposition A.1. This file formalizes that reduced form: the consumer utilities are those computed in the proof of Proposition 4.9 (pp. 36–37), gross profit is the constant $0$ (pp. 37–38, both when adopting and when deviating), and equilibrium is a pure Nash equilibrium over unilateral switches of $a_i$. Signal accuracy is $\alpha=1/2$ as in the paper's main text. Manufacturers are indexed by $\mathrm{Fin}\,2\times\mathrm{Bool}\times\mathrm{Fin}\,m$ (horizontal type, vertical type high $=$ true, copy index), and $\Delta$ is an argument of each object rather than a model field. Ties in the access decision are resolved towards paying, as the proof's "if and only if $h\ge 0$". Lean's division returns $0$ when $G(\phi)=0$; no stated result relies on that value.
-- source:
--   Iyengar, Saleh, Sethuraman, Wang, Economics of Permissioned Blockchain Adoption, SSRN 3602376 (version of 2022-08-19), pp. 8–13 (§3.1–3.2, (1)–(2), (8)), pp. 20–21 ((14)–(16) and the definition of overcoming adoption failures), pp. 36–38 (proof of Proposition 4.9), p. 38 (Lemma B.1)

import Mathlib

namespace PermBlockchain.Transfers

open MeasureTheory ProbabilityTheory

/-- The 4m manufacturers (§3.1, p. 8): horizontal type A/B as `Fin 2`, vertical type
high (`true`) / low (`false`), and a copy index in `Fin m`, so that each of the four
types `{A, B} × {h, l}` has exactly `m` members. -/
abbrev Mfr (m : ℕ) : Type := Fin 2 × Bool × Fin m

/-- Parameters of the model (§3, pp. 8–13): the low horizontal match utility `L`
(the high one is `H = L + Δ`, with `Δ` passed separately), vendor qualities `h`, `l`,
the high-type vendor's marginal cost `γ` (`c_h(x) = γ x`, p. 28), the law `μ` of the
consumers' outside option `φ_k`, and the adoption costs `χ_i`. -/
structure Model (m : ℕ) where
  L : ℝ
  h : ℝ
  l : ℝ
  γ : ℝ
  μ : Measure ℝ
  χ : Mfr m → ℝ

namespace Model

variable {m : ℕ} (M : Model m)

/-- Standing assumptions of §3 and App. A: `m ≥ 2`, `0 ≤ L`, `h > l ≥ 0`, `γ > 0`,
`χ_i > 0`, and `φ_k` follows a continuous distribution `G` supported on `[0, ∞)`
(a probability measure without atoms, giving no mass to `(-∞, 0)` and positive mass
to every open interval inside `[0, ∞)`). -/
def Standing : Prop :=
  2 ≤ m ∧ 0 ≤ M.L ∧ 0 ≤ M.l ∧ M.l < M.h ∧ 0 < M.γ ∧ (∀ i, 0 < M.χ i) ∧
    IsProbabilityMeasure M.μ ∧ NullSingletonClass M.μ ∧ M.μ (Set.Iio 0) = 0 ∧
    ∀ a b : ℝ, 0 ≤ a → a < b → 0 < M.μ (Set.Ioo a b)

/-- The cumulative distribution function `G` of the outside option. -/
noncomputable def G (x : ℝ) : ℝ := ProbabilityTheory.cdf M.μ x

/-- Best available product utility under full adoption for a consumer with access to
the blockchain: `H + h − γ = Δ + L + h − γ` (proof of Prop. 4.9, p. 36). -/
def uPay (Δ : ℝ) : ℝ := Δ + M.L + M.h - M.γ

/-- Best available product utility under full adoption for a consumer without access:
`(H + L)/2 + h − γ = Δ/2 + L + h − γ` (proof of Prop. 4.9, p. 37). -/
noncomputable def uFree (Δ : ℝ) : ℝ := Δ / 2 + M.L + M.h - M.γ

/-- Consumer's objective (16) when paying the access fee `κ` (`b_k = 1`). -/
def gPay (Δ κ φk : ℝ) : ℝ := max (M.uPay Δ) φk - κ

/-- Consumer's objective (16) when not paying (`b_k = 0`). -/
noncomputable def gFree (Δ φk : ℝ) : ℝ := max (M.uFree Δ) φk

/-- Outside-option values of the consumers who pay the fee `κ`: `b_k = 1` iff
`g(1) ≥ g(0)` (ties resolved towards paying, p. 37). -/
noncomputable def payers (Δ κ : ℝ) : Set ℝ := {φk | M.gFree Δ φk ≤ M.gPay Δ κ φk}

/-- `µ_κ`: the measure of consumers paying the fee `κ` (p. 21, `µ_κ = µ({k : b_k = 1})`),
computed from the law of the outside option. -/
noncomputable def μκ (Δ κ : ℝ) : ℝ := M.μ.real (M.payers Δ κ)

/-- The function `h(φ_k; φ) = g(1, φ_k; φ) − g(0, φ_k; φ)` of Lemma B.1 (p. 38), with
the fee `κ = Σ_i χ_i / G(φ)`. -/
noncomputable def hfun (Δ φk φ : ℝ) : ℝ :=
  max (M.uPay Δ) φk - (∑ i, M.χ i) / M.G φ - max (M.uFree Δ) φk

/-- The full-adoption profile `a_i = 1` for all `i`. -/
def fullAdopt : Mfr m → Bool := fun _ => true

/-- Manufacturer gross profit `Π(a_i, a_{−i})`: zero in every adoption profile, by price
competition (proof of Prop. 4.9, pp. 37–38, both when adopting and when deviating). -/
def grossProfit (_a : Mfr m → Bool) (_i : Mfr m) : ℝ := 0

/-- Manufacturer `i`'s objective (15): `Π(a_i, a_{−i}) − χ_i a_i + τ_i a_i`. -/
def payoffT (τ : Mfr m → ℝ) (a : Mfr m → Bool) (i : Mfr m) : ℝ :=
  grossProfit a i - (if a i then M.χ i else 0) + (if a i then τ i else 0)

/-- Pure Nash equilibrium of the adoption game (15): no manufacturer gains from a
unilateral switch of `a_i ∈ {0, 1}`. -/
def IsEquilibriumT (τ : Mfr m → ℝ) (a : Mfr m → Bool) : Prop :=
  ∀ (i : Mfr m) (b : Bool), M.payoffT τ (Function.update a i b) i ≤ M.payoffT τ a i

/-- A system of transfers `(κ, {τ_i})` overcomes adoption failures (p. 21): `τ_i ≥ 0`,
it is self-financing (14) with `µ_κ` the measure of paying consumers, and full adoption
is an equilibrium of (15). -/
def Overcomes (Δ κ : ℝ) (τ : Mfr m → ℝ) : Prop :=
  (∀ i, 0 ≤ τ i) ∧ κ * M.μκ Δ κ = ∑ i, τ i ∧ M.IsEquilibriumT τ fullAdopt

end Model

end PermBlockchain.Transfers


