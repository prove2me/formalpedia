-- Prove2me | Definitions.Def_ConfoundPromo_LongRun_Model
-- name    : ConfoundPromo_LongRun_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:27:44.415457+00:00
-- url     : https://prove2.me/theorems/cf4018e7-0336-4b51-a50e-b6426358466e
-- title:
--   §2–§4, pp. 8–19 — platform–seller game: demand (1), surplus (2), signals, promotion and pricing policies, Bayes beliefs, payoff (3), Definitions 1–4, W^C (10), W^max, co, (30)
-- statement:
--   This file sets up the dynamic platform–seller game of Gur, Macnamara, Morgenstern and Saban.
--
--   **Market.** A fraction $\phi\in\{\phi_L,\phi_H\}$ of consumers is impatient, with $0<\phi_L<\phi_H<1$. The seller sets prices in a compact interval $\mathcal P=[\underline p,\overline p]$ containing $0$. A patient consumer buys with probability $\bar\rho_c(p)$; an impatient one buys with probability $\bar\rho_0(p)$ if the seller is promoted and $0$ otherwise (equation (1)). Consumer surplus is $\bar W_c(p)$ for a patient consumer, $\bar W_0(p)$ for a promoted impatient one, and $\bar W_{\mathrm{out}}$ for an unpromoted impatient one (equation (2)). The standing assumptions are Assumption 1 ($\bar\rho_c,\bar\rho_0$ decreasing and Lipschitz on $\mathcal P$, $p\bar\rho_c(p)$ and $p\bar\rho_0(p)$ strictly concave, $\bar\rho_0\ge\bar\rho_c$) and Assumption 2 ($\bar W_c,\bar W_0$ decreasing and Lipschitz). With promotion probability $a$, the sale probability and the expected surplus in state $\phi$ are
--   $$
--   \phi\,a\,\bar\rho_0(p)+(1-\phi)\bar\rho_c(p),\qquad \phi\big(\bar W_{\mathrm{out}}+a(\bar W_0(p)-\bar W_{\mathrm{out}})\big)+(1-\phi)\bar W_c(p).
--   $$
--
--   **Strategies and beliefs.** A signaling mechanism $\sigma$ draws a signal $s$ from a finite set given $\phi$. A history $\bar h_t=\langle s,(p_{t'},y_{t'})_{t'<t}\rangle$ records the signal and past prices and sales. A promotion policy gives the probability $\alpha_t(p,\phi,\bar h_t)\in[0,1]$ of promoting the seller; a (deterministic) pricing policy gives the price $\pi_t(\bar h_t)$. The seller's belief $\mu_t$ that $\phi=\phi_H$ is updated by Bayes' rule, starting from the prior $\mu_0$, first on the signal and then on each observed (price, sale) pair. The platform's payoff (3) is $W_T^{\alpha,\sigma,\pi}(\mu_0)=\mathbb E\big(\sum_{t=1}^T W(p_t,a_t,\psi_t)\big)$, here written as a finite sum over $\phi$, the signal and the sale outcomes.
--
--   **Policy classes.** A pricing policy is *myopic* (Definition 1) if at every history it chooses a price in $\mathcal P$ maximizing the current expected revenue under the current belief and promotion rule, and among the maximizers one maximizing the current expected consumer surplus. A promotion policy is *belief-based* (Definition 2) if it depends on the history only through the belief, *single-price* (Definition 3) if after each history at most one price is promoted with positive probability, and *confounding* (Definition 4) if the seller's belief stays at its post-signal value $\mu_1$ throughout the horizon.
--
--   **Value functions.** $W^C(\mu)$ is (10) for one period: the supremum of the current expected surplus over promotion rules and myopic responses that leave the belief $\mu$ unchanged after either sale outcome. $W^{\max}(\mu)$ is the same supremum without the confounding requirement. The concavification is
--   $$
--   co(f)(\mu)=\sup\{z:(\mu,z)\in\operatorname{Conv}\{(x,t):x\in[0,1],\ t\le f(x)\}\}.
--   $$
--   The file also defines the period surplus, the event $\mu_t\in M^{\alpha_t}(\epsilon)$ that it exceeds $co(W^C)(\mu_t)+\epsilon$, and the belief $\mu_{t_n}$ at the index $t_n$ of (30).
--
--   These objects are shared by every statement of the mission.
--
--   **Formalization Note.** Periods $1,\dots,T$ are `Fin T`, so Lean period $t$ is the paper's period $t+1$, and the belief at a history of length $t$ is $\mu_{t+1}$. The state is `Bool` (`true` is $\phi_H$); signal sets are `Fin n`; pricing is deterministic. "Decreasing" is read as weakly decreasing. Added to the standing assumptions: $0\le\bar\rho_c$ and $\bar\rho_0\le 1$ on $\mathcal P$, since (1) defines them as probabilities. Bayes' rule keeps the previous belief when the observation has probability $0$; such histories carry no weight. Definitions 1–3 quantify over histories whose prices lie in $\mathcal P$, as in the paper's $\bar H_t$. In Definition 1 the surplus used to break ties is taken under the seller's belief. $W^C$, $W^{\max}$ and $co$ are real suprema: they equal $0$ on an empty or unbounded set. Under the standing assumptions the defining sets of $W^{\max}$ and $co$ (at $\mu\in[0,1]$) are nonempty and bounded above; nonemptiness of the $W^C$ set is the one-period content of Proposition 3. $co$ restricts the hypograph to beliefs in $[0,1]$, where $W^C$ lives, and is used only on $[0,1]$. When the count in (30) never reaches $n$, $\mu_{T+1}$ is $1$ if $\phi=\phi_H$ and $0$ if $\phi=\phi_L$, as on p. OA–15.
-- source:
--   Gur, Macnamara, Morgenstern & Saban, Information Disclosure and Promotion Policy Design for Platforms, arXiv:1911.09256v5, pp. 8–19, §2, (1)–(3), Assumptions 1–2, Definitions 1–4, (10), co (p. 19); p. OA–15 (PDF 49), M^{α_t}(ε), (30), W^max

import Mathlib

namespace ConfoundPromo.LongRun

noncomputable section
open scoped Classical
open Finset

/-! # The platform–seller game of Gur, Macnamara, Morgenstern & Saban (§2–§4)

Periods: the paper's periods `t = 1, …, T` are `Fin T` in Lean, so Lean period `t` is the paper's
period `t + 1`. A history of length `t` (type `SHist n t`) is the paper's `h̄_{t+1}`: the signal and
the first `t` (price, sale) pairs. The belief at a history of length `t` is the paper's `μ_{t+1}`;
in particular the belief at length `0` is `μ_1`, the post-signal belief. -/

/-- Primitives of the market (§2, pp. 8–10): the two fractions of impatient consumers `φ_L, φ_H`,
the price interval `P = [pLo, pHi]`, the purchase probabilities `ρ̄c, ρ̄0` of (1), and the surplus
levels `W̄c, W̄0, W̄out` of (2). -/
structure Market where
  phiL : ℝ
  phiH : ℝ
  pLo : ℝ
  pHi : ℝ
  rhoC : ℝ → ℝ
  rho0 : ℝ → ℝ
  Wc : ℝ → ℝ
  W0 : ℝ → ℝ
  Wout : ℝ

/-- The seller's price set `P`, a compact interval. -/
def Market.price (M : Market) : Set ℝ := Set.Icc M.pLo M.pHi

/-- The fraction of impatient consumers in state `b` (`true` is `φ_H`, `false` is `φ_L`). -/
def Market.phiVal (M : Market) (b : Bool) : ℝ := if b then M.phiH else M.phiL

/-- Standing assumptions of §2: `0 < φ_L < φ_H < 1` (p. 8); `P` contains `0` (p. 10);
Assumption 1 (p. 9); Assumption 2 (p. 10). "Decreasing" is read as weakly decreasing.
Disclosed addition: `0 ≤ ρ̄c` and `ρ̄0 ≤ 1` on `P`, since (1) defines them as probabilities. -/
structure Market.Standing (M : Market) : Prop where
  phiL_pos : 0 < M.phiL
  phiL_lt_phiH : M.phiL < M.phiH
  phiH_lt_one : M.phiH < 1
  pLo_nonpos : M.pLo ≤ 0
  pHi_nonneg : 0 ≤ M.pHi
  rhoC_antitone : AntitoneOn M.rhoC M.price
  rho0_antitone : AntitoneOn M.rho0 M.price
  rhoC_lipschitz : ∃ K, LipschitzOnWith K M.rhoC M.price
  rho0_lipschitz : ∃ K, LipschitzOnWith K M.rho0 M.price
  revC_strictConcave : StrictConcaveOn ℝ M.price (fun p => p * M.rhoC p)
  rev0_strictConcave : StrictConcaveOn ℝ M.price (fun p => p * M.rho0 p)
  rhoC_le_rho0 : ∀ p ∈ M.price, M.rhoC p ≤ M.rho0 p
  rhoC_nonneg : ∀ p ∈ M.price, 0 ≤ M.rhoC p
  rho0_le_one : ∀ p ∈ M.price, M.rho0 p ≤ 1
  Wc_antitone : AntitoneOn M.Wc M.price
  W0_antitone : AntitoneOn M.W0 M.price
  Wc_lipschitz : ∃ K, LipschitzOnWith K M.Wc M.price
  W0_lipschitz : ∃ K, LipschitzOnWith K M.W0 M.price

/-- Probability of a sale in state `b` at price `p` when the seller is promoted with probability
`a`: `φ a ρ̄0(p) + (1 − φ) ρ̄c(p)`, from (1). -/
def saleProb (M : Market) (b : Bool) (a p : ℝ) : ℝ :=
  M.phiVal b * a * M.rho0 p + (1 - M.phiVal b) * M.rhoC p

/-- Expected consumer surplus of one period in state `b` at price `p` with promotion probability
`a`: `φ (W̄out + a (W̄0(p) − W̄out)) + (1 − φ) W̄c(p)`, from (2). -/
def surplus (M : Market) (b : Bool) (a p : ℝ) : ℝ :=
  M.phiVal b * (M.Wout + a * (M.W0 p - M.Wout)) + (1 - M.phiVal b) * M.Wc p

/-- Probability of the sale outcome `y` (sale if `true`). -/
def likelihood (M : Market) (b : Bool) (a p : ℝ) (y : Bool) : ℝ :=
  if y then saleProb M b a p else 1 - saleProb M b a p

/-- Bayes' rule for the probability of `{φ = φ_H}` given likelihoods `lH`, `lL` of an
observation. Junk: if the observation has predictive probability `0`, the belief is kept. -/
def bayes (μ lH lL : ℝ) : ℝ :=
  if μ * lH + (1 - μ) * lL = 0 then μ else μ * lH / (μ * lH + (1 - μ) * lL)

/-- Prior weight of state `b`: `μ0` for `φ_H`, `1 − μ0` for `φ_L`. -/
def prior (μ0 : ℝ) (b : Bool) : ℝ := if b then μ0 else 1 - μ0

/-- A signaling mechanism with signal set `Fin n`: `sig b s` is the probability of signal `s`
in state `b`. -/
abbrev Signal (n : ℕ) : Type := Bool → Fin n → ℝ

/-- A signaling mechanism is valid when each `sig b ·` is a probability vector. -/
def Signal.IsValid {n : ℕ} (sig : Signal n) : Prop :=
  (∀ b s, 0 ≤ sig b s) ∧ ∀ b, ∑ s, sig b s = 1

/-- The uninformative signal (a single signal). -/
def trivialSignal : Signal 1 := fun _ _ => 1

/-- Seller histories `h̄ = ⟨s, (p_{t'}, y_{t'})_{t' < t}⟩` of length `t`. -/
abbrev SHist (n t : ℕ) : Type := Fin n × (Fin t → ℝ × Bool)

/-- Append a (price, sale) pair to a history. -/
def SHist.snoc {n t : ℕ} (h : SHist n t) (x : ℝ × Bool) : SHist n (t + 1) :=
  (h.1, Fin.snoc (α := fun _ => ℝ × Bool) h.2 x)

/-- Drop the last (price, sale) pair of a history. -/
def SHist.init {n t : ℕ} (h : SHist n (t + 1)) : SHist n t :=
  (h.1, Fin.init (α := fun _ => ℝ × Bool) h.2)

/-- The last (price, sale) pair of a history. -/
def SHist.last {n t : ℕ} (h : SHist n (t + 1)) : ℝ × Bool := h.2 (Fin.last t)

/-- All recorded prices lie in `P`: the history lies in the paper's `H̄ = S × (P × {0,1})^{t}`. -/
def SHist.InPrice (M : Market) {n t : ℕ} (h : SHist n t) : Prop := ∀ i, (h.2 i).1 ∈ M.price

/-- A promotion policy over horizon `T`: `α t q b h` is the probability of promoting the seller in
period `t` at price `q` in state `b` after history `h` (the paper's `α_t(p, φ, h̄_t)`). -/
abbrev Promo (n T : ℕ) : Type := (t : Fin T) → ℝ → Bool → SHist n t → ℝ

/-- Promotion probabilities lie in `[0, 1]`. -/
def Promo.IsValid {n T : ℕ} (α : Promo n T) : Prop := ∀ t q b h, α t q b h ∈ Set.Icc (0 : ℝ) 1

/-- `α` read at a natural-number period (`0` beyond the horizon; never used there). -/
def Promo.at {n T : ℕ} (α : Promo n T) (t : ℕ) (q : ℝ) (b : Bool) (h : SHist n t) : ℝ :=
  if ht : t < T then α ⟨t, ht⟩ q b h else 0

/-- A deterministic pricing policy: the price set in period `t` after history `h`. -/
abbrev Pricing (n T : ℕ) : Type := (t : Fin T) → SHist n t → ℝ

/-- `π` read at a natural-number period (`0` beyond the horizon; never used there). -/
def Pricing.at {n T : ℕ} (π : Pricing n T) (t : ℕ) (h : SHist n t) : ℝ :=
  if ht : t < T then π ⟨t, ht⟩ h else 0

/-- The seller's Bayesian belief that `φ = φ_H` at a history of length `t` (the paper's
`μ_{t+1}`). Length `0`: Bayes on the signal. Length `t + 1`: Bayes on the last recorded
(price, sale) pair, with likelihoods given by the sale probability under `α` at that price.
The belief depends on `μ0`, `σ`, `α` but not on the pricing policy, because the history records
the prices. -/
def belief (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T) :
    (t : ℕ) → SHist n t → ℝ
  | 0, h => bayes μ0 (sig true h.1) (sig false h.1)
  | t + 1, h =>
      bayes (belief M μ0 sig α t h.init)
        (likelihood M true (α.at t h.last.1 true h.init) h.last.1 h.last.2)
        (likelihood M false (α.at t h.last.1 false h.init) h.last.1 h.last.2)

/-- The sale outcome of period `t` on the outcome path `y` (`false` beyond the horizon). -/
def yAt {T : ℕ} (y : Fin T → Bool) (t : ℕ) : Bool := if ht : t < T then y ⟨t, ht⟩ else false

/-- The history of length `t` generated by pricing policy `π`, signal `s` and sale outcomes `y`
(prices are determined recursively by `π`). -/
def histAt {n T : ℕ} (π : Pricing n T) (s : Fin n) (y : Fin T → Bool) : (t : ℕ) → SHist n t
  | 0 => (s, fun i => i.elim0)
  | t + 1 => (histAt π s y t).snoc (π.at t (histAt π s y t), yAt y t)

/-- The price set in period `t` on the path `(s, y)`. -/
def priceAt {n T : ℕ} (π : Pricing n T) (s : Fin n) (y : Fin T → Bool) (t : ℕ) : ℝ :=
  π.at t (histAt π s y t)

/-- The promotion probability in period `t` on the path `(b, s, y)`. -/
def promoAt {n T : ℕ} (α : Promo n T) (π : Pricing n T) (b : Bool) (s : Fin n)
    (y : Fin T → Bool) (t : ℕ) : ℝ :=
  α.at t (priceAt π s y t) b (histAt π s y t)

/-- Probability of the sale-outcome path `y` given state `b` and signal `s`. -/
def pathProb (M : Market) {n T : ℕ} (α : Promo n T) (π : Pricing n T) (b : Bool) (s : Fin n)
    (y : Fin T → Bool) : ℝ :=
  ∏ t : Fin T, likelihood M b (promoAt α π b s y t) (priceAt π s y t) (y t)

/-- Total expected consumer surplus of the path, `∑_t E[W(p_t, a_t, ψ_t) | b, h̄_t]`. -/
def pathSurplus (M : Market) {n T : ℕ} (α : Promo n T) (π : Pricing n T) (b : Bool) (s : Fin n)
    (y : Fin T → Bool) : ℝ :=
  ∑ t : Fin T, surplus M b (promoAt α π b s y t) (priceAt π s y t)

/-- Expectation, conditional on `φ = φ_b`, of a function of `(s, y)`. -/
def condExpect (M : Market) {n T : ℕ} (sig : Signal n) (α : Promo n T) (π : Pricing n T)
    (b : Bool) (F : Fin n → (Fin T → Bool) → ℝ) : ℝ :=
  ∑ s, sig b s * ∑ y, pathProb M α π b s y * F s y

/-- Full expectation over `(φ, s, y)` of a function of `(φ, s, y)`, with prior `μ0`. -/
def expect (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T) (π : Pricing n T)
    (F : Bool → Fin n → (Fin T → Bool) → ℝ) : ℝ :=
  ∑ b, prior μ0 b * condExpect M sig α π b (F b)

/-- The platform's expected payoff (3): `W_T^{α,σ,π}(μ0) = E(∑_{t=1}^T W(p_t, a_t, ψ_t))`. -/
def surplusT (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) : ℝ :=
  expect M μ0 sig α π (fun b s y => pathSurplus M α π b s y)

/-! ## One-period quantities at belief `μ` under a promotion rule `a q b`. -/

/-- The seller's expected current revenue `E(v(q, y))` at price `q` and belief `μ`. -/
def expRev (M : Market) (μ : ℝ) (a : ℝ → Bool → ℝ) (q : ℝ) : ℝ :=
  q * (μ * saleProb M true (a q true) q + (1 - μ) * saleProb M false (a q false) q)

/-- The current expected consumer surplus at price `q` under belief `μ`. -/
def expSurplus (M : Market) (μ : ℝ) (a : ℝ → Bool → ℝ) (q : ℝ) : ℝ :=
  μ * surplus M true (a q true) q + (1 - μ) * surplus M false (a q false) q

/-- Definition 1 at one history: `p ∈ P` maximizes the expected current revenue, and among the
maximizers it maximizes the current expected consumer surplus (taken under the seller's belief). -/
def IsMyopicChoice (M : Market) (μ : ℝ) (a : ℝ → Bool → ℝ) (p : ℝ) : Prop :=
  p ∈ M.price ∧ (∀ q ∈ M.price, expRev M μ a q ≤ expRev M μ a p) ∧
    ∀ q ∈ M.price, expRev M μ a q = expRev M μ a p → expSurplus M μ a q ≤ expSurplus M μ a p

/-- Definition 1 (myopic Bayesian pricing policy): at every period and every history with prices
in `P`, `π` makes a myopic choice given the current belief and the current promotion rule. -/
def IsMyopic (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) : Prop :=
  ∀ (t : Fin T) (h : SHist n t), h.InPrice M →
    IsMyopicChoice M (belief M μ0 sig α t h) (fun q b => α t q b h) (π t h)

/-- Definition 2 (`α ∈ A^M`, for the given `σ`): `α_t` takes the same values on histories with
the same belief. -/
def IsBeliefBased (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T) : Prop :=
  ∀ (t : Fin T) (h h' : SHist n t), h.InPrice M → h'.InPrice M →
    belief M μ0 sig α t h = belief M μ0 sig α t h' → ∀ q ∈ M.price, ∀ b, α t q b h = α t q b h'

/-- Definition 3 (`α ∈ A^P`): after every history at most one price is promoted with positive
probability. -/
def IsSinglePrice (M : Market) {n T : ℕ} (α : Promo n T) : Prop :=
  ∀ (t : Fin T) (h : SHist n t), h.InPrice M →
    ∃ pbar ∈ M.price, ∀ q ∈ M.price, q ≠ pbar → ∀ b, α t q b h = 0

/-- Definition 4 (confounding): on every `(φ, s, y)` of positive probability, the belief at each
of the paper's periods `2, …, T + 1` equals the post-signal belief `μ_1`. -/
def IsConfounding (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) : Prop :=
  ∀ b s y, 0 < prior μ0 b * sig b s * pathProb M α π b s y →
    ∀ t : Fin T, belief M μ0 sig α (t + 1) (histAt π s y (t + 1)) =
      belief M μ0 sig α 0 (histAt π s y 0)

/-- One-period confounding: after either sale outcome the Bayes posterior equals `μ`. -/
def IsConfoundingChoice (M : Market) (μ : ℝ) (a : ℝ → Bool → ℝ) (p : ℝ) : Prop :=
  ∀ y : Bool, bayes μ (likelihood M true (a p true) p y) (likelihood M false (a p false) p y) = μ

/-- Promotion rule values lie in `[0, 1]`. -/
def IsValidRule (a : ℝ → Bool → ℝ) : Prop := ∀ q b, a q b ∈ Set.Icc (0 : ℝ) 1

/-- `W^C(μ)`, (10) at `T = 1`: the supremum of the current expected surplus over valid one-period
rules `a` and myopic choices `p` (Definition 1, with tie-break) that keep the belief at `μ`.
Real `sSup`: junk `0` if the set is empty or unbounded above. -/
def WC (M : Market) (μ : ℝ) : ℝ :=
  sSup {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
    IsConfoundingChoice M μ a p ∧ v = expSurplus M μ a p}

/-- `W^max(μ)` (p. OA–15): the supremum of the current expected surplus over all valid one-period
rules and myopic choices at belief `μ`. Real `sSup`, as for `WC`. -/
def Wmax (M : Market) (μ : ℝ) : ℝ :=
  sSup {v | ∃ (a : ℝ → Bool → ℝ) (p : ℝ), IsValidRule a ∧ IsMyopicChoice M μ a p ∧
    v = expSurplus M μ a p}

/-- Concavification (p. 19): `co(f)(μ) = sup{z | (μ, z) ∈ Conv(f)}`, with `Conv(f)` the convex
hull of the hypograph of `f` over beliefs in `[0, 1]`. Real `sSup`; used only at `μ ∈ [0, 1]`. -/
def co (f : ℝ → ℝ) (μ : ℝ) : ℝ :=
  sSup {z | (μ, z) ∈ convexHull ℝ {x : ℝ × ℝ | x.1 ∈ Set.Icc (0 : ℝ) 1 ∧ x.2 ≤ f x.1}}

/-! ## Quantities of the proof of Theorem 1 (§B.5.1) -/

/-- Current expected consumer surplus in period `t` at history `h`. -/
def periodSurplus (M : Market) {n T : ℕ} (μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) (t : Fin T) (h : SHist n t) : ℝ :=
  expSurplus M (belief M μ0 sig α t h) (fun q b => α t q b h) (π t h)

/-- `μ_t ∈ M^{α_t}(ε)`: the current expected surplus exceeds `co(W^C)(μ_t) + ε`. -/
def InExcess (M : Market) {n T : ℕ} (ε μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) (t : Fin T) (h : SHist n t) : Prop :=
  co (WC M) (belief M μ0 sig α t h) + ε < periodSurplus M μ0 sig α π t h

/-- `∑_{t' ≤ t} 1{μ_{t'} ∈ M^{α_{t'}}(ε)}` on the path `(s, y)`. -/
def excessCount (M : Market) {n T : ℕ} (ε μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) (s : Fin n) (y : Fin T → Bool) (t : Fin T) : ℕ :=
  (univ.filter (fun t' : Fin T => t' ≤ t ∧ InExcess M ε μ0 sig α π t' (histAt π s y t'))).card

/-- The periods at which the count has reached `m`. -/
def reachSet (M : Market) {n T : ℕ} (ε μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) (s : Fin n) (y : Fin T → Bool) (m : ℕ) : Finset (Fin T) :=
  univ.filter (fun t : Fin T => m ≤ excessCount M ε μ0 sig α π s y t)

/-- `μ_{t_m}` with `t_m` as in (30): the belief at the first period at which the count reaches `m`;
if it never does, `t_m = T + 1` and `μ_{T+1}` is `1` if `φ = φ_H` and `0` if `φ = φ_L`. -/
def hitBelief (M : Market) {n T : ℕ} (ε μ0 : ℝ) (sig : Signal n) (α : Promo n T)
    (π : Pricing n T) (b : Bool) (s : Fin n) (y : Fin T → Bool) (m : ℕ) : ℝ :=
  if hne : (reachSet M ε μ0 sig α π s y m).Nonempty then
    belief M μ0 sig α ((reachSet M ε μ0 sig α π s y m).min' hne : ℕ)
      (histAt π s y ((reachSet M ε μ0 sig α π s y m).min' hne : ℕ))
  else if b then 1 else 0

end

end ConfoundPromo.LongRun


