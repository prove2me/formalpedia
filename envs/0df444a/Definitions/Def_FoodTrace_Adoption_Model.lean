-- Prove2me | Definitions.Def_FoodTrace_Adoption_Model
-- name    : FoodTrace_Adoption_Model
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-22T03:44:28.976029+00:00
-- url     : https://prove2.me/theorems/10db65fa-d81e-4772-9083-1398ebfa3b1a
-- title:
--   The three-tier traceability game: parameters, tier-2 payoffs (1)–(2), tier-1 and retailer profits, SPNE with the selection rules of p. 8, closed-form thresholds and BPC (§3–§4, §6.1, Tables EC.1–EC.2)
-- statement:
--   A retailer sells $n$ units of a food product at an exogenous retail price $r$. She buys them at a wholesale price $w$ from one tier-1 supplier, who buys one unit at a procurement price $p$ from each of $n$ tier-2 suppliers (farms). Each farm produces its unit at cost $c_p$ and is contaminated independently with probability $\rho$, or with probability $\rho_e$ if it exerts a risk-reduction effort at cost $e$; write $\rho_\tau = \rho - \rho_e$. The **standing assumptions** are $n \ge 2$, $0 \le \rho_e < \rho < 1$, $e > 0$, $c_p > 0$ and Assumption 1,
--   $$c_p < \bar c_p = \frac{(1-\rho)e}{\rho_\tau}.$$
--
--   An **effort profile** is $a \in \{\text{true},\text{false}\}^n$ ($a_i$ true iff farm $i$ exerts effort). Farm $i$'s survival probability is $s(a_i) = 1-\rho_e$ with effort and $1-\rho$ without. There are two supply chains:
--
--   1. **Case N** (no traceability): any contamination voids every payment. Farm $i$'s payoff is $\pi^i_{2N}(a;p) = \big(\prod_j s(a_j)\big)p - (e\,\mathbb 1\{a_i\} + c_p)$ (eq. (1)), and the expected number of units sold is $n\prod_j s(a_j)$.
--   2. **Case T** (traceability): only contaminated units are lost. Farm $i$'s payoff is $\pi^i_{2T}(a;p) = s(a_i)p - (e\,\mathbb 1\{a_i\} + c_p)$ (eq. (2)), and the expected number of units sold is $\sum_j s(a_j)$.
--
--   The game is played in three stages: the retailer chooses $w$ or not to trade, tier-1 chooses $p$ or not to trade, then the farms choose effort simultaneously. The file defines:
--
--   1. A **viable equilibrium** at $p$: every farm's payoff is $\ge 0$; a farm exerting effort weakly prefers effort to no effort; a farm not exerting effort strictly prefers that (ties go to effort and to doing business).
--   2. The **selected tier-2 outcome** at $p$: a viable equilibrium whose payoffs weakly dominate, farm by farm, those of every viable equilibrium; or "no sale" when no viable equilibrium exists.
--   3. Tier-1's profit $(\text{units sold})\cdot(w-p)$ and the retailer's profit $(\text{units sold})\cdot(r-w)$, both $0$ without trade. On symmetric profiles these are $\pi_{1N} = nS^n(w-p)$, $\pi_{0N} = nS^n(r-w)$, $\pi_{1T} = nS(w-p)$, $\pi_{0T} = nS(r-w)$ with $S \in \{1-\rho_e, 1-\rho\}$.
--   4. Tier-1's **best response** at $w$ and the retailer's **optimal choice** at $r$: a maximizer over every price in $\mathbb R$ and over not trading which, among maximizers, induces all-farm effort whenever some maximizer does and trades whenever some maximizer trades.
--   5. A **subgame-perfect Nash equilibrium (SPNE)** at $r$: a selected tier-2 outcome at every $p$, a tier-1 best response at every $w$, and an optimal retailer choice at $r$. The retailer's **equilibrium profit** is her profit at the SPNE; the chain **trades** if the retailer's offer is accepted down the chain.
--   6. The closed forms, with $\ell = (1-\rho_e)^n - (1-\rho)^n$: $\underline c_p = \frac{e(1-\rho)^n}{\rho_\tau(1-\rho_e)^{n-1}}$, $p^o_N = w^o_N = r^o_N = \frac{c_p}{(1-\rho)^n}$, $p^e_N = \frac{e}{\rho_\tau(1-\rho_e)^{n-1}}$, $w^e_N = \max\{\frac{(1-\rho_e)e-\rho_\tau c_p}{\rho_\tau\ell}, p^e_N\}$, $r^e_N = \max\{\frac{(1-\rho_e)^{n+1}e-[2(1-\rho_e)^n-(1-\rho)^n]\rho_\tau c_p}{\rho_\tau\ell^2}, p^e_N\}$, $p^o_T = w^o_T = r^o_T = \frac{c_p}{1-\rho}$, $p^e_T = \frac{e}{\rho_\tau}$, $w^e_T = \frac{(1-\rho_e)e-\rho_\tau c_p}{\rho_\tau^2}$, $r^e_T = \frac{(1-\rho_e)^2e-(1+\rho-2\rho_e)\rho_\tau c_p}{\rho_\tau^3}$; and the retailer's branch profits of Tables EC.1–EC.2, $\pi^e_{0N}(r) = n(1-\rho_e)^n(r-w^e_N)$, $\pi^o_{0N}(r) = n(1-\rho)^n r - nc_p$, $\pi^e_{0T}(r) = n(1-\rho_e)(r-w^e_T)$, $\pi^o_{0T}(r) = n(1-\rho)r - nc_p$.
--   7. The **Break Point Criterion** (Definition 1): $\pi^e_{0T}(r^e_T) < \pi^e_{0N}(r^e_T)$.
--
--   These are the objects of Lemmas 1–5 and Propositions 1–3 of the paper.
--
--   **Formalization Note** Effort is a `Bool` per farm and profiles are `Fin n → Bool`; symmetry is not built into any definition. "No trade" is `none` in `Option`, with profit 0. Prices range over all of $\mathbb R$. Case T's revenue for an asymmetric profile is $\sum_j s(a_j)$ times the margin (the paper prints only the symmetric case $nS$). "Induces effort" means every farm exerts effort. $w^e_N$ and $r^e_N$ are defined with the max, so $\pi^e_{0N}$ is one formula in both cost branches. $\underline c_p$ is `cpLow` and $\bar c_p$ is `cpBar`. The exponent $n-1$ is natural-number subtraction, exact because $n \ge 2$.
-- source:
--   Dong, Jiang & Xu, Impact of Traceability Technology Adoption in Food Supply Chain Networks, Management Science (accepted manuscript, SSRN 3484664, March 2022), pp. 7–14, §3–§4 (eqs. (1), (2), Assumption 1, the rules of p. 8, Lemmas 1–4, Propositions 1–2), p. 20 (Definition 1), p. ec2 (Tables EC.1–EC.2), p. ec22 ((EC.9))

import Mathlib

namespace FoodTrace.Adoption

/-! The three-tier traceability game of Dong, Jiang & Xu, *Impact of Traceability Technology
Adoption in Food Supply Chain Networks*, Management Science (accepted manuscript, SSRN 3484664,
March 2022), §3 (pp. 6–8), §4.1 (pp. 9–11), §4.2 (pp. 12–14), §6.1 (p. 20) and Tables EC.1–EC.2
(p. ec2).

A retailer sells `n` units at the exogenous retail price `r`. She buys them at the wholesale price
`w` from one tier-1 supplier, who buys one unit at the procurement price `p` from each of `n`
tier-2 farms. Each farm produces at unit cost `c_p` and is contaminated independently with
probability `ρ`, or `ρ_e < ρ` if it exerts risk-reduction effort at cost `e`. Without traceability
(Case N) any contamination voids every payment; with traceability (Case T) only contaminated
units are lost. The retailer moves first (`w`), tier-1 second (`p`), and the farms then choose
effort simultaneously. -/

/-- The primitive parameters (§3, pp. 7–8): the number `n` of tier-2 suppliers, the contamination
probabilities `ρ` (no effort) and `ρe` (with effort), the effort cost `e` and the unit production
cost `cp`. The retail price `r` is not a parameter; it is an argument of every result. -/
structure Params where
  /-- number of tier-2 suppliers -/
  n : ℕ
  /-- contamination probability without effort -/
  ρ : ℝ
  /-- contamination probability with effort -/
  ρe : ℝ
  /-- cost of the risk-reduction effort -/
  e : ℝ
  /-- unit production cost `c_p` -/
  cp : ℝ

/-- `ρ_τ = ρ − ρ_e`, the risk-reduction rate of the effort (p. 7). -/
def ρτ (P : Params) : ℝ := P.ρ - P.ρe

/-- `c̄_p = (1 − ρ) e / ρ_τ` (Assumption 1, p. 8). -/
noncomputable def cpBar (P : Params) : ℝ := (1 - P.ρ) * P.e / ρτ P

/-- The standing assumptions: `n ≥ 2` (§4, p. 8); `ρ_τ = ρ − ρ_e > 0` (p. 7) with `0 ≤ ρ_e` and
`ρ < 1` (probabilities); `e > 0`, `c_p > 0`; and Assumption 1, `c_p < c̄_p` (p. 8). -/
def Standing (P : Params) : Prop :=
  2 ≤ P.n ∧ 0 ≤ P.ρe ∧ P.ρe < P.ρ ∧ P.ρ < 1 ∧ 0 < P.e ∧ 0 < P.cp ∧ P.cp < cpBar P

/-- The two supply chains: without traceability (Case N) and with traceability (Case T). -/
inductive Case
  | N
  | T

/-- An effort profile of the tier-2 suppliers: `a i = true` iff supplier `i` exerts effort `e`. -/
abbrev Profile (P : Params) := Fin P.n → Bool

/-- The profile in which every tier-2 supplier exerts effort (`eI`). -/
def allEffort (P : Params) : Profile P := fun _ => true

/-- The profile in which no tier-2 supplier exerts effort (`0`). -/
def noEffort (P : Params) : Profile P := fun _ => false

/-- A supplier's survival (non-contamination) probability `1 − ρ_e·𝟙{e_i=e} − ρ·𝟙{e_i=0}`. -/
def survival (P : Params) (b : Bool) : ℝ := if b then 1 - P.ρe else 1 - P.ρ

/-- A supplier's cost `e·𝟙{e_i=e} + c_p`. -/
def supplierCost (P : Params) (b : Bool) : ℝ := (if b then P.e else 0) + P.cp

/-- Tier-2 supplier `i`'s payoff at procurement price `p` under profile `a`.
Case N, eq. (1), p. 9: `(∏_j s(a_j))·p − (e·𝟙{a_i} + c_p)` (paid only if no supplier is
contaminated; this is `(1−ρ_e)^m (1−ρ)^{n−m−1}(1 − ρ_e𝟙 − ρ𝟙) p − (e𝟙 + c_p)` with `m` the number of
other suppliers exerting effort). Case T, eq. (2), p. 13: `s(a_i)·p − (e·𝟙{a_i} + c_p)`. -/
noncomputable def tier2Payoff : Case → (P : Params) → ℝ → Profile P → Fin P.n → ℝ
  | .N, P, p, a, i => (∏ j, survival P (a j)) * p - supplierCost P (a i)
  | .T, P, p, a, i => survival P (a i) * p - supplierCost P (a i)

/-- Expected number of units sold (and paid for) under profile `a`. Case N: `n·∏_j s(a_j)` (any
contamination voids all payments, p. 8). Case T: `Σ_j s(a_j)` (only uncontaminated units are paid,
p. 8). On symmetric profiles these are the paper's `n S^n` and `n S`. -/
noncomputable def unitsSold : Case → (P : Params) → Profile P → ℝ
  | .N, P, a => (P.n : ℝ) * ∏ j, survival P (a j)
  | .T, P, a => ∑ j, survival P (a j)

/-- `a` is a viable tier-2 Nash equilibrium at procurement price `p` (conditions (EC.9), p. ec22,
with the tie rules of p. 8): every supplier's payoff is nonnegative (at zero profit it conducts
business), a supplier exerting effort weakly prefers it to not exerting effort (ties are broken
towards effort), and a supplier not exerting effort strictly prefers that. -/
def IsViableEq (c : Case) (P : Params) (p : ℝ) (a : Profile P) : Prop :=
  ∀ i : Fin P.n,
    0 ≤ tier2Payoff c P p a i ∧
    (a i = true → tier2Payoff c P p (Function.update a i false) i ≤ tier2Payoff c P p a i) ∧
    (a i = false → tier2Payoff c P p (Function.update a i true) i < tier2Payoff c P p a i)

/-- The tier-2 outcome selected at procurement price `p` (p. 8: "we focus on the Pareto dominant
one as the unique equilibrium"): `some a` for a viable equilibrium `a` that weakly Pareto-dominates
every viable equilibrium, or `none` (tier-2 suppliers do not sell) when no viable equilibrium
exists. -/
def Tier2Selects (c : Case) (P : Params) (p : ℝ) : Option (Profile P) → Prop
  | some a => IsViableEq c P p a ∧
      ∀ b : Profile P, IsViableEq c P p b → ∀ i, tier2Payoff c P p b i ≤ tier2Payoff c P p a i
  | none => ∀ a : Profile P, ¬ IsViableEq c P p a

/-- A tier-2 outcome induces effort: trade takes place and every tier-2 supplier exerts effort. -/
def InducesEffort (P : Params) (o : Option (Profile P)) : Prop := o = some (allEffort P)

/-- The tier-2 outcome reached when tier-1 chooses `x` (`some p`: offer procurement price `p`;
`none`: do not trade), given the tier-2 response `σ₂`. -/
def tier1Outcome {P : Params} (σ₂ : ℝ → Option (Profile P)) : Option ℝ → Option (Profile P)
  | some p => σ₂ p
  | none => none

/-- Tier-1's profit at wholesale price `w` when choosing `x`: `unitsSold·(w − p)` if it offers `p`
and tier-2 sells (pp. 10, 13: `π_1(p; w) = n S^n (w − p)`, resp. `n S (w − p)`), and `0` with no
trade (reservation utility zero, p. 7). -/
noncomputable def tier1Profit (c : Case) {P : Params} (σ₂ : ℝ → Option (Profile P)) (w : ℝ) :
    Option ℝ → ℝ
  | some p => match σ₂ p with
    | some a => unitsSold c P a * (w - p)
    | none => 0
  | none => 0

/-- `x` is tier-1's best response at wholesale price `w`, given the tier-2 response `σ₂`, with the
tie rules of p. 8: it maximizes tier-1's profit over every procurement price `p ∈ ℝ` and over not
trading; among maximizers it induces tier-2 effort whenever some maximizer does; and it trades
whenever some maximizer trades. -/
def IsTier1BR (c : Case) {P : Params} (σ₂ : ℝ → Option (Profile P)) (w : ℝ) (x : Option ℝ) :
    Prop :=
  (∀ y : Option ℝ, tier1Profit c σ₂ w y ≤ tier1Profit c σ₂ w x) ∧
  ((∃ y : Option ℝ, tier1Profit c σ₂ w y = tier1Profit c σ₂ w x ∧
      InducesEffort P (tier1Outcome σ₂ y)) → InducesEffort P (tier1Outcome σ₂ x)) ∧
  ((∃ y : Option ℝ, tier1Profit c σ₂ w y = tier1Profit c σ₂ w x ∧
      tier1Outcome σ₂ y ≠ none) → tier1Outcome σ₂ x ≠ none)

/-- The tier-2 outcome reached when the retailer chooses `x` (`some w`: offer wholesale price `w`;
`none`: do not trade), given tier-1's strategy `σ₁` and the tier-2 response `σ₂`. -/
def retailerOutcome {P : Params} (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ) :
    Option ℝ → Option (Profile P)
  | some w => tier1Outcome σ₂ (σ₁ w)
  | none => none

/-- The retailer's profit at retail price `r` when choosing `x`: `unitsSold·(r − w)` if she offers
`w` and the chain trades (pp. 11, 14: `π_0(w; r) = n S^n (r − w)`, resp. `n S (r − w)`), and `0`
with no trade. -/
noncomputable def retailerPayoff (c : Case) {P : Params} (σ₂ : ℝ → Option (Profile P))
    (σ₁ : ℝ → Option ℝ) (r : ℝ) : Option ℝ → ℝ
  | some w => match tier1Outcome σ₂ (σ₁ w) with
    | some a => unitsSold c P a * (r - w)
    | none => 0
  | none => 0

/-- `x` is the retailer's optimal choice at retail price `r`, given `σ₁` and `σ₂`, with the tie
rules of p. 8: it maximizes her profit over every wholesale price `w ∈ ℝ` and over not trading;
among maximizers it induces tier-2 effort whenever some maximizer does; and it trades whenever
some maximizer trades. -/
def IsRetailerOpt (c : Case) {P : Params} (σ₂ : ℝ → Option (Profile P)) (σ₁ : ℝ → Option ℝ)
    (r : ℝ) (x : Option ℝ) : Prop :=
  (∀ y : Option ℝ, retailerPayoff c σ₂ σ₁ r y ≤ retailerPayoff c σ₂ σ₁ r x) ∧
  ((∃ y : Option ℝ, retailerPayoff c σ₂ σ₁ r y = retailerPayoff c σ₂ σ₁ r x ∧
      InducesEffort P (retailerOutcome σ₂ σ₁ y)) → InducesEffort P (retailerOutcome σ₂ σ₁ x)) ∧
  ((∃ y : Option ℝ, retailerPayoff c σ₂ σ₁ r y = retailerPayoff c σ₂ σ₁ r x ∧
      retailerOutcome σ₂ σ₁ y ≠ none) → retailerOutcome σ₂ σ₁ x ≠ none)

/-- A strategy profile of the three-stage game: the tier-2 outcome `σ₂ p` at every procurement
price, tier-1's choice `σ₁ w` at every wholesale price, and the retailer's choice `w`. -/
structure Strategy (P : Params) where
  /-- tier-2 response: the outcome at each procurement price (`none`: tier-2 does not sell) -/
  σ₂ : ℝ → Option (Profile P)
  /-- tier-1 strategy: the procurement price offered at each wholesale price (`none`: no trade) -/
  σ₁ : ℝ → Option ℝ
  /-- the retailer's wholesale price (`none`: no trade) -/
  w : Option ℝ

/-- Subgame-perfect Nash equilibrium of the game of Case `c` at retail price `r` (backward
induction, p. 9, with the selection rules of p. 8): tier-2 plays the selected equilibrium at every
`p`, tier-1 best-responds at every `w`, and the retailer's choice is optimal at `r`. -/
def IsSPNE (c : Case) (P : Params) (r : ℝ) (s : Strategy P) : Prop :=
  (∀ p : ℝ, Tier2Selects c P p (s.σ₂ p)) ∧
  (∀ w : ℝ, IsTier1BR c s.σ₂ w (s.σ₁ w)) ∧
  IsRetailerOpt c s.σ₂ s.σ₁ r s.w

/-- The retailer's equilibrium profit: her profit at the strategy profile `s`. -/
noncomputable def retailerProfit (c : Case) (P : Params) (r : ℝ) (s : Strategy P) : ℝ :=
  retailerPayoff c s.σ₂ s.σ₁ r s.w

/-- The supply chain trades at `s` (it is viable): the retailer offers a wholesale price, tier-1
offers a procurement price, and tier-2 sells. -/
def Trades {P : Params} (s : Strategy P) : Prop := retailerOutcome s.σ₂ s.σ₁ s.w ≠ none

/-! ### Closed forms (Lemmas 1–4, Propositions 1–2, Tables EC.1–EC.2) -/

/-- `ℓ(ρ, ρ_e, n) = (1 − ρ_e)^n − (1 − ρ)^n`, the survival probability difference (p. 10). -/
def ell (P : Params) : ℝ := (1 - P.ρe) ^ P.n - (1 - P.ρ) ^ P.n

/-- `c̲_p = e(1 − ρ)^n / (ρ_τ (1 − ρ_e)^{n−1})` (Lemma 1, p. 9). -/
noncomputable def cpLow (P : Params) : ℝ :=
  P.e * (1 - P.ρ) ^ P.n / (ρτ P * (1 - P.ρe) ^ (P.n - 1))

/-- `p^o_N = c_p / (1 − ρ)^n` (Lemma 1, p. 9). -/
noncomputable def pNo (P : Params) : ℝ := P.cp / (1 - P.ρ) ^ P.n

/-- `p^e_N = e / (ρ_τ (1 − ρ_e)^{n−1})` (Lemma 1, p. 9). -/
noncomputable def pNe (P : Params) : ℝ := P.e / (ρτ P * (1 - P.ρe) ^ (P.n - 1))

/-- `w^o_N = p^o_N` (Lemma 2, p. 10). -/
noncomputable def wNo (P : Params) : ℝ := pNo P

/-- `w^e_N = max{((1 − ρ_e)e − ρ_τ c_p)/(ρ_τ ℓ), p^e_N}` (Lemma 2, p. 10). -/
noncomputable def wNe (P : Params) : ℝ :=
  max (((1 - P.ρe) * P.e - ρτ P * P.cp) / (ρτ P * ell P)) (pNe P)

/-- `r^o_N = p^o_N` (Proposition 1, p. 11). -/
noncomputable def rNo (P : Params) : ℝ := pNo P

/-- `r^e_N = max{((1 − ρ_e)^{n+1} e − [2(1 − ρ_e)^n − (1 − ρ)^n] ρ_τ c_p)/(ρ_τ ℓ²), p^e_N}`
(Proposition 1, p. 11). -/
noncomputable def rNe (P : Params) : ℝ :=
  max (((1 - P.ρe) ^ (P.n + 1) * P.e
      - (2 * (1 - P.ρe) ^ P.n - (1 - P.ρ) ^ P.n) * ρτ P * P.cp) / (ρτ P * ell P ^ 2)) (pNe P)

/-- `p^o_T = c_p / (1 − ρ)` (Lemma 3, p. 13). -/
noncomputable def pTo (P : Params) : ℝ := P.cp / (1 - P.ρ)

/-- `p^e_T = e / ρ_τ` (Lemma 3, p. 13). -/
noncomputable def pTe (P : Params) : ℝ := P.e / ρτ P

/-- `w^o_T = p^o_T` (Lemma 4, p. 13). -/
noncomputable def wTo (P : Params) : ℝ := pTo P

/-- `w^e_T = ((1 − ρ_e)e − ρ_τ c_p)/ρ_τ²` (Lemma 4, p. 13). -/
noncomputable def wTe (P : Params) : ℝ := ((1 - P.ρe) * P.e - ρτ P * P.cp) / ρτ P ^ 2

/-- `r^o_T = c_p / (1 − ρ)` (Proposition 2, p. 14). -/
noncomputable def rTo (P : Params) : ℝ := P.cp / (1 - P.ρ)

/-- `r^e_T = ((1 − ρ_e)² e − (1 + ρ − 2ρ_e) ρ_τ c_p)/ρ_τ³` (Proposition 2, p. 14). -/
noncomputable def rTe (P : Params) : ℝ :=
  ((1 - P.ρe) ^ 2 * P.e - (1 + P.ρ - 2 * P.ρe) * ρτ P * P.cp) / ρτ P ^ 3

/-- `π^e_0N(r) = n(1 − ρ_e)^n (r − w^e_N)`: the retailer's profit on the effort branch without
traceability (Table EC.1, p. ec2; one formula for both cost branches through `w^e_N = max{…}`). -/
noncomputable def pi0Ne (P : Params) (r : ℝ) : ℝ := P.n * (1 - P.ρe) ^ P.n * (r - wNe P)

/-- `π^o_0N(r) = n(1 − ρ)^n r − n c_p` (Table EC.1, p. ec2). -/
noncomputable def pi0No (P : Params) (r : ℝ) : ℝ := P.n * (1 - P.ρ) ^ P.n * r - P.n * P.cp

/-- `π^e_0T(r) = n(1 − ρ_e)(r − w^e_T)` (Table EC.2, p. ec2). -/
noncomputable def pi0Te (P : Params) (r : ℝ) : ℝ := P.n * (1 - P.ρe) * (r - wTe P)

/-- `π^o_0T(r) = n(1 − ρ) r − n c_p` (Table EC.2, p. ec2). -/
noncomputable def pi0To (P : Params) (r : ℝ) : ℝ := P.n * (1 - P.ρ) * r - P.n * P.cp

/-- The Break Point Criterion (Definition 1, p. 20): `π^e_0T(r^e_T) < π^e_0N(r^e_T)`. -/
def BPC (P : Params) : Prop := pi0Te P (rTe P) < pi0Ne P (rTe P)

end FoodTrace.Adoption


