-- Prove2me | Definitions.Def_AuctionsOfAuctions_Model
-- name    : AuctionsOfAuctions_Model
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T03:26:49.708764+00:00
-- url     : https://prove2.me/theorems/6c7de456-f511-40fe-9b31-ca6b1e14c6b7
-- title:
--   Auctions of auctions model: $F$, regularity, $\lambda_m$, $\tilde\lambda$, bids $\beta,\tilde\sigma$, revenues $\pi^{dir}_P,\pi^{mono}_P,\pi^{ex}_P$, profit $\pi_C$, exchange game
-- statement:
--   A publisher sells one ad impression in a first-price sealed-bid **header auction** with reserve price $R$. Four advertisers have private valuations drawn independently from a distribution $F$ on $[0,1]$. This module defines every object of the model of Zeithammer and Choi.
--
--   1. **Valuation distribution** (§2, p.7). A density $f$ that is continuous on $[0,1]$, nonnegative there, strictly positive on $(0,1)$ and integrates to $1$ over $[0,1]$; the distribution function is $F(x)=\int_0^x f(t)\,dt$.
--   2. **Virtual value and regularity** (p.7). $\psi(x)=x-\frac{1-F(x)}{f(x)}$; $F$ is **regular** if $\psi$ is (weakly) increasing on $(0,1)$.
--   3. **Generalized hazard rate** (1): for $m\in\{1,2,\dots\}$,
--   $$\lambda_m(x)=\frac{mF^{m-1}(x)f(x)}{1-F^m(x)}.$$
--   4. **Advertisers' bid** (3): the symmetric equilibrium bid of a first-price auction with reserve $R$ and four bidders,
--   $$\beta(v;R)=\frac{RF^3(R)}{F^3(v)}+\frac{1}{F^3(v)}\int_R^v x\,dF^3(x).$$
--   By (10) the advertisers use the same bid when they are represented by exchanges.
--   5. **Exchanges' bid** (13), in terms of the highest valuation $m$ among the two advertisers an exchange represents,
--   $$\tilde\sigma(m;R)=\frac{RF^2(R)}{F^2(m)}+\frac{1}{F^2(m)}\int_R^m\beta(y;R)\,dF^2(y).$$
--   6. **Publisher revenues**: with $M$ the highest of the four valuations (law $F^4$),
--   $$\pi^{dir}_P(R)=\int_R^1\beta(M;R)\,dF^4(M)\ \ (4),\qquad \pi^{mono}_P(R)=R\,(1-F^4(R))\ \ (8),\qquad \pi^{ex}_P(R)=\int_R^1\tilde\sigma(M;R)\,dF^4(M)\ \ (18).$$
--   7. **Advertiser profit** (5): $\pi_C(R)=\frac14\int_R^1\big(M-\beta(M;R)\big)\,dF^4(M)$. By (16) this one function of the reserve is the advertiser's ex ante profit in every arrangement (direct, monopoly exchange, competing exchanges).
--   8. **Pseudo hazard rate** (19): $\tilde\lambda(x)=\dfrac{2F(x)f(x)}{[1-F(x)][3-F(x)]}$.
--   9. **Exchanges' header auction** (11)–(12). An exchange of type $m\in[R,1]$ receives its internal winning bid $\beta(m;R)$ and bids $s\ge R$. The rival exchange's type $m'$ has law $F^2$ (density $2F(m')f(m')$); it stays out if $m'<R$ and otherwise bids $\sigma(m')$. The win probability of $s$ is $P(m'<R\ \text{or}\ \sigma(m')<s)$ and the payoff is $P(\text{win})\cdot(\beta(m;R)-s)$. A strategy $\sigma$ is a **symmetric equilibrium** if every type $m\in[R,1]$ bids $\sigma(m)\ge R$ and no type gains by deviating to any bid $s\ge R$ when the rival plays $\sigma$.
--
--   These are the objects of Proposition 2 (double marginalization) and of the milestones that lead to it.
--
--   **Formalization Note** Integrals $\int g\,dF^k$ are written with the density $kF^{k-1}f$. $\lambda_m$ is `lam m` ($\lambda$ is reserved in Lean). The quotients in (3) and (13) divide by $F^3(v)$ and $F^2(m)$, which vanish only at $v=0$ or $m=0$ (possible only when $R=0$); Lean returns $0$ there, a single point that does not affect any integral. Ties in the header auction count as losses; they are null events under strictly increasing strategies.
-- source:
--   Zeithammer–Choi, Auctions of Auctions, Management Science (2024), doi:10.1287/mnsc.2024.05233, §2, p.7 (model, ψ, regularity, eq. (1)); §3.1, eqs. (3)–(5), pp.9–10; §3.2, eq. (8), p.11; §3.3, eqs. (10)–(13), pp.12–13; §4.1, eqs. (16), (18), pp.15–16; Proposition 1, eq. (19), p.16; App. A1.10, pp.42–43

import Mathlib

open MeasureTheory

namespace AuctionsOfAuctions

/-- **Valuation distribution** of the model, Zeithammer–Choi, *Auctions of Auctions*, Management
Science (2024), doi:10.1287/mnsc.2024.05233, §2, p.7 (PDF 8): the four advertisers' private
valuations are drawn independently from a distribution `F` with support `[0, 1]`.

The distribution is given by its density `f`: `f` is continuous on `[0, 1]`, nonnegative there,
strictly positive on the open interval `(0, 1)`, and integrates to `1` over `[0, 1]`. The
distribution function is `F x = ∫₀ˣ f` (`ValuationDist.F` below), so `F 0 = 0`, `F 1 = 1` and `F`
is strictly increasing on `[0, 1]`.

**Formalization Note.** This is the reading of "distribution `F` with support `[0, 1]`" that the
paper's computations use: it writes `f = F'`, divides by `f(x)` for `x ∈ (0, 1)` (virtual value,
hazard rates) and differentiates the revenue in the reserve price (proof of Proposition 1, (A18)),
which uses continuity of `f`. `f(0) = 0` and `f(1) = 0` are allowed. Values of `f` outside
`[0, 1]` play no role: every statement of the mission only evaluates `F` and `f` on `[0, 1]`. -/
structure ValuationDist where
  /-- the density `f` of a valuation -/
  f : ℝ → ℝ
  continuousOn_f : ContinuousOn f (Set.Icc 0 1)
  nonneg_f : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f x
  pos_f : ∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 < f x
  integral_f : ∫ x in (0 : ℝ)..1, f x = 1

namespace ValuationDist

variable (D : ValuationDist)

/-- **Distribution function** `F(x) = ∫₀ˣ f(t) dt` of a valuation (§2, p.7). -/
noncomputable def F (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, D.f t

/-- **Virtual value** `ψ(x) = x − (1 − F(x))/f(x)`, §2, p.7 (PDF 8).

**Formalization Note.** Only used for `x ∈ (0, 1)`, where `f(x) > 0`. -/
noncomputable def psi (x : ℝ) : ℝ := x - (1 - D.F x) / D.f x

/-- **Regularity**, §2, p.7 (PDF 8): "`F` is regular; i.e., the associated virtual value function
`ψ` … is increasing".

**Formalization Note.** "Increasing" is read as weakly increasing (`MonotoneOn`), the general
(Myerson) notion; the strict reading is a special case. It is required on the open interval
`(0, 1)`, where `ψ` is defined (`f > 0`). -/
def IsRegular : Prop := MonotoneOn D.psi (Set.Ioo 0 1)

/-- **Generalized hazard rate**, eq. (1), p.7 (PDF 8):
`λ_m(x) = m F^{m−1}(x) f(x) / (1 − F^m(x))`, `m ∈ {1, 2, …}`.

**Formalization Note.** Written `lam m x` because `λ` is reserved in Lean. `m` is a natural number
and statements use it only for `m ≥ 1` (so `m - 1` is the ordinary predecessor). The quotient is
meaningful for `x ∈ [0, 1)`; at `x = 1` the denominator is `0` and Lean returns `0`. -/
noncomputable def lam (m : ℕ) (x : ℝ) : ℝ :=
  (m : ℝ) * D.F x ^ (m - 1) * D.f x / (1 - D.F x ^ m)

/-- **Advertisers' equilibrium bid**, eq. (3), p.9 (PDF 10):
`β(v; R) = R F³(R)/F³(v) + (1/F³(v)) ∫_R^v x dF³(x)`, the symmetric equilibrium bid in a
first-price auction with reserve `R` and four bidders. By eq. (10), p.12, it is also the
advertisers' bid in the auction of auctions.

**Formalization Note.** `dF³(x)` is written with its density `3 F(x)² f(x) dx`. Used for
`R ≤ v ≤ 1`. The quotient divides by `F(v)³`, which vanishes only at `v = 0` (possible only when
`R = 0`); there Lean returns `0`, a single point that does not affect any integral. -/
noncomputable def beta (v R : ℝ) : ℝ :=
  (R * D.F R ^ 3 + ∫ x in R..v, x * (3 * D.F x ^ 2 * D.f x)) / D.F v ^ 3

/-- **Exchanges' equilibrium bid** in terms of the highest valuation `m` of the two advertisers an
exchange represents, eq. (13) of Lemma 2, p.13 (PDF 14):
`σ̃(m; R) = R F²(R)/F²(m) + (1/F²(m)) ∫_R^m β(y; R) dF²(y)`.

**Formalization Note.** `dF²(y)` is written with its density `2 F(y) f(y) dy`. Used for
`R ≤ m ≤ 1`; division by `F(m)² = 0` happens only at `m = 0` (when `R = 0`), where Lean returns
`0`. -/
noncomputable def sigmaTilde (m R : ℝ) : ℝ :=
  (R * D.F R ^ 2 + ∫ y in R..m, D.beta y R * (2 * D.F y * D.f y)) / D.F m ^ 2

/-- **Publisher revenue in the direct benchmark**, eq. (4), p.10 (PDF 11):
`π^dir_P(R) = ∫_R^1 β^dir(M; R) dF⁴(M)`, with `M` the highest of the four valuations (law `F⁴`).

**Formalization Note.** `dF⁴(M)` is written with its density `4 F(M)³ f(M) dM`. -/
noncomputable def revDir (R : ℝ) : ℝ :=
  ∫ M in R..1, D.beta M R * (4 * D.F M ^ 3 * D.f M)

/-- **Publisher revenue with a monopoly exchange**, eq. (8), p.11 (PDF 12):
`π^mono_P(R) = R (1 − F⁴(R))`. -/
noncomputable def revMono (R : ℝ) : ℝ := R * (1 - D.F R ^ 4)

/-- **Publisher revenue in the auction of auctions**, eq. (18), p.16 (PDF 17), with the exchanges'
bid `γ^ex = σ̃` of (13): `π^ex_P(R) = ∫_R^1 σ̃(M; R) dF⁴(M)`. The publisher faces two exchanges
whose types (highest valuation each represents) have law `F²`; their maximum `M` has law `F⁴`
(footnote 17, p.15).

**Formalization Note.** `dF⁴(M)` is written with its density `4 F(M)³ f(M) dM`. -/
noncomputable def revEx (R : ℝ) : ℝ :=
  ∫ M in R..1, D.sigmaTilde M R * (4 * D.F M ^ 3 * D.f M)

/-- **Advertiser's ex ante expected profit**, eq. (5), p.10 (PDF 11):
`π_C(R) = (1/4) ∫_R^1 (M − β^dir(M; R)) dF⁴(M)`.

By eq. (16), p.15 (PDF 16), the same function of the reserve gives the advertiser's profit in
every arrangement `A ∈ {dir, mono, ex}`: `π^A_C(R^A) = (1/4) ∫_{R^A}^1 (M − β^dir(M; R^A)) dF⁴(M)`.
(16) is the paper's statement that the exchange arrangement leaves the advertisers' allocation
and bids unchanged; the mission uses this one function for both arrangements.

**Formalization Note.** `dF⁴(M)` is written with its density `4 F(M)³ f(M) dM`. -/
noncomputable def advertiserProfit (R : ℝ) : ℝ :=
  (1 / 4) * ∫ M in R..1, (M - D.beta M R) * (4 * D.F M ^ 3 * D.f M)

/-- **Pseudo hazard rate**, eq. (19) of Proposition 1, p.16 (PDF 17):
`λ̃(x) = 2 F(x) f(x) / ([1 − F(x)][3 − F(x)])`. Used for `x ∈ [0, 1)`. -/
noncomputable def lamTilde (x : ℝ) : ℝ :=
  2 * D.F x * D.f x / ((1 - D.F x) * (3 - D.F x))

/-- **Exchange's probability of winning the header auction**, eqs. (11)–(12), pp.12–13
(PDF 13–14), in terms of types: the rival exchange's type `m'` (the highest valuation among its
two advertisers) has law `F²` on `[0, 1]`, with density `2 F(m') f(m')`. The rival stays out when
`m' < R` and otherwise bids `σ(m')`. A bid `s` wins if the rival stays out or bids strictly less:
`P(m' < R ∨ σ(m') < s) = ∫₀¹ 1{m' < R ∨ σ(m') < s} 2 F(m') f(m') dm'`.

**Formalization Note.** Ties count as losses; under a strictly increasing rival strategy (the
only case used) a tie is a single type, a null event. -/
noncomputable def exchangeWinProb (R : ℝ) (σ : ℝ → ℝ) (s : ℝ) : ℝ :=
  ∫ m' in (0 : ℝ)..1,
    Set.indicator {m' : ℝ | m' < R ∨ σ m' < s} (fun m' => 2 * D.F m' * D.f m') m'

/-- **Exchange's expected profit**, eq. (12), p.13 (PDF 14), in terms of types: an exchange of type
`m ∈ [R, 1]` receives its internal auction's winning bid `w = β(m; R)` from its advertiser and pays
its own header bid `s` when it wins: `U_σ(s, m) = P(win with s) · (β(m; R) − s)`. -/
noncomputable def exchangePayoff (R : ℝ) (σ : ℝ → ℝ) (s m : ℝ) : ℝ :=
  D.exchangeWinProb R σ s * (D.beta m R - s)

/-- **Symmetric equilibrium of the exchanges' header auction**, §3.3, (11)–(12), pp.12–13
(PDF 13–14), in terms of types (as in Lemma 2 and its proof, A1.10, pp.42–43): a strategy `σ`
mapping the exchange's type `m ∈ [R, 1]` to a header bid is a symmetric equilibrium if every type
bids at least the reserve and no type gains from deviating to any bid `s ≥ R` when the rival
exchange plays `σ`.

**Formalization Note.** Deviations to every real bid `s ≥ R` count, not only to the bids `σ(z)` of
other types; bids below the reserve are not admissible in the header auction. -/
def IsSymmetricEquilibrium (R : ℝ) (σ : ℝ → ℝ) : Prop :=
  ∀ m ∈ Set.Icc R 1, R ≤ σ m ∧
    ∀ s : ℝ, R ≤ s → D.exchangePayoff R σ s m ≤ D.exchangePayoff R σ (σ m) m

end ValuationDist

end AuctionsOfAuctions


