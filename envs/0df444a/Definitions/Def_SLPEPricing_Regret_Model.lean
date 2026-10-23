-- Prove2me | Definitions.Def_SLPEPricing_Regret_Model
-- name    : SLPEPricing_Regret_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:32:31.522594+00:00
-- url     : https://prove2.me/theorems/5231ef02-63b7-4000-827e-eb8d6547ecd0
-- title:
--   §2–§3, pp. 8–18 — the additive-noise demand model, Assumptions 1–2, the SLPE round schedule and price recursion (Algorithm 1 with d_est of p. 18), regret (4), LPC (5), the concentration event
-- statement:
--   This file sets up the dynamic pricing model and the SLPE policy of Perakis and Singhvi.
--
--   **Model (§2.1, p. 8).** A retailer charges prices $p_1,\dots,p_T$, normalised to the range $[p^L,p^U]=[0,1]$ (p. 10). The demand observed in period $t$ is
--   $$Y_t = d(p_t)+\epsilon_t,$$
--   where $d$ is an unknown demand curve and $\epsilon_t$ is a noise term. The revenue is $r(p)=p\,d(p)$, and $p^*$ is the revenue-maximising price.
--
--   **Standing hypotheses.** The bundle $\mathrm{Standing}(d,p^*,\kappa,K_1,c,\mu,\rho)$ collects the assumptions of Theorem 1 (pp. 10–12, 16–17):
--   1. $d$ is three times continuously differentiable, non-increasing and nonnegative on $[0,1]$;
--   2. $0<p^*<1$ and $p^*$ is the unique maximiser of $r$ on $[0,1]$;
--   3. **Assumption 1** with $\kappa>0$: $d(p^*)-\kappa(p-p^*)^2\le -d'(p)\,p^*$ for $p\in[-1,2]$;
--   4. $|d^{(k)}(p)|\le K_1$ for $k=0,1,2,3$ and $p\in[-1,2]$;
--   5. $c>0$ and the gradient condition $|d'(p^*)|\ge (K_1/24+\kappa/4)\cdot\tfrac14 + c/2$;
--   6. $\rho>0$ and $M\le\mu<2$, where
--   $$M=\frac1c\Big(\frac1{\rho^2}+\frac{K_1}6+\frac\kappa4\Big)+\frac{K_1}{12}+4\kappa \qquad\text{(Lemma 4, p. 17)}.$$
--
--   **Round schedule (Algorithm 1, p. 14).** Rounds are numbered $i=1,2,\dots$. The half-width of round $i$ is $\Delta_1=\tfrac12$, $\Delta_{i+1}=\mu\Delta_i^2$. Round $i$ charges each of three prices for
--   $$n_i=\Big\lceil \frac{2\rho^4\log T}{\Delta_i^4}\Big\rceil$$
--   periods, and starts at period $s_i=3\sum_{j<i}n_j$. Its blocks are $[s_i,s_i+n_i)$ (price $p^L_i$), $[s_i+n_i,s_i+2n_i)$ (price $p^M_i$) and $[s_i+2n_i,s_i+3n_i)$ (price $p^H_i$); periods at or after $T$ are not charged. Round $i$'s estimate is *used* if round $i+1$ starts before $T$, and $i_{\max}$ is the number of rounds that start before $T$.
--
--   **Price recursion.** $p^M_1=\tfrac12$, $p^L_i=p^M_i-\Delta_i$, $p^H_i=p^M_i+\Delta_i$ (so round 1 charges $0,\tfrac12,1$). After round $i$ the policy forms the piecewise linear estimate of p. 18,
--   $$d^{est}(p)=\begin{cases}\bar D(p^M)+\dfrac{D_{M_1^*}(p^M)-D_{L^*}(p^L)}{\Delta_i}(p-p^M), & p\le p^M,\\[2mm] \bar D(p^M)+\dfrac{D_{H^*}(p^H)-D_{M_2^*}(p^M)}{\Delta_i}(p-p^M), & p>p^M,\end{cases}$$
--   where $\bar D(p^M)$ is the average of the $n_i$ observations at $p^M_i$ and $D_{L^*},D_{M_1^*},D_{M_2^*},D_{H^*}$ are the observations at four periods $(a,b,b',c)$ chosen by a *pair selector*. It sets $\tilde p^*_i=\arg\max_{p\in[p^L_i,p^H_i]}p\,d^{est}(p)$ and $p^M_{i+1}=\tilde p^*_i$, so the next prices are $\tilde p^*_i\pm\mu\Delta_i^2$. The maximiser is returned by an *argmax selector*, any rule that returns a maximiser of a continuous function on a closed interval.
--
--   **Metrics (p. 9).** Regret (4) and the number of price changes (5):
--   $$R(T)=\sum_{t=1}^{T}\big(r(p^*)-r(p_t)\big),\qquad LPC(T)=1+\big|\{2\le t\le T:\ p_t\ne p_{t-1}\}\big|.$$
--
--   **Assumption 2 and the concentration event.** On a fixed noise realisation, Assumption 2 holds in round $i$ when the selected periods lie in the right blocks ($a$ in the $p^L$-block, $b,b'$ in the $p^M$-block, $c$ in the $p^H$-block) and $\epsilon_a=\epsilon_b$, $\epsilon_{b'}=\epsilon_c$ (two-point bandit feedback, p. 11). The concentration event of round $i$ (proof of Lemma 4, pp. 19–20) is
--   $$\big|\bar D_{n_i}(p^M_i)-d(p^M_i)\big|\le \Delta_i^2/\rho^2 .$$
--   `Assumption2` and `Concentration` require these in every used round.
--
--   Every later statement of the mission is phrased through these objects.
--
--   **Formalization Note** Periods are 0-based ($t=0,\dots,T-1$ is the paper's $t=1,\dots,T$); rounds are 1-based, as on the page; the unused index $0$ carries the junk values $\Delta_0=p^M_0=\tfrac12$. The noise is a single realisation $\epsilon:\mathbb N\to\mathbb R$, defined beyond $T$ so that the recursion is total; regret and LPC are numbers on that realisation, with no expectation. The policy (`policyCentre`) receives only the environment's response $p,t\mapsto d(p)+\epsilon_t$ at the prices it charges, $T,\mu,\rho$ and the two selectors; it never sees $d$, $p^*$, $\kappa$, $K_1$ or $c$ directly. The selectors are arbitrary inputs: the argmax selector is constrained by `IsArgmaxSelector` in the theorems, the pair selector by Assumption 2. A selected period outside round $i$'s blocks is read with round $i$'s block price (junk, excluded by Assumption 2). $n_i$ is rounded up ($n_i\ge1$ once $T\ge2$). $d$ is defined on all of $\mathbb R$ and Assumption 1 and the bound $K_1$ are imposed on $[-1,2]$, because Algorithm 1 can charge prices outside $[0,1]$ (e.g. $p^L_2=\tilde p^*_1-\mu/4<0$ when $\tilde p^*_1<\mu/4$); on the concentration event every charged price lies within $2\mu\Delta_1^2<1$ of $p^*$. $0<p^*<1$ is added (the paper says "strictly positive"), because the proofs use the first-order condition at $p^*$. $K_1$ is an upper bound rather than the maximum, which only strengthens the hypotheses on the constants. $i_{\max}$ counts rounds $i\in[1,T]$ with $s_i<T$, which is every round that charges a period once $n_j\ge1$.
-- source:
--   Perakis & Singhvi, Dynamic Pricing with Unknown Non-Parametric Demand and Limited Price Changes, SSRN 3336949 (PDF of 2020-07-03), pp. 8–18: (1)–(5) pp. 8–9, normalisation p. 10, Assumption 1 p. 10, Assumption 2 p. 11, standing assumptions p. 12, Algorithm 1 p. 14, d_est p. 18, Lemma 4's M p. 17, Theorem 1's gradient condition p. 16, concentration event pp. 19–20

import Mathlib

namespace SLPEPricing.Regret

/-! # Perakis & Singhvi, SSRN 3336949, §2–§3 (pp. 8–18): the additive-noise demand model, the
standing assumptions (Assumption 1, Theorem 1's gradient condition, `2 > μ ≥ M`), the SLPE round
schedule and price recursion (Algorithm 1, p. 14, with `d_est` of p. 18), regret (4), LPC (5),
Assumption 2 on a noise realisation, and the concentration event of Lemma 4's proof.

Periods are 0-based (`t = 0, …, T-1` is the paper's `t = 1, …, T`); rounds are 1-based
(`i = 1` is the first round, `Delta μ 1 = 1/2`). -/

/-- Revenue (2), p. 9: `r(p) = p d(p)`. -/
def r (d : ℝ → ℝ) (p : ℝ) : ℝ := p * d p

/-- Lemma 4's constant (p. 17): `M = (1/c)(1/ρ² + K₁/6 + κ/4) + K₁/12 + 4κ`. -/
noncomputable def Mconst (c ρ K₁ κ : ℝ) : ℝ := (1 / c) * (1 / ρ ^ 2 + K₁ / 6 + κ / 4) + K₁ / 12 + 4 * κ

/-- The standing hypotheses of Theorem 1 (pp. 10–12, 16–17), shared by every model statement.
`d` is the unknown demand, `pstar` the revenue-maximising price, `κ` the constant of
Assumption 1, `K₁` a bound on the derivatives of order `≤ 3`, `c` the constant of the gradient
condition, and `μ, ρ` the parameters of SLPE. -/
structure Standing (d : ℝ → ℝ) (pstar κ K₁ c μ ρ : ℝ) : Prop where
  /-- `d` is three times continuously differentiable ("w-differentiable", w ≥ 3). -/
  smooth : ContDiff ℝ 3 d
  /-- Demand is non-increasing on the price range `[0, 1]`. -/
  antitone : AntitoneOn d (Set.Icc 0 1)
  /-- Demand is nonnegative on the price range `[0, 1]`. -/
  nonneg : ∀ p ∈ Set.Icc (0 : ℝ) 1, 0 ≤ d p
  /-- The optimal price is strictly positive ... -/
  pstar_pos : 0 < pstar
  /-- ... and below the upper end of the price range. -/
  pstar_lt_one : pstar < 1
  /-- `pstar` is the unique maximiser of the revenue `r` on `[0, 1]`. -/
  unique_max : ∀ p ∈ Set.Icc (0 : ℝ) 1, p ≠ pstar → r d p < r d pstar
  /-- Assumption 1's constant is positive. -/
  kappa_pos : 0 < κ
  /-- Assumption 1 (p. 10), required on `[-1, 2]`. -/
  assumption1 : ∀ p ∈ Set.Icc (-1 : ℝ) 2, d pstar - κ * (p - pstar) ^ 2 ≤ -(deriv d p) * pstar
  /-- `K₁` bounds `|d^{(k)}|`, `k = 0, …, 3`, on `[-1, 2]`. -/
  K1_bound : ∀ k ≤ 3, ∀ p ∈ Set.Icc (-1 : ℝ) 2, |iteratedDeriv k d p| ≤ K₁
  /-- The constant of the gradient condition is positive. -/
  c_pos : 0 < c
  /-- Theorem 1's gradient condition `|d'(p*)| ≥ (K₁/24 + κ/4)·(1/4) + c/2`. -/
  gradient : (K₁ / 24 + κ / 4) * (1 / 4) + c / 2 ≤ |deriv d pstar|
  /-- The sample-size parameter is positive. -/
  rho_pos : 0 < ρ
  /-- `μ ≥ M`. -/
  mu_ge : Mconst c ρ K₁ κ ≤ μ
  /-- `μ < 2`. -/
  mu_lt : μ < 2

/-! ## The round schedule (deterministic; depends on `μ, ρ, T` only) -/

/-- Half-width `Δ_i` of round `i` (1-based): `Δ_1 = 1/2`, `Δ_{i+1} = μ Δ_i²`.
The value at the unused index `0` is also `1/2`. -/
noncomputable def Delta (μ : ℝ) : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | (i + 2) => μ * Delta μ (i + 1) ^ 2

/-- Number of periods `n_i = ⌈2ρ⁴ log(T)/Δ_i⁴⌉` spent at each of the three prices of round `i`. -/
noncomputable def nRound (μ ρ : ℝ) (T i : ℕ) : ℕ :=
  ⌈2 * ρ ^ 4 * Real.log (T : ℝ) / Delta μ i ^ 4⌉₊

/-- The 0-based period at which round `i` (1-based) starts: `3 ∑_{1 ≤ j < i} n_j`. -/
noncomputable def roundStart (μ ρ : ℝ) (T i : ℕ) : ℕ :=
  3 * ∑ j ∈ Finset.Ico 1 i, nRound μ ρ T j

/-- Round `i`'s estimate `p̃*_i` affects a charged price: round `i + 1` starts before `T`. -/
def UsedRound (μ ρ : ℝ) (T i : ℕ) : Prop :=
  roundStart μ ρ T (i + 1) < T

/-- The number of rounds that charge at least one period: `#{i ≥ 1 : roundStart i < T}`
(searched over `1 ≤ i ≤ T`, which contains every such round once `n_j ≥ 1`). -/
noncomputable def iMax (μ ρ : ℝ) (T : ℕ) : ℕ :=
  ((Finset.Icc 1 T).filter (fun i => roundStart μ ρ T i < T)).card

/-! ## The policy: it sees only `T, μ, ρ`, the two selectors, and the observations -/

/-- Price charged at period `t` by a round centred at `q` with half-width `Δ`, starting at period
`s`, with `n` periods per price: `q - Δ` on `[s, s+n)`, `q` on `[s+n, s+2n)`, `q + Δ` from
`s + 2n` on. -/
def blockPrice (q Δ : ℝ) (s n t : ℕ) : ℝ :=
  if t < s + n then q - Δ else if t < s + 2 * n then q else q + Δ

/-- The two-piece linear demand estimate `d_est` of p. 18, built from the average `avgM` of the
observations at `p^M = q` and the two two-point-feedback pairs `(yL, yM₁)`, `(yM₂, yH)`. -/
noncomputable def dest (Δ q avgM yL yM₁ yM₂ yH : ℝ) (p : ℝ) : ℝ :=
  if p ≤ q then avgM + (yM₁ - yL) / Δ * (p - q) else avgM + (yH - yM₂) / Δ * (p - q)

/-- An argmax selector: on every interval `[a, b]` it returns a maximiser of every function
continuous there. -/
def IsArgmaxSelector (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) : Prop :=
  ∀ (f : ℝ → ℝ) (a b : ℝ), a ≤ b → ContinuousOn f (Set.Icc a b) →
    amax f a b ∈ Set.Icc a b ∧ ∀ x ∈ Set.Icc a b, f x ≤ f (amax f a b)

/-- `p̃* = argmax_{p ∈ [q-Δ, q+Δ]} p · d_est(p)`, computed by the selector `amax`. -/
noncomputable def estimate (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ) (Δ q avgM yL yM₁ yM₂ yH : ℝ) : ℝ :=
  amax (fun p => p * dest Δ q avgM yL yM₁ yM₂ yH p) (q - Δ) (q + Δ)

/-- One update of SLPE. `Yfn p t` is the demand observed at period `t` when price `p` is charged
there (the environment's response). Round `i`, centred at `q`, charges `blockPrice` and reads:
the average of its `n_i` observations at `p^M`, and the four observations at the periods
`(a, b, b', c) = sel i` chosen by the pair selector. -/
noncomputable def roundUpdate (Yfn : ℝ → ℕ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (T i : ℕ) (q : ℝ) : ℝ :=
  let Δ := Delta μ i
  let s := roundStart μ ρ T i
  let n := nRound μ ρ T i
  let Y := fun t => Yfn (blockPrice q Δ s n t) t
  let avgM := (1 / (n : ℝ)) * ∑ t ∈ Finset.Ico (s + n) (s + 2 * n), Y t
  estimate amax Δ q avgM (Y (sel i).1) (Y (sel i).2.1) (Y (sel i).2.2.1) (Y (sel i).2.2.2)

/-- The centre `p^M_i` of round `i` (1-based) when the environment answers `Yfn`:
`p^M_1 = 1/2` and `p^M_{i+1} = p̃*_i`. The value at the unused index `0` is `1/2`. -/
noncomputable def policyCentre (Yfn : ℝ → ℕ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (T : ℕ) : ℕ → ℝ
  | 0 => 1 / 2
  | 1 => 1 / 2
  | (i + 2) => roundUpdate Yfn μ ρ amax sel T (i + 1) (policyCentre Yfn μ ρ amax sel T (i + 1))

/-! ## The model: demand `Y_t = d(p_t) + ε_t` on a noise realisation `ε : ℕ → ℝ` -/

/-- The centre `p^M_i` of round `i` in the model (1). -/
noncomputable def centre (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) (i : ℕ) : ℝ :=
  policyCentre (fun p t => d p + ε t) μ ρ amax sel T i

/-- `p^L_i = p^M_i - Δ_i`. -/
noncomputable def pL (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) : ℝ :=
  centre d μ ρ amax sel ε T i - Delta μ i

/-- `p^M_i`. -/
noncomputable def pM (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) : ℝ :=
  centre d μ ρ amax sel ε T i

/-- `p^H_i = p^M_i + Δ_i`. -/
noncomputable def pH (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) : ℝ :=
  centre d μ ρ amax sel ε T i + Delta μ i

/-- The estimated optimal price `p̃*_i` of round `i`. -/
noncomputable def ptilde (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) : ℝ :=
  centre d μ ρ amax sel ε T (i + 1)

/-- The demand at period `t` as recorded by round `i`: `d(p) + ε_t` with `p` round `i`'s block
price at `t`. For `t` in round `i`'s blocks this is the realised demand `Y_t` of (1). -/
noncomputable def roundObs (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i t : ℕ) : ℝ :=
  d (blockPrice (centre d μ ρ amax sel ε T i) (Delta μ i) (roundStart μ ρ T i)
    (nRound μ ρ T i) t) + ε t

/-- `D̄_{n_i}(p^M_i)`: the average of round `i`'s `n_i` demand observations at `p^M_i`. -/
noncomputable def avgM (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) : ℝ :=
  (1 / (nRound μ ρ T i : ℝ)) *
    ∑ t ∈ Finset.Ico (roundStart μ ρ T i + nRound μ ρ T i)
      (roundStart μ ρ T i + 2 * nRound μ ρ T i), roundObs d μ ρ amax sel ε T i t

/-- The round containing period `t`: the largest `i ≤ t + 1` with `roundStart i ≤ t`. -/
noncomputable def roundOf (μ ρ : ℝ) (T t : ℕ) : ℕ :=
  Nat.findGreatest (fun i => roundStart μ ρ T i ≤ t) (t + 1)

/-- The price `p_t` charged by SLPE at the 0-based period `t`. -/
noncomputable def price (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T t : ℕ) : ℝ :=
  blockPrice (centre d μ ρ amax sel ε T (roundOf μ ρ T t)) (Delta μ (roundOf μ ρ T t))
    (roundStart μ ρ T (roundOf μ ρ T t)) (nRound μ ρ T (roundOf μ ρ T t)) t

/-! ## Metrics (§2.2, p. 9) -/

/-- Regret (4): `R(T) = ∑_{t=1}^T (r(p*) - r(p_t))`, on one noise realisation. -/
noncomputable def regret (d : ℝ → ℝ) (pstar μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∑ t ∈ Finset.range T, (r d pstar - r d (price d μ ρ amax sel ε T t))

/-- Limited price changes (5): `LPC(T) = 1 + |{2 ≤ t ≤ T : p_t ≠ p_{t-1}}|` (1-based), i.e.
`1 + #{1 ≤ t < T : p_t ≠ p_{t-1}}` with 0-based periods. -/
noncomputable def lpc (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) : ℕ := by
  classical
  exact 1 + ((Finset.Ico 1 T).filter
    (fun t => price d μ ρ amax sel ε T t ≠ price d μ ρ amax sel ε T (t - 1))).card

/-! ## Assumption 2 and the concentration event, on a noise realisation -/

/-- Assumption 2 (p. 11) in round `i`: with `(a, b, b', c) = sel i`, period `a` lies in round
`i`'s `p^L`-block, `b, b'` in its `p^M`-block and `c` in its `p^H`-block, and the noise is equal
on each pair: `ε_a = ε_b` and `ε_{b'} = ε_c`. -/
def Assumption2At (μ ρ : ℝ) (T : ℕ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (i : ℕ) : Prop :=
  let s := roundStart μ ρ T i
  let n := nRound μ ρ T i
  (s ≤ (sel i).1 ∧ (sel i).1 < s + n) ∧
  (s + n ≤ (sel i).2.1 ∧ (sel i).2.1 < s + 2 * n) ∧
  (s + n ≤ (sel i).2.2.1 ∧ (sel i).2.2.1 < s + 2 * n) ∧
  (s + 2 * n ≤ (sel i).2.2.2 ∧ (sel i).2.2.2 < s + 3 * n) ∧
  ε (sel i).1 = ε (sel i).2.1 ∧ ε (sel i).2.2.1 = ε (sel i).2.2.2

/-- Assumption 2 in every round whose estimate is used. -/
def Assumption2 (μ ρ : ℝ) (T : ℕ) (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) : Prop :=
  ∀ i, 1 ≤ i → UsedRound μ ρ T i → Assumption2At μ ρ T sel ε i

/-- The concentration event of round `i` (proof of Lemma 4, pp. 19–20):
`|D̄_{n_i}(p^M_i) - d(p^M_i)| ≤ Δ_i²/ρ²`. -/
def ConcentrationAt (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T i : ℕ) : Prop :=
  |avgM d μ ρ amax sel ε T i - d (pM d μ ρ amax sel ε T i)| ≤ Delta μ i ^ 2 / ρ ^ 2

/-- The concentration event in every round whose estimate is used. -/
def Concentration (d : ℝ → ℝ) (μ ρ : ℝ) (amax : (ℝ → ℝ) → ℝ → ℝ → ℝ)
    (sel : ℕ → ℕ × ℕ × ℕ × ℕ) (ε : ℕ → ℝ) (T : ℕ) : Prop :=
  ∀ i, 1 ≤ i → UsedRound μ ρ T i → ConcentrationAt d μ ρ amax sel ε T i

end SLPEPricing.Regret


