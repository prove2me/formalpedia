-- Prove2me | Definitions.Def_RobustSPA_AllDist_Setting
-- name    : RobustSPA_AllDist_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T08:27:50.522811+00:00
-- url     : https://prove2.me/theorems/118e25e8-e819-4cd8-98bd-16090e751036
-- title:
--   §2, §3.2, §4.3, pp. 9–22 — DSIC mechanisms (IR), (IC), (AC), regret (2), minimax regret (3), 𝓕_all, 𝓕_exc, SPA with random reserve, the isorevenue law, Φ* and F* of Proposition 4
-- statement:
--   This file fixes the model of Anunrojwong, Balseiro and Besbes for $n$ buyers and one item, together with the two objects of Proposition 4.
--
--   **Valuations and mechanisms.** Buyers are indexed by $i \in \{1,\dots,n\}$ and have valuations $v = (v_1,\dots,v_n)$ in the **type cube** $[0,1]^n$. A (direct, possibly randomized) **mechanism** $m = (x, p)$ assigns to each report $v$ allocation probabilities $x_i(v)$ and payments $p_i(v)$. The class $\mathcal M$ of **DSIC mechanisms** (display (1)) consists of the mechanisms satisfying, for every $v \in [0,1]^n$ and every buyer $i$,
--
--   1. $x_i(v) \in [0,1]$;
--   2. (IR) $v_i x_i(v) - p_i(v) \ge 0$;
--   3. (IC) $v_i x_i(w, v_{-i}) - p_i(w, v_{-i}) \le v_i x_i(v) - p_i(v)$ for every misreport $w \in [0,1]$;
--   4. (AC) $\sum_i x_i(v) \le 1$;
--
--   and, in addition, $x_i$ and $p_i$ are measurable and the payments are bounded on $[0,1]^n$.
--
--   **Regret.** Writing $v^{(1)} = \max_i v_i$ and $v^{(2)}$ for the second-highest valuation, the **regret** of $m$ under a joint law $\mathbf F$ is (display (2))
--   $$\mathrm{Regret}(m, \mathbf F) = \mathbb E_{v \sim \mathbf F}\Big[v^{(1)} - \sum_{i=1}^n p_i(v)\Big],$$
--   and the **minimax regret** over a class $\mathcal F$ of laws is (display (3))
--   $$\mathcal R^*_n(\mathcal F) = \inf_{m \in \mathcal M}\ \sup_{\mathbf F \in \mathcal F} \mathrm{Regret}(m, \mathbf F).$$
--   $\mathcal F_{\mathrm{all}}$ is the class of all probability distributions on $[0,1]^n$, and $\mathcal F_{\mathrm{exc}} \subseteq \mathcal F_{\mathrm{all}}$ the **exchangeable** ones: those invariant under every permutation of the buyers (Definition 3).
--
--   **Second-price auction with random reserve.** For a reserve distribution $\Phi$ on $\mathbb R$, $\mathrm{SPA}(\Phi)$ draws a reserve $p \sim \Phi$, gives the item to a highest bidder if her bid is at least $p$, and charges her $\max(v^{(2)}, p)$. Averaging over $p$, the winner is allocated with probability $\Phi(v^{(1)})$ and pays $\mathbb E_{p \sim \Phi}[\max(v^{(2)}, p)\,\mathbf 1(v^{(1)} \ge p)]$; the other buyers get nothing and pay nothing.
--
--   **The objects of Proposition 4.** The **isorevenue** law on $[r, 1]$ has CDF $0$ below $r$, $1 - r/t$ on $[r, 1)$ and $1$ from $1$ on (an atom of mass $r$ at $1$); Proposition 4 uses $r = 1/e$. The reserve CDF
--   $$\Phi^*(p) = \begin{cases} 0 & p \le 1/e,\\ \log p + 1 & 1/e \le p \le 1,\\ 1 & p \ge 1,\end{cases}$$
--   and, for a law $G$ on $\mathbb R$, the mixture $\mathbf F^* = \frac1n \sum_{k=1}^n \mathbf F^{*,k}$, where $\mathbf F^{*,k}$ is the law of the vector $t\,e_k$ with $t \sim G$: buyer $k$ has value $t$ and every other buyer has value $0$.
--
--   These definitions are the common ground of every statement of the mission.
--
--   **Formalization Note** (IR), (IC), (AC) are imposed for types in $[0,1]^n$, the support the seller knows (p. 9). Measurability of $x_i, p_i$ and boundedness of the payments are added so that the expectation (2) is the Lebesgue expectation of a bounded measurable function; without them Lean's integral of a non-integrable payment is $0$. Ties for the highest bid are broken in favour of the lowest index (the paper breaks them "arbitrarily"; revenue does not depend on the rule). $v^{(2)}$ is the largest minimum over pairs of distinct buyers, which is $0$ when $n = 1$. Distributions are measures on $\mathbb R^n$; "supported on $[0,1]^n$" is "the complement of the cube is null". The CDF of a law $G$ on $\mathbb R$ is $t \mapsto G((-\infty, t])$. Proposition 4 prints $\Phi^*(p) = \log(v) + 1$; the definition uses $\log p + 1$.
-- source:
--   Anunrojwong, Balseiro & Besbes, On the Robustness of Second-Price Auctions in Prior-Independent Mechanism Design, arXiv:2204.10478v5, pp. 9–10 (IR), (IC), (AC), (1)–(3); p. 13 SPA with reserve; p. 16 §3.2 SPA(Φ); p. 22 §4.3 and Proposition 4; App-1 (F-IsoRevenue); Definition 3

import Mathlib

namespace RobustSPA.AllDist

open MeasureTheory
open scoped Classical

/-- The type cube `[0,1]ⁿ`. -/
def cube (n : ℕ) : Set (Fin n → ℝ) := Set.univ.pi fun _ => Set.Icc 0 1

/-- A direct mechanism for `n` buyers: allocation probabilities `x i v` and payments `p i v`. -/
structure Mechanism (n : ℕ) where
  x : Fin n → (Fin n → ℝ) → ℝ
  p : Fin n → (Fin n → ℝ) → ℝ

/-- The class `𝓜` of (1): (IR), (IC), (AC) on the type cube, plus measurability and bounded
payments (disclosed additions that make the expectation (2) meaningful). -/
structure Mechanism.IsDSIC {n : ℕ} (m : Mechanism n) : Prop where
  x_mem : ∀ v ∈ cube n, ∀ i, m.x i v ∈ Set.Icc (0 : ℝ) 1
  ir : ∀ v ∈ cube n, ∀ i, 0 ≤ v i * m.x i v - m.p i v
  ic : ∀ v ∈ cube n, ∀ i, ∀ w ∈ Set.Icc (0 : ℝ) 1,
    v i * m.x i (Function.update v i w) - m.p i (Function.update v i w) ≤ v i * m.x i v - m.p i v
  ac : ∀ v ∈ cube n, ∑ i, m.x i v ≤ 1
  meas_x : ∀ i, Measurable (m.x i)
  meas_p : ∀ i, Measurable (m.p i)
  p_bdd : ∃ B : ℝ, ∀ v ∈ cube n, ∀ i, |m.p i v| ≤ B

/-- The highest valuation `v^(1) = max v`. -/
noncomputable def top {n : ℕ} (v : Fin n → ℝ) : ℝ := ⨆ i, v i

/-- The second-highest valuation `v^(2)` (the largest minimum over pairs of distinct buyers;
`0` when `n = 1`). -/
noncomputable def second {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ⨆ q : {q : Fin n × Fin n // q.1 ≠ q.2}, min (v q.1.1) (v q.1.2)

/-- The regret (2): `E_{v∼μ}[max v − Σᵢ pᵢ(v)]`. -/
noncomputable def regret {n : ℕ} (m : Mechanism n) (μ : Measure (Fin n → ℝ)) : ℝ :=
  ∫ v, (top v - ∑ i, m.p i v) ∂μ

/-- The minimax regret (3): `inf_{m ∈ 𝓜} sup_{F ∈ 𝓕} Regret(m, F)`. -/
noncomputable def minimaxRegret (n : ℕ) (𝓕 : Set (Measure (Fin n → ℝ))) : ℝ :=
  ⨅ m : {m : Mechanism n // m.IsDSIC}, ⨆ μ : 𝓕, regret m.1 μ

/-- `𝓕_all`: all probability distributions supported on `[0,1]ⁿ`. -/
def Fall (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | IsProbabilityMeasure μ ∧ μ (cube n)ᶜ = 0}

/-- `𝓕_exc` (Definition 3): the exchangeable distributions in `𝓕_all`. -/
def Fexc (n : ℕ) : Set (Measure (Fin n → ℝ)) :=
  {μ | μ ∈ Fall n ∧ ∀ σ : Equiv.Perm (Fin n), μ.map (fun v => v ∘ σ) = μ}

/-- The CDF of a law on `ℝ`. -/
noncomputable def cdfOf (G : Measure ℝ) (t : ℝ) : ℝ := (G (Set.Iic t)).toReal

/-- Buyer `i` wins: a highest bid, ties broken in favour of the lowest index. -/
def isWinner {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : Prop :=
  (∀ j, v j ≤ v i) ∧ ∀ j, j < i → v j < v i

/-- `SPA(ρ)`: second-price auction with random reserve `q ∼ ρ`. The winner is allocated with
probability `ρ((-∞, v_i])` and pays `E_{q∼ρ}[max(v^(2), q) 1(v_i ≥ q)]`. -/
noncomputable def SPA {n : ℕ} (ρ : Measure ℝ) : Mechanism n where
  x i v := if isWinner v i then (ρ (Set.Iic (v i))).toReal else 0
  p i v := if isWinner v i then
    ∫ q, (Set.Iic (v i)).indicator (fun q => max (second v) q) q ∂ρ else 0

/-- The CDF of the isorevenue law on `[r, 1]` (F-IsoRevenue): `0` below `r`, `1 − r/t` on
`[r, 1)`, and `1` from `1` on (an atom of mass `r` at `1`). -/
noncomputable def isoCDF (r t : ℝ) : ℝ := if t < r then 0 else if t < 1 then 1 - r / t else 1

/-- The reserve CDF `Φ*` of Proposition 4: `0` on `(-∞, 1/e]`, `log v + 1` on `[1/e, 1]`,
`1` above `1`. -/
noncomputable def PhiE (v : ℝ) : ℝ :=
  if v ≤ Real.exp (-1) then 0 else if v ≤ 1 then Real.log v + 1 else 1

/-- `F* = (1/n) Σ_k F*,k`, where `F*,k` is the law of `t · e_k` with `t ∼ G`
(buyer `k` has value `t ∼ G`, every other buyer has value `0`). -/
noncomputable def Fstar (n : ℕ) (G : Measure ℝ) : Measure (Fin n → ℝ) :=
  (n : ENNReal)⁻¹ • ∑ k : Fin n, G.map (fun t => (Pi.single k t : Fin n → ℝ))

end RobustSPA.AllDist


