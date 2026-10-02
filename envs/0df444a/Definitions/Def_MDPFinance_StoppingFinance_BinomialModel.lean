-- Prove2me | Definitions.Def_MDPFinance_StoppingFinance_BinomialModel
-- name    : MDPFinance_StoppingFinance_BinomialModel
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T23:47:32.336301+00:00
-- url     : https://prove2.me/theorems/7378f46c-0316-4736-a903-52a49d0eaf7a
-- title:
--   The binomial model, the American put recursion and the perpetual option's value
-- statement:
--   The data of §11.1. The stock follows the **binomial model** of Chapter 3: from a price
--   $x$ it moves to $xu$ with the risk-neutral probability $q$ and to $xd$ with $1-q$, where
--   $0 < d < u$, the discount factor is $\beta \in (0,1]$ and $q \in (0,1)$. The book's own relation
--
--   $$ \beta q u + \beta (1-q) d = 1 $$
--
--   ("by definition of $q$ we have $\beta qu + \beta(1-q)d = 1$", proof of Proposition 11.1.2 b) is
--   carried as a field of the model, not derived: it is what makes the discounted stock price a
--   martingale under $\mathbb{Q}$, and the proof of Proposition 11.1.2 b) uses it directly.
--
--   The **American put** with strike $K$ pays $(K-x)^+$ on exercise. Its price with $n$ periods to
--   maturity is given by the recursion
--
--   $$ J_0(x) = (K-x)^+, \qquad J_n(x) = \max\Big\{(K-x)^+,\ \beta\big(q J_{n-1}(xu) + (1-q)J_{n-1}(xd)\big)\Big\}, $$
--
--   and $\pi_n(x) := J_{N-n}(x)$ is the price at time $n$ when the option matures at $N$. The
--   right-hand side is the operator
--
--   $$ \mathcal{T}P(x) := \max\Big\{(K-x)^+,\ \beta\big(qP(xu) + (1-q)P(xd)\big)\Big\}, $$
--
--   written for the **two-point binomial kernel** rather than a general transition kernel $Q$: the
--   book's proof and the explicit $qP(xu) + (1-q)P(xd)$ form both depend on the binomial structure.
--   $P$ is **superharmonic** when $P(x) \ge \beta(qP(xu) + (1-q)P(xd))$ for $x \in E$.
--
--   For the **perpetual** option the stopping-time side is built rather than assumed, because
--   Theorem 11.1.3 a) *is* the identification of
--
--   $$ P(x) := \sup_{\tau \le \infty} \mathbb{E}^{\mathbb{Q}}_x\big[\beta^\tau (K - S_\tau)\big] $$
--
--   with $\lim_n J_n(x)$, and carrying $P$ as an abstract function would make that vacuous. The stock
--   path is $S_0 = x$, $S_{n+1} = S_n \cdot u$ or $S_n \cdot d$ according to the $n$-th coordinate of
--   $\omega \in \{\text{up},\text{down}\}^{\mathbb{N}}$; its law $\mathbb{Q}$ is pinned by its
--   finite-dimensional distributions (i.i.d. up-moves with probability $q$), which determine it on
--   the cylinder sets that generate the product $\sigma$-field — no infinite product measure needs to
--   be constructed. A stopping time takes values in $\mathbb{N} \cup \{\infty\}$, since the supremum
--   is over $\tau \le \infty$, and "the stopping reward for $\tau = \infty$ is equal to zero"
--   (p. 337), so the reward $\beta^\tau(K-S_\tau)$ is defined to vanish there. Finally
--   $\tau^* := \inf\{n \in \mathbb{N}_0 \mid X_n \in E^*\}$ is the exercise time of an exercise region
--   $E^*$, with $\inf \emptyset = \infty$.
--
--   **Moderation note.** The perpetual price was carried as a free function pinned by `IsLUB` against Bochner-integrable rewards; now `P(x) := sup_τ 𝔼^ℚ_x[β^τ(K − S_τ)]` and the maturity-`N` price `sup_{τ ≤ N} 𝔼^ℚ_x[β^τ(K − S_τ)⁺]` are `[-∞,∞]`-valued suprema over stopping times, `J := lim_n J_n` and `J_{f^*} := lim_n 𝒯_{f^*}^n 0` are the model's own limits (of increasing sequences bounded by `K`), and the threshold exercise time of Proposition 11.1.2 d) is defined. The binomial data, recursion, path law and stopping times are as drafted.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, §11.1, pp. 336-337 (PDF 344-345)

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal

namespace MDPFinance.StoppingFinance

/-- The `[-∞,∞]`-valued integral `∫ v⁺ − ∫ v⁻` (with `∞ − ∞ = −∞`), used for expected rewards so
that no real integral silently returns `0`. -/
noncomputable def erealIntegral {α : Type*} [MeasurableSpace α] (μ : Measure α) (v : α → EReal) :
    EReal :=
  ((∫⁻ a, (v a ⊔ 0).toENNReal ∂μ : ℝ≥0∞) : EReal) + (-((∫⁻ a, ((-v a) ⊔ 0).toENNReal ∂μ : ℝ≥0∞) : EReal))

/-- The binomial model of Chapter 3 as §11.1 uses it (p. 331, 336): up/down factors `d < u`,
`d > 0`, discount `β = (1+i)^{-1} ∈ (0,1]`, risk-neutral probability `q ∈ (0,1)` with
`βqu + β(1−q)d = 1` (equivalently `d < 1+i < u`, (11.1)), strike `K > 0`, and a state space `E`
of positive prices closed under the moves. -/
structure BinomialModel where
  u : ℝ
  d : ℝ
  beta : ℝ
  q : ℝ
  K : ℝ
  E : Set ℝ
  d_lt_u : d < u
  d_pos : 0 < d
  beta_mem : beta ∈ Set.Ioc (0 : ℝ) 1
  q_mem : q ∈ Set.Ioo (0 : ℝ) 1
  K_pos : 0 < K
  E_pos : ∀ x ∈ E, 0 < x
  E_up : ∀ x ∈ E, x * u ∈ E
  E_down : ∀ x ∈ E, x * d ∈ E
  riskNeutral : beta * q * u + beta * (1 - q) * d = 1

/-- `(K − x)⁺`. -/
noncomputable def BinomialModel.payoff (M : BinomialModel) (x : ℝ) : ℝ := max (M.K - x) 0

/-- `𝒯P(x) = max{(K − x)⁺, β(qP(xu) + (1−q)P(xd))}` (p. 337). -/
noncomputable def BinomialModel.T (M : BinomialModel) (P : ℝ → ℝ) (x : ℝ) : ℝ :=
  max (M.payoff x) (M.beta * (M.q * P (x * M.u) + (1 - M.q) * P (x * M.d)))

/-- `J_0(x) = (K − x)⁺`, `J_n(x) = max{(K − x)⁺, β(qJ_{n−1}(xu) + (1−q)J_{n−1}(xd))}` (p. 336). -/
noncomputable def BinomialModel.J (M : BinomialModel) : ℕ → ℝ → ℝ
  | 0 => M.payoff
  | (n + 1) => M.T (M.J n)

/-- `π_n(x) := J_{N−n}(x)`, the price of the American put at time `n` with maturity `N`. -/
noncomputable def BinomialModel.price (M : BinomialModel) (N n : ℕ) (x : ℝ) : ℝ :=
  M.J (N - n) x

/-- `J := lim_n J_n`, the limit of the increasing sequence `0 ≤ J_n ≤ K` (p. 337). -/
noncomputable def BinomialModel.Jlim (M : BinomialModel) (x : ℝ) : ℝ := ⨆ n, M.J n x

/-- `P` is **superharmonic**: `P(x) ≥ β(qP(xu) + (1−q)P(xd))` for `x ∈ E`. -/
def BinomialModel.Superharmonic (M : BinomialModel) (P : ℝ → ℝ) : Prop :=
  ∀ x ∈ M.E, M.beta * (M.q * P (x * M.u) + (1 - M.q) * P (x * M.d)) ≤ P x

open Classical in
/-- `𝒯_{f^*}` for the exercise rule `f^* = 1_{E^*}`: exercise on `E^*`, continue off it. -/
noncomputable def BinomialModel.Tf (M : BinomialModel) (Estar : Set ℝ) (g : ℝ → ℝ) (y : ℝ) : ℝ :=
  if y ∈ Estar then M.payoff y else M.beta * (M.q * g (y * M.u) + (1 - M.q) * g (y * M.d))

/-- `J_{f^*} := lim_n 𝒯_{f^*}^n 0` (p. 337), the limit of an increasing sequence bounded by `K`. -/
noncomputable def BinomialModel.JfStar (M : BinomialModel) (Estar : Set ℝ) (x : ℝ) : ℝ :=
  ⨆ n, ((M.Tf Estar)^[n] (fun _ => 0)) x

/-- The stock path: `S_0 = x`, each step multiplies by `u` or `d` according to `ω ∈ {up,down}^ℕ`. -/
noncomputable def BinomialModel.stock (M : BinomialModel) (x : ℝ) : ℕ → (ℕ → Bool) → ℝ
  | 0, _ => x
  | (n + 1), w => M.stock x n w * (if w n then M.u else M.d)

/-- The risk-neutral law `ℚ` of the moves: i.i.d. up moves with probability `q`, pinned by its
finite-dimensional distributions. -/
def BinomialModel.IsPathLaw (M : BinomialModel) (Q : Measure (ℕ → Bool)) : Prop :=
  IsProbabilityMeasure Q ∧
  ∀ (n : ℕ) (b : Fin n → Bool),
    Q {w : ℕ → Bool | ∀ i : Fin n, w (i : ℕ) = b i}
      = ∏ i : Fin n, (if b i then ENNReal.ofReal M.q else ENNReal.ofReal (1 - M.q))

/-- `τ` is a **stopping time** of the stock path: `{τ = n}` is decided by the first `n` moves
(a finite-coordinate event, hence measurable). Values in `ℕ∞`. -/
def IsStoppingTime (tau : (ℕ → Bool) → ℕ∞) : Prop :=
  ∀ (n : ℕ) (w w' : ℕ → Bool), (∀ i < n, w i = w' i) → (tau w = (n : ℕ∞) ↔ tau w' = (n : ℕ∞))

/-- `β^τ (K − S_τ)`, zero on `{τ = ∞}` (p. 337). -/
noncomputable def BinomialModel.reward (M : BinomialModel) (x : ℝ) (tau : (ℕ → Bool) → ℕ∞)
    (w : ℕ → Bool) : ℝ :=
  match tau w with
  | (n : ℕ) => M.beta ^ n * (M.K - M.stock x n w)
  | ⊤ => 0

/-- `β^τ (K − S_τ)⁺`, the finite-horizon exercise payoff (p. 332), zero on `{τ = ∞}`. -/
noncomputable def BinomialModel.rewardPlus (M : BinomialModel) (x : ℝ) (tau : (ℕ → Bool) → ℕ∞)
    (w : ℕ → Bool) : ℝ :=
  match tau w with
  | (n : ℕ) => M.beta ^ n * M.payoff (M.stock x n w)
  | ⊤ => 0

/-- `𝔼^ℚ_x[β^τ (K − S_τ)]` in `[-∞,∞]`. -/
noncomputable def BinomialModel.EReward (M : BinomialModel) (Q : Measure (ℕ → Bool)) (x : ℝ)
    (tau : (ℕ → Bool) → ℕ∞) : EReal :=
  erealIntegral Q (fun w => (M.reward x tau w : EReal))

noncomputable def BinomialModel.ERewardPlus (M : BinomialModel) (Q : Measure (ℕ → Bool)) (x : ℝ)
    (tau : (ℕ → Bool) → ℕ∞) : EReal :=
  erealIntegral Q (fun w => (M.rewardPlus x tau w : EReal))

/-- `P(x) := sup_{τ ≤ ∞} 𝔼^ℚ_x[β^τ (K − S_τ)]`, the price of the perpetual American put (p. 337). -/
noncomputable def BinomialModel.perpetualValue (M : BinomialModel) (Q : Measure (ℕ → Bool))
    (x : ℝ) : EReal :=
  ⨆ tau : (ℕ → Bool) → ℕ∞, ⨆ (_ : IsStoppingTime tau), M.EReward Q x tau

/-- `sup_{τ ≤ N} 𝔼^ℚ_x[β^τ (K − S_τ)⁺]`, the price of the American put with maturity `N`
(p. 332). -/
noncomputable def BinomialModel.finiteValue (M : BinomialModel) (Q : Measure (ℕ → Bool)) (N : ℕ)
    (x : ℝ) : EReal :=
  ⨆ tau : (ℕ → Bool) → ℕ∞, ⨆ (_ : IsStoppingTime tau ∧ ∀ w, tau w ≤ (N : ℕ∞)),
    M.ERewardPlus Q x tau

/-- `τ^* := inf{n ∈ ℕ₀ | S_n ∈ E^*}` (`inf ∅ = ∞`). -/
noncomputable def BinomialModel.exerciseTime (M : BinomialModel) (x : ℝ) (Estar : Set ℝ)
    (w : ℕ → Bool) : ℕ∞ :=
  sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | M.stock x k w ∈ Estar})

/-- `τ^* := inf{n ∈ {0,…,N} | S_n ≤ x^*_n}` (Proposition 11.1.2 d)), capped at `N`. -/
noncomputable def BinomialModel.thresholdTime (M : BinomialModel) (x : ℝ) (xstar : ℕ → ℝ) (N : ℕ)
    (w : ℕ → Bool) : ℕ∞ :=
  min (sInf ((fun k : ℕ => (k : ℕ∞)) '' {k : ℕ | M.stock x k w ≤ xstar k})) (N : ℕ∞)

end MDPFinance.StoppingFinance


