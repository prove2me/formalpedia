-- Prove2me | Definitions.Def_MDPFinance_InfiniteHorizonApplications_Bandit
-- name    : MDPFinance_InfiniteHorizonApplications_Bandit
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-27T22:59:23.96151+00:00
-- url     : https://prove2.me/theorems/8843f80c-b0ab-4d1f-9cc9-4d4ef02c1004
-- title:
--   The K-stopping problem, the Gittins index (Definition 7.6.5), and the two-arm joint value
-- statement:
--   For a single Beta-Bernoulli bandit arm with posterior mean success probability $p(m,n) :=
--   (m+1)/(m+n+2)$ and Bayes-update operator $(Pv)(m,n) := p(m,n)v(m+1,n) + (1-p(m,n))v(m,n+1)$
--   (restated from chunk `05b`'s identical model, kept the same in substance per this series'
--   file-ownership boundary), the **`K`-stopping problem** asks: pull the arm and continue, or quit
--   now and collect a fixed reward $K$. Its value function $J(m,n;K)$ solves $v(m,n) = \max\{K,
--   p(m,n)+\beta(Pv)(m,n)\}$ — bundled as data satisfying this defining fixed-point equation, since
--   no finite recursion computes it directly. The **Gittins index** $I(m,n) := \min\{K \mid
--   J(m,n;K)=K\}$ (Definition 7.6.5) is the smallest quit-reward at which quitting immediately is
--   already optimal — the single number, computed from arm $(m,n)$'s own data alone, that later lets
--   the two-arm bandit be solved by comparing indices rather than searching a joint state space. The
--   two-arm joint value $\tilde J(x;K)$ (three actions: pull arm 1, pull arm 2, or quit for $K$) and
--   the true two-arm bandit value $J_\infty$ (a fixed point of chunk `07a`'s contracting theory,
--   applied to this model, restated here rather than re-derived) are built the same way.
--
--   **Moderation note.** Several changes. (1) The $K$-stopping value, the joint value and the bandit value are the *bounded* solutions of their fixed-point equations (`hJ_bdd` etc.), with $\beta\in(0,1)$ as fields: the equations also have unbounded solutions ($v+C\beta^{-(m+n)}$ solves $v=p+\beta Pv$), for which the draft's `sInf` defining the index is a default value and the theorems fail. (2) The single-arm problem is parametrized by the arm's success-probability function $q$, so that Corollary 7.6.8(d) (known success probability $p_0$) is a genuine instance rather than a vacuous clause. (3) The expectations of Theorem 7.6.6 are now defined (`EStop`: discounted sums over outcome prefixes weighted by the predictive law; `statesOf`, `prefixProb`), and $\tau^*$ is defined (`tauStar`, with $n\ge 1$); the draft took the expectations as unconstrained data and its $\tau^*$ ranged over $n\ge 0$, hence was always $0$ and contradicted $\tau^*\ge 1$. (4) `banditVpi` gives the value of a stationary policy, needed to state optimality in Theorem 7.6.10.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 230-231, §7.6.4-7.6.5, Definition 7.6.5 and model data

import Mathlib

open MeasureTheory ProbabilityTheory

namespace MDPFinance.InfiniteHorizonApplications

/-- `p(m,n) := (m+1)/(m+n+2)`, the posterior mean success probability of a Beta-Bernoulli arm
after `m` successes and `n` failures (Bäuerle–Rieder, §5.5, restated in this chunk's own
namespace per the file-ownership boundary — the same Beta-conjugate model as chunk `05b`'s
`p1B`/`p2B`, kept identical in substance). -/
noncomputable def pMN (mn : ℕ × ℕ) : ℝ := (mn.1 + 1) / (mn.1 + mn.2 + 2)

/-- `(P_q v)(m,n) := q(m,n)v(m+1,n) + (1-q(m,n))v(m,n+1)`, the one-step expectation operator of a
single arm with success probability `q(m,n)` in state `(m,n)` (`q = p` for the Beta-Bernoulli arm,
`q ≡ p_0` for an arm with known success probability, Corollary 7.6.8(d)). -/
noncomputable def PQ (q : ℕ × ℕ → ℝ) (v : ℕ × ℕ → ℝ) (mn : ℕ × ℕ) : ℝ :=
  q mn * v (mn.1 + 1, mn.2) + (1 - q mn) * v (mn.1, mn.2 + 1)

/-- `(Pv)(m,n) := p(m,n)v(m+1,n) + (1-p(m,n))v(m,n+1)`, the one-step Bayes-update expectation
operator for a single arm (Bäuerle–Rieder, §5.5, restated — matches chunk `05b`'s `Q1B`/`Q2B`
shape specialized to one arm). -/
noncomputable def PMN (v : ℕ × ℕ → ℝ) (mn : ℕ × ℕ) : ℝ :=
  PQ pMN v mn

/-- The **`K`-stopping value function** `J(\cdot;K)`, bundled as *data* satisfying its own
defining fixed-point equation `v(m,n) = \max\{K, p(m,n)+\beta(Pv)(m,n)\}` (Bäuerle–Rieder, p.
231, PDF 242) — the same "data satisfying a defining formula" convention this series uses
throughout for an object characterized as *the* solution of a fixed-point equation, rather than
built by an explicit recursion (there is none here: the horizon is infinite and the equation is
not, in general, a contraction uniformly in `K`); bounded, so that it is *the* value function
(the unique bounded solution, `β ∈ (0,1)`). Parametrized by the arm's success-probability
function `q` (`q = p` for the Beta-Bernoulli arm). -/
structure KStoppingValue (β : ℝ) (q : ℕ × ℕ → ℝ) where
  hβ0 : 0 < β
  hβ1 : β < 1
  hq : ∀ mn, 0 ≤ q mn ∧ q mn ≤ 1
  J : ℝ → ℕ × ℕ → ℝ
  /-- `J(·;K)` is bounded: the fixed-point equation has a *unique bounded* solution (Banach,
  `β < 1`), but also unbounded ones (`v + C β^{-(m+n)}` solves `v = q + β P_q v`), which are not
  the value function. -/
  hJ_bdd : ∀ K, ∃ C : ℝ, ∀ mn, |J K mn| ≤ C
  hJ_fix : ∀ K mn, J K mn = max K (q mn + β * PQ q (J K) mn)

/-- The **Gittins index** `I(m,n) := \min\{K \in ℝ \mid J(m,n;K) = K\}` (Bäuerle–Rieder,
Definition 7.6.5, p. 231, PDF 242), rendered via `sInf` (real infimum, total/junk-safe if the
defining set were empty or unbounded below — Corollary 7.6.8c shows it is neither: the set is
bounded below by `p(m,n)/(1-\beta)` and, by Proposition 7.6.7's continuity of `K \mapsto
J(m,n;K)`, the infimum is attained, matching the book's own `\min`). -/
noncomputable def GittinsIndex {β : ℝ} {q : ℕ × ℕ → ℝ} (KS : KStoppingValue β q) (mn : ℕ × ℕ) :
    ℝ :=
  sInf {K : ℝ | KS.J K mn = K}

/-- The two-arm bandit's state space `ℕ_0^2 \times ℕ_0^2`. -/
abbrev BanditState2 := (ℕ × ℕ) × (ℕ × ℕ)

/-- `(Q_1v)(x) := p(m_1,n_1)v((m_1+1,n_1),(m_2,n_2)) + (1-p(m_1,n_1))v((m_1,n_1+1),(m_2,n_2))`,
the Bayes-update expectation operator for pulling arm `1` of the two-arm bandit (Bäuerle–Rieder,
p. 230, PDF 241, restated from chunk `05b`'s two-arm `Q1B`). -/
noncomputable def Q1Bandit (v : BanditState2 → ℝ) (x : BanditState2) : ℝ :=
  pMN x.1 * v ((x.1.1 + 1, x.1.2), x.2) + (1 - pMN x.1) * v ((x.1.1, x.1.2 + 1), x.2)

/-- `(Q_2v)(x)`, the analogous operator for arm `2`. -/
noncomputable def Q2Bandit (v : BanditState2 → ℝ) (x : BanditState2) : ℝ :=
  pMN x.2 * v (x.1, (x.2.1 + 1, x.2.2)) + (1 - pMN x.2) * v (x.1, (x.2.1, x.2.2 + 1))

/-- `p_a(x)`, the posterior mean success probability of arm `a \in \{1,2\}` at state `x`. -/
noncomputable def paBandit (a : Fin 2) (x : BanditState2) : ℝ :=
  if a = 0 then pMN x.1 else pMN x.2

/-- `Q_a`, the Bayes-update operator for arm `a \in \{1,2\}`. -/
noncomputable def QaBandit (a : Fin 2) (v : BanditState2 → ℝ) (x : BanditState2) : ℝ :=
  if a = 0 then Q1Bandit v x else Q2Bandit v x

/-- The **two-arm joint `K`-stopping value function** `\tilde J(\cdot;K)`, bundled as data
satisfying `\tilde J(x;K) = \max\{K,\max_a[p_a(x)+\beta(Q_a\tilde J)(x;K)]\}` (Bäuerle–Rieder, p.
233, PDF 244), the two-arm analogue of `KStoppingValue`. -/
structure JointKStoppingValue (β : ℝ) where
  hβ0 : 0 < β
  hβ1 : β < 1
  Jt : ℝ → BanditState2 → ℝ
  hJt_bdd : ∀ K, ∃ C : ℝ, ∀ x, |Jt K x| ≤ C
  hJt_fix : ∀ K x, Jt K x = max K (max (paBandit 0 x + β * QaBandit 0 (Jt K) x)
    (paBandit 1 x + β * QaBandit 1 (Jt K) x))

/-- The infinite-horizon two-arm bandit's own value function `J_\infty`, bundled as data
satisfying its own Bellman equation `v(x) = \max\{p_1(x)+\beta Q_1v(x), p_2(x)+\beta Q_2v(x)\}`
(Bäuerle–Rieder, p. 230, PDF 241, established via chunk `07a`'s Theorem 7.3.5 applied to this
contracting model — restated here as the fixed-point characterization that theorem yields, not
re-derived). -/
structure BanditValue (β : ℝ) where
  hβ0 : 0 < β
  hβ1 : β < 1
  Jinf : BanditState2 → ℝ
  hJinf_bdd : ∃ C : ℝ, ∀ x, |Jinf x| ≤ C
  hJinf_fix : ∀ x, Jinf x = max (paBandit 0 x + β * QaBandit 0 Jinf x)
    (paBandit 1 x + β * QaBandit 1 Jinf x)

/-- The value `V_n^f(x)` of the stationary policy `f^∞` of the two-arm bandit over `n` stages
(the reward iteration with `r(x,a) = p_a(x)`). -/
noncomputable def banditVpi (β : ℝ) (f : BanditState2 → Fin 2) : ℕ → BanditState2 → ℝ
  | 0, _ => 0
  | (n + 1), x => paBandit (f x) x + β * QaBandit (f x) (banditVpi β f n) x

/-- The states `X_k` of one arm along an outcome sequence `w` (`true` = success), started at
`i_0`: a success moves `(m,n) ↦ (m+1,n)`, a failure `(m,n) ↦ (m,n+1)`. -/
def statesOf (i0 : ℕ × ℕ) (w : ℕ → Bool) : ℕ → ℕ × ℕ
  | 0 => i0
  | (k + 1) =>
      let x := statesOf i0 w k
      if w k then (x.1 + 1, x.2) else (x.1, x.2 + 1)

/-- The probability of the first `k` outcomes `w_0, …, w_{k-1}` under the arm's predictive law
(`ℙ(success | X_j) = p(X_j)`), started at `i_0`. -/
noncomputable def prefixProb (i0 : ℕ × ℕ) (w : ℕ → Bool) (k : ℕ) : ℝ :=
  ∏ j ∈ Finset.range k,
    (if w j then pMN (statesOf i0 w j) else 1 - pMN (statesOf i0 w j))

/-- A finite outcome prefix, extended by failures (irrelevant for adapted quantities). -/
def extendPrefix {k : ℕ} (w : Fin k → Bool) : ℕ → Bool :=
  fun j => if h : j < k then w ⟨j, h⟩ else false

/-- A **stopping time** for the state process `(X_k)` of one arm, represented as a function
`τ : (ℕ → ℕ × ℕ) → ℕ∞` of the whole state path, adapted in the sense that whether `τ ≤ n`
depends only on the path up to `n`. -/
def IsStoppingTime (τ : (ℕ → ℕ × ℕ) → ℕ∞) : Prop :=
  ∀ n : ℕ, ∀ x y : ℕ → ℕ × ℕ, (∀ k ≤ n, x k = y k) → (τ x ≤ n ↔ τ y ≤ n)

/-- `τ ≥ 1` everywhere. -/
def IsPositiveStoppingTime (τ : (ℕ → ℕ × ℕ) → ℕ∞) : Prop :=
  ∀ x, 1 ≤ τ x

/-- `𝔼_{i_0}[Σ_{k=0}^{τ-1} β^k g(X_k)]` for a stopping time `τ` of the arm's state process started
at `i_0`: the sum over `k` of `β^k` times the expectation of `g(X_k) 1_{τ > k}`, the latter a
finite sum over the `2^k` outcome prefixes weighted by their probabilities (`{τ > k}` depends
only on the first `k` states). -/
noncomputable def EStop (β : ℝ) (g : ℕ × ℕ → ℝ) (τ : (ℕ → ℕ × ℕ) → ℕ∞) (i0 : ℕ × ℕ) : ℝ :=
  ∑' k : ℕ, β ^ k * ∑ w : Fin k → Bool,
    (if (k : ℕ∞) < τ (statesOf i0 (extendPrefix w)) then
      prefixProb i0 (extendPrefix w) k * g (statesOf i0 (extendPrefix w) k) else 0)

/-- `τ^* := inf{n ∈ ℕ | I(X_n) ≤ I(i_0)}` (`n ≥ 1`), the first time the index drops to or below
the starting index (Theorem 7.6.6). -/
noncomputable def tauStar {β : ℝ} (KS : KStoppingValue β pMN) (i0 : ℕ × ℕ) (x : ℕ → ℕ × ℕ) :
    ℕ∞ :=
  sInf {n : ℕ∞ | ∃ k : ℕ, 1 ≤ k ∧ n = (k : ℕ∞) ∧ GittinsIndex KS (x k) ≤ GittinsIndex KS i0}

end MDPFinance.InfiniteHorizonApplications


