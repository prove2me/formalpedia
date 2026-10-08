-- Prove2me | Definitions.Def_ZhengFedergruenSS_Algorithm_Model
-- name    : ZhengFedergruenSS_Algorithm_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-06T15:55:25.69744+00:00
-- url     : https://prove2.me/theorems/d434db3e-3a6a-4861-b26a-781afd08b8ee
-- title:
--   §1, (1)–(2): the assumptions on G, the renewal quantities m and M, the cost c(s, S) of an (s, S) policy, and optimality
-- statement:
--   This module fixes the model of Zheng and Federgruen (1991), §1, pp. 655–656.
--
--   **Data.** One-period demands are i.i.d., nonnegative and integer valued, with $p_j=\Pr\{D=j\}$, $j=0,1,2,\dots$ (a demand distribution: $p_j\ge 0$, $\sum_j p_j=1$). $K$ is the fixed cost of an order, and $G:\mathbb Z\to\mathbb R$ gives the one-period expected cost when starting a period with inventory position $y$.
--
--   **Assumptions on $G$** (p. 655). The paper assumes only that $-G$ is unimodal and $\lim_{|y|\to\infty}G(y)>\min_y G(y)+K$. These are recorded as two predicates:
--
--   1. $-G$ is *unimodal*: there is an integer $m$ such that $G$ is nonincreasing on $\{y\le m\}$ and nondecreasing on $\{y\ge m\}$ (plateaus allowed).
--   2. *Growth*: $G$ has a minimizer $y_0$, and $G(y)>G(y_0)+K$ for all but finitely many integers $y$.
--
--   **Renewal quantities** (2a)–(2c), p. 656. With $m(0)=(1-p_0)^{-1}$ and, for $j\ge1$,
--   $$m(j)=(1-p_0)^{-1}\sum_{l=1}^{j}p_l\,m(j-l),$$
--   which is (2b) $m(j)=\sum_{l=0}^{j}p_l\,m(j-l)$ solved for $m(j)$, and $M(j)=\sum_{i=0}^{j-1}m(i)$, so that $M(0)=0$ and $M(j)=M(j-1)+m(j-1)$. Also $\alpha_n=M(n)/M(n+1)$.
--
--   **The cost of an $(s,S)$ policy.** For integers $s<S$, the long-run average cost of the policy that orders up to $S$ whenever the inventory position drops to or below $s$ is
--   $$c(s,S)=\frac{K+\sum_{j=0}^{S-s-1}m(j)\,G(S-j)}{M(S-s)}.$$
--
--   **Optimality.** $s$ is an *optimal reorder level* for $S$ if $s<S$ and $c(s,S)\le c(s',S)$ for every $s'<S$. $(s,S)$ is an *optimal policy* if $s<S$ and $c(s,S)\le c(s',S')$ for every pair of integers $s'<S'$; the optimal average cost $c^*$ is the cost of any optimal policy.
--
--   **Formalization Note.** The demand law is the published `VeinottWagnerSS.RenewalCost.DemandDist` (a real function on $\mathbb N$ with nonnegative values summing to $1$). Equation (1) is misprinted on p. 655 as $M(S-s)K+\sum\cdots$; the ratio above is the one given by (3) and (5) on p. 656 and used in (6) and every proof. Since (2b) has $m(j)$ on both sides, $m$ is defined by the solved recursion of p. 660 (printed there with the typo $m(l-j)$). For $s\ge S$ the Lean value of $c(s,S)$ is $0$ (division by $M(0)=0$), so every statement quantifies over $s<S$. Under unimodality, each one-sided limit of $G$ is the supremum of a monotone tail, so the growth predicate is equivalent to the page's limit condition. The limit may be finite: $G\to+\infty$ is not assumed. Optimality is among $(s,S)$ policies only. That such a policy is optimal among all policies is Veinott (1966), which this paper cites and does not use (§5: the analysis rests only on the form (1)). Optimal costs $c^*$ are never formed as infima.
-- source:
--   Zheng and Federgruen, Finding Optimal (s, S) Policies Is About As Simple As Evaluating a Single Policy, Oper. Res. 39(4):654–665 (1991), DOI 10.1287/opre.39.4.654, pp. 655–656, §1, (1), (2a)–(2c), (3), (5); p. 656, α_n before (6); p. 660 (solved form of (2b))

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand

namespace ZhengFedergruenSS.Algorithm

/-- `−G` is unimodal (Zheng and Federgruen 1991, p. 655): there is an integer `m` such that `G`
is nonincreasing on `{y ≤ m}` and nondecreasing on `{y ≥ m}`. Plateaus (equal consecutive values)
are allowed. Same body as `FedergruenZhengRQ.OPT.NegUnimodal`. -/
def NegUnimodal (G : ℤ → ℝ) : Prop :=
  ∃ m : ℤ, AntitoneOn G (Set.Iic m) ∧ MonotoneOn G (Set.Ici m)

/-- The growth assumption `lim_{|y|→∞} G(y) > min_y G(y) + K` of p. 655, stated without limits:
`G` has a minimizer `y₀`, and `G(y) > G(y₀) + K` for all but finitely many integers `y`
(on both tails).

Formalization Note: when `−G` is unimodal, each one-sided limit of `G` exists in `(−∞, +∞]` as the
supremum of a monotone tail, so the page's strict inequality between the limit and `min G + K`
holds iff the tail eventually exceeds `min G + K`; this predicate is therefore equivalent to the
page's assumption. The limit may be finite: this is weaker than `G(y) → +∞` (the "common case"
of p. 655), which is *not* assumed. -/
def GrowthCond (K : ℝ) (G : ℤ → ℝ) : Prop :=
  ∃ y₀ : ℤ, (∀ x : ℤ, G y₀ ≤ G x) ∧ ∀ᶠ y in Filter.cofinite, G y₀ + K < G y

/-- The renewal density `m` of (2a)–(2b), p. 656: `m(0) = (1 − p₀)⁻¹` and, for `j ≥ 1`,
`m(j) = Σ_{l=0}^{j} p_l m(j − l)`. Since (2b) has `m(j)` on both sides (the `l = 0` term), it is
defined here by the solved form the paper writes on p. 660,
`m(j) = (1 − p₀)⁻¹ Σ_{l=1}^{j} p_l m(j − l)`, by strong recursion: `m (j + 1)` is
`(1 − p₀)⁻¹ Σ_{i=0}^{j} p_{j+1−i} m(i)` (substituting `i = j + 1 − l`). For `p₀ < 1` this `m`
satisfies (2b), since `(1 − p₀) m(j) = Σ_{l=1}^{j} p_l m(j − l)` is (2b) with the `l = 0` term moved
to the left. (The page's solved form prints `m(l − j)`, a typo for `m(j − l)`.) -/
noncomputable def m (p : ℕ → ℝ) : ℕ → ℝ
  | 0 => (1 - p 0)⁻¹
  | j + 1 => (1 - p 0)⁻¹ * ∑ i : Fin (j + 1), p (j + 1 - i.val) * m p i.val
decreasing_by exact i.isLt

/-- The renewal function `M` of (2a), (2c), p. 656: `M(0) = 0`, `M(j) = M(j − 1) + m(j − 1)`,
i.e. `M(j) = Σ_{i<j} m(i)`. -/
noncomputable def M (p : ℕ → ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, m p i

/-- `α_n ≡ M(n)/M(n + 1)` (p. 656, before (6)), used for `n = 1, 2, …`. -/
noncomputable def alpha (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  M p n / M p (n + 1)

/-- The long-run average cost of the `(s, S)` policy, (1) as corrected by (3) and (5), pp. 655–656:
`c(s, S) = [K + Σ_{j=0}^{S−s−1} m(j) G(S − j)] / M(S − s)`.

(1) is misprinted on p. 655 as `M(S − s)K + Σ …`; (3) `c(s, S) = k(s, S)/M(S − s)` and
(5) `k(s, y) = K + Σ_{j=0}^{y−s−1} m(j)G(y − j)` give the ratio, which is what (6) and the proofs use.

Formalization Note: a policy is a pair of integers `s < S`. For `s ≥ S` the Lean value is junk
(`(S − s).toNat = 0`, `M 0 = 0`, so `c s S = 0` by `x / 0 = 0`); every statement about `c`
quantifies over `s < S` only. -/
noncomputable def c (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (s S : ℤ) : ℝ :=
  (K + ∑ j ∈ Finset.range (S - s).toNat, m p j * G (S - (j : ℤ))) / M p (S - s).toNat

/-- `s` is an optimal reorder level for the order-up-to level `S` (p. 656, Lemma 1):
`s < S` and `c(s, S) ≤ c(s′, S)` for every `s′ < S`, i.e. `c(s, S) = min_{s′<S} c(s′, S)`. -/
def IsOptimalReorder (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (S s : ℤ) : Prop :=
  s < S ∧ ∀ s' : ℤ, s' < S → c p K G s S ≤ c p K G s' S

/-- `(s, S)` is an optimal policy: `s < S` and `c(s, S) ≤ c(s′, S′)` for **every** pair of integers
`s′ < S′`. Optimality is among `(s, S)` policies, whose costs are given by (1) (the paper's
analysis "is solely based on the cost function c(·,·) being of the form (1)", §5, p. 663). The
optimal average cost `c*` is `c(s, S)` for any optimal `(s, S)`. -/
def IsOptimalPolicy (p : ℕ → ℝ) (K : ℝ) (G : ℤ → ℝ) (s S : ℤ) : Prop :=
  s < S ∧ ∀ s' S' : ℤ, s' < S' → c p K G s S ≤ c p K G s' S'

end ZhengFedergruenSS.Algorithm


