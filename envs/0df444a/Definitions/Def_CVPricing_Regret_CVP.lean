-- Prove2me | Definitions.Def_CVPricing_Regret_CVP
-- name    : CVPricing_Regret_CVP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T09:49:47.05044+00:00
-- url     : https://prove2.me/theorems/bab12173-cd49-431e-be3c-8edad6170a82
-- title:
--   §2.2 and §3.2, pp. 774–775 — the quasi-likelihood equations (3), the taboo interval (6) and the Controlled Variance Pricing rule
-- statement:
--   Given prices $p_1, \dots, p_t$ and demands $d_1, \dots, d_t$, the **maximum quasi-likelihood estimate** (MQLE) $\hat a_t = (\hat a_{0t}, \hat a_{1t})$ is a solution of
--
--   $$l_t(\hat a_t) = \sum_{i=1}^t \frac{\dot h(\hat a_{0t} + \hat a_{1t} p_i)}{\sigma^2 v\big(h(\hat a_{0t} + \hat a_{1t} p_i)\big)} \begin{pmatrix} 1 \\ p_i \end{pmatrix} \big(d_i - h(\hat a_{0t} + \hat a_{1t} p_i)\big) = 0. \tag{3}$$
--
--   Write $\bar p_t = t^{-1}\sum_{i\le t} p_i$ and $\operatorname{Var}(p)_t = t^{-1}\sum_{i \le t}(p_i - \bar p_t)^2$. For $\alpha \in (0,1)$ and $c > 0$ the **taboo interval** at time $t$ is the open interval
--
--   $$\mathrm{TI}(t) = \Big(\bar p_t - \sqrt{c[(t+1)^\alpha - t^\alpha]\tfrac{t+1}{t}},\ \bar p_t + \sqrt{c[(t+1)^\alpha - t^\alpha]\tfrac{t+1}{t}}\Big). \tag{6}$$
--
--   A path $(p_t, d_t)_{t \ge 1}$ **follows Controlled Variance Pricing** (CVP) when:
--
--   1. $p_1, p_2 \in [p_l, p_h]$, $p_1 \ne p_2$, $\alpha \in (0,1)$ and $0 < c < 2^{-\alpha}(p_1 - p_2)^2 \min\{1, (3\alpha)^{-1}\}$;
--   2. for every $t \ge 2$: if (3) has no solution, or the solution has $\hat a_{0t} \le 0$, or $\hat a_{1t} \ge 0$, or $\hat a_{0t} + \hat a_{1t} p < 0$ for some $p \in [p_l, p_h]$, then $p_{t+1} \in \{p_1, p_2\}$ with $|p_{t+1} - \bar p_t| = \max(|p_1 - \bar p_t|, |p_2 - \bar p_t|)$;
--   3. otherwise $p_{t+1} \in \arg\max_{p \in [p_l,p_h]} r(p, \hat a_t)$ (7) if such a maximizer gives $\operatorname{Var}(p)_{t+1} \ge c(t+1)^{\alpha-1}$, and else $p_{t+1} \in \arg\max_{p \in [p_l,p_h]\setminus \mathrm{TI}(t)} r(p, \hat a_t)$ (8).
--
--   The definition also contains the hypothesis that (3) has at most one root, used by the mission's stochastic statements.
--
--   **Formalization Note** Periods are 1-based (index $0$ unused); $t\operatorname{Var}(p)_t$, $\bar p_t$ and the design matrix are the referenced Keskin–Zeevi functions `infoMetricOf`, `avgPriceOf`, `fisherOf`. Because the paper's $h$ lives on $[0,\infty)$, a root of (3) counts as an MQLE only if $\hat a_0 + \hat a_1 p_i \ge 0$ for every observed price. CVP is a predicate on a realized path: any maximizer is allowed in (7) and (8), so statements cover every tie-breaking rule; without uniqueness the policy may use any root. The uniqueness hypothesis `MQLEUnique` (for histories with $t \ge 2$, prices in $[p_l,p_h]$ and $p_1 \ne p_2$, (3) has at most one root) is not in the paper, which notes that roots "may, in general, not always be unique"; it holds for canonical links such as normal–identity, Poisson–exp and Bernoulli–logistic.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 774 (PDF 6), §2.2, eq. (3); p. 775 (PDF 7), §3.2, eqs. (6)–(8) and the CVP box

import Mathlib
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares
import Definitions.Def_CVPricing_Regret_Model

open KeskinZeevi.SufficientConditions

namespace CVPricing.Regret

/-- The quasi-likelihood score `l_t(a)` of eq. (3) (den Boer–Zwart 2014, §2.2, p. 774) for prices
`p₁, …, p_t` and demands `d₁, …, d_t` (periods are 1-based; index `0` is unused):
`l_t(a) = Σ_{i=1}^t ḣ(a₀ + a₁ p_i) / (σ² v(h(a₀ + a₁ p_i))) · (1, p_i)ᵀ · (d_i − h(a₀ + a₁ p_i))`. -/
noncomputable def qscore (M : Model) (p d : ℕ → ℝ) (t : ℕ) (a : ℝ × ℝ) : ℝ × ℝ :=
  ∑ i ∈ Finset.Icc 1 t,
    (deriv M.h (a.1 + a.2 * p i) / (M.σ ^ 2 * M.v (M.h (a.1 + a.2 * p i))) *
        (d i - M.h (a.1 + a.2 * p i)),
      deriv M.h (a.1 + a.2 * p i) / (M.σ ^ 2 * M.v (M.h (a.1 + a.2 * p i))) *
        (d i - M.h (a.1 + a.2 * p i)) * p i)

/-- `a` is a maximum quasi-likelihood estimate (MQLE) at time `t`: a solution of (3). Since `h` is only
given on `[0, ∞)` in the paper, (3) is only defined when `a₀ + a₁ p_i ≥ 0` for every observed price;
roots outside that domain (where the Lean extension of `h` is junk) are not MQLEs. -/
def IsMQLE (M : Model) (p d : ℕ → ℝ) (t : ℕ) (a : ℝ × ℝ) : Prop :=
  (∀ i ∈ Finset.Icc 1 t, 0 ≤ a.1 + a.2 * p i) ∧ qscore M p d t a = 0

/-- Disclosed hypothesis: for every history with `t ≥ 2`, prices `p₁, …, p_t ∈ [pl, ph]` and
`p₁ ≠ p₂`, equation (3) has at most one solution, so "the MQLE" of p. 774 is well defined whenever it
exists. The paper notes (p. 774) that
the solution "may, in general, not always be unique". The hypothesis holds e.g. for canonical links
(normal–identity, Poisson–exp, Bernoulli–logistic). -/
def MQLEUnique (M : Model) : Prop :=
  ∀ (p d : ℕ → ℝ) (t : ℕ), 2 ≤ t → (∀ i ∈ Finset.Icc 1 t, p i ∈ Set.Icc M.pl M.ph) →
    p 1 ≠ p 2 → {a | IsMQLE M p d t a}.Subsingleton

/-- An estimate `a` passes the sign checks of CVP step 2 (p. 775): `a₀ > 0`, `a₁ < 0` and
`a₀ + a₁ p ≥ 0` for every `p ∈ [pl, ph]` (the negation of cases (b) and (c)). -/
def GoodEst (M : Model) (a : ℝ × ℝ) : Prop :=
  0 < a.1 ∧ a.2 < 0 ∧ ∀ q ∈ Set.Icc M.pl M.ph, 0 ≤ a.1 + a.2 * q

/-- The sample variance `Var(p)_t = t⁻¹ Σ_{i=1}^t (p_i − p̄_t)²` (p. 774); `infoMetricOf p t` is
`t · Var(p)_t`. -/
noncomputable def sampleVar (p : ℕ → ℝ) (t : ℕ) : ℝ :=
  infoMetricOf p t / t

/-- Half-width `√(c[(t+1)^α − t^α](t+1)/t)` of the taboo interval (6) (p. 775). -/
noncomputable def tabooHalfWidth (α c : ℝ) (t : ℕ) : ℝ :=
  Real.sqrt (c * (((t : ℝ) + 1) ^ α - (t : ℝ) ^ α) * (((t : ℝ) + 1) / t))

/-- The taboo interval (6) at time `t` (p. 775): the open interval
`TI(t) = (p̄_t − √(c[(t+1)^α − t^α](t+1)/t), p̄_t + √(c[(t+1)^α − t^α](t+1)/t))`. -/
noncomputable def tabooInterval (α c : ℝ) (p : ℕ → ℝ) (t : ℕ) : Set ℝ :=
  Set.Ioo (avgPriceOf p t - tabooHalfWidth α c t) (avgPriceOf p t + tabooHalfWidth α c t)

/-- Fallback price of CVP step 2 in cases (a)–(c): `p_{t+1} ∈ {p₁, p₂}` with
`|p_{t+1} − p̄_t| = max(|p₁ − p̄_t|, |p₂ − p̄_t|)`. -/
def FarPrice (p : ℕ → ℝ) (t : ℕ) : Prop :=
  (p (t + 1) = p 1 ∨ p (t + 1) = p 2) ∧
    |p (t + 1) - avgPriceOf p t| = max |p 1 - avgPriceOf p t| |p 2 - avgPriceOf p t|

/-- Pricing with a good estimate `a` (p. 775): if some maximizer of `r(·, a)` over `[pl, ph]` gives
`Var(p)_{t+1} ≥ c(t+1)^{α−1}`, then `p_{t+1}` is such a maximizer (eq. (7)); otherwise `p_{t+1}` is a
maximizer of `r(·, a)` over `[pl, ph] ∖ TI(t)` (eq. (8)). Any maximizer is allowed (all tie-breaks). -/
def ExploitOrTaboo (M : Model) (α c : ℝ) (p : ℕ → ℝ) (t : ℕ) (a : ℝ × ℝ) : Prop :=
  ((∃ q, IsRevMaxOn M a (Set.Icc M.pl M.ph) q ∧
        c * ((t : ℝ) + 1) ^ (α - 1) ≤ sampleVar (Function.update p (t + 1) q) (t + 1)) ∧
      IsRevMaxOn M a (Set.Icc M.pl M.ph) (p (t + 1)) ∧
      c * ((t : ℝ) + 1) ^ (α - 1) ≤ sampleVar p (t + 1)) ∨
  ((¬ ∃ q, IsRevMaxOn M a (Set.Icc M.pl M.ph) q ∧
        c * ((t : ℝ) + 1) ^ (α - 1) ≤ sampleVar (Function.update p (t + 1) q) (t + 1)) ∧
      IsRevMaxOn M a (Set.Icc M.pl M.ph \ tabooInterval α c p t) (p (t + 1)))

/-- A realized price/demand path `(p_t, d_t)_{t ≥ 1}` follows the pricing policy
**Controlled Variance Pricing** (CVP) with parameters `α, c` (den Boer–Zwart 2014, p. 775).

* Initialization: `p₁, p₂ ∈ [pl, ph]`, `p₁ ≠ p₂`, `α ∈ (0, 1)` and
  `c ∈ (0, 2^{−α}(p₁ − p₂)² min{1, (3α)⁻¹})` (the printed range).
* For all `t ≥ 2`: if (3) has no solution, or the solution fails case (b) or (c), then `p_{t+1}` is the
  initial price farthest from `p̄_t`; otherwise `p_{t+1}` follows (7)/(8) with that solution.
  Without uniqueness of the root (see `MQLEUnique`) the policy may use any root. -/
def IsCVPPath (M : Model) (α c : ℝ) (p d : ℕ → ℝ) : Prop :=
  p 1 ∈ Set.Icc M.pl M.ph ∧ p 2 ∈ Set.Icc M.pl M.ph ∧ p 1 ≠ p 2 ∧
  α ∈ Set.Ioo (0 : ℝ) 1 ∧ 0 < c ∧
  c < (2 : ℝ) ^ (-α) * (p 1 - p 2) ^ 2 * min 1 (3 * α)⁻¹ ∧
  ∀ t : ℕ, 2 ≤ t →
    ((∀ a, ¬ IsMQLE M p d t a) ∧ FarPrice p t) ∨
    (∃ a, IsMQLE M p d t a ∧ ¬ GoodEst M a ∧ FarPrice p t) ∨
    (∃ a, IsMQLE M p d t a ∧ GoodEst M a ∧ ExploitOrTaboo M α c p t a)

end CVPricing.Regret


