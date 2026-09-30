-- Prove2me | Definitions.Def_VeinottWagnerSS_Bounds_Model
-- name    : VeinottWagnerSS_Bounds_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T13:30:24.17374+00:00
-- url     : https://prove2.me/theorems/047adee5-7de8-48b5-a246-a877f4315143
-- title:
--   The n-period (s, S) inventory model of Veinott–Wagner: history-dependent policies, the cost $f_n(x \mid Y)$ of Eq. (2), optimality and (s, S) rules
-- statement:
--   This definition sets up the finite-horizon periodic-review inventory model of Veinott and Wagner (1965) in the reduced form of their Eq. (2).
--
--   **Demand.** The demands $\xi_1, \xi_2, \dots$ are independent, non-negative, integer-valued random variables with common distribution $\varphi$, $\varphi(k) = \Pr(\xi_t = k)$. Unfilled demand is backlogged, so stock levels are arbitrary integers.
--
--   **Policies.** Let $X_t$ be the stock on hand plus on order before ordering in period $t$, and $Y_t$ the level after ordering. A **policy** chooses $Y_t$ as any integer-valued function of the information available at the start of period $t$. Given $X_1 = x$, that information is determined by $x$ and the past demands $\xi_1, \dots, \xi_{t-1}$, so a policy is a family of functions $Y_t(x; \xi_1, \dots, \xi_{t-1})$. The levels evolve by
--   $$X_1 = x, \qquad X_{t+1} = Y_t - \xi_t .$$
--   A policy is **admissible** if $Y_t \ge X_t$ (orders are non-negative) in every period along every demand history.
--
--   **Cost.** With set-up cost $K$, discount factor $\alpha$ and one-period cost function $G_\alpha : \mathbb Z \to \mathbb R$, the $n$-period cost from $X_1 = x$ is
--   $$f_n(x \mid Y) = \sum_{t=1}^{n} \alpha^{t-1}\bigl[K\,E\,\delta(Y_t - X_t) + E\,G_\alpha(Y_t)\bigr], \qquad \delta(0) = 0,\ \delta(z) = 1 \ (z > 0).$$
--   The expectations are over $(\xi_1, \dots, \xi_{t-1})$ with probability $\prod_i \varphi(\xi_i)$. The value may be $+\infty$.
--
--   **Optimality and (s, S) rules.** A policy $Y$ is **optimal** for the $n$-period model if it is admissible and $f_n(x \mid Y) \le f_n(x \mid Y')$ for every admissible policy $Y'$ and every initial level $x$. For integers $s \le S$, the **$(s, S)$ rule** in period $t$ is
--   $$Y_t = \begin{cases} S, & X_t < s, \\ X_t, & X_t \ge s. \end{cases}$$
--   A policy is an **$(s, S)$ policy** for the $n$-period model if for each period $t \le n$ there are integers $s_t \le S_t$ whose rule it uses in that period.
--
--   These objects are the common language of Lemmas 2–5 and Theorem 4(a) of the paper, which bound the first-period parameters of an optimal $(s, S)$ policy.
--
--   **Formalization Note** The model is the paper's reduced model of Eq. (2), p. 529: the purchase cost $c$, the lead time $\lambda$ and the holding–penalty cost $L$ enter only through $G_\alpha(y) = (1-\alpha)cy + L(y)$, which is taken as a primitive function `G : ℤ → ℝ`. Periods are numbered from $0$ in Lean: `Y t x h` is the paper's $Y_{t+1}$, where `h : Fin t → ℕ` lists $\xi_1, \dots, \xi_t$, and `state Y x t h` is $X_{t+1}$. The demand law is a `PMF ℕ`. Because $G_\alpha$ may be negative and a general policy may have infinite expected cost, $E\,G_\alpha(Y_t)$ is computed in the extended reals as the expectation of the positive part minus that of the negative part, each in $[0, \infty]$; the cost `cost φ G K α n x Y` is an `EReal`. Under the standing assumptions of the paper ($G_\alpha$ convex and $G_\alpha(y) \to \infty$ as $|y| \to \infty$) $G_\alpha$ is bounded below, so the negative part is finite and the difference is never the degenerate $\infty - \infty$. `IsSSPolicy n Y` indexes its parameters by the Lean period, so `s 0` is the paper's first-period $s_n$.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), pp. 526-529, Section 2 (Basic Definitions; Eq. (2); Optimality of a Stationary (s, S) Policy)

import Mathlib

namespace VeinottWagnerSS.Bounds

open scoped ENNReal

/-- The `(s, S)` ordering rule of Veinott & Wagner (1965), p. 529: with `s ≤ S`, if the stock on
hand plus on order `X` has fallen below `s` (`X < s`), order up to `S`; otherwise order nothing.
`sSRule s S X` is the resulting level `Y` after ordering. -/
def sSRule (s S X : ℤ) : ℤ := if X < s then S else X

/-- A (general, history-dependent) ordering policy for the periodic-review model (p. 527).
`Y t x h` is the level `Y_{t+1}` of stock on hand plus on order after ordering in period `t + 1`
(periods are numbered `1, 2, ⋯` in the paper and `0, 1, ⋯` here), as a function of the initial
level `X₁ = x` and the demands `h = (ξ₁, ⋯, ξ_t)` of the first `t` periods. Since every earlier
`X` and `Y` is determined by `x` and these demands, this is exactly the paper's "any integer
valued function of the information accumulated up to the beginning of period t"; it cannot see
the demand of the current or of any later period. -/
abbrev Policy : Type := (t : ℕ) → ℤ → (Fin t → ℕ) → ℤ

/-- The level `X_{t+1}` of stock on hand plus on order before ordering in period `t + 1`, when
policy `Y` is used from `X₁ = x` and the first `t` demands are `h = (ξ₁, ⋯, ξ_t)`:
`X₁ = x` and `X_{t+1} = Y_t − ξ_t` (p. 527, full backlogging, so levels may be negative). -/
def state (Y : Policy) (x : ℤ) : (t : ℕ) → (Fin t → ℕ) → ℤ
  | 0, _ => x
  | t + 1, h => Y t x (Fin.init h) - (h (Fin.last t) : ℤ)

/-- A policy is admissible if orders are non-negative, `Y_t ≥ X_t`, in every period and along
every demand history (p. 527). -/
def Admissible (Y : Policy) : Prop :=
  ∀ (t : ℕ) (x : ℤ) (h : Fin t → ℕ), state Y x t h ≤ Y t x h

/-- The probability `∏_{i} φ(ξ_i)` of the demand history `h = (ξ₁, ⋯, ξ_t)` when the demands are
i.i.d. with distribution `φ` (p. 526). -/
noncomputable def weight (φ : PMF ℕ) {t : ℕ} (h : Fin t → ℕ) : ℝ≥0∞ :=
  ∏ i, φ (h i)

/-- The probability `E δ(Y_{t+1} − X_{t+1})` that an order is placed in period `t + 1`
(`δ(0) = 0`, `δ(z) = 1` for `z > 0`, p. 527). -/
noncomputable def orderProb (φ : PMF ℕ) (Y : Policy) (x : ℤ) (t : ℕ) : ℝ≥0∞ :=
  ∑' h : Fin t → ℕ, weight φ h * (if state Y x t h < Y t x h then 1 else 0)

/-- The expectation `E G_α(Y_{t+1})` in the extended reals: the expectation of the positive part
minus that of the negative part, each computed in `[0, ∞]`. It is `+∞` when the positive part has
infinite expectation and the negative part does not. -/
noncomputable def expectedG (φ : PMF ℕ) (G : ℤ → ℝ) (Y : Policy) (x : ℤ) (t : ℕ) : EReal :=
  ((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (G (Y t x h)) : ℝ≥0∞) : EReal) -
    ((∑' h : Fin t → ℕ, weight φ h * ENNReal.ofReal (-G (Y t x h)) : ℝ≥0∞) : EReal)

/-- The expected cost `K E δ(Y_{t+1} − X_{t+1}) + E G_α(Y_{t+1})` of period `t + 1`. -/
noncomputable def periodCost (φ : PMF ℕ) (G : ℤ → ℝ) (K : ℝ) (Y : Policy) (x : ℤ) (t : ℕ) :
    EReal :=
  (K : EReal) * (orderProb φ Y x t : EReal) + expectedG φ G Y x t

/-- The `n`-period cost of Eq. (2), p. 529:
`f_n(x | Y) = ∑_{t=1}^{n} α^{t−1} [K E δ(Y_t − X_t) + E G_α(Y_t)]` with `X₁ = x`,
valued in the extended reals (it is `+∞` for policies of infinite expected cost). -/
noncomputable def cost (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (x : ℤ) (Y : Policy) : EReal :=
  ∑ t ∈ Finset.range n, ((α ^ t : ℝ) : EReal) * periodCost φ G K Y x t

/-- `Y` is an optimal policy for the `n`-period model (p. 529): it is admissible and
`f_n(x | Y) ≤ f_n(x | Y')` for every admissible policy `Y'` and every initial level `x`. -/
def IsOptimal (φ : PMF ℕ) (G : ℤ → ℝ) (K α : ℝ) (n : ℕ) (Y : Policy) : Prop :=
  Admissible Y ∧ ∀ Y' : Policy, Admissible Y' → ∀ x : ℤ, cost φ G K α n x Y ≤ cost φ G K α n x Y'

/-- Policy `Y` uses the `(s, S)` rule in period `t + 1`:
`Y_{t+1} = S` if `X_{t+1} < s` and `Y_{t+1} = X_{t+1}` if `X_{t+1} ≥ s`, along every history. -/
def UsesRule (Y : Policy) (t : ℕ) (s S : ℤ) : Prop :=
  ∀ (x : ℤ) (h : Fin t → ℕ), Y t x h = sSRule s S (state Y x t h)

/-- `Y` is an `(s, S)` policy for the `n`-period model (p. 529): for each period `t + 1 ≤ n` there
are integers `s t ≤ S t` such that `Y` uses the `(s t, S t)` rule in period `t + 1`. -/
def IsSSPolicy (n : ℕ) (Y : Policy) : Prop :=
  ∃ s S : ℕ → ℤ, ∀ t < n, s t ≤ S t ∧ UsesRule Y t (s t) (S t)

end VeinottWagnerSS.Bounds


