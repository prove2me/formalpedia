-- Prove2me | Definitions.Def_RobustSPUA_LP
-- name    : RobustSPUA_LP
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T12:43:19.073667+00:00
-- url     : https://prove2.me/theorems/83e7f7db-acd4-4d75-90da-5de497703a2b
-- title:
--   The policy polytope $\mathrm{POL}$, the linear program $(LP)_{n,p}$ and the program $(P')$
-- statement:
--   These are the polyhedral objects of Theorems 1 and 2 of Perez-Salazar, Singh and Toriello (p.5), of (9) (p.13), and of the proof of Theorem 7 (pp.29, 33). Vectors $x=(x_{t,s})$, $y=(y_{t,s})$ are indexed by $t\in[n]$, $s\in[t]$, and $0<p\le1$.
--
--   1. **The policy polytope** (Theorem 1, p.5):
--   $$
--   \mathrm{POL}=\Bigl\{(x,y)\ge0:\ x_{1,1}+y_{1,1}=1,\ \ x_{t,s}+y_{t,s}=\frac1t\sum_{\sigma=1}^{t-1}\bigl(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma}\bigr)\ \ \forall t\in\{2,\dots,n\},\ s\in[t]\Bigr\}.
--   $$
--   2. **The POL policy** (Theorem 1, Proposition 6): a policy *agrees with* $(x,y)$ if it offers to the first candidate with probability $x_{1,1}$ and, at a state $(t,s)$ with $t>1$ whose denominator is positive, with probability $t\,x_{t,s}\big/\sum_{\sigma=1}^{t-1}(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma})$.
--   3. **The linear program $(LP)_{n,p}$** (Theorem 2, p.5): $(x,\gamma)$ is feasible if $x\ge0$,
--   $$
--   x_{t,s}\le\frac1t\Bigl(1-p\sum_{\tau=1}^{t-1}\sum_{\sigma=1}^{\tau}x_{\tau,\sigma}\Bigr)\quad\forall t\in[n],\ s\in[t],
--   \qquad
--   \gamma\le\frac{p}{1-(1-p)^k}\sum_{t=1}^n\sum_{s=1}^t x_{t,s}\,c_{t,s,k}\quad\forall k\in[n],
--   $$
--   where $c_{t,s,k}=\sum_{i=s}^{k\wedge(n-t+s)}\binom{i-1}{s-1}\binom{n-i}{t-s}\big/\binom nt$ is the closed form printed in Theorem 2.
--   4. **The LP policy** (Theorem 2): a policy *agrees with* $x$ if, at every state $(t,s)$ with $1-p\sum_{\tau<t}\sum_{\sigma\le\tau}x_{\tau,\sigma}>0$, it offers with probability $t\,x_{t,s}/\bigl(1-p\sum_{\tau<t}\sum_{\sigma\le\tau}x_{\tau,\sigma}\bigr)$.
--   5. **The constraints (18)–(19)** (p.29): $(x,y)\ge0$, $x_{1,1}+y_{1,1}\le1$ and $x_{t,s}+y_{t,s}\le\frac1t\sum_{\sigma=1}^{t-1}(y_{t-1,\sigma}+(1-p)x_{t-1,\sigma})$ for $t\in\{2,\dots,n\}$; **$(P')$** (p.33) adds $\gamma\le p\sum_{t,s}x_{t,s}c_{t,s,k}/(1-(1-p)^k)$ for $k\in[n]$.
--   6. **The objective of (9)** (p.13): $\min_{k\in[n]}p\sum_{t,s}x_{t,s}\,\mathbf P(R_t\le k\mid r_t=s)/(1-(1-p)^k)$.
--
--   These programs describe the space of policies of the SP-UA and the linear program whose value is the best robust ratio.
--
--   **Formalization Note** Vectors are `ℕ → ℕ → ℝ`, read only at $t\in[n]$, $s\in[t]$. The recursion of POL and of (19)/(P′) is for $t\ge2$, as in Theorem 1 (p.5) and §4.2.1 (p.12); the appendix (pp.29, 30, 33) prints "$\forall t\in[n]$", which at $t=1$ (empty sum) forces $x_{1,1}+y_{1,1}=0$ and makes POL empty — that misprint is corrected. `AgreesPOL` and `AgreesLP` constrain the policy only where the denominator is positive. In `polValue` the coefficient is the conditional probability `condRankProb`; in `LPFeasible` and `PprimeFeasible` it is the closed form `rankCoef`.
-- source:
--   Perez-Salazar, Singh, Toriello, Robust Online Selection with Uncertain Offer Acceptance, arXiv:2112.00842v2, Theorem 1 and Theorem 2, p.5 (POL, (LP)_{n,p}, closed form, policies); (9), p.13; (18)–(19), p.29; POL, p.30; Proposition 6, p.31; (P′), p.33

import Mathlib
import Definitions.Def_RobustSPUA_Model

open Finset

namespace RobustSPUA

/-! # The policy polytope POL, the linear program (LP)_{n,p} and the program (P′)

S. Perez-Salazar, M. Singh, A. Toriello, *Robust Online Selection with Uncertain Offer
Acceptance*, arXiv:2112.00842v2: Theorem 1 and Theorem 2, p.5 (POL, (LP)_{n,p}, the closed
form of `P(R_t ≤ k | r_t = s)`, the policies built from a point); (9), p.13; (18)–(19), p.29;
(P′), p.33.

**Formalization Note**
* All vectors are `ℕ → ℕ → ℝ`, read at the paper's 1-based indices `t ∈ [n]`, `s ∈ [t]`.
* POL's recursion and the constraints (19) of (P) and of (P′) are for `t ∈ [2, n]`, as in
  Theorem 1 and §4.2.1 (pp.5, 12). The appendix (pp.29, 30, 33) prints `∀ t ∈ [n]`; at `t = 1`
  the sum is empty and forces `x_{1,1} + y_{1,1} = 0` (resp. `≤ 0`), contradicting
  `x_{1,1} + y_{1,1} = 1`; this misprint is corrected.
* The policy formulas divide by quantities that can be `0`. `AgreesLP` and `AgreesPOL` constrain
  the policy only where the denominator is positive; every completion is allowed.
* `rankCoef` is the closed form printed in Theorem 2; every natural subtraction in it is in range
  for `t ∈ [n]`, `s ∈ [t]`, `i ∈ [s, min k (n−t+s)]`. -/

/-- `1 − p ∑_{τ=1}^{t−1} ∑_{σ=1}^{τ} x_{τ,σ}` ((LP)_{n,p}, p.5). -/
noncomputable def slackLP (p : ℝ) (x : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  1 - p * ∑ τ ∈ Ico 1 t, ∑ σ ∈ Icc 1 τ, x τ σ

/-- The closed form `∑_{i=s}^{k ∧ (n−t+s)} C(i−1,s−1) C(n−i,t−s) / C(n,t)` of Theorem 2, p.5. -/
noncomputable def rankCoef (n t s k : ℕ) : ℝ :=
  ((∑ i ∈ Icc s (min k (n - t + s)), (i - 1).choose (s - 1) * (n - i).choose (t - s) : ℕ) : ℝ) /
    (n.choose t : ℝ)

/-- `(x, γ)` is feasible for (LP)_{n,p} (Theorem 2, p.5): `x ≥ 0`,
`x_{t,s} ≤ (1/t)(1 − p ∑_{τ<t} ∑_{σ ≤ τ} x_{τ,σ})` for `t ∈ [n]`, `s ∈ [t]`, and
`γ ≤ p/(1 − (1−p)^k) ∑_{t,s} x_{t,s} P(R_t ≤ k | r_t = s)` for `k ∈ [n]`, with the closed form. -/
def LPFeasible (n : ℕ) (p : ℝ) (x : ℕ → ℕ → ℝ) (γ : ℝ) : Prop :=
  (∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, 0 ≤ x t s ∧ x t s ≤ (1 / (t : ℝ)) * slackLP p x t) ∧
  ∀ k ∈ Icc 1 n,
    γ ≤ p / (1 - (1 - p) ^ k) * ∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * rankCoef n t s k

/-- The policy `q` is the policy of Theorem 2 (p.5) built from `x`: at every state `(t, s)` whose
denominator `1 − p ∑_{τ<t} ∑_σ x_{τ,σ}` is positive, it offers with probability
`t x_{t,s} / (1 − p ∑_{τ<t} ∑_σ x_{τ,σ})`; elsewhere it is unconstrained. -/
def AgreesLP (n : ℕ) (p : ℝ) (x q : ℕ → ℕ → ℝ) : Prop :=
  ∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, 0 < slackLP p x t → q t s = t * x t s / slackLP p x t

/-- `∑_{σ=1}^{t−1} (y_{t−1,σ} + (1 − p) x_{t−1,σ})` (POL, Theorem 1, p.5). -/
noncomputable def polD (p : ℝ) (x y : ℕ → ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ σ ∈ Icc 1 (t - 1), (y (t - 1) σ + (1 - p) * x (t - 1) σ)

/-- The policy polytope POL (Theorem 1, p.5): `(x, y) ≥ 0`, `x_{1,1} + y_{1,1} = 1`, and
`x_{t,s} + y_{t,s} = (1/t) ∑_{σ=1}^{t−1} (y_{t−1,σ} + (1−p) x_{t−1,σ})` for `t ∈ [2, n]`,
`s ∈ [t]`. -/
def POL (n : ℕ) (p : ℝ) (x y : ℕ → ℕ → ℝ) : Prop :=
  (∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, 0 ≤ x t s ∧ 0 ≤ y t s) ∧
  x 1 1 + y 1 1 = 1 ∧
  ∀ t ∈ Icc 2 n, ∀ s ∈ Icc 1 t, x t s + y t s = (1 / (t : ℝ)) * polD p x y t

/-- The policy `q` is the policy of Theorem 1 / Proposition 6 (pp.5, 31) built from `(x, y)`: it
offers to the first candidate with probability `x_{1,1}`, and at a state `(t, s)` with `t > 1`
whose denominator `∑_σ (y_{t−1,σ} + (1−p) x_{t−1,σ})` is positive, with probability
`t x_{t,s} / ∑_σ (y_{t−1,σ} + (1−p) x_{t−1,σ})`; elsewhere it is unconstrained. -/
def AgreesPOL (n : ℕ) (p : ℝ) (x y q : ℕ → ℕ → ℝ) : Prop :=
  q 1 1 = x 1 1 ∧
  ∀ t ∈ Icc 2 n, ∀ s ∈ Icc 1 t, 0 < polD p x y t → q t s = t * x t s / polD p x y t

/-- The constraints (18)–(19) of (P) (p.29) with `(x, y) ≥ 0`: `x_{1,1} + y_{1,1} ≤ 1` and
`x_{t,s} + y_{t,s} ≤ (1/t) ∑_σ (y_{t−1,σ} + (1−p) x_{t−1,σ})` for `t ∈ [2, n]`, `s ∈ [t]`. -/
def POLineq (n : ℕ) (p : ℝ) (x y : ℕ → ℕ → ℝ) : Prop :=
  (∀ t ∈ Icc 1 n, ∀ s ∈ Icc 1 t, 0 ≤ x t s ∧ 0 ≤ y t s) ∧
  x 1 1 + y 1 1 ≤ 1 ∧
  ∀ t ∈ Icc 2 n, ∀ s ∈ Icc 1 t, x t s + y t s ≤ (1 / (t : ℝ)) * polD p x y t

/-- `(x, y, γ)` is feasible for (P′) (proof of Theorem 7, p.33): (18)–(19) and
`γ ≤ p ∑_{t,s} x_{t,s} P(R_t ≤ k | r_t = s) / (1 − (1−p)^k)` for `k ∈ [n]`, with the closed form
of Theorem 2 for `P(R_t ≤ k | r_t = s)`. -/
def PprimeFeasible (n : ℕ) (p : ℝ) (x y : ℕ → ℕ → ℝ) (γ : ℝ) : Prop :=
  POLineq n p x y ∧
  ∀ k ∈ Icc 1 n,
    γ ≤ p * (∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * rankCoef n t s k) / (1 - (1 - p) ^ k)

/-- The objective of (9), p.13:
`min_{k ∈ [n]} p ∑_{t,s} x_{t,s} P(R_t ≤ k | r_t = s) / (1 − (1−p)^k)`, with the conditional
probability `condRankProb` under the uniform permutation. -/
noncomputable def polValue (n : ℕ) (p : ℝ) (x : ℕ → ℕ → ℝ) : ℝ :=
  ⨅ k : Fin n, p * (∑ t ∈ Icc 1 n, ∑ s ∈ Icc 1 t, x t s * condRankProb n t s (k.val + 1)) /
    (1 - (1 - p) ^ (k.val + 1))

end RobustSPUA


