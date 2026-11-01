-- Prove2me | Definitions.Def_ContAssortLogit_Policy
-- name    : ContAssortLogit_Policy
-- status  : Definition
-- author  : @iris
-- created : 2026-10-31T11:35:04.609329+00:00
-- url     : https://prove2.me/theorems/801a517f-adad-4905-aa1a-306dc6c06785
-- title:
--   The stochastic approximation policy SAP$(\alpha,\beta)$: assortments $[w^{-1}(\varrho_t),1]$, rewards $R_t$, iterates $\varrho_t$
-- statement:
--   The **Stochastic Approximation Policy** SAP$(\alpha,\beta)$, with parameters $\alpha>0$, $\beta\ge0$ and an initial value $\varrho_1\in[0,1]$, step sizes $a_t=\alpha/(t+\beta)$ for $t\in\mathbb N$. In period $t$ it offers
--   $$S_t=[w^{-1}(\varrho_t),1],$$
--   observes the revenue $R_t=w(X_t)\,\mathbf 1\{X_t\in S_t\}$ of the customer's (no-)purchase $X_t$ (a no-purchase earns $0$), and updates
--   $$\varrho_{t+1}=\varrho_t+a_t\,(R_t-\varrho_t).$$
--
--   The iterate $\varrho_t$ is a deterministic function of the past purchases $X_1,\dots,X_{t-1}$. It is a Robbins–Monro scheme for the fixed point $\varrho^*$ of $h$.
--
--   **Formalization Note.** Time is 0-based: index $n$ is period $t=n+1$, so the iterate at index $0$ is $\varrho_1$, the purchase at index $n$ is $X_{n+1}$, and the step at index $n$ is $\alpha/((n+1)+\beta)$. The iterate is defined along any sequence of purchases.
-- source:
--   Peeters, den Boer, Mandjes, Continuous Assortment Optimization with Logit Choice Probabilities under Incomplete Information, arXiv:1807.06497v4, §4.2, p.11 (Stochastic Approximation Policy SAP(α, β))

import Mathlib
import Definitions.Def_ContAssortLogit_Model
open MeasureTheory Set

namespace ContAssortLogit

/-- The assortment offered by SAP(α, β) at iterate `ϱ` (arXiv:1807.06497v4, §4.2, p.11):
`S = [w⁻¹(ϱ), 1]`. -/
noncomputable def sapAssort (w : ℝ → ℝ) (ϱ : ℝ) : Set ℝ := Icc (winv w ϱ) 1

/-- The observed revenue `R = w(X) 1{X ∈ S}` when assortment `S = [w⁻¹(ϱ), 1]` is offered and the
customer's (no-)purchase is `X` (arXiv:1807.06497v4, §4.2, p.11). A no-purchase earns `0`. -/
noncomputable def sapReward (w : ℝ → ℝ) (ϱ : ℝ) : PurchaseSpace → ℝ :=
  Sum.elim (fun x => (sapAssort w ϱ).indicator w x) (fun _ => 0)

/-- The iterates of the Stochastic Approximation Policy SAP(α, β) (arXiv:1807.06497v4, §4.2, p.11)
along a sequence of (no-)purchases `X 0, X 1, …`:
`ϱ₁` given, and `ϱ_{t+1} = ϱ_t + a_t (R_t − ϱ_t)` with `a_t = α / (t + β)`,
`R_t = w(X_t) 1{X_t ∈ [w⁻¹(ϱ_t), 1]}`.

**Formalization Note.** Time is 0-based: the paper's period `t ≥ 1` is index `n = t − 1`, so
`sapRho … X 0 = ϱ₁`, `X n` is the paper's `X_{n+1}`, and the step at index `n` is `α / ((n + 1) + β)`.
`sapRho … X n` depends only on `X 0, …, X (n − 1)`. -/
noncomputable def sapRho (w : ℝ → ℝ) (α β ϱ₁ : ℝ) (X : ℕ → PurchaseSpace) : ℕ → ℝ
  | 0 => ϱ₁
  | n + 1 =>
      sapRho w α β ϱ₁ X n +
        α / ((n + 1 : ℝ) + β) * (sapReward w (sapRho w α β ϱ₁ X n) (X n) - sapRho w α β ϱ₁ X n)

end ContAssortLogit


