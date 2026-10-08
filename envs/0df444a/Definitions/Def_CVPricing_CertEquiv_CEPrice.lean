-- Prove2me | Definitions.Def_CVPricing_CertEquiv_CEPrice
-- name    : CVPricing_CertEquiv_CEPrice
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-05T10:12:38.222848+00:00
-- url     : https://prove2.me/theorems/d1df0f80-3e66-4e00-aa35-329734200686
-- title:
--   §3.1, Eq. (5), p. 774 — the certainty equivalent price path driven by a noise path
-- statement:
--   Fix the model of `CVPricing.CertEquiv.Model` and two initial prices $p_1, p_2 \in [p_l, p_h]$. Let $e_1, e_2, \dots$ be a realization of the demand noise, so that the demand in period $t$ is $d_t = a_0^{(0)} + a_1^{(0)} p_t + e_t$.
--
--   **Certainty equivalent pricing** charges $p_1$ and $p_2$ in the first two periods. After $t \ge 2$ periods it computes the least squares estimates $\hat a_t = (\hat a_{0t}, \hat a_{1t})$, the solution of the normal equations
--
--   $$\sum_{i=1}^t \begin{pmatrix} 1 \\ p_i \end{pmatrix} \big(d_i - \hat a_{0t} - \hat a_{1t} p_i\big) = 0, \tag{4}$$
--
--   and charges the price that is optimal for these estimates,
--
--   $$p_{t+1} = \arg\max_{p \in [p_l, p_h]} p\,(\hat a_{0t} + \hat a_{1t} p). \tag{5}$$
--
--   When the estimated slope has the wrong sign, $\hat a_{1t} \ge 0$, the price is $p_{t+1} = p_h$. When $\hat a_{1t} < 0$ the revenue estimate is a strictly concave quadratic, and its maximizer over $[p_l, p_h]$ is the projection of $-\hat a_{0t}/(2\hat a_{1t})$ onto $[p_l, p_h]$:
--
--   $$p_{t+1} = \max\Big(p_l, \min\Big(p_h, \frac{-\hat a_{0t}}{2 \hat a_{1t}}\Big)\Big).$$
--
--   This defines the price path $(p_t)_{t \ge 1}$ as a deterministic function of the noise path; evaluating it at a random noise path gives the random price process of Proposition 1.
--
--   **Formalization Note** The rule $p_{t+1} = p_h$ whenever $\hat a_{1t} \ge 0$ is the convention stated in the proof of Proposition 1 (p. 780): (5) has no unique maximizer when $\hat a_{1t} = 0$ and may have the value $p_l$ when $\hat a_{1t} > 0$, $\hat a_{0t} < 0$. The least squares estimate is the referenced `KeskinZeevi.SufficientConditions.lsEstimateOf`, i.e. $P_t^{-1}\big(\sum d_i, \sum d_i p_i\big)$ with $P_t = \sum_{i \le t} \begin{pmatrix}1 & p_i\\ p_i & p_i^2\end{pmatrix}$, which is the unique solution of (4) whenever two of the prices differ (in particular when $p_1 \ne p_2$). Periods are 1-based; the value at index $0$ is unused.
-- source:
--   den Boer, Zwart, Simultaneously Learning and Optimizing Using Controlled Variance Pricing, Management Science 60(3):770–783 (2014), p. 774 (PDF 6), §2.2 Eq. (4) and §3.1 Eq. (5); p. 780 (PDF 12), Appendix, proof of Proposition 1 (convention p_{t+1} = p_h when â_{1t} ≥ 0)

import Mathlib
import Definitions.Def_CVPricing_CertEquiv_Model
import Definitions.Def_KeskinZeevi_SufficientConditions_LeastSquares

namespace CVPricing.CertEquiv

open KeskinZeevi.SufficientConditions

/-- The certainty-equivalent price chosen from estimates `â = (â₀, â₁)` (§3.1, (5), p. 774, with the
convention of the proof of Proposition 1, p. 780):
* if `â₁ ≥ 0` (wrong-signed slope) the price is `p_h`;
* if `â₁ < 0` the price is `max p_l (min p_h (−â₀ / (2 â₁)))`, which is the unique maximizer of the
  concave quadratic `p ↦ p (â₀ + â₁ p)` over `[p_l, p_h]`. -/
noncomputable def ceRule (M : Model) (â : ℝ × ℝ) : ℝ :=
  if 0 ≤ â.2 then M.ph else max M.pl (min M.ph (-â.1 / (2 * â.2)))

/-- The realized demand `d_s = a₀ + a₁ p_s + e_s` in period `s`, given the price sequence `p` and the
noise path `e` (both indexed by the paper's 1-based period). -/
def demandOf (M : Model) (p e : ℕ → ℝ) (s : ℕ) : ℝ := M.a₀ + M.a₁ * p s + e s

/-- The certainty-equivalent price path `p_t` (§3.1, p. 774) driven by the noise path `e`
(`e s` is the paper's `e_s`, `s ≥ 1`), with initial prices `p₁, p₂`:
* `p_1 = p₁`, `p_2 = p₂`;
* for `t ≥ 3`, `p_t = ceRule M â_{t−1}`, where `â_{t−1}` is the ordinary least squares estimate,
  i.e. the solution of the normal equations (4), computed from the prices `p_1, …, p_{t−1}` and
  demands `d_s = a₀ + a₁ p_s + e_s`, `s ≤ t − 1`.
The value at `t = 0` is `p₁` and is not used. -/
noncomputable def cePrice (M : Model) (p₁ p₂ : ℝ) (e : ℕ → ℝ) : ℕ → ℝ
  | t =>
    if t ≤ 1 then p₁
    else if t = 2 then p₂
    else
      ceRule M (lsEstimateOf (fun s => if s < t then cePrice M p₁ p₂ e s else 0)
        (fun s => if s < t then M.a₀ + M.a₁ * cePrice M p₁ p₂ e s + e s else 0) (t - 1))
termination_by t => t

end CVPricing.CertEquiv


