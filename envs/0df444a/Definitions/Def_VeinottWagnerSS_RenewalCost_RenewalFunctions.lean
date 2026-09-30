-- Prove2me | Definitions.Def_VeinottWagnerSS_RenewalCost_RenewalFunctions
-- name    : VeinottWagnerSS_RenewalCost_RenewalFunctions
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-09-29T12:56:43.257853+00:00
-- url     : https://prove2.me/theorems/cfb12f82-3ce3-4fcd-8c54-d14b2312a8c6
-- title:
--   The renewal quantities $m_\alpha$, $M_\alpha$, $L_\alpha(x,d)$ (Eq. (7)) and $r_\alpha(d)$ (Eq. (9), first line)
-- statement:
--   Let $\varphi$ be a demand distribution with convolution powers $\varphi^i$ and distribution functions $\Phi^i$, let $\alpha$ be the one-period discount factor, and let $G_\alpha : \mathbb Z \to \mathbb R$ be the one-period (holding and penalty) cost. Veinott and Wagner define, for integers $x$ and $d, k \in \{0, 1, \dots\}$:
--   $$m_\alpha(k) = \sum_{i=1}^{\infty} \alpha^i \varphi^i(k), \qquad M_\alpha(k) = \sum_{i=1}^{\infty} \alpha^i \Phi^i(k),$$
--   the latter being the **discount renewal function**;
--   $$L_\alpha(x, d) = G_\alpha(x) + \sum_{i=1}^{\infty} \sum_{k=0}^{d} \alpha^i G_\alpha(x-k)\,\varphi^i(k), \tag{7}$$
--   the expected discounted cost $G_\alpha$ incurred during periods $1, \dots, T(d)$, where $T(d)$ is the first period in which cumulative demand exceeds $d$ and no order is placed before; and
--   $$r_\alpha(d) = \sum_{i=1}^{\infty} \alpha^i\bigl[\Phi^{i-1}(d) - \Phi^i(d)\bigr],$$
--   which is $E[\alpha^{T(d)}]$ because $\Pr[T(d) = i] = \Phi^{i-1}(d) - \Phi^i(d)$.
--
--   These are the ingredients of the closed form (10)–(11) for the discounted cost of a stationary $(s, S)$ policy.
--
--   **Formalization Note** $L_\alpha$ is taken to be the series (7) and $r_\alpha$ the series in the first line of (9); the paper derives both from the description via $T(d)$, and that derivation is not formalized. The paper's sums over $i \ge 1$ are written with index $i+1$, $i \ge 0$. All four are real `tsum`s, whose value is the paper's whenever the series is summable, which holds for $0 \le \alpha < 1$ and, by Appendix §1 of the paper, for $0 \le \alpha \le 1$ with $\alpha\varphi(0) < 1$. The paper's identity $M_\alpha(k) = \sum_{j=0}^{k} m_\alpha(j)$ is a consequence, not part of the definition.
-- source:
--   Veinott & Wagner, Computing Optimal (s, S) Inventory Policies, Management Sci. 11 (1965), p. 532, Eq. (7) and the definitions of m_α, M_α; p. 533, r_α(d) ≡ E[α^{T(d)}] and the first line of Eq. (9)

import Mathlib
import Definitions.Def_VeinottWagnerSS_RenewalCost_Demand

namespace VeinottWagnerSS.RenewalCost

/-- `m_α(k) ≡ ∑_{i=1}^{∞} αⁱ φⁱ(k)` (Veinott & Wagner 1965, p. 532). The paper's index `i ≥ 1`
is written `i + 1` with `i : ℕ`. A real `tsum`: it is the paper's value whenever the series is
summable (for instance `0 ≤ α < 1`, or `α ≤ 1` with `α φ(0) < 1`, Appendix §1). -/
noncomputable def mAlpha (φ : ℕ → ℝ) (α : ℝ) (k : ℕ) : ℝ :=
  ∑' i : ℕ, α ^ (i + 1) * convPow φ (i + 1) k

/-- The discount renewal function `M_α(k) ≡ ∑_{i=1}^{∞} αⁱ Φⁱ(k)` (p. 532). The index `i ≥ 1`
is written `i + 1`. A real `tsum`, meaningful when the series is summable (Appendix §1). -/
noncomputable def MAlpha (φ : ℕ → ℝ) (α : ℝ) (k : ℕ) : ℝ :=
  ∑' i : ℕ, α ^ (i + 1) * cdfPow φ (i + 1) k

/-- `L_α(x, d)`, the expected discounted one-period cost `G_α` accumulated during the periods
`1, ⋯, T(d)` before cumulative demand first exceeds `d`, starting from stock `x` with no order,
**taken as the series (7)** of p. 532:
`L_α(x, d) = G_α(x) + ∑_{i=1}^{∞} ∑_{k=0}^{d} αⁱ G_α(x − k) φⁱ(k)`.
The paper's index `i ≥ 1` is written `i + 1`. -/
noncomputable def LAlpha (φ : ℕ → ℝ) (α : ℝ) (G : ℤ → ℝ) (x : ℤ) (d : ℕ) : ℝ :=
  G x + ∑' i : ℕ, ∑ k ∈ Finset.range (d + 1), α ^ (i + 1) * G (x - (k : ℤ)) * convPow φ (i + 1) k

/-- `r_α(d) ≡ E[α^{T(d)}]`, where `T(d)` is the first period in which cumulative demand exceeds
`d`, **taken as the series in the first line of (9)** (p. 533), which uses the law
`Pr[T(d) = i] = Φ^{i−1}(d) − Φⁱ(d)` displayed on the same page:
`r_α(d) = ∑_{i=1}^{∞} αⁱ [Φ^{i−1}(d) − Φⁱ(d)]`. The index `i ≥ 1` is written `i + 1`. -/
noncomputable def rAlpha (φ : ℕ → ℝ) (α : ℝ) (d : ℕ) : ℝ :=
  ∑' i : ℕ, α ^ (i + 1) * (cdfPow φ i d - cdfPow φ (i + 1) d)

end VeinottWagnerSS.RenewalCost


