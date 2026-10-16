-- Prove2me | Definitions.Def_TokenFinance_Debt_Setting
-- name    : TokenFinance_Debt_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-16T04:29:06.010992+00:00
-- url     : https://prove2.me/theorems/b31d63c5-a808-4285-8657-e777ad4e1575
-- title:
--   §II–III — uniform demand U(0, θ), monopoly output and profit (2), NPV (3), equity share (5), debt payoffs (7), the token contract of Proposition 3 and condition (16)
-- statement:
--   This file fixes the model of Malinova and Park, *Tokenomics: When Tokens Beat Equity*, §II–III.
--
--   An entrepreneur pays a set-up cost $C_0$ and then becomes a monopolist facing the linear inverse demand $p(q) = x - q$, where the demand intercept $x$ is revealed only after the set-up cost is paid and is uniformly distributed on $(0,\theta)$. Each unit costs $c$ to produce. Investors require a zero rate of return. The following objects are defined, all as plain functions of real parameters.
--
--   1. **Expectation.** For an integrable payoff $g$ of the demand realization, $\mathsf E_\theta[g] = \frac{1}{\theta}\int_0^\theta g(x)\,dx$, the expectation under $U(0,\theta)$.
--   2. **Monopoly quantity** (2): $q^m(x) = \max\{(x-c)/2,\,0\}$.
--   3. **Monopoly profit**: $\pi^m(x) = \max\{x-c,\,0\}^2/4$, that is $(x-c)^2/4$ for $x \ge c$ and $0$ below $c$, where nothing is produced.
--   4. **Net present value** (3): $\mathrm{NPV}(c,C_0,\theta) = \mathsf E_\theta[\pi^m] - C_0$, defined as the integral, not as its closed form.
--   5. **Equity share** (5): $\alpha_s = C_0 / \mathsf E_\theta[\pi^m]$, the fraction of profits with $\alpha_s\,\mathsf E[\pi^m(x)] = C_0$.
--   6. **Debt payoffs** under a promised repayment $D$: investors receive $\min\{\pi^m(x), D\}$ (the full repayment when the venture is solvent, the whole monopoly profit under the debtor-in-possession arrangement otherwise, zero for $x<c$), and the entrepreneur keeps $\max\{\pi^m(x) - D,\,0\}$.
--   7. **Token contract** of Proposition 3 with $t$ pre-sold tokens: the revenue share $\alpha_t = t/(t+c)$ (12); the entrepreneur's realized profit at demand $x$ and output $q$, equal to $(1-\alpha_t)(q-t)(x-q) - c(q-t)$ when $q > t$ and $0$ when $q \le t$; and the token-holders' realized receipts, $t(x-q) + \alpha_t(q-t)(x-q)$ when $q>t$ and $q(x-q) + c(t-q)$ (output plus refund of unused production cost) when $q \le t$.
--   8. **Condition (16)**, as printed: $\frac{c}{c+t}\cdot\frac{2}{3\theta}\left(\frac{\theta-c}{2} - t\right)^3 = \frac{(\theta-c)^3}{12\theta} - C_0$.
--
--   These are the shared objects used by the four result missions in this series. The formulae for expectations and financial contracts are applied under the paper’s admissible parameter conditions.
--
--   **Formalization Note** All objects live in the namespace `TokenFinance.Debt`, which the other three missions import after consolidation. There is no probability layer: the uniform demand enters only through `expect θ g = (∫ x in 0..θ, g x) / θ`. The case splits of the paper are written with `max`/`min`, so they remain meaningful when the paper's split points lie outside $(0,\theta)$. The token objects (7)–(8) are declared identically in all four missions of this series, so that they can later be merged; they are not used here.
-- source:
--   Malinova & Park, Tokenomics: When Tokens Beat Equity, SSRN 3286825 (version of June 1, 2023), pp. 13–24 (PDF 14–25), (1)–(16), and pp. 39–40 (PDF 40–41)

import Mathlib

namespace TokenFinance.Debt

/-- Expectation under the uniform distribution of demand intercept `x` on `(0, θ)` (p. 13). -/
noncomputable def expect (θ : ℝ) (g : ℝ → ℝ) : ℝ := (∫ x in (0 : ℝ)..θ, g x) / θ

/-- The monopoly quantity (2): `(x − c)/2` for `x ≥ c` and `0` otherwise. -/
noncomputable def qm (c x : ℝ) : ℝ := max ((x - c) / 2) 0

/-- The monopoly profit `π^m(x) = (x − c)²/4` for `x ≥ c`, and `0` below `c` (pp. 14, 16). -/
noncomputable def pim (c x : ℝ) : ℝ := (max (x - c) 0) ^ 2 / 4

/-- The project's expected net present value (3), as an integral of realized profits. -/
noncomputable def npv (c C0 θ : ℝ) : ℝ := expect θ (pim c) - C0

/-- The equity investors' share `α_s` from `α_s E[π^m(x)] = C₀` (5). -/
noncomputable def equityShare (c C0 θ : ℝ) : ℝ := C0 / expect θ (pim c)

/-- What debtholders receive at demand `x` under repayment `D` (p. 16). -/
noncomputable def debtInv (c D x : ℝ) : ℝ := min (pim c x) D

/-- What the entrepreneur keeps at demand `x` under repayment `D`. -/
noncomputable def debtEnt (c D x : ℝ) : ℝ := max (pim c x - D) 0

/-- The revenue share (12) of the token contract. -/
noncomputable def alphaT (c t : ℝ) : ℝ := t / (t + c)

/-- The entrepreneur's realized profit at demand `x` and output `q` under the token contract
of Proposition 3. -/
noncomputable def tokEnt (c t x q : ℝ) : ℝ :=
  if t < q then (1 - alphaT c t) * (q - t) * (x - q) - c * (q - t) else 0

/-- What the token-holders receive at demand `x` and output `q` under the token contract of
Proposition 3. -/
noncomputable def tokInv (c t x q : ℝ) : ℝ :=
  if t < q then t * (x - q) + alphaT c t * (q - t) * (x - q) else q * (x - q) + c * (t - q)

/-- Condition (16) as printed. -/
def tokenBreakEven (c C0 θ t : ℝ) : Prop :=
  c / (c + t) * (2 / (3 * θ)) * ((θ - c) / 2 - t) ^ 3 = (θ - c) ^ 3 / (12 * θ) - C0

end TokenFinance.Debt


