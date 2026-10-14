-- Prove2me | Definitions.Def_RefMNLPricing_Myopic_Equation13
-- name    : RefMNLPricing_Myopic_Equation13
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:15.9104+00:00
-- url     : https://prove2.me/theorems/d4aba00f-a27a-4f73-8232-89221cc5541c
-- title:
--   Definition 3 and (13), p. 12 — the auxiliary functions λ_i, γ_i, the threshold Z_i and the right-hand side of (13)
-- statement:
--   These are the auxiliary functions of Definition 3 and the right-hand side of equation (13), which characterises the optimal single-period revenue of the myopic problem.
--
--   For a gain-seeking product ($c_i^+ > c_i^-$) define the threshold
--
--   $$
--   Z_i := \frac{\log(b_i + c_i^+) - \log(b_i + c_i^-)}{c_i^+ - c_i^-}.
--   $$
--
--   For a loss-averse product ($c_i^+ < c_i^-$) and a scalar $\Pi$,
--
--   $$
--   \begin{aligned}
--   \lambda_i(\Pi,r_i) :=\;& \mathbb 1\Big\{r_i < \Pi + \tfrac{1}{b_i+c_i^-}\Big\}\,\tfrac{1}{b_i+c_i^-}\, e^{a_i - (b_i+c_i^-)\Pi + c_i^- r_i - 1} \\
--   &+ \mathbb 1\Big\{\Pi + \tfrac{1}{b_i+c_i^-} \le r_i \le \Pi + \tfrac{1}{b_i+c_i^+}\Big\}\,(r_i - \Pi)\, e^{a_i - b_i r_i} \\
--   &+ \mathbb 1\Big\{r_i > \Pi + \tfrac{1}{b_i+c_i^+}\Big\}\,\tfrac{1}{b_i+c_i^+}\, e^{a_i - (b_i+c_i^+)\Pi + c_i^+ r_i - 1},
--   \end{aligned}
--   $$
--
--   and for a gain-seeking product
--
--   $$
--   \gamma_i(\Pi,r_i) := \mathbb 1\{r_i < \Pi + Z_i\}\,\tfrac{1}{b_i+c_i^-}\, e^{a_i - (b_i+c_i^-)\Pi + c_i^- r_i - 1} + \mathbb 1\{r_i \ge \Pi + Z_i\}\,\tfrac{1}{b_i+c_i^+}\, e^{a_i - (b_i+c_i^+)\Pi + c_i^+ r_i - 1}.
--   $$
--
--   The right-hand side of (13) is
--
--   $$
--   F(\Pi, r) := \sum_{i\in N_l} \lambda_i(\Pi,r_i) + \sum_{i\in N_n} \frac{1}{b_i+c_i}\, e^{a_i - (b_i+c_i)\Pi + c_i r_i - 1} + \sum_{i\in N_g} \gamma_i(\Pi,r_i),
--   $$
--
--   where $N_l, N_n, N_g$ are the loss-averse ($c_i^+<c_i^-$), loss-neutral ($c_i^+=c_i^-=:c_i$) and gain-seeking ($c_i^+>c_i^-$) products.
--
--   Theorem 1 states that the optimal single-period revenue $\Pi^m(r)$ is the unique root of $\Pi = F(\Pi,r)$, and Corollary 1 that $F$ is non-increasing in $\Pi$.
--
--   **Formalization Note** The variable `rev` stands for $\Pi$ (`Π` is reserved in Lean). The three sums of (13) are written as one sum over all products whose term is selected by the product's type; this equals the paper's three sums. The indicators are `if … then … else 0` with exactly the paper's boundary conventions (closed middle interval in $\lambda_i$, $<$ / $\ge$ in $\gamma_i$). $Z_i$ is defined for every product but used only for gain-seeking ones, where $c_i^+ - c_i^- > 0$.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), p. 12, Definition 3 (11)–(12), Theorem 1 (13)

import Mathlib
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Myopic

/-- The threshold `Z_i := (log(b_i + c_i⁺) - log(b_i + c_i⁻)) / (c_i⁺ - c_i⁻)` of Definition 3,
p. 12. It is only meaningful for a gain-seeking product (`c_i⁻ < c_i⁺`); every statement uses it
only under that hypothesis. -/
noncomputable def Zgap {n : ℕ} (b cp cm : Fin n → ℝ) (i : Fin n) : ℝ :=
  (Real.log (b i + cp i) - Real.log (b i + cm i)) / (cp i - cm i)

/-- `λ_i(Π, r_i)` of (11), Definition 3, p. 12, for a loss-averse product (`c_i⁺ < c_i⁻`), written
literally as the sum of three indicator terms:
`𝟙{r_i < Π + 1/(b_i+c_i⁻)} · 1/(b_i+c_i⁻) · exp(a_i - (b_i+c_i⁻)Π + c_i⁻ r_i - 1)
 + 𝟙{Π + 1/(b_i+c_i⁻) ≤ r_i ≤ Π + 1/(b_i+c_i⁺)} · (r_i - Π) · exp(a_i - b_i r_i)
 + 𝟙{r_i > Π + 1/(b_i+c_i⁺)} · 1/(b_i+c_i⁺) · exp(a_i - (b_i+c_i⁺)Π + c_i⁺ r_i - 1)`.
The variable `rev` stands for the paper's `Π`. -/
noncomputable def lam {n : ℕ} (a b cp cm : Fin n → ℝ) (rev : ℝ) (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  (if r i < rev + 1 / (b i + cm i) then
      1 / (b i + cm i) * Real.exp (a i - (b i + cm i) * rev + cm i * r i - 1)
    else 0) +
  (if rev + 1 / (b i + cm i) ≤ r i ∧ r i ≤ rev + 1 / (b i + cp i) then
      (r i - rev) * Real.exp (a i - b i * r i)
    else 0) +
  (if rev + 1 / (b i + cp i) < r i then
      1 / (b i + cp i) * Real.exp (a i - (b i + cp i) * rev + cp i * r i - 1)
    else 0)

/-- `γ_i(Π, r_i)` of (12), Definition 3, p. 12, for a gain-seeking product (`c_i⁺ > c_i⁻`):
`𝟙{r_i < Π + Z_i} · 1/(b_i+c_i⁻) · exp(a_i - (b_i+c_i⁻)Π + c_i⁻ r_i - 1)
 + 𝟙{r_i ≥ Π + Z_i} · 1/(b_i+c_i⁺) · exp(a_i - (b_i+c_i⁺)Π + c_i⁺ r_i - 1)`.
The variable `rev` stands for the paper's `Π`. -/
noncomputable def gam {n : ℕ} (a b cp cm : Fin n → ℝ) (rev : ℝ) (r : Fin n → ℝ) (i : Fin n) : ℝ :=
  (if r i < rev + Zgap b cp cm i then
      1 / (b i + cm i) * Real.exp (a i - (b i + cm i) * rev + cm i * r i - 1)
    else 0) +
  (if rev + Zgap b cp cm i ≤ r i then
      1 / (b i + cp i) * Real.exp (a i - (b i + cp i) * rev + cp i * r i - 1)
    else 0)

/-- The right-hand side of (13), Theorem 1, p. 12, as a function of `Π` (here `rev`) and `r`:
`∑_{i ∈ N_l} λ_i(Π, r_i) + ∑_{i ∈ N_n} 1/(b_i+c_i) · exp(a_i - (b_i+c_i)Π + c_i r_i - 1)
 + ∑_{i ∈ N_g} γ_i(Π, r_i)`, written as one sum over all products whose term is chosen by the
product's type (Definition 2): loss-averse `c_i⁺ < c_i⁻`, loss-neutral `c_i⁺ = c_i⁻` (with
`c_i := c_i⁺`), gain-seeking otherwise (`c_i⁻ < c_i⁺`). -/
noncomputable def rhs13 {n : ℕ} (a b cp cm : Fin n → ℝ) (rev : ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ i, if cp i < cm i then lam a b cp cm rev r i
    else if cp i = cm i then
      1 / (b i + cp i) * Real.exp (a i - (b i + cp i) * rev + cp i * r i - 1)
    else gam a b cp cm rev r i

end RefMNLPricing.Myopic


