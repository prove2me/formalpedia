-- Prove2me | Definitions.Def_RiskBalancingMNL_Supplement_AsymParams
-- name    : RiskBalancingMNL_Supplement_AsymParams
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:55:08.179944+00:00
-- url     : https://prove2.me/theorems/562063f8-b33e-44ce-8fdd-de047417b572
-- title:
--   MNL with asymmetric price sensitivities $\hat b_i$: shares, profit $\pi$, $g$, $L=\pi^2-\lambda g$, optimality, $\theta$, adjusted markups and $\bar\lambda$
-- statement:
--   A firm sells $n$ products. In the model (16) of §5 the customer's utility for product $i$ is $v_i=a_i+y_i-bp_i+\beta y_ip_i$; writing $\hat a_i=a_i+y_i$ and $\hat b_i=b-\beta y_i>0$ (the effective price sensitivity), the utility at markup $m_i$ (price $p_i=c_i+m_i$) is
--   $$
--   v_i(m_i)=\hat a_i-\hat b_ic_i-\hat b_im_i .
--   $$
--   The multinomial logit choice probabilities are
--   $$
--   q_i(m)=\frac{e^{v_i(m_i)}}{1+\sum_je^{v_j(m_j)}},\qquad q_0(m)=\frac{1}{1+\sum_je^{v_j(m_j)}},
--   $$
--   and the expected profit per customer, the second moment and the risk-balancing objective with risk weight $\lambda$ are $\pi(m)=\sum_im_iq_i(m)$, $g(m)=\sum_im_i^2q_i(m)$ and $L_\lambda(m)=\pi(m)^2-\lambda g(m)$. A markup vector is **feasible** for problem (6) when $\pi(m)\ge0$ and **optimal** when it is feasible and $L_\lambda(m)\ge L_\lambda(m')$ for every feasible $m'\in\mathbb R^n$.
--
--   At a markup vector $m$ the paper's auxiliary quantity of §5.1 is
--   $$
--   \theta=\Big(\frac{\pi}{\lambda}\Big)^2+2\sum_{i=1}^n\frac{(m_i-\pi/\lambda)\,q_i}{\hat b_i\,q_0},
--   $$
--   the **adjusted markup** of product $j$ is $\check m_j=m_j-1/\hat b_j$, and $\bar\lambda=A/(1+A)$ with $A=\sum_ie^{\hat a_i-\hat b_ic_i}$ is the total market share at zero markups.
--
--   These objects carry every statement of §5 in this mission: Eq. (18), Lemma 5, Theorems 2–3 and the fixed-point map of §5.2.
--
--   **Formalization Note** The model is stated in the reduced form $(\hat a,\hat b,c)$; the primitives $a_i,y_i,b,\beta$ enter only through $\hat a_i$ and $\hat b_i$, and every positive $\hat b$ arises from some $y,\beta$. The ordering $\hat b_1\ge\dots\ge\hat b_n$ of p.14 is not built in; statements that use it assume it. Shares are the platform's finite logit share; problem (6) is stated over markups, as in the published symmetric model `RiskBalancingMNL.Params`. $\theta$ is meaningful for $\lambda>0$ only.
-- source:
--   Li & Webster, Optimizing Risk-balancing Return under Discrete Choice Models, SSRN 3959428 (PDF of 2021-11-14), §5, (16) and the definitions of $\hat a_i$, $\hat b_i$, p.14; $\theta$ and the adjusted markup, p.15; problem (6), p.9

import Mathlib
import Definitions.Def_FlagshipMEA_Monopoly_LogitChoice

namespace RiskBalancingMNL.Supplement

/-- Data of the MNL model with asymmetric price sensitivities, Li & Webster, *Optimizing
Risk-balancing Return under Discrete Choice Models*, SSRN 3959428 (PDF of 2021-11-14), §5, (16),
p.14: `n` products with adjusted quality terms `âᵢ = aᵢ + yᵢ`, unit costs `cᵢ`, and effective price
sensitivities `b̂ᵢ = b − βyᵢ`, so that the nominal utility at markup `mᵢ` is
`vᵢ(mᵢ) = âᵢ − b̂ᵢcᵢ − b̂ᵢmᵢ`.

**Formalization Note** The model is in the paper's reduced form `(â, b̂, c)`: the primitives
`aᵢ, yᵢ, b, β` of (16) enter only through `âᵢ` and `b̂ᵢ`, and since `y` and `β` are free every
positive `b̂` arises. `b̂ᵢ > 0` is the paper's assumption on p.14 ("we assume `b̂ᵢ > 0` for all
`i`"). The indexing `b̂₁ ≥ … ≥ b̂ₙ` is not a field: it is a hypothesis of every statement that
uses the order of the products (`Antitone bHat`). -/
structure AsymParams (n : ℕ) where
  aHat : Fin n → ℝ
  c : Fin n → ℝ
  bHat : Fin n → ℝ
  hb : ∀ i, 0 < bHat i

namespace AsymParams

variable {n : ℕ}

/-- The attraction `e^{vᵢ(mᵢ)} = e^{âᵢ − b̂ᵢcᵢ − b̂ᵢmᵢ}` of product `i` (SSRN 3959428, p.14). -/
noncomputable def attraction (P : AsymParams n) (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  Real.exp (P.aHat i - P.bHat i * P.c i - P.bHat i * m i)

/-- The MNL choice probability `qᵢ = e^{vᵢ(mᵢ)} / (1 + Σⱼ e^{vⱼ(mⱼ)})` (SSRN 3959428, p.14,
"the functional form of `vᵢ` in Section 4"; (25), p.18), via the platform's finite logit share. -/
noncomputable def share (P : AsymParams n) (m : Fin n → ℝ) (i : Fin n) : ℝ :=
  FlagshipMEA.Monopoly.logitShare (P.attraction m) i

/-- The no-purchase probability `q₀ = 1 / (1 + Σⱼ e^{vⱼ(mⱼ)})` (SSRN 3959428, §4–§5). -/
noncomputable def noPurchase (P : AsymParams n) (m : Fin n → ℝ) : ℝ :=
  1 / (1 + ∑ j, P.attraction m j)

/-- The expected profit per customer `π = Σᵢ mᵢqᵢ` (SSRN 3959428, p.9). -/
noncomputable def profit (P : AsymParams n) (m : Fin n → ℝ) : ℝ :=
  ∑ i, m i * P.share m i

/-- `g = Σᵢ mᵢ²qᵢ` (SSRN 3959428, p.9). -/
noncomputable def spread (P : AsymParams n) (m : Fin n → ℝ) : ℝ :=
  ∑ i, m i ^ 2 * P.share m i

/-- The risk-balancing objective `L = π² − λg` (SSRN 3959428, p.9 and (17), p.15). -/
noncomputable def objective (P : AsymParams n) (lam : ℝ) (m : Fin n → ℝ) : ℝ :=
  P.profit m ^ 2 - lam * P.spread m

/-- Feasibility in problem (6), SSRN 3959428, p.9: nonnegative expected profit `π ≥ 0`.

**Formalization Note** As in the published `RiskBalancingMNL.Feasible`, (6) is stated over markup
vectors `m ∈ ℝⁿ` through the one-to-one map between markups and shares with every `qᵢ > 0`. -/
def Feasible (P : AsymParams n) (m : Fin n → ℝ) : Prop :=
  0 ≤ P.profit m

/-- `m` is an optimal solution of problem (6) with risk weight `lam` (SSRN 3959428, p.9): it is
feasible and its objective is at least that of every feasible markup vector in `ℝⁿ`.
Optimality is attainment; no interior, equal-markup or existence assumption is built in. -/
def IsOptimal (P : AsymParams n) (lam : ℝ) (m : Fin n → ℝ) : Prop :=
  P.Feasible m ∧ ∀ m' : Fin n → ℝ, P.Feasible m' → P.objective lam m' ≤ P.objective lam m

/-- `θ := (π/λ)² + 2 Σᵢ (mᵢ − π/λ) qᵢ / (b̂ᵢ q₀)`, SSRN 3959428, §5.1, p.15, exactly as printed,
with `π`, `qᵢ`, `q₀` evaluated at the markup vector `m`.

**Formalization Note** Meaningful for `λ > 0`; at `λ = 0` Lean's `x / 0 = 0` gives a junk value,
and every statement using `theta` assumes `0 < λ`. -/
noncomputable def theta (P : AsymParams n) (lam : ℝ) (m : Fin n → ℝ) : ℝ :=
  (P.profit m / lam) ^ 2 +
    2 * ∑ i, (m i - P.profit m / lam) * P.share m i / (P.bHat i * P.noPurchase m)

/-- The adjusted markup `m̌ⱼ := mⱼ − 1/b̂ⱼ` (SSRN 3959428, p.15). -/
noncomputable def adjMarkup (P : AsymParams n) (m : Fin n → ℝ) (j : Fin n) : ℝ :=
  m j - 1 / P.bHat j

/-- `A = Σᵢ e^{âᵢ − b̂ᵢcᵢ}`, the total attraction at zero markups (SSRN 3959428, §5). -/
noncomputable def zeroMarkupMass (P : AsymParams n) : ℝ :=
  ∑ i, Real.exp (P.aHat i - P.bHat i * P.c i)

/-- `λ̄ = A / (1 + A)`, the total market share at zero markups (SSRN 3959428, p.11 for the
symmetric model, and p.22, "the case of symmetric price sensitivity"), for the asymmetric model. -/
noncomputable def lamBar (P : AsymParams n) : ℝ :=
  P.zeroMarkupMass / (1 + P.zeroMarkupMass)

end AsymParams

end RiskBalancingMNL.Supplement


