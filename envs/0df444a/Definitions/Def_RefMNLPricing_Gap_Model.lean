-- Prove2me | Definitions.Def_RefMNLPricing_Gap_Model
-- name    : RefMNLPricing_Gap_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-14T05:15:40.555483+00:00
-- url     : https://prove2.me/theorems/40a21e07-b1fa-47b4-8d5f-f872d467ca27
-- title:
--   §2, pp. 9–11, and (19), p. 17 — reference path (1), discounted revenue, optimal value V⋆, myopic selections and V^m, ceiling assumption (9), constant ω
-- statement:
--   This file adds to the multi-product pricing model of Guo, Jiang and Shen (the utilities, market shares, revenue $\Pi$, price box $\mathcal P^n=[0,p_H]^n$, right-hand side of (9) and myopic reference path, all defined in `RefMNLPricing.Myopic.Model`) the objects of the dynamic problem: the reference path of an arbitrary price sequence, the discounted revenue, the optimal value $V^\star$, the myopic value $V^m$, and the constant $\omega$ of the optimality-gap bound.
--
--   The products are $i\in N=\{1,\dots,n\}$ with parameters $a_i$ (intrinsic utility), $b_i$ (price sensitivity), $c_i^+$ and $c_i^-$ (sensitivities to gains and to losses relative to the reference price).
--
--   1. **Ceiling constant and ceiling assumption** ((9), §2.4). With
--   $$\chi=\max_{i\in N}\frac{1}{b_i+\min\{c_i^+,c_i^-\}},$$
--   the ceiling assumption says that some solution $\hat p_H$ of
--   $$p=\chi+\sum_{i\in N}\frac{1}{b_i+c_i^+}\exp\big(a_i-b_ip+(b_i+c_i^+)\chi-1\big)$$
--   satisfies $\hat p_H\le p_H$. Equation (9) has a unique solution (Proposition 1.2), so this is the paper's $p_H\ge\hat p_H$.
--   2. **Reference path** ((1)). For a memory parameter $\alpha$, an initial reference price $\mathbf r^0$ and a price sequence $(\mathbf p^t)_{t\ge0}$: $\mathbf r^{t+1}=\alpha\mathbf r^t+(1-\alpha)\mathbf p^t$.
--   3. **Discounted revenue** (objective of (5)). For a discount factor $\beta$, the sequence earns $\sum_{t\ge0}\beta^t\,\Pi(\mathbf p^t,\mathbf r^t)$.
--   4. **Optimal value** ((5)–(6)).
--   $$V^\star(\mathbf r^0)=\sup_{(\mathbf p^t)_{t\ge0}\subseteq\mathcal P^n}\ \sum_{t=0}^{\infty}\beta^t\,\Pi(\mathbf p^t,\mathbf r^t),$$
--   the supremum of the discounted revenue over all admissible price sequences. It is written as an instance of Karlin's deterministic dynamic program: the state is the reference price, a decision is a price vector in $\mathcal P^n$, the one-period return is $\Pi(\mathbf p,\mathbf r)$, the transition is (1), and the discount factor is the constant $\beta$.
--   5. **Myopic selections and the myopic value** ((7), (8)). A myopic selection is a map $\mathbf p^m$ such that, for every $\mathbf r\in\mathcal P^n$, $\mathbf p^m(\mathbf r)\in\mathcal P^n$ maximises $\Pi(\cdot,\mathbf r)$ over $\mathcal P^n$. Its value is
--   $$V^m(\mathbf r^0)=\sum_{t\ge0}\beta^t\,\Pi(\mathbf p^m(\mathbf r^t),\mathbf r^t),\qquad \mathbf r^{t+1}=\alpha\mathbf r^t+(1-\alpha)\mathbf p^m(\mathbf r^t).$$
--   6. **The constant of the optimality gap** ((19)).
--   $$\omega=\max_{i\in N}\Big\{\frac{c_i^+}{b_i+c_i^+},\ \frac{c_i^-}{b_i+c_i^-}\Big\}.$$
--
--   These objects carry the Bellman equation (6), the comparison $V^m\le V^\star$, the dependence of $V^\star$ on the ceiling (Proposition 1.1) and the optimality-gap bound (Proposition 2), and the ceiling assumption is a hypothesis of most results of §3–§4.
--
--   **Formalization Note** Products are indexed by `Fin n`, so the paper's product $i$ is Lean index $i-1$. $V^\star$ is `optValue`, built on the published `KarlinDP.Deterministic.optimalReturn`, whose total yield with constant weight $\beta$ is $\sum_t\beta^t\Pi(\mathbf p^t,\mathbf r^t)$. The paper writes (5) as a maximum over stationary policies and then uses the Bellman equation (6); for this deterministic problem with continuous $\Pi$ on the compact box the two values coincide. The supremum is Lean's real `⨆`, which would be $0$ on an unbounded or empty family; every theorem assumes $0\le\beta<1$ and $p_H>0$, under which the family is nonempty and bounded by $p_H/(1-\beta)$. The maxima $\chi$ and $\omega$ over $N$ are written `⨆ i`, which is $0$ when $n=0$. A myopic selection is any maximiser selection, since maximisers need not be unique. `chi`, `CeilingOK` and `IsMyopicSel` here are definitionally the same as `RefMNLPricing.Myopic.chi`, `.CeilingOK` and `.IsMyopicSel`, and `optValue` equals `RefMNLPricing.GainSeeking.optValue`. The standing assumptions $b>0$, $c^\pm\ge0$, $\alpha\in[0,1]$, $\beta\in[0,1)$, $p_H>0$ are hypotheses of the theorems, not part of the definitions.
-- source:
--   Guo, Jiang, Shen, Multi-Product Dynamic Pricing with Reference Effects Under Logit Demand, SSRN 4189049 (version of 2024-05-25), pp. 7–11, Definition 1 (1), (5)–(9), §2.4 p. 11; p. 17, the constant ω of (19)

import Mathlib
import Definitions.Def_KarlinDP_Deterministic_Model
import Definitions.Def_RefMNLPricing_Myopic_Model

namespace RefMNLPricing.Gap

/-! Model of Guo, Jiang, Shen, *Multi-Product Dynamic Pricing with Reference Effects Under Logit
Demand* (SSRN 4189049, version of 2024-05-25), §2, pp. 7–11, and the constant `ω` of (19), p. 17.

Products are indexed by `Fin n` (the paper's product `i` is index `i - 1`). The parameters are
`a b cp cm : Fin n → ℝ` for the intrinsic utilities `a`, the price sensitivities `b`, and the
reference-price sensitivities `c⁺` (`cp`, gains) and `c⁻` (`cm`, losses). The paper's standing
assumptions `b > 0`, `c⁺, c⁻ ≥ 0`, `α ∈ [0, 1]`, `β ∈ [0, 1)`, `p_H > 0` are hypotheses of the
theorems, not part of these definitions. -/

variable {n : ℕ}

/-- `χ = max_i 1/(b_i + min{c_i⁺, c_i⁻})` of (9), p. 10. The maximum over `Fin n` is written `⨆ i`,
which is `0` when `n = 0`. -/
noncomputable def chi (b cp cm : Fin n → ℝ) : ℝ :=
  ⨆ i, 1 / (b i + min (cp i) (cm i))

/-- The standing ceiling assumption of §2.4, p. 11: `p_H ≥ p̂_H`, where `p̂_H` solves (9). -/
def CeilingOK (a b cp cm : Fin n → ℝ) (pH : ℝ) : Prop :=
  ∃ pHat : ℝ, pHat = RefMNLPricing.Myopic.ceilRHS a b cp cm pHat ∧ pHat ≤ pH

/-- The reference-price path (1), p. 7: `r⁰ = r₀`, `r^{t+1} = α r^t + (1 − α) p^t`. -/
def refPath (α : ℝ) (r₀ : Fin n → ℝ) (p : ℕ → Fin n → ℝ) : ℕ → Fin n → ℝ
  | 0 => r₀
  | t + 1 => fun i => α * refPath α r₀ p t i + (1 - α) * p t i

/-- The long-term discounted revenue of a price sequence `p` from reference `r₀` (objective of (5),
p. 9): `Σ_t β^t Π(p^t, r^t)` along the reference path (1). -/
noncomputable def disc (a b cp cm : Fin n → ℝ) (α β : ℝ) (p : ℕ → Fin n → ℝ)
    (r₀ : Fin n → ℝ) : ℝ :=
  ∑' t, β ^ t * RefMNLPricing.Myopic.revenue a b cp cm (p t) (refPath α r₀ p t)

/-- The optimal value function `V⋆(r₀)` of (5)–(6), p. 9, as an instance of Karlin's deterministic
dynamic program (`KarlinDP.Deterministic.optimalReturn`): the state is the reference price
`r ∈ ℝⁿ`, a decision is a price vector in `Pⁿ = [0, p_H]ⁿ`, the one-period return is `Π(p, r)`,
the transition is (1), `r ↦ α r + (1 − α) p`, and every stage is discounted by the constant
factor `β`. So `V⋆(r₀) = sup_{(p^t) ⊆ Pⁿ} Σ_t β^t Π(p^t, r^t)`, the supremum over all admissible
price sequences. -/
noncomputable def optValue (a b cp cm : Fin n → ℝ) (α β pH : ℝ) (r₀ : Fin n → ℝ) : ℝ :=
  KarlinDP.Deterministic.optimalReturn
    (fun (r : Fin n → ℝ) (p : Fin n → Set.Icc (0 : ℝ) pH) =>
      RefMNLPricing.Myopic.revenue a b cp cm (fun i => (p i : ℝ)) r)
    (fun (p : Fin n → Set.Icc (0 : ℝ) pH) (r : Fin n → ℝ) =>
      fun i => α * r i + (1 - α) * (p i : ℝ))
    (fun _ => β) r₀

/-- A myopic selection (7), p. 9: on `Pⁿ`, `pm r` lies in `Pⁿ` and maximises `Π(·, r)` over `Pⁿ`. -/
def IsMyopicSel (a b cp cm : Fin n → ℝ) (pH : ℝ) (pm : (Fin n → ℝ) → (Fin n → ℝ)) : Prop :=
  ∀ r, RefMNLPricing.Myopic.InBox pH r → RefMNLPricing.Myopic.InBox pH (pm r) ∧
    ∀ p, RefMNLPricing.Myopic.InBox pH p → RefMNLPricing.Myopic.revenue a b cp cm p r ≤ RefMNLPricing.Myopic.revenue a b cp cm (pm r) r

/-- The myopic value function `V^m(r₀)` (8), p. 10: the discounted revenue of the price sequence
`p^t = p^m(r^t)` generated by the myopic selection `pm`. -/
noncomputable def myopicValue (a b cp cm : Fin n → ℝ) (α β : ℝ)
    (pm : (Fin n → ℝ) → (Fin n → ℝ)) (r₀ : Fin n → ℝ) : ℝ :=
  disc a b cp cm α β (fun t => pm (RefMNLPricing.Myopic.myopicRef pm α r₀ t)) r₀

/-- The constant `ω = max_{i ∈ N} {c_i⁺/(b_i + c_i⁺), c_i⁻/(b_i + c_i⁻)}` of (19), p. 17. The
maximum over `Fin n` is written `⨆ i`, which is `0` when `n = 0`. -/
noncomputable def omega (b cp cm : Fin n → ℝ) : ℝ :=
  ⨆ i, max (cp i / (b i + cp i)) (cm i / (b i + cm i))

end RefMNLPricing.Gap


