-- Prove2me | Definitions.Def_RobustCtxPricing_Supplement_Algorithm5
-- name    : RobustCtxPricing_Supplement_Algorithm5
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:03:38.537201+00:00
-- url     : https://prove2.me/theorems/9303cfb7-f96b-413c-a7d7-0551d0edb6c3
-- title:
--   Algorithm 5 — robust contextual pricing with unknown corruption (randomized commit with a discounted matrix counter)
-- statement:
--   This module defines Algorithm 5 of Castiglioni–Stradi (§5, p.24), which is given the horizon $T$ and a confidence parameter $\delta\in(0,1)$ but **not** the corruption budget.
--
--   Set $\epsilon=\eta=T^{-3}$ and
--   $$
--   \beta=\Big\lceil 8\log\frac{32T}{\delta}\Big\rceil,\qquad \alpha=\exp(-4/\beta).
--   $$
--   The state is a density $\mu_t$ on $\Theta$ (initially uniform), one evidence set $\mathcal H$ (initially empty), and a matrix $M_t\in\mathbb R^{(d+1)\times(d+1)}$ with $M_1=\eta^2 I_{d+1}$. In round $t$:
--
--   1. **Commit**, if $\mathcal H$ satisfies the prediction test (1) for $u_t$: with coefficients $\lambda_t$ satisfying (1), let $\hat v_t=\sum_i\lambda_{t,i}p_i$, $\tilde v_t=\mathrm{clip}_{[0,1]}(\hat v_t)$, $a_t=(u_t,-\tilde v_t)\in\mathbb R^{d+1}$,
--   $$
--   \gamma_t=\sqrt{a_t^\top M_t^{-1}a_t},\qquad q_t=\min\{\tfrac12,\beta\gamma_t\},\qquad L_t=\max\{0,\tilde v_t-\tfrac1{8T}\},\qquad U_t=\tilde v_t+\tfrac1{4T}.
--   $$
--   Post $U_t$ with probability $q_t$ and $L_t$ otherwise, observe $Y_t$, and set $\bar M_t=M_t+a_ta_t^\top/\gamma_t$ ($\bar M_t=M_t$ when $a_t=0$). The round *fails* if $L_t$ was posted and $Y_t=0$, or $U_t$ was posted and $Y_t=1$; then $\mathcal H\leftarrow\emptyset$ and $M_{t+1}=\alpha^2\bar M_t$, otherwise $M_{t+1}=\bar M_t$. The density is kept.
--   2. **Explore**, otherwise: post an $\epsilon$-window median $m_t$ of $\mu_t$ in direction $u_t$, observe $Y_t$, append $(u_t,m_t)$ to $\mathcal H$, update the density by Update-Density (Algorithm 3), and keep $M$.
--
--   The module fixes the helpers $\mathrm{clip}$, $a_t$, $\beta$, $\alpha$, $\gamma_t$, $q_t$, $\bar M_t$, $L_t$, $U_t$, a run structure (density, evidence set, matrix, the pre-coin choice $w_t$, which is $m_t$ or $\hat v_t$, and the price), and the run relation `IsAlg5Run`, which takes the learner's coins $\xi_t$ as an input: $U_t$ is posted iff $\xi_t<q_t$.
--
--   **Formalization Note** $\mathbb R^{d+1}$ is `Fin (d+1) → ℝ` and $M^{-1}$ is Mathlib's matrix inverse; along a run $M_t$ is positive definite, so it is the true inverse, and for $a_t=0$ the score is $0$, as the paper sets. With $\xi_t$ uniform on $[0,1]$, "post $U_t$ with probability $q_t$" is "post $U_t$ iff $\xi_t<q_t$". The tie-breaks are left free here; that they are functions of the history is imposed by `IsUnknownCInteraction`.
-- source:
--   Castiglioni and Stradi, Decoupling Corruption and Horizon in Robust Contextual Pricing, arXiv:2607.11210, §5, Algorithm 5, p.24; Equations (4)–(5) p.23, (6)–(7) p.24, (8)–(9) and the convention for a_t = 0 p.25, (10) p.26

import Mathlib
import Definitions.Def_RobustCtxPricing_Model
import Definitions.Def_RobustCtxPricing_Evidence
import Definitions.Def_RobustCtxPricing_Density
import Definitions.Def_RobustCtxPricing_Algorithm4

open Matrix

namespace RobustCtxPricing.Supplement

/-- **Clipping to `[0,1]`, Equation (4).** Castiglioni–Stradi, *Decoupling Corruption and Horizon
in Robust Contextual Pricing*, arXiv:2607.11210, §5.1, p.23: `ṽ_t = clip_{[0,1]}(v̂_t)`. -/
def clip01 (x : ℝ) : ℝ :=
  max 0 (min 1 x)

/-- **The augmented vector `a_t`, Equation (5).** Castiglioni–Stradi, arXiv:2607.11210, §5.1,
p.23: `a_t = (u_t, −ṽ_t) ∈ ℝ^{d+1}`.

**Formalization Note.** `ℝ^{d+1}` is `Fin (d + 1) → ℝ`; the first `d` coordinates are those of
`u_t` and the last one is `−ṽ_t`. -/
def augVec {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (v : ℝ) : Fin (d + 1) → ℝ :=
  Fin.snoc (fun i => u i) (-v)

/-- **The checking multiplier `β`, Equation (6).** Castiglioni–Stradi, arXiv:2607.11210, §5.1,
p.24: `β = ⌈8 log(32T/δ)⌉`.

**Formalization Note.** `log` is the natural logarithm; the ceiling is `Nat.ceil` (its argument is
positive for `T ≥ 1`, `δ ∈ (0,1)`). -/
noncomputable def beta5 (T : ℕ) (δ : ℝ) : ℝ :=
  (⌈8 * Real.log (32 * (T : ℝ) / δ)⌉₊ : ℝ)

/-- **The matrix discount `α`, Equation (6).** Castiglioni–Stradi, arXiv:2607.11210, §5.1, p.24:
`α = exp(−4/β)`. -/
noncomputable def alpha5 (T : ℕ) (δ : ℝ) : ℝ :=
  Real.exp (-4 / beta5 T δ)

/-- **The score `γ_t`, Equation (7).** Castiglioni–Stradi, arXiv:2607.11210, §5.1, p.24:
`γ_t = sqrt(a_tᵀ M_t⁻¹ a_t)`.

**Formalization Note.** `M⁻¹` is Mathlib's matrix inverse; along a run `M_t` is positive definite
(`M_1 = η² I`, rank-one positive semidefinite insertions, positive rescalings), so it is the true
inverse. For `a_t = 0` the value is `0`, which is the convention of p.25 ("When `a_t = 0`, we set
`γ_t = q_t = 0`"). -/
noncomputable def score {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a : Fin (d + 1) → ℝ) : ℝ :=
  Real.sqrt (a ⬝ᵥ (M⁻¹ *ᵥ a))

/-- **The checking probability `q_t`, Equation (7).** Castiglioni–Stradi, arXiv:2607.11210, §5.1,
p.24: `q_t = min{1/2, β γ_t}`. -/
noncomputable def checkProb {d : ℕ} (T : ℕ) (δ : ℝ) (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a : Fin (d + 1) → ℝ) : ℝ :=
  min (1 / 2) (beta5 T δ * score M a)

/-- **The matrix insertion `M̄_t`, Equation (9).** Castiglioni–Stradi, arXiv:2607.11210, §5.1,
p.25: `M̄_t = M_t + a_t a_tᵀ / γ_t`, and "When `a_t = 0`, we set `γ_t = q_t = 0` and `M̄_t = M_t`".
-/
noncomputable def insertMat {d : ℕ} (M : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (a : Fin (d + 1) → ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  if a = 0 then M else M + (score M a)⁻¹ • vecMulVec a a

/-- **The lower price `L_t`, Equation (8).** Castiglioni–Stradi, arXiv:2607.11210, §5.1, p.25:
`L_t = max{0, ṽ_t − 1/(8T)}`. -/
noncomputable def lowerPrice (T : ℕ) (v : ℝ) : ℝ :=
  max 0 (v - 1 / (8 * (T : ℝ)))

/-- **The upper price `U_t`, Equation (8).** Castiglioni–Stradi, arXiv:2607.11210, §5.1, p.25:
`U_t = ṽ_t + 1/(4T)`. -/
noncomputable def upperPrice (T : ℕ) (v : ℝ) : ℝ :=
  v + 1 / (4 * (T : ℝ))

/-- **A run of Algorithm 5: the trajectory of its state and prices.** For a round `t` (`0`-based),
`μ t` is the density held at the start of round `t`, `H t` the single evidence set `𝓗`, `M t` the
matrix `M_t ∈ ℝ^{(d+1)×(d+1)}`, `w t` the learner's choice in round `t` before its coin is used
(the ϵ-window median `m_t` in an exploration round, the estimate `v̂_t` in a commit round), and
`p t` the posted price. -/
structure Run5 (d : ℕ) where
  /-- the density held at the start of each round -/
  μ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ
  /-- the evidence set held at the start of each round -/
  H : ℕ → List (EuclideanSpace ℝ (Fin d) × ℝ)
  /-- the matrix `M_t` held at the start of each round -/
  M : ℕ → Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ
  /-- the median (exploration) or the estimate `v̂_t` (commit) chosen in each round -/
  w : ℕ → ℝ
  /-- the posted prices -/
  p : ℕ → ℝ

/-- **Algorithm 5 (Robust Contextual Pricing with Unknown Corruption), as a relation on runs.**
Castiglioni–Stradi, arXiv:2607.11210, §5, Algorithm 5, p.24, with Equations (4)–(10) (pp.23–26),
the prediction test (1) (p.13), the ϵ-window median (3) (p.14) and Update-Density (Algorithm 3,
p.15):

```
Require: Horizon T, confidence parameter δ ∈ (0, 1)
1: Set ϵ = η = T⁻³ and choose β, α as in Equation (6)
2: Initialize µ₁ as the uniform density over Θ
3: Initialize 𝓗 ← ∅ and M₁ ← [η²e₁, …, η²e_{d+1}]
4: for t = 1, …, T do
5:   Observe context u_t
6:   if 𝓗 satisfies Equation (1) for u_t then
7:     Compute ṽ_t, a_t using Equations (4) and (5)
8:     Compute γ_t, q_t using Equation (7)
9:     Post U_t with probability q_t and L_t otherwise
10:    Observe sale feedback Y_t
11:    Set M̄_t ← M_t + a_t a_tᵀ/γ_t
12:    if (p_t = L_t and Y_t = 0) or (p_t = U_t and Y_t = 1) then
13:      Set 𝓗 ← ∅ and M_{t+1} ← α² M̄_t
14:    else
15:      M_{t+1} ← M̄_t
16:    end if
17:    Set µ_{t+1} ← µ_t
18:  else
19:    Let m_t be the ϵ-window median of µ_t in direction u_t, as in Equation (3)
20:    Post p_t = m_t and observe sale feedback Y_t
21:    Insert (u_t, m_t) into 𝓗 and invoke Update-Density()
22:    Set M_{t+1} ← M_t
23:  end if
24: end for
```

`IsAlg5Run T δ u Y ξ r` says that `r` is a run of Algorithm 5 with horizon `T` and confidence
parameter `δ` (Algorithm 5 is **not** given the corruption budget) on the contexts `u`, the observed
feedback `Y` and the learner's coins `ξ`: initially `µ` is uniform, `𝓗 = ∅` and `M = η² I` with
`η = T⁻³`, and in every round `t < T`

* **commit** (`𝓗` predicts `u_t`): `w_t = v̂_t = Σ λ_i p_i` for coefficients `λ` satisfying (1);
  with `ṽ_t = clip_{[0,1]}(v̂_t)`, `a_t = (u_t, −ṽ_t)`, `q_t` as in (7), the price is `U_t` if
  `ξ_t < q_t` and `L_t` otherwise; the round fails iff (`L_t` posted and `Y_t = 0`) or (`U_t`
  posted and `Y_t = 1`); on failure `𝓗 ← ∅` and `M_{t+1} = α² M̄_t`, else `M_{t+1} = M̄_t`; `µ` is
  kept;
* **explore** (`𝓗` does not predict `u_t`): the price is `w_t = m_t`, an ϵ-window median of the
  current density in direction `u_t`; `(u_t, m_t)` is appended to `𝓗`, the density is replaced by
  Update-Density with feedback `Y_t`, and `M` is kept.

**Formalization Note.** The learner's randomness is one coin `ξ_t` per round; with `ξ_t` uniform
on `[0,1]` (see `coinLaw`), "post `U_t` with probability `q_t`" is "post `U_t` iff `ξ_t < q_t`".
Since `L_t ≤ ṽ_t < U_t`, "`p_t = L_t`" is "the lower price was chosen". The tie-breaking choices
(which solution of (3), which coefficients satisfying (1)) are left free here; that they are
functions of the history is required separately (`IsUnknownCInteraction`). `ϵ = η = T⁻³` is
`epsT T`. -/
def IsAlg5Run {d : ℕ} (T : ℕ) (δ : ℝ) (u : ℕ → EuclideanSpace ℝ (Fin d)) (Y : ℕ → Bool)
    (ξ : ℕ → ℝ) (r : Run5 d) : Prop :=
  r.μ 0 = uniformDensity d ∧ r.H 0 = [] ∧ r.M 0 = (epsT T ^ 2) • (1 : Matrix _ _ ℝ) ∧
  ∀ t < T,
    (Predicts (epsT T) T (r.H t) (u t) ∧
      (∃ lam : Fin (r.H t).length → ℝ,
        PredictsWith (epsT T) T (r.H t) (u t) lam ∧ r.w t = estimate (r.H t) lam) ∧
      r.p t = (if ξ t < checkProb T δ (r.M t) (augVec (u t) (clip01 (r.w t)))
        then upperPrice T (clip01 (r.w t)) else lowerPrice T (clip01 (r.w t))) ∧
      (((ξ t < checkProb T δ (r.M t) (augVec (u t) (clip01 (r.w t))) ∧ Y t = true) ∨
          (¬ ξ t < checkProb T δ (r.M t) (augVec (u t) (clip01 (r.w t))) ∧ Y t = false)) →
        r.H (t + 1) = [] ∧
        r.M (t + 1) = alpha5 T δ ^ 2 • insertMat (r.M t) (augVec (u t) (clip01 (r.w t)))) ∧
      (¬ ((ξ t < checkProb T δ (r.M t) (augVec (u t) (clip01 (r.w t))) ∧ Y t = true) ∨
          (¬ ξ t < checkProb T δ (r.M t) (augVec (u t) (clip01 (r.w t))) ∧ Y t = false)) →
        r.H (t + 1) = r.H t ∧
        r.M (t + 1) = insertMat (r.M t) (augVec (u t) (clip01 (r.w t)))) ∧
      r.μ (t + 1) = r.μ t) ∨
    (¬ Predicts (epsT T) T (r.H t) (u t) ∧
      r.w t = r.p t ∧ IsWindowMedian (epsT T) (r.μ t) (u t) (r.p t) ∧
      r.H (t + 1) = r.H t ++ [(u t, r.p t)] ∧
      r.μ (t + 1) = updateDensity (epsT T) (r.μ t) (u t) (r.p t) (Y t) ∧
      r.M (t + 1) = r.M t)

end RobustCtxPricing.Supplement


