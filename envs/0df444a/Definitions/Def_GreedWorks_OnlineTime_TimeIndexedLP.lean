-- Prove2me | Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP
-- name    : GreedWorks_OnlineTime_TimeIndexedLP
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-08T23:02:53.957672+00:00
-- url     : https://prove2.me/theorems/8f8156da-7c3f-4ee8-aff3-efdf6c4a622c
-- title:
--   (S_r), (P_r), (D_r), §3 and §6.2, pp. 6–8, 15 — time-indexed relaxations with release dates and the dual
-- statement:
--   Let $M$ be a finite set of machines, $J=\{1,\dots,n\}$ a set of jobs with integer release dates $r_j$ and weights $w_j$, an eligibility relation between machines and jobs, and for each eligible pair $(i,j)$ a mean $\mathbb E[P_{ij}]$ and a squared coefficient of variation $\mathbb{CV}[P_{ij}]^2$. The variables $y_{ijs}\ge0$, for eligible $(i,j)$ and integer slots $s\ge r_j$, stand for the probability that job $j$ is processed on machine $i$ during $[s,s+1]$; for ineligible pairs and for $s<r_j$ there are no variables ($y_{ijs}=0$).
--
--   The relaxation $(\mathrm P_r)$ requires
--   $$\sum_{j\in J}y_{ijs}\le 1\quad(i\in M,\ s\in\mathbb Z_{\ge0}),\qquad \sum_{i\in M}\sum_{s\in\mathbb Z_{\ge0}}\frac{y_{ijs}}{\mathbb E[P_{ij}]}=1\quad(j\in J),$$
--   and minimizes $z^{P_r}=\sum_j w_jC^P_j$ with
--   $$C^P_j=\sum_{i\in M}\sum_{s\in\mathbb Z_{\ge0}}\Big(\frac{y_{ijs}}{\mathbb E[P_{ij}]}\big(s+\tfrac12\big)+\frac{y_{ijs}}2\Big).$$
--   The stochastic relaxation $(\mathrm S_r)$ uses instead
--   $$C^S_j=\sum_{i\in M}\sum_{s\in\mathbb Z_{\ge0}}\Big(\frac{y_{ijs}}{\mathbb E[P_{ij}]}\big(s+\tfrac12\big)+\frac{1-\mathbb{CV}[P_{ij}]^2}{2}\,y_{ijs}\Big),$$
--   adds the constraint $C^S_j\ge\sum_i\sum_s y_{ijs}$, and minimizes $z^{S_r}=\sum_jw_jC^S_j$.
--
--   The dual $(\mathrm D_r)$ of $(\mathrm P_r)$ has free variables $\alpha_j$ and variables $\beta_{is}\ge0$; it maximizes $z^{D_r}=\sum_j\alpha_j-\sum_i\sum_s\beta_{is}$ subject to
--   $$\frac{\alpha_j}{\mathbb E[P_{ij}]}\le\beta_{is}+w_j\Big(\frac{s+\frac12}{\mathbb E[P_{ij}]}+\frac12\Big)\qquad\text{for all eligible }(i,j)\text{ and all }s\ge r_j .$$
--
--   These are the linear programs through which the paper lower-bounds the optimal expected cost in the model with release dates.
--
--   **Formalization Note** The data are passed as plain functions (`elig`, `r`, `μ`, `cv2`, `w`); the theorems instantiate `μ` and `cv2` with the means and squared coefficients of variation of the instance. Feasibility includes summability of $s\mapsto y_{ijs}$ and $s\mapsto(s+\frac12)y_{ijs}$ in $(\mathrm P_r)$ and $(\mathrm S_r)$, and of $s\mapsto\beta_{is}$ in $(\mathrm D_r)$, so that every infinite series has its intended value (a non-summable `tsum` is $0$ in Lean). Optimal values are never written as infima: statements quantify over feasible points.
-- source:
--   Gupta, Moseley, Uetz & Xie, Greed Works – Online Algorithms For Unrelated Machine Stochastic Scheduling, arXiv:1703.01634v4, pp. 6–8, §3, (2)–(6), (S), (P), (D); p. 15, §6.2, (S_r), (P_r), (D_r)

import Mathlib

namespace GreedWorks.OnlineTime

open Classical

/-! # The time-indexed relaxations (S_r), (P_r) and the dual (D_r)

§3, pp. 6–8, and §6.2, p. 15. The data are deterministic: an eligibility relation `elig`
(ineligible pairs have no variables), integer release dates `r`, means `μ i j = 𝔼[P_ij]`,
squared coefficients of variation `cv2 i j = ℂ𝕍[P_ij]²` and weights `w`. A variable `y i j s`
(`s ∈ ℤ_{≥0}`) is the probability that job `j` is processed on GreedWorks.OnlineList.machine `i` in `[s, s + 1]`. -/

variable {M : Type*} [Fintype M] {n : ℕ}

/-- (4): `C^S_j = Σ_i Σ_s ( y_ijs/𝔼[P_ij] · (s + ½) + (1 − ℂ𝕍[P_ij]²)/2 · y_ijs )`, the sum
over machines eligible for `j`. -/
noncomputable def completionS (elig : M → Fin n → Prop) (μ cv2 : M → Fin n → ℝ)
    (y : M → Fin n → ℕ → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => elig i j),
    ∑' s : ℕ, (y i j s / μ i j * ((s : ℝ) + 1 / 2) + (1 - cv2 i j) / 2 * y i j s)

/-- (6): `C^P_j = Σ_i Σ_s ( y_ijs/𝔼[P_ij] · (s + ½) + y_ijs/2 )`. -/
noncomputable def completionP (elig : M → Fin n → Prop) (μ : M → Fin n → ℝ)
    (y : M → Fin n → ℕ → ℝ) (j : Fin n) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => elig i j),
    ∑' s : ℕ, (y i j s / μ i j * ((s : ℝ) + 1 / 2) + y i j s / 2)

/-- Feasibility for (P_r) (§6.2, p. 15): nonnegativity; no variables for ineligible pairs or
for slots before the release date (`y_ijs` is defined only for `s ≥ r_j`); summability of
`y_ij·` and of `(s + ½) y_ijs` (so that every series has its intended value); constraint (2),
`Σ_j y_ijs ≤ 1`; and constraint (3), `Σ_i Σ_s y_ijs / 𝔼[P_ij] = 1`. -/
def IsFeasibleP (elig : M → Fin n → Prop) (r : Fin n → ℕ) (μ : M → Fin n → ℝ)
    (y : M → Fin n → ℕ → ℝ) : Prop :=
  (∀ i j s, 0 ≤ y i j s) ∧
  (∀ i j s, ¬ elig i j → y i j s = 0) ∧
  (∀ i j s, s < r j → y i j s = 0) ∧
  (∀ i j, Summable (y i j)) ∧
  (∀ i j, Summable (fun s : ℕ => ((s : ℝ) + 1 / 2) * y i j s)) ∧
  (∀ i s, ∑ j : Fin n, y i j s ≤ 1) ∧
  (∀ j, ∑ i ∈ Finset.univ.filter (fun i => elig i j), (∑' s : ℕ, y i j s) / μ i j = 1)

/-- Feasibility for (S_r): the constraints of (P_r) together with constraint (5),
`C^S_j ≥ Σ_i Σ_s y_ijs`. -/
def IsFeasibleS (elig : M → Fin n → Prop) (r : Fin n → ℕ) (μ cv2 : M → Fin n → ℝ)
    (y : M → Fin n → ℕ → ℝ) : Prop :=
  IsFeasibleP elig r μ y ∧
  ∀ j, ∑ i ∈ Finset.univ.filter (fun i => elig i j), ∑' s : ℕ, y i j s ≤
    completionS elig μ cv2 y j

/-- Objective `z^{S_r}(y) = Σ_j w_j C^S_j`. -/
noncomputable def valueS (elig : M → Fin n → Prop) (μ cv2 : M → Fin n → ℝ) (w : Fin n → ℝ)
    (y : M → Fin n → ℕ → ℝ) : ℝ :=
  ∑ j : Fin n, w j * completionS elig μ cv2 y j

/-- Objective `z^{P_r}(y) = Σ_j w_j C^P_j`. -/
noncomputable def valueP (elig : M → Fin n → Prop) (μ : M → Fin n → ℝ) (w : Fin n → ℝ)
    (y : M → Fin n → ℕ → ℝ) : ℝ :=
  ∑ j : Fin n, w j * completionP elig μ y j

/-- Feasibility for the dual (D_r) (§6.2, p. 15): `α` free, `β_is ≥ 0` with `Σ_s β_is`
convergent, and for every eligible pair `(i, j)` and every slot `s ≥ r_j`,
`α_j / 𝔼[P_ij] ≤ β_is + w_j ((s + ½)/𝔼[P_ij] + ½)`. -/
def IsFeasibleD (elig : M → Fin n → Prop) (r : Fin n → ℕ) (μ : M → Fin n → ℝ)
    (w : Fin n → ℝ) (α : Fin n → ℝ) (β : M → ℕ → ℝ) : Prop :=
  (∀ i s, 0 ≤ β i s) ∧ (∀ i, Summable (β i)) ∧
  ∀ i j s, elig i j → r j ≤ s →
    α j / μ i j ≤ β i s + w j * (((s : ℝ) + 1 / 2) / μ i j + 1 / 2)

/-- Objective `z^{D_r}(α, β) = Σ_j α_j − Σ_i Σ_s β_is`. -/
noncomputable def valueD (α : Fin n → ℝ) (β : M → ℕ → ℝ) : ℝ :=
  ∑ j : Fin n, α j - ∑ i : M, ∑' s : ℕ, β i s

end GreedWorks.OnlineTime


