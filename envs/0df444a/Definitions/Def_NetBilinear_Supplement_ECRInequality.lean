-- Prove2me | Definitions.Def_NetBilinear_Supplement_ECRInequality
-- name    : NetBilinear_Supplement_ECRInequality
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T02:41:57.30217+00:00
-- url     : https://prove2.me/theorems/aa914ad0-85b6-44e7-a9df-a66af3f3c636
-- title:
--   A class-$l^\pm$ EC&R inequality of $\mathcal S$ (aggregation under (C1), (C2), then relaxation of the remaining bilinear terms)
-- statement:
--   Let $\mathcal S$ be the bilinear set of p.2. A **class-$l^\pm$ EC&R inequality** is obtained as follows.
--   1. Choose a base equality $l\in K$, say $y_{j'}x_{i'}-z_l=0$ with $A^l_{j'i'}=1$, and a sign $\sigma\in\{+,-\}$ (weight $\pm1$).
--   2. Choose an EC&R assignment $[\mathcal I_1,\dots,\mathcal I_m,\bar{\mathcal I}\,|\,\mathcal J,\bar{\mathcal J}]$ with $\mathcal I_1\cap\dots\cap\mathcal I_m\cap\bar{\mathcal I}=\emptyset$ and $\mathcal J\cap\bar{\mathcal J}=\emptyset$, and weights $\gamma,\theta,\lambda,\mu\ge0$ satisfying (C1) and (C2).
--   3. Aggregate
--   $$
--   \sigma(y_{j'}x_{i'}-z_l)+\sum_{j}\sum_{t\in\mathcal I_j}\gamma^j_t y_j(E_tx-f_t)+\sum_{t\in\bar{\mathcal I}}\theta_t\Big(1-\sum_{j}y_j\Big)(E_tx-f_t)+\sum_{i\in\mathcal J}\lambda_i\Big(1-\sum_j y_j\Big)x_i+\sum_{i\in\bar{\mathcal J}}\mu_i\Big(1-\sum_j y_j\Big)(u_i-x_i)\ \ge 0 .
--   $$
--   4. Relax every remaining bilinear term. A term $c\,x_iy_j$ with $c>0$ is relaxed with $u_iy_j-x_iy_j\ge0$ or with $-x_iy_j+z_k\ge0$ for some $k$ with $A^k_{ji}=1$. A term $c\,x_iy_j$ with $c<0$ is relaxed with $x_iy_j\ge0$ or with $x_iy_j-z_k\ge0$ for such a $k$.
--
--   The result is a linear inequality in $(x,y,z)$. The definition records all of these choices and states when a point satisfies the inequality.
--
--   **Formalization Note** Conditions (C1), (C2) and the aggregated coefficients are those of `NetBilinear.Supplement.IsECRAssignment` for the rows $E$, with $(i',j')$ the position of the entry $1$ of $A^l$. The relaxation adds the chosen constraint, multiplied by $|c|$, to the aggregated inequality, so all bilinear terms cancel in the sum. A relaxation choice is recorded for every pair $(j,i)$ but is used only where $c\neq0$.
-- source:
--   Khademnia & Davarnia, Convexification of Bilinear Terms over Network Polytopes, arXiv:2302.14151v2, §2, p.3 (EC&R procedure, Steps 1–3, (C1), (C2) and the relaxation step)

import Mathlib
import Definitions.Def_NetBilinear_Network
import Definitions.Def_NetBilinear_Supplement_IsECRAssignment
import Definitions.Def_NetBilinear_Supplement_BilinearSet

namespace NetBilinear.Supplement

/-- **A class-`l±` EC&R inequality of the set `S`**, given by all the choices of the EC&R
procedure. Khademnia & Davarnia, *Convexification of Bilinear Terms over Network Polytopes*,
arXiv:2302.14151v2, §2, p.3: Step 1 (the base equality `l`, sign `σ`, weight `±1`), Step 2
(`I_1, …, I_m, Ī ⊆ T` with empty intersection; row `t ∈ I_j` times `γ^j_t y_j`, row `t ∈ Ī`
times `θ_t (1 − Σ_{i∈M} y_i)`), Step 3 (`J, J̄ ⊆ N` disjoint; `x_i ≥ 0` times
`λ_i (1 − Σ_j y_j)` for `i ∈ J`, `u_i − x_i ≥ 0` times `µ_i (1 − Σ_j y_j)` for `i ∈ J̄`),
weights `γ, θ, λ, µ ≥ 0` satisfying (C1) and (C2), and the relaxation step: every remaining
bilinear term `x_i y_j` is relaxed using `u_i y_j − x_i y_j ≥ 0` (`relax j i = none`) or
`−x_i y_j + z_k ≥ 0` for some `k` with `A^k_{ji} = 1` (`relax j i = some k`), and every
remaining term `−x_i y_j` using `x_i y_j ≥ 0` (`none`) or `x_i y_j − z_k ≥ 0` (`some k`).

**Formalization Note.** The base equality `l` has base term `y_{j'} x_{i'}` with
`(i', j') = pos l`; (C1), (C2) and the aggregated coefficients are those of
`NetBilinear.Supplement.IsECRAssignment` (`aggCoef`, `CondC1`, `CondC2`) for the rows `E`. The
relaxation choice is recorded for every pair `(j, i)` and used only where the aggregated
coefficient is nonzero. -/
structure ECRInequality {N M K R : Type*} [DecidableEq N] [Fintype M] [DecidableEq M]
    (S : BilinearSet N M K R) where
  /-- The base equality `l ∈ K` (Step 1). -/
  l : K
  /-- Its sign indicator (Step 1). -/
  σ : Sign
  /-- `I_j` (Step 2). -/
  I : M → Finset R
  /-- `Ī` (Step 2). -/
  Ibar : Finset R
  /-- `J` (Step 3). -/
  J : Finset N
  /-- `J̄` (Step 3). -/
  Jbar : Finset N
  /-- `γ^j_t`. -/
  γ : M → R → ℝ
  /-- `θ_t`. -/
  θ : R → ℝ
  /-- `λ_i`. -/
  lam : N → ℝ
  /-- `µ_i`. -/
  μ : N → ℝ
  /-- The relaxation of the remaining term `x_i y_j`: `none` for the bound constraint,
  `some k` for the bilinear constraint `k`. -/
  relax : M → N → Option K
  /-- `I_1 ∩ ⋯ ∩ I_m ∩ Ī = ∅` (Step 2). -/
  inter : ∀ t ∈ Ibar, ¬ ∀ j, t ∈ I j
  /-- `J ∩ J̄ = ∅` (Step 3). -/
  disj : Disjoint J Jbar
  /-- `γ^j_t ≥ 0`. -/
  γ_nonneg : ∀ j, ∀ t ∈ I j, 0 ≤ γ j t
  /-- `θ_t ≥ 0`. -/
  θ_nonneg : ∀ t ∈ Ibar, 0 ≤ θ t
  /-- `λ_i ≥ 0`. -/
  lam_nonneg : ∀ i ∈ J, 0 ≤ lam i
  /-- `µ_i ≥ 0`. -/
  μ_nonneg : ∀ i ∈ Jbar, 0 ≤ μ i
  /-- (C1). -/
  c1 : CondC1 S.E (S.pos l).1 (S.pos l).2 σ I Ibar J Jbar γ θ lam μ
  /-- (C2). -/
  c2 : CondC2 S.E (S.pos l).1 (S.pos l).2 σ I Ibar J Jbar γ θ lam μ
  /-- A relaxation through `z_k` uses a `k` with `A^k_{ji} = 1`. -/
  relax_valid : ∀ j i k, relax j i = some k → S.pos k = (i, j)

namespace ECRInequality

variable {N M K R : Type*} [Fintype N] [DecidableEq N] [Fintype M] [DecidableEq M]
  {S : BilinearSet N M K R}

/-- **The aggregated inequality's left-hand side** at `p = (x, y, z)` (arXiv:2302.14151v2,
p.3, "We next aggregate all aforementioned weighted constraints"):
`σ (y_{j'} x_{i'} − z_l) + Σ_j Σ_{t∈I_j} γ^j_t y_j (E_t x − f_t)
 + Σ_{t∈Ī} θ_t (1 − Σ y)(E_t x − f_t) + Σ_{i∈J} λ_i (1 − Σ y) x_i
 + Σ_{i∈J̄} µ_i (1 − Σ y)(u_i − x_i)`. -/
def aggValue (e : ECRInequality S) (p : (N → ℝ) × (M → ℝ) × (K → ℝ)) : ℝ :=
  e.σ.toReal * (p.2.1 (S.pos e.l).2 * p.1 (S.pos e.l).1 - p.2.2 e.l)
    + ∑ j, ∑ t ∈ e.I j, e.γ j t * p.2.1 j * ((∑ i, S.E t i * p.1 i) - S.f t)
    + ∑ t ∈ e.Ibar, e.θ t * (1 - ∑ j, p.2.1 j) * ((∑ i, S.E t i * p.1 i) - S.f t)
    + ∑ i ∈ e.J, e.lam i * (1 - ∑ j, p.2.1 j) * p.1 i
    + ∑ i ∈ e.Jbar, e.μ i * (1 - ∑ j, p.2.1 j) * (S.u i - p.1 i)

/-- **The relaxation step** (arXiv:2302.14151v2, p.3): for each remaining term `c · x_i y_j`
(`c` the aggregated coefficient `aggCoef`, `c ≠ 0`) the multiple of the relaxing constraint
that is added: for `c > 0`, `c (u_i y_j − x_i y_j)` or `c (z_k − x_i y_j)`; for `c < 0`,
`(−c) x_i y_j` or `(−c)(x_i y_j − z_k)`. -/
noncomputable def relaxValue (e : ECRInequality S) (p : (N → ℝ) × (M → ℝ) × (K → ℝ)) : ℝ :=
  ∑ j, ∑ i,
    let c := aggCoef S.E (S.pos e.l).1 (S.pos e.l).2 e.σ e.I e.Ibar e.J e.Jbar e.γ e.θ e.lam e.μ j i
    if 0 < c then
      (match e.relax j i with
        | none => c * (S.u i * p.2.1 j - p.1 i * p.2.1 j)
        | some k => c * (p.2.2 k - p.1 i * p.2.1 j))
    else if c < 0 then
      (match e.relax j i with
        | none => -c * (p.1 i * p.2.1 j)
        | some k => -c * (p.1 i * p.2.1 j - p.2.2 k))
    else 0

/-- **The class-`l±` EC&R inequality holds at `p`**: the aggregated inequality with every
remaining bilinear term relaxed, `aggValue + relaxValue ≥ 0`. All bilinear terms cancel in this
sum, so it is the linear inequality the paper calls a class-`l±` EC&R inequality. -/
def Holds (e : ECRInequality S) (p : (N → ℝ) × (M → ℝ) × (K → ℝ)) : Prop :=
  0 ≤ e.aggValue p + e.relaxValue p

end ECRInequality

end NetBilinear.Supplement


