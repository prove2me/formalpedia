-- Prove2me | Definitions.Def_AlmostSSDPortfolio_AASSD_Model
-- name    : AlmostSSDPortfolio_AASSD_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T17:30:12.008503+00:00
-- url     : https://prove2.me/theorems/6139f5fe-34de-4406-a16f-1faad2fa1fe6
-- title:
--   §2–§3.2, pp. 6–12 — finite-scenario portfolio model, LPMs F^(2)_λ and G^(2), ASSD (Definition 1), discretization scheme, A_{D,s,λ} (Definition 2), F̂^(2) (2), AASSD (Definition 3)
-- statement:
--   This file fixes the model of §2–§3.2 of Luo, Chen and Jaillet.
--
--   **Assets and benchmark.** There are $n$ base assets and $T$ scenarios; scenario $t$ has probability $p_t$ and asset $i$ returns $x_{i,t}$ in it. A portfolio is a weight vector $\lambda$ in the simplex
--   $$\Lambda=\Big\{\lambda\in\mathbb R^n:\ \sum_{i=1}^n\lambda_i=1,\ \lambda_i\ge 0\Big\},$$
--   and its return $X$ takes the value $X_t=\sum_{i=1}^n x_{i,t}\lambda_i$ in scenario $t$. The benchmark $Y$ takes the value $b_{t'}$ with probability $p_{t'}$, $t'=1,\dots,T_b$. The **standing assumptions** are: $-\infty<a<b<\infty$; $(p_t)$ and $(p_{t'})$ are probability vectors; every $x_{i,t}$ and every $b_{t'}$ lies in $[a,b]$.
--
--   **Lower partial moments** (p. 7). For a finite distribution with values $v_t$ and probabilities $p_t$, the first-order LPM is $z\mapsto\sum_t p_t\,(z-v_t)\,I(v_t\le z)$. Applied to $X$ and $Y$:
--   $$F^{(2)}_\lambda(z)=\sum_{t=1}^T p_t\Big(z-\sum_{i=1}^n x_{i,t}\lambda_i\Big)I_{\lambda,t}(z),\qquad G^{(2)}(z)=\sum_{t'=1}^{T_b}p_{t'}(z-b_{t'})I(b_{t'}\le z).$$
--   Means and variances are $\mathbb E X=\sum_t p_tX_t$ and $\mathrm{Var}(X)=\sum_t p_t(X_t-\mathbb E X)^2$, and likewise for $Y$.
--
--   **ASSD** (Definition 1, p. 8). Let $S_2=\{t\in[a,b]:F^{(2)}_\lambda(t)>G^{(2)}(t)\}$ and $\bar S_2=[a,b]\setminus S_2$. For $\tau\in(1,\infty)$, $X$ dominates $Y$ by $\tau$-ASSD when
--   $$\tau\int_{S_2}\big(F^{(2)}_\lambda(t)-G^{(2)}(t)\big)\,dt\ \le\ \int_{\bar S_2}\big(G^{(2)}(t)-F^{(2)}_\lambda(t)\big)\,dt\quad\text{and}\quad \mathbb E X\ge\mathbb E Y.$$
--
--   **Discretization scheme** (p. 9). Grid points $a=d_1<d_2<\dots<d_{T_D}=b$ that contain every benchmark return $b_{t'}$; they cut $[a,b]$ into the sub-intervals $[d_s,d_{s+1}]$, $s=1,\dots,T_D-1$.
--
--   **Approximate SSD violation** (Definition 2, p. 9). Write $f_l,f_r$ for $F^{(2)}_\lambda(d_s),F^{(2)}_\lambda(d_{s+1})$ and $g_l,g_r$ for $G^{(2)}(d_s),G^{(2)}(d_{s+1})$. Then $A_{D,s,\lambda}$ is $0$ if $f_l\le g_l$ and $f_r\le g_r$ (Case 1);
--   $$\frac{(d_{s+1}-d_s)(f_r-g_r)^2}{2(f_r-g_r+g_l-f_l)}\ \text{(Case 2: } f_l\le g_l,\ f_r\ge g_r),\qquad \frac{(d_{s+1}-d_s)(f_l-g_l)^2}{2(g_r-f_r+f_l-g_l)}\ \text{(Case 3: } f_l\ge g_l,\ f_r\le g_r);$$
--   and $(f_r+f_l)\frac{d_{s+1}-d_s}{2}-(g_r+g_l)\frac{d_{s+1}-d_s}{2}$ if $f_l\ge g_l$ and $f_r\ge g_r$ (Case 4), with at least one strict inequality in Cases 2–4.
--
--   **Interpolated LPM** (2), p. 9: on each $[d_s,d_{s+1}]$,
--   $$\hat F^{(2)}_{D,\lambda}(z)=F^{(2)}_\lambda(d_s)+\frac{F^{(2)}_\lambda(d_{s+1})-F^{(2)}_\lambda(d_s)}{d_{s+1}-d_s}(z-d_s),$$
--   and $\hat S_2=\{t\in[a,b]:\hat F^{(2)}_{D,\lambda}(t)>G^{(2)}(t)\}$ (Proposition 3, p. 11).
--
--   **AASSD** (Definition 3, pp. 11–12). For $\tau\in(1,\infty)$, $X$ dominates $Y$ by $\tau$-AASSD under $D$ when
--   $$2(\tau-1)\sum_{s=1}^{T_D-1}A_{D,s,\lambda}\ \le\ \mathrm{Var}(Y)+(b-\mathbb E Y)^2-\mathrm{Var}(X)-(b-\mathbb E X)^2\quad\text{and}\quad\mathbb E X\ge\mathbb E Y,$$
--   which is the paper's own form (5d), p. 17, of the ratio inequality printed in Definition 3.
--
--   These objects are the vocabulary of the mission's goal, Theorem 1 (AASSD implies ASSD), and of its milestones.
--
--   **Formalization Note.** (1) The grid is `d : Fin (K+1) → ℝ` with 0-based indices ($T_D=K+1$); sub-interval `s : Fin K` is `[d s, d (s+1)]`. (2) Both dominance notions are stated with the ratios cross-multiplied. With a positive denominator this is equivalent to the printed ratio; when the denominator vanishes (no SSD violation) the printed ratio is $+\infty$ and the cross-multiplied form holds, as intended, whereas Lean's convention $x/0=0$ would make the literal ratio fail. (3) $\bar S_2$ is the complement of $S_2$ inside $[a,b]$, where both variables live; over all of $\mathbb R$ the integral would diverge. (4) The case analysis of Definition 2 is an if-chain in the paper's order; on the overlaps of the cases the printed formulas agree, and the denominators in Cases 2–3 are positive whenever their branch is taken. (5) $\hat F^{(2)}_{D,\lambda}$ chooses a sub-interval containing $z$; at a shared grid point both choices give $F^{(2)}_\lambda(d_s)$. Outside $[a,b]$ it is set equal to $F^{(2)}_\lambda$, which agrees with the LPM of the paper's approximate distribution $\hat F_{D,\lambda}$ there. (6) The variance is written in scenario form $\sum_tp_t(X_t-\mathbb EX)^2$, which equals the paper's $\lambda^\top\mathrm{Cov}\,\lambda$. (7) The ascending order $b_1\le\dots\le b_{T_b}$ (p. 7, "without loss of generality") is not imposed. (8) The simplex and probability vectors use Mathlib's `stdSimplex`.
-- source:
--   Luo, Chen & Jaillet, Portfolio Optimization Based on Almost Second-Degree Stochastic Dominance, accepted manuscript (April 2024) of Management Science doi:10.1287/mnsc.2022.01092, pp. 6–12, §2, §3.1–3.2, Definitions 1–3, eq. (2); p. 17, (5d)

import Mathlib

namespace AlmostSSDPortfolio.AASSD

open MeasureTheory Set

/-- First-order lower partial moment of a finite discrete distribution with values `v` and
probabilities `p` (p. 7): `z ↦ Σ_t p_t (z − v_t) I(v_t ≤ z) = Σ_t p_t (z − v_t)⁺`. -/
noncomputable def lpm {T : Type*} [Fintype T] (p v : T → ℝ) (z : ℝ) : ℝ :=
  ∑ t, p t * max (z - v t) 0

/-- Expected value `Σ_t p_t v_t` of a finite discrete distribution. -/
def mean {T : Type*} [Fintype T] (p v : T → ℝ) : ℝ := ∑ t, p t * v t

/-- Variance `Σ_t p_t (v_t − E)²` of a finite discrete distribution. -/
def var {T : Type*} [Fintype T] (p v : T → ℝ) : ℝ := ∑ t, p t * (v t - mean p v) ^ 2

/-- A probability vector: nonnegative entries summing to `1` (Mathlib's standard simplex). -/
def IsProbVec {T : Type*} [Fintype T] (p : T → ℝ) : Prop := p ∈ stdSimplex ℝ T

/-- §2, pp. 6–7: `n` base assets with returns `x i t` in `T` scenarios of probability `p t`;
a benchmark portfolio with `Tb` scenarios of probability `q t'` and returns `bv t'`;
the investment return range `[a, b]`. -/
structure Setting (n T Tb : ℕ) where
  a : ℝ
  b : ℝ
  p : Fin T → ℝ
  x : Fin n → Fin T → ℝ
  q : Fin Tb → ℝ
  bv : Fin Tb → ℝ

variable {n T Tb : ℕ}

/-- Standing assumptions of §2 (p. 6–7) and §3.1 (p. 8): `−∞ < a < b < ∞`, both scenario
distributions are probability vectors, and every asset and benchmark return lies in `[a, b]`. -/
def Setting.Standing (S : Setting n T Tb) : Prop :=
  S.a < S.b ∧ IsProbVec S.p ∧ IsProbVec S.q ∧
    (∀ i t, S.x i t ∈ Icc S.a S.b) ∧ ∀ t', S.bv t' ∈ Icc S.a S.b

/-- The portfolio set `Λ = {λ ∈ ℝⁿ : Σ_i λ_i = 1, λ_i ≥ 0}`, p. 6. -/
def simplex (n : ℕ) : Set (Fin n → ℝ) := stdSimplex ℝ (Fin n)

/-- Return of portfolio `λ` in scenario `t`: `Σ_i x_{i,t} λ_i`, p. 6. -/
def Setting.ret (S : Setting n T Tb) (lam : Fin n → ℝ) (t : Fin T) : ℝ := ∑ i, S.x i t * lam i

/-- `F_λ^{(2)}`, the first-order LPM of the portfolio return, p. 7. -/
noncomputable def Setting.F2 (S : Setting n T Tb) (lam : Fin n → ℝ) : ℝ → ℝ :=
  lpm S.p (S.ret lam)

/-- `G^{(2)}`, the first-order LPM of the benchmark, p. 7. -/
noncomputable def Setting.G2 (S : Setting n T Tb) : ℝ → ℝ := lpm S.q S.bv

/-- `S₂ = {t ∈ [a, b] : F^{(2)}(t) > G^{(2)}(t)}`, §3.1, p. 8. -/
def Setting.S2 (S : Setting n T Tb) (lam : Fin n → ℝ) : Set ℝ :=
  {t | t ∈ Icc S.a S.b ∧ S.G2 t < S.F2 lam t}

/-- `S̄₂`, the complement of `S₂` taken inside `[a, b]`. -/
def Setting.S2c (S : Setting n T Tb) (lam : Fin n → ℝ) : Set ℝ :=
  {t | t ∈ Icc S.a S.b ∧ S.F2 lam t ≤ S.G2 t}

/-- Definition 1 (τ-ASSD), p. 8, for the portfolio return and the benchmark, with the ratio
cross-multiplied: `τ ∫_{S₂} (F^{(2)} − G^{(2)}) ≤ ∫_{S̄₂} (G^{(2)} − F^{(2)})` and `E X ≥ E Y`. -/
def Setting.IsASSD (S : Setting n T Tb) (lam : Fin n → ℝ) (τ : ℝ) : Prop :=
  τ * (∫ t in S.S2 lam, (S.F2 lam t - S.G2 t)) ≤ ∫ t in S.S2c lam, (S.G2 t - S.F2 lam t) ∧
    mean S.q S.bv ≤ mean S.p (S.ret lam)

/-- A discretization scheme, p. 9: grid points `d 0 < d 1 < … < d K` (the paper's
`d_1 < … < d_{T_D}`, `T_D = K + 1`) with `d 0 = a`, `d K = b`, containing every benchmark
return `b_{t'}`. -/
structure Discretization (S : Setting n T Tb) where
  K : ℕ
  d : Fin (K + 1) → ℝ
  strictMono : StrictMono d
  first : d 0 = S.a
  last : d (Fin.last K) = S.b
  covers : ∀ t', ∃ s, d s = S.bv t'

/-- The four cases of Definition 2 on one sub-interval `[dl, dr]`, with `fl, fr` the values of
`F_λ^{(2)}` and `gl, gr` those of `G^{(2)}` at its left and right end points. -/
noncomputable def violation (fl fr gl gr dl dr : ℝ) : ℝ :=
  if fl ≤ gl ∧ fr ≤ gr then 0
  else if fl ≤ gl ∧ gr ≤ fr then (dr - dl) * (fr - gr) ^ 2 / (2 * (fr - gr + gl - fl))
  else if gl ≤ fl ∧ fr ≤ gr then (dr - dl) * (fl - gl) ^ 2 / (2 * (gr - fr + fl - gl))
  else (fr + fl) * ((dr - dl) / 2) - (gr + gl) * ((dr - dl) / 2)

/-- `A_{D,s,λ}`, the approximate SSD violation on the sub-interval `[d s, d (s+1)]`,
Definition 2, p. 9. -/
noncomputable def Discretization.A {S : Setting n T Tb} (D : Discretization S)
    (lam : Fin n → ℝ) (s : Fin D.K) : ℝ :=
  violation (S.F2 lam (D.d s.castSucc)) (S.F2 lam (D.d s.succ)) (S.G2 (D.d s.castSucc))
    (S.G2 (D.d s.succ)) (D.d s.castSucc) (D.d s.succ)

/-- `F̂^{(2)}_{D,λ}`, the linear interpolation (2), p. 9, of `F_λ^{(2)}` at the grid points;
outside `[a, b]` it is `F_λ^{(2)}` itself. -/
noncomputable def Discretization.hatF2 {S : Setting n T Tb} (D : Discretization S)
    (lam : Fin n → ℝ) (z : ℝ) : ℝ :=
  if h : ∃ s : Fin D.K, z ∈ Icc (D.d s.castSucc) (D.d s.succ) then
    S.F2 lam (D.d h.choose.castSucc) +
      (S.F2 lam (D.d h.choose.succ) - S.F2 lam (D.d h.choose.castSucc)) /
        (D.d h.choose.succ - D.d h.choose.castSucc) * (z - D.d h.choose.castSucc)
  else S.F2 lam z

/-- `Ŝ₂ = {t ∈ [a, b] : F̂^{(2)}_{D,λ}(t) > G^{(2)}(t)}`, Proposition 3, p. 11. -/
def Discretization.hatS2 {S : Setting n T Tb} (D : Discretization S) (lam : Fin n → ℝ) :
    Set ℝ :=
  {t | t ∈ Icc S.a S.b ∧ S.G2 t < D.hatF2 lam t}

/-- Definition 3 (τ-AASSD), pp. 11–12, in the paper's cross-multiplied form (5d), p. 17:
`2(τ − 1) Σ_s A_{D,s,λ} ≤ Var Y + (b − E Y)² − Var X − (b − E X)²` and `E X ≥ E Y`. -/
def Discretization.IsAASSD {S : Setting n T Tb} (D : Discretization S) (lam : Fin n → ℝ)
    (τ : ℝ) : Prop :=
  2 * (τ - 1) * ∑ s, D.A lam s ≤
      var S.q S.bv + (S.b - mean S.q S.bv) ^ 2 - var S.p (S.ret lam) -
        (S.b - mean S.p (S.ret lam)) ^ 2 ∧
    mean S.q S.bv ≤ mean S.p (S.ret lam)

end AlmostSSDPortfolio.AASSD


