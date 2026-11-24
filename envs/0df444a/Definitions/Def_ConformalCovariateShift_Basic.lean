-- Prove2me | Definitions.Def_ConformalCovariateShift_Basic
-- name    : ConformalCovariateShift_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T02:20:55.413977+00:00
-- url     : https://prove2.me/theorems/fca2862d-93ce-47f6-8405-7994d6dfd8dc
-- title:
--   Conformal prediction under covariate shift: quantiles, scores, (weighted) exchangeability and conformal bands
-- statement:
--   Objects of Sections 1-3 of Tibshirani, Barber, Candès and Ramdas (2019).
--
--   1. **Quantiles (Section 1.1).** For a distribution $F$ on the augmented real line $\mathbb{R}\cup\{\infty\}$, $\mathrm{Quantile}(\beta;F)=\inf\{z:\mathbb{P}_{Z\sim F}\{Z\le z\}\ge\beta\}$. A discrete distribution is $\sum_ip_i\delta_{v_i}$. For values $v_1,\dots,v_{n+1}$, $\mathrm{Quantile}(\beta;v_{1:(n+1)})$ is the quantile of $\frac1{n+1}\sum_{i=1}^{n+1}\delta_{v_i}$, and $\mathrm{Quantile}(\beta;v_{1:n}\cup\{\infty\})$ is the quantile of $\frac1{n+1}\sum_{i=1}^{n}\delta_{v_i}+\frac1{n+1}\delta_\infty$. For weights $p_1,\dots,p_{n+1}$, the distribution $\sum_{i=1}^np_i\delta_{v_i}+p_{n+1}\delta_\infty$ is used in (8), (16) and Lemma 3.
--   2. **Scores (Section 1.2, eq. 4).** Data points are $(x,y)\in\mathbb{R}^d\times\mathbb{R}$. A score function $\mathcal S((x,y),Z)$ takes a point and a multiset $Z$ of points. For points $z_1,\dots,z_m$, the nonconformity scores are $V_i=\mathcal S(z_i,z_{1:m}\setminus\{z_i\})$, where $z_{1:m}\setminus\{z_i\}$ is the multiset of the other points. For training points $Z_1,\dots,Z_n$ and a candidate $(x,y)$, the scores $V_i^{(x,y)}$ of (4) are those of the $n+1$ points $Z_1,\dots,Z_n,(x,y)$.
--   3. **Exchangeability.** Random variables $V_1,\dots,V_m$ are exchangeable if $(V_{\sigma(1)},\dots,V_{\sigma(m)})$ has the same law as $(V_1,\dots,V_m)$ for every permutation $\sigma$.
--   4. **Conformal band (eq. 5).** $\widehat C_n(x)=\{y\in\mathbb{R}:V_{n+1}^{(x,y)}\le\mathrm{Quantile}(1-\alpha;V_{1:n}^{(x,y)}\cup\{\infty\})\}$.
--   5. **Covariate shift (eqs. 7-8).** For a weight function $w$ on $\mathbb{R}^d$, $p_i^w(x)=w(X_i)/(\sum_{j=1}^nw(X_j)+w(x))$ for $i\le n$ and $p_{n+1}^w(x)=w(x)/(\sum_{j=1}^nw(X_j)+w(x))$. The band (8) is $\{y:V_{n+1}^{(x,y)}\le\mathrm{Quantile}(1-\alpha;\sum_{i=1}^np_i^w(x)\delta_{V_i^{(x,y)}}+p_{n+1}^w(x)\delta_\infty)\}$.
--   6. **Weighted exchangeability (Definition 1).** Random variables $Z_1,\dots,Z_m$ with values in a measurable space $E$ are weighted exchangeable with measurable, nonnegative weight functions $w_1,\dots,w_m$ if their joint law has a density $f$ with respect to a measure $\nu$ on $E^m$ that is invariant under permutations of the coordinates, and $f(z_1,\dots,z_m)=\prod_iw_i(z_i)\cdot g(z_1,\dots,z_m)$ with $g$ invariant under permutations of its arguments.
--   7. **Weighted band (eqs. 15-16).** $p_i^w(z_1,\dots,z_{n+1})=\sum_{\sigma:\sigma(n+1)=i}\prod_{j=1}^{n+1}w_j(z_{\sigma(j)})\big/\sum_\sigma\prod_{j=1}^{n+1}w_j(z_{\sigma(j)})$, the sums over permutations of $\{1,\dots,n+1\}$. The band (16) is $\{y:V_{n+1}^{(x,y)}\le\mathrm{Quantile}(1-\alpha;\sum_{i=1}^np_i^w(Z_1,\dots,Z_n,(x,y))\delta_{V_i^{(x,y)}}+p_{n+1}^w(Z_1,\dots,Z_n,(x,y))\delta_\infty)\}$.
--
--   **Formalization Note** The augmented real line is `EReal` with $\infty=\top$; quantiles take values there, and the infimum of an empty set is $+\infty$. Weights enter a discrete distribution through `ENNReal.ofReal`, which is the identity on the nonnegative weights used here. When a denominator in (7) or (15) is $0$, Lean's division returns $0$, all weights vanish and the quantile is $+\infty$; this happens only on a null event in every statement. The paper allows an arbitrary base measure in Definition 1; the definition requires it to be permutation invariant, because with an arbitrary base measure Lemma 3 is false (see the report).
-- source:
--   Tibshirani, Barber, Candès and Ramdas, Conformal Prediction Under Covariate Shift, arXiv:1904.06019v3 (2019), Section 1.1 (quantiles, p. 2), Section 1.2 (eqs. (4)-(5), pp. 2-3), Section 2.1 (eqs. (7)-(8), p. 4), Section 3.2 (Definition 1, p. 12), Sections 3.3-3.4 (eqs. (15)-(16), pp. 12-13)

import Mathlib

/-!
Tibshirani, Barber, Candès and Ramdas, *Conformal Prediction Under Covariate Shift*,
arXiv:1904.06019v3 (2019): quantiles of discrete distributions on the augmented real line
(Section 1.1), nonconformity scores and the conformal band (Section 1.2, eqs. (4)-(5)), the
covariate-shift weights and band (Section 2.1, eqs. (7)-(8)), and weighted exchangeability with
the weights (15) and the weighted conformal band (16) (Sections 3.2-3.4).
-/

open MeasureTheory

noncomputable section

namespace ConformalCovariateShift

/-- Section 1.1, p. 2: `Quantile(β; F) = inf {z : P{Z ≤ z} ≥ β}` for `Z ∼ F`, where `F` is a
distribution on the augmented real line `ℝ ∪ {∞}`, here encoded in `EReal` (with `∞ = ⊤`). -/
def quantile (β : ℝ) (F : Measure EReal) : EReal :=
  sInf {z : EReal | ENNReal.ofReal β ≤ F (Set.Iic z)}

/-- Section 1.1, p. 2: the discrete distribution `∑_i p_i δ_{v_i}` on `ℝ ∪ {∞}`. With
`p_i = 1/m` for all `i` it is the empirical distribution of the multiset `v_{1:m}`. -/
def discreteDist {ι : Type*} [Fintype ι] (p : ι → ℝ) (v : ι → EReal) : Measure EReal :=
  ∑ i, ENNReal.ofReal (p i) • Measure.dirac (v i)

/-- Eqs. (8), (16) and Lemma 3: `∑_{i=1}^n p_i δ_{v_i} + p_{n+1} δ_∞`, the distribution of
the first `n` values with weights `p_1, …, p_n` plus a point mass `p_{n+1}` at `∞` (the
`(n+1)`-st value is not used). -/
def augDist {n : ℕ} (p : Fin (n + 1) → ℝ) (v : Fin (n + 1) → ℝ) : Measure EReal :=
  discreteDist p (fun i => if i = Fin.last n then (⊤ : EReal) else (v i : EReal))

/-- Lemma 1 and eq. (5): `Quantile(β; v_{1:n} ∪ {∞})`, the level-`β` quantile of the empirical
distribution of the `n + 1` values `v_1, …, v_n, ∞` (the `(n+1)`-st value is not used). -/
def quantileWithInf {n : ℕ} (β : ℝ) (v : Fin (n + 1) → ℝ) : EReal :=
  quantile β (augDist (fun _ => 1 / ((n : ℝ) + 1)) v)

/-- Eq. (2): `Quantile(β; v_{1:(n+1)})`, the level-`β` quantile of the empirical distribution
of the `n + 1` real values `v_1, …, v_{n+1}`. -/
def empQuantile {n : ℕ} (β : ℝ) (v : Fin (n + 1) → ℝ) : EReal :=
  quantile β (discreteDist (fun _ => 1 / ((n : ℝ) + 1)) (fun i => (v i : EReal)))

/-- Section 1.2, p. 2: a data point `(x, y) ∈ ℝ^d × ℝ`. -/
abbrev DataPt (d : ℕ) : Type := (Fin d → ℝ) × ℝ

/-- Section 1.2, p. 2 and footnote 1: a score function `S((x, y), Z)` of a point and a multiset
`Z` of points (the points of `Z` are unordered). -/
abbrev ScoreFn (E : Type*) : Type _ := E → Multiset E → ℝ

/-- Eq. (4) and Lemma 3: the nonconformity scores `V_i = S(z_i, z_{1:m} \ {z_i})` of the points
`z_1, …, z_m`, where `z_{1:m} \ {z_i}` is the multiset of the other `m - 1` points. -/
def scores {E : Type*} {m : ℕ} (S : ScoreFn E) (z : Fin m → E) (i : Fin m) : ℝ :=
  S (z i) ((Finset.univ.erase i).val.map z)

/-- Section 1.2, p. 2: the `n + 1` points `Z_1, …, Z_n, (x, y)` formed by the `n` training points
and a candidate test point `(x, y)`; the scores of eq. (4) are `scores S (withTest Z (x, y))`. -/
def withTest {E : Type*} {n : ℕ} (data : Fin n → E) (p : E) : Fin (n + 1) → E :=
  Fin.snoc (α := fun _ => E) data p

/-- Section 1.1 and the proof of Theorem 1, p. 3: the random variables `V_1, …, V_m` (measurable
maps on a probability space) are exchangeable, i.e. `(V_{σ(1)}, …, V_{σ(m)})` and
`(V_1, …, V_m)` have the same joint law for every permutation `σ`. -/
def IsExchangeable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] {m : ℕ}
    (P : Measure Omega) (V : Fin m → Omega → E) : Prop :=
  (∀ i, Measurable (V i)) ∧
    ∀ σ : Equiv.Perm (Fin m),
      Measure.map (fun ω i => V (σ i) ω) P = Measure.map (fun ω i => V i ω) P

/-- Eq. (5), Theorem 1: the conformal band at `x` built from the training points
`Z_1, …, Z_n`: the set of `y ∈ ℝ` with `V_{n+1}^{(x,y)} ≤ Quantile(1 - α; V_{1:n}^{(x,y)} ∪ {∞})`. -/
def conformalBand {d n : ℕ} (S : ScoreFn (DataPt d)) (α : ℝ) (data : Fin n → DataPt d)
    (x : Fin d → ℝ) : Set ℝ :=
  {y | (scores S (withTest data (x, y)) (Fin.last n) : EReal) ≤
    quantileWithInf (1 - α) (scores S (withTest data (x, y)))}

/-- Eq. (7), Section 2.1, p. 4: the covariate-shift weights
`p_i^w(x) = w(X_i) / (∑_{j=1}^n w(X_j) + w(x))` for `i ≤ n` and
`p_{n+1}^w(x) = w(x) / (∑_{j=1}^n w(X_j) + w(x))`. -/
def covShiftWeights {d n : ℕ} (w : (Fin d → ℝ) → ℝ) (X : Fin n → (Fin d → ℝ))
    (x : Fin d → ℝ) : Fin (n + 1) → ℝ :=
  fun i => w (withTest X x i) / (∑ j, w (X j) + w x)

/-- Eq. (8), Corollary 1: the weighted conformal band under covariate shift: the set of `y ∈ ℝ`
with `V_{n+1}^{(x,y)} ≤ Quantile(1 - α; ∑_{i=1}^n p_i^w(x) δ_{V_i^{(x,y)}} + p_{n+1}^w(x) δ_∞)`. -/
def covShiftBand {d n : ℕ} (S : ScoreFn (DataPt d)) (α : ℝ) (w : (Fin d → ℝ) → ℝ)
    (data : Fin n → DataPt d) (x : Fin d → ℝ) : Set ℝ :=
  {y | (scores S (withTest data (x, y)) (Fin.last n) : EReal) ≤
    quantile (1 - α) (augDist (covShiftWeights w (fun i => (data i).1) x)
      (scores S (withTest data (x, y))))}

/-- Definition 1, Section 3.2, p. 12: the random variables `Z_1, …, Z_m` are weighted
exchangeable with weight functions `w_1, …, w_m` if their joint law has a density `f` with respect
to a base measure `ν` on `E^m` and `f(z_1, …, z_m) = ∏_i w_i(z_i) · g(z_1, …, z_m)` with `g`
invariant under permutations of its arguments. The `Z_i` are measurable, the weight functions are
measurable and nonnegative, and the base measure `ν` is required to be invariant under
permutations of the coordinates (the paper says "arbitrary base measure"; see the mission's
report for why invariance is needed). -/
def IsWeightedExchangeable {Omega E : Type*} [MeasurableSpace Omega] [MeasurableSpace E] {m : ℕ}
    (P : Measure Omega) (Z : Fin m → Omega → E) (w : Fin m → E → ℝ) : Prop :=
  (∀ i, Measurable (Z i)) ∧ (∀ i, Measurable (w i)) ∧ (∀ i z, 0 ≤ w i z) ∧
    ∃ (ν : Measure (Fin m → E)) (f g : (Fin m → E) → ENNReal),
      (∀ σ : Equiv.Perm (Fin m), Measure.map (fun z => z ∘ σ) ν = ν) ∧
      Measurable f ∧
      Measure.map (fun ω i => Z i ω) P = ν.withDensity f ∧
      (∀ z, f z = (∏ i, ENNReal.ofReal (w i (z i))) * g z) ∧
      (∀ (σ : Equiv.Perm (Fin m)) (z : Fin m → E), g (z ∘ σ) = g z)

/-- Eq. (15), Lemma 3, p. 12: `p_i^w(z_1, …, z_{n+1}) =
(∑_{σ : σ(n+1) = i} ∏_{j=1}^{n+1} w_j(z_{σ(j)})) / (∑_σ ∏_{j=1}^{n+1} w_j(z_{σ(j)}))`, the sums
running over permutations `σ` of `1, …, n+1`. -/
def permWeight {E : Type*} {n : ℕ} (w : Fin (n + 1) → E → ℝ) (z : Fin (n + 1) → E)
    (i : Fin (n + 1)) : ℝ :=
  (∑ σ ∈ Finset.univ.filter (fun σ : Equiv.Perm (Fin (n + 1)) => σ (Fin.last n) = i),
      ∏ j, w j (z (σ j))) /
    ∑ σ : Equiv.Perm (Fin (n + 1)), ∏ j, w j (z (σ j))

/-- Eq. (16), Theorem 2, p. 13: the weighted conformal band: the set of `y ∈ ℝ` with
`V_{n+1}^{(x,y)} ≤ Quantile(1 - α; ∑_{i=1}^n p_i^w(Z_1, …, Z_n, (x, y)) δ_{V_i^{(x,y)}}
+ p_{n+1}^w(Z_1, …, Z_n, (x, y)) δ_∞)`. -/
def weightedConformalBand {d n : ℕ} (S : ScoreFn (DataPt d)) (α : ℝ)
    (w : Fin (n + 1) → DataPt d → ℝ) (data : Fin n → DataPt d) (x : Fin d → ℝ) : Set ℝ :=
  {y | (scores S (withTest data (x, y)) (Fin.last n) : EReal) ≤
    quantile (1 - α) (augDist (permWeight w (withTest data (x, y)))
      (scores S (withTest data (x, y))))}

end ConformalCovariateShift


