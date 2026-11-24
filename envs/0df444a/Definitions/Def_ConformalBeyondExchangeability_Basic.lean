-- Prove2me | Definitions.Def_ConformalBeyondExchangeability_Basic
-- name    : ConformalBeyondExchangeability_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T07:45:51.663642+00:00
-- url     : https://prove2.me/theorems/7e3e7b90-500a-40f3-b6db-aac08f01464c
-- title:
--   Weighted quantiles, nonexchangeable conformal sets, jackknife+ intervals and swap distances
-- statement:
--   Objects of Barber, Candès, Ramdas and Tibshirani (2023), Sections 2-4 and Appendices B, C, E.
--
--   1. **Data.** The data are $Z=(Z_1,\dots,Z_{n+1})$ with $Z_i=(X_i,Y_i)\in\mathcal X\times\mathbb R$; points $1,\dots,n$ are the training data and $Z_{n+1}$ is the test point. Their joint law $P$ on $(\mathcal X\times\mathbb R)^{n+1}$ is arbitrary. For $k\in[n+1]$, $\pi_k$ is the transposition of $k$ and $n+1$ ($\pi_{n+1}=\mathrm{id}$), and $Z^k=(Z_{\pi_k(1)},\dots,Z_{\pi_k(n+1)})$ is $Z$ with the test point and point $k$ swapped (eq. (2)). For $y\in\mathbb R$, $Y^y_i=Y_i$ for $i\le n$ and $Y^y_{n+1}=y$.
--   2. **Weighted quantiles.** For masses $p_i$ at points $v_i\in[-\infty,+\infty]$, $\mathsf Q_\tau(\sum_ip_i\delta_{v_i})=\inf\{q:\sum_{i:v_i\le q}p_i\ge\tau\}$ is the smallest $\tau$-quantile (footnote 1). In the jackknife+ lower endpoint, $\mathsf Q_\alpha$ is the largest $\alpha$-quantile, $\sup\{q:\sum_{i:v_i<q}p_i\le\alpha\}$ (footnote 7).
--   3. **Weights.** Fixed weights $w_1,\dots,w_n\in[0,1]$ give $\tilde w_i=w_i/(w_1+\dots+w_n+1)$ for $i\le n$ and $\tilde w_{n+1}=1/(w_1+\dots+w_n+1)$ (eq. (10)). The random index $K\sim\sum_i\tilde w_i\delta_i$ is drawn independently of $Z$ (eq. (17)), so an event $E$ has probability $\sum_k\tilde w_k\,P\{Z\in E_k\}$, where $E_k$ is the event for $K=k$.
--   4. **Algorithms.** A tagged algorithm $\mathcal A$ maps any finite sequence of tagged points $(x_i,y_i,t_i)\in\mathcal X\times\mathbb R\times\mathcal T$ to a function $\hat\mu:\mathcal X\to\mathbb R$ (eq. (16)); the tags $t_1,\dots,t_{n+1}$ are fixed. An untagged algorithm acts on sequences of points $(x_i,y_i)$. It is symmetric if permuting its input does not change its output (eq. (6)).
--   5. **Residuals and the coverage-gap term.** $R(z)_i=|y_i-\hat\mu(x_i)|$ with $\hat\mu=\mathcal A((x_i,y_i,t_i):i\in[n+1])$ (Section 4). For split conformal, $R(z)_i=|y_i-\hat\mu(x_i)|$ for the pre-fitted $\hat\mu$. The term $\sum_{i=1}^n\tilde w_i\,\mathsf d_{\mathsf{TV}}(R(Z),R(Z^i))$ uses the total variation distance $\mathsf d_{\mathsf{TV}}(\mu,\nu)=\sup_A|\mu(A)-\nu(A)|$ between the laws of $R(Z)$ and $R(Z^i)$.
--   6. **Conformal sets.** Split conformal (eqs. (5), (11)) is $\hat C_n(X_{n+1})=\{y:|y-\hat\mu(X_{n+1})|\le\mathsf Q_{1-\alpha}(\sum_{i=1}^n\tilde w_i\delta_{R_i}+\tilde w_{n+1}\delta_{+\infty})\}$. Nonexchangeable full conformal (eq. (18)) is $\{y:R^{y,K}_{n+1}\le\mathsf Q_{1-\alpha}(\sum_{i=1}^{n+1}\tilde w_i\delta_{R^{y,K}_i})\}$, where $R^{y,k}_i=|Y^y_i-\hat\mu^{y,k}(X_i)|$ and $\hat\mu^{y,k}=\mathcal A((X_{\pi_k(i)},Y^y_{\pi_k(i)},t_i):i\in[n+1])$. For a symmetric algorithm, eq. (12) is the same set with $\hat\mu^y=\mathcal A((X_1,Y_1),\dots,(X_n,Y_n),(X_{n+1},y))$; with $w\equiv1$ it is full conformal (eq. (8)).
--   7. **Jackknife+.** $\hat\mu_{-ij}=\mathcal A((x_k,y_k,t_k):k\in[n+1]\setminus\{i,j\})$, and $R_{\mathrm{jack+}}(z)$ is the matrix with entries $|y_i-\hat\mu_{-ij}(x_i)|$ for $i\neq j$ and zero diagonal. $\hat\mu^k_{-i}=\mathcal A((X_{\pi_k(j)},Y_{\pi_k(j)},t_j):\pi_k(j)\notin\{i,n+1\})$ and $R^{k,\mathrm{LOO}}_i=|Y_i-\hat\mu^k_{-i}(X_i)|$. The interval (eq. (34)) is $[\mathsf Q_\alpha(\sum_{i\le n}\tilde w_i\delta_{\hat\mu^K_{-i}(X_{n+1})-R^{K,\mathrm{LOO}}_i}+\tilde w_{n+1}\delta_{-\infty}),\ \mathsf Q_{1-\alpha}(\sum_{i\le n}\tilde w_i\delta_{\hat\mu^K_{-i}(X_{n+1})+R^{K,\mathrm{LOO}}_i}+\tilde w_{n+1}\delta_{+\infty})]$. Eq. (33) is the symmetric version, with leave-one-out models $\hat\mu_{-i}$ fitted on $(X_j,Y_j)$, $j\in[n]\setminus\{i\}$.
--   8. **Strange points.** $\mathcal S(r)=\{i:r_i>\mathsf Q_{1-\alpha}(\sum_jp_j\delta_{r_j})\}$ for $r\in\mathbb R^{n+1}$ (eq. (24)), and $\mathcal S(r)=\{i:\sum_jp_j\mathbb 1\{r_{ij}>r_{ji}\}\ge1-\alpha\}$ for a matrix $r$ (eq. (39)).
--   9. **Contamination.** $\mathsf d_{\mathrm{mix}}(D,D')=\inf\{t\ge0:D=(1-t)D'+tD''\text{ for a distribution }D''\}$ (eq. (36)). With $\bar w_i=w_i/(w_1+\dots+w_n)$, the contamination term is $\sum_{i=1}^n\bar w_i\,\mathsf d_{\mathrm{mix}}(Z_i,Z_{n+1})$. $\mathbb E[f(B)]$ for independent $B_i\sim\mathrm{Bernoulli}(p_i)$ is the finite sum $\sum_{b\in\{0,1\}^n}\prod_ip_i^{b_i}(1-p_i)^{1-b_i}f(b)$.
--
--   **Formalization Note** Indices run over $\mathrm{Fin}(n+1)$, with the last index the test point. Algorithms take Lean lists, which are finite sequences of any length. Quantiles take values in the extended reals $[-\infty,+\infty]$, so the infimum of an empty set is $+\infty$ and the atoms at $\pm\infty$ are represented exactly. The probability over the data and the independent index $K$ is written as the finite sum $\sum_k\tilde w_k\,P\{\cdot\}$. Total variation is a real supremum over measurable sets. $\mathsf d_{\mathrm{mix}}$ restricts $t$ to $[0,1]$, the only values for which $(1-t)D'$ is a measure.
-- source:
--   Barber, Candès, Ramdas and Tibshirani, Conformal prediction beyond exchangeability, arXiv:2202.13415v5 (2023), Section 2 (eqs. (5)-(8), footnote 1), Section 3 (eqs. (10)-(12), (16)-(18)), Section 4 (residual map R), Section 6.2 (eq. (24)), Appendix B (eqs. (31)-(34), footnote 3), Appendix C (eq. (36)), Appendix E.4.2 (eq. (39)), Appendix E.5 (Lemma 3)

import Mathlib

/-!
Barber, Candès, Ramdas and Tibshirani, *Conformal prediction beyond exchangeability*,
arXiv:2202.13415v5 (2023): weighted quantiles (Section 2, footnote 1; Appendix B.1, footnote 7),
normalized weights (eq. (10)), the swapped data sequence `Z^i` (eq. (2)), the total variation
distance, split and full conformal prediction (eqs. (5), (8), (11), (12)), tagged nonsymmetric
algorithms and nonexchangeable full conformal prediction with the random swap index `K`
(eqs. (16)-(18)), the residual map `R` (Section 4), the strange-point sets (eqs. (24), (39)),
the jackknife+ (Appendix B, eqs. (33)-(34)), the contamination distance `d_mix` (eq. (36)) and
expectations over independent Bernoulli variables (Lemma 3).

Data points are `Z_i = (X_i, Y_i) ∈ X × ℝ`, indexed by `Fin (n + 1)`; index `Fin.last n` is the
test point `n + 1`, and `Fin.castSucc i` (for `i : Fin n`) is the training point `i + 1`.
-/

open MeasureTheory

noncomputable section

namespace ConformalBeyondExchangeability

/-- Section 2, eq. (5) and footnote 1: `Q_τ(∑_i p_i δ_{v_i})`, the smallest `τ`-quantile of the
discrete distribution with masses `p_i` at the points `v_i ∈ [-∞, +∞]`:
`inf {q : ∑_{i : v_i ≤ q} p_i ≥ τ}` (the infimum of the empty set is `+∞`). -/
def wQuantile {m : ℕ} (p : Fin m → ℝ) (v : Fin m → EReal) (τ : ℝ) : EReal :=
  sInf {q : EReal | τ ≤ ∑ i, if v i ≤ q then p i else 0}

/-- Appendix B.1, footnote 7: `Q_τ(∑_i p_i δ_{v_i})` in the lower endpoint of the jackknife+
interval, the largest `τ`-quantile: `sup {q : ∑_{i : v_i < q} p_i ≤ τ}`. -/
def wQuantileUpper {m : ℕ} (p : Fin m → ℝ) (v : Fin m → EReal) (τ : ℝ) : EReal :=
  sSup {q : EReal | (∑ i, if v i < q then p i else 0) ≤ τ}

/-- Eq. (10): the normalized weights `w̃_i = w_i / (w_1 + ⋯ + w_n + 1)` for `i ≤ n` and
`w̃_{n+1} = 1 / (w_1 + ⋯ + w_n + 1)`. -/
def normWeights {n : ℕ} (w : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  fun i => (if h : (i : ℕ) < n then w ⟨i, h⟩ else 1) / (∑ j, w j + 1)

/-- Eq. (3) and Lemma 1: the total variation distance
`d_TV(μ, ν) = sup_A |μ(A) - ν(A)|` over measurable sets `A`. -/
def tvDist {Ω : Type*} [MeasurableSpace Ω] (μ ν : Measure Ω) : ℝ :=
  sSup {r | ∃ A : Set Ω, MeasurableSet A ∧ r = |μ.real A - ν.real A|}

/-- Section 3.2: `π_k`, the permutation of `[n+1]` swapping `k` and `n + 1` (the identity when
`k = n + 1`). -/
def swapIdx {n : ℕ} (k : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.swap k (Fin.last n)

/-- Eq. (2): `Z^k = (Z_1, …, Z_{k-1}, Z_{n+1}, Z_{k+1}, …, Z_n, Z_k)`, the data sequence with
the test point and the `k`-th point swapped, i.e. `(Z^k)_i = Z_{π_k(i)}`. -/
def swapData {E : Type*} {n : ℕ} (k : Fin (n + 1)) (z : Fin (n + 1) → E) : Fin (n + 1) → E :=
  fun i => z (swapIdx k i)

/-- Section 3.2: the data `(X_1, Y^y_1), …, (X_{n+1}, Y^y_{n+1})` with `Y^y_i = Y_i` for `i ≤ n`
and `Y^y_{n+1} = y`, i.e. the training data together with the hypothesized test point
`(X_{n+1}, y)`. -/
def withTest {X : Type*} {n : ℕ} (z : Fin (n + 1) → X × ℝ) (y : ℝ) : Fin (n + 1) → X × ℝ :=
  Function.update z (Fin.last n) ((z (Fin.last n)).1, y)

/-- Eq. (16): an algorithm `A : ∪_{m ≥ 0} (X × ℝ × T)^m → {μ̂ : X → ℝ}` mapping a finite
sequence of tagged data points `(X_i, Y_i, t_i)` to a fitted regression function. -/
abbrev TaggedAlg (X T : Type*) : Type _ := List (X × ℝ × T) → X → ℝ

/-- Section 2, full conformal prediction: an algorithm `A : ∪_{m ≥ 0} (X × ℝ)^m → {μ̂ : X → ℝ}`
on untagged data points `(X_i, Y_i)`. -/
abbrev Alg (X : Type*) : Type _ := List (X × ℝ) → X → ℝ

/-- Eq. (6): the algorithm treats the data points symmetrically,
`A((x_{π(1)}, y_{π(1)}), …, (x_{π(m)}, y_{π(m)})) = A((x_1, y_1), …, (x_m, y_m))` for every
`m` and every permutation `π`. -/
def IsSymmetric {X : Type*} (alg : Alg X) : Prop :=
  ∀ l l' : List (X × ℝ), l.Perm l' → alg l = alg l'

/-- Theorem 1: the data points `Z_1, …, Z_{n+1}` are exchangeable: their joint law `P` is
invariant under every permutation of the indices. -/
def IsExchangeable {E : Type*} [MeasurableSpace E] {m : ℕ} (P : Measure (Fin m → E)) : Prop :=
  ∀ σ : Equiv.Perm (Fin m), P.map (fun z i => z (σ i)) = P

/-- Section 3.2: the tagged sequence `((x_1, y_1, t_1), …, (x_{n+1}, y_{n+1}, t_{n+1}))`. -/
def tagged {X T : Type*} {n : ℕ} (t : Fin (n + 1) → T) (z : Fin (n + 1) → X × ℝ) :
    List (X × ℝ × T) :=
  List.ofFn fun i => ((z i).1, (z i).2, t i)

/-- Section 4: the residual vector `R(z)`, `R(z)_i = |y_i - μ̂(x_i)|` with
`μ̂ = A((x_i, y_i, t_i) : i ∈ [n+1])`. -/
def residuals {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (z : Fin (n + 1) → X × ℝ) : Fin (n + 1) → ℝ :=
  fun i => |(z i).2 - alg (tagged t z) (z i).1|

/-- Section 3.2: the residuals `R^{y,k}_i = |Y^y_i - μ̂^{y,k}(X_i)|` of the model
`μ̂^{y,k} = A((X_{π_k(i)}, Y^y_{π_k(i)}, t_i) : i ∈ [n+1])`. -/
def swapResiduals {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (z : Fin (n + 1) → X × ℝ) (y : ℝ) (k : Fin (n + 1)) : Fin (n + 1) → ℝ :=
  fun i => |(withTest z y i).2 - alg (tagged t (swapData k (withTest z y))) (withTest z y i).1|

/-- Eq. (18): the nonexchangeable full conformal prediction set for the value `K = k` of the
random index, `{y : R^{y,k}_{n+1} ≤ Q_{1-α}(∑_{i=1}^{n+1} w̃_i δ_{R^{y,k}_i})}`. It depends on
`z` only through `(X_1, Y_1), …, (X_n, Y_n), X_{n+1}`. -/
def fullSet {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (w : Fin n → ℝ) (α : ℝ) (z : Fin (n + 1) → X × ℝ) (k : Fin (n + 1)) : Set ℝ :=
  {y | (swapResiduals alg t z y k (Fin.last n) : EReal) ≤
    wQuantile (normWeights w) (fun i => (swapResiduals alg t z y k i : EReal)) (1 - α)}

/-- Eq. (17): the probability of an event depending on the data `Z ∼ P` and on the random index
`K ∼ ∑_i w̃_i δ_i`, drawn independently of `Z`: `P{E} = ∑_k w̃_k P{Z ∈ E_k}`, where `E_k` is the
event for `K = k`. -/
def randIndexProb {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (P : Measure Ω) (w : Fin n → ℝ)
    (E : Fin (n + 1) → Set Ω) : ℝ :=
  ∑ k, normWeights w k * P.real (E k)

/-- Theorem 2: the coverage probability `P{Y_{n+1} ∈ Ĉ_n(X_{n+1})}` of nonexchangeable full
conformal prediction (eq. (18)), over the data `Z ∼ P` and the independent index `K`. -/
def fullCoverage {X T : Type*} [MeasurableSpace X] {n : ℕ} (P : Measure (Fin (n + 1) → X × ℝ))
    (alg : TaggedAlg X T) (t : Fin (n + 1) → T) (w : Fin n → ℝ) (α : ℝ) : ℝ :=
  randIndexProb P w (fun k => {z | (z (Fin.last n)).2 ∈ fullSet alg t w α z k})

/-- Section 2 and eq. (11): the residuals `|Y_i - μ̂(X_i)|`, `i = 1, …, n+1`, of a pre-fitted
model `μ̂` (the residual vector `R(Z)` of split conformal prediction). -/
def splitResiduals {X : Type*} {n : ℕ} (μ : X → ℝ) (z : Fin (n + 1) → X × ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => |(z i).2 - μ (z i).1|

/-- Eq. (11): the nonexchangeable split conformal interval
`μ̂(X_{n+1}) ± Q_{1-α}(∑_{i=1}^n w̃_i δ_{R_i} + w̃_{n+1} δ_{+∞})`, written as the set of `y` with
`|y - μ̂(X_{n+1})| ≤ Q_{1-α}(…)`. With `w_1 = ⋯ = w_n = 1` it is the split conformal interval
of eq. (5). -/
def splitSet {X : Type*} {n : ℕ} (μ : X → ℝ) (w : Fin n → ℝ) (α : ℝ)
    (z : Fin (n + 1) → X × ℝ) : Set ℝ :=
  {y | ((|y - μ (z (Fin.last n)).1| : ℝ) : EReal) ≤
    wQuantile (normWeights w)
      (fun i => if i = Fin.last n then ⊤ else (splitResiduals μ z i : EReal)) (1 - α)}

/-- Theorems 1-3: the coverage probability `P{Y_{n+1} ∈ Ĉ_n(X_{n+1})}` of split conformal
prediction (eq. (11)). -/
def splitCoverage {X : Type*} [MeasurableSpace X] {n : ℕ} (P : Measure (Fin (n + 1) → X × ℝ))
    (μ : X → ℝ) (w : Fin n → ℝ) (α : ℝ) : ℝ :=
  P.real {z | (z (Fin.last n)).2 ∈ splitSet μ w α z}

/-- Theorems 2, 3 and 5: the coverage-gap term `∑_{i=1}^n w̃_i · d_TV(R(Z), R(Z^i))` for a
map `R` of the data sequence (a residual vector or matrix), where `Z ∼ P`. -/
def swapGap {X E : Type*} [MeasurableSpace X] [MeasurableSpace E] {n : ℕ}
    (P : Measure (Fin (n + 1) → X × ℝ)) (w : Fin n → ℝ) (R : (Fin (n + 1) → X × ℝ) → E) : ℝ :=
  ∑ i : Fin n, normWeights w i.castSucc *
    tvDist (P.map R) (P.map fun z => R (swapData i.castSucc z))

/-- Eq. (24): the strange points of `r ∈ ℝ^{n+1}`,
`S(r) = {i : r_i > Q_{1-α}(∑_{j=1}^{n+1} p_j δ_{r_j})}` (with `p = w̃`). -/
def strangeSet {m : ℕ} (p : Fin m → ℝ) (α : ℝ) (r : Fin m → ℝ) : Finset (Fin m) :=
  Finset.univ.filter fun i => wQuantile p (fun j => (r j : EReal)) (1 - α) < (r i : EReal)

/-- Section 2, eqs. (7)-(8) and Section 6.1: the residual vector of a symmetric algorithm,
`R(z)_i = |y_i - μ̂(x_i)|` with `μ̂ = A((x_1, y_1), …, (x_{n+1}, y_{n+1}))`. -/
def symResiduals {X : Type*} {n : ℕ} (alg : Alg X) (z : Fin (n + 1) → X × ℝ) :
    Fin (n + 1) → ℝ :=
  fun i => |(z i).2 - alg (List.ofFn z) (z i).1|

/-- Eq. (12): the nonexchangeable full conformal set for a symmetric algorithm,
`{y : R^y_{n+1} ≤ Q_{1-α}(∑_{i=1}^{n+1} w̃_i δ_{R^y_i})}`, with `R^y` the residuals (eq. (7)) of
`μ̂^y = A((X_1, Y_1), …, (X_n, Y_n), (X_{n+1}, y))`. With `w_1 = ⋯ = w_n = 1` it is the full
conformal set of eq. (8). -/
def symFullSet {X : Type*} {n : ℕ} (alg : Alg X) (w : Fin n → ℝ) (α : ℝ)
    (z : Fin (n + 1) → X × ℝ) : Set ℝ :=
  {y | (symResiduals alg (withTest z y) (Fin.last n) : EReal) ≤
    wQuantile (normWeights w) (fun i => (symResiduals alg (withTest z y) i : EReal)) (1 - α)}

/-- Appendix B.3: the leave-two-out model
`μ̂_{-ij} = A((x_k, y_k, t_k) : k ∈ [n+1] \ {i, j})`, the remaining points kept in order. -/
def ltoModel {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (z : Fin (n + 1) → X × ℝ) (i j : Fin (n + 1)) : X → ℝ :=
  alg (((List.finRange (n + 1)).filter fun k => decide (k ≠ i ∧ k ≠ j)).map
    fun k => ((z k).1, (z k).2, t k))

/-- Appendix B.3: the residual matrix `R_jack+(z)`, with entries `|y_i - μ̂_{-ij}(x_i)|` for
`i ≠ j` and zeros on the diagonal. -/
def jackResiduals {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (z : Fin (n + 1) → X × ℝ) : Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => if i = j then 0 else |(z i).2 - ltoModel alg t z i j (z i).1|

/-- Appendix B.2: the model `μ̂^k_{-i} = A((X_{π_k(j)}, Y_{π_k(j)}, t_j) : j ∈ [n+1],
π_k(j) ∉ {i, n+1})`, fitted on the training data without point `i`, with point `k` given the
tag `t_{n+1}`. -/
def looSwapModel {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (z : Fin (n + 1) → X × ℝ) (k i : Fin (n + 1)) : X → ℝ :=
  alg (((List.finRange (n + 1)).filter
      fun j => decide (swapIdx k j ≠ i ∧ swapIdx k j ≠ Fin.last n)).map
    fun j => ((z (swapIdx k j)).1, (z (swapIdx k j)).2, t j))

/-- Appendix B.2: the leave-one-out residual `R^{k,LOO}_i = |Y_i - μ̂^k_{-i}(X_i)|`. -/
def looSwapResidual {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (z : Fin (n + 1) → X × ℝ) (k i : Fin (n + 1)) : ℝ :=
  |(z i).2 - looSwapModel alg t z k i (z i).1|

/-- Eq. (34): the nonexchangeable jackknife+ interval for the value `K = k` of the random index,
`[Q_α(∑_{i=1}^n w̃_i δ_{μ̂^k_{-i}(X_{n+1}) - R^{k,LOO}_i} + w̃_{n+1} δ_{-∞}),
Q_{1-α}(∑_{i=1}^n w̃_i δ_{μ̂^k_{-i}(X_{n+1}) + R^{k,LOO}_i} + w̃_{n+1} δ_{+∞})]`, with the largest
`α`-quantile at the left end and the smallest `(1-α)`-quantile at the right end. -/
def jackInterval {X T : Type*} {n : ℕ} (alg : TaggedAlg X T) (t : Fin (n + 1) → T)
    (w : Fin n → ℝ) (α : ℝ) (z : Fin (n + 1) → X × ℝ) (k : Fin (n + 1)) : Set ℝ :=
  {y | wQuantileUpper (normWeights w)
        (fun i => if i = Fin.last n then ⊥ else
          ((looSwapModel alg t z k i (z (Fin.last n)).1 - looSwapResidual alg t z k i : ℝ) :
            EReal)) α ≤ (y : EReal) ∧
      (y : EReal) ≤ wQuantile (normWeights w)
        (fun i => if i = Fin.last n then ⊤ else
          ((looSwapModel alg t z k i (z (Fin.last n)).1 + looSwapResidual alg t z k i : ℝ) :
            EReal)) (1 - α)}

/-- Theorem 5: the coverage probability `P{Y_{n+1} ∈ Ĉ_n(X_{n+1})}` of the nonexchangeable
jackknife+ (eq. (34)), over the data `Z ∼ P` and the independent index `K`. -/
def jackCoverage {X T : Type*} [MeasurableSpace X] {n : ℕ} (P : Measure (Fin (n + 1) → X × ℝ))
    (alg : TaggedAlg X T) (t : Fin (n + 1) → T) (w : Fin n → ℝ) (α : ℝ) : ℝ :=
  randIndexProb P w (fun k => {z | (z (Fin.last n)).2 ∈ jackInterval alg t w α z k})

/-- Eq. (39): the weighted strange points of a matrix `r`,
`S(r) = {i : ∑_j p_j 1{r_ij > r_ji} ≥ 1 - α}`. -/
def tournamentStrangeSet {m : ℕ} (p : Fin m → ℝ) (α : ℝ) (r : Fin m → Fin m → ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => 1 - α ≤ ∑ j, if r j i < r i j then p j else 0

/-- Eq. (31): the leave-one-out model `μ̂_{-i} = A((X_j, Y_j) : j ∈ [n] \ {i})` of a symmetric
algorithm, fitted on the training data without point `i`. -/
def looModel {X : Type*} {n : ℕ} (alg : Alg X) (z : Fin (n + 1) → X × ℝ) (i : Fin (n + 1)) :
    X → ℝ :=
  alg (((List.finRange (n + 1)).filter fun j => decide (j ≠ i ∧ j ≠ Fin.last n)).map z)

/-- Eq. (33): the nonexchangeable jackknife+ interval for a symmetric algorithm,
`[Q_α(∑_{i=1}^n w̃_i δ_{μ̂_{-i}(X_{n+1}) - R^{LOO}_i} + w̃_{n+1} δ_{-∞}),
Q_{1-α}(∑_{i=1}^n w̃_i δ_{μ̂_{-i}(X_{n+1}) + R^{LOO}_i} + w̃_{n+1} δ_{+∞})]`, with
`R^{LOO}_i = |Y_i - μ̂_{-i}(X_i)|`. -/
def symJackInterval {X : Type*} {n : ℕ} (alg : Alg X) (w : Fin n → ℝ) (α : ℝ)
    (z : Fin (n + 1) → X × ℝ) : Set ℝ :=
  {y | wQuantileUpper (normWeights w)
        (fun i => if i = Fin.last n then ⊥ else
          ((looModel alg z i (z (Fin.last n)).1 - |(z i).2 - looModel alg z i (z i).1| : ℝ) :
            EReal)) α ≤ (y : EReal) ∧
      (y : EReal) ≤ wQuantile (normWeights w)
        (fun i => if i = Fin.last n then ⊤ else
          ((looModel alg z i (z (Fin.last n)).1 + |(z i).2 - looModel alg z i (z i).1| : ℝ) :
            EReal)) (1 - α)}

/-- Appendix B.3 for a symmetric algorithm: the residual matrix with entries
`|y_i - μ̂_{-ij}(x_i)|`, `μ̂_{-ij} = A((x_k, y_k) : k ∈ [n+1] \ {i, j})`, for `i ≠ j`, and zeros
on the diagonal. -/
def symJackResiduals {X : Type*} {n : ℕ} (alg : Alg X) (z : Fin (n + 1) → X × ℝ) :
    Fin (n + 1) → Fin (n + 1) → ℝ :=
  fun i j => if i = j then 0 else
    |(z i).2 - alg (((List.finRange (n + 1)).filter fun k => decide (k ≠ i ∧ k ≠ j)).map z)
      (z i).1|

/-- Eq. (36): `d_mix(D, D') = inf {t ≥ 0 : D = (1 - t) D' + t D'' for some distribution D''}`
for probability measures `D, D'` (only `t ≤ 1` can occur, since `(1 - t) D'` must be a
measure). -/
def dmix {Ω : Type*} [MeasurableSpace Ω] (D D' : Measure Ω) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ t ≤ 1 ∧ ∃ D'' : Measure Ω, IsProbabilityMeasure D'' ∧
    D = ENNReal.ofReal (1 - t) • D' + ENNReal.ofReal t • D''}

/-- Theorem 6: the contamination term `∑_{i=1}^n w̄_i · d_mix(Z_i, Z_{n+1})`, with
`w̄_i = w_i / (w_1 + ⋯ + w_n)` and `Z_i ∼ μ_i`. -/
def mixTerm {X : Type*} [MeasurableSpace X] {n : ℕ} (μ : Fin (n + 1) → Measure (X × ℝ))
    (w : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, w i / (∑ j, w j) * dmix (μ i.castSucc) (μ (Fin.last n))

/-- Lemma 3: `E[f(B_1, …, B_n)]` for independent `B_i ∼ Bernoulli(p_i)`,
`∑_{b ∈ {0,1}^n} ∏_i p_i^{b_i} (1 - p_i)^{1 - b_i} f(b)`. -/
def bernoulliExp {n : ℕ} (p : Fin n → ℝ) (f : (Fin n → Bool) → ℝ) : ℝ :=
  ∑ b : Fin n → Bool, (∏ i, if b i then p i else 1 - p i) * f b

/-- Lemma 3: the ratio `(a_1 + ⋯ + a_n + 1) / (a_1 b_1 + ⋯ + a_n b_n + 1)` at `b ∈ {0,1}^n`. -/
def invBernoulliRatio {n : ℕ} (a : Fin n → ℝ) (b : Fin n → Bool) : ℝ :=
  (∑ i, a i + 1) / (∑ i, a i * (if b i then 1 else 0) + 1)

end ConformalBeyondExchangeability


