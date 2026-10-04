-- Prove2me | Definitions.Def_IntermediateDisorder_PointToLine_UStatistic
-- name    : IntermediateDisorder_PointToLine_UStatistic
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T04:23:33.31339+00:00
-- url     : https://prove2.me/theorems/1f0d3a39-75f5-4d6f-afdf-6070c7e52fec
-- title:
--   Weighted U-statistics $\mathcal S_k^n(g)$ and the discrete kernels $p_k^n$ (eq. (29), Definition 5.1)
-- statement:
--   This file defines the discrete objects of Sections 3.1, 4.1 and 5.
--
--   **Rectangles and averages.** For $n\ge1$, a vector of times $\mathbf i\in[n]^k$ and sites $\mathbf x\in\mathbb Z^k$, let
--   $$R(\mathbf i,\mathbf x)=\Big(\frac{\mathbf i-\mathbf 1}{n},\frac{\mathbf i}{n}\Big]\times\Big(\frac{\mathbf x-\mathbf 1}{\sqrt n},\frac{\mathbf x+\mathbf 1}{\sqrt n}\Big]\subset[0,1]^k\times\mathbb R^k,$$
--   so $|R|=2^kn^{-3k/2}$. Write $\mathbf i\leftrightarrow\mathbf x$ if $\mathbf i_j$ and $\mathbf x_j$ have the same parity for every $j$; the rectangles with $\mathbf i\leftrightarrow\mathbf x$ tile $(0,1]^k\times\mathbb R^k$. For $g\in L^2([0,1]^k\times\mathbb R^k)$, $\bar g_n(\mathbf i/n,\mathbf x/\sqrt n)=|R(\mathbf i,\mathbf x)|^{-1}\int_{R(\mathbf i,\mathbf x)}g$ is the average of $g$ on that rectangle, and
--   $$\|\bar g_n\|^2_{L^2}=\sum_{\mathbf i\in[n]^k}\sum_{\mathbf x\leftrightarrow\mathbf i}|R(\mathbf i,\mathbf x)|\,\bar g_n(\mathbf i/n,\mathbf x/\sqrt n)^2 .$$
--
--   **U-statistics (29).** With $E_k^n=\{\mathbf i\in[n]^k:\mathbf i_j\ne\mathbf i_l\text{ for }j\ne l\}$ and $\omega(\mathbf i,\mathbf x)=\prod_{j=1}^k\omega(\mathbf i_j,\mathbf x_j)$,
--   $$\mathcal S_k^n(g)=2^{k/2}\sum_{\mathbf i\in E_k^n}\sum_{\mathbf x\in\mathbb Z^k}\bar g_n\Big(\frac{\mathbf i}{n},\frac{\mathbf x}{\sqrt n}\Big)\mathbf 1\{\mathbf i\leftrightarrow\mathbf x\}\,\omega(\mathbf i,\mathbf x),$$
--   with $\mathcal S_0^n(g_0)=g_0$. The **discrete chaos** of Lemma 4.4 is $I^n(g)=\sum_{k\ge0}n^{-3k/4}\mathcal S_k^n(g_k)$; the terms with $k>n$ vanish because $E_k^n=\emptyset$. A function $g$ is **simplex-supported** if it vanishes almost everywhere outside $\Delta_k\times\mathbb R^k$.
--
--   **Random walk kernels.** $p(i,x)=\mathbf P(S_i=x)$ is the simple random walk transition kernel, $p_k(\mathbf i,\mathbf x)=\prod_{j=1}^kp(\mathbf i_j-\mathbf i_{j-1},\mathbf x_j-\mathbf x_{j-1})$ with $\mathbf i_0=\mathbf x_0=0$, $[x]_i$ is the integer of the parity of $i$ closest to $x$, and $\bar p_k(\mathbf i,\mathbf x)=2^{-k}p_k(\mathbf i,[\mathbf x]_{\mathbf i})$. With $D_k^n=\{1\le\mathbf i_1<\dots<\mathbf i_k\le n\}$, **Definition 5.1** sets
--   $$p_k^n(\mathbf t,\mathbf x)=\bar p_k\big(\lceil n\mathbf t\rceil,\mathbf x\sqrt n\big)\,\mathbf 1\{\lceil n\mathbf t\rceil\in D_k^n\}.$$
--
--   These are the objects through which the paper writes the modified partition function as a finite sum of U-statistics (Lemma 5.2) and compares them with the multiple stochastic integrals of white noise.
--
--   **Formalization Note** The inner sum over $\mathbf x\in\mathbb Z^k$ is an $L^2(Q)$-valued sum of orthogonal terms: for a general $L^2$ kernel the coefficients are square summable but not summable, so a pointwise real series would be meaningless. Each $\omega(\mathbf i,\mathbf x)$ and $p_k^n$ is turned into an $L^2$ element by a case split on membership in $L^2$; the milestones on Lemma 4.1 and Lemma A.1 rule out the default values. The paper indexes the rectangles by $\mathbf i\in D_k^n$ but evaluates $\bar g_n$ at $\mathbf i\in E_k^n$; here a rectangle is defined for every $\mathbf i\in[n]^k$. $p(i,x)$ is defined as the fraction of the $2^i$ step sequences ending at $x$. Ties in $[x]_i$ (a null set) are broken upwards. $\|\bar g_n\|^2$ is an extended nonnegative real. For $k=0$, $p_0^n=1$.
-- source:
--   Alberts, Khanin, Quastel, The intermediate disorder regime for directed polymers in dimension 1+1, arXiv:1202.4398v3, pp. 16–17, §3.1 (p, p_k, D_k^n, i↔x, [x]_i, p̄_k); p. 21, §4.1 (E_k^n, 𝓡_k^n, ḡ_n, eq. (29)); p. 22, remark; p. 27, Lemma 4.4 (I^n); p. 29, Definition 5.1

import Mathlib
import Definitions.Def_IntermediateDisorder_PointToLine_Environment
import Definitions.Def_IntermediateDisorder_PointToLine_WienerChaos

namespace IntermediateDisorder.PointToLine

open MeasureTheory ProbabilityTheory

/-- The rectangle `((i - 1)/n, i/n] × ((x - 1)/√n, (x + 1)/√n]` of `𝓡_k^n` (§4.1), for a vector
of times `i ∈ ℕ^k` and of sites `x ∈ ℤ^k`, as a subset of `[0,1]^k × ℝ^k`
(coordinates `z j = (t_j, x_j)`). -/
noncomputable def cell {k : ℕ} (n : ℕ) (i : Fin k → ℕ) (x : Fin k → ℤ) :
    Set (Fin k → ℝ × ℝ) :=
  Set.univ.pi fun j =>
    Set.Ioc (((i j : ℝ) - 1) / n) ((i j : ℝ) / n) ×ˢ
      Set.Ioc (((x j : ℝ) - 1) / Real.sqrt n) (((x j : ℝ) + 1) / Real.sqrt n)

/-- `ḡ_n(i/n, x/√n) = |R|⁻¹ ∫_R g` for the rectangle `R` of `𝓡_k^n` with corner data `(i, x)`:
the average of `g` over that rectangle. -/
noncomputable def cellAverage {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) (n : ℕ)
    (i : Fin k → ℕ) (x : Fin k → ℤ) : ℝ :=
  ((kernelMeasure k) (cell n i x)).toReal⁻¹ * ∫ z in cell n i x, g z ∂(kernelMeasure k)

/-- The parity relation `i ↔ x`: `i_j` and `x_j` have the same parity for every `j`. -/
def ParityMatch {k : ℕ} (i : Fin k → ℕ) (x : Fin k → ℤ) : Prop :=
  ∀ j, Even ((i j : ℤ) - x j)

/-- `ω(i, x) = ∏_{j=1}^k ω(i_j, x_j)`. -/
def envProduct {Ω : Type*} (ω : ℕ × ℤ → Ω → ℝ) {k : ℕ} (i : Fin k → ℕ) (x : Fin k → ℤ) :
    Ω → ℝ :=
  fun a => ∏ j, ω (i j, x j) a

open scoped Classical in
/-- `ω(i, x)` as an element of `L²(Q)` (junk value `0` only if it is not square integrable,
which does not happen for distinct times `i` under `IsStdEnvironment`). -/
noncomputable def envProductLp {Ω : Type*} [MeasurableSpace Ω] (ω : ℕ × ℤ → Ω → ℝ)
    (Q : Measure Ω) {k : ℕ} (i : Fin k → ℕ) (x : Fin k → ℤ) : Lp ℝ 2 Q :=
  if h : MemLp (envProduct ω i x) 2 Q then h.toLp _ else 0

/-- Time vector of an index `i : Fin k → Fin n`: the actual times are `i_j + 1 ∈ [n]`. -/
def timesOf {k n : ℕ} (i : Fin k → Fin n) : Fin k → ℕ := fun j => (i j : ℕ) + 1

open scoped Classical in
/-- One term `2^{k/2} ḡ_n(i/n, x/√n) 1{i ↔ x} ω(i, x)` of the weighted U-statistic (29), with
times `timesOf i`. -/
noncomputable def uStatisticTerm {Ω : Type*} [MeasurableSpace Ω] (ω : ℕ × ℤ → Ω → ℝ)
    (Q : Measure Ω) (n k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)) (i : Fin k → Fin n)
    (x : Fin k → ℤ) : Lp ℝ 2 Q :=
  (Real.sqrt 2 ^ k * cellAverage g n (timesOf i) x *
      (if ParityMatch (timesOf i) x then 1 else 0)) • envProductLp ω Q (timesOf i) x

open scoped Classical in
/-- The weighted U-statistic (29):
`𝒮_k^n(g) = 2^{k/2} ∑_{i ∈ E_k^n} ∑_{x ∈ ℤ^k} ḡ_n(i/n, x/√n) 1{i ↔ x} ω(i, x)`,
`E_k^n = {i ∈ [n]^k : i_j ≠ i_l for j ≠ l}`. The inner sum over `ℤ^k` is an `L²(Q)`-valued
`tsum` (a sum of orthogonal terms). For `k = 0` it is the constant `g_0`. -/
noncomputable def uStatistic {Ω : Type*} [MeasurableSpace Ω] (ω : ℕ × ℤ → Ω → ℝ)
    (Q : Measure Ω) (n k : ℕ) (g : Lp ℝ 2 (kernelMeasure k)) : Lp ℝ 2 Q :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin k → Fin n => Function.Injective i),
    ∑' x : Fin k → ℤ, uStatisticTerm ω Q n k g i x

open scoped Classical in
/-- `‖ḡ_n‖²_{L²([0,1]^k × ℝ^k)} = ∑_{i ∈ [n]^k} ∑_{x ↔ i} |R(i, x)| ḡ_n(i/n, x/√n)²`, the squared
norm of the rectangle average `ḡ_n` (constant on each rectangle; the rectangles tile
`(0,1]^k × ℝ^k`), as an extended nonnegative real. -/
noncomputable def cellAverageNormSq {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) (n : ℕ) :
    ENNReal :=
  ∑' p : (Fin k → Fin n) × (Fin k → ℤ),
    if ParityMatch (timesOf p.1) p.2 then
      kernelMeasure k (cell n (timesOf p.1) p.2) *
        ENNReal.ofReal (cellAverage g n (timesOf p.1) p.2 ^ 2)
    else 0

/-- `g` vanishes almost everywhere outside `Δ_k × ℝ^k`. -/
def SimplexSupported {k : ℕ} (g : Lp ℝ 2 (kernelMeasure k)) : Prop :=
  ∀ᵐ z ∂(kernelMeasure k), z ∉ simplex k → g z = 0

/-- The discrete chaos `I^n(g) = ∑_{k ≥ 0} n^{-3k/4} 𝒮_k^n(g_k)` of Lemma 4.4. The terms with
`k > n` vanish (`E_k^n = ∅`), so the sum is over `k ≤ n`. -/
noncomputable def discreteChaos {Ω : Type*} [MeasurableSpace Ω] (ω : ℕ × ℤ → Ω → ℝ)
    (Q : Measure Ω) (n : ℕ) (g : (k : ℕ) → Lp ℝ 2 (kernelMeasure k)) : Lp ℝ 2 Q :=
  ∑ k ∈ Finset.range (n + 1), ((n : ℝ) ^ (-(3 * (k : ℝ) / 4))) • uStatistic ω Q n k (g k)

open scoped Classical in
/-- The simple random walk transition kernel `p(m, y) = P(S_m = y)`: the fraction of the `2^m`
step sequences of length `m` ending at `y`. -/
noncomputable def srwProb (m : ℕ) (y : ℤ) : ℝ :=
  ((2 : ℝ) ^ m)⁻¹ * ((Finset.univ.filter fun s : Fin m → Bool => walkPos s m = y).card : ℝ)

/-- `p_k(i, x) = ∏_{j=1}^k p(i_j - i_{j-1}, x_j - x_{j-1})`, `i_0 = x_0 = 0` (used for
increasing `i`). -/
noncomputable def pathKernel {k : ℕ} (i : Fin k → ℕ) (x : Fin k → ℤ) : ℝ :=
  ∏ j : Fin k,
    srwProb (i j - (Fin.cons 0 i : Fin (k + 1) → ℕ) j.castSucc)
      (x j - (Fin.cons 0 x : Fin (k + 1) → ℤ) j.castSucc)

/-- `[y]_i`: the integer of the parity of `i` closest to `y` (ties, a null set, are broken
upwards). -/
noncomputable def parityRound (i : ℕ) (y : ℝ) : ℤ :=
  2 * round ((y - ((i % 2 : ℕ) : ℝ)) / 2) + ((i % 2 : ℕ) : ℤ)

/-- `p̄_k(i, y) = 2^{-k} p_k(i, [y]_i)`, `([y]_i)_j = [y_j]_{i_j}`. -/
noncomputable def pathKernelBar {k : ℕ} (i : Fin k → ℕ) (y : Fin k → ℝ) : ℝ :=
  ((2 : ℝ) ^ k)⁻¹ * pathKernel i (fun j => parityRound (i j) (y j))

/-- `i ∈ D_k^n`, i.e. `1 ≤ i_1 < i_2 < ⋯ < i_k ≤ n`. -/
def InDiscreteSimplex {k : ℕ} (n : ℕ) (i : Fin k → ℕ) : Prop :=
  (∀ j, 1 ≤ i j ∧ i j ≤ n) ∧ StrictMono i

open scoped Classical in
/-- Definition 5.1: `p_k^n(t, x) = p̄_k(⌈nt⌉, x√n) 1{⌈nt⌉ ∈ D_k^n}` on `[0,1]^k × ℝ^k`
(for `k = 0` this is the constant `1`). -/
noncomputable def discreteKernel (n k : ℕ) (z : Fin k → ℝ × ℝ) : ℝ :=
  if InDiscreteSimplex n (fun j => ⌈(n : ℝ) * (z j).1⌉₊) then
    pathKernelBar (fun j => ⌈(n : ℝ) * (z j).1⌉₊) (fun j => (z j).2 * Real.sqrt n)
  else 0

open scoped Classical in
/-- `p_k^n` as an element of `L²([0,1]^k × ℝ^k)` (junk `0` only if `p_k^n ∉ L²`). -/
noncomputable def discreteKernelLp (n k : ℕ) : Lp ℝ 2 (kernelMeasure k) :=
  if h : MemLp (discreteKernel n k) 2 (kernelMeasure k) then h.toLp _ else 0

end IntermediateDisorder.PointToLine


