-- Prove2me | Definitions.Def_AgnosticImitate_Reduction_Algorithms
-- name    : AgnosticImitate_Reduction_Algorithms
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:24:47.193289+00:00
-- url     : https://prove2.me/theorems/8cecb07f-b57a-4a26-96e1-f495f2c9802e
-- title:
--   Algorithm 1, the Conditional Multiaccuracy Algorithm, Algorithm 2 and the composed reduction
-- statement:
--   Algorithm 1 (p. 5, PDF 7), Algorithm 2 and Theorems 1.2–1.3 (p. 6, PDF 8), proof of Theorem 1.2 (p. 17, PDF 19) and §1.4.3 (p. 12, PDF 14). Lean round $t$ is the paper's round $t+1$.
--
--   - **Algorithm 1** (Weighted Multiaccuracy): $p_0=0$ (`alg1Prev`); round $t$ asks the multiaccuracy oracle about label mean $m g+(1-m)p_{t-1}$ and receives $p_t$ (`alg1CallValid`); the output is $\frac1T\sum_{t=1}^T p_t$ (`alg1Output`).
--   - **Conditional Multiaccuracy Algorithm**: for $f:X\to\mathrm{Fin}\,M$, Algorithm 1 is run for $T$ rounds on each level set with $m=\mathbf 1\{f=v\}$, level after level (call $v T+t$ is round $t$ of level $v$; `cmaRun`, `cmaCallValid`), and the outputs are stitched: $p(x)=p^{(f(x))}(x)$ (`cmaStitch`).
--   - **$R_\gamma$** (`roundGrid`): nearest multiple of $\gamma$, $R_\gamma(v)=\gamma\,\mathrm{round}(v/\gamma)$ (ties up). **$\mathrm{sign}_\varepsilon$** (`signSoft`): $-1$ for $v\le-\varepsilon$, $1$ for $v\ge\varepsilon$, $v/\varepsilon$ otherwise.
--   - **Algorithm 2** (Agnostic Learning): $q_t=\sum_{s<t}s\,r_s/\binom t2$ with $q_1=0$ (`aggVals`, `alg2Agg`); round $t$ queries the conditional multiaccuracy oracle with the splitting function $R_\gamma\circ f\circ q_t$ (`alg2Split`, `alg2CallValid`: the answer is a predictor that is conditionally multiaccurate per level set for $D$); the output is $p=\sum_{t=1}^T t\,(f\circ q_t)/\binom{T+1}2$ (`alg2Output`).
--   - **Composed reduction** (`composedReduction n T₂ T₁`): Algorithm 2 with $f=\mathrm{sign}_{1/n}$ and $\gamma=1/n$ for $T_2$ rounds, each conditional multiaccuracy call implemented by $T_1$ rounds of Algorithm 1 on each of the $2n+1$ level sets of $R_\gamma\circ\mathrm{sign}_{1/n}\circ q_t$ (`levelIndex`, `stitchedList`); $T_2(2n+1)T_1$ calls, all queries and the output pointwise functions of earlier answers. ($\mathrm{sign}_\sigma=\mathbb E[\mathrm{sign}(N_\sigma(\cdot))]$ with $\mathrm{sign}(0)=0$, p. 21.)
-- source:
--   Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), Agnostic Learning by Imitating, STOC 2027 submission, SHA-256 225d86c2…0fb04, Algorithms 1–2 (pp. 5–6, PDF 7–8), p. 17 (PDF 19), §1.4.3 (p. 12, PDF 14)

import Mathlib
import Definitions.Def_AgnosticImitate_Reduction_Setting
import Definitions.Def_AgnosticImitate_Reduction_Oracle

noncomputable section
open MeasureTheory Classical

namespace AgnosticImitate.Reduction

/-! # Algorithm 1, the Conditional Multiaccuracy Algorithm, Algorithm 2 and the composed reduction

Casacuberta, Gopalan, Kanade, Reingold, Stavropoulos, Tankala (2026), *Agnostic Learning by
Imitating*, Algorithm 1 (p. 5, PDF 7), Algorithm 2 and Theorems 1.2–1.3 (p. 6, PDF 8), proof of
Theorem 1.2 (p. 17, PDF 19), §1.4.3 (p. 12, PDF 14).

Rounds are indexed from `0` in Lean: Lean round `t` is the paper's round `t + 1`, and the oracle
answer of Lean round `t` is `r t`. -/

variable {X : Type*} [MeasurableSpace X]

/-! ## Algorithm 1 (Weighted Multiaccuracy) -/

/-- Algorithm 1's `p_{t-1}` before Lean round `t`: `p_0 = 0`, and afterwards the previous answer. -/
def alg1Prev (r : ℕ → X → ℝ) (t : ℕ) : X → ℝ :=
  if t = 0 then 0 else r (t - 1)

/-- Algorithm 1's output after `T` rounds: `p = (1/T) Σ_{t=1}^T p_t`. -/
def alg1Output (r : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => (∑ t ∈ Finset.range T, r t x) / T

/-- Round `t` of Algorithm 1 with reweighting measure `m` is answered correctly by a
`(C, ε)`-multiaccuracy oracle: the answer `p_t` is a predictor that is `(C, ε)`-multiaccurate for
the labels `z` with `E[z | x, y] = m(x) · y + (1 - m(x)) · p_{t-1}(x)` (line 3). -/
def alg1CallValid (μ : Measure X) (C : Set (X → ℝ)) (g m : X → ℝ) (ε : ℝ) (t : ℕ)
    (r : ℕ → X → ℝ) : Prop :=
  IsPredictor (r t) ∧ IsMultiaccurate μ C (queryMean g m (alg1Prev r t)) (r t) ε

/-! ## The Conditional Multiaccuracy Algorithm (Theorem 1.2)

The splitting function is `f : X → Fin M` (`M = |V|` level sets). Algorithm 1 is run for `T`
rounds on each level set `v` with `m = 1{f = v}`, level after level: the calls of level `v` are
the calls `v * T + t`, `t < T`, so `M * T` calls in total. The answers are stitched:
`p(x) = p^{(f(x))}(x)`. -/

/-- The answers of the Algorithm 1 run on level set `i` inside a flat transcript. -/
def cmaRun (r : ℕ → X → ℝ) (T i : ℕ) : ℕ → X → ℝ :=
  fun t => r (i * T + t)

/-- The stitched predictor of the Conditional Multiaccuracy Algorithm. -/
def cmaStitch {M : ℕ} (f : X → Fin M) (r : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => alg1Output (cmaRun r T (f x)) T x

/-- Call `k` (level `k / T`, round `k % T`) of the Conditional Multiaccuracy Algorithm is
answered correctly by a `(C, ε)`-multiaccuracy oracle. -/
def cmaCallValid (μ : Measure X) (C : Set (X → ℝ)) (g : X → ℝ) {M : ℕ} (f : X → Fin M)
    (T : ℕ) (ε : ℝ) (k : ℕ) (r : ℕ → X → ℝ) : Prop :=
  alg1CallValid μ C g (levelInd (fun x => (f x : ℕ)) (k / T)) ε (k % T) (cmaRun r T (k / T))

/-! ## Algorithm 2 (Agnostic Learning) -/

/-- `R_γ`: rounding to the nearest multiple of `γ` (ties rounded up), `R_γ(v) = γ · round(v/γ)`. -/
def roundGrid (γ v : ℝ) : ℝ :=
  γ * round (v / γ)

/-- The soft threshold `sign_ε(v)`: `-1` if `v ≤ -ε`, `+1` if `v ≥ ε`, and `v/ε` otherwise
(p. 6). -/
def signSoft (ε v : ℝ) : ℝ :=
  if v ≤ -ε then -1 else if ε ≤ v then 1 else v / ε

/-- Linearly weighted average of values `v_0, …, v_{t-1}`:
`(Σ_{s<t} (s+1) v_s) / binom(t+1, 2)`, which is `0` for `t = 0`. -/
def aggVals (v : ℕ → ℝ) (t : ℕ) : ℝ :=
  (∑ s ∈ Finset.range t, ((s : ℝ) + 1) * v s) / ((t : ℝ) * ((t : ℝ) + 1) / 2)

/-- Algorithm 2, line 2: `q_t = Σ_{s<t} s · r_s / binom(t, 2)` (paper indexing), i.e. the query
aggregate before Lean round `t`; `q = 0` before the first round. -/
def alg2Agg (r : ℕ → X → ℝ) (t : ℕ) : X → ℝ :=
  fun x => aggVals (fun s => r s x) t

/-- Algorithm 2, line 3: the splitting function `R_γ ∘ f ∘ q_t` submitted in Lean round `t`. -/
def alg2Split (γ : ℝ) (f : ℝ → ℝ) (r : ℕ → X → ℝ) (t : ℕ) : X → ℝ :=
  fun x => roundGrid γ (f (alg2Agg r t x))

/-- Algorithm 2, line 4: the output `p = Σ_{t=1}^T t · (f ∘ q_t) / binom(T+1, 2)`. -/
def alg2Output (f : ℝ → ℝ) (r : ℕ → X → ℝ) (T : ℕ) : X → ℝ :=
  fun x => (∑ t ∈ Finset.range T, ((t : ℝ) + 1) * f (alg2Agg r t x)) /
    ((T : ℝ) * ((T : ℝ) + 1) / 2)

/-- Lean round `t` of Algorithm 2 is answered correctly by a `(C, ε')`-conditional multiaccuracy
oracle for `D`: the answer `r_t` is a predictor that is `(C, ε')`-conditionally multiaccurate
(per level set) with respect to `R_γ ∘ f ∘ q_t`. -/
def alg2CallValid (μ : Measure X) (C : Set (X → ℝ)) (g : X → ℝ) (γ : ℝ) (f : ℝ → ℝ) (ε' : ℝ)
    (t : ℕ) (r : ℕ → X → ℝ) : Prop :=
  IsPredictor (r t) ∧ IsCondMultiaccurate μ C g (alg2Split γ f r t) (r t) ε'

/-! ## The composed reduction (Theorem 1.1, first bullet; §1.4.3)

Algorithm 2 with `f = sign_{1/n}`, `γ = 1/n` and `T₂` rounds, each conditional multiaccuracy call
implemented by the Conditional Multiaccuracy Algorithm with `T₁` rounds of Algorithm 1 on each of
the `2n + 1` level sets of `R_γ ∘ sign_{1/n} ∘ q_t` (values `(i - n)/n`, `i = 0, …, 2n`). Call
`k` belongs to outer round `k / B`, level `(k % B) / T₁` and inner round `k % T₁`, where
`B = (2n + 1) T₁`. Everything is a pointwise function of earlier answer values. -/

/-- Index `i ∈ {0, …, 2n}` of the level `R_{1/n}(sign_{1/n}(q)) = (i - n)/n`. -/
def levelIndex (n : ℕ) (q : ℝ) : ℕ :=
  (round ((n : ℝ) * signSoft (1 / (n : ℝ)) q) + n).toNat

/-- The stitched answers `r_0(x), …, r_{s-1}(x)` of the first `s` outer rounds, from the flat
answer values `a`. -/
def stitchedList (n T₁ : ℕ) (a : ℕ → ℝ) : ℕ → List ℝ
  | 0 => []
  | s + 1 =>
    let prev := stitchedList n T₁ a s
    prev ++ [(∑ j ∈ Finset.range T₁,
      a (s * ((2 * n + 1) * T₁) + levelIndex n (aggVals (fun u => prev.getD u 0) s) * T₁ + j))
        / T₁]

/-- Extend a prefix of answer values by `0`. -/
def extendVals {k : ℕ} (a : Fin k → ℝ) : ℕ → ℝ :=
  fun u => if h : u < k then a ⟨u, h⟩ else 0

/-- The composed reduction with `T₂ (2n+1) T₁` calls to a multiaccuracy oracle. -/
def composedReduction (n T₂ T₁ : ℕ) : OracleReduction (T₂ * ((2 * n + 1) * T₁)) where
  mq := fun k a =>
    let B := (2 * n + 1) * T₁
    let st := stitchedList n T₁ (extendVals a) (k / B)
    if levelIndex n (aggVals (fun u => st.getD u 0) (k / B)) = (k % B) / T₁ then 1 else 0
  pq := fun k a => if k % T₁ = 0 then 0 else extendVals a (k - 1)
  out := fun a =>
    let st := stitchedList n T₁ (extendVals a) T₂
    (∑ t ∈ Finset.range T₂, ((t : ℝ) + 1) *
        signSoft (1 / (n : ℝ)) (aggVals (fun u => st.getD u 0) t)) /
      ((T₂ : ℝ) * ((T₂ : ℝ) + 1) / 2)

end AgnosticImitate.Reduction


