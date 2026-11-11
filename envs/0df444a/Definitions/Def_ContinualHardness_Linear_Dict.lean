-- Prove2me | Definitions.Def_ContinualHardness_Linear_Dict
-- name    : ContinualHardness_Linear_Dict
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:11:52.088432+00:00
-- url     : https://prove2.me/theorems/d7596b95-53cd-460a-9dba-1bc3e3f01580
-- title:
--   The dictatorship test Dict(ε, δ, T, M) and the parameters σ, τ of (7) and R, Q of (15)
-- statement:
--   Let $\varepsilon>0$, $T,M\ge1$ and $\varepsilon\le T$. Vectors $x\in\mathbb R^{[T]\times[M]}$ are written $x=(x_1,\dots,x_T)$ with blocks $x_t=(x_{t1},\dots,x_{tM})$. For a scale $\sigma>0$ and each $\hat t\in[T]$, the dataset $\tilde D_{\hat t}$ is the law of the following sample (`dictData ε σ T M t̂`):
--
--   1. independently for every $t\ne\hat t$ and $j\in[M]$, $x_{tj}=0$ with probability $1-\varepsilon/T$ and $x_{tj}$ uniform in $\{-\sigma,\sigma\}$ with probability $\varepsilon/T$;
--   2. $y$ uniform in $\{-1,1\}$;
--   3. $x_{\hat tj}=y$ for every $j\in[M]$;
--
--   output $(x,y)$. In Lean an outcome is $a:[T]\times[M]\to\{0,1,2\}$ ($0\mapsto0$, $1\mapsto\sigma$, $2\mapsto-\sigma$; `dictVal`), weighted by the product of the coordinate probabilities over the blocks $t\neq\hat t$ (`dictProb`, `dictWeight`) times $1/2$ for the label; coinciding points add their weights. The paper's test fixes, with $c_1$ the Berry–Esseen constant of Theorem A.1, Eq. (7):
--   $$\sigma=\frac1\delta\sqrt{\frac{8TM}{\pi\varepsilon}}\ (\texttt{dictSigma}),\qquad \tau=\frac{\delta}{4c_1}\sqrt{\frac{\varepsilon}{T}}\ (\texttt{dictTau}).$$
--   The block norm is $\|r_t\|_2=(\sum_j r_{tj}^2)^{1/2}$ (`blockNorm`). For the reduction, Eq. (15) sets, with $c_0$ the constant of Theorem A.3 and $q=4^R$,
--   $$R=\max\Big(1,\Big\lceil\frac1{c_0}\log_2\frac{2^{12}}{\delta^2\tau^4}\Big\rceil\Big)\ (\texttt{paramR}),\qquad Q=\max\Big(1,\Big\lceil\frac{2^{12}q^2}{\tau^4\delta^2}\Big\rceil\Big)\ (\texttt{paramQ}).$$
--
--   **Formalization Note.** (15) prints real expressions with "log"; they are rounded up (Theorem A.3 needs integers $Q,R\ge1$) and the logarithm is read in base 2, the only base for which the argument at the end of §A.5 closes. Outside $0<\varepsilon\le T$ the weights are still defined but are not probabilities; every statement about the test assumes $0<\varepsilon\le T$.
-- source:
--   Saket, Intractability of Continual Learning using Parametric Models with Unlimited Replay Buffer, STOC 2027 submission (manuscript sha256 86821df1…), p. 17, §A.2 and Eq. (7) (PDF p. 18); p. 19, Eq. (15) (PDF p. 20)

import Mathlib
import Definitions.Def_ContinualHardness_Linear_Dataset

namespace ContinualHardness.Linear

/-! # The dictatorship test `Dict(ε, δ, T, M)` (§A.2, Eq. (7)) and the parameters `R, Q` of (15)

Coordinates are indexed by `Fin T × Fin M`: `x (t, j)` is the paper's `x_{tj}`, and the block
`x_t = (x_{t1}, …, x_{tM})`. The test is built from a scale `σ > 0` (Eq. (7) fixes
`σ = dictSigma ε δ T M`). A random sample of `D̃_{t̂}` is: independently for each block `t ≠ t̂` and
each `j`, `x_{tj} = 0` with probability `1 − ε/T` and `x_{tj} = ±σ` with probability `ε/(2T)` each;
`y` uniform in `{−1, 1}`; `x_{t̂j} = y` for all `j`. The distribution is well defined (all
probabilities in `[0, 1]`) when `0 < ε ≤ T`. -/

/-- `σ := (1/δ) √(8TM/(πε))`, Eq. (7). -/
noncomputable def dictSigma (ε δ : ℝ) (T M : ℕ) : ℝ :=
  1 / δ * Real.sqrt (8 * T * M / (Real.pi * ε))

/-- `τ := (δ/(4c₁)) √(ε/T)`, Eq. (7), for the Berry–Esseen constant `c₁` of Theorem A.1. -/
noncomputable def dictTau (c₁ ε δ : ℝ) (T : ℕ) : ℝ :=
  δ / (4 * c₁) * Real.sqrt (ε / T)

/-- Value of one off-block coordinate in outcome `a ∈ {0, 1, 2}`: `0`, `σ` or `−σ`. -/
noncomputable def dictVal (σ : ℝ) (a : Fin 3) : ℝ :=
  if a = 0 then 0 else if a = 1 then σ else -σ

/-- Probability of outcome `a` of one off-block coordinate: `1 − ε/T` for `0`, `ε/(2T)` for each
of `±σ`. -/
noncomputable def dictProb (ε : ℝ) (T : ℕ) (a : Fin 3) : ℝ :=
  if a = 0 then 1 - ε / T else ε / (2 * T)

/-- The feature vector of the sample with off-block outcomes `a` and label `labelOf b`, for
`D̃_{t̂}`: the block `t̂` is constantly `y`, every other coordinate is `dictVal σ (a (t, j))`. -/
noncomputable def dictPoint (σ : ℝ) {T M : ℕ} (th : Fin T) (a : Fin T × Fin M → Fin 3) (b : Bool) :
    Fin T × Fin M → ℝ :=
  fun k => if k.1 = th then (labelOf b : ℝ) else dictVal σ (a k)

/-- The probability of the off-block outcomes `a` under `D̃_{t̂}`: the product of the coordinate
probabilities over the blocks `t ≠ t̂` (outcomes on the block `t̂` are pinned to `0`). -/
noncomputable def dictWeight (ε : ℝ) {T M : ℕ} (th : Fin T) (a : Fin T × Fin M → Fin 3) : ℝ :=
  ∏ k, if k.1 = th then (if a k = 0 then 1 else 0) else dictProb ε T (a k)

/-- The dataset `D̃_{t̂}` of the dictatorship test with parameters `ε`, scale `σ`, `T` blocks of
`M` coordinates: the law of `(x, y)` for the sampling procedure of §A.2 (a uniform label times the
product weight of the off-block outcomes; coinciding points add up). -/
noncomputable def dictData (ε σ : ℝ) (T M : ℕ) (th : Fin T) : WData (Fin T × Fin M) :=
  ∑ a : Fin T × Fin M → Fin 3, ∑ b : Bool,
    Finsupp.single (dictPoint σ th a b, labelOf b) (dictWeight ε th a / 2)

/-- The block norm `‖r_t‖₂ = (∑_j r_{tj}²)^{1/2}`. -/
noncomputable def blockNorm {T M : ℕ} (r : Fin T × Fin M → ℝ) (t : Fin T) : ℝ :=
  Real.sqrt (∑ j, r (t, j) ^ 2)

/-- `R := (1/c₀) log₂(2¹²/(δ²τ⁴))` of (15), rounded up to an integer and at least `1`. -/
noncomputable def paramR (c₀ δ τ : ℝ) : ℕ :=
  max 1 ⌈1 / c₀ * Real.logb 2 (2 ^ 12 / (δ ^ 2 * τ ^ 4))⌉₊

/-- `Q := 2¹² q²/(τ⁴δ²)` of (15) with `q = 4^R`, rounded up to an integer and at least `1`. -/
noncomputable def paramQ (δ τ : ℝ) (R : ℕ) : ℕ :=
  max 1 ⌈2 ^ 12 * ((4 : ℝ) ^ R) ^ 2 / (τ ^ 4 * δ ^ 2)⌉₊

end ContinualHardness.Linear


