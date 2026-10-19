-- Prove2me | Definitions.Def_QGradGAW_Smooth_Setting
-- name    : QGradGAW_Smooth_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-18T17:27:44.438778+00:00
-- url     : https://prove2.me/theorems/dfdab7c1-f507-46e5-bf62-4fbff339c6aa
-- title:
--   Definitions 4–7 and the algorithms of Theorems 21, 25 — a_ℓ^(2m), f_(2m), ∂_α f, analytic (5), ∇f, median of T runs of Algorithm 2, query count
-- statement:
--   This module fixes the objects of §2 and §5.2–5.4 of Gilyén, Arunachalam and Wiebe. Points of $\mathbb R^d$ are vectors $x=(x_1,\dots,x_d)$, and $\|x\|_\infty=\max_i |x_i|$.
--
--   1. **Central difference coefficients** (Definition 7). For $m\in\mathbb N$ and an integer $\ell$ with $\ell\neq0$,
--   $$a_\ell^{(2m)}=\frac{(-1)^{\ell-1}}{\ell}\,\frac{\binom{m}{|\ell|}}{\binom{m+|\ell|}{|\ell|}},\qquad a_0^{(2m)}=0 .$$
--   For $|\ell|>m$ the coefficient vanishes.
--   2. **Central difference approximation** (Definition 7, display (7)). For $F:\mathbb R^d\to\mathbb R$,
--   $$F_{(2m)}(y)=\sum_{\ell=-m}^{m} a_\ell^{(2m)}\,F(\ell y)\;\approx\;\nabla F(0)\cdot y .$$
--   3. **Partial derivatives along index sequences** (Definition 4). For $\alpha=(\alpha_1,\dots,\alpha_k)\in[d]^k$, $\partial_\alpha f(x)$ is the $k$-th derivative of $f$ at $x$ applied to the coordinate directions $e_{\alpha_1},\dots,e_{\alpha_k}$; and $y^\alpha=\prod_{j} y_{\alpha_j}$.
--   4. **Analyticity around a point** (Definition 5, centred at $x$). $f$ coincides with its multivariate Taylor series around $x$:
--   $$f(x+y)=\sum_{k=0}^{\infty}\sum_{\alpha\in[d]^k}\frac{y^\alpha\,\partial_\alpha f(x)}{k!}\qquad\text{for every }y\in\mathbb R^d .$$
--   Definition 5 ("$f$ is analytic") is the case $x=0$.
--   5. **Gradient** $\nabla f(x)=(\partial_1 f(x),\dots,\partial_d f(x))$, and the grid point $\hat x=(x^{(b_1)},\dots,x^{(b_d)})\in G_n^d$ labelled by $d$ registers of $n$ qubits (Definition 17).
--   6. **Median of $T$ runs of Algorithm 2** (proof of Theorem 21). Algorithm 2 is run $T$ times independently on an input $h$; each outcome $\kappa_t\in G_n^d$ is turned into an estimate $\mathrm{est}(\kappa_t)\in\mathbb R^d$, and the output is the coordinate-wise median (the entry of index $\lfloor T/2\rfloor$ of the sorted list, counting from $0$). The *failure probability* is the probability that this output is more than $\varepsilon$ away from a target $g$ in $\|\cdot\|_\infty$.
--   7. **The algorithm of Theorem 25.** With parameters $m,n_\varepsilon,n_M,T\in\mathbb N$ and $r>0$, put $n=n_\varepsilon+n_M$ and $g(y)=f(x+y)$, and run the median procedure with $h(z)=g_{(2m)}(rz)/2^{n_M}$ (so that Algorithm 2's oracle is $e^{2\pi i\,2^{n_\varepsilon} g_{(2m)}(rz)}$) and estimate $(2^{n_M}/r)\,k$ from the outcome $k\in G_n^d$. Its failure probability is measured against $\nabla f(x)$.
--   8. **Query count.** One run applies $e^{2\pi i\,2^{n_\varepsilon}\sum_\ell a_\ell^{(2m)} f(x+\ell r z)}$, whose factor for $\ell$ has total phase $2\pi 2^{n_\varepsilon}|a_\ell^{(2m)}|$ and costs $\lceil 2\pi 2^{n_\varepsilon}|a_\ell^{(2m)}|\rceil$ fractional phase queries $O_f^s$, $|s|\le1$ (Definitions 10–11 and display (25) with $S=2\pi2^{n_\varepsilon}$). The total over $T$ runs is
--   $$Q(m,n_\varepsilon,T)=T\sum_{\ell=-m}^{m}\big\lceil 2\pi\, 2^{n_\varepsilon}\,|a_\ell^{(2m)}|\big\rceil .$$
--
--   These are the objects in which Lemmas 20, 22, 34, 36 and Theorems 21, 24, 25 are stated.
--
--   **Formalization Note** $\mathbb R^d$ is `Fin d → ℝ`, whose norm is the sup norm $\|\cdot\|_\infty$. The grid $G_n$, its Fourier transform and Algorithm 2 up to the measurement are the published `QAlgorithms.gridPoint`, `QAlgorithms.gridQFT` and `QAlgorithms.gradientAlgState`; outcome probabilities are `QAlgorithms.prob`. $\partial_\alpha f$ is `iteratedFDeriv`, which is meaningful when $f$ is smooth; the theorems assume `ContDiff`. The median of an empty list is $0$ (only $T=0$). The coefficient $(-1)^{\ell-1}$ is an integer power.
-- source:
--   Gilyén, Arunachalam, Wiebe, Optimizing quantum optimization algorithms via faster quantum gradient computation, arXiv:1711.00465v3, pp. 11–12, Definitions 4, 5, 7 (displays (5), (7)); p. 17, Definitions 10–11; pp. 24–25, Definition 17, Algorithm 2; p. 27, proof of Theorem 21; pp. 29–30, proof of Theorem 25, display (25)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_GradientMethods

namespace QGradGAW.Smooth

open QAlgorithms

/-- Gilyén–Arunachalam–Wiebe, arXiv:1711.00465v3, p. 12, Definition 7: the central difference
coefficient `a_ℓ^(2m) = ((−1)^{ℓ−1}/ℓ) · binom(m,|ℓ|)/binom(m+|ℓ|,|ℓ|)` for `ℓ ≠ 0`, and
`a_0^(2m) = 0`. Only `ℓ ∈ {−m, …, m}` is used; for `|ℓ| > m` the value is `0` because
`binom(m, |ℓ|) = 0`. -/
noncomputable def centralCoeff (m : ℕ) (ℓ : ℤ) : ℝ :=
  if ℓ = 0 then 0
  else (-1 : ℝ) ^ (ℓ - 1) / (ℓ : ℝ) *
    ((m.choose ℓ.natAbs : ℝ) / ((m + ℓ.natAbs).choose ℓ.natAbs : ℝ))

/-- arXiv:1711.00465v3, p. 12, Definition 7, display (7): the degree-`2m` central difference
approximation `F_(2m)(y) = Σ_{ℓ=−m}^{m} a_ℓ^(2m) F(ℓ y)` of `∇F(0) · y` (the `ℓ = 0` term
vanishes since `a_0^(2m) = 0`). -/
noncomputable def centralDiff {d : ℕ} (m : ℕ) (F : (Fin d → ℝ) → ℝ) (y : Fin d → ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, centralCoeff m ℓ * F ((ℓ : ℝ) • y)

/-- arXiv:1711.00465v3, p. 11, Definition 4: the partial derivative `∂_α f(x)` along the
index-sequence `α ∈ [d]^k`, i.e. the `k`-th Fréchet derivative of `f` at `x` evaluated at the
coordinate directions `e_{α_1}, …, e_{α_k}`. (For `k = 0` it is `f x`.) -/
noncomputable def partialAlpha {d : ℕ} (f : (Fin d → ℝ) → ℝ) (k : ℕ) (α : Fin k → Fin d)
    (x : Fin d → ℝ) : ℝ :=
  iteratedFDeriv ℝ k f x (fun j => (Pi.single (α j) (1 : ℝ) : Fin d → ℝ))

/-- arXiv:1711.00465v3, p. 12, Definition 5 (display (5)), centred at the point `x`: `f`
coincides with its multivariate Taylor series around `x`,
`f(x + y) = Σ_{k=0}^∞ Σ_{α∈[d]^k} y^α ∂_α f(x)/k!` for every `y ∈ ℝ^d`, where
`y^α = Π_j y_{α_j}`. Definition 5 itself ("`f` is analytic") is `IsTaylorRep f 0`. -/
def IsTaylorRep {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Prop :=
  ∀ y : Fin d → ℝ, HasSum
    (fun k : ℕ => ∑ α : Fin k → Fin d, (∏ j, y (α j)) * partialAlpha f k α x / (k.factorial : ℝ))
    (f (x + y))

/-- The gradient `∇f(x) ∈ ℝ^d`, coordinate `i` being `∂_i f(x)`. -/
noncomputable def gradVec {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  fun i => fderiv ℝ f x (Pi.single i 1)

/-- arXiv:1711.00465v3, p. 24, Definition 17: the point `(x_1, …, x_d) ∈ G_n^d` labelled by
the `d` registers of `n` qubits each (`gridPoint` is the published `x^(b)` of Definition 17). -/
noncomputable def gridVec {d n : ℕ} (x : Fin d → Qubits n) : Fin d → ℝ :=
  fun i => gridPoint n (x i)

/-- The median of `T` numbers (proof of Theorem 21, p. 27): the entry of index `⌊T/2⌋` of the
sorted list (0-based), i.e. the median for odd `T` and the upper median for even `T`; `0` for
`T = 0`. -/
noncomputable def medianOf (T : ℕ) (v : Fin T → ℝ) : ℝ :=
  ((List.ofFn v).mergeSort (fun a b => decide (a ≤ b))).getD (T / 2) 0

/-- Proof of Theorem 21, p. 27 ("repeating the procedure … and taking the median
coordinate-wise"): run Algorithm 2 (`gradientAlgState d n h`, measured in the computational
basis) `T` times independently, run `t` giving the outcome `κ t ∈ (Qubits n)^d`; turn each
outcome into an estimate `est (κ t) ∈ ℝ^d`; output the coordinate-wise median. This is the
probability that the output is more than `ε` away from `g` in the sup norm `‖·‖∞` (the norm of
`Fin d → ℝ`). -/
noncomputable def medianFailProb (d n T : ℕ) (h : (Fin d → ℝ) → ℝ)
    (est : (Fin d → Qubits n) → Fin d → ℝ) (g : Fin d → ℝ) (ε : ℝ) : ℝ :=
  ∑ κ : Fin T → (Fin d → Qubits n),
    if ε < ‖(fun i => medianOf T (fun t => est (κ t) i)) - g‖ then
      ∏ t, prob (gradientAlgState d n h) (κ t)
    else 0

/-- The algorithm of Theorem 25 (proof pp. 29–30, via the proof of Theorem 21 on p. 27), with
parameters `m` (central-difference degree), `nε`, `nM` (so `n = nε + nM` qubits per register),
`T` (number of repetitions) and `r` (edge length of the grid): with `g(y) := f(x + y)`, run the
median procedure on `h(z) := g_(2m)(r z)/2^{nM}`, whose Algorithm 2 oracle is
`e^{2πi 2^{n} h(z)} = e^{2πi 2^{nε} g_(2m)(r z)}`, with estimate `(2^{nM}/r) · k` from the
outcome `k ∈ G_n^d`. The value is the probability that the output is more than `ε` away from
`∇f(x)` in `‖·‖∞`. -/
noncomputable def gradAlgFailProb (d m nε nM T : ℕ) (r : ℝ) (f : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) (ε : ℝ) : ℝ :=
  medianFailProb d (nε + nM) T
    (fun z => centralDiff m (fun u => f (x + u)) (r • z) / 2 ^ nM)
    (fun k i => (2 ^ nM / r) * gridPoint (nε + nM) (k i)) (gradVec f x) ε

/-- The number of (fractional) phase queries to `O_f` made by `gradAlgFailProb d m nε nM T r`
(Definitions 10–11, p. 17, and display (25), p. 30, with `S = 2π 2^{nε}`): each of the `T` runs
applies the oracle `e^{2πi 2^{nε} Σ_ℓ a_ℓ^(2m) f(x + ℓ r z)}` once, and its factor
`e^{i · 2π 2^{nε} a_ℓ^(2m) f(·)}` costs `⌈2π 2^{nε} |a_ℓ^(2m)|⌉` fractional queries
`O_f^s` with `|s| ≤ 1`. -/
noncomputable def queryCount (m nε T : ℕ) : ℕ :=
  T * ∑ ℓ ∈ Finset.Icc (-(m : ℤ)) m, ⌈2 * Real.pi * 2 ^ nε * |centralCoeff m ℓ|⌉₊

end QGradGAW.Smooth


