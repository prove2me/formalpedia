-- Prove2me | Definitions.Def_SparseNLO_Partial_Method
-- name    : SparseNLO_Partial_Method
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-07T15:12:51.997996+00:00
-- url     : https://prove2.me/theorems/cd94dcf8-b127-4e44-a210-153b04de2024
-- title:
--   The partial sparse-simplex method (box, p. 25) and the quantity A(x) of (4.8)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and $0<s<n$. Write $e_i$ for the $i$-th unit vector.
--
--   **The partial sparse-simplex method** (p. 25) starts from $x^0\in C_s$ and, for $k=0,1,2,\dots$, performs one of two steps.
--
--   1. If $\|x^k\|_0<s$ (the greedy step): with $f_i=\min_{t\in\mathbb R}f(x^k+te_i)$ attained at $t_i$, pick $i_k\in\operatorname{argmin}_i f_i$. If $f_{i_k}<f(x^k)$, set $x^{k+1}=x^k+t_{i_k}e_{i_k}$; otherwise STOP.
--   2. If $\|x^k\|_0=s$: choose
--      - $i^1_k\in\operatorname{argmin}\{f_i : i\in I_1(x^k)\}$ and $T^1_k\in\operatorname{argmin}_t f(x^k+te_{i^1_k})$;
--      - $i^2_k\in\operatorname{argmax}\{|\nabla_i f(x^k)| : i\in I_0(x^k)\}$;
--      - $m_k\in\operatorname{argmin}\{|x^k_i| : i\in I_1(x^k)\}$ and $T^2_k\in\operatorname{argmin}_t f(x^k-x^k_{m_k}e_{m_k}+te_{i^2_k})$;
--
--      let $D^1_k=f(x^k+T^1_ke_{i^1_k})$ and $D^2_k=f(x^k-x^k_{m_k}e_{m_k}+T^2_ke_{i^2_k})$. If $D^1_k<D^2_k$ set $x^{k+1}=x^k+T^1_ke_{i^1_k}$; else set $x^{k+1}=x^k-x^k_{m_k}e_{m_k}+T^2_ke_{i^2_k}$.
--
--   In words: when the iterate is saturated, the method either re-optimizes the best support coordinate, or swaps the smallest support coordinate out for the off-support coordinate with the largest partial derivative, whichever gives the lower value. A sequence is a **run** of the method if it arises this way for some choice of all the minimizers and maximizers.
--
--   **The quantity $A(x)$** of (4.8) is, for a constant $L_2>0$,
--   $$A(x)=\max\Big\{\frac1{2L_2}\max_{i\in I_1(x)}(\nabla_if(x))^2,\ M_s(x)\Big[\max_{i\in I_0(x)}|\nabla_if(x)|-\max_{i\in I_1(x)}|\nabla_if(x)|-L_2M_s(x)\Big]\Big\}.$$
--   It lower-bounds the decrease $f(x^k)-f(x^{k+1})$ of a saturated step (Lemma 4.1).
--
--   **Correction of two misprints.** The printed box (arXiv v1) says "compute for every $i\in I_1(x^*)$" and "$i^1_k\in\operatorname{argmax}\{f_i : i\in I_1(x^k)\}$". There is no $x^*$ at that point of the algorithm, so the first is read as $I_1(x^k)$. The second is read as **argmin**: the prose on p. 24 chooses "the variable in the support of $x^k$ which causes the maximum decrease in function value", and the bound (4.10) in the proof of Lemma 4.1 requires the smallest $f_i$.
--
--   **Formalization Note** A STOP is modelled by the sequence staying at the stopping point, $x^{k+1}=x^k$. Each argmin is stated as an inequality against every competitor rather than computed; the selections $i^1_k,T^1_k$ are stated jointly ($f(x^k+T^1_ke_{i^1_k})\le f(x^k+te_i)$ for all $i\in I_1(x^k)$, $t\in\mathbb R$), which is the same as $i^1_k\in\operatorname{argmin}f_i$ with $T^1_k$ a minimizer. Only the selected minimizers are required to exist. The maxima over $I_1(x)$, $I_0(x)$ and over all indices are suprema in $\mathbb R_{\ge0}$ of $|\nabla_if(x)|$ (resp. $(\nabla_if(x))^2$), which equal the maxima on a nonempty index set and are $0$ on an empty one; $A$ is only used at points with $\|x\|_0=s$, where $0<s<n$ makes $I_1(x)$ and $I_0(x)$ nonempty. Indices are $0,\dots,n-1$.
-- source:
--   Beck, Eldar, Sparsity Constrained Nonlinear Optimization: Optimality Conditions and Algorithms, SIAM J. Optim. (2013), doi:10.1137/120869778 (source: arXiv:1203.4580v1), pp. 24–25, 30, §3.3 the partial sparse-simplex method (box, p. 25), (4.8)

import Mathlib
import Definitions.Def_SparseNLO_Partial_Setting

namespace SparseNLO.Partial

/-- `max_{i ∈ S} |vᵢ|`, computed as a supremum in `ℝ≥0` and cast to `ℝ`. It equals the maximum
of `|vᵢ|` over `S` when `S` is nonempty, and is `0` when `S = ∅`. -/
noncomputable def maxAbs {n : ℕ} (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((S.sup fun i => ‖v i‖₊ : NNReal) : ℝ)

/-- `max_{i ∈ S} (vᵢ)²`, computed as a supremum in `ℝ≥0` and cast to `ℝ`. It equals the maximum
of `(vᵢ)²` over `S` when `S` is nonempty, and is `0` when `S = ∅`. -/
noncomputable def maxSq {n : ℕ} (S : Finset (Fin n)) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ((S.sup fun i => ‖v i‖₊ ^ 2 : NNReal) : ℝ)

/-- The quantity `A(x)` of (4.8), p. 30, with the local Lipschitz constant `L2`:
`A(x) = max { (1/(2 L2)) max_{i∈I₁(x)} (∇ᵢf(x))²,
  M_s(x) [ max_{i∈I₀(x)} |∇ᵢf(x)| − max_{i∈I₁(x)} |∇ᵢf(x)| − L2 M_s(x) ] }`.
It is used only at points with `‖x‖₀ = s`, where (for `0 < s < n`) both `I₁(x)` and `I₀(x)` are
nonempty; elsewhere an empty maximum is read as `0`. -/
noncomputable def Aval {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℕ) (L2 : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  max (1 / (2 * L2) * maxSq (I1 x) (gradient f x))
    (Ms s x * (maxAbs (I0 x) (gradient f x) - maxAbs (I1 x) (gradient f x) - L2 * Ms s x))

/-- The general step of the partial sparse-simplex method (box, p. 25) when `‖xᵏ‖₀ < s`; it is
the greedy step: either (move) `xᵏ⁺¹ = xᵏ + t eᵢ` for some `i, t` with `f(xᵏ⁺¹) < f(xᵏ)` and
`f(xᵏ⁺¹) ≤ f(xᵏ + t' eⱼ)` for every `j` and `t'` (so `(i, t)` realizes `(i_k, t_{i_k})`), or
(STOP) `f(xᵏ) ≤ f(xᵏ + t' eⱼ)` for every `j, t'` (i.e. `f_{i_k} ≥ f(xᵏ)`), and then
`xᵏ⁺¹ = xᵏ`. A STOP is modelled by the sequence staying at the stopping point. -/
def StepBelow {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xk xk1 : EuclideanSpace ℝ (Fin n)) : Prop :=
  (∃ (i : Fin n) (t : ℝ), xk1 = xk + EuclideanSpace.single i t ∧ f xk1 < f xk ∧
      ∀ (j : Fin n) (t' : ℝ), f xk1 ≤ f (xk + EuclideanSpace.single j t')) ∨
  ((∀ (j : Fin n) (t' : ℝ), f xk ≤ f (xk + EuclideanSpace.single j t')) ∧ xk1 = xk)

/-- The general step of the partial sparse-simplex method (box, p. 25) when `‖xᵏ‖₀ = s`, with
its selections `i¹ = i¹_k`, `T1 = T¹_k`, `i² = i²_k`, `m = m_k`, `T2 = T²_k`:

* `i¹ ∈ I₁(xᵏ)` and `T1` jointly minimize `f(xᵏ + t eᵢ)` over `i ∈ I₁(xᵏ)` and `t ∈ ℝ`
  (`i¹_k ∈ argmin{fᵢ : i ∈ I₁(xᵏ)}`, `T¹_k ∈ argmin_t f(xᵏ + t e_{i¹_k})`);
* `i² ∈ argmax{|∇ᵢf(xᵏ)| : i ∈ I₀(xᵏ)}`;
* `m ∈ argmin{|xᵏᵢ| : i ∈ I₁(xᵏ)}`;
* `T2 ∈ argmin_t f(xᵏ − xᵏ_m e_m + t e_{i²})`;
* with `D¹ = f(xᵏ + T1 e_{i¹})` and `D² = f(xᵏ − xᵏ_m e_m + T2 e_{i²})`: if `D¹ < D²` then
  `xᵏ⁺¹ = xᵏ + T1 e_{i¹}`, else `xᵏ⁺¹ = xᵏ − xᵏ_m e_m + T2 e_{i²}`.

The printed box (arXiv v1) reads "compute for every `i ∈ I₁(x*)`" and
"`i¹_k ∈ argmax{fᵢ : i ∈ I₁(xᵏ)}`"; both are typos, corrected here to `I₁(xᵏ)` and `argmin`
(the prose on p. 24 selects "the variable in the support of xᵏ which causes the maximum decrease
in function value", and (4.10) needs it). -/
def StepAt {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (xk xk1 : EuclideanSpace ℝ (Fin n)) (i1 : Fin n) (T1 : ℝ) (i2 m : Fin n) (T2 : ℝ) :
    Prop :=
  i1 ∈ I1 xk ∧
  (∀ i ∈ I1 xk, ∀ t : ℝ,
      f (xk + EuclideanSpace.single i1 T1) ≤ f (xk + EuclideanSpace.single i t)) ∧
  i2 ∈ I0 xk ∧
  (∀ i ∈ I0 xk, |gradient f xk i| ≤ |gradient f xk i2|) ∧
  m ∈ I1 xk ∧
  (∀ i ∈ I1 xk, |xk m| ≤ |xk i|) ∧
  (∀ t : ℝ, f (xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 T2) ≤
      f (xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 t)) ∧
  (f (xk + EuclideanSpace.single i1 T1) <
      f (xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 T2) →
    xk1 = xk + EuclideanSpace.single i1 T1) ∧
  (¬ f (xk + EuclideanSpace.single i1 T1) <
      f (xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 T2) →
    xk1 = xk - EuclideanSpace.single m (xk m) + EuclideanSpace.single i2 T2)

/-- A sequence `x : ℕ → ℝⁿ` generated by the partial sparse-simplex method (box, p. 25):
`x⁰ ∈ C_s`, every step from an iterate with `‖xᵏ‖₀ < s` is a `StepBelow`, and every step from an
iterate with `‖xᵏ‖₀ = s` is a `StepAt` for some choice of the selections
`i¹_k, T¹_k, i²_k, m_k, T²_k`. The selections are arbitrary minimizers/maximizers, so this
describes every run of the method. -/
def IsPartialRun {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (s : ℕ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  x 0 ∈ Cs n s ∧ ∀ k : ℕ,
    (l0 (x k) < s → StepBelow f (x k) (x (k + 1))) ∧
    (l0 (x k) = s → ∃ (i1 : Fin n) (T1 : ℝ) (i2 m : Fin n) (T2 : ℝ),
      StepAt f (x k) (x (k + 1)) i1 T1 i2 m T2)

end SparseNLO.Partial


