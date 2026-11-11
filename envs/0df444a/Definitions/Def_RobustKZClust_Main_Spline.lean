-- Prove2me | Definitions.Def_RobustKZClust_Main_Spline
-- name    : RobustKZClust_Main_Spline
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T05:10:59.28521+00:00
-- url     : https://prove2.me/theorems/901845d1-276e-44a9-9f4d-3a10264421a9
-- title:
--   Sums of uniforms: β_n, the probability vectors f_n(t) ∈ ℓ_1(ℤ), ℓ_1 norms, products F^d and truncations τ^r
-- statement:
--   Let $V_1,\dots,V_n$ be independent and uniform on $[0,1)$. For $t\in\mathbb R$ and an integer $n\ge0$,
--
--   $$\beta_n(t)=\Pr\Bigl[t-1<\sum_{j\le n}V_j\le t\Bigr],\qquad f_n(t)=\Bigl(\Pr\Bigl[\Bigl\lfloor t-\sum_{j\le n}V_j\Bigr\rfloor=v\Bigr]\Bigr)_{v\in\mathbb Z}\in\ell_1(\mathbb Z).$$
--
--   A vector $b:\mathbb Z\to\mathbb R$ (or $\mathbb Z^d\to\mathbb R$) is in $\ell_1$ if $\sum|b_v|<\infty$, and $\|b\|_1=\sum_v|b_v|$.
--
--   For $f:\mathbb R\to\ell_1(\mathbb Z)$ and $x\in\mathbb R^d$, the tensor product is $F^d(x)=\bigotimes_{j=1}^d f(x_j)$, that is $(F^d(x))_v=\prod_j(f(x_j))_{v_j}$ for $v\in\mathbb Z^d$.
--
--   Given coefficient vectors $b_0(c),b_1(c),\dots\in\ell_1(\mathbb Z)$ for $c\in\mathbb R$, and $c,u\in\mathbb R^d$, the homogeneous degree-$j$ part of the expansion of $\bigotimes_{i=1}^d\bigl(\sum_{k=0}^{r-1}b_k(c_i)u_i^k\bigr)$ is
--   $$\tau^{[j]}_r(c,u)_v=\sum_{\alpha\in\{0,\dots,r-1\}^d,\ |\alpha|=j}\ \prod_{i=1}^d\bigl(b_{\alpha_i}(c_i)\bigr)_{v_i}u_i^{\alpha_i}.$$
--   The truncation $\tau^r(c,u)=\sum_{j<r}\tau^{[j]}_r(c,u)$ keeps the terms of total degree less than $r$ in $u$.
--
--   These are the one-dimensional assignment probabilities of the hierarchical Lipschitz assignment of §4 ($F_\ell(s_\ell v,x)=\beta_z(x/s_\ell-v)$) and the objects of its tensorization.
--
--   **Formalization Note.** The law of $(V_1,\dots,V_n)$ is Lebesgue measure restricted to the cube $[0,1)^n$. `l1norm` is the `tsum` of absolute values, used only on vectors that are in $\ell_1$.
-- source:
--   Guo, Jiang, Krauthgamer, Xie, Zhou, Adversarially Robust Streaming Algorithms for (k, z)-Clustering, STOC 2027 submission (manuscript sha256 7d9aadba…), pp. 16–18 §4.1 (V_j, β_n, f_n), pp. 21–22 §4.2 (F^d, τ^r, τ^{[j]}_r)

import Mathlib

namespace RobustKZClust.Main

/-! The one-dimensional objects of §4.1 (pp. 16–18) and the tensor products of §4.2 (pp. 21–22):
sums of independent uniforms on `[0, 1)`, `β_n`, the probability vectors `f_n(t) ∈ ℓ_1(ℤ)`,
the `ℓ_1` norm, the products `F^d`, and the total-degree truncations `τ^r`. -/

open MeasureTheory

/-- The joint law of `V_1, …, V_n`, independent and uniform on `[0, 1)`: Lebesgue measure on the
cube `[0, 1)^n`. -/
noncomputable def unifCube (n : ℕ) : Measure (Fin n → ℝ) :=
  volume.restrict (Set.pi Set.univ fun _ => Set.Ico (0 : ℝ) 1)

/-- `β_n(t) = Pr[t − 1 < V_1 + ⋯ + V_n ≤ t]`. -/
noncomputable def beta (n : ℕ) (t : ℝ) : ℝ :=
  (unifCube n {V | t - 1 < ∑ i, V i ∧ ∑ i, V i ≤ t}).toReal

/-- `f_n(t) = (Pr[⌊t − (V_1 + ⋯ + V_n)⌋ = v])_{v ∈ ℤ}`. -/
noncomputable def fvec (n : ℕ) (t : ℝ) : ℤ → ℝ :=
  fun v => (unifCube n {V | ⌊t - ∑ i, V i⌋ = v}).toReal

/-- Membership in `ℓ_1`: absolutely summable. -/
def InL1 {ι : Type} (f : ι → ℝ) : Prop := Summable fun i => |f i|

/-- The `ℓ_1` norm `∑_i |f_i|` (used only on vectors in `ℓ_1`). -/
noncomputable def l1norm {ι : Type} (f : ι → ℝ) : ℝ := ∑' i, |f i|

/-- `F^d(x) = ⊗_{j=1}^d f(x_j)`, i.e. `(F^d(x))_v = ∏_j (f(x_j))_{v_j}` for `v ∈ ℤ^d`. -/
def tensorVec {d : ℕ} (f : ℝ → ℤ → ℝ) (x : Fin d → ℝ) : (Fin d → ℤ) → ℝ :=
  fun v => ∏ j, f (x j) (v j)

/-- The degree multi-indices `α ∈ {0, …, r − 1}^d` with total degree `|α| = deg`. -/
def degIdx (d r deg : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset fun _ : Fin d => Finset.range r).filter fun α => ∑ j, α j = deg

/-- The homogeneous degree-`deg` part `τ^{[deg]}_r(c, u)` of the expansion of
`⊗_{j=1}^d (∑_{k=0}^{r−1} b_k(c_j) u_j^k)`:
`(τ^{[deg]}_r(c, u))_v = ∑_{α ∈ {0,…,r−1}^d, |α| = deg} ∏_j (b_{α_j}(c_j))_{v_j} u_j^{α_j}`. -/
def tauHom {d : ℕ} (b : ℕ → ℝ → ℤ → ℝ) (r deg : ℕ) (c u : Fin d → ℝ) : (Fin d → ℤ) → ℝ :=
  fun v => ∑ α ∈ degIdx d r deg, ∏ j, b (α j) (c j) (v j) * u j ^ α j

/-- `τ^r(c, u)`: the expansion of `⊗_{j=1}^d (∑_{k=0}^{r−1} b_k(c_j) u_j^k)` with only the
terms of total degree less than `r` in `u` retained. -/
def tau {d : ℕ} (b : ℕ → ℝ → ℤ → ℝ) (r : ℕ) (c u : Fin d → ℝ) : (Fin d → ℤ) → ℝ :=
  fun v => ∑ deg ∈ Finset.range r, tauHom b r deg c u v

end RobustKZClust.Main


