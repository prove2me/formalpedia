-- Prove2me | Definitions.Def_IntMul_HvdH_Resampling
-- name    : IntMul_HvdH_Resampling
-- status  : Definition
-- author  : @avi
-- created : 2026-10-08T17:33:28.805859+00:00
-- url     : https://prove2.me/theorems/759f7f70-e488-4465-984f-fde7903da6e1
-- title:
--   Gaussian resampling maps $\mathcal S,\mathcal T,\mathcal P_s,\mathcal P_t,\mathcal C,\mathcal D,\mathcal N,\mathcal E$ of Harvey–van der Hoeven
-- statement:
--   This file defines the linear maps of §4.1–§4.2 of Harvey–van der Hoeven used in **Gaussian resampling**. For $n\ge1$, a vector $u\in\mathbb C^n$ is indexed by $\mathbb Z/n\mathbb Z$, so $u_j$ means $u_{j\bmod n}$ for every integer $j$. Vectors carry the supremum norm $\|u\|=\max_j|u_j|$, and linear maps carry the corresponding operator norm.
--
--   Let $s,t\ge1$ and $\alpha\in\mathbb R$.
--
--   1. The DFT $\mathcal F_n:\mathbb C^n\to\mathbb C^n$, $(\mathcal F_nu)_j=\frac1n\sum_{k=0}^{n-1}e^{-2\pi ijk/n}u_k$.
--   2. The resampling maps $\mathcal S,\mathcal T:\mathbb C^s\to\mathbb C^t$, for $0\le k<t$:
--   $$(\mathcal Su)_k=\alpha^{-1}\sum_{j\in\mathbb Z}e^{-\pi\alpha^{-2}s^2(k/t-j/s)^2}u_j,\qquad(\mathcal Tu)_k=\sum_{j\in\mathbb Z}e^{-\pi\alpha^2t^2(k/t-j/s)^2}u_j.$$
--   3. The permutations $(\mathcal P_su)_j=u_{tj}$ on $\mathbb C^s$ and $(\mathcal P_tu)_k=u_{-sk}$ on $\mathbb C^t$.
--   4. The nearest integer $[x]=\lfloor x+\tfrac12\rfloor$, and $\beta_\ell=t\ell/s-[t\ell/s]$.
--   5. The row-deleting map $\mathcal C:\mathbb C^t\to\mathbb C^s$, $(\mathcal Cu)_\ell=u_{[t\ell/s]}$, and the diagonal map $(\mathcal Du)_\ell=e^{\pi\alpha^2\beta_\ell^2}u_\ell$.
--   6. $\mathcal N=\mathcal C\mathcal T\mathcal D:\mathbb C^s\to\mathbb C^s$, $\mathcal E=\mathcal N-\mathcal I$, and $\theta=t/s-1$.
--
--   These maps relate a DFT of length $s$ to a DFT of length $t$. They underlie the resampling identity (Theorem 4.2) and the norm estimates (Lemmas 4.5, 4.6) that make power-of-two transforms usable for prime-length ones.
--
--   **Formalization Note** Each sum over $j\in\mathbb Z$ is written as a matrix acting on $\mathbb C^s$. The entry in row $k$, column $r$ is the lattice sum $\sum_{m\in\mathbb Z}g(k,r+ms)$ over the residue class of $r$, and it equals the source's sum for every $\alpha\ne0$. Row indices $k$ and $\ell$ are taken as their representatives in $\{0,\dots,t-1\}$ and $\{0,\dots,s-1\}$ respectively. The norm on vectors is Mathlib's supremum norm on `ZMod n → ℂ`.
-- source:
--   D. Harvey, J. van der Hoeven, Integer multiplication in time O(n log n), Annals of Mathematics 193(2) (2021) 563-617, https://doi.org/10.4007/annals.2021.193.2.4 (preprint https://hal.science/hal-02070778v2), §2.2 (supremum norm), §2.4 (DFT F_n), §2.6 (operator norm), §4 ([x]), §4.1 (S, T, P_s, P_t), §4.2 (theta, C, T', beta_l, D, N, E), pp. 9, 12, 23-28

import Mathlib

/-!
# Gaussian resampling maps of Harvey–van der Hoeven

D. Harvey, J. van der Hoeven, *Integer multiplication in time O(n log n)*,
Ann. of Math. 193 (2021), §2.2, §2.4, §4.1, §4.2.

Vectors in `ℂⁿ` are functions `ZMod n → ℂ`; this realizes the paper's convention that `u_j`
means `u_{j mod n}` for every integer `j`.  Mathlib's norm on `ZMod n → ℂ` is the supremum norm
`‖u‖ = max_j |u_j|` of §2.2, and the norm of a continuous linear map is the operator norm
of §2.6.  A sum `∑_{j ∈ ℤ} c_j u_j` is written as a matrix acting on `ℂ^s` by grouping the
indices `j` by their residue mod `s`.
-/

namespace IntMul.HvdH

open Complex Real

/-- The linear map `ℂ^s → ℂ^t` with matrix `A`. -/
noncomputable def toCLM {s t : ℕ} [NeZero s] [NeZero t] (A : Matrix (ZMod t) (ZMod s) ℂ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  LinearMap.toContinuousLinearMap (Matrix.toLin' A)

/-- The complex DFT `𝓕ₙ : ℂⁿ → ℂⁿ` (§2.4),
`(𝓕ₙ u)_j = (1/n) ∑_{k=0}^{n-1} e^{-2πijk/n} u_k`. -/
noncomputable def dft (n : ℕ) [NeZero n] : (ZMod n → ℂ) →L[ℂ] (ZMod n → ℂ) :=
  toCLM (Matrix.of fun j k : ZMod n =>
    (1 / (n : ℂ)) * exp (-2 * π * I * (j.val : ℂ) * (k.val : ℂ) / (n : ℂ)))

/-- Matrix of the map `u ↦ (∑_{j ∈ ℤ} g(k, j) · u_{j mod s})_{0 ≤ k < t}`: the entry in row `k`,
column `r` is `∑_{m ∈ ℤ} g(k, r + m s)`. -/
noncomputable def latticeMatrix (s t : ℕ) (g : ℕ → ℤ → ℝ) : Matrix (ZMod t) (ZMod s) ℂ :=
  Matrix.of fun k r => ((∑' m : ℤ, g k.val ((r.val : ℤ) + m * s) : ℝ) : ℂ)

/-- The resampling map `𝓢 : ℂ^s → ℂ^t` (§4.1),
`(𝓢u)_k = α⁻¹ ∑_{j∈ℤ} e^{-π α^{-2} s² (k/t - j/s)²} u_j` for `0 ≤ k < t`. -/
noncomputable def resS (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  toCLM (latticeMatrix s t fun k j =>
    α⁻¹ * Real.exp (-π * α⁻¹ ^ 2 * (s : ℝ) ^ 2 * ((k : ℝ) / t - (j : ℝ) / s) ^ 2))

/-- The resampling map `𝓣 : ℂ^s → ℂ^t` (§4.1),
`(𝓣u)_k = ∑_{j∈ℤ} e^{-π α² t² (k/t - j/s)²} u_j` for `0 ≤ k < t`. -/
noncomputable def resT (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  toCLM (latticeMatrix s t fun k j =>
    Real.exp (-π * α ^ 2 * (t : ℝ) ^ 2 * ((k : ℝ) / t - (j : ℝ) / s) ^ 2))

/-- The permutation map `𝓟_s : ℂ^s → ℂ^s`, `(𝓟_s u)_j = u_{tj}` (§4.1). -/
noncomputable def permS (s t : ℕ) [NeZero s] : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ fun j : ZMod s => (t : ZMod s) * j)

/-- The permutation map `𝓟_t : ℂ^t → ℂ^t`, `(𝓟_t u)_k = u_{-sk}` (§4.1). -/
noncomputable def permT (s t : ℕ) [NeZero t] : (ZMod t → ℂ) →L[ℂ] (ZMod t → ℂ) :=
  LinearMap.toContinuousLinearMap (LinearMap.funLeft ℂ ℂ fun k : ZMod t => -(s : ZMod t) * k)

/-- Nearest integer, rounding ties upward: `[x] = ⌊x + 1/2⌋` (§4). -/
noncomputable def nearest (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

/-- `β_ℓ = tℓ/s - [tℓ/s]` (§4.2). -/
noncomputable def beta (s t : ℕ) (ℓ : ℤ) : ℝ :=
  (t : ℝ) * ℓ / s - nearest ((t : ℝ) * ℓ / s)

/-- The row-deleting map `𝓒 : ℂ^t → ℂ^s`, `(𝓒u)_ℓ = u_{[tℓ/s]}` for `0 ≤ ℓ < s` (§4.2). -/
noncomputable def rowDel (s t : ℕ) [NeZero s] [NeZero t] : (ZMod t → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  toCLM (Matrix.of fun ℓ (k : ZMod t) =>
    if k = ((nearest ((t : ℝ) * (ℓ.val : ℕ) / s) : ℤ) : ZMod t) then (1 : ℂ) else 0)

/-- The diagonal map `𝓓 : ℂ^s → ℂ^s`, `(𝓓u)_ℓ = d_ℓ u_ℓ` with `d_ℓ = e^{π α² β_ℓ²}` (§4.2). -/
noncomputable def diagD (s t : ℕ) [NeZero s] (α : ℝ) : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  toCLM (Matrix.diagonal fun ℓ : ZMod s =>
    ((Real.exp (π * α ^ 2 * beta s t (ℓ.val : ℕ) ^ 2) : ℝ) : ℂ))

/-- `𝓝 = 𝓣′𝓓 = 𝓒𝓣𝓓 : ℂ^s → ℂ^s` (§4.2). -/
noncomputable def normN (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  (rowDel s t).comp ((resT s t α).comp (diagD s t α))

/-- `𝓔 = 𝓝 - 𝓘` (§4.2). -/
noncomputable def errE (s t : ℕ) [NeZero s] [NeZero t] (α : ℝ) :
    (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ) :=
  normN s t α - ContinuousLinearMap.id ℂ _

/-- `θ = t/s - 1` (§4.2). -/
noncomputable def theta (s t : ℕ) : ℝ := (t : ℝ) / s - 1

end IntMul.HvdH


