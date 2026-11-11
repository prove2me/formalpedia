-- Prove2me | Definitions.Def_TensorPCAGlauber_OddK_Hypercube
-- name    : TensorPCAGlauber_OddK_Hypercube
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T14:52:51.052304+00:00
-- url     : https://prove2.me/theorems/67b9d0d0-a3c2-45a1-af0b-6dbf26322758
-- title:
--   Signed hypercube $\{\pm1\}^N$, uniform measure, correlation, Hamming balls, sign rounding, discrete derivatives and the discrete Sobolev norm $D^n$ (§3.1–3.2, Definition 3.5)
-- statement:
--   The signed Boolean hypercube is $\Omega_N=\{\pm1\}^N$ and $\pi$ is the uniform probability measure on it, with expectation $E_\pi[f]=2^{-N}\sum_{x\in\Omega_N}f(x)$. For a planted vector $x^\star\in\Omega_N$ the normalized correlation is $m(x)=N^{-1}\langle x^\star,x\rangle\in[-1,1]$. The Hamming distance is $d_H(x,y)=|\{i:x_i\ne y_i\}|$ and the normalized Hamming ball is $B_H(x,r)=\{y\in\Omega_N:N^{-1}d_H(x,y)\le r\}$. The sign rounding of $a\in\mathbb R^N$ is $\mathrm{sgn}(a)_i=+1$ if $a_i\ge0$ and $-1$ otherwise (so $\mathrm{sgn}(0)=+1$); the entrywise product of two configurations is $(x\odot y)_i=x_iy_i$, and $x^{\sim i}$ is $x$ with coordinate $i$ flipped.
--
--   The discrete partial derivative of $f:\Omega_N\to\mathbb R$ is
--   $$\partial_i f(x)=\tfrac12\big[f(x_{\neg i},x_i=+1)-f(x_{\neg i},x_i=-1)\big],$$
--   $\nabla_\Omega f=(\partial_1f,\dots,\partial_Nf)$, and the order-$\ell$ derivative tensor is $[\nabla^\ell_\Omega f(x)]_{i_1\dots i_\ell}=\partial_{i_1}\cdots\partial_{i_\ell}f(x)$. The operator norm of an order-$\ell$ tensor $T$ is $\|T\|_{op}=\sup_{x_1,\dots,x_\ell\in S^{N-1}}|T(x_1,\dots,x_\ell)|$ over Euclidean unit vectors, and the discrete Sobolev norm (Definition 3.5) is
--   $$\|f\|_{D^n}=\sum_{\ell=0}^nN^{\ell/2}\max_{x\in\Omega_N}\|\nabla^\ell_\Omega f(x)\|_{op},\qquad\|\nabla^0_\Omega f(x)\|=|f(x)|.$$
--
--   **Formalization Note.** `Cube N = Fin N → Bool`, `true` read as $+1$; `vec x` is the $\pm1$ vector. `eNorm` is the Euclidean norm and `supNorm` the max norm (Mathlib's norm on `Fin N → ℝ` is the sup norm, so neither is used implicitly). `tensorOpNorm` is a real `⨆` over tuples of unit vectors; it is bounded, and for $\ell=0$ it is $|T()|$, matching the convention.
-- source:
--   Das & Schramm, Averaged Annealed Markov Chains Achieve the Algorithmic Threshold for Tensor PCA, Part I: Glauber Dynamics, arXiv:2610.16705 (PDF of 2026-11-03, sha256 b1d9d241…), pp. 14–17 (PDF 17–20), §3, §3.1, Definition 3.5 and eq. (12)

import Mathlib

open MeasureTheory ProbabilityTheory

namespace TensorPCAGlauber.OddK

/-- The signed Boolean hypercube `Ω_N = {±1}^N` (Das–Schramm §3.1, p. 14), encoded as
`Fin N → Bool`: the Boolean `true` is the spin `+1` and `false` is the spin `−1`. -/
abbrev Cube (N : ℕ) := Fin N → Bool

/-- The real value `±1` of a spin: `true ↦ +1`, `false ↦ −1`. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- A configuration `x ∈ Ω_N` read as the vector `x ∈ ℝ^N` with entries `±1`. -/
def vec {N : ℕ} (x : Cube N) : Fin N → ℝ := fun i => spin (x i)

/-- The Euclidean inner product `⟨u, v⟩ = ∑_i u_i v_i` on `ℝ^N`. -/
def dot {N : ℕ} (u v : Fin N → ℝ) : ℝ := ∑ i, u i * v i

/-- The Euclidean norm `‖u‖ = (∑_i u_i²)^{1/2}` on `ℝ^N` (not Mathlib's sup norm on `Fin N → ℝ`). -/
noncomputable def eNorm {N : ℕ} (u : Fin N → ℝ) : ℝ := Real.sqrt (∑ i, u i ^ 2)

/-- The sup norm `‖u‖_∞ = max_i |u_i|` (`0` when `N = 0`). -/
noncomputable def supNorm {N : ℕ} (u : Fin N → ℝ) : ℝ := ⨆ i, |u i|

/-- The uniform probability measure `π` on `Ω_N`. -/
noncomputable def piMeasure (N : ℕ) : Measure (Cube N) := uniformOn Set.univ

instance (N : ℕ) : IsProbabilityMeasure (piMeasure N) := by
  unfold piMeasure
  infer_instance

/-- The expectation `E_π[f] = 2^{−N} ∑_{x ∈ Ω_N} f(x)` under the uniform measure `π`. -/
noncomputable def avg {N : ℕ} (f : Cube N → ℝ) : ℝ :=
  (Fintype.card (Cube N) : ℝ)⁻¹ * ∑ x, f x

/-- The normalized correlation with the planted vector, `m(x) = N^{−1}⟨x⋆, x⟩` (eq. (4)). -/
noncomputable def corr {N : ℕ} (xstar x : Cube N) : ℝ := (N : ℝ)⁻¹ * dot (vec xstar) (vec x)

/-- Hamming distance `d_H(x, y) = |{i : x_i ≠ y_i}|`. -/
def hamming {N : ℕ} (x y : Cube N) : ℕ := (Finset.univ.filter fun i => x i ≠ y i).card

/-- The normalized Hamming ball `B_H(x, r) = {y ∈ Ω_N : N^{−1} d_H(x, y) ≤ r}` (p. 15). -/
def hammingBall {N : ℕ} (x : Cube N) (r : ℝ) : Set (Cube N) :=
  {y | (N : ℝ)⁻¹ * (hamming x y : ℝ) ≤ r}

/-- Sign rounding (p. 14): `sgn(a)_i = +1` if `a_i ≥ 0` and `−1` otherwise (so `sgn 0 = +1`). -/
noncomputable def sgnCube {N : ℕ} (a : Fin N → ℝ) : Cube N := fun i => decide (0 ≤ a i)

/-- The entrywise (Hadamard) product `x ⊙ y` of two configurations: the spin of `(x ⊙ y)_i` is
`x_i y_i`, i.e. `+1` exactly when `x_i = y_i`. -/
def hadamard {N : ℕ} (x y : Cube N) : Cube N := fun i => (x i == y i)

/-- `x^{∼i}`: the configuration `x` with its `i`-th coordinate flipped. -/
def flipAt {N : ℕ} (x : Cube N) (i : Fin N) : Cube N := Function.update x i (!x i)

/-- The discrete partial derivative (p. 15):
`∂_i f(x) = ½[f(x_{¬i}, x_i = +1) − f(x_{¬i}, x_i = −1)]`. -/
noncomputable def pderiv {N : ℕ} (i : Fin N) (f : Cube N → ℝ) (x : Cube N) : ℝ :=
  (f (Function.update x i true) - f (Function.update x i false)) / 2

/-- The discrete gradient `∇_Ω f(x) = (∂_1 f(x), …, ∂_N f(x)) ∈ ℝ^N`. -/
noncomputable def grad {N : ℕ} (f : Cube N → ℝ) (x : Cube N) : Fin N → ℝ :=
  fun i => pderiv i f x

/-- The discrete derivative tensor of order `ℓ` (p. 15), entrywise:
`[∇^ℓ_Ω f(x)]_{i_1,…,i_ℓ} = ∂_{i_1} ⋯ ∂_{i_ℓ} f(x)`; `∇^0_Ω f = f`. -/
noncomputable def iterDeriv {N : ℕ} : (l : ℕ) → (Fin l → Fin N) → (Cube N → ℝ) → Cube N → ℝ
  | 0, _, f => f
  | l + 1, idx, f => pderiv (idx 0) (iterDeriv l (Fin.tail idx) f)

/-- The operator norm of an order-`ℓ` tensor `T` on `ℝ^N` (p. 14):
`‖T‖_op = sup_{x_1,…,x_ℓ ∈ S^{N−1}} |T(x_1,…,x_ℓ)|`, the sup over Euclidean unit vectors. For
`ℓ = 0` the tensor is a scalar `T()` and the value is `|T()|`. -/
noncomputable def tensorOpNorm {N l : ℕ} (T : (Fin l → Fin N) → ℝ) : ℝ :=
  ⨆ v : Fin l → {u : Fin N → ℝ // ∑ i, u i ^ 2 = 1},
    |∑ idx : Fin l → Fin N, T idx * ∏ j, (v j).1 (idx j)|

/-- The discrete Sobolev norm (Definition 3.5, eq. (12)):
`‖f‖_{D^n} = ∑_{ℓ=0}^n N^{ℓ/2} max_{x ∈ Ω_N} ‖∇^ℓ_Ω f(x)‖_op`, with `‖∇^0_Ω f(x)‖ = |f(x)|`. -/
noncomputable def sobolevNorm {N : ℕ} (n : ℕ) (f : Cube N → ℝ) : ℝ :=
  ∑ l ∈ Finset.range (n + 1),
    (N : ℝ) ^ ((l : ℝ) / 2) * ⨆ x : Cube N, tensorOpNorm (fun idx => iterDeriv l idx f x)

end TensorPCAGlauber.OddK


