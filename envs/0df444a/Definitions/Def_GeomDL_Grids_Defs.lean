-- Prove2me | Definitions.Def_GeomDL_Grids_Defs
-- name    : GeomDL_Grids_Defs
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T13:40:36.575985+00:00
-- url     : https://prove2.me/theorems/d3ba1c65-bab7-45e1-b3c2-3a319ccadbfa
-- title:
--   §4.2, pp. 36–38 — circular convolution x ⋆ θ, the right shift S = C(0, 1, 0, …, 0), the Fourier basis φ_k and the Fourier matrix Φ
-- statement:
--   This file fixes the objects of the "Circulant matrices and Convolutions" and "Derivation of the discrete Fourier transform" paragraphs of §4.2. Throughout, $n \ge 1$ and the one-dimensional periodic grid (the ring graph) has nodes $\mathbb Z_n = \{0, 1, \dots, n-1\}$ with arithmetic modulo $n$. A signal on the grid is a vector $x = (x_0, \dots, x_{n-1})$ with entries in a commutative ring $R$ (for instance $\mathbb R$).
--
--   1. **Circulant matrix.** For $\theta = (\theta_0, \dots, \theta_{n-1})$, the circulant matrix is $C(\theta) = (\theta_{u-v \bmod n})_{u,v}$. This is Mathlib's `Matrix.circulant` and is not redefined here.
--   2. **Circular convolution.** For signals $x$ and a filter $\theta$,
--   $$(x \star \theta)_u = \sum_{v=0}^{n-1} x_v\, \theta_{u - v \bmod n}.$$
--   3. **Shift operator.** The (right) shift $S$ is the circulant matrix of $\theta = (0, 1, 0, \dots, 0)^\top$, i.e. of the indicator of the index $1$:
--   $$S = C(e_1), \qquad S_{uv} = \begin{cases} 1 & u - v \equiv 1 \pmod n,\\ 0 & \text{otherwise.}\end{cases}$$
--   4. **Fourier basis.** Over $\mathbb C$, for $k \in \{0, \dots, n-1\}$, the $k$-th discrete Fourier basis vector has entries
--   $$\varphi_k(u) = \frac{1}{\sqrt n}\, e^{2\pi i k u / n}, \qquad u = 0, 1, \dots, n-1.$$
--   5. **Fourier matrix.** $\Phi = (\varphi_0, \dots, \varphi_{n-1})$ is the $n \times n$ complex matrix whose $k$-th column is $\varphi_k$, so $\Phi_{uk} = \varphi_k(u)$.
--
--   These are the objects every statement of the mission is about: circulant matrices are the convolution operators, $S$ generates the translations of the grid, and $\Phi$ is the change of coordinates to the Fourier domain.
--
--   **Formalization Note** Indices are elements of `ZMod n` with `[NeZero n]` (so `n ≥ 1` and the index type is finite). In $\varphi_k(u)$ the exponent uses the representatives $k, u \in \{0, \dots, n-1\}$ (`ZMod.val`). The shift is defined as `Matrix.circulant (Pi.single 1 1)`; for $n = 1$ the index $1$ equals $0$ and $S$ is the $1 \times 1$ identity, which is the one-position cyclic shift of a single entry.
-- source:
--   Bronstein et al., Geometric Deep Learning (arXiv:2104.13478v2), §4.2, pp. 36–38: circulant matrix and convolution display p. 36; shift S p. 37; Fourier basis φ_k and Fourier matrix Φ p. 38

import Mathlib

namespace GeomDL.Grids

open Matrix

/-- Circular convolution, Bronstein et al. §4.2, p. 36:
`(x ⋆ θ)_u = Σ_{v=0}^{n-1} x_v θ_{u-v mod n}`. Signals on the ring `ℤ_n` are functions
`ZMod n → R`; indices are taken modulo `n` by the arithmetic of `ZMod n`. -/
def conv {R : Type*} [CommRing R] {n : ℕ} [NeZero n] (x θ : ZMod n → R) : ZMod n → R :=
  fun u => ∑ v : ZMod n, x v * θ (u - v)

/-- The (right) shift operator `S`, Bronstein et al. §4.2, p. 37: the circulant matrix
`C(θ) = (θ_{u-v mod n})` (Mathlib's `Matrix.circulant`) of `θ = (0, 1, 0, …, 0)`, i.e. of the
indicator of the index `1 : ZMod n`. Its entries are `S u v = 1` if `u - v = 1` and `0` otherwise. -/
def shift (R : Type*) [CommRing R] (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) R :=
  circulant (Pi.single (1 : ZMod n) (1 : R))

/-- The `k`-th discrete Fourier basis vector, Bronstein et al. §4.2, p. 38:
`φ_k(u) = n^{-1/2} e^{2πi k u / n}` for `k, u ∈ {0, …, n-1}` (represented by `ZMod.val`). -/
noncomputable def fourierVec (n : ℕ) [NeZero n] (k : ZMod n) : ZMod n → ℂ :=
  fun u => ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((k.val * u.val : ℕ) : ℂ) / (n : ℂ))

/-- The `n × n` Fourier matrix `Φ = (φ_0, …, φ_{n-1})`, Bronstein et al. §4.2, p. 38: its
`k`-th column is `φ_k`, so `Φ u k = φ_k(u)`. -/
noncomputable def fourierMatrix (n : ℕ) [NeZero n] : Matrix (ZMod n) (ZMod n) ℂ :=
  fun u k => fourierVec n k u

end GeomDL.Grids


