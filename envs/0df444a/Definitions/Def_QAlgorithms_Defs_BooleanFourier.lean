-- Prove2me | Definitions.Def_QAlgorithms_Defs_BooleanFourier
-- name    : QAlgorithms_Defs_BooleanFourier
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-13T17:52:14.722193+00:00
-- url     : https://prove2.me/theorems/4d070d37-bd5c-43cc-a596-c3dae970e580
-- title:
--   Fourier analysis on the Boolean cube over `F₂`, XOR-convolution matrices, matrix square roots
-- statement:
--   Fourier analysis on the Boolean cube over `F₂`, XOR-convolution matrices, matrix square roots
--
--   ### QAlgorithms.boolFourier
--
--   For $n \in \mathbb{N}$, a real function $f$ on $\mathbb{F}_2^n$ (tuples of length $n$ over $\mathbb{Z}/2$), and $S \in \mathbb{F}_2^n$, the value is
--   $$\hat f(S) = \frac{1}{2^n}\sum_{x\in\mathbb{F}_2^n} f(x)\,(-1)^{S\cdot x}.$$
--
--   - The dot product $S\cdot x = \sum_{i} S_i x_i$ is computed in $\mathbb{Z}/2$.
--   - That result is then read as the integer $0$ or $1$ in the exponent.
--
--   For $n=0$, there is a single point $x$, the exponent is $0$, and $\hat f(S) = f(x)$.
--
--   ### QAlgorithms.xorConvMatrix
--
--   For $k\in\mathbb{N}$ and a real function $g$ on $\mathbb{F}_2^k$, this is the real matrix indexed by $\mathbb{F}_2^k \times \mathbb{F}_2^k$ with entries
--   $$\big(\mathrm{xorConv}(g)\big)_{x,y} = g(x+y).$$
--   Here $x+y$ is coordinatewise addition mod $2$, i.e. bitwise XOR.
--
--   ### QAlgorithms.psdSqrt
--
--   For a finite type $\iota$ with decidable equality and a real matrix $A$ on $\iota\times\iota$, $\mathrm{psdSqrt}(A)$ is the result of applying the real square root to $A$ via the continuous functional calculus on real matrices. The result depends on whether $A$ is symmetric:
--
--   - **Symmetric $A$ ($A^\top = A$):** write $A = Q\,\mathrm{diag}(\lambda)\,Q^\top$. Then the result is $Q\,\mathrm{diag}(\sqrt{\lambda})\,Q^\top$. Here $\sqrt{\lambda} = 0$ for any negative eigenvalue $\lambda$, since Mathlib's real square root sends negatives to $0$.
--   - **Non-symmetric $A$:** the result is the zero matrix by convention.
--
--   No positive-semidefiniteness hypothesis is imposed.
--
--   ### QAlgorithms.weightPowFun
--
--   For natural numbers $m$ and $T$ and a real number $\beta$, this is the real function on $\mathbb{F}_2^m$ given by
--   $$z \mapsto \Big(1 - \frac{\beta\,|z|}{m}\Big)^{T},$$
--   where $|z|$ is the Hamming weight of $z$, i.e. the number of coordinates $z_i \ne 0$.
--
--   Edge cases:
--
--   - **$m = 0$:** division by zero is defined as $0$, so the function is constantly $1^T = 1$; the domain is a single point.
--   - **$T = 0$:** the function is constantly $1$.
--   - **$\beta$:** no constraint is imposed, so the base may be negative.
-- source:
--   https://github.com/shiy1022/lean-quantum-complexity/blob/main/algorithms/QAlgorithms/Defs/BooleanFourier.lean . Exact primary-source page locators are preserved in the declaration docstrings.

import Definitions.Def_QAlgorithms_Defs_Ensemble
/-!
# Fourier analysis on the Boolean cube over `F₂`, XOR-convolution matrices, matrix square roots
(shared definition layer)

S. Arunachalam, *Quantum Algorithms and Learning Theory* (PhD thesis, 2018), cited
"Arunachalam p.N", and S. Arunachalam, R. de Wolf, *A survey of quantum learning theory* (2017),
cited "survey p.N" (PDF pages).

Bit strings that are multiplied by `F₂`-matrices (generator matrices of linear codes, §7.3.4 and
§7.5) are vectors `Fin m → ZMod 2`; a subset `S ⊆ [m]` is identified with its indicator vector,
`S · x` is Mathlib's `dotProduct` over `ZMod 2`, `x + y` is the source's `x ⊕ y`, and `|z|` is
Mathlib's Hamming weight `hammingNorm z`.
-/

namespace QAlgorithms

/-- Survey p.5 (§2.2.2), Arunachalam p.161 (Claim 7.3.5) and p.172 (proof of Lemma 7.5.4): the
Fourier coefficient `f̂(S) = E_x[f(x) (−1)^{S·x}]` of `f : {0,1}^n → ℝ`, with `x` uniform over
`{0,1}^n`. -/
noncomputable def boolFourier {n : ℕ} (f : (Fin n → ZMod 2) → ℝ) (S : Fin n → ZMod 2) : ℝ :=
  ((2 : ℝ) ^ n)⁻¹ * ∑ x : Fin n → ZMod 2, f x * (-1 : ℝ) ^ (S ⬝ᵥ x).val

/-- Arunachalam p.171 (Claim 7.5.2), p.170 (Thm 7.5.1), survey p.13 (Thm 4.13): the real
`2^k × 2^k` matrix `P(x, y) = g(x + y)` (addition over `F₂`) of `g : {0,1}^k → ℝ`. With
`g = f ∘ M` it is the matrix `A` of Thm 7.5.1 / Thm 4.13. -/
def xorConvMatrix {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) :
    Matrix (Fin k → ZMod 2) (Fin k → ZMod 2) ℝ :=
  Matrix.of fun x y => g (x + y)

/-- Survey p.5 (§2.3, `√G`), Arunachalam p.171 (Claim 7.5.3, `√A`): the square root of a real
symmetric matrix, the spectral square root `cfc Real.sqrt A`. On a positive semidefinite `A` this
is its unique PSD square root (the sources' `√A`, used only for matrices the sources prove PSD);
junk: `0` for a non-symmetric `A`, and negative eigenvalues are sent to `0`. -/
noncomputable def psdSqrt {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  cfc Real.sqrt A

/-- Arunachalam p.170 (Thm 7.5.1), p.172 (Lemma 7.5.4), survey p.13 (Thm 4.13): the function
`f(z) = (1 − β |z| / m)^T` on `{0,1}^m`, with `|z|` the Hamming weight. `T` is a natural number
(a number of copies; Lemma 7.5.4's proof expands `f` binomially). At `m = 0` the quotient is `0`
(the sources have `m ≥ 10`). -/
noncomputable def weightPowFun (m : ℕ) (β : ℝ) (T : ℕ) : (Fin m → ZMod 2) → ℝ :=
  fun z => (1 - β * (hammingNorm z : ℝ) / (m : ℝ)) ^ T

/-! ### Sanity tests -/

example (n : ℕ) : boolFourier (fun _ : Fin n → ZMod 2 => (1 : ℝ)) 0 = 1 := by
  simp [boolFourier]

example (m : ℕ) (β : ℝ) (T : ℕ) : weightPowFun m β T 0 = 1 := by
  simp [weightPowFun]

example {k : ℕ} (g : (Fin k → ZMod 2) → ℝ) : (xorConvMatrix g).transpose = xorConvMatrix g := by
  ext x y
  simp [xorConvMatrix, add_comm]

example {ι : Type*} [Fintype ι] [DecidableEq ι] : psdSqrt (1 : Matrix ι ι ℝ) = 1 := by
  simp [psdSqrt, cfc_one]

end QAlgorithms


