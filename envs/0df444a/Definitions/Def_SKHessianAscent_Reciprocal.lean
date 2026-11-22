-- Prove2me | Definitions.Def_SKHessianAscent_Reciprocal
-- name    : SKHessianAscent_Reciprocal
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-22T19:56:36.554648+00:00
-- url     : https://prove2.me/theorems/e4ee7263-0c91-42b4-af2f-a576f381669e
-- title:
--   The bounded extension $\phi$ of the reciprocal (5.1), the test functional $\Phi_{a,W,T}$ (5.2), and the projection $\Pi_{C_{\mathrm{op}}}$
-- statement:
--   **Matrix functions.** `matFun f Y` is the lift of a scalar function $f$ to a real symmetric matrix $Y$: the matrix with the same eigenvectors as $Y$ and eigenvalues transformed by $f$. `symPart X` is $(X+X^{\mathsf T})/2$.
--
--   **The cutoff (5.1).** For a fixed $\gamma=\gamma_Y>0$, `phi γ` is
--   $$\phi(y)=\Big[y+\gamma\Big(\frac{(\gamma-y)_+}{\gamma+y}\Big)^3\Big]^{-1},\qquad y>-\gamma ,$$
--   a bounded $C^2$ extension of $y\mapsto y^{-1}$, which it equals for $y\ge\gamma$. `cubePos` is $z\mapsto z_+^3$.
--
--   **The test functional (5.2).** For $\beta>0$, $a\in[0,1]$, a symmetric $A$, and diagonal matrices $W=\mathrm{diag}(w)$, $T=\mathrm{diag}(\tau)$, put $M=aI_n-\beta A$. `reciprocalArg β a w A` is $(I_n+WM)(I_n+MW)$ and `PhiFun β γ a w τ A` is
--   $$\Phi_{a,W,T}(A)=\mathrm{tr}_n\big[T\,\phi\big((I_n+WM)(I_n+MW)\big)\big].$$
--   `blockArg β a w A` is the $2n\times2n$ block matrix $\begin{pmatrix}0&I_n+WM\\I_n+MW&0\end{pmatrix}$ of (5.11), and `schatten2Block` is the normalized Schatten 2-norm of a $2n\times2n$ matrix.
--
--   **Theorem 5.4.** `opBallProj C A` is the metric projection $\Pi_C(A)$ of a symmetric matrix $A$ onto the closed convex set $\{M\text{ symmetric}:\|M\|_{\mathrm{op}}\le C\}$ with respect to $\|\cdot\|_{L^2}$, and `paramSet n` is the parameter set $\mathcal J=[0,1]\times\mathcal D_n([0,1])\times\{T\in\mathcal D_n(\mathbb R):\|T\|_{L^2}=1\}$.
--
--   These objects replace the weighted squared inverse $D(aI_n-\beta A+D)^{-2}D$ by a regularized quantity defined for every $A$, so that concentration and interpolation arguments can be run on the whole Gaussian space.
--
--   **Formalization Note** `matFun` is Mathlib's `Matrix.IsHermitian.cfc`, and is $0$ on non-symmetric matrices. `opBallProj` is defined as a nearest point in Frobenius norm, chosen by `Classical.choose` (unique for symmetric $A$), and is $0$ if none exists. `symPart` is used to express Fréchet differentiability on the space of symmetric matrices: a map $G$ on $\mathrm{Sym}_n(\mathbb R)$ is $C^k$ iff $G\circ\mathrm{symPart}$ is $C^k$ on all matrices, and for symmetric $Z,H$ the derivative $dG(Z)[H]$ is the derivative of $G\circ\mathrm{symPart}$ at $Z$ in the direction $H$.
-- source:
--   H. Lee, J. S. Sandhu, J. Shi, Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick model at β < 1, https://arxiv.org/abs/2609.30590, §5.1, equations (5.1)–(5.2), pp. 24–25; Proposition 5.2 (5.11), p. 26; Theorem 5.4, (5.20)–(5.21), p. 30

import Mathlib
import Definitions.Def_SKHessianAscent_Model

open scoped BigOperators

namespace SKHessianAscent

/-!
# The bounded extension `ϕ` of the reciprocal and the test functional `Φ_{a,W,T}`

H. Lee, J. S. Sandhu, J. Shi, *Potential Hessian Ascent IV: Sampling the Sherrington–Kirkpatrick
model at β < 1*, §5.1, equations (5.1), (5.2) (pp. 24–25); Proposition 5.2 (p. 26); Theorem 5.4,
(5.20)–(5.21) (p. 30).

**Formalization Note.**
* `matFun f Y` is the paper's lift of a scalar function to symmetric matrices ("the matrix with
  the same eigenvectors as `Y` but with eigenvalues transformed by `f`"): Mathlib's
  `Matrix.IsHermitian.cfc`. It is set to `0` when `Y` is not symmetric.
* `phi γ` is `ϕ` of (5.1) with cutoff `γ = γ_Y`, written with real division; the paper considers
  it for `y > −γ`, where the inner denominator `γ + y` is positive.
* Diagonal matrices `W`, `T` are given by their diagonal vectors `w`, `τ`.
* `symPart` is the orthogonal projection of a matrix onto the symmetric matrices. It is used to
  state Fréchet differentiability "on `Sym_n(ℝ)`": a map `G` on symmetric matrices is `C^k` there
  iff `G ∘ symPart` is `C^k` on all matrices, and for symmetric `Z, H` the derivative of `G` at
  `Z` in the direction `H` is that of `G ∘ symPart`.
-/

noncomputable section

/-- The lift of `f : ℝ → ℝ` to real symmetric matrices by the spectral theorem (`0` on
non-symmetric matrices). -/
def matFun {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ℝ → ℝ) (Y : Matrix ι ι ℝ) :
    Matrix ι ι ℝ :=
  open Classical in if h : Y.IsHermitian then h.cfc f else 0

/-- The symmetric part `(X + Xᵀ)/2`. -/
def symPart {ι : Type*} (X : Matrix ι ι ℝ) : Matrix ι ι ℝ := (1 / 2 : ℝ) • (X + X.transpose)

/-- The bounded `C²` extension of the reciprocal (5.1):
`ϕ(y) = [y + γ ((γ − y)₊ / (γ + y))³]⁻¹`. -/
def phi (γ y : ℝ) : ℝ := (y + γ * (max (γ - y) 0 / (γ + y)) ^ 3)⁻¹

/-- The cubed positive part `z ↦ z₊³` (Lemma 5.1). -/
def cubePos (z : ℝ) : ℝ := max z 0 ^ 3

/-- The argument of `ϕ` in (5.2): `(I_n + W M)(I_n + M W)` with `M = a I_n − βA`, `W = diag(w)`. -/
def reciprocalArg {n : ℕ} (β a : ℝ) (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 + Matrix.diagonal w * (a • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A)) *
    (1 + (a • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A) * Matrix.diagonal w)

/-- The test functional (5.2): `Φ_{a,W,T}(A) = tr_n[T ϕ((I_n + W M)(I_n + M W))]`, `M = a I_n − βA`,
`W = diag(w)`, `T = diag(τ)`. -/
def PhiFun {n : ℕ} (β γ a : ℝ) (w τ : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ntr (Matrix.diagonal τ * matFun (phi γ) (reciprocalArg β a w A))

/-- The block matrix of (5.11): `[[0, I_n + W M], [I_n + M W, 0]]`, `M = a I_n − βA`. -/
def blockArg {n : ℕ} (β a : ℝ) (w : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
  Matrix.fromBlocks 0
    (1 + Matrix.diagonal w * (a • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A))
    (1 + (a • (1 : Matrix (Fin n) (Fin n) ℝ) - β • A) * Matrix.diagonal w) 0

/-- The normalized Schatten 2-norm of a `2n × 2n` block matrix: `(tr_{2n}(XᵀX))^{1/2}`. -/
def schatten2Block {n : ℕ} (X : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ) : ℝ :=
  Real.sqrt ((∑ i, ∑ j, X i j ^ 2) / (2 * n))

/-- `A` projected onto `{M symmetric : ‖M‖_op ≤ C}`: a nearest point in Frobenius norm
(equivalently in `‖·‖_{L²}`). The set is closed and convex, so for symmetric `A` the nearest
point exists and is unique; this is the metric projection `Π_C` of Theorem 5.4. -/
def opBallProj {n : ℕ} (C : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  open Classical in
  if h : ∃ B : Matrix (Fin n) (Fin n) ℝ, B.IsSymm ∧ opNorm B ≤ C ∧
      ∀ B' : Matrix (Fin n) (Fin n) ℝ, B'.IsSymm → opNorm B' ≤ C → frob (A - B) ≤ frob (A - B')
  then Classical.choose h else 0

/-- The parameter set `J = [0,1] × D_n([0,1]) × {T ∈ D_n(ℝ) : ‖T‖_{L²} = 1}` of (5.20). -/
def paramSet (n : ℕ) : Set (ℝ × (Fin n → ℝ) × (Fin n → ℝ)) :=
  {θ | 0 ≤ θ.1 ∧ θ.1 ≤ 1 ∧ (∀ i, 0 ≤ θ.2.1 i ∧ θ.2.1 i ≤ 1) ∧
    Real.sqrt ((∑ i, θ.2.2 i ^ 2) / n) = 1}

end

end SKHessianAscent


