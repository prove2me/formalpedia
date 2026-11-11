-- Prove2me | Definitions.Def_RobustCorrClust_Main_NCMDual
-- name    : RobustCorrClust_Main_NCMDual
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T05:40:52.502409+00:00
-- url     : https://prove2.me/theorems/a8149365-7f1b-4d03-bed7-d61525460bc6
-- title:
--   Positive part, the nearest-correlation-matrix objective and its dual φ, the box B, and Algorithm 1 run with a gradient oracle (§5)
-- statement:
--   Let $C$ be a real $n\times n$ matrix (in Part B: symmetric, nonnegative, zero diagonal).
--
--   - **Positive part** (Definition 1): for symmetric $P=\sum_i\sigma_iw_iw_i^\top$ (orthonormal eigenvectors $w_i$), $P^+=\sum_i\max(\sigma_i,0)\,w_iw_i^\top$.
--   - $M(y)=C+\mathrm{Diag}(y)$ for $y\in\mathbb R^n$.
--   - $f(X)=\tfrac12\|X-C\|_F^2$ (Definition 4); the Lagrangian $L(X,y)=f(X)-\sum_u y_u(X_{uu}-1)$ (Definition 5); the dual objective $\varphi(y)=\tfrac12\|M(y)^+\|_F^2-\mathbf 1^\top y$ (eq. (4)).
--   - $R=n+\max_u\sum_vC_{uv}$ and the box $B=[-R,1]^n$ (Definition 7); $\Pi_B$ clips each coordinate to $[-R,1]$.
--   - Parameters (p. 22) for $\xi\in(0,1]$: $\nu=\xi/(100nR^2)$, $\eta=\nu^3$, $T=\lceil1/\nu^6\rceil$, $a=1+\nu$.
--   - **Algorithm 1 with a gradient oracle.** Given vectors $x^{t,u}\in\mathbb R^n$ (the vector obtained in line 4 at iteration $t$ for vertex $u$): $y_1=0$, and for $t\ge1$
--   $$y_{t+1}=\Pi_B\big(y_t-\eta\,\tilde g_t\big),\qquad(\tilde g_t)_u=x^{t,u}_u-1;$$
--   the output is $\bar y=\tfrac1T\sum_{t=1}^Ty_t$.
--   - **Diagonal repair**: $Y=X/a+\mathrm{Diag}(1-\mathrm{diag}(X)/a)$.
--
--   **Formalization Note.** $P^+$ uses Mathlib's eigenvector unitary and eigenvalues of a Hermitian (= symmetric real) matrix; on a non-symmetric matrix it is $0$, a value never used (every $M(y)$ is symmetric when $C$ is). For $n=0$ the maximum over no vertices is $0$. The oracle is a function `x : ℕ → Fin n → Fin n → ℝ`, `x t u` the vector for vertex `u` at iteration `t`; the iterates are indexed as in the paper (index $0$ unused).
-- source:
--   Cao, Fabius, Wang, Efficient Correlation Clustering in Single-pass Graph Streams: Deterministic and Adversarially Robust, STOC 2027 submission (sha256 814ae686…), p. 13, Definition 1; p. 22, Algorithm 1 and parameters; pp. 24-26, Definitions 4-5, eq. (4); p. 30, Definition 7; p. 34, conceptual process

import Mathlib
import Definitions.Def_RobustCorrClust_Main_Sparsifier

namespace RobustCorrClust.Main

open Finset Matrix

/-! Part B of the paper (§5, pp. 21–36): the nearest-correlation-matrix problem for a weighted
adjacency matrix `C` (symmetric, nonnegative, zero diagonal), its `n`-variable dual, and
Algorithm 1 (projected gradient descent on the dual) run with an arbitrary gradient oracle. -/

/-- Definition 1 (p. 13): the positive part `P⁺ = ∑_i max(σ_i, 0) w_i w_iᵀ` of a symmetric
matrix `P` with spectral decomposition `P = ∑_i σ_i w_i w_iᵀ`, written with Mathlib's
orthonormal eigenbasis `U` and eigenvalues `σ` as `U · Diag(max(σ, 0)) · Uᵀ`. (It does not
depend on the choice of eigenbasis. Every matrix it is applied to below is symmetric; the value
`0` on a non-symmetric matrix is a convention that is never used.) -/
noncomputable def posPart {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  if h : P.IsHermitian then
    (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) *
      diagonal (fun i => max (h.eigenvalues i) 0) *
      star (h.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ)
  else 0

/-- `M(y) := C + Diag(y)` (p. 25). -/
def Mmat {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  C + diagonal y

/-- Definition 4 (p. 24): the nearest-correlation-matrix objective `f(X) = ½‖X − C‖²_F`. -/
noncomputable def fObj {n : ℕ} (C X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  frobSq (X - C) / 2

/-- Definition 5 (p. 25): the Lagrangian `L(X, y) := f(X) − ∑_u y_u (X_uu − 1)`. -/
noncomputable def lagr {n : ℕ} (C X : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ :=
  fObj C X - ∑ u, y u * (X u u - 1)

/-- Eq. (4) (p. 26): the dual objective `φ(y) := ½‖M(y)⁺‖²_F − 1ᵀy`. -/
noncomputable def phi {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : ℝ :=
  frobSq (posPart (Mmat C y)) / 2 - ∑ u, y u

/-- Definition 7 (p. 30) and the parameter box (p. 22): `R = n + max_u ∑_v C_uv`. For `n = 0`
the maximum over the empty vertex set is read as `0`. -/
noncomputable def boxR {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (n : ℝ) + ⨆ u, ∑ v, C u v

/-- `y ∈ B = [−R, 1]ⁿ` (Definition 7, p. 30). -/
def InBox {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Prop :=
  ∀ u, -boxR C ≤ y u ∧ y u ≤ 1

/-- The projection `Π_B` onto the box: clip every coordinate to `[−R, 1]` (Algorithm 1, line 6). -/
noncomputable def clipBox {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) : Fin n → ℝ :=
  fun u => max (-boxR C) (min (y u) 1)

/-- Parameter box (p. 22): `ν = ξ / (100 n R²)`. -/
noncomputable def nuPar {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ξ : ℝ) : ℝ :=
  ξ / (100 * (n : ℝ) * boxR C ^ 2)

/-- Parameter box (p. 22): the step size `η = ν³`. -/
noncomputable def etaPar {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ξ : ℝ) : ℝ :=
  nuPar C ξ ^ 3

/-- Parameter box (p. 22): the number of iterations `T = ⌈1/ν⁶⌉`. -/
noncomputable def iterPar {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ξ : ℝ) : ℕ :=
  ⌈1 / nuPar C ξ ^ 6⌉₊

/-- Parameter box (p. 22): the scale `a = 1 + ν`. -/
noncomputable def aPar {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ξ : ℝ) : ℝ :=
  1 + nuPar C ξ

/-- The iterates `y¹, y², …` of Algorithm 1 (p. 22), indexed as in the paper (`pgdY C ξ x t` is
`y_t`; index `0` is unused and set to `0`), run with the gradient oracle `x`: `x t u` is the
vector `x ∈ ℝⁿ` obtained in line 4 at iteration `t` for vertex `u`. Line 1: `y₁ = 0`;
line 5: `g̃_u = (x t u)_u − 1`; line 6: `y_{t+1} = Π_B(y_t − η g̃)`. -/
noncomputable def pgdY {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ξ : ℝ)
    (x : ℕ → Fin n → Fin n → ℝ) : ℕ → (Fin n → ℝ)
  | 0 => 0
  | 1 => 0
  | t + 2 => clipBox C (fun u => pgdY C ξ x (t + 1) u - etaPar C ξ * (x (t + 1) u u - 1))

/-- The output `ȳ = (1/T) ∑_{t=1}^{T} y_t` of Algorithm 1 (line 7, p. 22). -/
noncomputable def pgdOut {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (ξ : ℝ)
    (x : ℕ → Fin n → Fin n → ℝ) : Fin n → ℝ :=
  fun u => (1 / (iterPar C ξ : ℝ)) * ∑ t ∈ Icc 1 (iterPar C ξ), pgdY C ξ x t u

/-- The diagonal repair of Lemma 5.17 and of the conceptual process (pp. 34–35):
`Y := X/a + Diag(1 − diag(X)/a)`. -/
noncomputable def repairY {n : ℕ} (X : Matrix (Fin n) (Fin n) ℝ) (a : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (1 / a) • X + diagonal (fun u => 1 - X u u / a)

end RobustCorrClust.Main


