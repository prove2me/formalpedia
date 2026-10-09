-- Prove2me | Definitions.Def_TensorBTD_Cogradient_Setting
-- name    : TensorBTD_Cogradient_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T07:23:15.840424+00:00
-- url     : https://prove2.me/theorems/f84a57a1-f922-40ad-9120-a5323bd44cd9
-- title:
--   §2, (3.2), (3.5)–(3.8), §4.1, pp. 3–8 — the (rank-L_r ∘ rank-1) BTD as a structured CPD, f_BTD, V^σ, W^σ, T_(n) and the cogradient
-- statement:
--   This module sets up the (rank-$L_r\circ$ rank-1) block term decomposition (BTD) of Sorber, Van Barel and De Lathauwer as a structured canonical polyadic decomposition (CPD), the least-squares objective $f_{\mathrm{BTD}}$, and the complex cogradient.
--
--   **Tensors and products.** An $N$th-order tensor $\mathcal T\in\mathbb C^{I_1\times\cdots\times I_N}$ has $N=P+Q$ modes. For matrices (second-order tensors) the inner product of Definition 2.1 is $\langle X,Y\rangle=\sum_{i,j}\overline{x_{ij}}\,y_{ij}$, conjugate on the first argument, and $\|X\|^2=\langle X,X\rangle$ (Definition 2.2). The Khatri–Rao product of $A\in\mathbb C^{I\times K}$ and $B\in\mathbb C^{J\times K}$ is $A\odot B=[a_1\otimes b_1\ \cdots\ a_K\otimes b_K]$ (Definition 2.10). For a permutation $p$ of the modes, the string $A^{(p_1)}\odot\cdots\odot A^{(p_N)}$ of Proposition 4.2 has the entry $\prod_k a^{(p_k)}_{i_{p_k} j}$ in row $(i_{p_1},\dots,i_{p_N})$ and column $j$.
--
--   **The structured CPD.** Let $R'=\sum_{r=1}^R L_r$. The unknowns are $A^{(p)}\in\mathbb C^{I_p\times R'}$ for $1\le p\le P$ and $C^{(q)}\in\mathbb C^{I_{P+q}\times R}$ for $1\le q\le Q$, collected in
--   $$z=(\operatorname{vec}A^{(1)},\dots,\operatorname{vec}A^{(P)},\operatorname{vec}C^{(1)},\dots,\operatorname{vec}C^{(Q)}).$$
--   With the $R\times R'$ block-diagonal matrix $E=\operatorname{diag}(1_{1\times L_1},\dots,1_{1\times L_R})$, the factor matrices are (3.6)
--   $$A^{(n)}\ \text{for } n\le P,\qquad A^{(P+q)}=C^{(q)}E .$$
--   The residual tensor is $\mathcal F_{\mathrm{BTD}}=\sum_{r'=1}^{R'}a^{(1)}_{r'}\circ\cdots\circ a^{(N)}_{r'}-\mathcal T$, i.e. (3.5) minus $\mathcal T$, and the objective (3.7) is
--   $$f_{\mathrm{BTD}}=\tfrac12\|\mathcal F_{\mathrm{BTD}}\|^2 .$$
--   The same objective with $N$ free factor matrices $A^{(1)},\dots,A^{(N)}\in\mathbb C^{I_n\times R'}$ is the unstructured CPD; $f_{\mathrm{BTD}}$ is that objective evaluated at the factor matrices (3.6).
--
--   **Khatri–Rao strings, Gramians and unfoldings.** For a set $\sigma$ of modes, $V^{\sigma}=\bigodot_{n\notin\sigma}A^{(n)}$ (3.2) and $W^{\sigma}=\ast_{n\notin\sigma}A^{(n)\mathrm H}A^{(n)}$, the Hadamard product of the Gramians (Corollary 4.3). The mode-$n$ unfolding $T_{(n)}$ (Definition 2.6) places the tensor entry $(i_1,\dots,i_N)$ in row $i_n$ and in the column given by the remaining indices, in the same order as the rows of $V^{\{n\}}$. The proof of Theorem 4.4 uses
--   $$f^{(1)}=\|A^{(n)}V^{\{n\}\mathrm T}\|^2,\quad f^{(2)}=\langle T_{(n)},A^{(n)}V^{\{n\}\mathrm T}\rangle,\quad f^{(3)}=\|T_{(n)}\|^2 .$$
--
--   **The cogradient** (§4.1). For $f$ a complex-valued function of complex variables $z_\beta=x_\beta+\mathrm i y_\beta$, the cogradient (Wirtinger derivative) is the partial derivative with respect to $z_\beta$ treating $\overline{z_\beta}$ as constant,
--   $$\frac{\partial f}{\partial z_\beta}=\frac12\Big(\frac{\partial f}{\partial x_\beta}-\mathrm i\,\frac{\partial f}{\partial y_\beta}\Big),$$
--   where $\partial f/\partial x_\beta$ and $\partial f/\partial y_\beta$ are the real derivatives at $t=0$ of $t\mapsto f(z+t e_\beta)$ and $t\mapsto f(z+\mathrm i t e_\beta)$. The matrices $\partial f/\partial A^{(p)}$ and $\partial f/\partial C^{(q)}$ collect these derivatives over the entries of $A^{(p)}$ and $C^{(q)}$; for the unstructured CPD, $\partial f/\partial A^{(n)}$ is defined for every mode $n$.
--
--   These objects are shared by every statement of the mission: the goal (Theorem 4.4) and its milestones (Propositions 4.1 and 4.2, Corollary 4.3, and the two displays of the proof of Theorem 4.4).
--
--   **Formalization Note.** All indices are 0-based. Modes are `Fin P ⊕ Fin Q` (the paper's mode $p$ is `Sum.inl (p-1)`, its mode $P+q$ is `Sum.inr (q-1)`); the $R'$ columns are `Σ r : Fin R, Fin (L r)` in lexicographic order, which is the cumulative-sum order of (3.5). `vec` is column-major (Mathlib's `Matrix.vec`, index (column, row)). The rows of $V^\sigma$ and the columns of $T_{(n)}$ are indexed by the tuple of the remaining indices instead of the integer of (3.2) and Definition 2.6; both use the same order of the remaining modes, and every product $T_{(n)}V^{\{n\}}$, $A^{(n)}V^{\{n\}\mathrm T}$ is invariant under a common reordering. The residual is defined entrywise; (3.8) is then a consequence. $f_{\mathrm{BTD}}$ is real and is cast to $\mathbb C$. The real partial derivatives are Mathlib's `deriv`, which is $0$ where no derivative exists; every function the mission's statements differentiate is a real polynomial in the real and imaginary parts, so `deriv` is the genuine derivative there. The paper's qualifiers "nonzero" (3.1) and "rank-$L_r$" (3.5) describe what a decomposition is and are not used in §4; they are not imposed, and $P,Q,R,L_r,I_n$ may be $0$.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), pp. 3–8, Definitions 2.1, 2.2, 2.6, 2.10; (3.2), p. 4; (3.5)–(3.8), pp. 5–6; §4.1 (4.1), Proposition 4.2, Corollary 4.3, p. 7; proof of Theorem 4.4, p. 8

import Mathlib
import Definitions.Def_TensorBTD_Gramian_Setting

namespace TensorBTD.Cogradient

open Matrix

/-! # The (rank-L_r ∘ rank-1) block term decomposition as a structured CPD

Sorber, Van Barel & De Lathauwer, *Optimization-Based Algorithms for Tensor Decompositions*,
SIAM J. Optim. 23(2) (2013), authors' manuscript (Lirias), §2 (p. 3), §3.1 (3.2) (p. 4),
§3.3 (3.5)–(3.8) (pp. 5–6), §4.1 (4.1), Proposition 4.2, Corollary 4.3 (p. 7).

Conventions (all indices 0-based):
* the `N = P + Q` modes are `Fin P ⊕ Fin Q`; the paper's mode `p` is `Sum.inl (p-1)` and its mode
  `P + q` is `Sum.inr (q-1)`;
* the `R' = ∑_r L_r` columns of `A^(1), …, A^(P)` are `Col L = Σ r : Fin R, Fin (L r)`, in the
  lexicographic (= cumulative-sum) order of (3.5);
* `vec` is column-major: a matrix `M : Matrix (Fin m) K ℂ` is the vector indexed by
  `(column, row) : K × Fin m`, as Mathlib's `Matrix.vec`. -/

/-- Definition 2.1, p. 3: `⟨T, U⟩ = ∑ conj(t_{i_1⋯i_N}) u_{i_1⋯i_N}` (conjugate on the first
argument), here for matrices (second-order tensors) with arbitrary finite index types. -/
def frobInner {m k : Type*} [Fintype m] [Fintype k] (X Y : Matrix m k ℂ) : ℂ :=
  ∑ i, ∑ j, starRingEnd ℂ (X i j) * Y i j

/-- Definition 2.2, p. 3: the squared Frobenius norm `‖X‖² = ⟨X, X⟩` of a matrix. -/
def frobNormSq {m k : Type*} [Fintype m] [Fintype k] (X : Matrix m k ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (X i j)

/-- Definition 2.10, p. 3: the Khatri–Rao product `A ⊙ B = [a_1 ⊗ b_1 ⋯ a_K ⊗ b_K]`; the row
`(i, j)` is the row `(i - 1) J + j` of the Kronecker product (Definition 2.9). -/
def khatriRao {m₁ m₂ K : Type*} (A : Matrix m₁ K ℂ) (B : Matrix m₂ K ℂ) : Matrix (m₁ × m₂) K ℂ :=
  fun ij k => A ij.1 k * B ij.2 k

/-- Proposition 4.2, p. 7: the Khatri–Rao string `A^(p_1) ⊙ ⋯ ⊙ A^(p_N)` of `N` matrices with
`J` columns, for a permutation `p`; its rows are indexed by the tuples `(i_{p_1}, …, i_{p_N})`. -/
def krString {N J : ℕ} {I : Fin N → ℕ} (A : (n : Fin N) → Matrix (Fin (I n)) (Fin J) ℂ)
    (p : Equiv.Perm (Fin N)) : Matrix ((k : Fin N) → Fin (I (p k))) (Fin J) ℂ :=
  fun ρ j => ∏ k, A (p k) (ρ k) j

/-- Row index of `V^σ`: one index `i_m` for every mode `m ∉ σ`. -/
abbrev KRIdx {P Q : ℕ} (I : Fin P ⊕ Fin Q → ℕ) (σ : Finset (Fin P ⊕ Fin Q)) : Type :=
  (m : {m : Fin P ⊕ Fin Q // m ∉ σ}) → Fin (I m.1)

/-- (3.2), p. 4: the Khatri–Rao string `V^σ = ⊙_{n ∉ σ} A^(n)` of the factor matrices outside `σ`,
rows indexed by the tuple of the remaining indices. -/
def V {P Q : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {K : Type*} (σ : Finset (Fin P ⊕ Fin Q))
    (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) K ℂ) : Matrix (KRIdx I σ) K ℂ :=
  fun ρ c => ∏ m : {m : Fin P ⊕ Fin Q // m ∉ σ}, A m.1 (ρ m) c

/-- Corollary 4.3, p. 7: `W^σ = ∗_{n ∉ σ} A^(n)ᴴ A^(n)`, the Hadamard product of the Gramians of
the factor matrices outside `σ`. -/
def W {P Q : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {K : Type*} [Fintype K] (σ : Finset (Fin P ⊕ Fin Q))
    (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) K ℂ) : Matrix K K ℂ :=
  fun c c' => ∏ m ∈ Finset.univ.filter (· ∉ σ), ((A m)ᴴ * A m) c c'

/-- Definition 2.6, p. 3: the mode-`n` unfolding `T_(n)`; tensor entry `(i_1, …, i_N)` sits in row
`i_n` and in the column indexed by the tuple of the remaining indices (the same index type as the
rows of `V^{n}`). -/
def unfolding {P Q : ℕ} {I : Fin P ⊕ Fin Q → ℕ} (T : TensorBTD.Gramian.Tensor I) (n : Fin P ⊕ Fin Q) :
    Matrix (Fin (I n)) (KRIdx I {n}) ℂ :=
  fun i ρ => T (fun m => if h : m = n then h ▸ i else ρ ⟨m, by simpa using h⟩)

/-- The unknown factor matrix `A^(p)` (`I_p × R'`) of `z`. -/
def Amat {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (z : TensorBTD.Gramian.Unk I L → ℂ) (p : Fin P) :
    Matrix (Fin (I (.inl p))) (TensorBTD.Gramian.Col L) ℂ :=
  Matrix.of fun i c => z ⟨.inl p, (c, i)⟩

/-- The unknown matrix `C^(q)` (`I_{P+q} × R`) of `z`. -/
def Cmat {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (z : TensorBTD.Gramian.Unk I L → ℂ) (q : Fin Q) :
    Matrix (Fin (I (.inr q))) (Fin R) ℂ :=
  Matrix.of fun i r => z ⟨.inr q, (r, i)⟩

/-- (3.5)/(3.8), p. 6: the residual tensor `F_BTD = ∑_{r'} a^(1)_{r'} ∘ ⋯ ∘ a^(N)_{r'} − T` of the
structured CPD, entrywise. -/
def residual {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (z : TensorBTD.Gramian.Unk I L → ℂ) : TensorBTD.Gramian.Tensor I :=
  fun ι => (∑ c : TensorBTD.Gramian.Col L, ∏ n, TensorBTD.Gramian.factor z n (ι n) c) - T ι

/-- The residual tensor of the unstructured CPD with unknowns `x`. -/
def cpdResidual {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (x : TensorBTD.Gramian.GIdx I L → ℂ) : TensorBTD.Gramian.Tensor I :=
  fun ι => (∑ c : TensorBTD.Gramian.Col L, ∏ n, TensorBTD.Gramian.cpdFactor x n (ι n) c) - T ι

/-- (3.7), p. 6: the objective `f_BTD = ½ ‖F_BTD‖²` (real-valued, viewed in `ℂ`). -/
noncomputable def fBTD {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (z : TensorBTD.Gramian.Unk I L → ℂ) : ℂ :=
  (((1 / 2 : ℝ) * ∑ ι, Complex.normSq (residual T z ι) : ℝ) : ℂ)

/-- The same objective for the unstructured CPD with unknowns `x`. -/
noncomputable def fCPD {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (x : TensorBTD.Gramian.GIdx I L → ℂ) : ℂ :=
  (((1 / 2 : ℝ) * ∑ ι, Complex.normSq (cpdResidual T x ι) : ℝ) : ℂ)

/-- Proof of Theorem 4.4, p. 8: `f^(1)_BTD = ‖A^(n) · V^{n}ᵀ‖²`. -/
noncomputable def fOne {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (n : Fin P ⊕ Fin Q) (x : TensorBTD.Gramian.GIdx I L → ℂ) : ℂ :=
  (frobNormSq (TensorBTD.Gramian.cpdFactor x n * (V {n} (TensorBTD.Gramian.cpdFactor x))ᵀ) : ℂ)

/-- Proof of Theorem 4.4, p. 8: `f^(2)_BTD = ⟨T_(n), A^(n) · V^{n}ᵀ⟩`. -/
noncomputable def fTwo {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (n : Fin P ⊕ Fin Q) (x : TensorBTD.Gramian.GIdx I L → ℂ) : ℂ :=
  frobInner (unfolding T n) (TensorBTD.Gramian.cpdFactor x n * (V {n} (TensorBTD.Gramian.cpdFactor x))ᵀ)

/-- Proof of Theorem 4.4, p. 8: `f^(3)_BTD = ‖T_(n)‖²`. -/
noncomputable def fThree {P Q : ℕ} {I : Fin P ⊕ Fin Q → ℕ} (T : TensorBTD.Gramian.Tensor I)
    (n : Fin P ⊕ Fin Q) : ℂ :=
  (frobNormSq (unfolding T n) : ℂ)

/-- §4.1, p. 7: the cogradient (Wirtinger derivative) `∂f/∂z_β = ½(∂f/∂x_β − i ∂f/∂y_β)` of
`f : ℂ^X → ℂ` at `x` in the coordinate `z_β = x_β + i y_β`, the partial derivative with respect
to `z_β` treating `z̄_β` as constant; `∂f/∂x_β` and `∂f/∂y_β` are the real derivatives at `t = 0`
of `t ↦ f(x + t e_β)` and `t ↦ f(x + i t e_β)`. -/
noncomputable def cograd {X : Type*} [DecidableEq X] (f : (X → ℂ) → ℂ) (x : X → ℂ) (β : X) : ℂ :=
  (1 / 2 : ℂ) *
    (deriv (fun t : ℝ => f (x + (t : ℂ) • Pi.single β 1)) 0 -
      Complex.I * deriv (fun t : ℝ => f (x + ((t : ℂ) * Complex.I) • Pi.single β 1)) 0)

/-- The matrix `∂f/∂A^(p)` of the cogradients of `f` with respect to the entries of the unknown
`A^(p)`; by construction its `vec` is the block of `∂f/∂z` belonging to `vec A^(p)`, as in (4.4). -/
noncomputable def cogradA {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (f : (TensorBTD.Gramian.Unk I L → ℂ) → ℂ) (z : TensorBTD.Gramian.Unk I L → ℂ) (p : Fin P) :
    Matrix (Fin (I (.inl p))) (TensorBTD.Gramian.Col L) ℂ :=
  Matrix.of fun i c => cograd f z ⟨.inl p, (c, i)⟩

/-- The matrix `∂f/∂C^(q)` of the cogradients of `f` with respect to the entries of the unknown
`C^(q)`; by construction its `vec` is the block of `∂f/∂z` belonging to `vec C^(q)`, as in (4.4). -/
noncomputable def cogradC {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (f : (TensorBTD.Gramian.Unk I L → ℂ) → ℂ) (z : TensorBTD.Gramian.Unk I L → ℂ) (q : Fin Q) :
    Matrix (Fin (I (.inr q))) (Fin R) ℂ :=
  Matrix.of fun i r => cograd f z ⟨.inr q, (r, i)⟩

/-- The matrix `∂f/∂A^(n)` of cogradients of `f` with respect to the entries of the `n`-th TensorBTD.Gramian.factor
matrix of the unstructured CPD (any mode `n`, including `n > P`). -/
noncomputable def cogradMatG {P Q R : ℕ} {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (f : (TensorBTD.Gramian.GIdx I L → ℂ) → ℂ) (x : TensorBTD.Gramian.GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) :
    Matrix (Fin (I n)) (TensorBTD.Gramian.Col L) ℂ :=
  Matrix.of fun i c => cograd f x ⟨n, (c, i)⟩

end TensorBTD.Cogradient


