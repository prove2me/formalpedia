-- Prove2me | Definitions.Def_TensorBTD_Gramian_Setting
-- name    : TensorBTD_Gramian_Setting
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T06:29:31.751116+00:00
-- url     : https://prove2.me/theorems/58c5560a-b4a7-4184-84ac-8a4becfe5d1c
-- title:
--   §2, §3.3, (3.6)–(3.8), Prop. 4.1, Cor. 4.3, (4.11)–(4.12) — the (rank-L_r ∘ rank-1) BTD as a structured CPD: E, A^(P+q) = C^(q)E, residual, Jacobian, W^σ, F^(q), Σ, Π
-- statement:
--   This file sets up the (rank-$L_r$ $\circ$ rank-1) block term decomposition (BTD) of Sorber, Van Barel and De Lathauwer as a structured canonical polyadic decomposition (CPD), together with every matrix that appears in their Theorem 4.5.
--
--   **Tensors.** Fix natural numbers $P, Q$ and put $N = P + Q$. A tensor $\mathcal T \in \mathbb C^{I_1\times\cdots\times I_N}$ is a function of a multi-index $\iota = (i_1,\dots,i_N)$. The inner product (Definition 2.1) is
--   $$\langle \mathcal T, \mathcal U\rangle = \sum_{i_1,\dots,i_N} \overline{t_{i_1\cdots i_N}}\, u_{i_1\cdots i_N},$$
--   with the conjugate on the first argument, and the outer product of vectors $v^{(n)}\in\mathbb C^{I_n}$ is the tensor $(v^{(1)}\circ\cdots\circ v^{(N)})_{\iota} = \prod_n v^{(n)}_{i_n}$ (Definitions 2.3–2.4).
--
--   **The structured CPD.** Fix $R$ and block sizes $L_1,\dots,L_R$, and let $R' = \sum_r L_r$. The $R'$ columns are numbered by pairs $(r,l)$ with $1\le l\le L_r$, in lexicographic order, which is the cumulative-sum order of (3.5). The matrix $E\in\mathbb R^{R\times R'}$ is the block diagonal matrix $\mathrm{diag}(1_{1\times L_1},\dots,1_{1\times L_R})$: $E_{r,(r',l)} = 1$ if $r'=r$ and $0$ otherwise. The unknowns are
--   $$z = (\mathrm{vec}(A^{(1)}),\dots,\mathrm{vec}(A^{(P)}),\mathrm{vec}(C^{(1)}),\dots,\mathrm{vec}(C^{(Q)})),$$
--   with $A^{(p)}\in\mathbb C^{I_p\times R'}$ and $C^{(q)}\in\mathbb C^{I_{P+q}\times R}$, and $\mathrm{vec}$ is column-major. The factor matrices of the structured CPD are $A^{(p)}$ for $p\le P$ and
--   $$A^{(P+q)} = C^{(q)}\cdot E \qquad (3.6).$$
--   The residual tensor is $\mathcal F_{\mathrm{BTD}} = \sum_{c=1}^{R'} a^{(1)}_c\circ\cdots\circ a^{(N)}_c - \mathcal T$, i.e. entrywise the residual (3.8). Alongside it, the *unstructured* CPD residual in $R'$ terms treats all $N$ factor matrices $A^{(1)},\dots,A^{(N)}\in\mathbb C^{I_n\times R'}$ as free unknowns $x = (\mathrm{vec}A^{(1)},\dots,\mathrm{vec}A^{(N)})$; the map $z\mapsto x$ that sends $z$ to its factor matrices (with $A^{(P+q)}=C^{(q)}E$) is also defined.
--
--   **Jacobians.** For a map $G$ from $\mathbb C^X$ to $\mathbb C^Y$, the complex Jacobian $\partial\,\mathrm{vec}(G)/\partial x^{\mathrm T}$ at $x$ is the $Y\times X$ matrix whose entry $(y,\beta)$ is the complex derivative at $t=0$ of $t\mapsto G(x+t e_\beta)_y$. Applied to $\mathcal F_{\mathrm{BTD}}$ as a function of $z$, this is the Jacobian $J$ of Theorem 4.5.
--
--   **Gramian blocks.** For a set $\sigma$ of modes, $W^\sigma = \ast_{m\notin\sigma} A^{(m)\mathrm H}A^{(m)}$ is the Hadamard (entrywise) product of the Gramians of the factor matrices outside $\sigma$ (Corollary 4.3). $F^{(q)} = E\otimes \mathbb I_{I_{P+q}}$ (Proposition 4.1), and
--   $$\Sigma = \mathrm{diag}(\mathbb I_{I_1R'},\dots,\mathbb I_{I_PR'},F^{(1)},\dots,F^{(Q)}) \qquad (4.11).$$
--   Finally $\Pi$ is the $N\times N$ block matrix of the right-hand side of (4.12): its $(n,n)$ block is $W^{\{n\}}\otimes\mathbb I_{I_n}$, and for $n_1\ne n_2$ its $(n_1,n_2)$ block is the $R'\times R'$ array whose $(r_1,r_2)$ sub-block is $w^{\{n_1,n_2\}}_{r_1r_2}\,a^{(n_1)}_{r_2}a^{(n_2)\mathrm H}_{r_1}$.
--
--   These objects are shared by every statement of the mission: the goal theorem identifies the Gramian $J^{\mathrm H}J$ in terms of $\Sigma$ and $\Pi$.
--
--   **Formalization Note.** Modes are `Fin P ⊕ Fin Q` (mode $p$ is `Sum.inl (p-1)`, mode $P+q$ is `Sum.inr (q-1)`); all indices are 0-based. The $R'$ columns are `Σ r : Fin R, Fin (L r)`. Vectorized indices are pairs (column, row), which is Mathlib's column-major `Matrix.vec`; Kronecker products use Mathlib's `⊗ₖ` with index (row of the left factor, row of the right factor), so $F^{(q)}$ has rows $(r,i)$ and columns $((r,l),i)$. The Jacobian is the ℂ-derivative `deriv` (the holomorphic Jacobian), not a real derivative. In $\Pi$ the Kronecker delta $\delta_{ij}$ between $i\in[I_{n_1}]$ and $j\in[I_{n_2}]$ is written as equality of the dependent pairs $(n_1,i)$ and $(n_2,j)$. The residual is defined entrywise as a sum of outer products rather than through unfoldings $T_{(n)}$; the paper's (3.8) is the mode-$n$ unfolding of this tensor. The paper's standing assumption that $N, P, Q$ are positive and its qualifiers "nonzero", "rank-$L_r$" are not imposed: the definitions make sense for all sizes.
-- source:
--   Sorber, Van Barel & De Lathauwer, Optimization-Based Algorithms for Tensor Decompositions, SIAM J. Optim. 23(2) (2013), doi:10.1137/120868323, authors' manuscript (Lirias), pp. 3–7 and 10–12, Definitions 2.1–2.5, 2.9, (3.1), (3.5)–(3.8), Proposition 4.1, Corollary 4.3, (4.6), (4.8), Theorem 4.4 (vector of unknowns), (4.11)–(4.12)

import Mathlib

namespace TensorBTD.Gramian

open Matrix
open scoped Kronecker

/-! The (rank-`L_r` ∘ rank-1) block term decomposition of Sorber, Van Barel & De Lathauwer (2013),
read as a structured CPD in `R′ = ∑ r, L r` rank-one terms ((3.5)–(3.8)), together with the
objects of Theorem 4.5: the holomorphic Jacobian, the Hadamard-Gramian products `W^σ`
(Corollary 4.3), the matrices `F^(q) = E ⊗ 𝕀` (Proposition 4.1), `Σ` (4.11) and the closed form
of `Π` (4.12).

Conventions: the `N = P + Q` modes are `Fin P ⊕ Fin Q` (mode `p` is `Sum.inl (p-1)`, mode
`P + q` is `Sum.inr (q-1)`), all indices are 0-based, and the `R′` columns are
`Σ r : Fin R, Fin (L r)` in lexicographic order (the cumulative-sum order of (3.5)). -/

variable {P Q R : ℕ}

/-- The `R′ = ∑ r, L r` columns of the factor matrices `A^(n)`: column `⟨r, l⟩` is the
`l`-th column of the `r`-th block. -/
abbrev Col (L : Fin R → ℕ) : Type := Σ r : Fin R, Fin (L r)

/-- The `R × R′` block diagonal matrix `E = diag(1_{1×L_1}, …, 1_{1×L_R})` (p. 6, after (3.6)). -/
def E (L : Fin R → ℕ) : Matrix (Fin R) (Col L) ℂ :=
  Matrix.of fun r c => if c.1 = r then 1 else 0

/-- Complex `N`-th order tensors `ℂ^{I_1 × ⋯ × I_N}`, `N = P + Q`. -/
abbrev Tensor (I : Fin P ⊕ Fin Q → ℕ) : Type := ((n : Fin P ⊕ Fin Q) → Fin (I n)) → ℂ

/-- Definition 2.1: `⟨T, U⟩ = ∑_ι conj(t_ι) u_ι` (conjugate on the first argument). -/
def tensorInner {I : Fin P ⊕ Fin Q → ℕ} (T U : Tensor I) : ℂ :=
  ∑ ι, starRingEnd ℂ (T ι) * U ι

/-- Definitions 2.3–2.4: the outer product `v^(1) ∘ ⋯ ∘ v^(N)` of one vector per mode. -/
def outer {I : Fin P ⊕ Fin Q → ℕ} (v : (n : Fin P ⊕ Fin Q) → Fin (I n) → ℂ) : Tensor I :=
  fun ι => ∏ n, v n (ι n)

/-- The CPD model (3.1) in `R′` rank-one terms: `∑_c a_c^(1) ∘ ⋯ ∘ a_c^(N)` for factor
matrices `A^(n) ∈ ℂ^{I_n × R′}`. -/
def cpdModel {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}
    (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ) : Tensor I :=
  ∑ c : Col L, outer fun n k => A n k c

/-- The column type of the unknown matrix of mode `n`: `A^(p)` has `R′` columns, `C^(q)` has `R`. -/
def UCol (L : Fin R → ℕ) : Fin P ⊕ Fin Q → Type
  | .inl _ => Col L
  | .inr _ => Fin R

instance UCol.instFintype (L : Fin R → ℕ) : (n : Fin P ⊕ Fin Q) → Fintype (UCol L n)
  | .inl _ => inferInstanceAs (Fintype (Col L))
  | .inr _ => inferInstanceAs (Fintype (Fin R))

instance UCol.instDecidableEq (L : Fin R → ℕ) : (n : Fin P ⊕ Fin Q) → DecidableEq (UCol L n)
  | .inl _ => inferInstanceAs (DecidableEq (Col L))
  | .inr _ => inferInstanceAs (DecidableEq (Fin R))

/-- Index set of the vector of unknowns `z = (vec A^(1), …, vec A^(P), vec C^(1), …, vec C^(Q))`
(Theorem 4.4): mode, then (column, row), which is the column-major order of `Matrix.vec`. -/
abbrev Unk (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) : Type :=
  Σ n : Fin P ⊕ Fin Q, UCol L n × Fin (I n)

/-- Index set of the unknowns of the unstructured CPD in `R′` terms,
`(vec A^(1), …, vec A^(N))` with every `A^(n) ∈ ℂ^{I_n × R′}` free. -/
abbrev GIdx (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) : Type :=
  Σ n : Fin P ⊕ Fin Q, Col L × Fin (I n)

variable {I : Fin P ⊕ Fin Q → ℕ} {L : Fin R → ℕ}

/-- The factor matrix `A^(p) ∈ ℂ^{I_p × R′}` read off the unknowns `z`. -/
def aMat (z : Unk I L → ℂ) (p : Fin P) : Matrix (Fin (I (.inl p))) (Col L) ℂ :=
  Matrix.of fun i c => z ⟨.inl p, (c, i)⟩

/-- The matrix `C^(q) ∈ ℂ^{I_{P+q} × R}` read off the unknowns `z`. -/
def cMat (z : Unk I L → ℂ) (q : Fin Q) : Matrix (Fin (I (.inr q))) (Fin R) ℂ :=
  Matrix.of fun i r => z ⟨.inr q, (r, i)⟩

/-- The factor matrices of the structured CPD (3.6): `A^(n)` for `n ≤ P` and
`A^(P+q) ≜ C^(q) · E`. -/
def factor (z : Unk I L → ℂ) : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ
  | .inl p => aMat z p
  | .inr q => cMat z q * E L

/-- The factor matrices of the unstructured CPD read off its unknowns `x`. -/
def cpdFactor (x : GIdx I L → ℂ) (n : Fin P ⊕ Fin Q) : Matrix (Fin (I n)) (Col L) ℂ :=
  Matrix.of fun i c => x ⟨n, (c, i)⟩

/-- The point `(vec A^(1), …, vec A^(N))` of the unstructured CPD, with `A^(P+q) = C^(q) E`. -/
def fullVec (z : Unk I L → ℂ) : GIdx I L → ℂ :=
  fun g => factor z g.1 g.2.2 g.2.1

/-- The residual tensor of the unstructured CPD in `R′` terms (entrywise form of (3.8)). -/
def cpdResidual (T : Tensor I) (x : GIdx I L → ℂ) : Tensor I :=
  cpdModel (cpdFactor x) - T

/-- The residual tensor `ℱ_BTD` of the BTD (3.8) as a function of the unknowns `z`
(entrywise: `ℱ_ι = ∑_c ∏_n A^(n)_{ι_n c} − T_ι`). -/
def residual (T : Tensor I) (z : Unk I L → ℂ) : Tensor I :=
  cpdModel (factor z) - T

/-- The complex Jacobian `∂ vec(G) / ∂ xᵀ` of `G` at `x`: row `y`, column `β`, entry the complex
derivative of `t ↦ G(x + t e_β)_y` at `t = 0`. -/
noncomputable def jac {X Y : Type*} [DecidableEq X] (G : (X → ℂ) → (Y → ℂ)) (x : X → ℂ) : Matrix Y X ℂ :=
  Matrix.of fun y β => deriv (fun t : ℂ => G (x + t • Pi.single β 1) y) 0

/-- Corollary 4.3: `W^σ = ∗_{m ∉ σ} A^(m)ᴴ A^(m)` (Hadamard product of the Gramians of the
factor matrices outside `σ`). -/
def W (σ : Finset (Fin P ⊕ Fin Q)) (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ) :
    Matrix (Col L) (Col L) ℂ :=
  Matrix.of fun c c' => ∏ m ∈ Finset.univ.filter (· ∉ σ), ((A m)ᴴ * A m) c c'

/-- Proposition 4.1: `F^(q) = E ⊗ 𝕀_{I_(P+q)}` (Mathlib's Kronecker product, index `(r, i)`). -/
def F (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) (q : Fin Q) :
    Matrix (Fin R × Fin (I (.inr q))) (Col L × Fin (I (.inr q))) ℂ :=
  E L ⊗ₖ (1 : Matrix (Fin (I (.inr q))) (Fin (I (.inr q))) ℂ)

/-- The diagonal blocks of `Σ` (4.11): `𝕀_{I_p R′}` for `n = p ≤ P` and `F^(q)` for `n = P + q`. -/
def SigmaBlock (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) :
    (n : Fin P ⊕ Fin Q) → Matrix (UCol L n × Fin (I n)) (Col L × Fin (I n)) ℂ
  | .inl p => (1 : Matrix (Col L × Fin (I (.inl p))) (Col L × Fin (I (.inl p))) ℂ)
  | .inr q => F I L q

/-- `Σ ≜ diag(𝕀_{I_1 R′}, …, 𝕀_{I_P R′}, F^(1), …, F^(Q))` (4.11): rows indexed by the
unknowns `z`, columns by the unknowns of the unstructured CPD. -/
def Sigma (I : Fin P ⊕ Fin Q → ℕ) (L : Fin R → ℕ) : Matrix (Unk I L) (GIdx I L) ℂ :=
  Matrix.blockDiagonal' (SigmaBlock I L)

/-- The right-hand side of (4.12), assembled into the `N × N` block matrix `[Π^(n1,n2)]`:
entry `(⟨n1, (r1, i)⟩, ⟨n2, (r2, j)⟩)` is `w^{n}_{r1 r2} δ_{ij}` when `n1 = n2 = n` (the block
`W^{n} ⊗ 𝕀_{I_n}`), and `w^{n1,n2}_{r1 r2} a^(n1)_{i r2} conj(a^(n2)_{j r1})` otherwise (the
`(r1, r2)` sub-block `w^{n1,n2}_{r1 r2} a^(n1)_{r2} a^(n2)ᴴ_{r1}`). -/
def PiMat (A : (n : Fin P ⊕ Fin Q) → Matrix (Fin (I n)) (Col L) ℂ) :
    Matrix (GIdx I L) (GIdx I L) ℂ :=
  Matrix.of fun a b =>
    if a.1 = b.1 then
      W {a.1} A a.2.1 b.2.1 *
        (if (⟨a.1, a.2.2⟩ : Σ n, Fin (I n)) = ⟨b.1, b.2.2⟩ then 1 else 0)
    else
      W {a.1, b.1} A a.2.1 b.2.1 * A a.1 a.2.2 b.2.1 * starRingEnd ℂ (A b.1 b.2.2 a.2.1)

end TensorBTD.Gramian


