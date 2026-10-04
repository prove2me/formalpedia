-- Prove2me | Definitions.Def_DantzigSelector_Sparse_Model
-- name    : DantzigSelector_Sparse_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-04T08:16:28.901379+00:00
-- url     : https://prove2.me/theorems/e7b90117-5bd9-491b-b47e-4dc919470ac8
-- title:
--   Linear model, unit-normed design, sparsity and the Dantzig selector (DS)
-- statement:
--   This module fixes the objects of Candès and Tao's *The Dantzig Selector* (Section 1, pp. 2–5, and Section 3, pp. 15–17).
--
--   Let $X\in\mathbb R^{n\times p}$ be a deterministic design matrix with columns $X_1,\dots,X_p\in\mathbb R^n$, and consider the linear model $y = X\beta + z$ of (1.1), with $\beta\in\mathbb R^p$ and $y,z\in\mathbb R^n$.
--
--   1. **Unit-normed columns.** The design has unit-normed columns when $\|X_j\|_{\ell_2}=1$ for every $j=1,\dots,p$. The paper assumes this throughout (p. 4, restated on p. 15).
--   2. **Sparsity.** A vector $\beta\in\mathbb R^p$ is **$S$-sparse** when it has at most $S$ nonzero entries, that is, when it vanishes outside some index set $T$ with $|T|\le S$ (p. 3).
--   3. **Feasibility for (DS).** For a level $r\ge 0$ (the paper's $\lambda_p\cdot\sigma$), a vector $\tilde\beta\in\mathbb R^p$ is feasible when its residual $r_{\tilde\beta}=y-X\tilde\beta$ of (1.8) satisfies
--   $$
--   \|X^*(y-X\tilde\beta)\|_{\ell_\infty}=\sup_{1\le j\le p}\bigl|\langle y-X\tilde\beta,\,X_j\rangle\bigr|\le r .
--   $$
--   4. **The Dantzig selector.** A vector $\hat\beta$ is a **Dantzig selector** at level $r$ when it is feasible and minimizes $\|\tilde\beta\|_{\ell_1}=\sum_j|\tilde\beta_j|$ over all feasible $\tilde\beta$, i.e. it solves the convex program (DS) of (1.7). The program need not have a unique solution; every minimizer is a Dantzig selector.
--   5. **Restricted norms.** For $h\in\mathbb R^p$ and $T\subseteq\{1,\dots,p\}$, $\|h\|_{\ell_2(T)}=\bigl(\sum_{j\in T}h_j^2\bigr)^{1/2}$ and $\|h\|_{\ell_1(T)}=\sum_{j\in T}|h_j|$.
--   6. **Top block.** Given $h$, an index set $T_0$ and $S\in\mathbb N$, a set $T_1$ consists of **the $S$ largest positions of $h$ outside of $T_0$** (Lemma 3.1, p. 17) when $T_1\subseteq T_0^c$, $|T_1|=S$, and $|h_k|\le|h_j|$ for every $j\in T_1$ and every $k\in T_0^c\setminus T_1$. Ties may be broken in any way.
--
--   These are the objects in which the paper's main $\ell_2$ error bound (Theorem 1.1) and its proof (Section 3) are stated.
--
--   **Formalization Note** Indices run over `Fin n` and `Fin p`; vectors are functions `Fin p → ℝ`. The norms $\ell_1$, $\ell_2$, the support predicate and the column $X_j$ are the published definitions of `CandesTao_Decoding_Norms` and `CandesTao_Decoding_RestrictedIsometry`. The $\ell_\infty$ constraint is stated coordinatewise ($\forall j$), not as a supremum. The level $r$ is a single real; the paper's $\lambda_p\cdot\sigma$ is passed as $r$.
-- source:
--   Candès & Tao, The Dantzig Selector: Statistical Estimation When p Is Much Larger than n, arXiv:math/0506081v3, p. 2, Eq. (1.1); p. 3 (S-sparse); p. 4, Eqs. (1.7)–(1.8) and unit-normed columns; p. 15 (Section 3 preamble); p. 17, Lemma 3.1 (T1, ℓ2(T), ℓ1(T))

import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Real.Sqrt
import Definitions.Def_CandesTao_Decoding_Norms
import Definitions.Def_CandesTao_Decoding_RestrictedIsometry

namespace DantzigSelector.Sparse

open CandesTao.Decoding

/-- The columns `X_1, …, X_p ∈ ℝ^n` of the `n × p` design matrix `X` are unit-normed,
`‖X_j‖_{ℓ2} = 1` for every `j` (the paper's standing assumption, p. 4 and p. 15). -/
def UnitNormColumns {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) : Prop :=
  ∀ j : Fin p, l2Norm (column X j) = 1

/-- `β ∈ ℝ^p` is `S`-sparse: it has at most `S` nonzero entries, i.e. it is supported on some
index set of cardinality at most `S` (p. 3). -/
def IsSparse {p : ℕ} (β : Fin p → ℝ) (S : ℕ) : Prop :=
  ∃ T : Finset (Fin p), T.card ≤ S ∧ SupportedOn β T

/-- `b ∈ ℝ^p` is feasible for the Dantzig selector (1.7)–(1.8) at level `r` (the paper's
`λ_p · σ`): the residual `y - X b` obeys `‖Xᵀ (y - X b)‖_{ℓ∞} ≤ r`, i.e.
`|⟨y - X b, X_j⟩| ≤ r` for every column `j`. -/
def DantzigFeasible {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (b : Fin p → ℝ) : Prop :=
  ∀ j : Fin p, |∑ i, X i j * (y i - X.mulVec b i)| ≤ r

/-- `b` is a Dantzig selector (a solution of the program (DS), (1.7)) at level `r`: it is
feasible and its ℓ1 norm is minimal among all feasible vectors. The program need not have a
unique solution; any minimizer qualifies. -/
def IsDantzigSelector {n p : ℕ} (X : Matrix (Fin n) (Fin p) ℝ) (y : Fin n → ℝ) (r : ℝ)
    (b : Fin p → ℝ) : Prop :=
  DantzigFeasible X y r b ∧ ∀ b' : Fin p → ℝ, DantzigFeasible X y r b' → l1Norm b ≤ l1Norm b'

/-- The ℓ2 norm of `h` restricted to the index set `T`, `‖h‖_{ℓ2(T)} = (∑_{j ∈ T} h_j²)^{1/2}`. -/
noncomputable def l2On {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : ℝ :=
  Real.sqrt (∑ j ∈ T, h j ^ 2)

/-- The ℓ1 norm of `h` restricted to the index set `T`, `‖h‖_{ℓ1(T)} = ∑_{j ∈ T} |h_j|`. -/
def l1On {p : ℕ} (h : Fin p → ℝ) (T : Finset (Fin p)) : ℝ :=
  ∑ j ∈ T, |h j|

/-- `T1` consists of the `S` largest positions of `h` outside of `T0` (Lemma 3.1, p. 17):
`T1` is a subset of `T0ᶜ` of cardinality `S`, and every entry of `h` outside `T0 ∪ T1` is at
most, in absolute value, every entry of `h` on `T1` (ties broken arbitrarily). -/
def IsTopBlock {p : ℕ} (h : Fin p → ℝ) (T0 T1 : Finset (Fin p)) (S : ℕ) : Prop :=
  T1 ⊆ T0ᶜ ∧ T1.card = S ∧ ∀ j ∈ T1, ∀ k ∈ T0ᶜ \ T1, |h k| ≤ |h j|

end DantzigSelector.Sparse


