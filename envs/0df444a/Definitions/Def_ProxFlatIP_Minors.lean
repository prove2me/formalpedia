-- Prove2me | Definitions.Def_ProxFlatIP_Minors
-- name    : ProxFlatIP_Minors
-- status  : Definition
-- author  : @iris
-- created : 2026-11-03T05:13:31.739582+00:00
-- url     : https://prove2.me/theorems/b94b3a43-7986-4b1d-ae69-11ee9ab1e3bf
-- title:
--   The minors $\Delta_k(A)$, $\Delta^\alpha(A)$, $\gcd A_I$ and $\Delta^\alpha_I(A)$
-- statement:
--   Let $A\in\mathbb Z^{m\times n}$ and $\alpha\in\mathbb Z^n$.
--
--   1. $\Delta_k(A):=\max\{|\det M|: M\text{ is a }k\times k\text{ submatrix of }A\}$ is the largest absolute minor of order exactly $k$.
--   2. $\Delta^\alpha(A):=\max\left\{\left|\det\begin{pmatrix}\alpha^\top\\B\end{pmatrix}\right|: B\text{ is an }(n-1)\times n\text{ submatrix of }A\right\}$.
--   3. $\gcd A_I:=\gcd\{|\det M|: M\text{ is a }\operatorname{rank}(A_I)\times\operatorname{rank}(A_I)\text{ submatrix of }A_I\}$, with $\gcd A_\emptyset=1$.
--   4. $\Delta^\alpha_I(A):=\dfrac{1}{\gcd A_I}\cdot\max\left\{\left|\det\begin{pmatrix}\alpha^\top\\A_K\end{pmatrix}\right|: I\subseteq K\subseteq[m],\ |K|=n-1\right\}$.
--
--   The goal theorem is stated with $\Delta_{n-1}(A)$. The general linear-form bound is stated with $\Delta^\alpha(A)=\Delta^\alpha_\emptyset(A)$, which for $\alpha=\pm e_i$ is at most $\Delta_{n-1}(A)$.
--
--   **Formalization Note** Submatrices are given by injections of index types, which list rows and columns in every order; reordering does not change $|\det|$. Maxima are taken in `ℕ` through `natAbs`. The value $\gcd A_\emptyset=1$ is a consequence of the formula, since the only submatrix is the $0\times0$ one. The matrix $(\alpha^\top; B)$ is indexed by `Fin n`, with first row $\alpha^\top$, so no cast along $n-1+1=n$ is needed.
-- source:
--   Celaya, Kuhlmann, Paat, Weismantel, Proximity and flatness bounds for linear integer optimization, arXiv:2211.14941v1 [math.OC] (preprint, 27 Nov 2022), https://arxiv.org/abs/2211.14941v1, p.1 (Δ_k); Definition 1, p.3 (Δ^α); §2, p.4 (gcd A_I); p.5 (Δ^α_I)

import Mathlib
import Definitions.Def_ProxFlatIP_Polyhedra

open Matrix

namespace ProxFlatIP

/-! # Minors: `Δ_k(A)`, `Δ^α(A)`, `gcd A_I`, `Δ^α_I(A)`

Celaya–Kuhlmann–Paat–Weismantel, arXiv:2211.14941v1 (preprint): p.1, Definition 1 (p.3), p.4, p.5.

**Formalization Note.** A submatrix is given by injections `Fin k ↪ Fin m` and `Fin k ↪ Fin n`. They
also list the rows and columns in every other order, which does not change `|det|`. All maxima are
over finite sets and are taken in `ℕ` through `natAbs`; the maximum of an empty family is `0`, which
cannot occur under full column rank (then `m ≥ n`). The matrix `(α⊤ ; B)` is `bordered`, indexed by
`Fin n` so that no cast along `n − 1 + 1 = n` is needed. -/

variable {m n : ℕ}

/-- `Δ_k(A) := max{|det M| : M is a k × k submatrix of A}` (p.1): the largest absolute `k × k` minor,
for this one order `k` only. -/
noncomputable def minorMax (k : ℕ) (A : Matrix (Fin m) (Fin n) ℤ) : ℕ :=
  Finset.univ.sup fun p : (Fin k ↪ Fin m) × (Fin k ↪ Fin n) => (A.submatrix p.1 p.2).det.natAbs

/-- The `n × n` matrix `(α⊤ ; A_f)`: row `0` is `α⊤`, and rows `1, …, n − 1` are the rows
`f 0, …, f (n − 2)` of `A`. -/
def bordered (A : Matrix (Fin m) (Fin n) ℤ) (α : Fin n → ℤ) (f : Fin (n - 1) → Fin m) :
    Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j =>
    if h : (i : ℕ) = 0 then α j else A (f ⟨(i : ℕ) - 1, by have := i.isLt; omega⟩) j

/-- **Definition 1** (p.3): `Δ^α(A) := max{|det (α⊤ ; B)| : B is an (n−1) × n submatrix of A}`,
where `B` is a row-submatrix. -/
noncomputable def deltaAlpha (A : Matrix (Fin m) (Fin n) ℤ) (α : Fin n → ℤ) : ℕ :=
  Finset.univ.sup fun f : Fin (n - 1) ↪ Fin m => (bordered A α f).det.natAbs

/-- `gcd A_I := gcd{|det M| : M is a rank(A_I) × rank(A_I) submatrix of A_I}` (p.4). For `I = ∅` the
only submatrix is the `0 × 0` one, of determinant `1`, so `gcd A_∅ = 1` as the paper specifies. -/
noncomputable def gcdMinors (A : Matrix (Fin m) (Fin n) ℤ) (I : Finset (Fin m)) : ℕ :=
  (Finset.univ : Finset ((Fin (rowRank A I) ↪ {i // i ∈ I}) × (Fin (rowRank A I) ↪ Fin n))).gcd
    fun p => (A.submatrix (fun t => (p.1 t : Fin m)) p.2).det.natAbs

/-- `max{|det (α⊤ ; A_K)| : I ⊆ K ⊆ [m], |K| = n − 1}` (p.5). `K` is the image of the injection `f`;
every ordering of `K` occurs and gives the same `|det|`. -/
noncomputable def borderedMax (A : Matrix (Fin m) (Fin n) ℤ) (α : Fin n → ℤ) (I : Finset (Fin m)) : ℕ :=
  (Finset.univ.filter fun f : Fin (n - 1) ↪ Fin m => I ⊆ Finset.univ.map f).sup
    fun f => (bordered A α f).det.natAbs

/-- `Δ^α_I(A) := (1 / gcd A_I) · max{|det (α⊤ ; A_K)| : I ⊆ K ⊆ [m], |K| = n − 1}` (p.5). -/
noncomputable def deltaAlphaI (A : Matrix (Fin m) (Fin n) ℤ) (α : Fin n → ℤ)
    (I : Finset (Fin m)) : ℝ :=
  (1 / (gcdMinors A I : ℝ)) * (borderedMax A α I : ℝ)

end ProxFlatIP


