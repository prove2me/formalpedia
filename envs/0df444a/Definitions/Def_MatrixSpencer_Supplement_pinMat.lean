-- Prove2me | Definitions.Def_MatrixSpencer_Supplement_pinMat
-- name    : MatrixSpencer_Supplement_pinMat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-15T19:29:10.750177+00:00
-- url     : https://prove2.me/theorems/688f67e0-87c7-4018-896d-6bf924868251
-- title:
--   The rank-one pinching blocks $a(g)$, $b(g)$, $C(g)$ with respect to $\mathrm{span}\{v\}\oplus v^\perp$
-- statement:
--   Let $A_1,\dots,A_n$ be $d\times d$ matrices and let $v\in\mathbb R^d$ be a unit vector. Choose an orthogonal matrix $Q$ whose first column is $v$; its remaining columns form an orthonormal basis of $v^\perp$. In this basis each matrix splits into blocks with respect to $\mathbb R^d=\mathrm{span}\{v\}\oplus v^\perp$,
--   $$Q^\top A_iQ=\begin{pmatrix}a_i & u_i^\top\\ u_i & D_i\end{pmatrix},$$
--   with $a_i=v^\top A_iv$ a scalar, $u_i\in v^\perp\cong\mathbb R^{d-1}$ and $D_i$ a $(d-1)\times(d-1)$ matrix. For $g\in\mathbb R^n$ set
--   $$a(g)=\tfrac14\sum_i g_ia_i,\qquad b(g)=\tfrac14\sum_i g_iu_i,\qquad C(g)=\tfrac14\sum_i g_iD_i,$$
--   the blocks of the matrix $\tfrac14\sum_i g_i\,Q^\top A_iQ$.
--
--   These are the objects of the one-step pinching bound (Theorem B.2): pinching removes the off-diagonal block $b$ and leaves $a\oplus C$.
--
--   **Formalization Note** The dimension is written $d=m+1$. The definitions take $Q$ as an argument; the quantities of Theorem B.2 do not depend on which orthonormal basis of $v^\perp$ is chosen.
-- source:
--   E. Akbas, S. Sra, A Proof of the Matrix Spencer Conjecture, arXiv:2608.28816 (held file sha256 3e56f6a1…), Theorem B.2, p.17 (PDF p.19); block notation p.18 (PDF p.20)

import Mathlib
import Definitions.Def_RBMSensitivity_E
import Definitions.Def_MatrixSpencer_series
open RBMSensitivity (E)

namespace MatrixSpencer.Supplement

/-- **The rank-one pinching blocks `a(g)`, `b(g)`, `C(g)` of Theorem B.2.**
Akbas, Sra, *A Proof of the Matrix Spencer Conjecture*, arXiv:2608.28816 (held file sha256 3e56f6a1…),
Theorem B.2, p.17 (PDF p.19): "Fix a unit vector v ∈ ℝᵈ and consider the block-decomposition of the
matrices Aᵢ with respect to ℝᵈ = span{v} ⊕ v^⊥, Aᵢ = (aᵢ uᵢ^⊤; uᵢ Dᵢ). Let g ∈ ℝⁿ and denote
a(g) = ¼ ∑ᵢ gᵢaᵢ, b(g) = ¼ ∑ᵢ gᵢuᵢ, and C(g) = ¼ ∑ᵢ gᵢDᵢ."

`pinMat A Q g = ¼ ∑ᵢ gᵢ (Qᵀ Aᵢ Q)` is the matrix `¼ B(g)` written in the orthonormal basis given by
the columns of `Q`; the page's "slight abuse of notation" (p.18) writes the same matrix as
`(a(g) b(g)^⊤; b(g) C(g))`.

**Formalization Note.** The dimension is `d = m + 1` (a unit vector exists only for `d ≥ 1`). The
splitting `ℝᵈ = span{v} ⊕ v^⊥` is encoded by an orthogonal matrix `Q` whose column `0` is `v`; its
columns `1, …, m` are then an orthonormal basis of `v^⊥`. In this basis `aᵢ = (Qᵀ Aᵢ Q)₀₀`, the
coordinates of `uᵢ` are `(Qᵀ Aᵢ Q)_{k+1,0}`, and `Dᵢ` is the lower-right `m × m` block. -/
noncomputable def pinMat {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  (1 / 4 : ℝ) • series (fun i => Q.transpose * A i * Q) g

/-- `a(g) = ¼ ∑ᵢ gᵢaᵢ` with `aᵢ = v^⊤Aᵢv` (Theorem B.2, p.17). -/
noncomputable def pinA {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : ℝ :=
  pinMat A Q g 0 0

/-- `b(g) = ¼ ∑ᵢ gᵢuᵢ ∈ v^⊥`, in the coordinates of the orthonormal basis of `v^⊥` given by the
columns `1, …, m` of `Q` (Theorem B.2, p.17). -/
noncomputable def pinB {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : Fin m → ℝ :=
  fun k => pinMat A Q g k.succ 0

/-- `C(g) = ¼ ∑ᵢ gᵢDᵢ`, an `m × m` (that is `(d−1) × (d−1)`) symmetric matrix acting on `v^⊥`, in
the same basis (Theorem B.2, p.17). -/
noncomputable def pinC {n m : ℕ} (A : Fin n → Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ)
    (Q : Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ) (g : E n) : Matrix (Fin m) (Fin m) ℝ :=
  (pinMat A Q g).submatrix Fin.succ Fin.succ

end MatrixSpencer.Supplement


