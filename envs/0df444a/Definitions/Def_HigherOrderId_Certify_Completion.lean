-- Prove2me | Definitions.Def_HigherOrderId_Certify_Completion
-- name    : HigherOrderId_Certify_Completion
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T04:14:50.37923+00:00
-- url     : https://prove2.me/theorems/0651d8ff-3f43-4887-b046-f89f27188b9a
-- title:
--   The completion map D_U on Sym_m, its singular values, and the weighted outer-product frame G_w, S_w, U_w
-- statement:
--   For a $d\times m$ matrix $U$ with rows $u_a^\top$, the **completion map** is $D_U:\mathrm{Sym}_m\to\mathbb R^d$, $[D_U(B)]_a=u_a^\top Bu_a$, i.e. $D_U(B)=\operatorname{diag}(UBU^\top)$. $\mathrm{Sym}_m$ carries the Frobenius inner product, with orthonormal basis $E_{ii}$ and $(E_{ij}+E_{ji})/\sqrt2$ ($i<j$), and $\mathbb R^d$ the Euclidean one; the $t=m(m+1)/2$ **singular values** $a_j$ of $D_U$ are taken with respect to these norms. $D_U$ has **full column rank** when it is injective on $\mathrm{Sym}_m$.
--
--   For $m\ge1$, $t\le d$ and $1\le w\le m$, $G_w\in\mathbb R^{d\times m}$ has the $t$ nonzero rows $\sqrt w\,e_i^\top$ ($i\in[m]$) and $(e_i+e_j)^\top$ ($i<j$), all other rows zero, and
--   $$S_w=G_w^\top G_w,\qquad U_w=G_wS_w^{-1/2}.$$
--
--   **Formalization Note.** `DUmat U` is the $d\times t$ matrix of $D_U$ in the orthonormal basis of $\mathrm{Sym}_m$ (indexed by `SymIdx m = {(i,j) // i ≤ j}`); `singVals U j` is the square root of the `j`-th eigenvalue of `DUmat Uᴴ * DUmat U` (zeros included). The $t$ nonzero rows of $G_w$ are indexed by `FrameRows m` and placed in rows `ι r` by an injection `ι : FrameRows m ↪ Fin d` (the paper puts them first, in the order above; any placement is allowed here). $S_w^{-1/2}$ is `(CFC.sqrt S_w)⁻¹`.
-- source:
--   Zhang, Yan, Qiao, Yu, The Higher-Order Identifiability Paradox: Learning and Certifying Hypergraph Order, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 23, Eqs. (63)–(65)

import Mathlib
import Definitions.Def_HigherOrderId_Certify_Model

open Matrix
open scoped MatrixOrder

namespace HigherOrderId.Certify

/-!
# The completion map D_U on Sym_m, its singular values, and the weighted outer-product frame

Zhang, Yan, Qiao, Yu, *The Higher-Order Identifiability Paradox: Learning and Certifying
Hypergraph Order*, STOC 2027 submission (manuscript sha256 7e0ce916…), p. 23, Eqs. (63)–(65).

* `DU U B` is `D_U(B) = diag(U B Uᵀ)`, i.e. `[D_U(B)]_a = u_aᵀ B u_a` with `u_aᵀ` the `a`-th row
  of the `d × m` matrix `U`.
* `Sym_m` carries the Frobenius inner product. Its orthonormal basis `symBasis` is indexed by
  `SymIdx m = {(i, j) : i ≤ j}`: `E_ii`, and `(E_ij + E_ji)/√2` for `i < j`. `DUmat U` is the
  `d × t` matrix of `D_U` in that basis (`t = m(m+1)/2`), and the singular values `a_j` of `D_U`
  are the square roots of the eigenvalues of `DUmat Uᵀ DUmat U`, indexed by `SymIdx m`.
* `FullColRank U`: `D_U` is injective on `Sym_m`.
* The frame (63)–(64): the `t` nonzero rows `√w e_iᵀ` (`i ∈ [m]`) and `(e_i + e_j)ᵀ`
  (`i < j`) are indexed by `FrameRows m` and placed in the rows of a `d × m` matrix by an
  injection `ι : FrameRows m ↪ Fin d`; every other row is zero. `S_w = G_wᵀ G_w` and
  `U_w = G_w S_w^{-1/2}`, with `S_w^{-1/2} = (CFC.sqrt S_w)⁻¹`.
-/

/-- The completion map `D_U(B) = diag(U B Uᵀ)`. -/
def DU {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) (B : Matrix (Fin m) (Fin m) ℝ) : Fin d → ℝ :=
  fun a => (U * B * Uᵀ) a a

/-- Index set `{(i, j) : i ≤ j}` of the orthonormal basis of `Sym_m`. -/
abbrev SymIdx (m : ℕ) := {p : Fin m × Fin m // p.1 ≤ p.2}

/-- The Frobenius-orthonormal basis of `Sym_m`: `E_ii` and `(E_ij + E_ji)/√2` for `i < j`. -/
noncomputable def symBasis {m : ℕ} (p : SymIdx m) : Matrix (Fin m) (Fin m) ℝ :=
  if p.1.1 = p.1.2 then Matrix.single p.1.1 p.1.1 1
  else (1 / Real.sqrt 2) • (Matrix.single p.1.1 p.1.2 1 + Matrix.single p.1.2 p.1.1 1)

/-- The matrix of `D_U : Sym_m → ℝ^d` in the orthonormal basis `symBasis`. -/
noncomputable def DUmat {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) :
    Matrix (Fin d) (SymIdx m) ℝ :=
  fun a p => DU U (symBasis p) a

/-- The singular values `a_j` of `D_U` (Frobenius norm on `Sym_m`, Euclidean norm on `ℝ^d`),
indexed by `SymIdx m`, zeros included. -/
noncomputable def singVals {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) : SymIdx m → ℝ :=
  fun j => Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self (DUmat U)).eigenvalues j)

/-- `D_U` has full column rank: it is injective on `Sym_m`. -/
def FullColRank {d m : ℕ} (U : Matrix (Fin d) (Fin m) ℝ) : Prop :=
  ∀ B : Matrix (Fin m) (Fin m) ℝ, B.IsSymm → DU U B = 0 → B = 0

/-- Index set of the `t` nonzero rows of the frame (63). -/
abbrev FrameRows (m : ℕ) := Fin m ⊕ {p : Fin m × Fin m // p.1 < p.2}

/-- The nonzero rows of (63): `√w e_iᵀ` and `(e_i + e_j)ᵀ` (`i < j`). -/
noncomputable def frameRow {m : ℕ} (w : ℝ) : FrameRows m → Fin m → ℝ
  | .inl i => fun c => if c = i then Real.sqrt w else 0
  | .inr p => fun c => if c = p.1.1 ∨ c = p.1.2 then 1 else 0

/-- `G_w ∈ ℝ^{d×m}`: the rows of (63) placed in rows `ι r`, all other rows zero. -/
noncomputable def Gw {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) : Matrix (Fin d) (Fin m) ℝ :=
  fun a c => ∑ r, if ι r = a then frameRow w r c else 0

/-- `S_w = G_wᵀ G_w` (64). -/
noncomputable def Sw {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (Gw ι w)ᵀ * Gw ι w

/-- `U_w = G_w S_w^{-1/2}` (64). -/
noncomputable def Uw {d m : ℕ} (ι : FrameRows m ↪ Fin d) (w : ℝ) : Matrix (Fin d) (Fin m) ℝ :=
  Gw ι w * (CFC.sqrt (Sw ι w))⁻¹

end HigherOrderId.Certify


