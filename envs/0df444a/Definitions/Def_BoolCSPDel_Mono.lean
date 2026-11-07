-- Prove2me | Definitions.Def_BoolCSPDel_Mono
-- name    : BoolCSPDel_Mono
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:55:45.933723+00:00
-- url     : https://prove2.me/theorems/f301a56c-8db1-4c10-9812-cac60f134c09
-- title:
--   Monomial coordinates, Gram matrices and the Loewner order
-- statement:
--   The sets $T\subseteq[n]$ with $|T|\le d$ index the multilinear monomials of degree at most $d$, and $\phi(\alpha)=(\prod_{j\in T}\alpha_j)_T$. For a matrix $B$ and frequencies $f$, $G=B^\top\mathrm{diag}(f)^2B$; for weights, $W=\sum_{i\in S}w_ib_ib_i^\top$. $U\preceq V$ means $x^\top Ux\le x^\top Vx$ for every real $x$. $B$ **represents** the constraints if $b_C^\top\phi(\alpha)=0$ exactly when $\alpha$ satisfies $C$.
--
--   These objects turn exact sparsification into a matrix inequality.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), proof of Lemma 5.2, pp.30–31; §3.5, p.23

import Mathlib
import Definitions.Def_BoolCSPDel_Con

namespace BoolCSPDel

/-- **Monomial coordinates and Gram matrices.** Bandekar, Sharma, Velusamy, STOC 2027 submission
(manuscript sha256 15f83519…), proof of Lemma 5.2, p.30: the sets `T ⊆ [n]`, `|T| ≤ d`, indexing the
multilinear monomials of degree at most `d`, including the constant monomial. -/
abbrev Mono (n d : ℕ) : Type := {T : Finset (Fin n) // T.card ≤ d}

/-- p.30: `ϕ(α) = (∏_{j ∈ T} α_j)_T`. -/
def phi {n d : ℕ} (α : Fin n → Bool) (T : Mono n d) : ℝ :=
  ∏ j ∈ T.1, if α j then 1 else 0

/-- §3.5, p.23: `U ⪯ V` means `xᵀUx ≤ xᵀVx` for every real `x`. -/
def LoewnerLE {κ : Type} [Fintype κ] (U V : Matrix κ κ ℝ) : Prop :=
  ∀ x : κ → ℝ, x ⬝ᵥ (U.mulVec x) ≤ x ⬝ᵥ (V.mulVec x)

/-- The row `b_i` as a real vector. -/
def rowR {ι κ : Type} (B : Matrix ι κ ℤ) (i : ι) : κ → ℝ := fun j => (B i j : ℝ)

/-- `G = Bᵀ diag(f)² B`. -/
noncomputable def gramR {ι κ : Type} [Fintype ι] (B : Matrix ι κ ℤ) (f : ι → ℤ) : Matrix κ κ ℝ :=
  Matrix.of fun j j' => ∑ i, (f i : ℝ) ^ 2 * rowR B i j * rowR B i j'

/-- `W = Σ_{i ∈ S} w_i b_i b_iᵀ`. -/
noncomputable def weightedSum {ι κ : Type} (B : Matrix ι κ ℤ) (S : Finset ι) (w : ι → ℝ) :
    Matrix κ κ ℝ :=
  ∑ i ∈ S, w i • Matrix.vecMulVec (rowR B i) (rowR B i)

/-- p.31: the row of `C` is the coefficient vector of its constraint polynomial: `b_Cᵀϕ(α)` vanishes
exactly when `α` satisfies `C`. -/
def IsPolyRep {k : ℕ} {Γ : Lang k} {n d : ℕ} (B : Matrix (Con Γ (Fin n)) (Mono n d) ℤ) : Prop :=
  ∀ (C : Con Γ (Fin n)) (α : Fin n → Bool), rowR B C ⬝ᵥ phi α = 0 ↔ SatBy C α

end BoolCSPDel


