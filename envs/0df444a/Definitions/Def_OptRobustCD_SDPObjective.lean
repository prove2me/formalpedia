-- Prove2me | Definitions.Def_OptRobustCD_SDPObjective
-- name    : OptRobustCD_SDPObjective
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T23:49:59.56888+00:00
-- url     : https://prove2.me/theorems/59187d6a-2c8b-401d-a1dc-54c40c0aab1c
-- title:
--   Density matrices $\mathcal S$, the set $\mathcal D_K$, $\mathrm{dist}_1$ and the objective $F(X)=\langle A,X\rangle+P\,\mathrm{dist}_1(\mathrm{diag}X,\mathcal D_K)$
-- statement:
--   Let $n\ge2$ and $K\ge1$ (§8):
--   $$\mathcal S=\{X\in\mathbb R^{n\times n}:X\succeq0,\ \mathrm{Tr}X=1\},\qquad \mathcal D_K=\{q\in\mathbb R^n:\|q\|_2^2\le K/n\},$$
--   $\langle B,C\rangle=\mathrm{Tr}(B^TC)$, $\mathrm{dist}_1(p,D)=\inf_{q\in D}\|p-q\|_1$, and for a matrix $A$ and $P>0$
--   $$F(X)=\langle A,X\rangle+P\cdot\mathrm{dist}_1(\mathrm{diag}X,\mathcal D_K).$$
--   $\min_{\mathcal S}F$ is the minimum of $F$ over $\mathcal S$. A factor $Z\in\mathbb R^{n\times r}$ is output as $[r,Z_{0,0},\dots,Z_{0,r-1},Z_{1,0},\dots]$.
--
--   **Formalization Note** $\mathrm{dist}_1$ and $\min_{\mathcal S}F$ are real infima; $0\in\mathcal D_K$ and $\mathcal S$ is nonempty and compact for $n\ge1$, so both are true infima and the second is attained.
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), §8 p.37 (pdf p.39)

import Mathlib

namespace OptRobustCD

/-!
# The density matrices `S`, the set `D_K`, `dist_1`, and the objective `F`

Hopkins, Hua, Mohanty, Rajaraman, Steurer, *Optimal Robust Community Detection*, STOC 2027
submission (manuscript of November 3, 2026, sha256 3d287d54…), §8, p.37 (pdf p.39): "Let `n` be an
integer with `n ⩾ 2`. For `K ⩾ 1`, define `S := {X ∈ R^{n×n} : X ⪰ 0, Tr X = 1}`,
`D_K := {q ∈ R^n : ∥q∥²_2 ⩽ K/n}`. … For matrices `B, C`, write `⟨B, C⟩ = Tr(B^T C)`. For `p ∈ R^n`
and `D ⊆ R^n`, write `dist_1(p, D) = inf_{q∈D} ∥p − q∥_1`", and (Theorems 8.1, 8.2)
`F(X) = ⟨A, X⟩ + P · dist_1(diag X, D_K)`.

**Formalization Note.**
* `X ⪰ 0` is `Matrix.PosSemidef` (which includes symmetry).
* `dist_1` and `min_S F` are real infima (`sInf`). `D_K` contains `0`, and `∥·∥_1 ⩾ 0`, so `dist_1`
  is a true infimum. For `n ⩾ 1`, `S` is nonempty and compact and `F` is continuous on it, so
  `minObj` is the attained minimum (the paper writes `min_S F`). The statements using them carry
  the standing assumption `n ⩾ 2`.
* `gramOfList n l` reads a factor `Z ∈ R^{n×r}` from the output list `[r, Z_{0,0}, …, Z_{0,r−1},
  Z_{1,0}, …]` (row by row) and returns `ZZ^T`; it is used only where the output is known to have
  this shape.
-/

open Finset

/-- `S = {X ∈ R^{n×n} : X ⪰ 0, Tr X = 1}`. -/
def densitySet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {X | X.PosSemidef ∧ X.trace = 1}

/-- `D_K = {q ∈ R^n : ∥q∥²_2 ⩽ K/n}`. -/
def ballDK (n : ℕ) (K : ℝ) : Set (Fin n → ℝ) := {q | ∑ i, q i ^ 2 ≤ K / n}

/-- `dist_1(p, D) = inf_{q∈D} ∥p − q∥_1`. -/
noncomputable def dist1 {n : ℕ} (p : Fin n → ℝ) (D : Set (Fin n → ℝ)) : ℝ :=
  sInf ((fun q => ∑ i, |p i - q i|) '' D)

/-- `F(X) = ⟨A, X⟩ + P · dist_1(diag X, D_K)`, with `⟨A, X⟩ = Tr(A^T X)`. -/
noncomputable def objF {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P K : ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (A.transpose * X).trace + P * dist1 (fun i => X i i) (ballDK n K)

/-- `min_S F`, the infimum of `F` over the density matrices. -/
noncomputable def minObj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (P K : ℝ) : ℝ :=
  sInf (objF A P K '' densitySet n)

/-- `Z Z^T` for the factor `Z ∈ R^{n×r}` written as `[r, Z_{0,0}, …, Z_{0,r−1}, Z_{1,0}, …]`. -/
noncomputable def gramOfList (n : ℕ) (l : List ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  let r : ℕ := ⌊l.headD 0⌋₊
  fun i j => ∑ k ∈ Finset.range r,
    l.getD (1 + (i : ℕ) * r + k) 0 * l.getD (1 + (j : ℕ) * r + k) 0

/-- `l` is `[r, Z_{0,0}, …, Z_{0,r−1}, Z_{1,0}, …, Z_{n−1,r−1}]` for the matrix `Z ∈ R^{n×r}`. -/
def FactorCode (n r : ℕ) (Z : Matrix (Fin n) (Fin r) ℝ) (l : List ℝ) : Prop :=
  l = (r : ℝ) :: (List.ofFn fun i : Fin n => List.ofFn fun k : Fin r => Z i k).flatten

end OptRobustCD


