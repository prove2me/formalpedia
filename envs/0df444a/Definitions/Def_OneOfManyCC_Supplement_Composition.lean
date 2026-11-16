-- Prove2me | Definitions.Def_OneOfManyCC_Supplement_Composition
-- name    : OneOfManyCC_Supplement_Composition
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T02:20:56.510675+00:00
-- url     : https://prove2.me/theorems/53820c82-5e0e-4c0e-a2af-c1e7fff8a677
-- title:
--   The composition $U_m\diamond\mathrm{KW}_g$ and its restriction $R_g(X)$ to a set of matrices
-- statement:
--   Let $g:\{0,1\}^n\to\{0,1\}$ and $m\ge 0$. Put $U_m=(\{0,1\}^n)^m$, the $m\times n$ Boolean matrices, and $g^m(Z)=(g(Z_1),\dots,g(Z_m))$ for the vector of values of $g$ on the rows of $Z$.
--
--   In the communication problem $U_m\diamond\mathrm{KW}_g$, Alice and Bob receive matrices $A,B\in U_m$ and must output a cell $(i,j)$ with
--   $$A_{i,j}\ne B_{i,j},$$
--   or **reject**, which is a valid answer exactly when $g^m(A)=g^m(B)$.
--
--   For a set $X\subseteq U_m$, the relation $R_g(X)$ is the same problem with both inputs restricted to $X$: Alice gets $A\in X$, Bob gets $B\in X$. Thus $U_m\diamond\mathrm{KW}_g=R_g(U_m)$.
--
--   These are the problems of Theorems 1.6, 1.7, 1.8 and 6.6; their communication complexity is the published $\mathrm{CC}$ of the mission.
--
--   **Formalization Note** Matrices are `Fin m → Fin n → Bool` (row $i$ is `Z i`). Outputs are `Option (Fin m × Fin n)`: `some (i, j)` is the 0-based cell, `none` is reject. $R_g(X)$ is a relation on the subtype `↥X`; every statement using it takes $X$ of positive size, so $X$ is nonempty there, as the paper requires.
-- source:
--   Chukhin, Kulikov, Mihajlin, Smal, Solving One of Many Instances Is Almost as Hard as Solving One, STOC 2027 submission (manuscript sha256 5d4d41dd…), §1.2, p.2 (PDF p.3); §6, p.12 (PDF p.13)

import Mathlib

namespace OneOfManyCC.Supplement

/-- **The matrices** `U_m = ({0,1}ⁿ)ᵐ`: `m` rows of `n` bits.
Chukhin, Kulikov, Mihajlin, Smal, *Solving One of Many Instances Is Almost as Hard as Solving One*, STOC 2027 submission (manuscript sha256 5d4d41dd…), §6, p.12: "put Um = ({0, 1}n)m". -/
abbrev Um (n m : ℕ) : Type := Fin m → Fin n → Bool

/-- `gᵐ(Z) = (g(Z₁), …, g(Z_m))` (§6, p.12). -/
def gm {n m : ℕ} (g : (Fin n → Bool) → Bool) (Z : Um n m) : Fin m → Bool :=
  fun i => g (Z i)

/-- **The composition** `U_m ⋄ KW_g` (§1.2, p.2): "Alice and Bob receive matrices A, B ∈ ({0, 1}n)m
and must output a cell (i, j) with Ai,j ≠ Bi,j, or reject when their vectors of row values
gm(A) = (g(A1), . . . , g(Am)) and gm(B) are equal."

**Formalization Note.** Outputs are `Option (Fin m × Fin n)`: `some (i, j)` is the cell `(i, j)`
(0-based), `none` is reject. -/
def UKW {n m : ℕ} (g : (Fin n → Bool) → Bool) :
    Um n m → Um n m → Option (Fin m × Fin n) → Prop
  | A, B, some (i, j) => A i j ≠ B i j
  | A, B, none => gm g A = gm g B

/-- **The restriction** `R_g(X)` of `U_m ⋄ KW_g` to `X × X` (§6, p.12): "for a nonempty subset
X ⊆ Um, the relation Rg(X) on X × X requires the players to output a cell (i, j) with Ai,j ≠ Bi,j,
or to reject when gm(A) = gm(B), so Um ⋄ KWg = Rg(Um)".

**Formalization Note.** Both players' inputs are the subtype `↥X`. Every statement using it takes `X`
of positive size, so `X` is nonempty there. -/
def Rg {n m : ℕ} (g : (Fin n → Bool) → Bool) (X : Set (Um n m)) :
    X → X → Option (Fin m × Fin n) → Prop :=
  fun A B o => UKW g A.1 B.1 o

end OneOfManyCC.Supplement


