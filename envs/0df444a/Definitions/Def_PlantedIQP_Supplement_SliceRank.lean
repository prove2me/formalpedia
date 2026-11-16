-- Prove2me | Definitions.Def_PlantedIQP_Supplement_SliceRank
-- name    : PlantedIQP_Supplement_SliceRank
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:01:59.509594+00:00
-- url     : https://prove2.me/theorems/b8e18d29-3210-4a9a-939e-b51332205dd5
-- title:
--   Trilinear forms, slice rank $\mathrm{SR}(P)\le r$ and independent triples of spaces
-- statement:
--   Let $F$ be a field and let $P(x,y,z)=\sum_{a=1}^{\ell}\sum_{b=1}^{m}\sum_{c=1}^{n}p_{abc}\,x_ay_bz_c$ be a **trilinear form** in three sets of variables $x$ ($\ell$ variables), $y$ ($m$) and $z$ ($n$). It is given by its coefficient tensor $p=(p_{abc})$, and its value at $(u,v,w)\in F^\ell\times F^m\times F^n$ is $P(u,v,w)=\sum p_{abc}u_av_bw_c$.
--
--   A **slice decomposition** with $(r_x,r_y,r_z)$ terms consists of linear forms $\ell_{x,i}(x)$ and bilinear forms $B_{x,i}(y,z)$ for $i\le r_x$, linear forms $\ell_{y,j}(y)$ and bilinear forms $B_{y,j}(x,z)$ for $j\le r_y$, and linear forms $\ell_{z,k}(z)$ and bilinear forms $B_{z,k}(x,y)$ for $k\le r_z$, such that
--
--   $$
--   P(x,y,z)=\sum_{i=1}^{r_x}\ell_{x,i}(x)B_{x,i}(y,z)+\sum_{j=1}^{r_y}\ell_{y,j}(y)B_{y,j}(x,z)+\sum_{k=1}^{r_z}\ell_{z,k}(z)B_{z,k}(x,y)
--   $$
--
--   as polynomials. The **slice rank** is the least $r_x+r_y+r_z$ over all slice decompositions, and $\mathrm{SR}(P)\le r$ means that some slice decomposition has $r_x+r_y+r_z\le r$.
--
--   An **independent triple of spaces** of $P$ is a triple of subspaces $V_x\le F^\ell$, $V_y\le F^m$, $V_z\le F^n$ with $P(V_x,V_y,V_z)=\{0\}$, i.e. $P(u,v,w)=0$ for all $u\in V_x$, $v\in V_y$, $w\in V_z$. Its dimension is $\dim V_x+\dim V_y+\dim V_z$.
--
--   These are the two sides of Theorem 53. Slice rank is the trilinear counterpart of the symmetric slice rank of cubic forms that Section 4 uses for the NP-hardness of the independent space problem.
--
--   **Formalization Note** Linear forms are coefficient vectors and bilinear forms coefficient matrices. The decomposition identity is required coefficientwise, which is equality of polynomials. Only the predicate $\mathrm{SR}(P)\le r$ is defined, not the minimum.
-- source:
--   Bläser, Gullans, Hangleiter, Liu, Qiao, Verifiable quantum advantage based on polynomials with planted structures, arXiv:2609.39918 (sha256 6e261694…), Definition 49 and Definition 51, p.29 (Section 4.1; arbitrary field, p.28)

import Mathlib

set_option autoImplicit false

namespace PlantedIQP.Supplement

/-!
# Trilinear forms, slice decompositions, slice rank `≤ r`, independent triples of spaces

Bläser, Gullans, Hangleiter, Liu, Qiao, *Verifiable quantum advantage based on polynomials with
planted structures*, arXiv:2609.39918 (sha256 6e261694…), Section 4.1, p.29:

* Definition 49 (Sawin and Tao): "Let P ∈ F[x, y, z] be a trilinear form. 1. A slice
  decomposition is a collection of linear forms ℓ_{x,i}(x) and bilinear forms B_{x,i}(y, z),
  1 ≤ i ≤ r_x, linear forms ℓ_{y,j}(y) and bilinear forms B_{y,j}(x, z), 1 ≤ j ≤ r_y, as well as
  linear forms ℓ_{z,k}(z) and bilinear forms B_{z,k}(x, y), 1 ≤ k ≤ r_z, such that
  P(x, y, z) = Σ_i ℓ_{x,i}(x)B_{x,i}(y, z) + Σ_j ℓ_{y,j}(y)B_{y,j}(x, z) + Σ_k ℓ_{z,k}(z)B_{z,k}(x, y).
  2. The slice rank SR(P) is the minimum r such that there is a slice decomposition as above with
  r_x + r_y + r_z ≤ r."
* Definition 51: "A trilinear form P(x, y, z) = Σ_{i=1}^ℓ Σ_{j=1}^m Σ_{k=1}^n p_{i,j,k} x_i y_j z_k
  has an independent triple of spaces of dimension h if there are spaces V_x ≤ F^ℓ, V_y ≤ F^m, and
  V_z ≤ F^n of dimensions h_x, h_y, and h_z with h_x + h_y + h_z = h such that
  P(V_x, V_y, V_z) = {0}."

Section 4 works over an arbitrary field F (p.28).

**Formalization Note.**
* A trilinear form in the variable sets `x` (`ℓ` variables), `y` (`m`), `z` (`n`) is its
  coefficient tensor `p : Fin ℓ → Fin m → Fin n → F` (a formal trilinear polynomial is determined
  by its coefficients). A linear form on `F^ℓ` is its coefficient vector `Fin ℓ → F`; a bilinear
  form on `F^m × F^n` is its coefficient matrix `Fin m → Fin n → F`.
* The decomposition identity is an identity of formal polynomials, i.e. coefficientwise:
  `p a b c = Σ_i ℓ_{x,i}(a) B_{x,i}(b, c) + Σ_j ℓ_{y,j}(b) B_{y,j}(a, c) + Σ_k ℓ_{z,k}(c) B_{z,k}(a, b)`
  (`SliceDecomp.toTensor`).
* `SliceRankLE p r` is "SR(P) ≤ r": some slice decomposition has `r_x + r_y + r_z ≤ r`. The
  minimum itself is not defined; the predicate is equivalent to it.
* `P(V_x, V_y, V_z) = {0}` is `triEval p u v w = 0` for all `u ∈ V_x`, `v ∈ V_y`, `w ∈ V_z`, where
  `triEval` evaluates the form. The dimension of the triple is the sum of the `Module.finrank`s.
-/

/-- The coefficient tensor of a trilinear form in `ℓ + m + n` variables over `F`. -/
abbrev TriTensor (F : Type*) (ℓ m n : ℕ) := Fin ℓ → Fin m → Fin n → F

/-- The value `P(u, v, w) = Σ_{a,b,c} p_{abc} u_a v_b w_c` of the trilinear form `P`. -/
def triEval {F : Type*} [Field F] {ℓ m n : ℕ} (p : TriTensor F ℓ m n)
    (u : Fin ℓ → F) (v : Fin m → F) (w : Fin n → F) : F :=
  ∑ a, ∑ b, ∑ c, p a b c * u a * v b * w c

/-- A slice decomposition with `(r_x, r_y, r_z)` terms (Definition 49.1): linear forms
`ℓ_{x,i}` on `F^ℓ` with bilinear forms `B_{x,i}` on `F^m × F^n`, linear forms `ℓ_{y,j}` on `F^m`
with bilinear forms `B_{y,j}` on `F^ℓ × F^n`, linear forms `ℓ_{z,k}` on `F^n` with bilinear forms
`B_{z,k}` on `F^ℓ × F^m`. -/
structure SliceDecomp (F : Type*) [Field F] (ℓ m n rx ry rz : ℕ) where
  /-- `ℓ_{x,i}`, a linear form in `x`. -/
  lx : Fin rx → Fin ℓ → F
  /-- `B_{x,i}`, a bilinear form in `(y, z)`. -/
  Bx : Fin rx → Fin m → Fin n → F
  /-- `ℓ_{y,j}`, a linear form in `y`. -/
  ly : Fin ry → Fin m → F
  /-- `B_{y,j}`, a bilinear form in `(x, z)`. -/
  By : Fin ry → Fin ℓ → Fin n → F
  /-- `ℓ_{z,k}`, a linear form in `z`. -/
  lz : Fin rz → Fin n → F
  /-- `B_{z,k}`, a bilinear form in `(x, y)`. -/
  Bz : Fin rz → Fin ℓ → Fin m → F

/-- The trilinear form `Σ_i ℓ_{x,i}(x)B_{x,i}(y,z) + Σ_j ℓ_{y,j}(y)B_{y,j}(x,z) +
Σ_k ℓ_{z,k}(z)B_{z,k}(x,y)` represented by a slice decomposition, as a coefficient tensor. -/
def SliceDecomp.toTensor {F : Type*} [Field F] {ℓ m n rx ry rz : ℕ}
    (D : SliceDecomp F ℓ m n rx ry rz) : TriTensor F ℓ m n :=
  fun a b c => (∑ i, D.lx i a * D.Bx i b c) + (∑ j, D.ly j b * D.By j a c) +
    ∑ k, D.lz k c * D.Bz k a b

/-- `SR(P) ≤ r` (Definition 49.2): `P` has a slice decomposition with `r_x + r_y + r_z ≤ r`. -/
def SliceRankLE {F : Type*} [Field F] {ℓ m n : ℕ} (p : TriTensor F ℓ m n) (r : ℕ) : Prop :=
  ∃ rx ry rz : ℕ, rx + ry + rz ≤ r ∧ ∃ D : SliceDecomp F ℓ m n rx ry rz, D.toTensor = p

/-- `(V_x, V_y, V_z)` is an independent triple of spaces of `P` (Definition 51):
`P(V_x, V_y, V_z) = {0}`. -/
def IsIndependentTriple {F : Type*} [Field F] {ℓ m n : ℕ} (p : TriTensor F ℓ m n)
    (Vx : Submodule F (Fin ℓ → F)) (Vy : Submodule F (Fin m → F))
    (Vz : Submodule F (Fin n → F)) : Prop :=
  ∀ u ∈ Vx, ∀ v ∈ Vy, ∀ w ∈ Vz, triEval p u v w = 0

end PlantedIQP.Supplement


