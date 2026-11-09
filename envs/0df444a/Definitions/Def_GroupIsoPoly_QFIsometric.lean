-- Prove2me | Definitions.Def_GroupIsoPoly_QFIsometric
-- name    : GroupIsoPoly_QFIsometric
-- status  : Definition
-- author  : @iris
-- created : 2026-11-09T02:51:57.370704+00:00
-- url     : https://prove2.me/theorems/357fdbd1-2052-4b92-bbb7-861078e239c5
-- title:
--   Isometry of tuples of quadratic forms
-- statement:
--   Let $(f_1,\dots,f_m)$ and $(g_1,\dots,g_m)$ be tuples of polynomials in $\mathbb F_q[x_1,\dots,x_n]$. For $A=(a_{i,j})\in\mathrm{GL}(n,q)$ put
--   $$
--   (g\circ A)(x_1,\dots,x_n)=g\Big(\sum_j a_{1,j}x_j,\;\dots,\;\sum_j a_{n,j}x_j\Big).
--   $$
--   The tuples are **isometric** if there is $A\in\mathrm{GL}(n,q)$ with $f_i=g_i\circ A$ for every $i\in[m]$ (Definition 11); for quadratic forms (homogeneous quadratic polynomials) this is the Quadratic Form Tuple Isometry problem.
--
--   **Formalization Note** $g\circ A$ is the substitution $x_k\mapsto\sum_j a_{k,j}x_j$ (`MvPolynomial.bind₁`). Definition 11 (p.27) and Definition 2 (p.2) both print $\sum_j a_{n,j}x_n$ in the last argument, against $\sum_j a_{1,j}x_j$ in the first; it is read as $\sum_j a_{n,j}x_j$, so that $g\circ A$ is the linear substitution $x\mapsto Ax$ in every argument. Homogeneity is a hypothesis of the theorems that use this relation.
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 11, p.27 (PDF p.31)

import Mathlib

set_option autoImplicit false

namespace GroupIsoPoly

open MvPolynomial

/-- `g ∘ A`: the substitution `x_k ↦ Σ_j a_{k,j} x_j` in a polynomial in `n` variables. -/
noncomputable def linSubst {K : Type*} [CommRing K] {n : ℕ} (g : MvPolynomial (Fin n) K)
    (A : Matrix (Fin n) (Fin n) K) : MvPolynomial (Fin n) K :=
  bind₁ (fun k => ∑ j, C (A k j) * X j) g

/-- **Isometry of tuples of quadratic forms.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Definition 11, p.27 (PDF p.31): "Let (f1, . . . , fm)
and (g1, . . . , gm) be two tuples of quadratic forms (homogeneous quadratic polynomials) in
Fq[x1, . . . , xn]. We say that they are isometric if there exists A = (a_{i,j}) ∈ GL(n, q) such that
for any i ∈ [m], fi = gi ◦ A, where (gi ◦ A)(x1, . . . , xn) = gi(Σ_j a_{1,j}x_j, . . . , Σ_j a_{n,j}x_n)."

`QFIsometric f g` says that some invertible `A` has `f_i = g_i ∘ A` for every `i`.

**Formalization Note.** Both Definition 11 (p.27) and Definition 2 (p.2) print `Σ_j a_{n,j} x_n` in
the last argument, against `Σ_j a_{1,j} x_j` in the first; it is read as `Σ_j a_{n,j} x_j`, so that
`g ∘ A` is the linear substitution `x ↦ A x` in every argument. Homogeneity of degree 2 is a
hypothesis of the theorems, not part of this relation. -/
def QFIsometric {K : Type*} [CommRing K] {n m : ℕ} (f g : Fin m → MvPolynomial (Fin n) K) : Prop :=
  ∃ A : GL (Fin n) K, ∀ i, f i = linSubst (g i) (A : Matrix (Fin n) (Fin n) K)

end GroupIsoPoly


