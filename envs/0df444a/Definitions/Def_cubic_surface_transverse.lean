-- Prove2me | Definitions.Def_cubic_surface_transverse
-- name    : cubic_surface_transverse
-- status  : Definition
-- author  : @LG
-- created : 2026-11-22T01:52:13.530002+00:00
-- url     : https://prove2.me/theorems/016b2bc5-d66f-47c5-9899-167ad16f378a
-- title:
--   Transverse zeroes of the section $s_F$
-- statement:
--   The section whose zeroes are the lines on a cubic surface, and the condition that those zeroes are transverse.
--
--   Let $F$ be a polynomial in four variables over $\mathbb{C}$, and let $G=\mathrm{Gr}(2,4)$ be the Grassmannian of lines in $\mathbb{P}^3$, identified with the $2$-dimensional linear subspaces $W\subset\mathbb{C}^4$. Huizenga's section of the bundle $E=\mathrm{Sym}^3 S^*$ is restriction of $F$ to the line,
--   $$
--   s_F(W) := F|_W.
--   $$
--   The zero locus of $s_F$ is exactly the set of lines on $V(F)$.
--
--   A zero $W$ is transverse when the derivative $ds_F:T_W G\to E_W$ is an isomorphism. In the affine chart of planes with basis $(v_0,v_1)$ and complementary directions $(p,q)$, this is the nonvanishing of the Jacobian determinant of the four coefficients of the restricted cubic. With $B$ the symmetric trilinear polarization of $F$, normalized so that $B(x,x,x)=F(x)$, that determinant is a unit in $\mathbb{C}$ times
--   $$
--   \det\begin{pmatrix}
--   B(p,v_0,v_0)&B(q,v_0,v_0)&0&0\\
--   2B(p,v_0,v_1)&2B(q,v_0,v_1)&B(p,v_0,v_0)&B(q,v_0,v_0)\\
--   B(p,v_1,v_1)&B(q,v_1,v_1)&2B(p,v_0,v_1)&2B(q,v_0,v_1)\\
--   0&0&B(p,v_1,v_1)&B(q,v_1,v_1)
--   \end{pmatrix}.
--   $$
--   The section $s_F$ has transverse zeroes when every line on $V(F)$ is a transverse zero.
--
--   This is the hypothesis the source isolates before the final count: the Chern-class computation gives the number of lines only when $s_F$ meets the zero section transversely.
--
--   **Formalization Note.** `polar3` is the polarization $B$. `polarJacDet` is the determinant displayed above (equivalently, the Jacobian determinant divided by $3^4$). `IsTransverseZero F W` quantifies the nonvanishing over every basis $(v_0,v_1)$ of $W$ and every complementary pair $(p,q)$. `HasTransverseZeroes F` says every member of `linesOf F` is a transverse zero.
-- source:
--   Jack Huizenga, answer to "In Algebraic Geometry, why are there exactly 27 straight lines on a smooth cubic surface?", Quora. Archived 2026-11-20 at https://perma.cc/38AQ-6ZCM (snapshot of https://suosuo.de/uu0jlKJ). Part II: the section $s_F(\ell):=F|_\ell$, the sentence "assuming $s_F$ has transverse zeroes", and the final Theorem.

import Definitions.Def_cubic_surface_27_layer

open MvPolynomial

namespace CubicSurface27

/-- The symmetric trilinear polarization of a polynomial, normalized so that a
homogeneous cubic `F` satisfies `polar3 F x x x = F(x)`. Explicitly,
`6 • polar3 F x y z` is the third finite difference
`F(x+y+z) − F(x+y) − F(y+z) − F(z+x) + F(x) + F(y) + F(z)`. -/
noncomputable def polar3 (F : MvPolynomial (Fin 4) ℂ) (x y z : Fin 4 → ℂ) : ℂ :=
  (6 : ℂ)⁻¹ * (eval (x + y + z) F - eval (x + y) F - eval (y + z) F - eval (z + x) F
    + eval x F + eval y F + eval z F)

/-- Jacobian determinant of the section `s_F` in the standard affine chart of
`Gr(2,4)` about the plane with basis `(v₀, v₁)` and complementary directions
`(p, q)`.

Writing `B` for `polar3 F` and `a(u,v,w) = B u v w`, the matrix is the
derivative at the origin of the four coefficients of `F` restricted to the
deformed plane, divided by `3` (a unit in `ℂ`):

```
⎡  B(p,v₀,v₀)     B(q,v₀,v₀)     0              0            ⎤
⎢  2 B(p,v₀,v₁)   2 B(q,v₀,v₁)   B(p,v₀,v₀)     B(q,v₀,v₀)   ⎥
⎢  B(p,v₁,v₁)     B(q,v₁,v₁)     2 B(p,v₀,v₁)   2 B(q,v₀,v₁) ⎥
⎣  0              0              B(p,v₁,v₁)     B(q,v₁,v₁)   ⎦
```

It is nonzero if and only if `ds_F` is an isomorphism on this chart. -/
noncomputable def polarJacDet (F : MvPolynomial (Fin 4) ℂ)
    (v0 v1 p q : Fin 4 → ℂ) : ℂ :=
  let B : (Fin 4 → ℂ) → (Fin 4 → ℂ) → (Fin 4 → ℂ) → ℂ := polar3 F
  let a00 := B p v0 v0
  let a01 := B q v0 v0
  let a12 := B p v0 v1
  let a13 := B q v0 v1
  let a20 := B p v1 v1
  let a21 := B q v1 v1
  (!![a00, a01, 0, 0;
      2 * a12, 2 * a13, a00, a01;
      a20, a21, 2 * a12, 2 * a13;
      0, 0, a20, a21] : Matrix (Fin 4) (Fin 4) ℂ).det

/-- A line `W` on `V(F)` is a transverse zero of `s_F` when, in every affine
chart of the Grassmannian centered at `W`, the Jacobian determinant of `s_F`
is nonzero. Equivalently, `ds_F : T_W Gr(2,4) → E_W` is an isomorphism. -/
def IsTransverseZero (F : MvPolynomial (Fin 4) ℂ) (W : Submodule ℂ (Fin 4 → ℂ)) : Prop :=
  ∀ v0 v1 p q : Fin 4 → ℂ,
    v0 ∈ W → v1 ∈ W →
    LinearIndependent ℂ ![v0, v1, p, q] →
    polarJacDet F v0 v1 p q ≠ 0

/-- The section `s_F` has transverse zeroes: every line on `V(F)` is a
transverse zero of `s_F`. -/
def HasTransverseZeroes (F : MvPolynomial (Fin 4) ℂ) : Prop :=
  ∀ W : Submodule ℂ (Fin 4 → ℂ), W ∈ linesOf F → IsTransverseZero F W

end CubicSurface27


