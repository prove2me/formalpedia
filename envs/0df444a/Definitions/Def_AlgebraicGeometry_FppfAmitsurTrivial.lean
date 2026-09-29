-- Prove2me | Definitions.Def_AlgebraicGeometry_FppfAmitsurTrivial
-- name    : AlgebraicGeometry_FppfAmitsurTrivial
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:24.773853+00:00
-- url     : https://prove2.me/theorems/7392d882-98e3-5770-9853-792190215ec4
-- title:
--   Amitsur triviality of an fppf abelian sheaf along Spec A → Spec ℤ
-- statement:
--   For an fppf sheaf $F$ of abelian groups on the big fppf site of schemes (an object of `Sheaf Scheme.fppfTopology AddCommGrpCat`) and a commutative ring $A$, [`AlgebraicGeometry.Scheme.FppfAmitsurTrivial F A`](../def/AlgebraicGeometry_FppfAmitsurTrivial.html#L9) asserts the vanishing of the first cohomology of the one-step Amitsur (Čech) complex attached to the single ring map $\mathbb Z \to A$. The rings and face maps are those of the descent-coface package instantiated at $\mathbb Z \to A$: $R_2 = A \otimes_{\mathbb Z} A$ and $R_3 = A \otimes_{\mathbb Z} (A \otimes_{\mathbb Z} A)$, with $i_1, i_2 \colon A \to R_2$ given by $a \mapsto a \otimes 1$ and $a \mapsto 1 \otimes a$, and $c_{12}, c_{23}, c_{13} \colon R_2 \to R_3$ given on generators by $x \otimes y \mapsto x \otimes (y \otimes 1)$, $x \otimes y \mapsto 1 \otimes (x \otimes y)$ and $x \otimes y \mapsto x \otimes (1 \otimes y)$. Applying $\mathrm{Spec}$ and passing to the opposite category turns each of these into a restriction map on sections of the presheaf underlying $F$. The predicate then says: for every section $c$ of $F$ over $\mathrm{Spec}(A \otimes_{\mathbb Z} A)$ satisfying the additively written cocycle identity
--   $$c_{12}^{*}c + c_{23}^{*}c = c_{13}^{*}c$$
--   in $F(\mathrm{Spec}\,R_3)$, there is a section $b$ of $F$ over $\mathrm{Spec}\,A$ with $c = i_1^{*}b - i_2^{*}b$; that is, every $1$-cocycle is a coboundary, with this sign convention. No flatness, finite presentation or faithfulness hypothesis on $\mathbb Z \to A$ is imposed in the definition: the predicate is stated for an arbitrary commutative ring $A$, and is a condition on the chosen presentation $\mathbb Z \to A$ rather than on a covering family of $\mathrm{Spec}\,\mathbb Z$. The sheaf $F$ enters only through its underlying presheaf of abelian groups evaluated on affine schemes.
--
--   **Relation to Mathlib.** Mathlib supplies the big fppf topology on schemes, sheaves of abelian groups on it, and the tensor-product inclusions used to build the cofaces; the Amitsur-triviality predicate itself is the project's own.
--
--   **Where it is used.** The predicate packages the hypothesis used in the passage from Čech triviality along faithfully flat finitely presented covers to the splitting of extensions of fppf abelian sheaves, and is the form in which the coefficient computations for $\mathbb G_m$ and for the constant sheaf $\mathbb Z/p$ over $\mathrm{Spec}\,\mathbb Z$ are recorded; these feed the flat-cohomology vanishing statements used in the Galois-cohomological part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_FppfAmitsurTrivial.lean

import Definitions.Def_Algebra_DescentCofaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

open CategoryTheory Opposite Algebra.DescentCofaces

def FppfAmitsurTrivial (F : Sheaf Scheme.fppfTopology.{0} AddCommGrpCat.{1})
    (A : Type) [CommRing A] : Prop :=
  ∀ c : ToType (F.obj.obj (op (Spec (R₂ ℤ A)))),
    F.obj.map (Spec.map (c₁₂ ℤ A)).op c + F.obj.map (Spec.map (c₂₃ ℤ A)).op c =
        F.obj.map (Spec.map (c₁₃ ℤ A)).op c →
      ∃ b : ToType (F.obj.obj (op (Spec (CommRingCat.of A)))),
        c = F.obj.map (Spec.map (i₁ ℤ A)).op b - F.obj.map (Spec.map (i₂ ℤ A)).op b

end AlgebraicGeometry.Scheme


