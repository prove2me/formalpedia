-- Prove2me | Definitions.Def_RPLib_S3_TateStmt
-- name    : RPLib_S3_TateStmt
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-14T16:19:49.152187+00:00
-- url     : https://prove2.me/theorems/9f7753ad-53d6-47bc-82e4-c04cd6e4f5a2
-- title:
--   Weight-two Ramanujan-Petersson library: Tate's isogeny theorem for elliptic curves over a finite field: the HYPOTHESIS
-- statement:
--   Tate's isogeny theorem for elliptic curves over a finite field: the HYPOTHESIS.
--
--   This file states, in pure Mathlib terms and WITHOUT proof, Tate's isogeny theorem for elliptic curves over a
--   finite field (J. Tate, *Endomorphisms of abelian varieties over finite fields*, Invent. Math. 2 (1966)):
--   two elliptic curves over a finite field `F` with the same number of `F`-rational points are `F`-isogenous.
--
--   The project does not prove it (it needs abelian surfaces or CM lifting, see
--   `scratch/rp/units/S3-DWS-Tate/NOTES.md`). Every result of the S3 DWS chain that needs it takes
--   `TateIsogenyStatement` as an explicit hypothesis. It is never assumed as an axiom.
--
--   * "Same number of points" is `Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point` (affine points plus the
--     point at infinity), equivalently the same trace of Frobenius `a = q + 1 - #E(F)`.
--   * "`F`-isogenous" is an `F`-algebra homomorphism `K(E') → K(E)` of function fields
--     (`WeierstrassCurve.Affine.FunctionField`, the fraction field of the coordinate ring): a nonconstant `F`-morphism
--     `E → E'`, which becomes an isogeny after a translation by an `F`-rational point.
--
--   **Formalization note.** Library module of a formalization of the Ramanujan-Petersson conjecture in weight two (Eichler-Shimura-Ihara route: the Eichler-Selberg trace formula on $S_2(\Gamma_1(M))$, the Deuring-Waterhouse-Schoof count of elliptic curves over $\mathbb F_q$ with level structure by Hurwitz class numbers, conditional on Tate's isogeny theorem in prime-to-$p$ form, the Kronecker-Hurwitz class number relation, and the Hasse-Weil bound for the components of $Y_1(M)$ by the Stepanov-Bombieri method). It contains definitions together with proved lemmas (no `sorry`; where Tate's theorem is used it is an explicit hypothesis), so that later solution files can import them.
-- source:
--   M. Deuring, Die Typen der Multiplikatorenringe elliptischer Funktionenkörper, Abh. Math. Sem. Univ. Hamburg 14 (1941), 197-272; W. C. Waterhouse, Abelian varieties over finite fields, Ann. Sci. École Norm. Sup. (4) 2 (1969), 521-560; R. Schoof, Nonsingular plane cubic curves over finite fields, J. Combin. Theory Ser. A 46 (1987), 183-211; J. Tate, Endomorphisms of abelian varieties over finite fields, Invent. Math. 2 (1966), 134-144; J. Vélu, Isogénies entre courbes elliptiques, C. R. Acad. Sci. Paris Sér. A 273 (1971), 238-241; J. H. Silverman, The Arithmetic of Elliptic Curves, 2nd ed., GTM 106, Springer 2009, Chapters III and V

import Mathlib

/-!
# Tate's isogeny theorem for elliptic curves over a finite field: the HYPOTHESIS (unit S3-DWS-Tate)

This file states, in pure Mathlib terms and WITHOUT proof, Tate's isogeny theorem for elliptic curves over a
finite field (J. Tate, *Endomorphisms of abelian varieties over finite fields*, Invent. Math. 2 (1966)):
two elliptic curves over a finite field `F` with the same number of `F`-rational points are `F`-isogenous.

The project does not prove it (it needs abelian surfaces or CM lifting, see
`scratch/rp/units/S3-DWS-Tate/NOTES.md`). Every result of the S3 DWS chain that needs it takes
`TateIsogenyStatement` as an explicit hypothesis. It is never assumed as an axiom.

* "Same number of points" is `Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point` (affine points plus the
  point at infinity), equivalently the same trace of Frobenius `a = q + 1 - #E(F)`.
* "`F`-isogenous" is an `F`-algebra homomorphism `K(E') → K(E)` of function fields
  (`WeierstrassCurve.Affine.FunctionField`, the fraction field of the coordinate ring): a nonconstant `F`-morphism
  `E → E'`, which becomes an isogeny after a translation by an `F`-rational point.
-/

set_option autoImplicit false

universe u

namespace RPLib.DWS

/-- **Tate's isogeny theorem for elliptic curves over finite fields** (statement only). Two elliptic curves over a
finite field `F` with the same number of `F`-points are `F`-isogenous: there is an `F`-algebra homomorphism from the
function field of `W'` to the function field of `W`. -/
def TateIsogenyStatement : Prop :=
  ∀ (F : Type u) [Field F] [Fintype F] (W W' : WeierstrassCurve F) [W.IsElliptic] [W'.IsElliptic],
    Nat.card W.toAffine.Point = Nat.card W'.toAffine.Point →
      Nonempty (W'.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField)

/-- Sanity check: the conclusion holds trivially for `W' = W` (the identity of the function field). -/
theorem tateIsogenyStatement_refl (F : Type u) [Field F] [Fintype F] (W : WeierstrassCurve F) :
    Nonempty (W.toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField) :=
  ⟨AlgHom.id F _⟩

end RPLib.DWS


