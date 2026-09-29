-- Prove2me | Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
-- name    : AlgebraicGeometry_RelativePic0DesignationBaseChange
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/44306520-ece0-59e2-aa4a-0e56f37b9ad3
-- title:
--   Base change of a relative Pic0 designation
-- statement:
--   Fix a commutative ring $R$, a scheme $C$ and a morphism $c\colon C\to\operatorname{Spec}R$. A term of the project's structure `RelativePic0Designation R c` consists of a scheme $P$, a morphism `toBase`$\colon P\to\operatorname{Spec}R$, a morphism `zeroSection`$\colon\operatorname{Spec}R\to P$, and the field `zeroSection_toBase` asserting that `zeroSection` followed by `toBase` is the identity of $\operatorname{Spec}R$; that is, a pointed scheme over $\operatorname{Spec}R$, designated as a model of $\mathrm{Pic}^0_{C/R}$, with the curve morphism $c$ appearing only as an index of the structure and not constrained by its fields. This module defines, for such a designation $D$ and an $R$-algebra $R'$, the designation $D_{R'}$ over $R'$ for the base-changed morphism `SmoothProperCurve.baseChange R c R'`, namely $\operatorname{pr}_2\colon C\times_{\operatorname{Spec}R}\operatorname{Spec}R'\to\operatorname{Spec}R'$. Its underlying scheme is the pullback of `D.toBase` along `specMap R R'`$\colon\operatorname{Spec}R'\to\operatorname{Spec}R$ (the morphism induced by the algebra map), its structure morphism is the second projection of that pullback, and its zero section is the morphism into the pullback determined by $\operatorname{Spec}R'\to\operatorname{Spec}R$ followed by `D.zeroSection` on the first factor and the identity on the second; the section condition is the corresponding projection identity. Four lemmas record these components: the underlying scheme, the structure morphism and the zero section are as just described, and the new zero section composed with the first projection equals `specMap R R'` followed by `D.zeroSection`.
--
--   **Relation to Mathlib.** Mathlib has no notion of a relative $\mathrm{Pic}^0$ or relative Jacobian; `RelativePic0Designation` and its base change are the project's own. The fibre product used is Mathlib's chosen pullback of schemes.
--
--   **Where it is used.** This supplies the vocabulary in which the relative Jacobian of a pointed smooth proper curve is asserted to be compatible with base change, so that a designation over a base ring can be transported to an $R$-algebra — for instance to a field of geometric points or to the factors of a decomposition of the base — in the good-reduction analysis of the Jacobians $J_1(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativePic0DesignationBaseChange.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve

namespace GoodReductionJacobian.RelativePic0Designation

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}

abbrev baseChange (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R'] :
    RelativePic0Designation R' (SmoothProperCurve.baseChange R c R') where
  P := pullback D.toBase (specMap R R')
  toBase := pullback.snd D.toBase (specMap R R')
  zeroSection := pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
    (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp])
  zeroSection_toBase := pullback.lift_snd _ _ _

variable (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']

theorem baseChange_P : (D.baseChange R').P = pullback D.toBase (specMap R R') := rfl

theorem baseChange_toBase : (D.baseChange R').toBase = pullback.snd D.toBase (specMap R R') := rfl

theorem baseChange_zeroSection :
    (D.baseChange R').zeroSection = pullback.lift (specMap R R' ≫ D.zeroSection) (𝟙 _)
      (by rw [Category.assoc, D.zeroSection_toBase, Category.comp_id, Category.id_comp]) := rfl

theorem baseChange_zeroSection_fst :
    (D.baseChange R').zeroSection ≫ pullback.fst D.toBase (specMap R R') = specMap R R' ≫ D.zeroSection :=
  pullback.lift_fst _ _ _

end GoodReductionJacobian.RelativePic0Designation

end


