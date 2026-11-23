-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_OrbitMapConjSmulZero
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:48.240484+00:00
-- url     : https://prove2.me/theorems/6f4fe744-8050-4422-96d7-54632dfe9f45
-- title:
--   Orbit Map Conj Smul Zero
-- statement:
--   Definitions and structural lemmas for Orbit Map Conj Smul Zero, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/ChartPullbacks/TangentLinearity/OrbitMapConjSmulZero.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_CanonGenIsGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifBaseChangeSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out.TLinPf
open Semi
section Fam
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
abbrev xc : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶ D.toPre.P.A :=
  toUnit _ ≫ D.toPre.c χ
abbrev hOv : (Over.map (thick R I e)).obj (thickObj R I e G) ⟶
    (Over.map (thick R I e)).obj (thickObj R I e G) :=
  (Over.map (thick R I e)).map ((Over.pullback (thick R I e)).map (ιG.act a))
abbrev φA : Fin 4 ⊕ Fin 6 → ((thickObj R I e G).left ⟶ D.toPre.P.A.left) :=
  Sum.elim (D.toPre.Oφ (U.gt e).pG (star a • χ))
    (fun k => (lift (xc e χ (G := G)) (U.gt e).pG).left ≫
      rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a) k)
abbrev εA : Fin 4 ⊕ Fin 6 → ℤ := Sum.elim Oinvε rosatiε
abbrev φB : Fin 4 → ((thickObj R I e G).left ⟶ D.toPre.P.A.left) :=
  fun k => ((Over.pullback (thick R I e)).map (ιG.act a)).left ≫ D.toPre.Oφ (U.gt e).pG χ k
abbrev lhs (u : LB.Gen (LB.LinComb D.toPre.P.L
    (rosatiφ D.toPre.P.A (ιD.onB.act (star a)) (ιD.onB.act a)) rosatiε)) :
    LB.Gen (LB.LinComb D.toPre.P.L (φA U ιD e a χ) εA) :=
  LB.mulGen D.toPre.P.L _ _ _ _ ((U.gt e).t (star a • χ))
    (LB.pullGen D.toPre.P.L _ _ u (lift (toUnit _ ≫ D.toPre.c χ) (U.gt e).pG).left)
abbrev rhs : LB.Gen (LB.LinComb D.toPre.P.L (φB U ιG e a χ) Oinvε) :=
  LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (thick R I e)).map (ιG.act a)).left
end Fam
section Eqs
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
abbrev OφX {T : Over (Spec (CommRingCat.of R))} (P x : T ⟶ D.toPre.P.A) :
    Fin 4 → (T.left ⟶ D.toPre.P.A.left) :=
  ![(padd D.toPre.P.A P x).left, x.left, P.left, (toUnit T ≫ η[D.toPre.P.A]).left]
end Eqs
section Sums
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {O : Type} [Ring O] [StarRing O]
  {D : DegData R I} [Module O D.toPre.X] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)
  (ιD : D.OAct O) (ιG : RingAct G O) (e : ℕ) (a : O) (χ : D.toPre.X)
  (hO : ∀ a : O, (Over.pullback (thick R I e)).map (ιG.act a) ≫ (U.gt e).q =
      (U.gt e).q ≫ (Over.pullback (thick R I e)).map (ιD.onB.act a))
end Sums
end ReciprocityTheory.ChartRestriction.G.Out.TLinPf


