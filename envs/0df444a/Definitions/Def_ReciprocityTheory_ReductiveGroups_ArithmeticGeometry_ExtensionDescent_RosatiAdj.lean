-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:28:11.156342+00:00
-- url     : https://prove2.me/theorems/f657c032-9c01-45b9-8e6f-67e384b1d394
-- title:
--   Rosati Adj
-- statement:
--   Definitions and structural lemmas for Rosati Adj, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/RosatiAdj.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
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
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
section Act
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
structure RingAct (O : Type) [Ring O] where

  act : O → (A ⟶ A)
  hom : ∀ a, IsMonHom (act a)
  map_one : act 1 = 𝟙 A
  map_mul : ∀ a b, act (a * b) = act b ≫ act a
  map_add : ∀ a b, act (a + b) = padd A (act a) (act b)
def rosatiφ (f g : A ⟶ A) : Fin 6 → ((A ⊗ A).left ⟶ A.left) :=
  ![(padd A (fst A A ≫ f) (snd A A)).left, (fst A A ≫ f).left, (snd A A).left,
    (padd A (fst A A) (snd A A ≫ g)).left, (fst A A).left, (snd A A ≫ g).left]
def rosatiε : Fin 6 → ℤ := ![1, -1, -1, -1, 1, 1]
def RosatiAdj (L : LB A.left) (f g : A ⟶ A) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 6)
        (fun i => ((A ⊗ A).hom ⁻¹ᵁ U).ι ≫ rosatiφ A f g i) rosatiε), t.IsGen
abbrev zero2 : (𝟙_ (Over S)).left ⟶ (A ⊗ A).left := (lift η[A] η[A]).left
end Act
structure PolAV.OAct (O : Type) [Ring O] [StarRing O] {S : Scheme.{0}} (P : PolAV S)
    extends RingAct P.A O where
  rosati : ∀ a : O, RosatiAdj P.A P.L (act a) (act (star a))
namespace DegPre
variable {R : Type} [CommRing R] [IsDomain R]
def pt2 (D : DegPre R) (y y' : D.X) : (TK R).left ⟶ (D.P.A ⊗ D.P.A).left :=
  (lift (toUnit (TK R) ≫ D.c y) (toUnit (TK R) ≫ D.c y')).left
def TauBal (D : DegPre R) (f g : D.P.A ⟶ D.P.A) (a a' : D.X → D.X) : Prop :=
  ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A f g) rosatiε)), u.IsGen →
    LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
    ∀ y y' : D.X, LB.Gen.Corr D.P.L _ _ _ _
      (LB.mulGen D.P.L _ _ _ _ (D.tau (a y) y') (LB.pullGen D.P.L _ _ u (D.pt2 y y')))
      (D.tau y (a' y'))
structure OAct (O : Type) [Ring O] [StarRing O] (D : DegPre R) [Module O D.X] where
  onB : D.P.OAct O
  c_lin : ∀ (a : O) (y : D.X), D.c (a • y) = D.c y ≫ onB.act a
  tau_bal : ∀ a : O, D.TauBal (onB.act a) (onB.act (star a)) (fun y => a • y) (fun y => star a • y)
end DegPre
abbrev DegData.OAct (O : Type) [Ring O] [StarRing O] {R : Type} [CommRing R] [IsDomain R]
    {I : Ideal R} (D : DegData R I) [Module O D.toPre.X] := D.toPre.OAct O
namespace Inh
def zeroOAct (O : Type) [Ring O] [StarRing O] (S : Scheme.{0}) : (zeroPolAV S).OAct O where
  act := fun _ => 𝟙 _
  hom := fun _ => inferInstance
  map_one := rfl
  map_mul := fun _ _ => (Category.id_comp _).symm
  map_add := fun _ _ => toUnit_unique _ _
  rosati := fun _ _ => ⟨⊤, trivial, ⟨fun _ => 1⟩, by
    intro i j; erw [linComb_triv_g, _root_.one_mul]; dsimp only; repeat erw [map_one]⟩
example (S : Scheme.{0}) : (zeroPolAV S).OAct ℤ := zeroOAct ℤ S
end Inh
end ReciprocityTheory.ChartRestriction.G.Out


