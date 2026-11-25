-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty
-- name    : Development_AbelianVarietyTheory_Counterexamples_UniformisationSurvey_EquivIffOfIsEmpty
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:23:55.616795+00:00
-- url     : https://prove2.me/theorems/c632278f-0cd8-5302-ad54-2dbd6053f6cb
-- title:
--   Equiv Iff Of Is Empty
-- statement:
--   Definitions and structural lemmas for Equiv Iff Of Is Empty, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/UniformisationSurvey/EquivIffOfIsEmpty.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_InhTate
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TorsionPairTest
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
section Empty
theorem corr_of_isEmpty {X Y : Scheme.{0}} [IsEmpty Y] (L : LB X) {K K' : Type} [Fintype K] [Fintype K']
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε))
    (t' : LB.Gen (LB.LinComb L φ' ε')) : LB.Gen.Corr L φ ε φ' ε' t t' :=
  fun _ _ _ _ _ => Units.ext (Subsingleton.elim _ _)
variable {T : Over (Spec (CommRingCat.of R))} [IsEmpty T.left]
theorem hom_eq {A : Over (Spec (CommRingCat.of R))} (a b : T ⟶ A) : a = b :=
  Over.OverMorphism.ext (isInitialOfIsEmpty.hom_ext _ _)
def emptyPt (D : DegPre R) (T : Over (Spec (CommRingCat.of R))) [IsEmpty T.left] : GtPt D T where
  b := DegPre.zeroT D T
  s := fun _ => ⟨fun _ => 1⟩
  isGen := fun _ _ _ => Units.ext (Subsingleton.elim _ _)
  s_zero := corr_of_isEmpty _ _ _ _ _ _ _
  mult := fun _ _ => corr_of_isEmpty _ _ _ _ _ _ _
end Empty
variable {W : (Spec (CommRingCat.of R)).Opens} (ψW : PsiOn D W) (k : ℕ) (T : Over W.toScheme) [IsEmpty T.left]
instance : IsEmpty (overW W T).left := inferInstanceAs (IsEmpty T.left)
def emptyPair (y : D.X) : QkPtW D W ψW k T where
  y := y
  g := emptyPt D _
  eq := ⟨emptyPt D _, ⟨fun _ => emptyPt D _, ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩,
    fun _ => ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩, rfl⟩,
    ⟨hom_eq _ _, fun _ => corr_of_isEmpty _ _ _ _ _ _ _⟩⟩
end GlobalTheory.TorsionPairTest


