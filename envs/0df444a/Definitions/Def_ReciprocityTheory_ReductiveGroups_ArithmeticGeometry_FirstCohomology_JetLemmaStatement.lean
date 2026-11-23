-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetLemmaStatement
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_JetLemmaStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T11:06:08.367236+00:00
-- url     : https://prove2.me/theorems/a19a81d7-f7b6-4a03-98cb-742e66163886
-- title:
--   Jet Lemma Statement
-- statement:
--   Definitions and structural lemmas for Jet Lemma Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/FirstCohomology/JetLemmaStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ConstGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaPt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_BaseOver
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
namespace ReciprocityTheory.ChartRestriction.G.H1
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
def jetLB {k : Type} [Field k] (P : PolAV (Spec (CommRingCat.of k)))
    (a₀ : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (q : ℕ) :
    LB (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left :=
  LB.LinComb P.L (K := Fin 3)
    ![(snd (baseOver (Spec (CommRingCat.of k))) P.A).left, (translPt P.A a₀).left,
      (snd (baseOver (Spec (CommRingCat.of k))) P.A).left] ![(q : ℤ), 1, -1]
def JetLemmaStatement : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] (P : PolAV (Spec (CommRingCat.of k)))
    (a₀ x : baseOver (Spec (CommRingCat.of k)) ⟶ P.A) (q D : ℕ), 4 * D + 4 ≤ q →
    ∀ y ∈ Set.range (ptSecT P.A x).left.base,
    ∀ (j : (jetLB P a₀ q).ι) (hy : y ∈ (jetLB P a₀ q).U j)
      (f : (baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left.presheaf.stalk y),
      ∃ s : LB.Sec (jetLB P a₀ q),
        ((baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left.presheaf.germ
            ((jetLB P a₀ q).U j) y hy).hom (s.f j) - f ∈
          IsLocalRing.maximalIdeal
            ((baseOver (Spec (CommRingCat.of k)) ⊗ P.A).left.presheaf.stalk y) ^ (D + 1)
end ReciprocityTheory.ChartRestriction.G.H1


