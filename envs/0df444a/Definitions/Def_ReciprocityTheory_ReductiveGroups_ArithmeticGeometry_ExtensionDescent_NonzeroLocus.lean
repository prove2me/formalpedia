-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
-- name    : ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:22:45.88546+00:00
-- url     : https://prove2.me/theorems/549f4e87-73f8-4bcb-b853-1b1ca24ab92b
-- title:
--   Nonzero Locus
-- statement:
--   Definitions and structural lemmas for Nonzero Locus, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/ExtensionDescent/NonzeroLocus.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_CubicalStructures_CubeSymmetricSwapFirst
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
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
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
  AlgebraicGeometry
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.Out
open Semi
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
def Rigidified (L : LB A.left) : Prop :=
  ∃ t : LB.Gen (L.pull (eSec A)), t.IsGen
def Sym (L : LB A.left) : Prop :=
  ∀ s : S, ∃ U : S.Opens, s ∈ U ∧
    ∃ t : LB.Gen (LB.LinComb L (K := Fin 2)
        ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]), t.IsGen
def powOver (L : LB A.left) (U : S.Opens) (N : ℕ) : LB (A.hom ⁻¹ᵁ U).toScheme :=
  LB.LinComb L (K := Fin N) (fun _ => (A.hom ⁻¹ᵁ U).ι) (fun _ => 1)
def nonzeroLocus {Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) : Y.Opens :=
  ⨆ k, Y.basicOpen (s.f k)
def RelAmple (L : LB A.left) : Prop :=
  ∀ U : S.Opens, IsAffineOpen U →
    ∃ N : ℕ, 1 ≤ N ∧ ∃ M : ℕ, ∃ s : Fin (M + 1) → LB.Sec (powOver A L U N),
      (⨆ i, nonzeroLocus (s i) = ⊤) ∧
      ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧
        ∃ r : Fin (M + 1) → Γ((A.hom ⁻¹ᵁ U).toScheme, nonzeroLocus (s i)),
          (∀ j k, ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s j).f k) =
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_left :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
            ((A.hom ⁻¹ᵁ U).toScheme.presheaf.map (homOfLE (inf_le_right :
              nonzeroLocus (s i) ⊓ (powOver A L U N).U k ≤ (powOver A L U N).U k)).op).hom
                ((s i).f k)) ∧
          Function.Surjective (MvPolynomial.eval₂Hom
            ((A.hom ∣_ U).appLE ⊤ (nonzeroLocus (s i)) le_top).hom r)
def translDiff (L : LB A.left) {T : Over S} (x : T ⟶ A) : LB (T ⊗ A).left :=
  LB.LinComb L (K := Fin 2) ![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] ![1, -1]
def KTriv (L : LB A.left) : Prop :=
  ∀ (R : Type) [CommRing R] (t : Spec (CommRingCat.of R) ⟶ S) (x : Over.mk t ⟶ A),
    (∀ p : Spec (CommRingCat.of R), ∃ V : (Spec (CommRingCat.of R)).Opens, p ∈ V ∧
      ∃ c : LB.Gen ((translDiff A L x).pull ((fst (Over.mk t) A).left ⁻¹ᵁ V).ι), c.IsGen) →
    x = toUnit _ ≫ η[A]
structure PolAV (S : Scheme.{0}) where

  A : Over S
  [grp : GrpObj A]
  isAb : IsAbelianScheme A

  g : ℕ
  smoothDim : SmoothOfRelativeDimension g A.hom

  L : LB A.left
  isLB : L.IsLB
  rigid : Rigidified A L
  sym : Sym A L
  ample : RelAmple A L
  ktriv : KTriv A L
attribute [instance] PolAV.grp
end ReciprocityTheory.ChartRestriction.G.Out


