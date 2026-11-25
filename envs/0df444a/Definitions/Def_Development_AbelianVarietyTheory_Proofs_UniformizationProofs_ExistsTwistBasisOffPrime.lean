-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
-- name    : Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsTwistBasisOffPrime
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T13:58:23.133918+00:00
-- url     : https://prove2.me/theorems/501fff19-03f5-47bd-baaa-ef196b34d5fe
-- title:
--   Exists Twist Basis Off Prime
-- statement:
--   Definitions and structural lemmas for Exists Twist Basis Off Prime, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsTwistBasisOffPrime.lean

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_NonemptyCubicalPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUniqueSecPull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.TwistLoc
section Glue
variable {X X' Y Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
end Glue
section Loc
variable {R : Type} [CommRing R] {X Y Y' Z : Scheme.{0}}
def cst (π : Y ⟶ Spec (CommRingCat.of R)) (U : Y.Opens) : CommRingCat.of R ⟶ Γ(Y, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ π.appLE ⊤ U le_top
def gc (π : Z ⟶ Spec (CommRingCat.of R)) (z : Z) (t : R) : Z.presheaf.stalk z :=
  gs π z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t)
variable {Rm : Type} [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
  {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
  (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
include H
end Loc
section Basis
variable {X X' Y Y₁ Y₂ T Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K] {m : ℕ}
def IsComb (π : Y ⟶ T) {N : LB Y} (b : Fin m → LB.Sec N) (s : LB.Sec N) (c : Fin m → Γ(T, ⊤)) : Prop :=
  ∀ j, s.f j = ∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (π.appTop.hom (c i)) * (b i).f j
theorem gs_comb (π : Y ⟶ T) (U : Y.Opens) (c : Fin m → Γ(T, ⊤)) (a : Fin m → Γ(Y, U)) (r : Z ⟶ Y) (z : Z)
    (hz : r z ∈ U) : gs r z U (∑ i, (Y.presheaf.map (homOfLE le_top).op).hom (π.appTop.hom (c i)) * a i) =
      ∑ i, gs (r ≫ π) z ⊤ (c i) * gs r z U (a i) := by
  rw [gs_eq r z U hz, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← gs_eq r z U hz, gs_mul r z U hz]
  exact congrArg (· * _) ((gs_res r z (le_top : U ≤ π ⁻¹ᵁ ⊤) hz _).trans (gs_pull r π z ⊤ trivial _))
theorem IsComb.gs {π : Y ⟶ T} {N : LB Y} {b : Fin m → LB.Sec N} {s : LB.Sec N} {c : Fin m → Γ(T, ⊤)}
    (h : IsComb π b s c) (r : Z ⟶ Y) (z : Z) (j : N.ι) (hz : r z ∈ N.U j) :
    gs r z (N.U j) (s.f j) = ∑ i, gs (r ≫ π) z ⊤ (c i) * gs r z (N.U j) ((b i).f j) := by
  rw [h j, gs_comb π _ c _ r z hz]
end Basis
section Main
end Main
end GlobalTheory.TwistLoc


