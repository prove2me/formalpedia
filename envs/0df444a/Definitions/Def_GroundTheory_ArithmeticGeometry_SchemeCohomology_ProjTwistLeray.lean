-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistLeray
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T01:03:21.420287+00:00
-- url     : https://prove2.me/theorems/06ecec4b-da52-45dd-b9f4-f3abffcaf0cd
-- title:
--   Proj Twist Leray
-- statement:
--   Definitions and structural lemmas for Proj Twist Leray, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistLeray.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechSeparated
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjCechModel
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_awayDegEquiv_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_ofL
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjSpace_lval_zero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_isLocallyFraction_mul
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_add
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_mkSection
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_neg
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_sub
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_val_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.awayDegEquiv_apply
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_ofL
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjSpace.lval_zero
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe w w' u
noncomputable section
instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Limits.coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
    (inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent)
section Transfer
variable {X : TopCat.{u}} {P Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} {D : Opens X}
end Transfer
namespace ProjTwist
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
lemma pow_mem_of_mem_one {u : A} (hu : u ∈ 𝒜 1) (m : ℕ) : u ^ m ∈ 𝒜 m := by
  have := SetLike.pow_mem_graded m hu
  rwa [smul_eq_mul, mul_one] at this
lemma pow_nmem {u : A} {x : ProjectiveSpectrum 𝒜} (hx : u ∉ x.asHomogeneousIdeal) (m : ℕ) :
    u ^ m ∉ x.asHomogeneousIdeal := fun h => hx (x.isPrime.mem_of_pow_mem m h)
def twistFrac (u : A) (k : ℤ) (x : ProjectiveSpectrum 𝒜) (hx : u ∉ x.asHomogeneousIdeal) :
    Loc 𝒜 x :=
  Localization.mk (u ^ k.toNat) ⟨u ^ (-k).toNat, pow_nmem hx _⟩
lemma isLocallyFraction_twistFrac {u : A} (hu : u ∈ 𝒜 1) (k : ℤ)
    {W : Opens (ProjectiveSpectrum.top 𝒜)} (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) :
    (isLocallyFraction 𝒜 k).pred (fun x : W => twistFrac u k x.1 (hW x)) := fun x =>
  ⟨W, x.2, 𝟙 W, (-k).toNat, k.toNat, by omega, u ^ k.toNat, u ^ (-k).toNat,
    pow_mem_of_mem_one hu _, pow_mem_of_mem_one hu _, fun y => pow_nmem (hW y) _, fun _ => rfl⟩
set_option backward.isDefEq.respectTransparency.types false in
lemma isLocallyFraction_val_section {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W)) :
    (isLocallyFraction 𝒜 0).pred (fun x : W => (t.1 x).val) := fun x => by
  obtain ⟨V, hxV, iV, j, ⟨r, hr⟩, ⟨s, hs⟩, hsn, w⟩ := t.2 x
  refine ⟨V, hxV, iV, j, j, by simp, r, s, hr, hs, hsn, fun y => ?_⟩
  exact (congrArg HomogeneousLocalization.val (w y)).trans (HomogeneousLocalization.val_mk _)
def twistMap {u : A} (hu : u ∈ 𝒜 1) (k : ℤ) {W : Opens (ProjectiveSpectrum.top 𝒜)}
    (hW : ∀ x : W, u ∉ x.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜).obj.obj (op W) →+
      (twistPresheafAb 𝒜 k).obj (op W) where
  toFun t := ⟨fun x => twistFrac u k x.1 (hW x) * (t.1 x).val,
    isLocallyFraction_mul (add_zero k) (isLocallyFraction_twistFrac hu k hW)
      (isLocallyFraction_val_section t)⟩
  map_zero' := Subtype.ext (funext fun x => by
    change twistFrac u k x.1 (hW x) * HomogeneousLocalization.val 0 = 0
    rw [HomogeneousLocalization.val_zero, mul_zero])
  map_add' t t' := Subtype.ext (funext fun x => by
    change twistFrac u k x.1 (hW x) * HomogeneousLocalization.val (t.1 x + t'.1 x) =
      twistFrac u k x.1 (hW x) * (t.1 x).val + twistFrac u k x.1 (hW x) * (t'.1 x).val
    rw [HomogeneousLocalization.val_add, mul_add])
end ProjTwist
section Leray
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
open ProjTwist
def AffineUnder {ι : Type w} (v : ι → A) (V : (Proj 𝒜).Opens) : Prop :=
  IsAffineOpen V ∧ ∃ j, V ≤ Proj.basicOpen 𝒜 (v j)
end Leray
namespace ProjSpace
attribute [local instance] MvPolynomial.gradedAlgebra
variable {A : Type u} [CommRing A] {n : ℕ}
end ProjSpace
end
end GroundTheory.Arith.SchemeCoh


