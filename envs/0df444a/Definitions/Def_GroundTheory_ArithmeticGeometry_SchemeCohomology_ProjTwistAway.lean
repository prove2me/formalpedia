-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwistAway
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:49.307158+00:00
-- url     : https://prove2.me/theorems/34ca5ab6-eee1-473f-ac3c-27b251affb13
-- title:
--   Proj Twist Away
-- statement:
--   Definitions and structural lemmas for Proj Twist Away, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/ProjTwistAway.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjTwist
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_ProjTwist_ext
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
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_add
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_mkSection
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_neg
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_sub
attribute [local simp] GroundTheory.Arith.SchemeCoh.ProjTwist.val_zero


set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
open AlgebraicGeometry TopologicalSpace CategoryTheory Opposite
universe u
variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜]
noncomputable section
namespace ProjTwist
def fpow (f : A) (n : ℕ) : Submonoid.powers f := ⟨f ^ n, (Submonoid.mem_powers_iff _ _).2 ⟨n, rfl⟩⟩
@[simp] lemma coe_fpow (f : A) (n : ℕ) : (fpow f n : A) = f ^ n := rfl
lemma fpow_add (f : A) (n m : ℕ) : fpow f (n + m) = fpow f n * fpow f m :=
  Subtype.ext (pow_add f n m)
def locMap {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal) :
    Localization.Away f →+* Loc 𝒜 x :=
  IsLocalization.map (M := Submonoid.powers f) (T := x.asHomogeneousIdeal.toIdeal.primeCompl) _
    (RingHom.id _) (Submonoid.powers_le.mpr hx)
lemma locMap_mk {f : A} (x : ProjectiveSpectrum 𝒜) (hx : f ∉ x.asHomogeneousIdeal) (a : A)
    (n : ℕ) :
    locMap x hx (Localization.mk a (fpow f n)) =
      Localization.mk a ⟨f ^ n, (Submonoid.powers_le.mpr hx) ⟨n, rfl⟩⟩ := by
  rw [locMap, Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  rfl
variable (𝒜) in

def awayDeg {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℤ) :
    AddSubgroup (Localization.Away f) where
  carrier := {z | ∃ (n j : ℕ) (a : A), a ∈ 𝒜 j ∧ (j : ℤ) = n * d + k ∧
    z = Localization.mk a (fpow f n)}
  zero_mem' := ⟨(-k).toNat, (-k).toNat * d + k.toNat - (-k).toNat, 0, zero_mem _, by
    have : (-k).toNat ≤ (-k).toNat * d := Nat.le_mul_of_pos_right _ hd
    omega, by rw [Localization.mk_zero]⟩
  add_mem' := by
    rintro _ _ ⟨n, j, a, ha, hj, rfl⟩ ⟨m, j', b, hb, hj', rfl⟩
    refine ⟨n + m, j + m * d, f ^ n * b + f ^ m * a, add_mem ?_ ?_, ?_, ?_⟩
    · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded n hf) hb
      have e : n • d + j' = j + m * d := by
        have : ((n • d + j' : ℕ) : ℤ) = ((j + m * d : ℕ) : ℤ) := by
          push_cast [smul_eq_mul]; linarith
        exact_mod_cast this
      rwa [e] at h
    · have h := SetLike.mul_mem_graded (SetLike.pow_mem_graded m hf) ha
      rwa [smul_eq_mul, add_comm] at h
    · push_cast; linarith
    · rw [Localization.add_mk, fpow_add]
      rfl
  neg_mem' := by
    rintro _ ⟨n, j, a, ha, hj, rfl⟩
    exact ⟨n, j, -a, neg_mem ha, hj, by rw [Localization.neg_mk]⟩
lemma nmem_of_mem {f : A} (x : Proj.basicOpen 𝒜 f) : f ∉ x.1.asHomogeneousIdeal := x.2
def toSection {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d) (k : ℤ) :
    awayDeg 𝒜 hf hd k →+ Γ(twistingSheaf 𝒜 k, Proj.basicOpen 𝒜 f) where
  toFun z := mkSection (fun x => locMap x.1 (nmem_of_mem x) z.1) (fun x => by
    obtain ⟨n, j, a, ha, hj, hz⟩ := z.2
    refine ⟨Proj.basicOpen 𝒜 f, x.2, 𝟙 _, n * d, j, by push_cast; linarith, a, f ^ n, ha,
      ?_, fun y h => nmem_of_mem y (y.1.isPrime.mem_of_pow_mem n h), fun y => ?_⟩
    · have := SetLike.pow_mem_graded n hf
      rwa [smul_eq_mul] at this
    · change locMap y.1 (nmem_of_mem y) z.1 = _
      rw [hz]
      exact locMap_mk y.1 (nmem_of_mem y) a n)
  map_zero' := by
    apply GroundTheory.Arith.SchemeCoh.ProjTwist.ext
    funext x
    exact map_zero _
  map_add' z w := by
    apply GroundTheory.Arith.SchemeCoh.ProjTwist.ext
    funext x
    exact map_add _ _ _
end ProjTwist
end
end GroundTheory.Arith.SchemeCoh


