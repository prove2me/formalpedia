-- Prove2me | Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
-- name    : Development_ResolutionOfSingularities_EmbeddedResolution_StrictTransformCharts_ControlledTransform
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:03:18.883648+00:00
-- url     : https://prove2.me/theorems/3469b132-aca4-4f28-b8c4-8907c884691c
-- title:
--   Controlled Transform
-- statement:
--   Definitions and structural lemmas for Controlled Transform, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrictTransformCharts/ControlledTransform.lean

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_BlowupBasic
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Blowup_StrictTransform
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_Schemes_IdealSheafData
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace FunctorialResolution.EmbeddedResolution
variable {Y : Scheme.{u}}
theorem exists_pow_mul_mem_of_algebraMap_mem_map {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] (r : R) [IsLocalization.Away r S] (I : Ideal R) (x : R)
    (hx : algebraMap R S x ∈ Ideal.map (algebraMap R S) I) : ∃ n : ℕ, r ^ n * x ∈ I := by
  rw [IsLocalization.mem_map_algebraMap_iff (M := Submonoid.powers r) (S := S)] at hx
  obtain ⟨w, hy⟩ := hx
  rw [← map_mul] at hy
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (M := Submonoid.powers r) (S := S)).mp hy
  obtain ⟨p, hp⟩ : ∃ p : ℕ, r ^ p = (c : R) := c.2
  obtain ⟨q, hq⟩ : ∃ q : ℕ, r ^ q = (w.2 : R) := w.2.2
  refine ⟨p + q, ?_⟩
  have h2 : r ^ (p + q) * x = (c : R) * (w.1 : R) := by
    rw [pow_add, hp, hq, ← hc]; ring
  rw [h2]
  exact I.mul_mem_left _ w.1.2
noncomputable def sectionsOpensImageIso {Y' : Scheme.{u}} (U : Y'.Opens)
    (V : U.toScheme.Opens) : Γ(Y', U.ι ''ᵁ V) ≅ Γ(U.toScheme, V) := U.ι.appIso V
theorem mem_colon_span {R : Type*} [CommRing R] (I : Ideal R) (s : Set R)
    (x : R) (h : ∀ g ∈ s, x * g ∈ I) : x ∈ I.colon (Submodule.span R s) := by
  refine Submodule.mem_colon.2 ?_
  intro p hp
  rw [smul_eq_mul]
  induction hp using Submodule.span_induction with
  | mem g hg => exact h g hg
  | zero => rw [mul_zero]; exact zero_mem I
  | add y z _ _ ihy ihz => rw [mul_add]; exact add_mem ihy ihz
  | smul c y _ ih =>
    rw [smul_eq_mul, ← mul_assoc, mul_comm x c, mul_assoc]
    exact I.mul_mem_left c ih
theorem map_colon_eq_colon_map_away {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] (I J : Ideal R) (hJ : J.FG) :
    Ideal.map (algebraMap R S) (I.colon J) =
      (Ideal.map (algebraMap R S) I).colon (Ideal.map (algebraMap R S) J) := by
  refine le_antisymm ?_ ?_
  · have hsub : Ideal.map (algebraMap R S) (I.colon J) * Ideal.map (algebraMap R S) J ≤
        Ideal.map (algebraMap R S) I := by
      rw [← Ideal.map_mul]
      refine Ideal.map_mono (Ideal.mul_le.2 ?_)
      intro a ha b hb
      have ha' := Submodule.mem_colon.mp ha b hb
      rwa [smul_eq_mul] at ha'
    intro z hz
    refine Submodule.mem_colon.2 ?_
    intro p hp
    rw [smul_eq_mul]
    exact hsub (Ideal.mul_mem_mul hz hp)
  · intro b hb
    obtain ⟨s, hs⟩ := hJ
    obtain ⟨w, hab⟩ := IsLocalization.surj (M := Submonoid.powers r) b
    have key : ∀ g ∈ (s : Set R), ∃ n : ℕ, r ^ n * (w.1 * g) ∈ I := by
      intro g hg
      have hgJ : g ∈ J := by
        rw [← hs]; exact Submodule.subset_span hg
      have h1 := Submodule.mem_colon.mp hb (algebraMap R S g) (Ideal.mem_map_of_mem _ hgJ)
      rw [smul_eq_mul] at h1
      have h2 : algebraMap R S (w.1 * g) ∈ Ideal.map (algebraMap R S) I := by
        have heq : algebraMap R S (w.1 * g) =
            b * algebraMap R S g * algebraMap R S (w.2 : R) := by
          rw [map_mul, ← hab]; ring
        rw [heq]
        exact Ideal.mul_mem_right _ _ h1
      exact exists_pow_mul_mem_of_algebraMap_mem_map r I (w.1 * g) h2
    choose! n hn using key
    have hNa : r ^ (s.sup n) * w.1 ∈ I.colon J := by
      rw [← hs]
      refine mem_colon_span I (↑s) (r ^ (s.sup n) * w.1) ?_
      intro g hg
      have hle : n g ≤ s.sup n := Finset.le_sup (Finset.mem_coe.mp hg)
      have hg' := hn g hg
      have hpow : r ^ (s.sup n - n g) * r ^ (n g) = r ^ (s.sup n) := by
        rw [← pow_add, Nat.sub_add_cancel hle]
      have hre : r ^ (s.sup n) * w.1 * g = r ^ (s.sup n - n g) * (r ^ (n g) * (w.1 * g)) := by
        rw [← hpow]; ring
      rw [hre]
      exact I.mul_mem_left _ hg'
    have hmem : r ^ (s.sup n) * (w.2 : R) ∈ Submonoid.powers r :=
      mul_mem (pow_mem (Submonoid.mem_powers r) _) w.2.2
    have hunit : IsUnit (algebraMap R S (r ^ (s.sup n) * (w.2 : R))) :=
      IsLocalization.map_units (M := Submonoid.powers r) S
        ⟨r ^ (s.sup n) * (w.2 : R), hmem⟩
    obtain ⟨v, hv⟩ := hunit.exists_right_inv
    have hb2 : b * algebraMap R S (r ^ (s.sup n) * (w.2 : R)) ∈
        Ideal.map (algebraMap R S) (I.colon J) := by
      have heq : b * algebraMap R S (r ^ (s.sup n) * (w.2 : R)) =
          algebraMap R S (r ^ (s.sup n) * w.1) := by
        rw [map_mul, map_mul, ← hab]; ring
      rw [heq]
      exact Ideal.mem_map_of_mem _ hNa
    have hbv := Ideal.mul_mem_right v (Ideal.map (algebraMap R S) (I.colon J)) hb2
    rw [mul_assoc, hv, mul_one] at hbv
    exact hbv
theorem idealSheafColon_ideal_map_basicOpen [IsLocallyNoetherian Y]
    (I' F : Y.IdealSheafData) (U : Y.affineOpens) (f : Γ(Y, U)) :
    Ideal.map (CommRingCat.Hom.hom (Y.presheaf.map (homOfLE (Y.basicOpen_le f)).op))
        ((I'.ideal U).colon (F.ideal U)) =
      (I'.ideal (Y.affineBasicOpen f)).colon (F.ideal (Y.affineBasicOpen f)) := by
  have := IsLocallyNoetherian.component_noetherian U
  have : IsLocalization.Away f Γ(Y, Y.basicOpen f) := U.2.isLocalization_basicOpen f
  have key := map_colon_eq_colon_map_away (S := Γ(Y, Y.basicOpen f)) f (I'.ideal U) (F.ideal U)
    (IsNoetherian.noetherian (F.ideal U))
  rw [← I'.map_ideal_basicOpen U f, ← F.map_ideal_basicOpen U f]
  exact key
def idealSheafColon [IsLocallyNoetherian Y] (I' F : Y.IdealSheafData) :
    Y.IdealSheafData where
  ideal U := (I'.ideal U).colon (F.ideal U)
  map_ideal_basicOpen := idealSheafColon_ideal_map_basicOpen I' F
variable {X X₁ : Scheme.{u}}
def controlledTransform [IsLocallyNoetherian X₁] (π : X₁ ⟶ X) (Z I : X.IdealSheafData)
    (n : ℕ) (_hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (_hI : I ≤ Z ^ n) : X₁.IdealSheafData :=
  idealSheafColon (I.comap π) (Blowup.exceptionalIdeal π Z ^ n)
end FunctorialResolution.EmbeddedResolution
end


