-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpecVectorFieldOfDualNumberSection
-- name    : Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsSpecVectorFieldOfDualNumberSection
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:16.793355+00:00
-- url     : https://prove2.me/theorems/945a46af-aff4-4958-9adf-3eb1cf54bea4
-- title:
--   Exists Spec Vector Field Of Dual Number Section
-- statement:
--   Definitions and structural lemmas for Exists Spec Vector Field Of Dual Number Section, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsSpecVectorFieldOfDualNumberSection.lean

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__DenseInterior_23def473f6482931
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS
noncomputable section
namespace GlobalTheory.SpecField
open AlgebraicGeometry
variable {A : Type} [CommRing A]
theorem dualMap_fst {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).fst = f x.fst := by
  simp [Formalism.L2.Pj.dualMap]
theorem dualMap_snd {B : Type} [CommRing B] (f : A →+* B) (x : DualNumber A) :
    (Formalism.L2.Pj.dualMap f x).snd = f x.snd := by
  simp [Formalism.L2.Pj.dualMap]
variable (σ : A →+* DualNumber A) (hσ : ∀ a, (σ a).fst = a) (S : Submonoid A)
def liftLoc : LocalizedModule S A →+* DualNumber (LocalizedModule S A) :=
  IsLocalization.lift (M := S) (g := (Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A))).comp σ)
    (fun y => by
      rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, RingHom.comp_apply, dualMap_fst, hσ]
      exact IsLocalization.map_units _ y)
theorem liftLoc_algebraMap (a : A) :
    liftLoc σ hσ S (algebraMap A _ a) = Formalism.L2.Pj.dualMap (algebraMap A (LocalizedModule S A)) (σ a) :=
  IsLocalization.lift_eq _ _
theorem liftLoc_fst (b : LocalizedModule S A) : (liftLoc σ hσ S b).fst = b := by
  have h : ((TrivSqZeroExt.fstHom (LocalizedModule S A) (LocalizedModule S A) (LocalizedModule S A)).toRingHom.comp
      (liftLoc σ hσ S)) = RingHom.id _ :=
    IsLocalization.ringHom_ext S (RingHom.ext fun a => by
      simp [liftLoc_algebraMap, dualMap_fst, hσ])
  exact congrArg (fun φ => φ b) h
def dloc (b : LocalizedModule S A) : LocalizedModule S A := (liftLoc σ hσ S b).snd
theorem dloc_mul (b b' : LocalizedModule S A) :
    dloc σ hσ S (b * b') = b * dloc σ hσ S b' + b' * dloc σ hσ S b := by
  simp only [dloc, map_mul, TrivSqZeroExt.snd_mul, liftLoc_fst, smul_eq_mul, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op]
  ring
theorem dloc_algebraMap (a : A) : dloc σ hσ S (algebraMap A _ a) = algebraMap A _ (σ a).snd := by
  simp [dloc, liftLoc_algebraMap, dualMap_snd]
theorem mk_mul_algebraMap (m : A) (u : S) :
    LocalizedModule.mk m u * algebraMap A (LocalizedModule S A) u = algebraMap A _ m := by
  rw [show algebraMap A (LocalizedModule S A) u = LocalizedModule.mk (u : A) 1 from rfl]
  erw [LocalizedModule.mk_mul_mk]
  rw [show algebraMap A (LocalizedModule S A) m = LocalizedModule.mk m 1 from rfl, LocalizedModule.mk_eq]
  exact ⟨1, by simp [Submonoid.smul_def, smul_eq_mul]; ring⟩
theorem dloc_mk (r : A) (t : S) :
    dloc σ hσ S (LocalizedModule.mk r t) =
      LocalizedModule.mk (t * (σ r).snd - r * (σ t).snd) (t * t) := by
  have h1 := mk_mul_algebraMap S r t
  have h2 := congrArg (dloc σ hσ S) h1
  rw [dloc_mul, dloc_algebraMap, dloc_algebraMap] at h2
  have hu : IsUnit (algebraMap A (LocalizedModule S A) ((t * t : S) : A)) := IsLocalization.map_units _ (t * t)
  refine (hu.mul_left_inj).1 ?_
  rw [mk_mul_algebraMap]
  simp only [Submonoid.coe_mul, map_mul, map_sub]
  linear_combination (algebraMap A (LocalizedModule S A) t) * h2 -
    (algebraMap A (LocalizedModule S A) (σ t).snd) * h1
def dsec (O : (Sp A).Opens) (s : Γ(Sp A, O)) : Γ(Sp A, O) :=
  ⟨fun x => dloc σ hσ _ (s.1 x), fun x => by
    obtain ⟨V, hxV, i, r, t, w⟩ := s.2 x
    refine ⟨V, hxV, i, t * (σ r).snd - r * (σ t).snd, t * t, fun y => ?_⟩
    obtain ⟨ht, hs⟩ := w y
    refine ⟨fun h => ((PrimeSpectrum.isPrime (y.1 : PrimeSpectrum A)).mem_or_mem h).elim ht ht, ?_⟩
    exact (congrArg (dloc σ hσ _) hs).trans (dloc_mk σ hσ _ r ⟨t, ht⟩)⟩
end GlobalTheory.SpecField


