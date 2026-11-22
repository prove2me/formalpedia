-- Prove2me | Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
-- name    : Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_DeRhamMap
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:53.203034+00:00
-- url     : https://prove2.me/theorems/771c287f-22a1-4a95-b05e-4dd55cc6df31
-- title:
--   De Rham Map
-- statement:
--   Definitions and structural lemmas for De Rham Map, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicArithmetic/IntegralCasts/CrystallinePeriods/DeRhamMap.lean

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CrystallinePeriods_TruncLogEqOfPowEqZero
import Theorems.Thm_Reformulated_AutPerF_AinfInv_map_map
import Theorems.Thm_Reformulated_AutPerF_AinfInv_theta_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_map_map
import Theorems.Thm_Reformulated_AutPerF_Ainf_theta_map
import Theorems.Thm_Reformulated_AutPerF_Bst_monodromy_logFlat
import Theorems.Thm_Reformulated_AutPerF_Tilt_map_map
import Theorems.Thm_Reformulated_AutPerF_adicMap_adicMap
import Theorems.Thm_Reformulated_AutPerF_adicMap_eq_id
import Theorems.Thm_Reformulated_AutPerF_awayMap_algebraMap
import Theorems.Thm_Reformulated_AutPerF_padic_hom_ext
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Reformulated.AutPerF.Bst.monodromy_logFlat
attribute [local simp] Reformulated.AutPerF.awayMap_algebraMap


set_option autoImplicit false
noncomputable section
open Ideal
namespace Reformulated.AutPerF
universe u v w
variable (p : ℕ) [Fact p.Prime]
variable {R : Type u} [CommRing R] [Fact ¬IsUnit (p : R)] [IsAdicComplete (span {(p : R)}) R]
variable {S : Type v} [CommRing S] [Fact ¬IsUnit (p : S)] [IsAdicComplete (span {(p : S)}) S]
variable {U : Type w} [CommRing U] [Fact ¬IsUnit (p : U)] [IsAdicComplete (span {(p : U)}) U]
theorem AinfInv.kerTheta_le_comap (f : R →+* S) :
    AinfInv.kerTheta p R ≤ (AinfInv.kerTheta p S).comap (AinfInv.map p f) := by
  intro x hx
  rw [Ideal.mem_comap, RingHom.mem_ker, AinfInv.theta_map, RingHom.mem_ker.1 hx, map_zero]
variable {p} in
@[simp] theorem AinfInv.map_algebraMap_padic (f : R →+* S) (a : ℚ_[p]) :
    AinfInv.map p f (algebraMap ℚ_[p] _ a) = algebraMap ℚ_[p] _ a := by
  refine RingHom.congr_fun (padic_hom_ext (f := (AinfInv.map p f).comp (algebraMap ℚ_[p] _))
    (g := algebraMap ℚ_[p] (AinfInv p S)) fun b => ?_) a
  rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
    IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p R) (AinfInv p R),
    IsScalarTower.algebraMap_apply ℤ_[p] (Ainf p S) (AinfInv p S),
    AinfInv.map_algebraMap, Ainf.map_algebraMap]
namespace BdRPlus
def map (f : R →+* S) : BdRPlus p R →+* BdRPlus p S :=
  adicMap _ _ (AinfInv.map p f) (AinfInv.kerTheta_le_comap p f)
variable {p}
theorem eval_map (f : R →+* S) (n : ℕ) (x : BdRPlus p R) :
    eval p S n (map p f x) = Ideal.quotientMap _ (AinfInv.map p f)
      (pow_le_comap_pow (AinfInv.kerTheta_le_comap p f) n) (eval p R n x) :=
  evalₐ_adicMap _ _ _ _ n x
@[simp] theorem map_algebraMap (f : R →+* S) (x : AinfInv p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (AinfInv.map p f x) :=
  adicMap_algebraMap _ _ _ _ x
@[simp] theorem map_algebraMap_ainf (f : R →+* S) (x : Ainf p R) :
    map p f (algebraMap _ _ x) = algebraMap _ _ (Ainf.map p f x) := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap,
    ← IsScalarTower.algebraMap_apply]
@[simp] theorem map_algebraMap_padic (f : R →+* S) (a : ℚ_[p]) :
    map p f (algebraMap _ _ a) = algebraMap _ _ a := by
  rw [IsScalarTower.algebraMap_apply _ (AinfInv p R), map_algebraMap, AinfInv.map_algebraMap_padic,
    ← IsScalarTower.algebraMap_apply]
@[simp] theorem map_id (x : BdRPlus p R) : map p (RingHom.id R) x = x :=
  adicMap_eq_id _ _ _ AinfInv.map_id x
theorem map_map (f : R →+* S) (g : S →+* U) (x : BdRPlus p R) :
    map p g (map p f x) = map p (g.comp f) x :=
  adicMap_adicMap _ _ _ _ _ _ _ _ _ (AinfInv.map_map f g) x
theorem theta_eq_of_eval_one {x : BdRPlus p R} {a : AinfInv p R}
    (h : eval p R 1 x = Ideal.Quotient.mk _ a) : theta p R x = AinfInv.theta p R a := by
  have h1 := AdicCompletion.factorₐ_evalₐ_one (AinfInv.kerTheta p R) x
  change Ideal.Quotient.factor _ (eval p R 1 x) = _ at h1
  rw [h] at h1
  change RingHom.kerLift _ (AdicCompletion.evalOneₐ (AinfInv.kerTheta p R) x) = _
  rw [← h1]
  rfl
theorem theta_map (f : R →+* S) (x : BdRPlus p R) :
    theta p S (map p f x) = awayMap p f (theta p R x) := by
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (eval p R 1 x)
  rw [theta_eq_of_eval_one ha.symm, ← AinfInv.theta_map]
  apply theta_eq_of_eval_one
  rw [eval_map, ← ha, Ideal.quotientMap_mk]
variable (p) in

def mapEquiv (e : R ≃+* S) : BdRPlus p R ≃+* BdRPlus p S :=
  RingEquiv.ofRingHom (map p e.toRingHom) (map p e.symm.toRingHom)
    (by ext x; simp [map_map]) (by ext x; simp [map_map])
end BdRPlus
namespace BdR
def map (e : R ≃+* S) : BdR p R ≃+* BdR p S :=
  IsFractionRing.ringEquivOfRingEquiv (BdRPlus.mapEquiv p e)
variable {p}
end BdR
end Reformulated.AutPerF


