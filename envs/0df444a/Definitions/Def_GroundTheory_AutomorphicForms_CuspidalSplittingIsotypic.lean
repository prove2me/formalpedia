-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic
-- name    : GroundTheory_AutomorphicForms_CuspidalSplittingIsotypic
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:25:47.899186+00:00
-- url     : https://prove2.me/theorems/71222d32-5c4d-53e2-8f59-76c0ed3524d7
-- title:
--   Cuspidal Splitting Isotypic
-- statement:
--   Definitions and structural lemmas for Cuspidal Splitting Isotypic, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/CuspidalSplittingIsotypic.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_CuspidalSplittingProjective
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_coinvariantsTranslate_mk
import Theorems.Thm_GroundTheory_Automorphic_frobenius_apply
import Theorems.Thm_GroundTheory_Automorphic_frobenius_symm_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.Cartan.dominantEquivDoubleCoset_apply
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Measures.adUnipotentHom_apply
attribute [local simp] GroundTheory.Automorphic.coinvariantsTranslate_mk
attribute [local simp] GroundTheory.Automorphic.frobenius_apply
attribute [local simp] GroundTheory.Automorphic.frobenius_symm_apply


set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
namespace GroundTheory.Automorphic
namespace Parabolic
open Function Topology
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section Constructions
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
def subrepIncl (Y : Subrepresentation ρ) :
    Representation.IntertwiningMap Y.toRepresentation ρ where
  toLinearMap := Y.toSubmodule.subtype
  isIntertwining' _ := rfl
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem HasCentralChar.toRepresentation (hωρ : HasCentralChar ρ ω) (Y : Subrepresentation ρ) :
    HasCentralChar Y.toRepresentation ω := fun z hz y => Subtype.ext (hωρ z hz y)
variable (π) in

def piRep (m : ℕ) : Representation ℂ (GL (Fin n) F) (Fin m → V) where
  toFun g := LinearMap.pi fun i => π g ∘ₗ LinearMap.proj i
  map_one' := by ext; simp
  map_mul' g h := by ext; simp
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
@[simp]
theorem piRep_apply (m : ℕ) (g : GL (Fin n) F) (x : Fin m → V) (i : Fin m) :
    piRep π m g x i = π g (x i) := rfl
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [TopologicalSpace F] in
theorem HasCentralChar.piRep (hωπ : HasCentralChar π ω) (m : ℕ) :
    HasCentralChar (piRep π m) ω := fun z hz x => funext fun i => hωπ z hz (x i)
variable (π) in

def piIncl (m : ℕ) (i : Fin m) : Representation.IntertwiningMap π (piRep π m) where
  toLinearMap := LinearMap.single ℂ (fun _ => V) i
  isIntertwining' g := by
    ext x j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
variable (π) in

def piProj (m : ℕ) (i : Fin m) : Representation.IntertwiningMap (piRep π m) π where
  toLinearMap := LinearMap.proj i
  isIntertwining' _ := rfl
end Constructions
section Detect
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
end Detect
section Isotypic
variable {V U : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
  {π : Representation ℂ (GL (Fin n) F) V} {ρ : Representation ℂ (GL (Fin n) F) U}
  {ω : GL (Fin n) F → ℂ}
variable (π ρ) in

def isotypicPart : Submodule ℂ U :=
  ⨆ t : Representation.IntertwiningMap π ρ, LinearMap.range t.toLinearMap
variable (π ρ) in

def isotypicKernel : Submodule ℂ U :=
  ⨅ Fm : Representation.IntertwiningMap ρ π, LinearMap.ker Fm.toLinearMap
variable [π.IsIrreducible] (hπ : IsSmooth π) (hsc : IsSupercuspidal π)
  (hωπ : HasCentralChar π ω) (hρ : IsSmooth ρ) (hωρ : HasCentralChar ρ ω)
include hπ hsc hωπ hρ hωρ
end Isotypic
end Parabolic
end GroundTheory.Automorphic


