-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
-- name    : GroundTheory_AutomorphicForms_GeometricLemmaCellGroups
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T11:40:27.973258+00:00
-- url     : https://prove2.me/theorems/c492f8de-969e-4575-987a-8a961bc895a4
-- title:
--   Geometric Lemma Cell Groups
-- statement:
--   Definitions and structural lemmas for Geometric Lemma Cell Groups, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GeometricLemmaCellGroups.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaCompact
import Definitions.Def_GroundTheory_AutomorphicForms_GeometricLemmaAverage
import Theorems.Thm_GroundTheory_Automorphic_Cartan_dominantEquivDoubleCoset_apply
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Measures_adUnipotentHom_apply
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_mem_unipotentRadical
import Theorems.Thm_GroundTheory_Automorphic_Parabolic_conj_permGL_mem_blockUpper_iff
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
set_option linter.unusedSectionVars false
namespace GroundTheory.Automorphic
namespace Parabolic
open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
section PermConj
variable {β : Fin n → ℕ} (w : Equiv.Perm (Fin n))
variable (F β) in

def permConj : blockUpper F n (β ∘ w) →* blockUpper F n β where
  toFun x := ⟨permGL F w * x * (permGL F w)⁻¹, (conj_permGL_mem_blockUpper_iff w).2 x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)
@[simp]
theorem coe_permConj (x : blockUpper F n (β ∘ w)) :
    ((permConj F β w x : blockUpper F n β) : GL (Fin n) F) =
      permGL F w * x * (permGL F w)⁻¹ := rfl
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable (β) in

def cellRep : Representation ℂ (blockUpper F n (β ∘ w)) W :=
  (inflateTwist F n β σ).comp (permConj F β w)
end PermConj
section Subgroups
variable (F) (β γ : Fin n → ℕ) (w : Equiv.Perm (Fin n))
def cellUnipotent : Subgroup (GL (Fin n) F) :=
  unipotentRadical F n γ ⊓ blockUpper F n (β ∘ w)
def cellLeviParabolic : Subgroup (GL (Fin n) F) :=
  levi F n γ ⊓ blockUpper F n (β ∘ w)
variable {F β γ w}
theorem cellUnipotent_le_blockUpper : cellUnipotent F β γ w ≤ blockUpper F n (β ∘ w) :=
  inf_le_right
theorem cellLeviParabolic_le_blockUpper : cellLeviParabolic F β γ w ≤ blockUpper F n (β ∘ w) :=
  inf_le_right
theorem conj_mem_cellUnipotent {b a : GL (Fin n) F} (hb : b ∈ cellLeviParabolic F β γ w)
    (ha : a ∈ cellUnipotent F β γ w) : b * a * b⁻¹ ∈ cellUnipotent F β γ w :=
  ⟨conj_mem_unipotentRadical (levi_le_blockUpper hb.1) ha.1,
    (blockUpper F n (β ∘ w)).mul_mem ((blockUpper F n (β ∘ w)).mul_mem hb.2 ha.2)
      ((blockUpper F n (β ∘ w)).inv_mem hb.2)⟩
variable {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)
variable (β γ w) in

def cellRepA : Representation ℂ (cellUnipotent F β γ w) W :=
  (cellRep β w σ).comp (Subgroup.inclusion cellUnipotent_le_blockUpper)
variable (β γ w) in

def cellRepM : Representation ℂ (cellLeviParabolic F β γ w) W :=
  (cellRep β w σ).comp (Subgroup.inclusion cellLeviParabolic_le_blockUpper)
theorem cellRepM_mul_cellRepA (b : cellLeviParabolic F β γ w) (a : cellUnipotent F β γ w) :
    cellRepM β γ w σ b * cellRepA β γ w σ a =
      cellRepA β γ w σ ⟨b * a * b⁻¹, conj_mem_cellUnipotent b.2 a.2⟩ * cellRepM β γ w σ b := by
  simp only [cellRepM, cellRepA, MonoidHom.coe_comp, Function.comp_apply, ← map_mul]
  congr 1
  ext
  simp
end Subgroups
section LeviProjCongruence
variable {α : Type*} [LinearOrder α] {β : Fin n → α}
end LeviProjCongruence
section Smooth
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (levi F n β) W}
end Smooth
section UnipotentCompactG
variable {γ : Fin n → ℕ}
end UnipotentCompactG
section LeviIwasawa
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
end LeviIwasawa
section Coinvariants
variable {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)} {W : Type*} [AddCommGroup W] [Module ℂ W]
  (σ : Representation ℂ (levi F n β) W)
def cellCoinvAction (b : cellLeviParabolic F β γ w) :
    Representation.Coinvariants (cellRepA β γ w σ) →ₗ[ℂ]
      Representation.Coinvariants (cellRepA β γ w σ) :=
  Representation.Coinvariants.lift _ ((Representation.Coinvariants.mk _) ∘ₗ cellRepM β γ w σ b)
    fun a => by
      ext v
      simp only [LinearMap.coe_comp, Function.comp_apply]
      have := congrArg (fun T : Module.End ℂ W => T v) (cellRepM_mul_cellRepA σ b a)
      simp only [Module.End.mul_apply] at this
      rw [this, Representation.Coinvariants.mk_self_apply]
theorem cellCoinvAction_mk (b : cellLeviParabolic F β γ w) (v : W) :
    cellCoinvAction σ b (Representation.Coinvariants.mk _ v) =
      Representation.Coinvariants.mk _ (cellRepM β γ w σ b v) := rfl
def cellCoinvRep : Representation ℂ (cellLeviParabolic F β γ w)
    (Representation.Coinvariants (cellRepA β γ w σ)) where
  toFun := cellCoinvAction σ
  map_one' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [cellCoinvAction_mk])
  map_mul' b b' := Representation.Coinvariants.hom_ext (LinearMap.ext fun v => by
    simp [cellCoinvAction_mk, Module.End.mul_apply])
end Coinvariants
end Parabolic
end GroundTheory.Automorphic


