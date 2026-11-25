-- Prove2me | Definitions.Def_GroundTheory_AutomorphicForms_WhittakerDistribution
-- name    : GroundTheory_AutomorphicForms_WhittakerDistribution
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T00:28:40.799158+00:00
-- url     : https://prove2.me/theorems/52940e08-cd8f-49f1-bc3f-162696968152
-- title:
--   Whittaker Distribution
-- statement:
--   Definitions and structural lemmas for Whittaker Distribution, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerDistribution.lean

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLSpace
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerOrbit
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerGroups
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerRelevance
import Theorems.Thm_GroundTheory_Automorphic_GLnLocal_quotientEquivLattice_mk
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_GoodPiece_smul
import Theorems.Thm_GroundTheory_Automorphic_Whittaker_transl_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GroundTheory.Automorphic.GLnLocal.quotientEquivLattice_mk
attribute [local simp] GroundTheory.Automorphic.Whittaker.transl_apply


set_option autoImplicit false
namespace GroundTheory.Automorphic
namespace Whittaker
open Set Topology MulAction Matrix DoubleCoset ValuativeRel
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] {n : ℕ}
section Action
variable (F n) in

abbrev NN := (Iwasawa.unipotent F n) × (Iwasawa.unipotent F n)
@[instance_reducible]
def biAction : MulAction (NN F n) (GL (Fin n) F) where
  smul h g := (h.1 : GL (Fin n) F) * g * (h.2 : GL (Fin n) F)⁻¹
  one_smul g := by
    show ((1 : NN F n).1 : GL (Fin n) F) * g * ((1 : NN F n).2 : GL (Fin n) F)⁻¹ = g
    simp
  mul_smul h k g := by
    show ((h * k).1 : GL (Fin n) F) * g * ((h * k).2 : GL (Fin n) F)⁻¹ =
      (h.1 : GL (Fin n) F) * ((k.1 : GL (Fin n) F) * g * (k.2 : GL (Fin n) F)⁻¹) *
        (h.2 : GL (Fin n) F)⁻¹
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul, _root_.mul_inv_rev]
    group
attribute [local instance] biAction
variable (ψ₀ : AddChar F ℂ)
noncomputable def chi : NN F n →* ℂ where
  toFun h := psiN ψ₀ (h.1 : GL (Fin n) F) * (psiN ψ₀ (h.2 : GL (Fin n) F))⁻¹
  map_one' := by simp [psiN_one]
  map_mul' h k := by
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    rw [psiN_mul ψ₀ h.1.2 k.1.2, psiN_mul ψ₀ h.2.2 k.2.2, mul_inv]
    ring
def swapTheta (h : NN F n) : NN F n := (thetaN h.2, thetaN h.1)
end Action
attribute [local instance] biAction
section Pull
variable [TopologicalSpace F] [IsTopologicalRing F]
def sigmaL : (GL (Fin n) F → ℂ) →ₗ[ℂ] (GL (Fin n) F → ℂ) := LinearMap.funLeft ℂ ℂ sigma
theorem sigmaL_mem_supportedIn {U : Set (GL (Fin n) F)} {f : GL (Fin n) F → ℂ}
    (hf : f ∈ supportedIn U) : sigmaL f ∈ supportedIn (sigma ⁻¹' U) := by
  refine ⟨⟨hf.1.1.comp_continuous continuous_sigma, ?_⟩, fun x hx => hf.2 hx⟩
  exact hf.1.2.comp_homeomorph sigmaHomeo
variable (ψ₀ : AddChar F ℂ)
noncomputable abbrev rel (n : ℕ) (ψ₀ : AddChar F ℂ) : Submodule ℂ (GL (Fin n) F → ℂ) := relSpan (chi (n := n) ψ₀) (univ : Set (GL (Fin n) F))
noncomputable def goodSub (n : ℕ) (ψ₀ : AddChar F ℂ) : Submodule ℂ (GL (Fin n) F → ℂ) := (rel n ψ₀).comap (LinearMap.id - sigmaL)
end Pull
section LocalField
variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
theorem totallyDisconnectedSpace_localField : TotallyDisconnectedSpace F := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro x
  refine Set.Subset.antisymm (fun y hy => ?_) (Set.singleton_subset_iff.mpr mem_connectedComponent)
  have hball : ∀ m : ℕ, valuation F (y - x) ≤ valuation F (GLnLocal.uniformizer F : F) ^ m := by
    intro m
    have hγ : valuation F (GLnLocal.uniformizer F : F) ^ m ≠ 0 :=
      pow_ne_zero _ (GLnLocal.valuation_uniformizer_ne_zero F)
    let S : Set F := (fun z => z - x) ⁻¹' {z : F | valuation F z ≤
      valuation F (GLnLocal.uniformizer F : F) ^ m}
    have hSo : IsOpen S := (GLnLocal.isOpen_valuation_le F hγ).preimage (continuous_sub_right x)
    have hSc : IsClosed S :=
      (IsNonarchimedeanLocalField.isCompact_closedBall F _).isClosed.preimage
        (continuous_sub_right x)
    have hxS : x ∈ S := by simp [S]
    exact IsClopen.connectedComponent_subset ⟨hSc, hSo⟩ hxS hy
  have := GLnLocal.eq_zero_of_forall_valuation_le F hball
  exact Set.mem_singleton_iff.2 (sub_eq_zero.1 this)
attribute [local instance] totallyDisconnectedSpace_localField
theorem continuousSMul_biAction : ContinuousSMul (NN F n) (GL (Fin n) F) := by
  refine ⟨?_⟩
  have e : (fun p : NN F n × GL (Fin n) F => p.1 • p.2) = fun p =>
      ((p.1.1 : GL (Fin n) F)) * p.2 * ((p.1.2 : GL (Fin n) F))⁻¹ := rfl
  rw [e]
  have h1 : Continuous fun p : NN F n × GL (Fin n) F => ((p.1.1 : GL (Fin n) F)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_fst)
  have h2 : Continuous fun p : NN F n × GL (Fin n) F => ((p.1.2 : GL (Fin n) F)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_fst)
  exact (h1.mul continuous_snd).mul h2.inv
attribute [local instance] continuousSMul_biAction
def cellGe (g : GL (Fin n) F) : Set (GL (Fin n) F) := {h | ∀ i j, llRank i j g ≤ llRank i j h}
def cellLe (g : GL (Fin n) F) : Set (GL (Fin n) F) := {h | ∀ i j, llRank i j h ≤ llRank i j g}
variable (ψ₀ : AddChar F ℂ)
def Irrelevant (w : Equiv.Perm (Fin n)) (t : Fin n → Fˣ) : Prop :=
  ∃ i j : Fin n, i < j ∧ w i < w j ∧ ∃ a : F,
    psiN ψ₀ (rootElt (w i) (w j) ((t (w i) : F) / (t (w j) : F) * a)) ≠ psiN ψ₀ (rootElt i j a)
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in

theorem twoSided_mem [IsTopologicalRing F] {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) (a b : GL (Fin n) F) :
    (fun x => f (a⁻¹ * x * b)) ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ := by
  refine ⟨hf.1.comp_continuous (by fun_prop), ?_⟩
  exact hf.2.comp_homeomorph ((Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight b))
omit [ValuativeRel F] [IsNonarchimedeanLocalField F] in

theorem comp_sigma_mem [IsTopologicalRing F] {f : GL (Fin n) F → ℂ}
    (hf : f ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ) :
    (fun x => f (sigma x)) ∈ locallyConstantCompactSupport (GL (Fin n) F) ℂ ℂ :=
  (sigmaL_mem_supportedIn (U := univ) ⟨hf, subset_univ _⟩).1
end LocalField
end Whittaker
end GroundTheory.Automorphic


