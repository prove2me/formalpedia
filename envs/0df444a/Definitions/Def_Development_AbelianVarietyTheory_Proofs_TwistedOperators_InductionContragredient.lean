-- Prove2me | Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
-- name    : Development_AbelianVarietyTheory_Proofs_TwistedOperators_InductionContragredient
-- status  : Definition
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:53.14556+00:00
-- url     : https://prove2.me/theorems/33c7754f-00f9-433c-9090-1f07adc0eaf1
-- title:
--   Induction Contragredient
-- statement:
--   Definitions and structural lemmas for Induction Contragredient, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/InductionContragredient.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwahoriProjSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeviIntegralFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsOpenNormalisedSubgroupSubset
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IntegralIntegralGLMulRightComplexProductSigma
import Theorems.Thm_GlobalTheory_SmGL_isLocallyConstant_smInd
import Theorems.Thm_GlobalTheory_SplitWeil_HasConductor_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Topology
namespace GlobalTheory.SmGL.IndDual
section Abstract
variable {G W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup W'] [Module ℂ W'] {P : Subgroup G}
def cell (P J : Subgroup G) : Set G := {g | ∃ p : P, (p : G)⁻¹ * g ∈ J}
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem cell_cases (J : Subgroup G) (g : G) : g ∉ cell P J ∨ ∃ p : P, ∃ j ∈ J, g = p * j := by
  by_cases h : g ∈ cell P J
  · obtain ⟨p, hp⟩ := h
    exact Or.inr ⟨p, _, hp, by simp⟩
  · exact Or.inl h
open Classical in

def extFun (σ : Representation ℂ P W) (J : Subgroup G) (φ : G → W) (g : G) : W :=
  if h : g ∈ cell P J then σ h.choose (φ ((h.choose : G)⁻¹ * g)) else 0
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem extFun_mul {σ : Representation ℂ P W} {J : Subgroup G} {φ : G → W}
    (hφ : ∀ p : P, (p : G) ∈ J → ∀ j ∈ J, φ (p * j) = σ p (φ j)) (p : P) {j : G} (hj : j ∈ J) :
    extFun σ J φ (p * j) = σ p (φ j) := by
  have h : (p : G) * j ∈ cell P J := ⟨p, by simpa using hj⟩
  rw [extFun, dif_pos h]
  have h1 := h.choose_spec
  generalize h.choose = q at h1
  have h2 : ((q⁻¹ * p : P) : G) ∈ J := by simpa [mul_assoc] using mul_mem h1 (inv_mem hj)
  have h3 := hφ _ h2 j hj
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc] at h3
  rw [h3, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem extFun_zero (σ : Representation ℂ P W) {J : Subgroup G} (φ : G → W) {g : G}
    (h : g ∉ cell P J) : extFun σ J φ g = 0 := dif_neg h
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem extFun_right {σ : Representation ℂ P W} {J : Subgroup G} {φ : G → W}
    (hφ : ∀ p : P, (p : G) ∈ J → ∀ j ∈ J, φ (p * j) = σ p (φ j)) {i : G} (hi : i ∈ J)
    (hφ' : ∀ j ∈ J, φ (j * i) = φ j) (g : G) : extFun σ J φ (g * i) = extFun σ J φ g := by
  rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
  · rw [extFun_zero _ _ h, extFun_zero]
    rintro ⟨p, hp⟩
    exact h ⟨p, by simpa [mul_assoc] using mul_mem hp (inv_mem hi)⟩
  · rw [mul_assoc, extFun_mul hφ p hj, extFun_mul hφ p (mul_mem hj hi), hφ' j hj]
def extInd (σ : Representation ℂ P W) {J I : Subgroup G} (hI : IsOpen (I : Set G)) (hle : I ≤ J) (φ : G → W)
    (hφ : ∀ p : P, (p : G) ∈ J → ∀ j ∈ J, φ (p * j) = σ p (φ j))
    (hφ' : ∀ i ∈ I, ∀ j ∈ J, φ (j * i) = φ j) : smoothPart (ind P σ) :=
  ⟨⟨extFun σ J φ, fun q g => by
      rcases cell_cases (P := P) J g with h | ⟨p, j, hj, rfl⟩
      · rw [extFun_zero _ _ h, extFun_zero, map_zero]
        rintro ⟨p, hp⟩
        exact h ⟨q⁻¹ * p, by simpa [mul_assoc] using hp⟩
      · rw [← mul_assoc, ← Subgroup.coe_mul, extFun_mul hφ _ hj, extFun_mul hφ _ hj, map_mul,
          Module.End.mul_apply]⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset (hI.mem_nhds (one_mem I)) fun i hi =>
      Subtype.ext (funext fun g => extFun_right hφ (hle hi) (hφ' i hi) g))⟩
omit [TopologicalSpace G] [IsTopologicalGroup G] in
theorem mem_fixed_iff {σ : Representation ℂ G W} {H : Subgroup G} {w : W} :
    w ∈ fixed σ H ↔ ∀ h ∈ H, σ h w = w :=
  ⟨fun hw h hh => by simpa using hw ⟨h, hh⟩, fun hw h => by simpa using hw h h.2⟩
def bump (σ : Representation ℂ P W) {J : Subgroup G} (hJ : IsOpen (J : Set G)) :
    fixed σ (J.subgroupOf P) →ₗ[ℂ] smoothPart (ind P σ) where
  toFun w := extInd σ hJ le_rfl (fun _ => w.1) (fun p hp _ _ => (mem_fixed_iff.1 w.2 p hp).symm)
    fun _ _ _ _ => rfl
  map_add' v w := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show extFun σ J (fun _ => v.1 + w.1) g = extFun σ J (fun _ => v.1) g + extFun σ J (fun _ => w.1) g
    unfold extFun
    split_ifs <;> simp
  map_smul' c w := by
    refine Subtype.ext (Subtype.ext (funext fun g => ?_))
    show extFun σ J (fun _ => c • w.1) g = c • extFun σ J (fun _ => w.1) g
    unfold extFun
    split_ifs <;> simp
variable [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure] {K : Subgroup G}
  (hK : IsCompact (K : Set G)) (σ : Representation ℂ P W) (τ : Representation ℂ P W')
  (B : W' →ₗ[ℂ] Module.Dual ℂ W)
omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
theorem continuous_pair (f' : smoothPart (ind P τ)) (f : smoothPart (ind P σ)) :
    Continuous fun x => B (f'.1.1 x) (f.1.1 x) :=
  ((isLocallyConstant_smInd f').comp₂ (isLocallyConstant_smInd f) fun l w => B l w).continuous
def pair : smoothPart (ind P τ) →ₗ[ℂ] Module.Dual ℂ (smoothPart (ind P σ)) :=
  LinearMap.mk₂ ℂ (fun f' f => ∫ x in (K : Set G), B (f'.1.1 x) (f.1.1 x) ∂μ)
    (fun f' g' f => by
      rw [← integral_add ((continuous_pair σ τ B f' f).continuousOn.integrableOn_compact hK)
        ((continuous_pair σ τ B g' f).continuousOn.integrableOn_compact hK)]
      simp)
    (fun c f' f => by rw [← integral_smul]; simp)
    (fun f' f g => by
      rw [← integral_add ((continuous_pair σ τ B f' f).continuousOn.integrableOn_compact hK)
        ((continuous_pair σ τ B f' g).continuousOn.integrableOn_compact hK)]
      simp)
    (fun c f' f => by rw [← integral_smul]; simp)
end Abstract
end GlobalTheory.SmGL.IndDual


