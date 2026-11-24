-- Prove2me | Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
-- name    : GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PAnalyticGermsNoetherian
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:51.083783+00:00
-- url     : https://prove2.me/theorems/a2eb321f-81ef-4059-92ab-32d5a2d1d87d
-- title:
--   PAnalytic Germs Noetherian
-- statement:
--   Definitions and structural lemmas for PAnalytic Germs Noetherian, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/HeightsAndTheta/Heights/ComplexAnalyticSets/PAnalyticGermsNoetherian.lean

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StAnalyticGermsNoetherian
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermGeneralCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter
noncomputable section
theorem tendsto_nhds_of_analyticAt_eq {σ τ : Type} [Fintype σ] [Fintype τ] {h : (σ → ℂ) → (τ → ℂ)} {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : Tendsto h (𝓝 a) (𝓝 b) := by
  rw [← hab]; exact hh.continuousAt.tendsto
def germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) : holGerms b →+* holGerms a where
  toFun φ := ⟨(φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab), by
      obtain ⟨f, hf, hφ⟩ := φ.2
      exact ⟨f ∘ h, hf.comp_of_eq hh hab, by rw [← hφ]; rfl⟩⟩
  map_one' := rfl
  map_mul' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ * ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) *
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_mul, ← hf, ← hg]; rfl
  map_zero' := rfl
  map_add' φ ψ := by
    obtain ⟨f, -, hf⟩ := φ.2
    obtain ⟨g, -, hg⟩ := ψ.2
    apply Subtype.ext
    show ((φ + ψ : holGerms b) : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) =
      (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) +
        (ψ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab)
    rw [Subring.coe_add, ← hf, ← hg]; rfl
theorem germPull_coe {σ τ : Type} [Fintype σ] [Fintype τ] (h : (σ → ℂ) → (τ → ℂ)) {a : σ → ℂ} {b : τ → ℂ}
    (hh : AnalyticAt ℂ h a) (hab : h a = b) (φ : holGerms b) (f : (τ → ℂ) → ℂ)
    (hφ : (f : Germ (𝓝 b) ℂ) = φ) : ((germPull h hh hab φ : holGerms a) : Germ (𝓝 a) ℂ) = ↑(f ∘ h) := by
  show (φ : Germ (𝓝 b) ℂ).compTendsto h (tendsto_nhds_of_analyticAt_eq hh hab) = _
  rw [← hφ]; rfl
theorem germPull_germPull {σ τ : Type} [Fintype σ] [Fintype τ] (h₁ : (σ → ℂ) → (τ → ℂ))
    (h₂ : (τ → ℂ) → (σ → ℂ)) {a : σ → ℂ} {b : τ → ℂ} (hh₁ : AnalyticAt ℂ h₁ a) (hab : h₁ a = b)
    (hh₂ : AnalyticAt ℂ h₂ b) (hba : h₂ b = a) (h₁₂ : ∀ y, h₁ (h₂ y) = y) (φ : holGerms b) :
    germPull h₂ hh₂ hba (germPull h₁ hh₁ hab φ) = φ := by
  obtain ⟨f, hf, hφ⟩ := φ.2
  apply Subtype.ext
  have e1 := germPull_coe h₁ hh₁ hab φ f hφ
  rw [germPull_coe h₂ hh₂ hba _ (f ∘ h₁) e1.symm, ← hφ]
  congr 1
  funext y
  simp [h₁₂]
def germAffineEquiv {σ τ : Type} [Fintype σ] [Fintype τ] (e : (σ → ℂ) ≃L[ℂ] (τ → ℂ)) (c : τ → ℂ) :
    holGerms c ≃+* holGerms (0 : σ → ℂ) :=
  have h1 : AnalyticAt ℂ (fun z : σ → ℂ => e z + c) 0 := (e.analyticAt 0).add analyticAt_const
  have h1e : (fun z : σ → ℂ => e z + c) 0 = c := by simp
  have h2 : AnalyticAt ℂ (fun y : τ → ℂ => e.symm (y - c)) c :=
    (e.symm.analyticAt _).comp (analyticAt_id.sub analyticAt_const)
  have h2e : (fun y : τ → ℂ => e.symm (y - c)) c = 0 := by simp
  RingEquiv.ofRingHom (germPull _ h1 h1e) (germPull _ h2 h2e)
    (RingHom.ext fun φ => germPull_germPull _ _ h2 h2e h1 h1e (fun z => by simp) φ)
    (RingHom.ext fun φ => germPull_germPull _ _ h1 h1e h2 h2e (fun y => by simp) φ)
end
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets


