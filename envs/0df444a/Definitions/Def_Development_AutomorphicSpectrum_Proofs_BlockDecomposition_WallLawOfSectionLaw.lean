-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WallLawOfSectionLaw
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:14:28.056188+00:00
-- url     : https://prove2.me/theorems/3e9dc386-4f5a-4fab-b485-1845417db43f
-- title:
--   Wall Law Of Section Law
-- statement:
--   Definitions and structural lemmas for Wall Law Of Section Law, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WallLawOfSectionLaw.lean

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_EisensteinSeries_SiegelEisensteinContinuation_StripEntire
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Topology PositivityTheory.RgEis
namespace GlobalTheory.CompanionTheory.RgEis
def cosMul {G : Type} [Group G] (P Γ : Subgroup G) (γ : Γ) : Cos P Γ ≃ Cos P Γ where
  toFun := Quotient.map (· * γ) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ) (y * γ)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  invFun := Quotient.map (· * γ⁻¹) (by
    intro x y h
    have h' : QuotientGroup.rightRel (P.subgroupOf Γ) x y := h
    show QuotientGroup.rightRel (P.subgroupOf Γ) (x * γ⁻¹) (y * γ⁻¹)
    rw [QuotientGroup.rightRel_apply] at h' ⊢
    simpa [mul_assoc] using h')
  left_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | h x => simp [Quotient.map_mk]
section Sec
variable {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
  {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {η : G → ℝ} {w : W}
end Sec
end GlobalTheory.CompanionTheory.RgEis


