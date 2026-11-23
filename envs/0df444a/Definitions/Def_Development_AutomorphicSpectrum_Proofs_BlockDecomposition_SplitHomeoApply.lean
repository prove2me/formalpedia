-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SplitHomeoApply
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T19:24:26.226735+00:00
-- url     : https://prove2.me/theorems/671f1ddb-54f4-444b-acbe-171875efa392
-- title:
--   Split Homeo Apply
-- statement:
--   Definitions and structural lemmas for Split Homeo Apply, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SplitHomeoApply.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal
namespace GlobalTheory.CompanionTheory.SplitExtLat
variable {P G₁ : Type} [Group P] [Group G₁]
def splitMap (ι : G₁ →* P) (π : P →* G₁) : π.ker × G₁ → P := fun z => (z.1 : P) * ι z.2
def kerPart (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) (p : P) : π.ker :=
  ⟨p * (ι (π p))⁻¹, by simp [MonoidHom.mem_ker, h]⟩
def splitEquiv (ι : G₁ →* P) (π : P →* G₁) (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ P where
  toFun := splitMap ι π
  invFun p := (kerPart ι π h p, π p)
  left_inv z := by
    obtain ⟨⟨m, hm⟩, u⟩ := z
    have hm' : π m = 1 := hm
    ext <;> simp [splitMap, kerPart, hm', h]
  right_inv p := by simp [splitMap, kerPart]
def splitHomeo [TopologicalSpace P] [IsTopologicalGroup P] [TopologicalSpace G₁]
    (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π)
    (h : ∀ u, π (ι u) = u) : π.ker × G₁ ≃ₜ P where
  toEquiv := splitEquiv ι π h
  continuous_toFun := by
    change Continuous fun z : π.ker × G₁ => (z.1 : P) * ι z.2
    fun_prop
  continuous_invFun := by
    change Continuous fun p => (kerPart ι π h p, π p)
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _) hπ
    fun_prop
end GlobalTheory.CompanionTheory.SplitExtLat


