-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeFundamentalDomainVolume
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:49:48.65526+00:00
-- url     : https://prove2.me/theorems/fc6d60e3-a8f5-4864-89d4-2862bd568994
-- title:
--   Lattice Fundamental Domain Volume
-- statement:
--   Definitions and structural lemmas for Lattice Fundamental Domain Volume, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LatticeFundamentalDomainVolume.lean

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_CountData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
noncomputable section
namespace GlobalTheory.CompanionTheory.SW.FD
open scoped Pointwise
variable {F : Type} [Field F] [NumberField F]
def scaleMap (ρ : InfinitePlace F → (F →+* ℝ)) (N : ℕ) : 𝓞 F →+ (InfinitePlace F → ℝ) where
  toFun r := fun w => ρ w ((N : F) * (r : F))
  map_zero' := by ext w; simp
  map_add' a b := by ext w; simp [mul_add]
theorem embedding_bijective (hF : IsTotallyReal F) :
    Function.Bijective (fun w : InfinitePlace F => (w.embedding : F →+* ℂ)) := by
  constructor
  · intro w w' h
    have := congrArg InfinitePlace.mk h
    simpa using this
  · intro φ
    have hr : ComplexEmbedding.IsReal φ :=
      InfinitePlace.isReal_mk_iff.1 (hF.isReal (InfinitePlace.mk φ))
    exact ⟨InfinitePlace.mk φ, InfinitePlace.embedding_mk_eq_of_isReal hr⟩
def placeEquiv (hF : IsTotallyReal F) : InfinitePlace F ≃ (F →ₐ[ℚ] ℂ) :=
  (Equiv.ofBijective _ (embedding_bijective hF)).trans (RingHom.equivRatAlgHom F ℂ)
end GlobalTheory.CompanionTheory.SW.FD


