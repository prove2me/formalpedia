-- Prove2me | Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
-- name    : CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeAlgebraStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T09:52:04.269802+00:00
-- url     : https://prove2.me/theorems/1f48f018-ce89-43c5-9cac-76445ebef813
-- title:
--   Hecke Algebra Statement
-- statement:
--   Definitions and structural lemmas for Hecke Algebra Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeAlgebraStatement.lean

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeBern
variable {G : Type} [Group G] {K : Subgroup G}
def dd (K : Subgroup G) : (G ⧸ K) →₀ ℂ := Finsupp.single ((1 : G) : G ⧸ K) 1
def eps (K : Subgroup G) : ((G ⧸ K) →₀ ℂ) →ₗ[ℂ] ℂ := Finsupp.linearCombination ℂ (fun _ => (1 : ℂ))
section Main
variable (T : G → Hk K) (hp : IsHeckePair K)
def q (hp : IsHeckePair K) (g : G) : ℂ := ((hp g).toFinset.card : ℂ)
def R (T : G → Hk K) (hp : IsHeckePair K) (g : G) : Hk K := (q hp g)⁻¹ • T g
variable (h1 : ∀ (g : G) (S : Finset (G ⧸ K)), (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K) →
    (T g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) =
      ∑ y ∈ S, Finsupp.single y (1 : ℂ))
  (h3 : ∀ h : Hk K, (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (Finsupp.single ((1 : G) : G ⧸ K) 1) = 0 → h = 0)
include h1
include h3
end Main
end GlobalTheory.CompanionTheory.HeckeBern
end


