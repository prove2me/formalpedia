-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InertiaQuotientTransport
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InertiaQuotientTransport
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:17:17.421924+00:00
-- url     : https://prove2.me/theorems/44985712-db57-492b-bf13-99beba3cf48a
-- title:
--   Inertia Quotient Transport
-- statement:
--   Definitions and structural lemmas for Inertia Quotient Transport, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InertiaQuotientTransport.lean

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_GelfandSpectralNormalisation_NormalisedInvariants_PTConclAt
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_NineTermExactIff
import Theorems.Thm_GlobalTheory_CompanionTheory_PTIso_subgroupIso_coe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CompanionTheory.PTIso.subgroupIso_coe


set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion GlobalTheory.CompanionTheory.PTIso
namespace GlobalTheory.CompanionTheory.PTIso
def quotientIso {A B : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [Group B] [TopologicalSpace B] [IsTopologicalGroup B] (Φ : A ≃ₜ* B)
    (H : Subgroup A) (K : Subgroup B) [H.Normal] [K.Normal] (h : ∀ a, a ∈ H ↔ Φ a ∈ K) :
    A ⧸ H ≃ₜ* B ⧸ K where
  toMulEquiv := QuotientGroup.congr H K (Φ : A ≃* B) (by
    ext b
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h a).1 ha
    · intro hb
      exact ⟨Φ.symm b, (h _).2 (by simpa using hb), Φ.apply_symm_apply b⟩)
  continuous_toFun := by
    exact (QuotientGroup.isQuotientMap_mk H).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.continuous)
  continuous_invFun := by
    exact (QuotientGroup.isQuotientMap_mk K).continuous_iff.2
      (QuotientGroup.continuous_mk.comp Φ.symm.continuous)
end GlobalTheory.CompanionTheory.PTIso


