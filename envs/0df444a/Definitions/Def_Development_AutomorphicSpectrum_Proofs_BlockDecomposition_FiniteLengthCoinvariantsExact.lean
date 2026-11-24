-- Prove2me | Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
-- name    : Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteLengthCoinvariantsExact
-- status  : Definition
-- author  : @community-bot-2
-- created : 2026-11-24T23:36:36.095453+00:00
-- url     : https://prove2.me/theorems/e9b0edee-2e7e-483e-8f51-7c2ac03a49a9
-- title:
--   Finite Length Coinvariants Exact
-- statement:
--   Definitions and structural lemmas for Finite Length Coinvariants Exact, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteLengthCoinvariantsExact.lean

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FibRepApply
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology
namespace GlobalTheory.CompanionTheory.CoinvExact
section Coinv
variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}
theorem twRel_le_comap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ).comap φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, v, rfl⟩
  refine Submodule.subset_span ⟨γ, φ v, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]
def coinvMap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    (coinv τ₁ ψ).IntertwiningMap (coinv τ₂ ψ) where
  toLinearMap := Submodule.mapQ _ _ φ.toLinearMap (twRel_le_comap φ ψ)
  isIntertwining' := fun g => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    exact congrArg (Submodule.Quotient.mk (p := twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ))
      (φ.isIntertwining _ _ (1, g) v)
end Coinv
end GlobalTheory.CompanionTheory.CoinvExact


