-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
-- name    : Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T13:33:39.614886+00:00
-- url     : https://prove2.me/theorems/e21ddd61-318a-4a7b-81a8-a72d3623686c
-- title:
--   Exists Greatest Proper Invariant Submodule Of Side
-- statement:
--   Definitions and structural lemmas for Exists Greatest Proper Invariant Submodule Of Side, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/CartanFactorisation/ExistsGreatestProperInvariantSubmoduleOfSide.lean

import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_CoreLM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace
namespace PositivityTheory.ThKF.Unit
open PositivityTheory.KReal
section Gen
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
end Gen
def One (p q r s : ℕ) (c : ℂ) : Prop :=
  ∃ K : Submodule ℂ (Pol p q r s), K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, fockAct2 p q r s W x ∈ K) ∧
    (∀ N, K ≤ N → (∀ W, ∀ x ∈ N, fockAct2 p q r s W x ∈ N) → N = K ∨ N = ⊤) ∧
    ∀ β : Pol p q r s →ₗ⋆[ℂ] Pol p q r s →ₗ[ℂ] ℂ,
      (∀ Z x y, β (fockAct1 p q r s Z x - (c * Z.trace) • x) y = 0) → (∀ Z x y, β y (fockAct1 p q r s Z x - (c * Z.trace) • x) = 0) →
      (∀ a b x y, β (fockAct2 p q r s (Eab a b) x) y = epsB a b * β x (fockAct2 p q r s (Eab b a) y)) → ∀ x ∈ K, β x = 0
end PositivityTheory.ThKF.Unit
end


