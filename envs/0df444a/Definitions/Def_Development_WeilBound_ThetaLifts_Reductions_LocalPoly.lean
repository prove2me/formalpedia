-- Prove2me | Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_LocalPoly
-- name    : Development_WeilBound_ThetaLifts_Reductions_LocalPoly
-- status  : Definition
-- author  : @community-bot-1
-- created : 2026-11-25T13:40:33.664228+00:00
-- url     : https://prove2.me/theorems/e27839da-3775-5360-a6d6-8878391b49fd
-- title:
--   Local Poly
-- statement:
--   Definitions and structural lemmas for Local Poly, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/Reductions/LocalPoly.lean

import Definitions.Def_Development_WeilBound_ThetaLifts_CartanFactorisation_ExistsGreatestProperInvariantSubmoduleOfSide
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
namespace PositivityTheory.ThKR.Join
open PositivityTheory.KReal PositivityTheory.ThKF.Unit
section Gen
variable {r s : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]
end Gen
def Two (p q r s : ℕ) (c : ℂ) : Prop :=
  ∃ K : Submodule ℂ (Pol p q r s), K ≠ ⊤ ∧ (∀ W, ∀ x ∈ K, fockAct2 p q r s W x ∈ K) ∧
    (∀ N, K ≤ N → (∀ W, ∀ x ∈ N, fockAct2 p q r s W x ∈ N) → N = K ∨ N = ⊤) ∧
    ∃ v : Pol p q r s, ∀ t : List (Pol p q r s), (∀ x ∈ t, x ∈ K) → ∀ y,
      ∃ u ∈ Algebra.adjoin ℂ (Set.range (fockAct2 p q r s)), u v - y ∈ coinvSub (act1 p q r s) (chiTr c) ∧
        ∀ x ∈ t, u x ∈ coinvSub (act1 p q r s) (chiTr c)
end PositivityTheory.ThKR.Join
end


