-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ScholzeWeinsteinB_b46feb887be11d09
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__ScholzeWeinsteinB_b46feb887be11d09
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:29:37.592192+00:00
-- url     : https://prove2.me/theorems/52e7a44c-d4ea-4e89-9ce2-a57813382cdb
-- title:
--   Scholze Weinstein B
-- statement:
--   Definitions and structural lemmas for Scholze Weinstein B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/ScholzeWeinsteinB.lean

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ToSpanSingletonConstGenInjective
import Theorems.Thm_GlobalTheory_IsBicharacter_baseChange
import Theorems.Thm_GlobalTheory_IsPerfectBicharacter_baseChange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Ideal
open scoped TensorProduct
namespace GlobalTheory.Published
open GlobalTheory.PDivGroup
def ScholzeWeinsteinB : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x, G.hodgeTateLinear x = 0 → H.hodgeTateLinear (f.baseChange O x) = 0) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule O (O ⊗[ℤ_[p]] (Fin h → ℤ_[p]))),
        (∀ (c : O) (x : O ⊗[ℤ_[p]] (Fin h → ℤ_[p])), c ≠ 0 → c • x ∈ W → x ∈ W) →
          ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
            ∀ x, G.hodgeTateLinear x = 0 ↔ e.toLinearMap.baseChange O x ∈ W
end GlobalTheory.Published


