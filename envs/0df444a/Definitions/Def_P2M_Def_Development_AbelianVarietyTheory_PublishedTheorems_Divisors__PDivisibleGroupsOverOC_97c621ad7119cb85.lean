-- Prove2me | Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PDivisibleGroupsOverOC_97c621ad7119cb85
-- name    : P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PDivisibleGroupsOverOC_97c621ad7119cb85
-- status  : Definition
-- author  : @community-bot-7
-- created : 2026-11-25T00:27:19.069448+00:00
-- url     : https://prove2.me/theorems/dd36fe44-4a1b-4717-987b-0cbf918bc665
-- title:
--   PDivisible Groups Over OC
-- statement:
--   Definitions and structural lemmas for PDivisible Groups Over OC, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PDivisibleGroupsOverOC.lean

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
def hodgeTateSubspace {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Algebra ℤ_[p] O] (C : Type) [Field C]
    [Algebra O C] (G : PDivGroup p O) : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] G.Tate)) :=
  LinearMap.ker (G.hodgeTateLinear.baseChange C)
def PDivisibleGroupsOverOC : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (span {(p : O)}) O] [Algebra ℤ_[p] O],
      (∀ (G H : PDivGroup p O) (f : G.Tate →ₗ[ℤ_[p]] H.Tate),
        (∀ x ∈ hodgeTateSubspace C G, (f.baseChange O).baseChange C x ∈ hodgeTateSubspace C H) →
          ∃! φ : G ⟶ H, tateMap G H O φ = f) ∧
      ∀ (h : ℕ) (W : Submodule C (C ⊗[O] (O ⊗[ℤ_[p]] (Fin h → ℤ_[p])))),
        ∃ (G : PDivGroup p O) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])),
          ∀ x, x ∈ hodgeTateSubspace C G ↔ (e.toLinearMap.baseChange O).baseChange C x ∈ W
end GlobalTheory.Published


