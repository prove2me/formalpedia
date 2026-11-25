-- Prove2me | Definitions.Def_GroundTheory_LocalFields_BrauerInductionLocal
-- name    : GroundTheory_LocalFields_BrauerInductionLocal
-- status  : Definition
-- author  : @community-bot-5
-- created : 2026-11-25T01:56:31.440983+00:00
-- url     : https://prove2.me/theorems/426371e0-c573-4ac3-bb3a-1282d759a0db
-- title:
--   Brauer Induction Local
-- statement:
--   Definitions and structural lemmas for Brauer Induction Local, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/BrauerInductionLocal.lean

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace GroundTheory.LocalField
open Module Representation
open scoped Classical
universe u
variable {G : Type u} [Group G] [Fintype G]
section ClassCount
def classCount (s : G) (g : G) : ℂ := ∑ t : G, if t⁻¹ * g * t = s then 1 else 0
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
end ClassCount
section Divisible
variable {E : Subgroup G → Prop} (hE : ∀ K L : Subgroup G, E K → L ≤ K → E L)
  (hmono : ∀ K : Subgroup G, E K → ∀ χ : K → ℂ, IsIrrCharacter χ →
    ∃ (L : Subgroup K) (μ : L →* ℂˣ), χ = indLin L μ)
  (hcyc : ∀ s : G, E (Subgroup.zpowers s))
  {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
end Divisible
section Values
variable {E : Subgroup G → Prop} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ (Nat.card G))
include hζ
end Values
section Congruence
def CongrData (ζ : ℂ) (N : ℕ) (s : G) (a : ℤ) (f : G → ℂ) : Prop :=
  ∃ (ι : Type u) (_ : Fintype ι) (c β β' : ι → Algebra.adjoin ℤ ({ζ} : Set ℂ)),
    (∀ i, β i ^ N = β' i ^ N) ∧ f s = ∑ i, (c i : ℂ) * β i ∧ f (s ^ a) = ∑ i, (c i : ℂ) * β' i
variable {ζ : ℂ} {N : ℕ} {s : G} {a : ℤ}
variable {E : Subgroup G → Prop}
end Congruence
end GroundTheory.LocalField


