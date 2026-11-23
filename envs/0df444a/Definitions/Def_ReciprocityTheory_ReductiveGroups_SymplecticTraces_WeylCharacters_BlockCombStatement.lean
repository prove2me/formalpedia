-- Prove2me | Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
-- name    : ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_BlockCombStatement
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T21:25:55.429813+00:00
-- url     : https://prove2.me/theorems/f32c3771-a33a-4590-a2ba-371a705aa71c
-- title:
--   Block Comb Statement
-- statement:
--   Definitions and structural lemmas for Block Comb Statement, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/SymplecticTraces/WeylCharacters/BlockCombStatement.lean

import Definitions.Def_ReciprocityTheory_ReductiveGroups_SymplecticTraces_WeylCharacters_AntitoneOfMemInterl
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
namespace ReciprocityTheory.ChartRestriction.TR.Weyl
def numK {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K) : K :=
  ∑ σ ∈ (univ : Finset (Equiv.Perm (Fin n))).filter (fun σ => ∀ i, ε (σ i) = ε i),
    ((Equiv.Perm.sign σ : ℤ) : K) * ∏ i, t (σ i) ^ a i
def wdenK {K : Type*} [Field K] {n : ℕ} (ε : Fin n → Bool) (t : Fin n → K) : K :=
  ∏ i : Fin n, ∏ j : Fin n, if i < j ∧ ε i = ε j then t i - t j else 1
def rhoK {n : ℕ} (ε : Fin n → Bool) : Fin n → ℤ :=
  fun i => ((univ.filter fun j : Fin n => i < j ∧ ε j = ε i).card : ℤ)
def cnt {n : ℕ} (ε : Fin n → Bool) (b : Bool) : ℕ := (univ.filter fun i : Fin n => ε i = b).card
def blk {n : ℕ} (ε : Fin n → Bool) (b : Bool) : Fin (cnt ε b) → Fin n :=
  fun r => (univ.filter fun i : Fin n => ε i = b).orderEmbOfFin rfl r
def BlockCombStatement : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (ε : Fin n → Bool) (a : Fin n → ℤ) (t : Fin n → K),
    wdenK ε t = wden (cnt ε true) (t ∘ blk ε true) * wden (cnt ε false) (t ∘ blk ε false) ∧
    numK ε a t = alt (cnt ε true) (a ∘ blk ε true) (t ∘ blk ε true) *
      alt (cnt ε false) (a ∘ blk ε false) (t ∘ blk ε false) ∧
    ∀ b : Bool, rhoK ε ∘ blk ε b = delta (cnt ε b)
end ReciprocityTheory.ChartRestriction.TR.Weyl


