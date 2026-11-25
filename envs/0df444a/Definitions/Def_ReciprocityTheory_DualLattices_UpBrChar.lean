-- Prove2me | Definitions.Def_ReciprocityTheory_DualLattices_UpBrChar
-- name    : ReciprocityTheory_DualLattices_UpBrChar
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-25T18:21:03.260388+00:00
-- url     : https://prove2.me/theorems/51e39aee-0c2c-4692-bd3d-6b1ffa7177ce
-- title:
--   Up Br Char
-- statement:
--   Definitions and structural lemmas for Up Br Char, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/DualLattices/UpBrChar.lean

import Definitions.Def_ReciprocityTheory_DualLattices_DetIntegralNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
namespace ReciprocityTheory.PGsh.Up
def omTr {R : Type} [CommRing R] {g N : ℕ} (M : Matrix (Fin g) (Fin N) R) (s : ℕ) (hs : s ≤ g) :
    Submodule R (Fin s → R) :=
  Submodule.span R (Set.range fun b : Fin N => fun a : Fin s => M (Fin.castLE hs a) b)
def CharStatement : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (g N : ℕ) (M : Matrix (Fin g) (Fin N) R) (c : R), c ≠ 0 →
    (∀ s (hs : s ≤ g), ∀ w : Fin s → R, c • w ∈ omTr M s hs) →
    ∃ ι : Fin g → Fin N, Function.Injective ι ∧ ∀ s (hs : s ≤ g),
      Submodule.span R (Set.range fun b : Fin s => fun a : Fin s => M (Fin.castLE hs a) (ι (Fin.castLE hs b)))
        = omTr M s hs
section Char
variable {R : Type} [CommRing R] [IsDomain R]
variable {C : Type} [Field C] {v : Valuation C NNReal} [Algebra R C]
end Char
end ReciprocityTheory.PGsh.Up


