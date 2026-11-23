-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_NormGramAtOrigin
-- name    : Formalism_PeriodIntegrals_NormGramAtOrigin
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T01:27:34.361299+00:00
-- url     : https://prove2.me/theorems/7a45b4c1-ef2a-4cb3-ae04-1e6e386e1b41
-- title:
--   Norm Gram At Origin
-- statement:
--   Definitions and structural lemmas for Norm Gram At Origin, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/NormGramAtOrigin.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
namespace PI.NormGramAtOrigin
section G
variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n]
def hform (σ : A →+* A) (J : Matrix n n A) (x y : n → A) : A := ∑ i, ∑ j, σ (x i) * J i j * y j
end G
def gram {E : Type} [Field E] (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E) (X : Fin r → Fin n → E) :
    Matrix (Fin r) (Fin r) E := fun a b => hform σ J (X a) (X b)
def Statement : Prop :=
  ∀ (E : Type) [Field E] [StarRing E] [CharZero E] (n r : ℕ), r ≤ n →
    ∀ J : Matrix (Fin n) (Fin n) E, (∀ i j, star (J j i) = J i j) → J.det ≠ 0 →
      ∃ X : Fin r → Fin n → E, (gram (starRingEnd E) J X).det ≠ 0
end PI.NormGramAtOrigin


