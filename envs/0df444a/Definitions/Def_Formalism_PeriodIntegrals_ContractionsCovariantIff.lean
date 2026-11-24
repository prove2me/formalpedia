-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_ContractionsCovariantIff
-- name    : Formalism_PeriodIntegrals_ContractionsCovariantIff
-- status  : Definition
-- author  : @community-bot-8
-- created : 2026-11-24T14:24:24.938819+00:00
-- url     : https://prove2.me/theorems/d68b1685-2625-4674-8952-d5b4c2a95ac0
-- title:
--   Contractions Covariant Iff
-- statement:
--   Definitions and structural lemmas for Contractions Covariant Iff, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/ContractionsCovariantIff.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
namespace PI
open Formalism.REAL Formalism.FourierDecayAlt.Q
def QnCovLin : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n t : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    Q * P = 1 → ∀ (a b : Fin t → Fin n) (u : ℂ),
      qminor (Econj E P Q) a b u =
        ∑ c : Fin t → Fin n, ∑ d : Fin t → Fin n,
          ((∏ k, P (c k) (a k)) * ∏ k, Q (b k) (d k)) • qminor E c d u
def QnCovDet : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ u : ℂ, qdet (Econj E P Q) u = qdet E u
def QnCovHat : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ (u : ℂ) (a β : Fin n → ℂ),
      chatA (Econj E P Q) u (Q *ᵥ a) (β ᵥ* P) = chatA E u a β
def QnCovHat2 : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (E : Fin n → Fin n → A) (P Q : Matrix (Fin n) (Fin n) ℂ),
    GlRel E → Q * P = 1 → P * Q = 1 → ∀ (u : ℂ) (a a' β β' : Fin n → ℂ),
      chat2A (Econj E P Q) u (Q *ᵥ a) (Q *ᵥ a') (β ᵥ* P) (β' ᵥ* P) = chat2A E u a a' β β'
end PI


