-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_RTTIndependence
-- name    : Formalism_PeriodIntegrals_RTTIndependence
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:27.529802+00:00
-- url     : https://prove2.me/theorems/fb3d4289-d544-4479-bbc0-405fbb0963d9
-- title:
--   RTTIndependence
-- statement:
--   Definitions and structural lemmas for RTTIndependence, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/RTTIndependence.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementW
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
namespace PI
open Formalism Formalism.FourierDecayAlt
def RTTSandwich : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A) (p c ci p' c' ci' : A),
    YangianSpanCharacter.T.WeylRel p c ci → YangianSpanCharacter.T.WeylRel p' c' ci' →
    (∀ x ∈ ({p, c, ci} : Set A), ∀ y ∈ ({p', c', ci'} : Set A), x * y = y * x) →
    (∀ x ∈ ({p, c, ci, p', c', ci'} : Set A), ∀ Y a b, x * QQ Y a b = QQ Y a b * x) →
    ∀ Y Y' : ℂ,
      let C : ℂ → A := fun y => (YangianSpanCharacter.T.Tm y p' c' ci' * QQ y * YangianSpanCharacter.T.Tm y p c ci) 0 0
      let X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A :=
        ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A) * YangianSpanCharacter.T.E1 (QQ Y') * YangianSpanCharacter.T.E2 (QQ Y) -
          YangianSpanCharacter.T.E2 (QQ Y) * YangianSpanCharacter.T.E1 (QQ Y') * ((Y' - Y) • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - YangianSpanCharacter.T.Pf A)
      algebraMap ℂ A (Y' - Y - 1) * (C Y' * C Y - C Y * C Y') =
        ((YangianSpanCharacter.T.T2 Y p' c' ci' * YangianSpanCharacter.T.T1 Y' p' c' ci') * X * (YangianSpanCharacter.T.T1 Y' p c ci * YangianSpanCharacter.T.T2 Y p c ci)) (0, 0) (0, 0)
def RTTIndependence : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (x : Fin 2 × Fin 2 → Fin 2 × Fin 2 → V) (Y Y' : ℂ), Y' ≠ Y + 1 →
    (∀ (c : ℂ), c ≠ 0 → ∀ (β : ℂ) (n : ℤ),
      ∑ A : Fin 2 × Fin 2, ∑ B : Fin 2 × Fin 2,
        ((if A = (0, 0) then (Y - β) * (Y' - β) else if A = (0, 1) then Y' - β else if A = (1, 0) then Y - β + 1 else 1) *
          (if B = (0, 0) then (Y' + (β + n)) * (Y + (β + n)) else if B = (0, 1) then Y' + (β + n) - 1
            else if B = (1, 0) then Y + (β + n) else 1) *
          (((‖c‖ : ℂ) ^ (2 * β)) * c ^ n * (c ^ ((B.1 : ℕ) + (B.2 : ℕ)))⁻¹ * (star c ^ ((A.1 : ℕ) + (A.2 : ℕ)))⁻¹)) • x A B = 0) →
    ∀ A B, x A B = 0
def QdetFromRTT : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (QQ : ℂ → Matrix (Fin 2) (Fin 2) A), W.IsRTT QQ → ∀ Y : ℂ, ∃ qh : A,
    (QQ (Y + 1))ᵀ * YangianSpanCharacter.T.J A * QQ Y = qh • YangianSpanCharacter.T.J A ∧ QQ Y * YangianSpanCharacter.T.J A * (QQ (Y + 1))ᵀ = qh • YangianSpanCharacter.T.J A ∧
    ∀ Y' a b, qh * QQ Y' a b = QQ Y' a b * qh
def LemmaD : Prop :=
  ∀ (A : Type) [CommRing A] [IsDomain A] (DD : ℕ → Set (A →+ A)), DD 0 = {0} →
    (∀ n, ∀ D ∈ DD (n + 1), ∀ a : A, ∃ D' ∈ DD n, ∀ b, D' b = D (a * b) - a * D b) →
    ∀ A' : AddSubgroup A, (∀ x ∈ A', ∀ y ∈ A', x * y ∈ A') →
    (∀ b : A, ∃ a₁ ∈ A', ∃ a₂ ∈ A', a₂ ≠ 0 ∧ a₂ * b = a₁) →
    ∀ n, ∀ D ∈ DD n, (∀ x ∈ A', D x = 0) → D = 0
end PI


