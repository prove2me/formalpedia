-- Prove2me | Definitions.Def_Formalism_PeriodIntegrals_WittUnram
-- name    : Formalism_PeriodIntegrals_WittUnram
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T22:59:09.981319+00:00
-- url     : https://prove2.me/theorems/fe6bb6ea-784a-4ab5-a35d-929e179a6e48
-- title:
--   Witt Unram
-- statement:
--   Definitions and structural lemmas for Witt Unram, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/WittUnram.lean

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
namespace PI
abbrev WF (p f : ℕ) [Fact p.Prime] := WittVector p (GaloisField p f)
def IsWittIdent {p f : ℕ} [Fact p.Prime] {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq] (σ : Qq ≃+* Qq)
    (φ : WF p f ≃+* W) : Prop :=
  ∀ x : WF p f, σ (algebraMap W Qq (φ x)) = algebraMap W Qq (φ (WittVector.frobenius x))
def WittUnram : Prop :=
  ∀ (p f : ℕ) [Fact p.Prime] (W Qq : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
    [Algebra W Qq] (σ : Qq ≃+* Qq),
    IsFractionRing W Qq → Irreducible (p : W) → Nat.card (W ⧸ Ideal.span {(p : W)}) = p ^ f →
    IsAdicComplete (Ideal.span {(p : W)}) W →
    (∀ x : W, ∃ y : W, σ (algebraMap W Qq x) = algebraMap W Qq (x ^ p + (p : W) * y)) →
    ∃ φ : WF p f ≃+* W, IsWittIdent σ φ
end PI


