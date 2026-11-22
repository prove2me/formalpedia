-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:38.409467+00:00
-- url     : https://prove2.me/theorems/98cb4fd9-93df-409f-9654-09508d5c7e82
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementB.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM.M MvPolynomial Finset
def FirstCoordinateRaisingCriterion : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ)
    (F : MvPolynomial (Fin N × Fin r) ℚ_[p]),
    F ∈ YCond p LL j M ↔
      ∀ l : List (Fin r), ((l.map fun c => glAct p LL j 0 c).prod) F ∈
        MvPolynomial.restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M}
def MulEarly : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), j ≤ K →
    (X (Fin.last K, c) * h ∈ YCond p LL j M ↔ h ∈ YCond p LL j M)
def MulLast : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), K + 1 ≤ j → LL.vec (Fin.last K) = true →
    (X (Fin.last K, c) * h ∈ YCond p LL j M ↔ h ∈ YCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)))
def FilEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    ∀ f, f ∈ FilE p LLw J M ρ w (Fin.last K, ρ) e ↔
      ∃ h ∈ MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        f = X (Fin.last K, ρ) ^ e * h
def FilBot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.deg (Fin.last K) < e → FilE p LLw J M ρ w (Fin.last K, ρ) e = ⊥
def GrEq : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    ∀ x, x ∈ grLat p LLw J M ρ w (Fin.last K, ρ) e ↔
      ∃ h ∈ MMwZ p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ (shiftWt w ρ e),
        x = X (Fin.last K, ρ) ^ e * initPart (Fin.last K, ρ) 0 h
def GrBot : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e : ℕ),
    LLw.deg (Fin.last K) < e → grLat p LLw J M ρ w (Fin.last K, ρ) e = ⊥
end Formalism.InvariantFactorPaths.L4


