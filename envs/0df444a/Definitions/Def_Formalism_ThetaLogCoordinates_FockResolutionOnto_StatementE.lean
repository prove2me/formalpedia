-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementE
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:35.349399+00:00
-- url     : https://prove2.me/theorems/ebba3b4f-e0df-438b-9999-d74dfc763716
-- title:
--   Statement E
-- statement:
--   Definitions and structural lemmas for Statement E, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementE.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
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
noncomputable def dpow (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (k : ℕ) :
    MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p] :=
  ((k.factorial : ℚ_[p])⁻¹) • (glAct p LL j 0 c) ^ k
def ModCond (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ)
    (h : MvPolynomial (Fin N × Fin r) ℚ_[p]) : Prop :=
  ∀ l : List (Fin r × ℕ), (∀ ck ∈ l, ck.1 ≠ 0) → ∀ m : Fin N × Fin r →₀ ℕ, ¬ (((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ M) →
    ‖coeff m (((l.map fun ck => dpow p LL j ck.1 ck.2).prod) h)‖ < 1
def LiftModP (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (LL : Letters N) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) : Prop :=
  ∀ h ∈ PolZ p r LL, (∀ k, ModCond p LL (J k) (M k) h) →
    ∃ h' ∈ Y p LL J M, h' ∈ IntPol p (Fin N × Fin r) ∧ ∃ b ∈ IntPol p (Fin N × Fin r), h = h' + (p : ℚ_[p]) • b
def DpowInt : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (j : ℕ) (c : Fin r) (k : ℕ), c ≠ 0 →
    ∀ h ∈ IntPol p (Fin N × Fin r), dpow p LL j c k h ∈ IntPol p (Fin N × Fin r)
def ModOfY : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (LL : Letters N) (j : ℕ) (M : WithTop ℤ),
    ∀ h ∈ YCond p (r := r) LL j M, ModCond p LL j M h
def MulEarlyModP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), j ≤ K →
    ModCond p LL j M (X (Fin.last K, c) * h) → ModCond p LL j M h
def MulLastModP : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (j : ℕ) (M : WithTop ℤ) (c : Fin r)
    (h : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]), K + 1 ≤ j → LL.vec (Fin.last K) = true →
    ModCond p LL j M (X (Fin.last K, c) * h) → ModCond p LL j (M + ((-1 : ℤ) : WithTop ℤ)) h
def DivModPOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r),
    LL.vec (Fin.last K) = true →
    LiftModP p (r := r) (setLast LL (LL.deg (Fin.last K) - 1)) J (shiftLastLetterThresholds K J M 1) → DivModP p LL J M ρ
def GramBoundOfModPLifting : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (∀ o ≤ LLw.deg (Fin.last K), HypP p (setLast LLw o) ρ e1 ∧ HypE p (setLast LLw o) ρ e1) →
    (∀ e, 1 ≤ e → e ≤ LLw.deg (Fin.last K) →
      LiftModP p (r := r) (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e)) →
    (((K + 5) * e1 : ℕ) : ℝ) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
end Formalism.InvariantFactorPaths.L4


