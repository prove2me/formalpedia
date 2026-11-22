-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:41.053748+00:00
-- url     : https://prove2.me/theorems/984d3340-c4f4-4776-8736-fc58e0883202
-- title:
--   Statement C
-- statement:
--   Definitions and structural lemmas for Statement C, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementC.lean

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
def YCondDrop : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) (M : WithTop ℤ),
    LL.vec (Fin.last K) = true →
    ∀ F ∈ Pol p r LL, F ∈ YCond p LL (K + 1) M → F ∈ YCond p LL K M
def ResInto : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 →
    ∀ h ∈ Y p LL J M, initPart (Fin.last K, ρ) 0 h ∈ XSp p LL J M ρ
def ResMM : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ResOntoK p LL J M ρ →
    ∀ x, x ∈ XH p LL J M ρ w ↔ ∃ h ∈ MMw p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = x
def ResMMZ : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ResSat p LL J M ρ →
    ∀ x ∈ XH p LL J M ρ w, x ∈ IntPol p (Fin (K + 1) × Fin r) →
      ∃ h ∈ MMwZ p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ e1) • x
def ProjX : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LL m → m (Fin.last K, ρ) = 0 →
        Pr (monomial m 1) ∈ XH p LL J M ρ w ∧
        ((p : ℚ_[p]) ^ ((K + 3) * e1)) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        ∀ g ∈ XH p LL J M ρ w, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)
def ProjAtOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 → HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 →
    ResOntoK p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ →
    ProjAt p LLw J M ρ w e ((K + 3) * e1)
def SatAtOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e e1 : ℕ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → e ≤ LLw.deg (Fin.last K) →
    HypP p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 → HypE p (setLast LLw (LLw.deg (Fin.last K) - e)) ρ e1 →
    ResSat p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ →
    SatAt p LLw J M ρ w e e1
def GramBoundOfRestriction : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 : ℕ) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (∀ o ≤ LLw.deg (Fin.last K), HypP p (setLast LLw o) ρ e1 ∧ HypE p (setLast LLw o) ρ e1) →
    (∀ e ≤ LLw.deg (Fin.last K), ResSat p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ) →
    (((K + 5) * e1 : ℕ) : ℝ) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def ResSatOf : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r),
    ResOntoK p LL J M ρ → DivModP p LL J M ρ → ResSat p LL J M ρ
end Formalism.InvariantFactorPaths.L4


