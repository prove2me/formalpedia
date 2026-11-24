-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
-- name    : Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T23:19:12.307307+00:00
-- url     : https://prove2.me/theorems/2409c18f-cd86-4ba7-8d76-8b53801fe531
-- title:
--   Statement H
-- statement:
--   Definitions and structural lemmas for Statement H, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/StatementH.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.PW MvPolynomial Finset
def TrivProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) (LL : Letters N) (j : ℕ) (T : Set (Fin r → ℤ))
    (P : MvPolynomial (Fin N × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin N × Fin r) ℚ_[p]),
    j ≤ 1 → 1 ≤ r → IsTypeProj p LL j univ T P → (∀ F ∈ Pol p r LL, P F = F) ∨ (∀ F ∈ Pol p r LL, P F = 0)
def HighestVectorProjectionPos : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (w : Fin r → ℤ) (e1 : ℕ),
    1 ≤ K → 2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last K) = true → HypP p LL ρ e1 → HypE p LL ρ e1 →
    ∃ Pr : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p],
      ∀ m : Fin (K + 1) × Fin r →₀ ℕ, MultiDeg LL m → m (Fin.last K, ρ) = 0 →
        Pr (monomial m 1) ∈ XH p LL J M ρ w ∧
        ((p : ℚ_[p]) ^ ((K + 1) * e1)) • Pr (monomial m 1) ∈ IntPol p (Fin (K + 1) × Fin r) ∧
        ∀ g ∈ XH p LL J M ρ w, fock p g (Pr (monomial m 1)) = fock p g (monomial m 1)
def GradedBoundOfSaturationPos : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (e1 c0 : ℕ) (κ : ℝ),
    1 ≤ K → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true →
    (∀ o ≤ LLw.deg (Fin.last K), HypP p (setLast LLw o) ρ e1 ∧ HypE p (setLast LLw o) ρ e1) →
    (∀ e ≤ LLw.deg (Fin.last K), ResSatL p (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e) ρ c0) →
    (((K + 3) * e1 + 2 * c0 : ℕ) : ℝ) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def ResSatLZero : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (r : ℕ) [NeZero r] (LL : Letters (0 + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r),
    2 ≤ r → (ρ : ℕ) = r - 1 → LL.vec (Fin.last 0) = true → ResSatL p LL J M ρ 0
def GramBoundUnconditionalPos : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (a : ℕ) (κ : ℝ),
    2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → LLw.total ≤ 2 * a →
    ((K + 3) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def TheoremMFree0 : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a : ℕ) (E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x ≤ 2 * a) → (∀ i, T.z i ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * lgV2 p a r ≤ κ →
    2 * a * N + r ≤ p ^ 2 * (8 * a + r) ^ 2 →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * lgV2 p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.InvariantFactorPaths.L4


