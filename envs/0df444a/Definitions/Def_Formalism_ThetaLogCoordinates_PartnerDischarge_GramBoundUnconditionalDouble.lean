-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_PartnerDischarge_GramBoundUnconditionalDouble
-- name    : Formalism_ThetaLogCoordinates_PartnerDischarge_GramBoundUnconditionalDouble
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T01:38:55.715556+00:00
-- url     : https://prove2.me/theorems/2e982059-5b68-4e31-a44a-04187a71ce14
-- title:
--   Gram Bound Unconditional Double
-- statement:
--   Definitions and structural lemmas for Gram Bound Unconditional Double, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerDischarge/GramBoundUnconditionalDouble.lean

import Definitions.Def_Formalism_ThetaLogCoordinates_PartnerDischarge_StatementPW
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementH
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PairStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds
open Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.PW Formalism.InvariantFactorPaths.L4 MvPolynomial Finset
def KapNum7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r d : ℕ) (a : ℝ), 1 ≤ a → 2 ≤ r → (d : ℝ) ≤ 2 * a →
    (((K + 5) * kapC p r d : ℕ) : ℝ) ≤ ((K + 3) * r ^ 2 : ℝ) * logEightAPlusR p a r
def GramBoundModPAtExponent : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (a κ : ℝ),
    1 ≤ a → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → (LLw.total : ℝ) ≤ 2 * a →
    ((K + 3) * r ^ 2 : ℝ) * logEightAPlusR p a r ≤ κ →
    (∀ e, 1 ≤ e → e ≤ LLw.deg (Fin.last K) →
      LiftModP p (r := r) (setLast LLw (LLw.deg (Fin.last K) - e)) J (shiftLastLetterThresholds K J M e)) →
    GramDeterminantGradedHypothesis p LLw J M ρ κ
def TheoremML7 : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    1 ≤ a → p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, ((LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x : ℝ) ≤ 2 * a) → (∀ i, (T.z i : ℝ) ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * logEightAPlusR p a r ≤ κ →
    2 * a * N + r ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      ∀ i, ∀ e, 1 ≤ e → e ≤ ((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) →
        LiftModP p (r := r)
          (setLast ((LL.setTies T n).takeD (T.pos i + 1))
            (((LL.setTies T n).takeD (T.pos i + 1)).deg (Fin.last (T.pos i)) - e))
          T.J (shiftLastLetterThresholds (T.pos i) T.J (T.thrUpTo i) e)) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * logEightAPlusR p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
def GramBoundUnconditionalDouble : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (a κ : ℝ),
    1 ≤ a → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → (LLw.total : ℝ) ≤ 2 * a →
    2 * (((K + 3) * r ^ 2 : ℝ) * logEightAPlusR p a r) ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def TheoremMFree7 : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    1 ≤ a → p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, ((LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x : ℝ) ≤ 2 * a) → (∀ i, (T.z i : ℝ) ≤ 2 * a) →
    2 * (((N + 2) * r ^ 2 : ℝ) * logEightAPlusR p a r) ≤ κ →
    2 * a * N + r ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * logEightAPlusR p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
def GramBoundUnconditionalReal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (a κ : ℝ),
    1 ≤ a → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → (LLw.total : ℝ) ≤ 2 * a →
    ((K + 3) * r ^ 2 : ℝ) * logEightAPlusR p a r ≤ κ → GramDeterminantGradedHypothesis p LLw J M ρ κ
def LatticeTheoremUnconditional : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (a E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    1 ≤ a → p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, ((LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x : ℝ) ≤ 2 * a) → (∀ i, (T.z i : ℝ) ≤ 2 * a) →
    ((N + 2) * r ^ 2 : ℝ) * logEightAPlusR p a r ≤ κ →
    2 * a * N + r ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * logEightAPlusR p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
def GramBoundAtKappa : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K r : ℕ) [NeZero r] (LLw : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ)
    (M : Fin q → WithTop ℤ) (ρ : Fin r) (s : ℕ) (a : ℝ),
    1 ≤ a → 2 ≤ r → (ρ : ℕ) = r - 1 → LLw.vec (Fin.last K) = true → (LLw.total : ℝ) ≤ 2 * a → K + 2 ≤ 2 * s →
    GramDeterminantGradedHypothesis p LLw J M ρ (3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * logEightAPlusR p a r)
def TheoremMKap7 : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero N] [NeZero r] (LL : Letters N) (T : TieData)
    (s : ℕ) (a E κ : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    1 ≤ a → p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL →
    1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    (∀ x, ((LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))).deg x : ℝ) ≤ 2 * a) → (∀ i, (T.z i : ℝ) ≤ 2 * a) →
    N = 2 * s + 1 → κ = 3 * ((s : ℝ) + 2) * (r : ℝ) ^ 2 * logEightAPlusR p a r →
    2 * a * N + r ≤ (p : ℝ) ^ 2 * (8 * a + r) ^ 2 →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr) ⌊(T.t : ℝ) * (E + C₀ * κ) + C₀ * κ⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, (2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) / Yl i +
          (C₀ * κ + 2 * (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) * logEightAPlusR p a r / Yl i) / E) *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.InvariantFactorPaths.OddLevelGainBounds
namespace Formalism.InvariantFactorPaths.OddLevelGainBounds
open Formalism.GM Formalism.GM.M Formalism.InvariantFactorPaths.KP.LL MvPolynomial Finset
def StepTie7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a : ℝ) (u : ℕ), 1 ≤ a → D.BlockOK → 1 ≤ r →
    (∀ x, (D.LL.deg x : ℝ) ≤ 2 * a) → (∀ i, (D.T.z i : ℝ) ≤ 2 * a) → HypJoin p (r := r) D →
    r * Nat.log p ⌊2 * a⌋₊ + Nat.log p ⌊6 * a + r⌋₊ ≤ u → ∀ k < D.T.t,
      (∀ v ∈ Mid p (r := r) D (k + 1), (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D k) ∧
      (∀ v ∈ Mid p (r := r) D k, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D (k + 1))
def StepPlus7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a : ℝ) (u : ℕ), 1 ≤ a → D.BlockOK → 1 ≤ r →
    (∀ x, (D.LL.deg x : ℝ) ≤ 2 * a) → (D.B : ℝ) ≤ 2 * a → (D.zPlus : ℝ) ≤ 2 * a → HypU p (r := r) D →
    r * Nat.log p ⌊2 * a⌋₊ + Nat.log p ⌊6 * a + r⌋₊ ≤ u →
      (∀ v ∈ Mid p (r := r) D 0, (p : ℚ_[p]) ^ u • v ∈ MidP p (r := r) D) ∧
      (∀ v ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ u • v ∈ Mid p (r := r) D 0)
def LevelLattice7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (D : BlockData N) (a : ℝ), D.BlockOK → 1 ≤ r → 1 ≤ a →
    (∀ x, (D.LL.deg x : ℝ) ≤ 2 * a) → (D.B : ℝ) ≤ 2 * a → (∀ i, (D.T.z i : ℝ) ≤ 2 * a) → (D.zPlus : ℝ) ≤ 2 * a →
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      Formalism.GM.tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y ∈
        Y p (r := r) (D.lettersAt (Function.update j i (j i + 1)) jp) D.T.J D.T.thr) →
    (∀ (j : Fin D.T.t → ℕ) (jp : ℕ) (c : Fin r), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      pderiv (D.uPos, c) y ∈ Y p (r := r) (D.lettersAt j (jp + 1)) D.T.J D.T.thr) →
    Submodule.span ℚ_[p] (D.SSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) =
        Submodule.span ℚ_[p] (D.PSZ p (r := r) : Set (MvPolynomial (BVar N r D.T.t) ℚ_[p])) ∧
      (∀ x ∈ D.SSZ p (r := r),
        ((p : ℚ_[p]) ^ ((D.T.t + 1) * ⌈((r : ℝ) + 1) * logEightAPlusR p a r⌉₊)) • x ∈ D.PSZ p (r := r)) ∧
      (∀ x ∈ D.PSZ p (r := r),
        ((p : ℚ_[p]) ^ ((D.T.t + 1) * ⌈((r : ℝ) + 1) * logEightAPlusR p a r⌉₊)) • x ∈ D.SSZ p (r := r))
end Formalism.InvariantFactorPaths.OddLevelGainBounds


