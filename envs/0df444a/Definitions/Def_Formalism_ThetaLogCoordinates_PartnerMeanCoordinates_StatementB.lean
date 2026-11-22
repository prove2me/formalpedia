-- Prove2me | Definitions.Def_Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_StatementB
-- name    : Formalism_ThetaLogCoordinates_PartnerMeanCoordinates_StatementB
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:16:56.406618+00:00
-- url     : https://prove2.me/theorems/fc647623-10fc-4e88-a9ce-fed5962cc05f
-- title:
--   Statement B
-- statement:
--   Definitions and structural lemmas for Statement B, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/PartnerMeanCoordinates/StatementB.lean

import Definitions.Def_Formalism_PolynomialDimension_ChainOrderLetters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.InvariantFactorPaths.MC
open Formalism.GM Formalism.GM.M Formalism.CountingSumsFrames MvPolynomial Finset
def TheoremMV7Relax : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s r : ℕ) [NeZero r] (LL : Letters (2 * s + 1)) (T : TieData)
    (a E : ℝ) (Yl n₀ dd Sb : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → ChainOrderLetters LL → ConditionShape s T →
    1 ≤ a → 1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ Sb i ∧ Sb i ≤ n₀ i) →
    SizeHypothesis (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) T r a Yl →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr)
          ⌊(T.t : ℝ) * (E + kapSeg p a r s) + kapSeg p a r s⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, epsSeg (Sb i : ℝ) (Yl i) (kapSeg p a r s) (lgSeg p a r) E *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
def LatticeTheoremExplicitEpsilon : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s r : ℕ) [NeZero r] (LL : Letters (2 * s + 1)) (T : TieData)
    (a Yr : ℝ) (Yl n₀ dd Sb : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → ChainOrderLetters LL → ConditionShape s T →
    1 ≤ a → 1 ≤ Yr → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ Sb i ∧ Sb i ≤ n₀ i) →
    SizeHypothesis (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) T r a Yl →
    (∀ i, epsSeg (Sb i : ℝ) (Yl i) (kapSeg p a r s) (lgSeg p a r) (Yr * kapSeg p a r s) ≤ 28 / Yr) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr)
          ⌊firstDepth T.t Yr (kapSeg p a r s)⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      28 / Yr * ∑ i,
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.InvariantFactorPaths.MC


