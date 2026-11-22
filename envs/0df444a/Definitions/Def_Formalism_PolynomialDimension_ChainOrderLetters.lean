-- Prove2me | Definitions.Def_Formalism_PolynomialDimension_ChainOrderLetters
-- name    : Formalism_PolynomialDimension_ChainOrderLetters
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-22T21:14:24.708033+00:00
-- url     : https://prove2.me/theorems/2bfc3381-ca18-4c67-b976-b63f9dcbe6db
-- title:
--   Chain Order Letters
-- statement:
--   Definitions and structural lemmas for Chain Order Letters, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PolynomialDimension/ChainOrderLetters.lean

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_PolynomialDimension_DigitSumValuationBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.M MvPolynomial Finset
def degreeAtPosition {N : ℕ} (LL : Letters N) (j : ℕ) : ℕ := if h : j < N then LL.deg ⟨j, h⟩ else 0
def ChainOrderLetters {s : ℕ} (LL : Letters (2 * s + 1)) : Prop := ∀ x, LL.vec x = decide ((x : ℕ) % 2 = 0)
def ConditionShape (s : ℕ) (T : TieData) : Prop := ∀ k, T.J k = 2 * s + 1 ∨ ∃ i, T.J k = T.pos i + 1
def SizeHypothesis {N : ℕ} (LLt : Letters N) (T : TieData) (r : ℕ) (a : ℝ) (Yl : Fin T.t → ℕ) : Prop :=
  (LLt.total : ℝ) ≤ 8 * a + r ∧
  ∀ i, ((degreeAtPosition LLt (T.pos i) + degreeAtPosition LLt (T.pos i + 1) + r + T.z i + 1 : ℕ) : ℝ) ≤ 8 * a + r ∧
    (Yl i : ℝ) ≤ 8 * a + r ∧ ((2 * T.S LLt i + 1 : ℕ) : ℝ) ≤ 8 * a + r
def TheoremMV7 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s r : ℕ) [NeZero r] (LL : Letters (2 * s + 1)) (T : TieData)
    (a E : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → ChainOrderLetters LL → ConditionShape s T →
    1 ≤ a → 1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    SizeHypothesis (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) T r a Yl →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr)
          ⌊(T.t : ℝ) * (E + kapSeg p a r s) + kapSeg p a r s⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, epsSeg (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) (Yl i) (kapSeg p a r s)
          (lgSeg p a r) E *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
def TheoremMV7Of : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (s r : ℕ) [NeZero r] (LL : Letters (2 * s + 1)) (T : TieData)
    (a E : ℝ) (Yl n₀ dd : Fin T.t → ℕ) (ρ : Fin r),
    p ≠ 2 → 2 ≤ r → (ρ : ℕ) = r - 1 → T.Admissible LL → ChainOrderLetters LL → ConditionShape s T →
    1 ≤ a → 1 ≤ E → (∀ i, 1 ≤ Yl i ∧ 0 < dd i ∧ IsCoprime (dd i : ℤ) p) →
    (∀ i, T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i ≤ n₀ i) →
    SizeHypothesis (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) T r a Yl →
    (∀ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
      HypP p (LL.setTies T n) ρ ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ ∧
      HypW p (r := r) (LL.setTies T n) ⌊(r : ℝ) ^ 2 * lgSeg p a r⌋₊ ∧
      ∀ i, GramDeterminantGradedHypothesis p ((LL.setTies T n).takeD (T.pos i + 1)) T.J (T.thrUpTo i) ρ
        (((s : ℝ) + 4) * ((r : ℝ) ^ 2 * lgSeg p a r))) →
    (∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
        (bad p (fun F G => fockN p (LL.setTies T n) (T.phis p (LL.setTies T n) F) G)
          (YZ p (r := r) (LL.setTies T n) T.J T.thr)
          ⌊(T.t : ℝ) * (E + kapSeg p a r s) + kapSeg p a r s⌋ : ℝ)) /
        (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card ≤
      ∑ i, epsSeg (T.S (LL.setTies T (fun i => n₀ i + dd i * (Yl i - 1))) i : ℝ) (Yl i) (kapSeg p a r s)
          (lgSeg p a r) E *
        ((∑ n ∈ Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j)),
            (Module.finrank ℚ_[p]
              (Y p (r := r) (LL.setTies T (Function.update n i (n₀ i + dd i * (Yl i - 1)))) T.J T.thr) : ℝ)) /
          (Fintype.piFinset (fun i => (range (Yl i)).image (fun j => n₀ i + dd i * j))).card)
end Formalism.CountingSumsFrames


