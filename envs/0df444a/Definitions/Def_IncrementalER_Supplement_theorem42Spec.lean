-- Prove2me | Definitions.Def_IncrementalER_Supplement_theorem42Spec
-- name    : IncrementalER_Supplement_theorem42Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:48:54.557739+00:00
-- url     : https://prove2.me/theorems/0fe57877-4b03-440c-99bd-8db1b09c650a
-- title:
--   Retained terminal-set sequence interface (Theorem 4.2)
-- statement:
--   This definition specifies the complete output of the initialization algorithm of Theorem 4.2: a positive number $s=\widetilde O(k^4)$, one common $k$-hitting set $S_0$, and sets $Q_1,\ldots,Q_s$.
--
--   It requires every containment and factor-two size bound, the pointwise average inequality $s^{-1}\sum_i f_{Q_i}(v)=O(1)$ for every vertex, total charged work, and one simultaneous high-probability event.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 4.2, p.16

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem21Spec

set_option autoImplicit false

namespace IncrementalER.Supplement

/-! Exact-real-RAM output interface for Theorem 4.2 (p.16). -/

/-- The number `s` written by the sequence-construction program (integer cell `-4`). -/
noncomputable def outputSetCount (s : PNormReg.State) : ℕ :=
  (s.integerMemory (-4)).toNat

/-- The initialized program for Theorem 4.2.  Output set `0` is the common hitting set `S₀`;
output sets `1,…,s` are `Q₁,…,Q_s`. -/
noncomputable def sequenceRun (P : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (fuel : ℕ) (omega : ℕ → Bool) :
    PNormReg.State :=
  PNormReg.run P (graphState N es k) omega fuel

/-- Full specification of Theorem 4.2, including the common hitting set, every size bound, the
pointwise average insertion-cost bound, total work and the single high-probability event. -/
def theorem42Spec (P : PNormReg.Program) (C : ℝ) (r p : ℕ) (c : ℝ) : Prop :=
  PNormReg.Admissible P ∧ 0 < C ∧
  ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N →
    ∀ es : List (IncrementalER.Edge n), ValidGraph es →
    QuasiPolyCapacity C r N es → ∀ k : ℝ, 1 < k →
      let work := softPolyBound C r p N es.length k
      let fuel := ⌊work⌋₊
      PNormReg.coinTape {omega |
        let st := sequenceRun P N es k fuel omega
        let s := outputSetCount st
        let S₀ := outputSet st n 0
        ¬ (st.halted = true ∧ (st.work : ℝ) ≤ work ∧ 1 ≤ s ∧
          (s : ℝ) ≤ softBound C r N (k ^ 4) ∧
          IsKHittingSet (edgeCond es) S₀ k C r N ∧
          (S₀.card : ℝ) ≤ softBound C r N (es.length / k) ∧
          (∀ i : Fin s, S₀ ⊆ outputSet st n (i + 1) ∧
            (outputSet st n (i + 1)).card ≤ 2 * S₀.card) ∧
          ∀ v : Fin n,
            (∑ i : Fin s, IncrementalER.insCost (edgeCond es) (outputSet st n (i + 1)) v) / s ≤ C)}
        ≤ ENNReal.ofReal ((N : ℝ) ^ (-c))

end IncrementalER.Supplement


