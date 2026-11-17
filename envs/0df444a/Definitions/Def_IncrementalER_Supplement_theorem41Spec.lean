-- Prove2me | Definitions.Def_IncrementalER_Supplement_theorem41Spec
-- name    : IncrementalER_Supplement_theorem41Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:48:12.352548+00:00
-- url     : https://prove2.me/theorems/55be84fc-4270-4b15-b354-75e69924a118
-- title:
--   Initialization and decoupled batch-insertion interface (Theorem 4.1)
-- statement:
--   This definition specifies the two-program data structure of Theorem 4.1. The initialization program outputs a random $k$-hitting set $T$ with bounded expected insertion cost. Each `InsertVertices(B)` invocation starts from the same initialized memory, returns a set $D$ containing $B$ with $|D|\le2|B|$, and is not composed with the output of any earlier call.
--
--   Initialization work, per-call work, the two expectation guarantees, set sizes, and high-probability correctness are stated explicitly on the randomized exact-real RAM.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 4.1, p.15

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem21Spec

set_option autoImplicit false

open MeasureTheory

namespace IncrementalER.Supplement

/-!
# Exact-real-RAM interface for Theorem 4.1

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, STOC 2027 submission
(manuscript sha256 a0415fd5…), Theorem 4.1, p.15.
-/

/-- Initialization of the terminal-robust-set data structure. -/
noncomputable def robustInitRun (Pre : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (fuel : ℕ) (omega : ℕ → Bool) :
    PNormReg.State :=
  PNormReg.run Pre (graphState N es k) omega fuel

/-- A decoupled `InsertVertices(B)` call.  Every call starts from the same initialized memory;
the output of an earlier call is not fed to a later one. -/
noncomputable def insertVerticesRun (Pre Batch : PNormReg.Program) {n : ℕ}
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (B : Finset (Fin n))
    (preFuel batchFuel : ℕ) (omega : ℕ → Bool) : PNormReg.State :=
  let pre := robustInitRun Pre N es k preFuel omega
  let words : List ℤ := [2, (n : ℤ), (B.card : ℤ)] ++
    B.toList.map fun v => ((v : ℕ) : ℤ)
  PNormReg.run Batch (loadWords { pre with work := 0 } words [k]) omega batchFuel

/-- Full specification of Theorem 4.1.  Expectations include the initialization randomness and,
for `InsertVertices`, the randomness of that one decoupled call. -/
def theorem41Spec (Pre Batch : PNormReg.Program) (C : ℝ) (r p : ℕ) (c : ℝ) : Prop :=
  PNormReg.Admissible Pre ∧ PNormReg.Admissible Batch ∧ 0 < C ∧
  ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, 1 ≤ n → n ≤ N →
    ∀ es : List (IncrementalER.Edge n), ValidGraph es →
    QuasiPolyCapacity C r N es → ∀ k : ℝ, 1 < k →
      let preWork := softPolyBound C r p N es.length k
      let preFuel := ⌊preWork⌋₊
      (∀ v : Fin n,
        (∫⁻ omega, ENNReal.ofReal
            (IncrementalER.insCost (edgeCond es)
              (outputSet (robustInitRun Pre N es k preFuel omega) n 0) v)
          ∂PNormReg.coinTape) ≤ ENNReal.ofReal C) ∧
      PNormReg.coinTape {omega |
        ¬ ((robustInitRun Pre N es k preFuel omega).halted = true ∧
          ((robustInitRun Pre N es k preFuel omega).work : ℝ) ≤ preWork ∧
          IsKHittingSet (edgeCond es)
            (outputSet (robustInitRun Pre N es k preFuel omega) n 0) k C r N ∧
          ((outputSet (robustInitRun Pre N es k preFuel omega) n 0).card : ℝ) ≤
            softBound C r N (es.length / k))} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c)) ∧
      ∀ B : Finset (Fin n),
        let batchWork := softPolyBound C r p N B.card k
        let batchFuel := ⌊batchWork⌋₊
        (∀ v : Fin n,
          (∫⁻ omega, ENNReal.ofReal
              (IncrementalER.insCost (edgeCond es)
                (outputSet (robustInitRun Pre N es k preFuel omega) n 0 ∪
                  outputSet (insertVerticesRun Pre Batch N es k B preFuel batchFuel omega) n 0) v)
            ∂PNormReg.coinTape) ≤ ENNReal.ofReal C) ∧
        PNormReg.coinTape {omega |
          let pre := robustInitRun Pre N es k preFuel omega
          let D := outputSet (insertVerticesRun Pre Batch N es k B preFuel batchFuel omega) n 0
          ¬ (pre.halted = true ∧ (pre.work : ℝ) ≤ preWork ∧
            IsKHittingSet (edgeCond es) (outputSet pre n 0) k C r N ∧
            ((outputSet pre n 0).card : ℝ) ≤ softBound C r N (es.length / k) ∧
            (insertVerticesRun Pre Batch N es k B preFuel batchFuel omega).halted = true ∧
            ((insertVerticesRun Pre Batch N es k B preFuel batchFuel omega).work : ℝ) ≤ batchWork ∧
            B ⊆ D ∧ D.card ≤ 2 * B.card)} ≤ ENNReal.ofReal ((N : ℝ) ^ (-c))

end IncrementalER.Supplement


