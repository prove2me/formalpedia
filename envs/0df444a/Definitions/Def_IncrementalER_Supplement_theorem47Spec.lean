-- Prove2me | Definitions.Def_IncrementalER_Supplement_theorem47Spec
-- name    : IncrementalER_Supplement_theorem47Spec
-- status  : Definition
-- author  : @iris
-- created : 2026-11-17T04:50:06.892191+00:00
-- url     : https://prove2.me/theorems/d417557e-0dcf-41fb-8ab9-740d789f3651
-- title:
--   Charged leverage-oracle batch augmentation interface (Theorem 4.7)
-- statement:
--   This definition specifies the single-batch randomized augmentation algorithm of Theorem 4.7. Its inputs are a common $k$-hitting set, the retained sets $Q_i$, a batch $B$, and an initialized one-sided leverage-degree estimator. Oracle calls are explicit interactions and their full query cost is added to the program's work.
--
--   The returned $D$ contains $B$, has $|D|\le2|B|$, and for every fixed vertex the expected average insertion cost is at most the original average plus an absolute constant. The integral ranges only over the fresh batch-algorithm tape.
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Theorem 4.7, p.19

import Mathlib
import Definitions.Def_IncrementalER_Supplement_theorem51Spec

set_option autoImplicit false

open MeasureTheory

namespace IncrementalER.Supplement

/-! Charged leverage-oracle interface for Theorem 4.7 (p.19). -/

/-- A one-sided leverage-degree query interface initialized with respect to `S₀`. -/
def ValidLeverageEstimator {n : ℕ} (c : Fin n → Fin n → ℝ) (S₀ : Finset (Fin n))
    (epsilon : ℝ) (hat : Fin n → Finset (Fin n) → ℝ) : Prop :=
  ∀ U v, S₀ ⊆ U → v ∈ U \ S₀ →
    IncrementalER.levDegT c U v ≤ hat v U ∧
      hat v U ≤ (1 + epsilon) * IncrementalER.levDegT c U v

/-- Input for one batch: `S₀`, all retained sets `Q_i`, and `B`, as characteristic vectors.
The program can request a leverage estimate by halting with flag `-5 = 1`, a vertex in `-6`, and
the requested set as output set `0`; the driver writes the charged answer in real cell `-101`. -/
noncomputable def batch47Input {n : ℕ} (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ)
    (S₀ B : Finset (Fin n)) (Q : List (Finset (Fin n))) : PNormReg.State :=
  let header : List ℤ := [6, (n : ℤ), (S₀.card : ℤ), (Q.length : ℤ), (B.card : ℤ)]
  let bits : List ℤ :=
    (List.ofFn fun v : Fin n => if v ∈ S₀ then (1 : ℤ) else 0) ++
    (Q.flatMap fun U => List.ofFn fun v : Fin n => if v ∈ U then (1 : ℤ) else 0) ++
    (List.ofFn fun v : Fin n => if v ∈ B then (1 : ℤ) else 0)
  loadWords (graphState N es k) (header ++ bits) [k]

/-- One charged call to the already initialized leverage oracle. -/
noncomputable def answerLeverageRequest {n : ℕ} (hn : 0 < n)
    (hat : Fin n → Finset (Fin n) → ℝ) (charge : ℕ) (s : PNormReg.State) :
    PNormReg.State :=
  let v : Fin n := ⟨(s.integerMemory (-6)).toNat % n, Nat.mod_lt _ hn⟩
  let U := outputSet s n 0
  { s with
    core := { s.core with
      pc := 0
      regs := (fun _ => 0)
      ptrs := (fun _ => 0)
      mem := Function.update s.core.mem (-101) (hat v U) }
    halted := false
    work := s.work + charge }

/-- Run at most `rounds` oracle-interaction rounds.  Every ordinary instruction and every complete
leverage-oracle call is included in `work`. -/
noncomputable def batch47Run (P : PNormReg.Program) {n : ℕ} (hn : 0 < n)
    (N : ℕ) (es : List (IncrementalER.Edge n)) (k : ℝ) (S₀ B : Finset (Fin n))
    (Q : List (Finset (Fin n))) (hat : Fin n → Finset (Fin n) → ℝ)
    (segmentFuel charge : ℕ) (omega : ℕ → Bool) : ℕ → PNormReg.State
  | 0 => PNormReg.run P (batch47Input N es k S₀ B Q) omega segmentFuel
  | rounds + 1 =>
      let prev := batch47Run P hn N es k S₀ B Q hat segmentFuel charge omega rounds
      if prev.integerMemory (-5) = 1 then
        PNormReg.run P (answerLeverageRequest hn hat charge prev) omega segmentFuel
      else prev

/-- Full single-batch theorem.  The estimator is an explicit assumption, its calls are charged,
and the only integration is over the batch algorithm's fresh random tape. -/
def theorem47Spec (P : PNormReg.Program) (C : ℝ) (r p : ℕ) : Prop :=
  PNormReg.Admissible P ∧ 0 < C ∧
  ∀ N : ℕ, 1 ≤ N → ∀ n : ℕ, ∀ hn : 0 < n, n ≤ N →
    ∀ es : List (IncrementalER.Edge n), ValidGraph es →
    QuasiPolyCapacity C r N es → ∀ k : ℝ, 1 < k →
    ∀ S₀ : Finset (Fin n), IsKHittingSet (edgeCond es) S₀ k C r N →
    ∀ Q : List (Finset (Fin n)), 1 ≤ Q.length →
      (Q.length : ℝ) ≤ softBound C r N ((1 + k) ^ p) →
      (∀ U ∈ Q, S₀ ⊆ U) → ∀ B : Finset (Fin n),
      ∀ hat : Fin n → Finset (Fin n) → ℝ,
        ValidLeverageEstimator (edgeCond es) S₀ (1 / 2) hat →
        let oracleCharge := ⌊softBound C r N ((1 + k) ^ p)⌋₊
        let work := softPolyBound C r p N B.card k
        let fuel := ⌊work⌋₊
        let final := fun omega => batch47Run P hn N es k S₀ B Q hat fuel oracleCharge omega fuel
        (∀ omega, (final omega).halted = true ∧ ((final omega).work : ℝ) ≤ work ∧
          B ⊆ outputSet (final omega) n 1 ∧
          (outputSet (final omega) n 1).card ≤ 2 * B.card) ∧
        ∀ v : Fin n,
          (∫⁻ omega, ENNReal.ofReal
              ((Q.map fun U => IncrementalER.insCost (edgeCond es)
                (U ∪ outputSet (final omega) n 1) v).sum / Q.length)
            ∂PNormReg.coinTape) ≤
          ENNReal.ofReal
            ((Q.map fun U => IncrementalER.insCost (edgeCond es) U v).sum / Q.length + C)

end IncrementalER.Supplement


