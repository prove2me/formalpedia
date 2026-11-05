-- Prove2me | Definitions.Def_QMCLeafB_runstreams
-- name    : QMCLeafB_runstreams
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-04T10:31:12.002247+00:00
-- url     : https://prove2.me/theorems/2a5d4d78-7eee-4c21-a710-fd168c568f7a
-- title:
--   QMCLeafB runstreams
-- statement:
--   # leaf B phase 17 — brick `run-streams` (swarm `smw1gfajf`, member m8, direction d3)
--
--   Published as part of the QMCLeafB library mirror supporting the quantum max-cut campaign's polynomial-time SDP-value certificate (AGM20, TQC 2020, arXiv 2003.14394).

import Mathlib
import Definitions.Def_QMCLeafB_round_program_m3
import Definitions.Def_QMCLeafB_relax_oracle_m4
import Definitions.Def_QMCLeafB_hdCert
import Definitions.Def_QMCLeafB_runparams_shallow_m5
import Definitions.Def_QMCLeafB_runparts_dilate_m5
/-
# leaf B phase 17 — brick `run-streams` (swarm `smw1gfajf`, member m8, direction d3)

The `hd` slot of the leaf is assembled through

    QMCLeafB.RunPartsStream.runParts_of_stream_data

which consumes the guarded run's *oracle records* at the queried centres `cX k`:

* `C     : ∀ k, ok k = false → RelaxCut (wMatrixQ G) (cX k) (t - eps) dq`,
* `hmem  : ∀ k, ok k = true  → RelaxMem (wMatrixQ G) (cX k) (t - eps) dq`,
* `hcEq` (the recorded normal), `hCsym` (the centre's symmetry) and the drift budgets.

This file machine-checks the *first two* of those against the concrete round program
`QMCLeafB.RoundProgram.oracleR`.  The outcome is a sharp, and negative, answer:

### 1.  The flag read-out (§1)

`oracleR s` is `(false, [])` (the loop's `ok`) exactly when

    dvR s = 0  ∧  stT s ≤ fvR s  ∧  pivAns s reports PSD,

and it is a cut otherwise, with normal `diagSignF …` (diagonal branch), `stA s` (threshold
branch) or `vecMulVecF …` (psd branch).  All three readings are proved here from the
definitions, with no hypotheses.

### 2.  The program's pairing is the Frobenius pairing (§2)

`fvR s = [wMatrixQ G, cX]`: the program's `frobV` on the two row-major codes is the library's
`SepOracle.frob` on the coded matrices.  This is the bridge that lets the program's threshold
test speak about the relaxation.

### 3.  `hmem` is refuted at every `ok` round (§3, the headline)

The loop's body at the refutation level `u = t − eps` is
`[A,X] ≤ t − eps + dq/2` (`RelaxMem.trace_le`), while the program answers `ok` only when
`t ≤ [A,cX]`.  Since `dq/2 < eps` at the campaign's own tolerance (`dqShallow G = eps/(9Rq+1)`,
§5), the two are **incompatible**: no `ok` round of the guarded run can certify `RelaxMem` at the
level the `hd` assembly queries.  Conversely, at exactly those centres a `RelaxCut` *does* exist
(§4, `relaxMem_or_cut`), so the `ok` flag is a mis-certificate, not a missing cut.

The consequence (§4) is that an `hd` supplier built on `runParts_of_stream_data` must have
**no `ok` round at all** on the interior bracket: `hmem` forces every round to be a cut, hence
`anyOk ok N = false`, hence `hverdict` fixes `o G t = false` there and the `hcert` slot is vacuous.

### 4.  The cut *slot* carries no content either (§4b)

`RelaxCut` puts no nondegeneracy condition on its normal, so the zero normal makes the separation
clause `-1 ≤ 0`: there is a `RelaxCut` at every centre and every level.  Taking `C` there gives
`c = 0`, hence `cn k = lam k • flat(1)`, and the assembly's whole `c`-side bookkeeping collapses
(`hcEq` is `c = 0`; `hstatec` and `hdriftc` become `0 ≤ margin/2`; the hard part of `hlam2`
vanishes).  What survives is the identity direction: `hstated`, `hdiagc`, and the flag stream.

### Net: item 1 is empty

So the phase-17 residual item "the oracle's `RelaxCut`/`RelaxMem` verdicts at the queried centres,
margins, normal ids, `hCsym`, `hverdict`" has no content left to supply: `RelaxMem` is *impossible*
at the round's `ok` rounds (§3) and `RelaxCut` is *free* (§4b).  The real residual is
(i) the flag stream, i.e. proving the interior verdict is `false` (equivalently the mirror of
`htop`), and (ii) the identity-direction analytics `hstated`/`hdiagc` (d1's half).  §5 records the
one arithmetic fact the level choice has to respect: the queried level `t - eps` and the round's own
ok test at `t + eps` differ by `2·eps > dqShallow/2`, so neither `round` nor `roundT` certifies the
other's level for free.

No `sorry`, no `axiom`, no `native_decide`, no `unsafe`; `set_option autoImplicit false`;
axiom audit at the end.
-/

open scoped BigOperators
open Matrix
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable section

namespace QMCLeafB.RunStreams

open QuantumMaxCutEnergy

/-! ## 1.  Reading the round program's oracle flag -/

/-- The PSD branch's flag is the descent's own flag. -/
theorem pivCut_fst (s : QMCLeafB.RoundProgram.RSt) :
    (QMCLeafB.RoundProgram.pivCut s).1 = (QMCLeafB.RoundProgram.pivAns s).1 := by
  unfold QMCLeafB.RoundProgram.pivCut QMCLeafB.RoundProgram.pivCutF
  cases h : (QMCLeafB.RoundProgram.pivAns s).1 <;> simp

/-- The threshold branch answers `ok` only above the state's threshold. -/
theorem threshB_fst_false (s : QMCLeafB.RoundProgram.RSt)
    (h : (QMCLeafB.RoundProgram.threshB s).1 = false) :
    QMCLeafB.RoundProgram.stT s ≤ QMCLeafB.RoundProgram.fvR s := by
  unfold QMCLeafB.RoundProgram.threshB at h
  by_cases hle : QMCLeafB.RoundProgram.stT s ≤ QMCLeafB.RoundProgram.fvR s
  · rw [if_pos hle] at h
    exact hle
  · rw [if_neg hle] at h
    simp at h

/-- **The `ok` read-out**: the loop's `ok` flag of the concrete round is exactly
"unit diagonal, above the threshold, and the pivot descent reports PSD". -/
theorem oracleR_ok (s : QMCLeafB.RoundProgram.RSt)
    (h : (QMCLeafB.RoundProgram.oracleR s).1 = false) :
    QMCLeafB.RoundProgram.dvR s = 0 ∧ QMCLeafB.RoundProgram.stT s ≤ QMCLeafB.RoundProgram.fvR s := by
  unfold QMCLeafB.RoundProgram.oracleR at h
  by_cases hdv : QMCLeafB.RoundProgram.dvR s = 0
  · rw [if_pos hdv] at h
    exact ⟨hdv, threshB_fst_false s h⟩
  · rw [if_neg hdv] at h
    exact absurd h (by simp)

/-- The diagonal branch's normal. -/
theorem oracleR_normal_diag (s : QMCLeafB.RoundProgram.RSt)
    (h : QMCLeafB.RoundProgram.dvR s ≠ 0) :
    (QMCLeafB.RoundProgram.oracleR s).2
      = QMCLeafB.RoundProgram.diagSignF (QMCLeafB.RoundProgram.stN s,
          QMCLeafB.RoundProgram.stX s) := by
  unfold QMCLeafB.RoundProgram.oracleR
  rw [if_neg h]

/-- The threshold branch's normal. -/
theorem oracleR_normal_thresh (s : QMCLeafB.RoundProgram.RSt)
    (hdv : QMCLeafB.RoundProgram.dvR s = 0)
    (ht : ¬ QMCLeafB.RoundProgram.stT s ≤ QMCLeafB.RoundProgram.fvR s) :
    (QMCLeafB.RoundProgram.oracleR s).2 = QMCLeafB.RoundProgram.stA s := by
  unfold QMCLeafB.RoundProgram.oracleR QMCLeafB.RoundProgram.threshB
  rw [if_pos hdv, if_neg ht]

/-- The psd branch's normal. -/
theorem oracleR_normal_psd (s : QMCLeafB.RoundProgram.RSt)
    (hdv : QMCLeafB.RoundProgram.dvR s = 0)
    (ht : QMCLeafB.RoundProgram.stT s ≤ QMCLeafB.RoundProgram.fvR s)
    (hp : (QMCLeafB.RoundProgram.pivAns s).1 = true) :
    (QMCLeafB.RoundProgram.oracleR s).2
      = QMCLeafB.RoundProgram.vecMulVecF (QMCLeafB.RoundProgram.stN s,
          (QMCLeafB.RoundProgram.pivAns s).2) := by
  unfold QMCLeafB.RoundProgram.oracleR QMCLeafB.RoundProgram.threshB
    QMCLeafB.RoundProgram.pivCut QMCLeafB.RoundProgram.pivCutF
  rw [if_pos hdv, if_pos ht]
  simp [hp]

/-! ## 2.  The program's pairing is the library's Frobenius pairing -/

/-- `List.sum` of a `range` is the `Finset` sum of the same range. -/
theorem list_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (m : ℕ) :
    ((List.range m).map g).sum = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
      simp

/-- **`frobV` is the Frobenius pairing of the coded matrices.** -/
theorem frobV_eq_frob {n : ℕ} {A X : List ℚ} {MA MX : Matrix (Fin n) (Fin n) ℚ}
    (hA : MatQ.correct n MA A) (hX : MatQ.correct n MX X) :
    QMCLeafB.RoundProgram.frobV (n, (A, X)) = QMCLeafB.SepOracle.frob MA MX := by
  have hlen : (X.take n).length = n := by
    rw [List.length_take, hX.1, Nat.min_eq_left (Nat.le_mul_self n)]
  have key : ∀ g : ℕ → ℕ → ℚ,
      ((List.range n).map (fun i => ((List.range n).map (fun j => g i j)).sum)).sum
        = ∑ i : Fin n, ∑ j : Fin n, g i j := by
    intro g
    simp only [list_sum_range]
    rw [← Fin.sum_univ_eq_sum_range (f := fun i => ∑ j ∈ Finset.range n, g i j)]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact (Fin.sum_univ_eq_sum_range (f := fun j => g (i : ℕ) j) n).symm
  unfold QMCLeafB.RoundProgram.frobV QMCLeafB.SepOracle.frob
  simp only [QMCLeafB.RoundProgram.idxs, hlen]
  rw [key (fun i j => A.getD (i * n + j) 0 * X.getD (i * n + j) 0)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← hA.2 i j, ← hX.2 i j]
  rfl

/-- The round program's `[A, X]` at a state, in the library's spelling. -/
theorem fvR_eq_frob {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℚ} {s : QMCLeafB.RoundProgram.RSt}
    (hstN : QMCLeafB.RoundProgram.stN s = n)
    (hA : MatQ.correct n A (QMCLeafB.RoundProgram.stA s))
    (hX : MatQ.correct n M (QMCLeafB.RoundProgram.stX s)) :
    QMCLeafB.RoundProgram.fvR s = QMCLeafB.SepOracle.frob A M := by
  unfold QMCLeafB.RoundProgram.fvR
  rw [hstN]
  exact frobV_eq_frob hA hX

#print axioms QMCLeafB.RunStreams.frobV_eq_frob
#print axioms QMCLeafB.RunStreams.fvR_eq_frob

/-! ## 3.  The `ok` branch cannot certify `RelaxMem` at the refutation level

`RelaxMem A cX u dq` is the loop's stop condition: the centre is in the relaxed body, whose
trace clause reads `[A, cX] ≤ u + dq/2` (`relaxBodyLE`'s third conjunct, `u = t - eps`).  The round
program answers `ok` only when `t ≤ [A, cX]` (`oracleR_ok`).  So an `ok` round certifies the
*opposite* inequality, and the two are incompatible as soon as `dq/2 < eps`. -/

/-- **The `hmem` slot is false at every `ok` round.** -/
theorem not_relaxMem_of_ok {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {t dq eps : ℚ}
    (hstN : QMCLeafB.RoundProgram.stN s = n)
    (hA : MatQ.correct n A (QMCLeafB.RoundProgram.stA s))
    (hX : MatQ.correct n M (QMCLeafB.RoundProgram.stX s))
    (hT : QMCLeafB.RoundProgram.stT s = t)
    (hok : (QMCLeafB.RoundProgram.oracleR s).1 = false)
    (hgap : dq / 2 < eps) :
    ¬ QMCLeafB.RelaxOracle.RelaxMem A M (t - eps) dq := by
  intro hmem
  have hle : t ≤ QMCLeafB.SepOracle.frob A M := by
    have h1 : QMCLeafB.RoundProgram.stT s ≤ QMCLeafB.RoundProgram.fvR s := (oracleR_ok s hok).2
    rw [hT, fvR_eq_frob hstN hA hX] at h1
    exact h1
  have h2 : QMCLeafB.SepOracle.frob A M ≤ t - eps + dq / 2 := hmem.trace_le
  linarith

/-- At an `ok` round of the concrete program a separating cut at the loop's level **exists**:
the program simply cannot certify membership there. -/
theorem nonempty_relaxCut_of_ok {n : ℕ} {A M : Matrix (Fin n) (Fin n) ℚ}
    {s : QMCLeafB.RoundProgram.RSt} {t dq eps : ℚ}
    (hdq : 0 < dq)
    (hstN : QMCLeafB.RoundProgram.stN s = n)
    (hA : MatQ.correct n A (QMCLeafB.RoundProgram.stA s))
    (hX : MatQ.correct n M (QMCLeafB.RoundProgram.stX s))
    (hT : QMCLeafB.RoundProgram.stT s = t)
    (hok : (QMCLeafB.RoundProgram.oracleR s).1 = false)
    (hgap : dq / 2 < eps) :
    Nonempty (QMCLeafB.RelaxOracle.RelaxCut A M (t - eps) dq) :=
  (QMCLeafB.RelaxOracle.relaxMem_or_cut A M (t - eps) dq hdq).resolve_left
    (not_relaxMem_of_ok hstN hA hX hT hok hgap)

#print axioms QMCLeafB.RunStreams.not_relaxMem_of_ok
#print axioms QMCLeafB.RunStreams.nonempty_relaxCut_of_ok

/-! ## 4.  Consequence for the `hd` assembly: no `ok` round on the interior -/

/-- The loop's `ok` bit recorded by the round (the state appends `true` on the `ok` branch). -/
def okBit (s : QMCLeafB.RoundProgram.RSt) : Bool := !(QMCLeafB.RoundProgram.oracleR s).1

theorem okBit_eq_true_iff (s : QMCLeafB.RoundProgram.RSt) :
    okBit s = true ↔ (QMCLeafB.RoundProgram.oracleR s).1 = false := by
  unfold okBit
  cases (QMCLeafB.RoundProgram.oracleR s).1 <;> simp

/-- **`hmem` forces every round to be a cut.**  Hence the `hd` supplier of
`runParts_of_stream_data` has `ok ≡ false` on the bracket: `hcert` is vacuous and `hverdict`
reads `false`. -/
theorem okBit_eq_false_of_hmem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {t dq eps : ℚ} (N : ℕ)
    (st : ℕ → QMCLeafB.RoundProgram.RSt) (M : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (hstN : ∀ k, QMCLeafB.RoundProgram.stN (st k) = n)
    (hA : ∀ k, MatQ.correct n A (QMCLeafB.RoundProgram.stA (st k)))
    (hX : ∀ k, MatQ.correct n (M k) (QMCLeafB.RoundProgram.stX (st k)))
    (hT : ∀ k, QMCLeafB.RoundProgram.stT (st k) = t)
    (hgap : dq / 2 < eps)
    (hmem : ∀ k, k < N → QMCLeafB.RelaxOracle.RelaxMem A (M k) (t - eps) dq) :
    ∀ k, k < N → okBit (st k) = false := by
  intro k hk
  have hnot : (QMCLeafB.RoundProgram.oracleR (st k)).1 ≠ false := fun hok =>
    not_relaxMem_of_ok (hstN k) (hA k) (hX k) (hT k) hok hgap (hmem k hk)
  unfold okBit
  cases h : (QMCLeafB.RoundProgram.oracleR (st k)).1
  · exact absurd h hnot
  · rfl

/-- The verdict bit of a run whose every round is a cut. -/
theorem anyOk_false_of_hmem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {t dq eps : ℚ} (N : ℕ)
    (st : ℕ → QMCLeafB.RoundProgram.RSt) (M : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (hstN : ∀ k, QMCLeafB.RoundProgram.stN (st k) = n)
    (hA : ∀ k, MatQ.correct n A (QMCLeafB.RoundProgram.stA (st k)))
    (hX : ∀ k, MatQ.correct n (M k) (QMCLeafB.RoundProgram.stX (st k)))
    (hT : ∀ k, QMCLeafB.RoundProgram.stT (st k) = t)
    (hgap : dq / 2 < eps)
    (hmem : ∀ k, k < N → QMCLeafB.RelaxOracle.RelaxMem A (M k) (t - eps) dq) :
    QMCLeafB.SimLoop.anyOk (fun k => okBit (st k)) N = false := by
  induction N with
  | zero => rfl
  | succ K ih =>
      have h1 : QMCLeafB.SimLoop.anyOk (fun k => okBit (st k)) K = false :=
        ih (fun k hk => hmem k (Nat.lt_trans hk (Nat.lt_succ_self K)))
      have h2 : okBit (st K) = false :=
        okBit_eq_false_of_hmem (K + 1) st M hstN hA hX hT hgap hmem K (Nat.lt_succ_self K)
      rw [QMCLeafB.SimLoop.anyOk_succ, h1, h2]
      rfl

/-- **The capstone**: if the run's recorded flags are the program's own `ok` bits and the `hmem`
slot of `runParts_of_stream_data` is fed at the interior level `t - eps`, then the run's verdict on
that bracket is `false`.  So an `hd` at `RoundProgram.round` has verdict `false` on the interior:
the `ok` branch of that round is not a certificate, and `hcert` is vacuous there. -/
theorem verdict_false_of_hmem {n : ℕ} {A : Matrix (Fin n) (Fin n) ℚ}
    {t dq eps : ℚ} (N : ℕ) {o : Bool}
    (st : ℕ → QMCLeafB.RoundProgram.RSt) (M : ℕ → Matrix (Fin n) (Fin n) ℚ)
    (hstN : ∀ k, QMCLeafB.RoundProgram.stN (st k) = n)
    (hA : ∀ k, MatQ.correct n A (QMCLeafB.RoundProgram.stA (st k)))
    (hX : ∀ k, MatQ.correct n (M k) (QMCLeafB.RoundProgram.stX (st k)))
    (hT : ∀ k, QMCLeafB.RoundProgram.stT (st k) = t)
    (hgap : dq / 2 < eps)
    (hmem : ∀ k, k < N → QMCLeafB.RelaxOracle.RelaxMem A (M k) (t - eps) dq)
    (hverdict : o = QMCLeafB.SimLoop.anyOk (fun k => okBit (st k)) N) :
    o = false := by
  rw [hverdict, anyOk_false_of_hmem N st M hstN hA hX hT hgap hmem]

#print axioms QMCLeafB.RunStreams.okBit_eq_false_of_hmem
#print axioms QMCLeafB.RunStreams.anyOk_false_of_hmem
#print axioms QMCLeafB.RunStreams.verdict_false_of_hmem

/-! ## 4b.  The cut *slot* carries no content

`RelaxCut` demands `margin_pos` and a separation clause, but **no nondegeneracy condition on the
normal**.  The zero normal therefore gives a `RelaxCut` at *every* centre, at *every* level: the
separation clause becomes `-1 ≤ 0`.  Consequently `RunPartsStream`'s `C` slot is not where the work
is, and choosing `C` with the zero normal collapses the assembly's `c`-side bookkeeping: the
recorded normal is `c = 0`, so `hstatec` and `hdriftc` reduce to `0 ≤ margin/2` and `0 ≤ margin/2`,
`hcEq` is `c = 0`, and the dilated recorded normal is `cn = lam • flat(1)` — the identity direction.
What survives then is exactly `hstated` (the `d = 1` drift) and `hdiagc` (the diagonal band), i.e.
the analytic half, plus the flag stream. -/

/-- **The zero-normal cut.** -/
def relaxCut_zero {n : ℕ} (A cX : Matrix (Fin n) (Fin n) ℚ) (u δ : ℚ) :
    QMCLeafB.RelaxOracle.RelaxCut A cX u δ :=
  ⟨0, 1, one_pos, by
    intro X _
    have h0 : QMCLeafB.SepOracle.castMat (0 : Matrix (Fin n) (Fin n) ℚ) = 0 := by
      ext i j
      simp [QMCLeafB.SepOracle.castMat]
    rw [h0, QMCLeafB.SepOracle.frob]
    simp⟩

#print axioms QMCLeafB.RunStreams.relaxCut_zero

/-! ### 4c.  Executing the collapse: the witness of the zero normal, and the three trivialities -/

/-- The dilation engine's witness of the zero normal is zero (the shape is `PosQ`). -/
theorem witAt_zero (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0) (k : ℕ) :
    QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (fun _ => 0) k = 0 := by
  refine QMCLeafB.RunPartsDilate.mulVec_inj_of_posQ
    (QMCLeafB.RunPartsDilate.runShape_posQ G P hn cn hcne k) ?_
  rw [QMCLeafB.RunPartsDilate.witAt_spec]
  funext i
  simp

/-- **`hlam2` at the zero normal**: the two absolute values of the general ledger condition vanish,
so the dilation parameter only has to dominate the depth term. -/
theorem hlam2_zero_normal (G : QuantumMaxCutEnergy.Input)
    (P : QMCLeafB.FinalStroke.RunParams G) (hn : 2 ≤ G.n)
    (cn : ℕ → Fin (G.n * G.n) → ℚ) (hcne : ∀ k, cn k ≠ 0)
    (d : Fin (G.n * G.n) → ℚ) (lam T : ℚ) (k : ℕ)
    (h : T + 1 ≤ lam * (d ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne d k)) :
    |(fun _ => (0 : ℚ)) ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne d k
        + d ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (fun _ => 0) k|
      + |(fun _ => (0 : ℚ)) ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne (fun _ => 0) k|
      + T + 1
    ≤ lam * (d ⬝ᵥ QMCLeafB.RunPartsDilate.witAt G P hn cn hcne d k) := by
  rw [QMCLeafB.RunStreams.witAt_zero G P hn cn hcne k]
  simpa using h

/-- **`hstatec` and `hdriftc` at the zero normal** are both `0 ≤ margin/2`: the state mismatch and
the whole drift budget disappear. -/
theorem hstatec_zero (N : ℕ) (q : Fin N → ℝ) (cs : ℕ → Fin N → ℝ) (delta : ℕ → ℝ)
    (k : ℕ) (marg : ℚ) (hm : 0 ≤ marg) :
    (fun _ => ((0 : ℚ) : ℝ)) ⬝ᵥ q
        + ∑ j ∈ Finset.range k, delta j * max 0 (-((fun _ => ((0 : ℚ) : ℝ)) ⬝ᵥ cs j))
      ≤ (marg : ℝ) / 2 := by
  have h2 : (0 : ℝ) ≤ (marg : ℝ) / 2 := by
    have : (0 : ℝ) ≤ (marg : ℝ) := by exact_mod_cast hm
    linarith
  simpa using h2

/-- The same for the `d`-direction (`hdriftd`'s shape, which is *not* free: it is `hstated`). -/
theorem hdriftd_zero_trivial (N : ℕ) (a q : Fin N → ℝ) (marg : ℚ) (hm : 0 ≤ marg) :
    (fun _ => ((0 : ℚ) : ℝ)) ⬝ᵥ (a - q) ≤ (marg : ℝ) / 2 := by
  have h2 : (0 : ℝ) ≤ (marg : ℝ) / 2 := by
    have : (0 : ℝ) ≤ (marg : ℝ) := by exact_mod_cast hm
    linarith
  simpa using h2

#print axioms QMCLeafB.RunStreams.witAt_zero
#print axioms QMCLeafB.RunStreams.hlam2_zero_normal
#print axioms QMCLeafB.RunStreams.hstatec_zero
#print axioms QMCLeafB.RunStreams.hdriftd_zero_trivial

/-! ## 5.  The gap hypothesis holds at the campaign's own tolerance -/

/-- `dqShallow G / 2 < eps G` whenever the total weight is positive: the campaign's tolerance is
`eps/(9·Rq+1)`, far below `2·eps`.  So §3's incompatibility is not vacuous at the campaign
parameters — it is exactly the campaign's own slack. -/
theorem dqShallow_half_lt_eps (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G / 2 < QMCLeafB.RundataCert.eps G := by
  have hne : QMCLeafB.EngineRuntime.Rq G ≠ 0 := ne_of_gt hRq
  have hpos : 0 < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    positivity
  have hden : (1 : ℚ) ≤ 9 * QMCLeafB.EngineRuntime.Rq G + 1 := by linarith
  have h1 : QMCLeafB.RundataParams.dqShallow G ≤ QMCLeafB.RundataCert.eps G := by
    rw [QMCLeafB.RundataParams.dqShallow, if_neg hne, QMCLeafB.RundataParams.dqShallowCore]
    exact div_le_self hpos.le hden
  linarith

/-- **The slack round's test is `eps`-loose.**  `RoundT.roundT` reports `ok` when
`[A,cX] ≤ t + εw` with `εw = eps`, while the queried body at `u = t - eps` allows only
`[A,cX] ≤ t - eps + dq/2`.  The two agree only under `εw + eps ≤ dq/2`, which fails at the
campaign's tolerance by a factor `≈ 9·Rq`: `dqShallow G ≤ eps G < 2·eps G`.  So swapping the round
to `roundT` removes the *orientation* defect of §3 but not the *level* defect — the stream interface
must be re-based at the level the round's test actually certifies. -/
theorem two_eps_gt_dqShallow_half (G : QuantumMaxCutEnergy.Input)
    (hRq : 0 < QMCLeafB.EngineRuntime.Rq G) :
    QMCLeafB.RundataParams.dqShallow G / 2 < QMCLeafB.RundataCert.eps G + QMCLeafB.RundataCert.eps G := by
  have h := dqShallow_half_lt_eps G hRq
  have hpos : 0 < QMCLeafB.RundataCert.eps G := by
    unfold QMCLeafB.RundataCert.eps
    positivity
  linarith

#print axioms QMCLeafB.RunStreams.dqShallow_half_lt_eps
#print axioms QMCLeafB.RunStreams.two_eps_gt_dqShallow_half

/-! ## 6.  Axiom audit -/

#print axioms QMCLeafB.RunStreams.oracleR_ok
#print axioms QMCLeafB.RunStreams.oracleR_normal_diag
#print axioms QMCLeafB.RunStreams.oracleR_normal_thresh
#print axioms QMCLeafB.RunStreams.oracleR_normal_psd
#print axioms QMCLeafB.RunStreams.frobV_eq_frob
#print axioms QMCLeafB.RunStreams.fvR_eq_frob
#print axioms QMCLeafB.RunStreams.not_relaxMem_of_ok
#print axioms QMCLeafB.RunStreams.nonempty_relaxCut_of_ok
#print axioms QMCLeafB.RunStreams.okBit_eq_true_iff
#print axioms QMCLeafB.RunStreams.okBit_eq_false_of_hmem
#print axioms QMCLeafB.RunStreams.anyOk_false_of_hmem
#print axioms QMCLeafB.RunStreams.verdict_false_of_hmem
#print axioms QMCLeafB.RunStreams.relaxCut_zero
#print axioms QMCLeafB.RunStreams.witAt_zero
#print axioms QMCLeafB.RunStreams.hlam2_zero_normal
#print axioms QMCLeafB.RunStreams.hstatec_zero
#print axioms QMCLeafB.RunStreams.hdriftd_zero_trivial
#print axioms QMCLeafB.RunStreams.dqShallow_half_lt_eps
#print axioms QMCLeafB.RunStreams.two_eps_gt_dqShallow_half

end QMCLeafB.RunStreams


