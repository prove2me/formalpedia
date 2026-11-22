-- Prove2me | Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part07
-- name    : VehicleRoutingSurvey_RuralPostman1979_Part07
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-21T14:12:57.46223+00:00
-- url     : https://prove2.me/theorems/206f4874-46ed-42a8-bb0b-2c3c1a660fe7
-- title:
--   Rural postman algorithm — Routing input and compact weighted-matching dual state
-- statement:
--   This module supplies the Lean definitions and checked auxiliary results for routing input and compact weighted-matching dual state in the Table 3 proof. It uses the mission’s rural-run and arithmetic-RAM model.
-- source:
--   J. K. Lenstra and A. H. G. Rinnooy Kan, Complexity of vehicle routing and scheduling problems (1979), Table 3, printed p. 5. https://ir.cwi.nl/pub/9658/9658D.pdf

import Mathlib.Tactic.Ring
import Definitions.Def_SupplyChainTheory_tsp
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Chain
import Mathlib.Logic.Function.Basic
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part01
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part02
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part03
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part05
import Definitions.Def_VehicleRoutingSurvey_RuralPostman1979_Part06

/-! runtime/OccurrenceToMatchingInput.lean -/
section RppSource_OccurrenceToMatchingInput
namespace VehicleRoutingSurvey.Routing

variable {G : Network}

/-- Allocate parity, odd vertices, and their compact metric beyond the
completed occurrence prefix and the full real distance matrix. -/
def allocateMatchingInputBlock : List ArithmeticInstruction :=
  [.natAdd 9 29 28, .natAdd 31 9 5, .natAdd 21 31 5, .natAdd 63 21 5,
    .natSub 0 5 6, .natAdd 0 3 0, .natLoad 0 0, .natAdd 0 0 5,
    .natAdd 20 4 0, .natAdd 64 20 0, .natAdd 29 5 28, .natConst 10 0]

private def matchingInputLayoutWrites : List ℕ := [0, 9, 10, 20, 21, 29, 31, 63, 64]

theorem allocateMatchingInputBlock_correct {n table matrix : ℕ} {s : ArithmeticState}
    (frame : FloydFrame n table matrix s) (positive : 0 < n)
    (zero : s.nr 28 = 0) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns allocateMatchingInputBlock 12 s t ∧ t.halted = false ∧
      t.nr 9 = s.nr 29 ∧ t.nr 31 = s.nr 29 + n ∧ t.nr 21 = s.nr 29 + n + n ∧
      t.nr 63 = s.nr 29 + n + n + n ∧
      t.nr 20 = matrix + n * n ∧ t.nr 64 = matrix + n * n + n * n ∧
      t.nr 29 = n ∧ t.nr 10 = 0 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r ∉ matchingInputLayoutWrites, t.nr r = s.nr r := by
  let t := (arithmeticStep allocateMatchingInputBlock)^[12] s
  have ready : t.halted = false := by
    simp [t, allocateMatchingInputBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = allocateMatchingInputBlock.length := by
    simp [t, allocateMatchingInputBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have last : n - 1 < n := by omega
  have cells : s.nm (table + (n - 1)) + n = n * n := by
    rw [frame.rows _ last]
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
    simp [Nat.mul_succ]
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  have all : t.nr 9 = s.nr 29 ∧ t.nr 31 = s.nr 29 + n ∧ t.nr 21 = s.nr 29 + n + n ∧
      t.nr 63 = s.nr 29 + n + n + n ∧ t.nr 20 = matrix + n * n ∧
      t.nr 64 = matrix + n * n + n * n ∧ t.nr 29 = n ∧ t.nr 10 = 0 ∧
      t.nm = s.nm ∧ t.rm = s.rm := by
    simp [t, allocateMatchingInputBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
      zero, frame.dimension, frame.one, frame.tableBase, frame.matrixBase, cells]
  obtain ⟨parity, vertices, compactRows, freeNat, compact, freeReal, dimension, zeroReg,
    natural, real⟩ := all
  exact ⟨parity, vertices, compactRows, freeNat, compact, freeReal, dimension, zeroReg, natural, real,
    fun r outside => by
      have different (k : ℕ) (changed : k ∈ matchingInputLayoutWrites) : r ≠ k :=
        fun same => outside (same.symm ▸ changed)
      simp [t, allocateMatchingInputBlock, arithmeticStep, entry, running, Function.iterate_succ_apply',
        Function.update_of_ne (different 0 (by decide)), Function.update_of_ne (different 9 (by decide)),
        Function.update_of_ne (different 10 (by decide)), Function.update_of_ne (different 20 (by decide)),
        Function.update_of_ne (different 21 (by decide)), Function.update_of_ne (different 29 (by decide)),
        Function.update_of_ne (different 31 (by decide)), Function.update_of_ne (different 63 (by decide)),
        Function.update_of_ne (different 64 (by decide))]⟩

def occurrenceToMatchingInputBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock saveOccurrenceRegistersBlock publishOccurrenceBlock)
    allocateMatchingInputBlock) prepareMatchingInputBlock

private theorem compactMatchingNaturalDestinations :
    ∀ ins ∈ prepareMatchingInputBlock, naturalDestination ins < 63 := by
  have bounded : prepareMatchingInputBlock.all (fun ins => decide (naturalDestination ins < 63)) = true := by
    decide
  exact fun ins belongs => of_decide_eq_true (List.all_eq_true.mp bounded ins belongs)

private theorem saveOccurrenceDestinationBelowReservation :
    ∀ ins ∈ saveOccurrenceRegistersBlock, naturalDestination ins < 106 := by
  have bounded : saveOccurrenceRegistersBlock.all (fun ins => decide (naturalDestination ins < 106)) =
      true := by decide
  exact fun ins belongs => of_decide_eq_true (List.all_eq_true.mp bounded ins belongs)

/-- Build the actual compact input from an occurrence checkpoint. Matching
scratch starts beyond the reserved compact inputs, and the natural prefix
containing the occurrences and path pointers remains intact. -/
theorem occurrenceToMatchingInputBlock_correct {I : Service} {table matrix : ℕ}
    {edges : List (Fin I.graph.q)} {s : ArithmeticState}
    (positive : 0 < I.graph.n)
    (frame : FloydFrame I.graph.n table matrix s) (zero : s.nr 28 = 0)
    (cursor : s.nr 29 = s.nr 33 + edges.length)
    (encoded : OccurrenceArray s.nm (s.nr 33) edges)
    (raw : ∀ a < 2 + 3 * I.graph.q, s.nm a = (ruralNatInput I)[a]?.getD 0)
    (offsetBound : table + I.graph.n ≤ s.nr 29) (rawBound : 2 + 3 * I.graph.q ≤ s.nr 29)
    (costs : ∀ u v : Fin I.graph.n,
      s.rm (matrix + I.graph.n * u.val + v.val) = distance I.graph u v)
    (entry : s.pc = 0) (running : s.halted = false) :
    let n := I.graph.n
    let k := (oddVertexOrder I.graph edges).length
    let odd := s.nr 29 + n
    let rowOffsets := odd + n
    let compact := matrix + n * n
    ∃ t steps, BlockRuns occurrenceToMatchingInputBlock steps s t ∧ t.halted = false ∧
      steps ≤ 19 * edges.length + 17 * n ^ 2 + 26 * n + 34 ∧
      SavedOccurrenceRegisters s t ∧ t.nr 106 = s.nr 106 ∧
      t.nr 31 = odd ∧ t.nr 21 = rowOffsets ∧ t.nr 20 = compact ∧
      t.nr 63 = rowOffsets + n ∧ t.nr 64 = compact + n * n ∧ t.nr 32 = k ∧ k % 2 = 0 ∧
      (∀ i : Fin k, t.nm (odd + i.val) = (oddVertexAt I.graph edges i).val) ∧
      (∀ i < k, t.nm (rowOffsets + i) = k * i) ∧
      (∀ i j : Fin k, t.rm (compact + k * i.val + j.val) =
        distance I.graph (oddVertexAt I.graph edges i) (oddVertexAt I.graph edges j)) ∧
      (∀ a < s.nr 29, t.nm a = s.nm a) ∧ (∀ a < compact, t.rm a = s.rm a) := by
  let n := I.graph.n
  let k := (oddVertexOrder I.graph edges).length
  obtain ⟨saved, saves, itsReady, snapshot, savedNat, savedReal, savedFixed⟩ :=
    saveOccurrenceRegistersBlock_correct s entry running zero
  let publishEntry := {saved with pc := 0}
  have savedCursor : saved.nr 29 = saved.nr 33 + edges.length := by
    rw [savedFixed 29 (by decide), savedFixed 33 (by decide)]
    exact cursor
  have savedArray : OccurrenceArray publishEntry.nm (publishEntry.nr 33) edges := by
    change OccurrenceArray saved.nm (saved.nr 33) edges
    rwa [savedNat, savedFixed 33 (by decide)]
  obtain ⟨p, published, pReady, count, recordedBase, two, sameNat, sameReal, stored, keeps⟩ :=
    publishOccurrenceBlock_correct (s := publishEntry) rfl itsReady
      ((savedFixed 28 (by decide)).trans zero) savedCursor savedArray
  let publishedState := relocateState saveOccurrenceRegistersBlock.length p
  let allocateEntry := {publishedState with pc := 0}
  have pNat : p.nm = s.nm := sameNat.trans savedNat
  have pReal : p.rm = s.rm := sameReal.trans savedReal
  have pFixed (r : ℕ) (bound : r < 100) (different18 : r ≠ 18) (different23 : r ≠ 23)
      (different24 : r ≠ 24) : p.nr r = s.nr r :=
    (keeps r different18 different23 different24).trans (savedFixed r bound)
  have pFloyd : FloydFrame n table matrix allocateEntry :=
    frame.preserved (fun r hlo hhi => pFixed r (by omega) (by omega) (by omega) (by omega)) pNat
  have pZero := (pFixed 28 (by decide) (by decide) (by decide) (by decide)).trans zero
  have pCursor := pFixed 29 (by decide) (by decide) (by decide) (by decide)
  have pBase : p.nr 23 = s.nr 33 := recordedBase.trans (savedFixed 33 (by decide))
  obtain ⟨a, allocates, aReady, parityAt, oddAt, offsetsAt, freeNat,
      compactAt, freeReal, dimension, lowZero, aNat, aReal, aFixed⟩ :=
    allocateMatchingInputBlock_correct pFloyd positive pZero rfl pReady
  let allocatedState := relocateState (appendBlock saveOccurrenceRegistersBlock publishOccurrenceBlock).length a
  let compactEntry := {allocatedState with pc := 0}
  have aFrame : FloydFrame n table matrix compactEntry :=
    pFloyd.preserved (fun r lower upper => aFixed r (by
      simp [matchingInputLayoutWrites]
      omega)) aNat
  have indexedFrame : FloydFrame n (compactEntry.nr 3) (compactEntry.nr 4) compactEntry := by
    rw [aFrame.tableBase, aFrame.matrixBase]
    exact aFrame
  have parityBase : a.nr 9 = s.nr 29 := parityAt.trans pCursor
  have oddBase : a.nr 31 = s.nr 29 + n := by
    exact oddAt.trans (congrArg (· + n) pCursor)
  have offsetBase : a.nr 21 = s.nr 29 + n + n := by
    exact offsetsAt.trans (congrArg (fun value => value + n + n) pCursor)
  have scratch : a.nr 63 = s.nr 29 + n + n + n := by
    exact freeNat.trans (congrArg (fun value => value + n + n + n) pCursor)
  have aBase : a.nr 23 = s.nr 33 := (aFixed 23 (by decide)).trans pBase
  have allocatedNat : a.nm = s.nm := aNat.trans pNat
  have allocatedReal : a.rm = s.rm := aReal.trans pReal
  have prepareInput : EulerOccurrenceInput edges (compactEntry.nr 23) compactEntry.nm := by
    change EulerOccurrenceInput edges (a.nr 23) a.nm
    rw [aBase, allocatedNat]
    refine ⟨fun i => encoded i.val i.isLt, ?_, ?_⟩
    · intro e
      rw [show e.val + e.val + e.val + 2 = 2 + 3 * e.val by omega]
      exact (ruralInputs_preserveLinkEndpoints raw e).1
    · intro e
      rw [show e.val + e.val + e.val + 3 = 3 + 3 * e.val by omega]
      exact (ruralInputs_preserveLinkEndpoints raw e).2
  have preparedCosts (u v : Fin n) :
      compactEntry.rm (compactEntry.nr 4 + n * u.val + v.val) = distance I.graph u v := by
    rw [aFrame.matrixBase]
    change a.rm _ = _
    rw [allocatedReal]
    exact costs u v
  obtain ⟨readyState, prepares, ready, oddCount, even, stable, oddCells, compactOffsets,
      metric, naturalPrefix, realPrefix⟩ :=
    prepareMatchingInputBlock_correct (s := compactEntry) rfl aReady indexedFrame lowZero
      ((aFixed 24 (by decide)).trans two) dimension ((aFixed 18 (by decide)).trans count)
      (by change compactEntry.nr 3 + n ≤ a.nr 9; rwa [aFrame.tableBase, parityBase])
      (by change a.nr 23 + edges.length ≤ a.nr 9; rw [aBase, parityBase, cursor])
      (by change _ ≤ a.nr 9; rwa [parityBase])
      (by change a.nr 9 + n ≤ a.nr 31; rw [parityBase, oddBase])
      (by change a.nr 31 + n ≤ a.nr 21; rw [oddBase, offsetBase])
      (by change compactEntry.nr 4 + n * n ≤ a.nr 20; rw [aFrame.matrixBase, compactAt])
      prepareInput preparedCosts
  let final := relocateState
    (appendBlock (appendBlock saveOccurrenceRegistersBlock publishOccurrenceBlock) allocateMatchingInputBlock).length
    readyState
  have high (r : ℕ) (bound : 63 ≤ r) : readyState.nr r = a.nr r := by
    rw [← prepares.run]
    exact arithmeticRun_keeps_high_register (fun ins belongs =>
      (compactMatchingNaturalDestinations ins belongs).trans_le bound) compactEntry _
  have allocatedSnapshot : SavedOccurrenceRegisters s compactEntry := by
    apply snapshot.preserved
    intro r bound
    exact (aFixed r (by simp [matchingInputLayoutWrites]; omega)).trans
      (keeps r (by omega) (by omega) (by omega))
  have finalSnapshot : SavedOccurrenceRegisters s final :=
    allocatedSnapshot.preserved (fun r bound => high r (by omega))
  have r106 : final.nr 106 = s.nr 106 := by
    have savedReservation : saved.nr 106 = s.nr 106 := by
      rw [← saves.run]
      exact arithmeticRun_keeps_high_register saveOccurrenceDestinationBelowReservation s 6
    exact (high 106 (by decide)).trans ((aFixed 106 (by decide)).trans
      ((keeps 106 (by decide) (by decide) (by decide)).trans savedReservation))
  have recordedOdd : final.nr 31 = s.nr 29 + n := (stable 31 (by decide)).trans oddBase
  have recordedOffsets : final.nr 21 = s.nr 29 + n + n := (stable 21 (by decide)).trans offsetBase
  have recordedCompact : final.nr 20 = matrix + n * n := (stable 20 (by decide)).trans compactAt
  have combined := ((saves.append published).append allocates).append prepares
  have kBound : k ≤ n := by simpa using (oddVertexOrder_nodup I.graph edges).length_le_card
  have charge : k * (17 * k + 5) ≤ n * (17 * n + 5) := Nat.mul_le_mul kBound (by omega)
  have time : 6 + 3 + 12 +
      (1 + (1 + (n * 5 + 1)) + (19 * edges.length + 2) +
        (10 * n + 3 + (6 * k + 3) + (1 + (k * (17 * k + 5) + 1)))) ≤
      19 * edges.length + 17 * n ^ 2 + 26 * n + 34 := by
    have expansion : n * (17 * n + 5) = 17 * n ^ 2 + 5 * n := by ring
    rw [expansion] at charge
    omega
  refine ⟨final, _, combined, ready, time, finalSnapshot, r106, recordedOdd, recordedOffsets,
    recordedCompact, (high 63 le_rfl).trans scratch, (high 64 (by decide)).trans freeReal,
    oddCount, even, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have cell := oddCells i
    change readyState.nm (a.nr 31 + i.val) = _ at cell
    rwa [oddBase] at cell
  · intro i inside
    have cell := compactOffsets i inside
    change readyState.nm (a.nr 21 + i) = _ at cell
    rwa [offsetBase] at cell
  · intro i j
    have cell := metric i j
    change readyState.rm (a.nr 20 + k * i.val + j.val) = _ at cell
    rwa [compactAt] at cell
  · intro address before
    exact (naturalPrefix address (by change address < a.nr 9; rwa [parityBase])).trans
      ((congrFun aNat address).trans (congrFun pNat address))
  · intro address before
    exact (realPrefix address (by change address < a.nr 20; rwa [compactAt])).trans
      ((congrFun aReal address).trans (congrFun pReal address))

end VehicleRoutingSurvey.Routing
end RppSource_OccurrenceToMatchingInput

/-! matching/CompactMatchingLift.lean -/
section RppSource_CompactMatchingLift
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

private def compactEdgeEmbedding {k n : ℕ} (f : Fin k ↪ Fin n) :
    Sym2 (Fin k) ↪ Sym2 (Fin n) where
  toFun := Sym2.map f
  inj' := by
    intro a b same
    induction a using Sym2.inductionOn with
    | hf x y =>
      induction b using Sym2.inductionOn with
      | hf u v =>
        change s(f x, f y) = s(f u, f v) at same
        exact Sym2.eq_iff.mpr ((Sym2.eq_iff.mp same).elim
          (fun h => Or.inl ⟨f.injective h.1, f.injective h.2⟩)
          (fun h => Or.inr ⟨f.injective h.1, f.injective h.2⟩))

private theorem compactEdge_mem {k n : ℕ} (f : Fin k ↪ Fin n)
    {a : Fin k} {e : Sym2 (Fin k)} :
    f a ∈ compactEdgeEmbedding f e ↔ a ∈ e := by
  induction e using Sym2.inductionOn with
  | hf x y =>
    change f a ∈ s(f x, f y) ↔ a ∈ s(x, y)
    simp only [Sym2.mem_iff]
    exact ⟨fun h => h.elim (fun e => Or.inl (f.injective e)) (fun e => Or.inr (f.injective e)),
      fun h => h.elim (Or.inl ∘ congrArg f) (Or.inr ∘ congrArg f)⟩

private theorem compactEdge_member {k n : ℕ} (f : Fin k ↪ Fin n)
    {v : Fin n} {e : Sym2 (Fin k)} (inside : v ∈ compactEdgeEmbedding f e) :
    ∃ a ∈ e, f a = v := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    change v ∈ s(f a, f b) at inside
    rcases Sym2.mem_iff.mp inside with h | h
    · exact ⟨a, Sym2.mem_mk_left _ _, h.symm⟩
    · exact ⟨b, Sym2.mem_mk_right _ _, h.symm⟩

private theorem compactEdge_diag {k n : ℕ} (f : Fin k ↪ Fin n) (e : Sym2 (Fin k)) :
    (compactEdgeEmbedding f e).IsDiag ↔ e.IsDiag := by
  induction e using Sym2.inductionOn with
  | hf a b =>
    change s(f a, f b).IsDiag ↔ s(a, b).IsDiag
    simp only [Sym2.mk_isDiag_iff]
    exact ⟨fun e => f.injective e, congrArg f⟩

private theorem compactPerfect_iff {k n : ℕ} (f : Fin k ↪ Fin n) (O : Finset (Fin n))
    (range : ∀ v, v ∈ O ↔ ∃ a, f a = v) (M : Finset (Sym2 (Fin k))) :
    IsPerfectMatchingOn O (M.map (compactEdgeEmbedding f)) ↔
      IsPerfectMatchingOn Finset.univ M := by
  constructor
  · intro original
    constructor
    · intro e present
      have lifted := original.1 _ (Finset.mem_map.mpr ⟨e, present, rfl⟩)
      exact ⟨fun h => lifted.1 ((compactEdge_diag f e).mpr h), fun _ _ => Finset.mem_univ _⟩
    · intro a _
      have inOriginal : f a ∈ O := (range _).mpr ⟨a, rfl⟩
      obtain ⟨found, foundIn, unique⟩ := original.2 (f a) inOriginal
      obtain ⟨e, em, rfl⟩ := Finset.mem_map.mp foundIn.1
      refine ⟨e, ⟨em, (compactEdge_mem f).mp foundIn.2⟩, ?_⟩
      intro e' candidate
      exact (compactEdgeEmbedding f).injective (unique _
        ⟨Finset.mem_map.mpr ⟨e', candidate.1, rfl⟩, (compactEdge_mem f).mpr candidate.2⟩)
  · intro compact
    constructor
    · intro e present
      obtain ⟨child, inCompact, rfl⟩ := Finset.mem_map.mp present
      refine ⟨fun h => (compact.1 child inCompact).1 ((compactEdge_diag f child).mp h), ?_⟩
      intro v hv
      obtain ⟨a, _, rfl⟩ := compactEdge_member f hv
      exact (range _).mpr ⟨a, rfl⟩
    · intro v member
      obtain ⟨a, rfl⟩ := (range v).mp member
      obtain ⟨e, inCompact, unique⟩ := compact.2 a (Finset.mem_univ _)
      refine ⟨compactEdgeEmbedding f e,
        ⟨Finset.mem_map.mpr ⟨e, inCompact.1, rfl⟩, (compactEdge_mem f).mpr inCompact.2⟩, ?_⟩
      intro candidate good
      obtain ⟨e', e'm, rfl⟩ := Finset.mem_map.mp good.1
      exact congrArg (compactEdgeEmbedding f) (unique e' ⟨e'm, (compactEdge_mem f).mp good.2⟩)

private theorem compactEdgeSetWeight {k n : ℕ} (f : Fin k ↪ Fin n) (c : Fin n → Fin n → ℝ)
    (M : Finset (Sym2 (Fin k))) :
    edgeSetWeight c (M.map (compactEdgeEmbedding f)) =
      edgeSetWeight (fun i j => c (f i) (f j)) M := by
  unfold edgeSetWeight
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  induction e using Sym2.inductionOn with
  | hf a b => rfl

private theorem compactMinimum_lift {k n : ℕ} (f : Fin k ↪ Fin n) (c : Fin n → Fin n → ℝ)
    {O : Finset (Fin n)} (range : ∀ v, v ∈ O ↔ ∃ a, f a = v) {M : Finset (Sym2 (Fin k))}
    (optimal : IsMinMatchingOn (fun i j => c (f i) (f j)) Finset.univ M) :
    IsMinMatchingOn c O (M.map (compactEdgeEmbedding f)) := by
  refine ⟨(compactPerfect_iff f O range M).mpr optimal.1, ?_⟩
  intro candidate perfect
  let pulled := Finset.univ.filter (fun d : Sym2 (Fin k) => compactEdgeEmbedding f d ∈ candidate)
  have recovers : pulled.map (compactEdgeEmbedding f) = candidate := by
    ext e
    constructor
    · intro present
      obtain ⟨child, inPulled, rfl⟩ := Finset.mem_map.mp present
      exact (Finset.mem_filter.mp inPulled).2
    · intro present
      have endpoints := (perfect.1 e present).2
      induction e using Sym2.inductionOn with
      | hf u v =>
        obtain ⟨a, rfl⟩ := (range u).mp (endpoints u (Sym2.mem_mk_left _ _))
        obtain ⟨b, rfl⟩ := (range v).mp (endpoints v (Sym2.mem_mk_right _ _))
        exact Finset.mem_map.mpr ⟨s(a, b), Finset.mem_filter.mpr ⟨Finset.mem_univ _, present⟩, rfl⟩
  have lifted : IsPerfectMatchingOn O (pulled.map (compactEdgeEmbedding f)) := by
    rw [recovers]
    exact perfect
  have compact := (compactPerfect_iff f O range pulled).mp lifted
  rw [← recovers, compactEdgeSetWeight, compactEdgeSetWeight]
  exact optimal.2 pulled compact

def liftOddPairs {G : Network} (edges : List (Fin G.q))
    (pairs : List (Fin (oddVertexOrder G edges).length × Fin (oddVertexOrder G edges).length)) :
    List (Fin G.n × Fin G.n) :=
  pairs.map fun p => (oddVertexAt G edges p.1, oddVertexAt G edges p.2)

/-- An exact optimum in compact indices is also an exact optimum for the
original odd vertices. The map preserves different occurrences of pairs
and the same edge costs, including tied or zero distances. -/
theorem liftOddPairs_minimumMatching {G : Network} {edges : List (Fin G.q)}
    {pairs : List (Fin (oddVertexOrder G edges).length × Fin (oddVertexOrder G edges).length)}
    (nodup : (pairs.map (fun p => s(p.1, p.2))).Nodup)
    (optimal : IsMinMatchingOn
      (fun a b => distance G (oddVertexAt G edges a) (oddVertexAt G edges b))
      Finset.univ (pairs.map (fun p => s(p.1, p.2))).toFinset) :
    MinimumMatching G edges (liftOddPairs edges pairs) := by
  let f : Fin (oddVertexOrder G edges).length ↪ Fin G.n :=
    ⟨oddVertexAt G edges, oddVertexAt_injective G edges⟩
  let e := compactEdgeEmbedding f
  let encoded := pairs.map (fun p => s(p.1, p.2))
  have sequence : ((liftOddPairs edges pairs).map (fun p => s(p.1, p.2))) = encoded.map e := by
    simp only [liftOddPairs, encoded, List.map_map]
    rfl
  have asSet : matchingEdges G (liftOddPairs edges pairs) = encoded.toFinset.map e := by
    unfold matchingEdges
    rw [sequence]
    ext x
    simp only [List.mem_toFinset, List.mem_map, Finset.mem_map]
  refine ⟨?_, ?_⟩
  · rw [sequence]
    exact List.Nodup.map e.injective nodup
  · rw [asSet]
    exact compactMinimum_lift f (distance G) (oddVertexAt_range G edges) optimal


end VehicleRoutingSurvey.Routing
end RppSource_CompactMatchingLift

/-! runtime/MateOutput.lean -/
section RppSource_MateOutput
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

/-- Emit a compact matching pair only at its smaller index. The stored
values are original vertices, so the path emitter can read them directly. -/
def appendMatePairCell : List ArithmeticInstruction :=
  [.natAdd 0 33 17, .natLoad 1 0, .natBranch 1 17 13 3,
   .natAdd 0 31 17, .natLoad 2 0, .natAdd 0 31 1, .natLoad 7 0,
   .natStore 36 2, .natAdd 36 36 6, .natStore 36 7, .natAdd 36 36 6,
   .natAdd 35 35 6, .jump 23,
   .jump 14, .jump 15, .jump 16, .jump 17, .jump 18, .jump 19, .jump 20,
   .jump 21, .jump 22, .jump 23]

theorem appendMatePairCell_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) (one : s.nr 6 = 1) :
    let mate := s.nm (s.nr 33 + s.nr 17)
    let includePair := s.nr 17 < mate
    ∃ t, BlockRuns appendMatePairCell 13 s t ∧ t.halted = false ∧ t.rm = s.rm ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 7 → r ≠ 35 → r ≠ 36 → t.nr r = s.nr r) ∧
      t.nr 35 = (if includePair then s.nr 35 + 1 else s.nr 35) ∧
      t.nr 36 = (if includePair then s.nr 36 + 2 else s.nr 36) ∧
      t.nm = if includePair then
          Function.update (Function.update s.nm (s.nr 36) (s.nm (s.nr 31 + s.nr 17)))
            (s.nr 36 + 1) (s.nm (s.nr 31 + mate))
        else s.nm := by
  let t := (arithmeticStep appendMatePairCell)^[13] s
  have output : t.halted = false ∧ t.pc = appendMatePairCell.length ∧ t.rm = s.rm ∧
      (∀ r, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 7 → r ≠ 35 → r ≠ 36 → t.nr r = s.nr r) ∧
      t.nr 35 = (if s.nr 17 < s.nm (s.nr 33 + s.nr 17) then s.nr 35 + 1 else s.nr 35) ∧
      t.nr 36 = (if s.nr 17 < s.nm (s.nr 33 + s.nr 17) then s.nr 36 + 2 else s.nr 36) ∧
      t.nm = if s.nr 17 < s.nm (s.nr 33 + s.nr 17) then
          Function.update (Function.update s.nm (s.nr 36) (s.nm (s.nr 31 + s.nr 17)))
            (s.nr 36 + 1) (s.nm (s.nr 31 + s.nm (s.nr 33 + s.nr 17)))
        else s.nm := by
    by_cases chosen : s.nr 17 < s.nm (s.nr 33 + s.nr 17)
    · have pass : ¬s.nm (s.nr 33 + s.nr 17) ≤ s.nr 17 := Nat.not_le.mpr chosen
      simp [t, appendMatePairCell, arithmeticStep, entry, running, one, chosen, pass,
        Function.iterate_succ_apply', Nat.add_assoc]
      intro r not0 not1 not2 not7 not35 not36
      simp [Function.update_of_ne not0, Function.update_of_ne not1, Function.update_of_ne not2,
        Function.update_of_ne not7, Function.update_of_ne not35, Function.update_of_ne not36]
    · have skip : s.nm (s.nr 33 + s.nr 17) ≤ s.nr 17 := Nat.le_of_not_gt chosen
      simp [t, appendMatePairCell, arithmeticStep, entry, running, chosen, skip,
        Function.iterate_succ_apply']
      intro r not0 not1 _ _ _ _
      simp [Function.update_of_ne not0, Function.update_of_ne not1]
  exact ⟨t, BlockRuns.of_running_exit rfl output.1 output.2.1, output.1, output.2.2⟩

def emitMatePairsBlock : List ArithmeticInstruction :=
  appendBlock [.natAdd 36 34 10, .natConst 35 0] (countedLoopFromZero 6 17 32 appendMatePairCell)

def matePairsInIndexOrder {k : ℕ} (mate : Fin k → Fin k) : List (Fin k × Fin k) :=
  ((List.finRange k).filter (fun i => decide (i < mate i))).map fun i => (i, mate i)

theorem mem_matePairsInIndexOrder {k : ℕ} (mate : Fin k → Fin k) (p : Fin k × Fin k) :
    p ∈ matePairsInIndexOrder mate ↔ p ∈ pairsOfMate Finset.univ mate := by
  rw [mem_pairsOfMate]
  simp only [matePairsInIndexOrder, List.mem_map, List.mem_filter, List.mem_finRange,
    Finset.mem_univ, true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨i, ordered, rfl⟩
    exact ⟨ordered, rfl⟩
  · rintro ⟨ordered, right⟩
    exact ⟨p.1, ordered, Prod.ext rfl right.symm⟩

theorem matePairsInIndexOrder_nodup {k : ℕ} (mate : Fin k → Fin k) :
    ((matePairsInIndexOrder mate).map (fun p => s(p.1, p.2))).Nodup := by
  rw [matePairsInIndexOrder, List.map_map]
  apply List.Nodup.map_on _ ((List.nodup_finRange _).filter _)
  intro a ha b hb equal
  rcases Sym2.eq_iff.mp equal with same | reversed
  · exact same.1
  · have first := of_decide_eq_true (List.mem_filter.mp ha).2
    have second := of_decide_eq_true (List.mem_filter.mp hb).2
    have conflicting : mate a < a := calc
      mate a = b := reversed.2
      _ < mate b := second
      _ = a := reversed.1.symm
    exact (not_lt_of_ge first.le conflicting).elim

theorem matePairsInIndexOrder_edges {k : ℕ} (mate : Fin k → Fin k) :
    ((matePairsInIndexOrder mate).map (fun p => s(p.1, p.2))).toFinset =
      mateEdgeSet Finset.univ mate := by
  unfold mateEdgeSet
  ext e
  simp only [List.mem_toFinset, List.mem_map, mem_matePairsInIndexOrder]


end VehicleRoutingSurvey.Routing
end RppSource_MateOutput

/-! runtime/MatePairArray.lean -/
section RppSource_MatePairArray
namespace VehicleRoutingSurvey.Routing

private theorem ExpansionPairArray.storePair {G : Network} {memory : ℕ → ℕ}
    {base : ℕ} {pairs : List (Fin G.n × Fin G.n)} (encoded : ExpansionPairArray memory base pairs)
    (p : Fin G.n × Fin G.n) :
    let cursor := base + 2 * pairs.length
    let after := Function.update (Function.update memory cursor p.1.val) (cursor + 1) p.2.val
    ExpansionPairArray after base (pairs ++ [p]) := by
  dsimp only
  intro i valid
  by_cases old : i < pairs.length
  · have before : base + 2 * i + 1 < base + 2 * pairs.length := by omega
    rw [List.getElem_append_left old]
    constructor
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (encoded i old).1
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact (encoded i old).2
  · have last : i = pairs.length := by
      simp only [List.length_append, List.length_singleton] at valid
      omega
    subst i
    rw [List.getElem_append_right le_rfl]
    simp [Function.update_of_ne (show base + 2 * pairs.length ≠ base + 2 * pairs.length + 1 by omega)]

private def matePairsPrefix {k : ℕ} (mate : Fin k → Fin k) (size : ℕ) : List (Fin k × Fin k) :=
  (((List.finRange k).take size).filter (fun j => decide (j < mate j))).map fun j => (j, mate j)

private theorem matePairsPrefix_succ {k : ℕ} (mate : Fin k → Fin k) (i : Fin k) :
    matePairsPrefix mate (i.val + 1) =
      if i < mate i then matePairsPrefix mate i.val ++ [(i, mate i)] else matePairsPrefix mate i.val := by
  have within : i.val < (List.finRange k).length := by simpa using i.isLt
  have here : (List.finRange k)[i.val] = i := Fin.ext (by simp)
  unfold matePairsPrefix
  rw [List.take_succ_eq_append_getElem within, here, List.filter_append, List.map_append]
  by_cases selected : i < mate i <;> simp [selected]

private theorem matePairsPrefix_length_le {k : ℕ} (mate : Fin k → Fin k) (i : ℕ) :
    (matePairsPrefix mate i).length ≤ k := by
  unfold matePairsPrefix
  rw [List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

private def mateOutputFixed : List ℕ := [3, 4, 5, 6, 26, 28, 29, 31, 32, 33, 34]

private structure MateOutputProgress {G : Network} {edges : List (Fin G.q)}
    (mate : Fin (oddVertexOrder G edges).length → Fin (oddVertexOrder G edges).length)
    (s : ArithmeticState) (i : ℕ) (m : ArithmeticState) : Prop where
  entry : m.pc = 0
  running : m.halted = false
  index : m.nr 17 = i
  fixed : ∀ r ∈ mateOutputFixed, m.nr r = s.nr r
  count : m.nr 35 = (matePairsPrefix mate i).length
  cursor : m.nr 36 = s.nr 34 + 2 * (matePairsPrefix mate i).length
  outside : ∀ a, a < s.nr 34 ∨ s.nr 34 + 2 * (matePairsPrefix mate i).length ≤ a →
    m.nm a = s.nm a
  realMemory : m.rm = s.rm
  written : ExpansionPairArray m.nm (s.nr 34) (liftOddPairs edges (matePairsPrefix mate i))

/-- Decode an optimal compact partner table into the original pair array
consumed by the path expansion block. Each selected mate is emitted once. -/
theorem emitMatePairsBlock_withFootprint {G : Network} {edges : List (Fin G.q)} {s : ArithmeticState}
    {mate : Fin (oddVertexOrder G edges).length → Fin (oddVertexOrder G edges).length}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (count : s.nr 32 = (oddVertexOrder G edges).length)
    (oddBound : s.nr 31 + (oddVertexOrder G edges).length ≤ s.nr 34 ∨
      s.nr 34 + 2 * (oddVertexOrder G edges).length ≤ s.nr 31)
    (mateBound : s.nr 33 + (oddVertexOrder G edges).length ≤ s.nr 34 ∨
      s.nr 34 + 2 * (oddVertexOrder G edges).length ≤ s.nr 33)
    (oddMap : ∀ i : Fin (oddVertexOrder G edges).length,
      s.nm (s.nr 31 + i.val) = (oddVertexAt G edges i).val)
    (mateMap : ∀ i : Fin (oddVertexOrder G edges).length, s.nm (s.nr 33 + i.val) = (mate i).val)
    (least : SupplyChainTheory.IsMinMatchingOn
      (fun i j => distance G (oddVertexAt G edges i) (oddVertexAt G edges j))
      Finset.univ (mateEdgeSet Finset.univ mate)) :
    let k := (oddVertexOrder G edges).length
    ∃ t pairs, BlockRuns emitMatePairsBlock (16 * k + 4) s t ∧ t.halted = false ∧
      t.nr 34 = s.nr 34 ∧ t.nr 35 = pairs.length ∧ ExpansionPairArray t.nm (s.nr 34) pairs ∧
      MinimumMatching G edges pairs ∧ (∀ a < s.nr 34, t.nm a = s.nm a) ∧ t.rm = s.rm ∧
      (∀ a, a < s.nr 34 ∨ s.nr 34 + 2 * pairs.length ≤ a → t.nm a = s.nm a) ∧
      pairs.length ≤ k := by
  let k := (oddVertexOrder G edges).length
  let setup : List ArithmeticInstruction := [.natAdd 36 34 10, .natConst 35 0]
  let first := {s with
    pc := 2
    nr := Function.update (Function.update s.nr 36 (s.nr 34)) 35 0}
  have set : BlockRuns setup 2 s first := by
    have run : (arithmeticStep setup)^[2] s = first := by
      simp [setup, first, arithmeticStep, entry, running, zero, Function.iterate_succ_apply']
    exact BlockRuns.of_running_exit run running rfl
  have seed : MateOutputProgress (edges := edges) mate s 0
      {{first with pc := 0} with nr := Function.update first.nr 17 0} := by
    refine ⟨rfl, running, by simp, ?_, by simp [first, matePairsPrefix],
      by simp [first, matePairsPrefix], fun _ _ => rfl, rfl, ?_⟩
    · intro r hr
      have not17 : r ≠ 17 := by rintro rfl; simp [mateOutputFixed] at hr
      have not35 : r ≠ 35 := by rintro rfl; simp [mateOutputFixed] at hr
      have not36 : r ≠ 36 := by rintro rfl; simp [mateOutputFixed] at hr
      simp [first, Function.update_of_ne not17, Function.update_of_ne not35, Function.update_of_ne not36]
    · intro j impossible
      simp [matePairsPrefix, liftOddPairs] at impossible
  have control (i : ℕ) (m : ArithmeticState) (inv : MateOutputProgress (edges := edges) mate s i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 17 = i ∧ m.nr 32 = k :=
    ⟨inv.entry, inv.running, inv.index, (inv.fixed 32 (by decide)).trans count⟩
  have iterate (i : ℕ) (inside : i < k) (m : ArithmeticState)
      (inv : MateOutputProgress (edges := edges) mate s i m) :
      ∃ t, BlockRuns appendMatePairCell 13 m t ∧ t.halted = false ∧
        MateOutputProgress (edges := edges) mate s (i + 1)
          {t with pc := 0, nr := Function.update t.nr 17 (t.nr 17 + t.nr 6)} := by
    let a : Fin k := ⟨i, inside⟩
    let pair := (oddVertexAt G edges a, oddVertexAt G edges (mate a))
    have prefixLength : (matePairsPrefix mate i).length ≤ k := matePairsPrefix_length_le mate i
    have outsideMate : s.nr 33 + i < s.nr 34 ∨
        s.nr 34 + 2 * (matePairsPrefix mate i).length ≤ s.nr 33 + i := by
      change s.nr 33 + k ≤ s.nr 34 ∨ s.nr 34 + 2 * k ≤ s.nr 33 at mateBound
      rcases mateBound with lower | upper
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have outsideOdd (j : Fin k) : s.nr 31 + j.val < s.nr 34 ∨
        s.nr 34 + 2 * (matePairsPrefix mate i).length ≤ s.nr 31 + j.val := by
      have inside := j.isLt
      change s.nr 31 + k ≤ s.nr 34 ∨ s.nr 34 + 2 * k ≤ s.nr 31 at oddBound
      rcases oddBound with lower | upper
      · exact Or.inl (by omega)
      · exact Or.inr (by omega)
    have mateRead : m.nm (m.nr 33 + m.nr 17) = (mate a).val := by
      rw [inv.fixed 33 (by decide), inv.index, inv.outside _ outsideMate]
      exact mateMap a
    have currentRead : m.nm (m.nr 31 + m.nr 17) = pair.1.val := by
      rw [inv.fixed 31 (by decide), inv.index, inv.outside _ (outsideOdd a)]
      exact oddMap a
    have nextRead : m.nm (m.nr 31 + (mate a).val) = pair.2.val := by
      rw [inv.fixed 31 (by decide), inv.outside _ (outsideOdd (mate a))]
      exact oddMap (mate a)
    have mOne := (inv.fixed 6 (by decide)).trans one
    obtain ⟨t, run, ready, preservedReal, registers, length, cursor, memory⟩ :=
      appendMatePairCell_correct inv.entry inv.running mOne
    have tIndex := (registers 17 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans inv.index
    have tOne := (registers 6 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans mOne
    have kept (r : ℕ) (hr : r ∈ mateOutputFixed) :
        (Function.update t.nr 17 (t.nr 17 + t.nr 6)) r = s.nr r := by
      have safety : r ≠ 0 ∧ r ≠ 1 ∧ r ≠ 2 ∧ r ≠ 7 ∧ r ≠ 17 ∧ r ≠ 35 ∧ r ≠ 36 := by
        simp [mateOutputFixed] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      obtain ⟨p0, p1, p2, p7, p17, p35, p36⟩ := safety
      exact (Function.update_of_ne p17 _ _).trans
        ((registers r p0 p1 p2 p7 p35 p36).trans (inv.fixed r hr))
    have incrementShape := matePairsPrefix_succ mate a
    change matePairsPrefix mate (i + 1) =
      (if a < mate a then matePairsPrefix mate i ++ [(a, mate a)] else matePairsPrefix mate i) at incrementShape
    rw [mateRead, inv.index, inv.count] at length
    rw [mateRead, inv.index, inv.cursor] at cursor
    rw [mateRead, currentRead, nextRead, inv.index, inv.cursor] at memory
    refine ⟨t, run, ready, ⟨rfl, ready, by simp [tIndex, tOne], kept, ?_, ?_, ?_,
      preservedReal.trans inv.realMemory, ?_⟩⟩
    · change t.nr 35 = _
      rw [length, incrementShape]
      by_cases chosen : a < mate a
      · have rawChosen : i < (mate a).val := chosen
        simp [if_pos chosen, if_pos rawChosen]
      · have rawChosen : ¬i < (mate a).val := chosen
        simp [if_neg chosen, if_neg rawChosen]
    · change t.nr 36 = _
      rw [cursor, incrementShape]
      by_cases chosen : a < mate a
      · have rawChosen : i < (mate a).val := chosen
        simp [if_pos chosen, if_pos rawChosen, Nat.mul_succ, Nat.add_assoc]
      · have rawChosen : ¬i < (mate a).val := chosen
        simp [if_neg chosen, if_neg rawChosen]
    · intro address out
      change t.nm address = _
      rw [memory]
      change address < s.nr 34 ∨ s.nr 34 + 2 * (matePairsPrefix mate (i + 1)).length ≤ address at out
      rw [incrementShape] at out
      by_cases chosen : a < mate a
      · have rawChosen : i < (mate a).val := chosen
        rw [if_pos chosen, List.length_append, List.length_singleton] at out
        rw [if_pos rawChosen]
        have first : address ≠ s.nr 34 + 2 * (matePairsPrefix mate i).length := by
          rcases out with lower | upper <;> omega
        have second : address ≠ s.nr 34 + 2 * (matePairsPrefix mate i).length + 1 := by
          rcases out with lower | upper <;> omega
        rw [Function.update_of_ne second, Function.update_of_ne first]
        exact inv.outside address (out.imp id (by intro greater; omega))
      · have rawChosen : ¬i < (mate a).val := chosen
        rw [if_neg rawChosen]
        exact inv.outside address (by simpa only [if_neg chosen] using out)
    · change ExpansionPairArray t.nm (s.nr 34) (liftOddPairs edges (matePairsPrefix mate (i + 1)))
      rw [memory, incrementShape]
      by_cases chosen : a < mate a
      · have rawChosen : i < (mate a).val := chosen
        simpa [if_pos chosen, if_pos rawChosen, liftOddPairs, pair] using
          inv.written.storePair pair
      · have rawChosen : ¬i < (mate a).val := chosen
        simpa [if_neg chosen, if_neg rawChosen] using inv.written
  obtain ⟨last, inv, loop⟩ := countedLoopFromZero_correct 6 17 32 k 13
    appendMatePairCell (MateOutputProgress (edges := edges) mate s)
      (s := {first with pc := 0}) rfl running seed control iterate
  have time : 2 + (1 + (k * (13 + 3) + 1)) = 16 * k + 4 := by omega
  have run := set.append loop
  rw [time] at run
  have full : matePairsPrefix mate k = matePairsInIndexOrder mate := by
    rw [matePairsPrefix, matePairsInIndexOrder, List.take_of_length_le (by simp [k])]
  have global : MinimumMatching G edges (liftOddPairs edges (matePairsInIndexOrder mate)) :=
    liftOddPairs_minimumMatching (matePairsInIndexOrder_nodup mate)
      (by rw [matePairsInIndexOrder_edges]; exact least)
  refine ⟨_, liftOddPairs edges (matePairsInIndexOrder mate), run, inv.running,
    inv.fixed 34 (by decide), ?_, ?_, global, fun a earlier => inv.outside a (.inl earlier),
    inv.realMemory, ?_, ?_⟩
  · change last.nr 35 = _
    rw [inv.count, full]
    simp [liftOddPairs]
  · change ExpansionPairArray last.nm (s.nr 34) _
    simpa only [full] using inv.written
  · intro address outside
    exact inv.outside address (by simpa [liftOddPairs, full] using outside)
  · simpa [liftOddPairs, full] using matePairsPrefix_length_le mate k

/-- Decoder interface for callers that put the complete compact tables
before the pair array. -/
theorem emitMatePairsBlock_correct {G : Network} {edges : List (Fin G.q)} {s : ArithmeticState}
    {mate : Fin (oddVertexOrder G edges).length → Fin (oddVertexOrder G edges).length}
    (entry : s.pc = 0) (running : s.halted = false)
    (one : s.nr 6 = 1) (zero : s.nr 10 = 0) (count : s.nr 32 = (oddVertexOrder G edges).length)
    (oddBound : s.nr 31 + (oddVertexOrder G edges).length ≤ s.nr 34)
    (mateBound : s.nr 33 + (oddVertexOrder G edges).length ≤ s.nr 34)
    (oddMap : ∀ i : Fin (oddVertexOrder G edges).length,
      s.nm (s.nr 31 + i.val) = (oddVertexAt G edges i).val)
    (mateMap : ∀ i : Fin (oddVertexOrder G edges).length, s.nm (s.nr 33 + i.val) = (mate i).val)
    (least : SupplyChainTheory.IsMinMatchingOn
      (fun i j => distance G (oddVertexAt G edges i) (oddVertexAt G edges j))
      Finset.univ (mateEdgeSet Finset.univ mate)) :
    let k := (oddVertexOrder G edges).length
    ∃ t pairs, BlockRuns emitMatePairsBlock (16 * k + 4) s t ∧ t.halted = false ∧
      t.nr 34 = s.nr 34 ∧ t.nr 35 = pairs.length ∧ ExpansionPairArray t.nm (s.nr 34) pairs ∧
      MinimumMatching G edges pairs ∧ (∀ a < s.nr 34, t.nm a = s.nm a) ∧ t.rm = s.rm := by
  obtain ⟨t, pairs, run, ready, base, length, encoded, minimum, below, real, _, _⟩ :=
    emitMatePairsBlock_withFootprint entry running one zero count (.inl oddBound) (.inl mateBound)
      oddMap mateMap least
  exact ⟨t, pairs, run, ready, base, length, encoded, minimum, below, real⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatePairArray

/-! runtime/RuralOutputBlock.lean -/
section RppSource_RuralOutputBlock
namespace VehicleRoutingSurvey.Routing

theorem BlockRuns.halt {code : List ArithmeticInstruction} {steps : ℕ}
    {s t : ArithmeticState} (run : BlockRuns code steps s t) (ready : t.halted = false) :
    (arithmeticStep (code ++ [.halt]))^[steps + 1] s = {t with halted := true} := by
  rw [Nat.add_comm steps 1, Function.iterate_add_apply, Function.iterate_one,
    arithmeticIterate_prefix _ _ _ _ run.inside, run.run]
  have instruction : (code ++ [.halt])[t.pc]? = some .halt := by
    rw [List.getElem?_append_right (by rw [run.exit]), run.exit]
    simp
  simp [arithmeticStep, ready, instruction]

def emitEmptyRuralRunBlock : List ArithmeticInstruction :=
  [.natConst 0 0, .natConst 6 1, .natStore 0 6, .natStore 6 0]

theorem emitEmptyRuralRunBlock_correct {I : Service} {s : ArithmeticState}
    (rural : Rural I) (empty : I.links = ∅) (entry : s.pc = 0) (running : s.halted = false) :
    ∃ (t : ArithmeticState) (u : Fin I.graph.n), BlockRuns emitEmptyRuralRunBlock 4 s t ∧ t.halted = false ∧
      arithmeticOutput t = tourCode I.graph u [] ∧ RuralRun I u [] := by
  let t := (arithmeticStep emitEmptyRuralRunBlock)^[4] s
  let u : Fin I.graph.n := ⟨0, rural.1.1⟩
  have ready : t.halted = false := by
    simp [t, emitEmptyRuralRunBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = emitEmptyRuralRunBlock.length := by
    simp [t, emitEmptyRuralRunBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, u, BlockRuns.of_running_exit rfl ready exit, ready, ?_, by simp [RuralRun, empty]⟩
  simp [t, emitEmptyRuralRunBlock, arithmeticStep, arithmeticOutput, tourCode, u, entry, running,
    Function.iterate_succ_apply']

/-- Complete a nonempty service run from its augmented occurrence array.
The emitted walk satisfies the actual mission relation, and this stage
costs at most 324 times the mission's size expression. -/
theorem emitNonemptyRuralRunBlock_correct {I : Service} {s : ArithmeticState}
    {base : List (Fin I.graph.q)} {tree matching : List (Fin I.graph.n × Fin I.graph.n)}
    {treePaths matchingPaths : List (List (Traversal I.graph))} {root : Fin I.graph.n}
    (rural : Rural I) (nonempty : I.links ≠ ∅) (baseUnique : base.Nodup)
    (baseCoverage : base.toFinset = I.links) (treeOptimal : MinimumComponentTree I tree)
    (treeExpands : Expands I.graph tree treePaths)
    (treeBound : ∀ walk ∈ treePaths, walk.length < I.graph.n)
    (matchingOptimal : MinimumMatching I.graph (base ++ treePaths.flatten.map Prod.fst) matching)
    (matchingExpands : Expands I.graph matching matchingPaths)
    (matchingBound : ∀ walk ∈ matchingPaths, walk.length < I.graph.n)
    (entry : s.pc = 0) (running : s.halted = false)
    (vertices : s.nr 29 = I.graph.n) (vertex : s.nr 28 = root.val)
    (rawBound : 2 + 3 * I.graph.q ≤ s.nr 30) :
    let edges := base ++ treePaths.flatten.map Prod.fst ++ matchingPaths.flatten.map Prod.fst
    s.nr 18 = edges.length → s.nr 23 + edges.length ≤ s.nr 30 →
    EulerOccurrenceInput edges (s.nr 23) s.nm → EdgeSupport I.graph edges root →
      ∃ (t : ArithmeticState) (ts : List (Traversal I.graph)) (steps : ℕ),
        BlockRuns eulerFromOccurrencesBlock steps s t ∧
        t.halted = false ∧ RuralRun I root ts ∧ arithmeticOutput t = tourCode I.graph root ts ∧
        steps ≤ 324 * (I.graph.n ^ 3 + I.graph.q) := by
  dsimp only
  let edges := base ++ treePaths.flatten.map Prod.fst ++ matchingPaths.flatten.map Prod.fst
  intro count inputBound encoded supported
  have treeEnds (p : Fin I.graph.n × Fin I.graph.n) (inTree : p ∈ tree) :
      p.1 ∈ requiredVertices I ∧ p.2 ∈ requiredVertices I :=
    let reaches := treeOptimal.1.2.1 p inTree
    ⟨reaches.1, reaches.2.1⟩
  have oddRequired := oddVertices_subset_required baseCoverage treeExpands treeEnds
  have matchingStarts (p : Fin I.graph.n × Fin I.graph.n) (inMatching : p ∈ matching) :
      p.1 ∈ requiredVertices I := by
    have chosen : s(p.1, p.2) ∈ matchingEdges I.graph matching :=
      List.mem_toFinset.mpr (List.mem_map_of_mem inMatching)
    exact oddRequired ((matchingOptimal.2.1.1 _ chosen).2 _ (Sym2.mem_mk_left _ _))
  have connected : EdgeSupportConnected I.graph edges :=
    expandedSupport_connected baseCoverage treeOptimal.1 treeExpands matchingExpands matchingStarts
  have perfect : PerfectMatching I.graph (base ++ treePaths.flatten.map Prod.fst) matching :=
    ⟨matchingOptimal.1, matchingOptimal.2.1⟩
  have even : ∀ v, degree I.graph edges v % 2 = 0 :=
    degree_matching_augmentation_even perfect matchingExpands
  obtain ⟨t, ts, run, ready, closed, uses, output⟩ :=
    eulerFromOccurrencesBlock_correct entry running count vertices vertex inputBound rawBound
      encoded rural.2.2.1 even connected supported
  have valid : RuralRun I root ts := by
    rw [RuralRun, if_neg nonempty]
    exact ⟨base, tree, matching, treePaths, matchingPaths, baseUnique, baseCoverage, treeOptimal,
      treeExpands, matchingOptimal, matchingExpands, closed, uses⟩
  have size := expanded_traversal_count_le baseUnique treeOptimal.1 treeExpands treeBound
    matchingOptimal matchingExpands matchingBound uses
  have eq : ts.length = edges.length := by simpa only [List.length_map] using uses.length_eq
  have square : I.graph.n ^ 2 ≤ I.graph.n ^ 3 := by
    calc
      _ = I.graph.n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ I.graph.n ^ 2 * I.graph.n := Nat.mul_le_mul_left _ rural.1.1
      _ = _ := (pow_succ _ 2).symm
  have vertexBound : I.graph.n ≤ I.graph.n ^ 3 := by
    have sq : I.graph.n ≤ I.graph.n ^ 2 := by
      simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left I.graph.n rural.1.1
    exact sq.trans square
  have positive : 0 < I.graph.n ^ 3 := pow_pos rural.1.1 _
  refine ⟨t, ts, 130 * edges.length + 5 * I.graph.n + 59, run, ready, valid, output, ?_⟩
  omega


end VehicleRoutingSurvey.Routing
end RppSource_RuralOutputBlock

/-! runtime/MatchingToRuralRun.lean -/
section RppSource_MatchingToRuralRun
namespace VehicleRoutingSurvey.Routing

def matchingToRuralRunBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock expandPairListBlock configureEulerNonemptyOccurrencesBlock)
    eulerFromOccurrencesBlock

/-- Complete the running machine state once minimum matching pairs have
been written. The actual path, occurrence and Euler blocks produce the
mission's encoded rural run, and a final halt preserves that output. -/
theorem matchingToRuralRunBlock_correct {I : Service} {rowOffsets distances : ℕ}
    {table : DirectLinkTable I.graph} {s : ArithmeticState}
    {tree matching : List (Fin I.graph.n × Fin I.graph.n)}
    {treePaths : List (List (Traversal I.graph))}
    (rural : Rural I) (nonempty : I.links ≠ ∅)
    (treeOptimal : MinimumComponentTree I tree) (treeExpands : Expands I.graph tree treePaths)
    (treeBound : ∀ path ∈ treePaths, path.length < I.graph.n)
    (minimum : MinimumMatching I.graph (requiredLinkList I ++ treePaths.flatten.map Prod.fst) matching)
    (frame : FloydFrame I.graph.n rowOffsets distances s)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives I.graph (tableChooses table))
    (rows : ∀ target, TightStoredRow target table (s.nr 26) s.nm)
    (count : s.nr 35 = matching.length) (zero : s.nr 28 = 0)
    (encodedPairs : ExpansionPairArray s.nm (s.nr 34) matching)
    (encodedRaw : ∀ a < 2 + 3 * I.graph.q, s.nm a = (ruralNatInput I)[a]?.getD 0)
    (pairsBelow : s.nr 34 + 2 * matching.length ≤ s.nr 29)
    (rowsBelow : rowOffsets + I.graph.n ≤ s.nr 29)
    (pointersBelow : s.nr 26 + I.graph.n * I.graph.n ≤ s.nr 29)
    (rawBelow : 2 + 3 * I.graph.q ≤ s.nr 29)
    (entry : s.pc = 0) (running : s.halted = false) :
    let prior := requiredLinkList I ++ treePaths.flatten.map Prod.fst
    s.nr 29 = s.nr 33 + prior.length → OccurrenceArray s.nm (s.nr 33) prior →
      ∃ (t : ArithmeticState) (root : Fin I.graph.n) (ts : List (Traversal I.graph)) (steps : ℕ),
        BlockRuns matchingToRuralRunBlock steps s t ∧
        t.halted = false ∧ RuralRun I root ts ∧ arithmeticOutput t = tourCode I.graph root ts ∧
        steps + 1 ≤ 400 * (I.graph.n ^ 3 + I.graph.q) ∧
        (arithmeticStep (matchingToRuralRunBlock ++ [.halt]))^[steps + 1] s = {t with halted := true} := by
  intro prior initialCursor initialArray
  obtain ⟨p, pathCost, matchingPaths, pathRun, pathBudget, pReady, matchingExpands, matchingBound,
      cursor, occurrence, fixed, _, lower⟩ :=
    expandPairListBlock_correct matching prior rural.1 rural.2.1 frame sound representative rows
      count zero initialCursor encodedPairs initialArray pairsBelow rowsBelow pointersBelow rawBelow
      (fun e => (ruralInputs_preserveLinkEndpoints encodedRaw e).1)
      (fun e => (ruralInputs_preserveLinkEndpoints encodedRaw e).2) entry running
  obtain ⟨baseUnique, baseCoverage⟩ := requiredLinkList_spec I
  let edges := prior ++ matchingPaths.flatten.map Prod.fst
  have basePresent : requiredLinkList I ≠ [] := by
    intro empty
    apply nonempty
    simpa [empty] using baseCoverage.symm
  have occurrencesPresent : edges ≠ [] :=
    List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_left_ne_nil basePresent _) _
  obtain ⟨edge, other, head⟩ := List.exists_cons_of_ne_nil occurrencesPresent
  let eulerSetup := {p with pc := 0}
  have finalCursor : p.nr 29 = p.nr 33 + edges.length := by
    rw [fixed 33 (by decide)]
    exact cursor
  have configuredCursor : p.nr 29 = p.nr 33 + (edge :: other).length := by
    rw [← head]
    exact finalCursor
  have encoded : OccurrenceArray p.nm (p.nr 33) (edge :: other) := by
    rw [← head, fixed 33 (by decide)]
    exact occurrence
  have grows : s.nr 29 ≤ p.nr 29 := by
    rw [initialCursor, cursor]
    simp
  have raw (a : ℕ) (valid : a < 2 + 3 * I.graph.q) :
      p.nm a = (ruralNatInput I)[a]?.getD 0 :=
    (lower a (valid.trans_le rawBelow)).trans (encodedRaw a valid)
  obtain ⟨configured, root, layout, configuredReady, support, lengthReg, vertexCount, entryVertex,
      buffer, linkBound, contents⟩ :=
    configureEulerNonemptyOccurrencesBlock_correct (s := eulerSetup) rfl pReady
      ((fixed 6 (by decide)).trans frame.one) ((fixed 28 (by decide)).trans zero)
      ((fixed 5 (by decide)).trans frame.dimension) configuredCursor (rawBelow.trans grows)
      encoded (fun e => (ruralInputs_preserveLinkEndpoints raw e).1)
      (fun e => (ruralInputs_preserveLinkEndpoints raw e).2)
  let laidOut := relocateState expandPairListBlock.length configured
  let eulerEntry := {laidOut with pc := 0}
  have currentLength : eulerEntry.nr 18 = edges.length := by
    rw [head]
    exact lengthReg
  have currentBuffer : eulerEntry.nr 23 + edges.length ≤ eulerEntry.nr 30 := by
    rw [head]
    exact buffer
  have currentEncoding : EulerOccurrenceInput edges (eulerEntry.nr 23) eulerEntry.nm := by
    rw [head]
    exact contents
  have currentSupport : EdgeSupport I.graph edges root := by rwa [head]
  obtain ⟨tourState, ts, eulerTime, euler, ready, valid, output, tourBound⟩ :=
    emitNonemptyRuralRunBlock_correct (s := eulerEntry) rural nonempty baseUnique baseCoverage
      treeOptimal treeExpands treeBound minimum matchingExpands matchingBound rfl configuredReady
      vertexCount entryVertex linkBound currentLength currentBuffer currentEncoding currentSupport
  let steps := pathCost + 12 + eulerTime
  let t := relocateState (appendBlock expandPairListBlock configureEulerNonemptyOccurrencesBlock).length
    tourState
  have executes : BlockRuns matchingToRuralRunBlock steps s t := (pathRun.append layout).append euler
  have square : I.graph.n ^ 2 ≤ I.graph.n ^ 3 := by
    calc
      _ = I.graph.n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ I.graph.n ^ 2 * I.graph.n := Nat.mul_le_mul_left _ rural.1.1
      _ = _ := (pow_succ _ 2).symm
  have cube : 0 < I.graph.n ^ 3 := pow_pos rural.1.1 _
  have pathCap : pathCost ≤ 37 * I.graph.n ^ 3 := by
    have lifted := Nat.mul_le_mul_right (25 * I.graph.n + 9) (minimumMatching_length_le_square minimum)
    have expands : I.graph.n ^ 2 * (25 * I.graph.n + 9) =
        25 * I.graph.n ^ 3 + 9 * I.graph.n ^ 2 := by ring
    rw [expands] at lifted
    omega
  have total : steps + 1 ≤ 400 * (I.graph.n ^ 3 + I.graph.q) := by dsimp [steps]; omega
  exact ⟨t, root, ts, steps, executes, ready, valid, output, total, executes.halt ready⟩

end VehicleRoutingSurvey.Routing
end RppSource_MatchingToRuralRun

/-! runtime/CompactMateToRuralRun.lean -/
section RppSource_CompactMateToRuralRun
namespace VehicleRoutingSurvey.Routing

def pointAtReservedMatePairArrayBlock : List ArithmeticInstruction :=
  [.natConst 6 1, .natConst 10 0, .natAdd 34 106 10]

private theorem pointAtReservedMatePairArrayBlock_correct (s : ArithmeticState)
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns pointAtReservedMatePairArrayBlock 3 s t ∧ t.halted = false ∧
      t.nr 6 = 1 ∧ t.nr 10 = 0 ∧ t.nr 34 = s.nr 106 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r, r ≠ 6 → r ≠ 10 → r ≠ 34 → t.nr r = s.nr r := by
  let t := (arithmeticStep pointAtReservedMatePairArrayBlock)^[3] s
  have ready : t.halted = false := by
    simp [t, pointAtReservedMatePairArrayBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = pointAtReservedMatePairArrayBlock.length := by
    simp [t, pointAtReservedMatePairArrayBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals
    first
    | intro r one zero output
      simp [t, pointAtReservedMatePairArrayBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply', Function.update_of_ne one, Function.update_of_ne zero,
        Function.update_of_ne output]
    | simp [t, pointAtReservedMatePairArrayBlock, arithmeticStep, entry, running,
        Function.iterate_succ_apply']

private theorem naturalDestinations_emitMatePairsBlock :
    ∀ ins ∈ emitMatePairsBlock, naturalDestination ins < 100 := by
  have checked : emitMatePairsBlock.all (fun ins => decide (naturalDestination ins < 100)) = true := by
    decide
  exact fun ins occurs => of_decide_eq_true (List.all_eq_true.mp checked ins occurs)

def compactMateToRuralRunBlock : List ArithmeticInstruction :=
  appendBlock (appendBlock (appendBlock pointAtReservedMatePairArrayBlock emitMatePairsBlock)
    restoreOccurrenceRegistersBlock) matchingToRuralRunBlock

/-- Lift the compact optimal mate table to routing pairs, preserve the
existing occurrences, and finish the exact rural-postman run. -/
theorem compactMateToRuralRunBlock_correct {I : Service} {rows matrix : ℕ}
    {table : DirectLinkTable I.graph} {checkpoint s : ArithmeticState}
    {tree : List (Fin I.graph.n × Fin I.graph.n)} {treePaths : List (List (Traversal I.graph))}
    (rural : Rural I) (required : I.links.Nonempty)
    (treeOptimal : MinimumComponentTree I tree) (treeExpands : Expands I.graph tree treePaths)
    (treeBound : ∀ path ∈ treePaths, path.length < I.graph.n)
    (frame : FloydFrame I.graph.n rows matrix checkpoint)
    (sound : DirectLinkTableSound table)
    (representative : DirectLinkRepresentatives I.graph (tableChooses table))
    (pointers : ∀ target, TightStoredRow target table (checkpoint.nr 26) checkpoint.nm)
    (raw : ∀ a < 2 + 3 * I.graph.q, checkpoint.nm a = (ruralNatInput I)[a]?.getD 0)
    (rawBound : 2 + 3 * I.graph.q ≤ checkpoint.nr 106)
    (rowBound : rows + I.graph.n ≤ checkpoint.nr 106)
    (pointerBound : checkpoint.nr 26 + I.graph.n * I.graph.n ≤ checkpoint.nr 106)
    (reserve : checkpoint.nr 33 = checkpoint.nr 106 + 2 * I.graph.n)
    (reservation : s.nr 106 = checkpoint.nr 106)
    (saved : SavedOccurrenceRegisters checkpoint s)
    (retained : ∀ address < checkpoint.nr 29, s.nm address = checkpoint.nm address)
    (oddAfter : checkpoint.nr 29 ≤ s.nr 31) (mateAfter : checkpoint.nr 29 ≤ s.nr 33)
    (entry : s.pc = 0) (running : s.halted = false) :
    let prior := requiredLinkList I ++ treePaths.flatten.map Prod.fst
    let k := (oddVertexOrder I.graph prior).length
    ∀ mate : Fin k → Fin k,
      checkpoint.nr 29 = checkpoint.nr 33 + prior.length →
      OccurrenceArray checkpoint.nm (checkpoint.nr 33) prior →
      s.nr 32 = k →
      (∀ i : Fin k, s.nm (s.nr 31 + i.val) = (oddVertexAt I.graph prior i).val) →
      (∀ i : Fin k, s.nm (s.nr 33 + i.val) = (mate i).val) →
      SupplyChainTheory.IsMinMatchingOn
        (fun i j => distance I.graph (oddVertexAt I.graph prior i) (oddVertexAt I.graph prior j))
        Finset.univ (mateEdgeSet Finset.univ mate) →
      ∃ (t : ArithmeticState) (root : Fin I.graph.n) (ts : List (Traversal I.graph)) (steps : ℕ),
        BlockRuns compactMateToRuralRunBlock steps s t ∧ t.halted = false ∧
        RuralRun I root ts ∧ arithmeticOutput t = tourCode I.graph root ts ∧
        steps + 1 ≤ 450 * (I.graph.n ^ 3 + I.graph.q) ∧
        (arithmeticStep (compactMateToRuralRunBlock ++ [.halt]))^[steps + 1] s = {t with halted := true} := by
  intro prior k mate oldCursor occurrences count oddMap mateMap optimal
  have nPos : 0 < I.graph.n := rural.1.1
  have kBound : k ≤ I.graph.n := by simpa using (oddVertexOrder_nodup I.graph prior).length_le_card
  obtain ⟨a, configures, aReady, one, zero, output, natural, _, fixed⟩ :=
    pointAtReservedMatePairArrayBlock_correct s entry running
  let decodeEntry := {a with pc := 0}
  have pairBase : a.nr 34 = checkpoint.nr 106 := output.trans reservation
  have oldEnd : checkpoint.nr 106 + 2 * k ≤ checkpoint.nr 29 := by
    rw [oldCursor, reserve]
    omega
  have oddDisjoint : a.nr 34 + 2 * k ≤ a.nr 31 := by
    rw [pairBase, fixed 31 (by decide) (by decide) (by decide)]
    exact oldEnd.trans oddAfter
  have mateDisjoint : a.nr 34 + 2 * k ≤ a.nr 33 := by
    rw [pairBase, fixed 33 (by decide) (by decide) (by decide)]
    exact oldEnd.trans mateAfter
  have od (i : Fin k) : decodeEntry.nm (decodeEntry.nr 31 + i.val) =
      (oddVertexAt I.graph prior i).val := by
    change a.nm (a.nr 31 + i.val) = _
    rw [natural, fixed 31 (by decide) (by decide) (by decide)]
    exact oddMap i
  have ma (i : Fin k) : decodeEntry.nm (decodeEntry.nr 33 + i.val) = (mate i).val := by
    change a.nm (a.nr 33 + i.val) = _
    rw [natural, fixed 33 (by decide) (by decide) (by decide)]
    exact mateMap i
  obtain ⟨d, pairs, decodes, dReady, dBase, dCount, dPairs, minimum, _, _, footprint, lengthBound⟩ :=
    emitMatePairsBlock_withFootprint (s := decodeEntry) rfl aReady one zero
      ((fixed 32 (by decide) (by decide) (by decide)).trans count)
      (.inr oddDisjoint) (.inr mateDisjoint) od ma optimal
  let decoded := relocateState pointAtReservedMatePairArrayBlock.length d
  let restoreEntry := {decoded with pc := 0}
  have savedForRestore : SavedOccurrenceRegisters checkpoint restoreEntry := by
    apply saved.preserved
    intro r high
    change d.nr r = s.nr r
    calc
      _ = a.nr r := by
        rw [← decodes.run]
        exact arithmeticRun_keeps_high_register (fun ins occurs =>
          (naturalDestinations_emitMatePairsBlock ins occurs).trans_le high) decodeEntry _
      _ = _ := fixed r (by omega) (by omega) (by omega)
  obtain ⟨r, replaces, rReady, rNatural, _, rowAt, matrixAt, sizeAt, nextAt, endAt, baseAt,
      rOne, rZero, pairsAt, pairCount⟩ :=
    restoreOccurrenceRegistersBlock_correct (s := restoreEntry) rfl dReady savedForRestore
  let restored := relocateState (appendBlock pointAtReservedMatePairArrayBlock emitMatePairsBlock).length r
  let tailEntry := {restored with pc := 0}
  have exactPairBase : r.nr 34 = checkpoint.nr 106 := pairsAt.trans (dBase.trans pairBase)
  have belowPair (address : ℕ) (below : address < checkpoint.nr 106) :
      r.nm address = checkpoint.nm address := by
    have beforePairs : address < decodeEntry.nr 34 := by change address < a.nr 34; rwa [pairBase]
    have beforeOccurrences : address < checkpoint.nr 29 := by
      rw [oldCursor, reserve]
      omega
    exact (congrFun rNatural address).trans ((footprint address (.inl beforePairs)).trans
      ((congrFun natural address).trans (retained address beforeOccurrences)))
  have copiedOccurrences : OccurrenceArray r.nm (r.nr 33) prior := by
    rw [baseAt]
    intro i hi
    have beforeWrite : checkpoint.nr 33 + i < checkpoint.nr 29 := by rw [oldCursor]; omega
    have afterPairs : decodeEntry.nr 34 + 2 * pairs.length ≤ checkpoint.nr 33 + i := by
      change a.nr 34 + _ ≤ _
      rw [pairBase, reserve]
      omega
    let address := checkpoint.nr 33 + i
    exact (congrFun rNatural address).trans ((footprint address (.inr afterPairs)).trans
      ((congrFun natural address).trans ((retained address beforeWrite).trans (occurrences i hi))))
  have restoredFrame : FloydFrame I.graph.n rows matrix tailEntry := by
    refine ⟨rowAt.trans frame.tableBase, matrixAt.trans frame.matrixBase, sizeAt.trans frame.dimension,
      rOne, ?_⟩
    intro i hi
    exact (belowPair _ ((Nat.add_lt_add_left hi _).trans_le rowBound)).trans (frame.rows i hi)
  have copiedPointers (target : Fin I.graph.n) :
      TightStoredRow target table (tailEntry.nr 26) tailEntry.nm := by
    change TightStoredRow target table (r.nr 26) r.nm
    rw [nextAt]
    exact (pointers target).preservedBelow pointerBound belowPair
  have copiedRaw (address : ℕ) (inInput : address < 2 + 3 * I.graph.q) :
      tailEntry.nm address = (ruralNatInput I)[address]?.getD 0 :=
    (belowPair address (inInput.trans_le rawBound)).trans (raw address inInput)
  have copiedPairs : ExpansionPairArray tailEntry.nm (tailEntry.nr 34) pairs := by
    change ExpansionPairArray r.nm (r.nr 34) pairs
    rw [rNatural, pairsAt]
    change ExpansionPairArray d.nm (d.nr 34) pairs
    rw [dBase]
    exact dPairs
  have pairsBelow : tailEntry.nr 34 + 2 * pairs.length ≤ tailEntry.nr 29 := by
    change r.nr 34 + _ ≤ r.nr 29
    rw [exactPairBase, endAt]
    omega
  have baseLe : checkpoint.nr 106 ≤ tailEntry.nr 29 := by
    change _ ≤ r.nr 29
    rw [endAt, oldCursor, reserve]
    omega
  have nextBelow : tailEntry.nr 26 + I.graph.n * I.graph.n ≤ tailEntry.nr 29 := by
    change r.nr 26 + _ ≤ _
    rw [nextAt]
    exact pointerBound.trans baseLe
  have tailCursor : tailEntry.nr 29 = tailEntry.nr 33 + prior.length := by
    change r.nr 29 = r.nr 33 + prior.length
    rwa [baseAt, endAt]
  obtain ⟨t, root, ts, tailSteps, outputRun, ready, valid, result, budget, _⟩ :=
    matchingToRuralRunBlock_correct rural required.ne_empty treeOptimal treeExpands treeBound minimum
      restoredFrame sound representative copiedPointers (pairCount.trans dCount) rZero copiedPairs
      copiedRaw pairsBelow (rowBound.trans baseLe) nextBelow (rawBound.trans baseLe)
      rfl rReady tailCursor copiedOccurrences
  let final := relocateState
    (appendBlock (appendBlock pointAtReservedMatePairArrayBlock emitMatePairsBlock)
      restoreOccurrenceRegistersBlock).length t
  have all := ((configures.append decodes).append replaces).append outputRun
  have square : I.graph.n ^ 2 ≤ I.graph.n ^ 3 := by
    calc
      _ = I.graph.n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ I.graph.n ^ 2 * I.graph.n := Nat.mul_le_mul_left _ nPos
      _ = _ := (pow_succ _ 2).symm
  have vertexBound : I.graph.n ≤ I.graph.n ^ 3 :=
    (by simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left I.graph.n nPos :
      I.graph.n ≤ I.graph.n ^ 2).trans square
  have cube : 0 < I.graph.n ^ 3 := pow_pos nPos _
  have time : 3 + (16 * k + 4) + 8 + tailSteps + 1 ≤ 450 * (I.graph.n ^ 3 + I.graph.q) := by omega
  exact ⟨final, root, ts, _, all, ready, valid, result, time, all.halt ready⟩

end VehicleRoutingSurvey.Routing
end RppSource_CompactMateToRuralRun

/-! runtime/RequiredServiceDispatch.lean -/
section RppSource_RequiredServiceDispatch
set_option linter.unusedSimpArgs false

namespace VehicleRoutingSurvey.Routing

private def requiredServiceHeader : List ArithmeticInstruction :=
  [.natConst 60 1, .natLoad 61 60, .natConst 63 4, .natConst 64 0, .natConst 65 3]

private def readRequiredServiceBit : List ArithmeticInstruction :=
  [.natLoad 66 63, .natBranch 66 67 2 3, .jump 4, .natAdd 64 60 67, .natAdd 63 63 65]

/-- Read the required bits once, remembering whether any bit is set. -/
def scanRequiredServiceBlock : List ArithmeticInstruction :=
  appendBlock requiredServiceHeader (countedLoopFromZero 60 62 61 readRequiredServiceBit)

private def NoRequiredInPrefix (I : Service) (i : ℕ) : Prop :=
  ∀ e : Fin I.graph.q, e.val < i → e ∉ I.links

private theorem noRequiredInPrefix_succ (I : Service) (i : ℕ) (bound : i < I.graph.q) :
    NoRequiredInPrefix I (i + 1) ↔ NoRequiredInPrefix I i ∧ (⟨i, bound⟩ : Fin I.graph.q) ∉ I.links := by
  constructor
  · exact fun absent => ⟨fun e early => absent e (by omega), absent ⟨i, bound⟩ (by simp)⟩
  · rintro ⟨prior, current⟩ e early
    by_cases atIndex : e.val = i
    · have same : e = ⟨i, bound⟩ := Fin.ext atIndex
      rwa [same]
    · exact prior e (by omega)

open Classical in
private structure RequiredServiceScanState (I : Service) (i : ℕ) (s : ArithmeticState) : Prop where
  entry : s.pc = 0
  ready : s.halted = false
  index : s.nr 62 = i
  one : s.nr 60 = 1
  count : s.nr 61 = I.graph.q
  cursor : s.nr 63 = 4 + 3 * i
  flag : s.nr 64 = if NoRequiredInPrefix I i then 0 else 1
  stride : s.nr 65 = 3
  regs : ∀ r, r < 60 ∨ 66 < r → s.nr r = 0
  reals : s.rr = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).rr
  natural : s.nm = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).nm
  weights : s.rm = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).rm

private theorem readRequiredServiceBit_correct {I : Service} {i : ℕ} {s : ArithmeticState}
    (within : i < I.graph.q) (inv : RequiredServiceScanState I i s) :
    ∃ t, BlockRuns readRequiredServiceBit 4 s t ∧ t.halted = false ∧
      RequiredServiceScanState I (i + 1) {t with pc := 0, nr := Function.update t.nr 62 (t.nr 62 + t.nr 60)} := by
  classical
  let e : Fin I.graph.q := ⟨i, within⟩
  have zero := inv.regs 67 (Or.inr (by decide))
  have bit : s.nm (s.nr 63) = if e ∈ I.links then 1 else 0 := by
    rw [inv.natural, inv.cursor]
    change (ruralNatInput I)[4 + 3 * i]?.getD 0 = _
    rw [show 4 + 3 * i = 2 + 3 * e.val + 2 by dsimp [e]; omega,
      ruralNatInput_link_record I e (by decide : 2 < 3)]
    simp
  let t := (arithmeticStep readRequiredServiceBit)^[4] s
  have ready : t.halted = false := by
    by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, bit, zero, required,
        Function.iterate_succ_apply']
  have exit : t.pc = readRequiredServiceBit.length := by
    by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, bit, zero, required,
        Function.iterate_succ_apply']
  have unchanged : t.rr = s.rr ∧ t.nm = s.nm ∧ t.rm = s.rm := by
    by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, bit, zero, required,
        Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready,
    rfl, ready, ?_, ?_, ?_, ?_, ?_, ?_, ?_, unchanged.1.trans inv.reals,
    unchanged.2.1.trans inv.natural, unchanged.2.2.trans inv.weights⟩
  · by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, inv.index, inv.one,
        bit, zero, required, Function.iterate_succ_apply']
  · by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, inv.one, bit, zero, required,
        Function.iterate_succ_apply']
  · by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, inv.count, bit, zero, required,
        Function.iterate_succ_apply']
  · have cursor := inv.cursor
    by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, inv.stride, bit, zero,
        required, Function.iterate_succ_apply'] <;> omega
  · have extend : NoRequiredInPrefix I (i + 1) ↔ NoRequiredInPrefix I i ∧ e ∉ I.links :=
      noRequiredInPrefix_succ I i within
    rw [extend]
    by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, inv.one, inv.flag,
        bit, zero, required, Function.iterate_succ_apply']
  · by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, inv.stride, bit, zero, required,
        Function.iterate_succ_apply']
  · intro r outside
    have different (j : ℕ) (low : 60 ≤ j) (high : j ≤ 66) : r ≠ j := by omega
    by_cases required : e ∈ I.links <;>
      simp [t, readRequiredServiceBit, arithmeticStep, inv.entry, inv.ready, bit, zero, required,
        Function.iterate_succ_apply', Function.update_of_ne (different 62 (by decide) (by decide)),
        Function.update_of_ne (different 63 (by decide) (by decide)),
        Function.update_of_ne (different 64 (by decide) (by decide)),
        Function.update_of_ne (different 66 (by decide) (by decide)), inv.regs r outside]

structure RequiredServiceInput (I : Service) (s : ArithmeticState) : Prop where
  ready : s.halted = false
  one : s.nr 60 = 1
  flag : s.nr 64 = if I.links = ∅ then 0 else 1
  regs : ∀ r, r < 60 ∨ 66 < r → s.nr r = 0
  reals : s.rr = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).rr
  natural : s.nm = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).nm
  weights : s.rm = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).rm

theorem scanRequiredServiceBlock_correct (I : Service) :
    ∃ t, BlockRuns scanRequiredServiceBlock (7 * I.graph.q + 7)
      (arithmeticInput (ruralNatInput I) (ruralRealInput I)) t ∧ RequiredServiceInput I t := by
  classical
  let s := arithmeticInput (ruralNatInput I) (ruralRealInput I)
  let header := (arithmeticStep requiredServiceHeader)^[5] s
  have ready : header.halted = false := by
    simp [header, s, arithmeticInput, requiredServiceHeader, arithmeticStep, Function.iterate_succ_apply']
  have exit : header.pc = requiredServiceHeader.length := by
    simp [header, s, arithmeticInput, requiredServiceHeader, arithmeticStep, Function.iterate_succ_apply']
  have headerRun : BlockRuns requiredServiceHeader 5 s header := BlockRuns.of_running_exit rfl ready exit
  let scan := {header with pc := 0}
  let inv := RequiredServiceScanState I
  have initial : inv 0 {scan with pc := 0, nr := Function.update scan.nr 62 0} := by
    have noEarlier : NoRequiredInPrefix I 0 := fun e tooEarly => (Nat.not_lt_zero _ tooEarly).elim
    refine ⟨rfl, ready, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals try simp [scan, header, s, arithmeticInput, requiredServiceHeader, arithmeticStep,
      Function.iterate_succ_apply', ruralNatInput, noEarlier]
    intro r outside
    have different (j : ℕ) (low : 60 ≤ j) (high : j ≤ 66) : r ≠ j := by omega
    simp [scan, header, s, arithmeticInput, requiredServiceHeader, arithmeticStep,
      Function.iterate_succ_apply', Function.update_of_ne (different 60 (by decide) (by decide)),
      Function.update_of_ne (different 61 (by decide) (by decide)),
      Function.update_of_ne (different 62 (by decide) (by decide)),
      Function.update_of_ne (different 63 (by decide) (by decide)),
      Function.update_of_ne (different 64 (by decide) (by decide)),
      Function.update_of_ne (different 65 (by decide) (by decide))]
  have control (i : ℕ) (m : ArithmeticState) (h : inv i m) :
      m.pc = 0 ∧ m.halted = false ∧ m.nr 62 = i ∧ m.nr 61 = I.graph.q :=
    ⟨h.entry, h.ready, h.index, h.count⟩
  obtain ⟨last, final, run⟩ := countedLoopFromZero_correct 60 62 61 I.graph.q 4
    readRequiredServiceBit inv (s := scan) rfl ready initial control (fun _ hi _ h => readRequiredServiceBit_correct hi h)
  have empty : NoRequiredInPrefix I I.graph.q ↔ I.links = ∅ := by
    constructor
    · intro absent
      exact Finset.eq_empty_iff_forall_notMem.mpr (fun e => absent e e.isLt)
    · intro empty e _
      simp [empty]
  have completed := headerRun.append run
  have steps : 5 + (1 + (I.graph.q * (4 + 3) + 1)) = 7 * I.graph.q + 7 := by omega
  rw [steps] at completed
  have flag : last.nr 64 = if I.links = ∅ then 0 else 1 := by
    simpa only [empty] using final.flag
  exact ⟨_, completed, final.ready, final.one, flag, final.regs, final.reals, final.natural, final.weights⟩

private def resetRequiredServiceRegisters : List ArithmeticInstruction :=
  [.natConst 60 0, .natConst 61 0, .natConst 62 0, .natConst 63 0, .natConst 64 0,
    .natConst 65 0, .natConst 66 0]

private def resetServiceRegs (regs : ℕ → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update regs 60 0) 61 0) 62 0) 63 0) 64 0) 65 0) 66 0

private theorem resetRequiredServiceRegisters_correct {I : Service} {s : ArithmeticState}
    (state : RequiredServiceInput I s) (entry : s.pc = 0) :
    BlockRuns resetRequiredServiceRegisters 7 s
      {arithmeticInput (ruralNatInput I) (ruralRealInput I) with pc := 7} := by
  have cleared : resetServiceRegs s.nr = (arithmeticInput (ruralNatInput I) (ruralRealInput I)).nr := by
    funext r
    change resetServiceRegs s.nr r = 0
    by_cases outside : r < 60 ∨ 66 < r
    · have different (j : ℕ) (low : 60 ≤ j) (high : j ≤ 66) : r ≠ j := by omega
      simp [resetServiceRegs, Function.update_of_ne (different 60 (by decide) (by decide)),
        Function.update_of_ne (different 61 (by decide) (by decide)),
        Function.update_of_ne (different 62 (by decide) (by decide)),
        Function.update_of_ne (different 63 (by decide) (by decide)),
        Function.update_of_ne (different 64 (by decide) (by decide)),
        Function.update_of_ne (different 65 (by decide) (by decide)),
        Function.update_of_ne (different 66 (by decide) (by decide)), state.regs r outside]
    · have lower : 60 ≤ r := by omega
      have upper : r ≤ 66 := by omega
      interval_cases r <;> simp [resetServiceRegs]
  apply BlockRuns.of_running_exit _ rfl rfl
  have executes : (arithmeticStep resetRequiredServiceRegisters)^[7] s =
      {s with pc := 7, nr := resetServiceRegs s.nr} := by
    simp [resetRequiredServiceRegisters, resetServiceRegs, arithmeticStep, entry, state.ready,
      Function.iterate_succ_apply']
  rw [executes, cleared]
  simp [arithmeticInput, state.natural, state.reals, state.weights, state.ready]

/-- Check empty service before running the nonempty-service algorithm.
The nonempty branch receives the original input state. -/
def ruralInputDispatchBlock (nonempty : List ArithmeticInstruction) : List ArithmeticInstruction :=
  appendBlock scanRequiredServiceBlock
    (appendBlock (branchOnUnequal 64 60 emitEmptyRuralRunBlock)
      (branchOnUnequal 64 67 (appendBlock resetRequiredServiceRegisters nonempty)))

/-- Add input dispatch and a final halt to a nonempty-service implementation.
The scan and dispatch add at most 19 times the mission size expression. -/
theorem ruralInputDispatchBlock_correct {program : List ArithmeticInstruction} {C N : ℕ}
    (nonempty : ∀ I : Service, Rural I → I.links.Nonempty →
      ∃ (t : ArithmeticState) (u : Fin I.graph.n) (ts : List (Traversal I.graph)) (steps : ℕ),
        BlockRuns program steps (arithmeticInput (ruralNatInput I) (ruralRealInput I)) t ∧
        t.halted = false ∧ arithmeticOutput t = tourCode I.graph u ts ∧ RuralRun I u ts ∧
        (N ≤ I.graph.n + I.graph.q → steps ≤ C * (I.graph.n ^ 3 + I.graph.q))) :
    RuralImplementation (ruralInputDispatchBlock program ++ [.halt]) (C + 19) N := by
  classical
  refine ⟨by omega, ?_⟩
  intro I rural
  obtain ⟨scanned, scan, info⟩ := scanRequiredServiceBlock_correct I
  let start := {scanned with pc := 0}
  let emptyGate := branchOnUnequal 64 60 emitEmptyRuralRunBlock
  let nonemptyBody := appendBlock resetRequiredServiceRegisters program
  let nonemptyGate := branchOnUnequal 64 67 nonemptyBody
  have cube : 0 < I.graph.n ^ 3 := pow_pos rural.1.1 _
  have budget (steps : ℕ) (main : N ≤ I.graph.n + I.graph.q → steps ≤ C * (I.graph.n ^ 3 + I.graph.q))
      (large : N ≤ I.graph.n + I.graph.q) :
      7 * I.graph.q + 19 + steps ≤ (C + 19) * (I.graph.n ^ 3 + I.graph.q) := by
    have mainBound := main large
    rw [Nat.add_mul, Nat.mul_add 19]
    omega
  by_cases empty : I.links = ∅
  · have atZero : start.nr 64 = 0 := by simpa [start, empty] using info.flag
    have notOne : start.nr 64 ≠ start.nr 60 := by
      change start.nr 64 ≠ scanned.nr 60
      rw [atZero, info.one]
      decide
    obtain ⟨out, u, writes, ready, output, valid⟩ := emitEmptyRuralRunBlock_correct
      (s := start) rural empty rfl info.ready
    have emptyRun : BlockRuns emptyGate (2 + 4) start (relocateState 3 out) :=
      branchOnUnequal_take 64 60 emitEmptyRuralRunBlock rfl info.ready notOne writes
    let next := {relocateState 3 out with pc := 0}
    have noRequired : next.nr 64 = next.nr 67 := by
      change out.nr 64 = out.nr 67
      rw [← writes.run]
      have zero := info.regs 67 (Or.inr (by decide))
      simp [emitEmptyRuralRunBlock, arithmeticStep, start, info.ready, Function.iterate_succ_apply',
        show scanned.nr 64 = 0 from atZero, zero]
    have skip := branchOnUnequal_skip 64 67 nonemptyBody next rfl ready noRequired
    have run := scan.append (emptyRun.append skip)
    have halted := run.halt ready
    have bound (large : N ≤ I.graph.n + I.graph.q) :
        (7 * I.graph.q + 7) + ((2 + 4) + 2) + 1 ≤ (C + 19) * (I.graph.n ^ 3 + I.graph.q) := by
      have ample := budget 0 (fun _ => Nat.zero_le _) large
      omega
    refine ⟨(7 * I.graph.q + 7) + ((2 + 4) + 2) + 1, u, [], ?_⟩
    rw [show arithmeticRun (ruralInputDispatchBlock program ++ [.halt])
      ((7 * I.graph.q + 7) + ((2 + 4) + 2) + 1) (ruralNatInput I) (ruralRealInput I) = _ from halted]
    exact ⟨rfl, output, valid, bound⟩
  · have atOne : start.nr 64 = 1 := by simpa [start, empty] using info.flag
    have equal : start.nr 64 = start.nr 60 := atOne.trans info.one.symm
    have skip := branchOnUnequal_skip 64 60 emitEmptyRuralRunBlock start rfl info.ready equal
    let next := {{start with pc := emptyGate.length} with pc := 0}
    have active : next.nr 64 ≠ next.nr 67 := by
      change start.nr 64 ≠ scanned.nr 67
      rw [atOne, info.regs 67 (Or.inr (by decide))]
      decide
    have frame : RequiredServiceInput I next := ⟨info.ready, info.one, info.flag, info.regs,
      info.reals, info.natural, info.weights⟩
    have reset := resetRequiredServiceRegisters_correct frame rfl
    obtain ⟨out, u, ts, steps, works, ready, output, valid, time⟩ :=
      nonempty I rural (Finset.nonempty_iff_ne_empty.mpr empty)
    have execute : BlockRuns nonemptyGate (2 + (7 + steps)) next
        (relocateState 3 (relocateState resetRequiredServiceRegisters.length out)) :=
      branchOnUnequal_take 64 67 nonemptyBody rfl info.ready active (reset.append works)
    have run := scan.append (skip.append execute)
    have halted := run.halt ready
    have bound (large : N ≤ I.graph.n + I.graph.q) :
        (7 * I.graph.q + 7) + (2 + (2 + (7 + steps))) + 1 ≤
          (C + 19) * (I.graph.n ^ 3 + I.graph.q) := by
      have ample := budget steps time large
      omega
    refine ⟨(7 * I.graph.q + 7) + (2 + (2 + (7 + steps))) + 1, u, ts, ?_⟩
    rw [show arithmeticRun (ruralInputDispatchBlock program ++ [.halt])
      ((7 * I.graph.q + 7) + (2 + (2 + (7 + steps))) + 1) (ruralNatInput I) (ruralRealInput I) = _ from halted]
    exact ⟨rfl, output, valid, bound⟩

end VehicleRoutingSurvey.Routing
end RppSource_RequiredServiceDispatch

/-! runtime/RuralRAMComposition.lean -/
section RppSource_RuralRAMComposition
namespace VehicleRoutingSurvey.Routing

def nonemptyRuralRAMBlock (matching : List ArithmeticInstruction) : List ArithmeticInstruction :=
  appendBlock rawToConnectorOccurrencesBlock
    (appendBlock occurrenceToMatchingInputBlock (appendBlock matching compactMateToRuralRunBlock))

def ruralRAMProgram (matching : List ArithmeticInstruction) : List ArithmeticInstruction :=
  ruralInputDispatchBlock (nonemptyRuralRAMBlock matching) ++ [.halt]

/-- The exact nonempty-service program, composed with a compact minimum
matching program that obeys the memory layout and cubic time bound. -/
theorem nonemptyRuralRAMBlock_correct {matching : List ArithmeticInstruction} {C : ℕ}
    (solver : CompactMateBlockSpec matching C) (I : Service) (rural : Rural I)
    (required : I.links.Nonempty) :
    ∃ (t : ArithmeticState) (u : Fin I.graph.n) (ts : List (Traversal I.graph)) (steps : ℕ),
      BlockRuns (nonemptyRuralRAMBlock matching) steps
        (arithmeticInput (ruralNatInput I) (ruralRealInput I)) t ∧
      t.halted = false ∧ arithmeticOutput t = tourCode I.graph u ts ∧ RuralRun I u ts ∧
      steps ≤ (C * 2 + 1050) * (I.graph.n ^ 3 + I.graph.q) := by
  let n := I.graph.n
  let q := I.graph.q
  let rows := 2 + 3 * q
  let next := rows + n + n * n + n + n
  obtain ⟨b, table, tree, treePaths, rawSteps, rawRun, rawReady, rawBudget, treeOptimal, treeExpands,
    treeBound, rawFrame, nextAt, rawZero, nBeforeReserve, reserve, oldCursor, oldArray, sound,
    representative, oldRows, raw, routeDistances, _⟩ := rawToConnectorOccurrencesBlock_correct rural required
  let checkpoint := {b with pc := 0}
  let prior := requiredLinkList I ++ treePaths.flatten.map Prod.fst
  let k := (oddVertexOrder I.graph prior).length
  let compact := q + n * n
  let cost (u v : Fin k) : ℝ := distance I.graph (oddVertexAt I.graph prior u) (oddVertexAt I.graph prior v)
  have checkpointFrame : FloydFrame n rows q checkpoint := rawFrame.preserved (fun _ _ _ => rfl) rfl
  have rowBeforeReserve : rows + n ≤ checkpoint.nr 106 := by
    change rows + n ≤ b.nr 106
    change next + n ^ 2 ≤ b.nr 106 at nBeforeReserve
    dsimp [next] at nBeforeReserve
    omega
  have rawBeforeReserve : 2 + 3 * q ≤ checkpoint.nr 106 := by
    change rows ≤ _
    exact (Nat.le_add_right _ _).trans rowBeforeReserve
  have pointerBeforeReserve : checkpoint.nr 26 + n * n ≤ checkpoint.nr 106 := by
    change b.nr 26 + n * n ≤ b.nr 106
    rw [nextAt]
    simpa only [pow_two] using nBeforeReserve
  have reserveBeforeEnd : checkpoint.nr 106 ≤ checkpoint.nr 29 := by
    change b.nr 106 ≤ b.nr 29
    change b.nr 29 = b.nr 33 + prior.length at oldCursor
    rw [oldCursor, reserve]
    omega
  have keptPaths (target : Fin n) : TightStoredRow target table (checkpoint.nr 26) checkpoint.nm := by
    change TightStoredRow target table (b.nr 26) b.nm
    rw [nextAt]
    exact oldRows target
  have pathCosts (u v : Fin n) : checkpoint.rm (q + n * u.val + v.val) = distance I.graph u v := by
    change b.rm _ = _
    simpa [primPairOffset, Nat.add_assoc] using routeDistances (u, v)
  obtain ⟨c, compactSteps, compactRun, compactReady, compactBudget, saved, keptReservation, oddAt,
    compactRowsAt, compactAt, naturalSpaceAt, realSpaceAt, dimension, even, oddList, compactOffsets,
    compactCosts, keepsNatural, _⟩ := occurrenceToMatchingInputBlock_correct (s := checkpoint)
      rural.1.1 checkpointFrame rawZero
      oldCursor oldArray raw (rowBeforeReserve.trans reserveBeforeEnd) (rawBeforeReserve.trans reserveBeforeEnd)
      pathCosts rfl rawReady
  let matchingEntry := {c with pc := 0}
  have kBound : k ≤ n := by simpa using (oddVertexOrder_nodup I.graph prior).length_le_card
  have naturalSpace : matchingEntry.nr 21 + k ≤ matchingEntry.nr 63 := by
    change c.nr 21 + k ≤ c.nr 63
    rw [compactRowsAt, naturalSpaceAt]
    exact Nat.add_le_add_left kBound _
  have realSpace : matchingEntry.nr 20 + k ^ 2 ≤ matchingEntry.nr 64 := by
    change c.nr 20 + k ^ 2 ≤ c.nr 64
    rw [compactAt, realSpaceAt]
    simpa only [pow_two] using Nat.add_le_add_left (Nat.pow_le_pow_left kBound 2) compact
  have compactInput : CompactMateInput cost matchingEntry := by
    refine ⟨dimension, even, ?_, ?_, naturalSpace, realSpace,
      fun i j => distance_nonnegative rural.1 rural.2.1 _ _,
      fun i j => distance_symm rural.2.2.1 _ _, fun i => distance_self rural.2.1 _⟩
    · intro i hi
      change c.nm (c.nr 21 + i) = _
      rw [compactRowsAt]
      exact compactOffsets i hi
    · intro i j
      change c.rm (c.nr 20 + k * i.val + j.val) = _
      rw [compactAt]
      exact compactCosts i j
  obtain ⟨m, mate, matchSteps, matchRun, matchReady, matchBudget, oddStill, count, mateBase, mateInputs,
    minimum, keepsRegisters, matchKeeps, _⟩ := solver.run compactInput rfl compactReady
  let tail := {m with pc := 0}
  have oldBeforeNew : checkpoint.nr 29 ≤ matchingEntry.nr 63 := by
    change checkpoint.nr 29 ≤ c.nr 63
    rw [naturalSpaceAt]
    change checkpoint.nr 29 ≤ checkpoint.nr 29 + n + n + n
    omega
  have keepsPrior (a : ℕ) (early : a < checkpoint.nr 29) : tail.nm a = checkpoint.nm a :=
    (matchKeeps a (early.trans_le oldBeforeNew)).trans (keepsNatural a early)
  have nextSaved : SavedOccurrenceRegisters checkpoint tail :=
    saved.preserved (fun r high => keepsRegisters r high)
  have sameReservation : tail.nr 106 = checkpoint.nr 106 := (keepsRegisters 106 (by decide)).trans keptReservation
  have oddData (i : Fin k) : tail.nm (tail.nr 31 + i.val) = (oddVertexAt I.graph prior i).val := by
    change m.nm (m.nr 31 + i.val) = _
    rw [oddStill]
    have oddBefore : matchingEntry.nr 31 + i.val < matchingEntry.nr 63 := by
      change c.nr 31 + i.val < c.nr 63
      rw [oddAt, naturalSpaceAt]
      change checkpoint.nr 29 + n + i.val < checkpoint.nr 29 + n + n + n
      have inside := i.isLt.trans_le kBound
      omega
    exact (matchKeeps _ oddBefore).trans (by
      change c.nm (c.nr 31 + i.val) = _
      rw [oddAt]
      exact oddList i)
  have oddAfter : checkpoint.nr 29 ≤ tail.nr 31 := by
    change checkpoint.nr 29 ≤ m.nr 31
    rw [oddStill]
    change checkpoint.nr 29 ≤ c.nr 31
    rw [oddAt]
    exact Nat.le_add_right _ _
  have mateAfter : checkpoint.nr 29 ≤ tail.nr 33 := oldBeforeNew.trans mateBase
  obtain ⟨out, root, walk, tailSteps, tailRun, tailReady, valid, output, tailBudget, _⟩ :=
    compactMateToRuralRunBlock_correct (s := tail) rural required treeOptimal treeExpands treeBound
      checkpointFrame sound representative keptPaths raw rawBeforeReserve rowBeforeReserve pointerBeforeReserve
      reserve sameReservation nextSaved keepsPrior oddAfter mateAfter rfl matchReady
      mate oldCursor oldArray count oddData mateInputs minimum
  have requiredSize : (requiredLinkList I).length ≤ q := by
    simpa using (requiredLinkList_spec I).1.length_le_card
  have connectorSize : treePaths.flatten.length ≤ n ^ 2 :=
    (expands_traversal_count_le treeExpands treeBound).trans (by
      simpa only [pow_two] using Nat.mul_le_mul_right n (componentTree_length_lt treeOptimal.1).le)
  have priorSize : prior.length ≤ q + n ^ 2 := by
    simpa only [prior, List.length_append, List.length_map] using Nat.add_le_add requiredSize connectorSize
  have square : n ^ 2 ≤ n ^ 3 := by
    calc
      _ = n ^ 2 * 1 := (Nat.mul_one _).symm
      _ ≤ n ^ 2 * n := Nat.mul_le_mul_left _ rural.1.1
      _ = _ := (pow_succ _ 2).symm
  have vertexSize : n ≤ n ^ 3 :=
    (by simpa only [pow_two, Nat.mul_one] using Nat.mul_le_mul_left n rural.1.1 : n ≤ n ^ 2).trans square
  have sizePositive : 0 < n ^ 3 := pow_pos rural.1.1 _
  have prepBudget : compactSteps ≤ 100 * (n ^ 3 + q) := by
    change compactSteps ≤ 19 * prior.length + 17 * n ^ 2 + 26 * n + 34 at compactBudget
    omega
  have solveBudget : matchSteps ≤ (C * 2) * (n ^ 3 + q) := by
    refine matchBudget.trans ?_
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    have order := Nat.pow_le_pow_left kBound 3
    omega
  have total : rawSteps + (compactSteps + (matchSteps + tailSteps)) ≤ (C * 2 + 1050) * (n ^ 3 + q) := by
    calc
      _ ≤ 500 * (n ^ 3 + q) + (100 * (n ^ 3 + q) + ((C * 2) * (n ^ 3 + q) + 450 * (n ^ 3 + q))) :=
        Nat.add_le_add rawBudget (Nat.add_le_add prepBudget
          (Nat.add_le_add solveBudget ((Nat.le_succ tailSteps).trans tailBudget)))
      _ = _ := by ring
  have executes := rawRun.append (compactRun.append (matchRun.append tailRun))
  exact ⟨_, root, walk, _, executes, tailReady, output, valid, total⟩

/-- The route dispatcher, all preprocessing, and Euler output compose
into the mission's implementation once the compact matching block is given. -/
theorem ruralRAMProgram_correct {matching : List ArithmeticInstruction} {C : ℕ}
    (solver : CompactMateBlockSpec matching C) : RuralImplementation (ruralRAMProgram matching) (C * 2 + 1069) 0 := by
  have result := ruralInputDispatchBlock_correct (N := 0) (program := nonemptyRuralRAMBlock matching)
    (C := C * 2 + 1050) (fun I rural required => by
      obtain ⟨t, u, ts, steps, run, ready, output, valid, bound⟩ :=
        nonemptyRuralRAMBlock_correct solver I rural required
      exact ⟨t, u, ts, steps, run, ready, output, valid, fun _ => bound⟩)
  exact result

end VehicleRoutingSurvey.Routing
end RppSource_RuralRAMComposition

/-! RuralRAMGuarantees.lean -/
section RppSource_RuralRAMGuarantees
namespace VehicleRoutingSurvey.Routing

/-- Complete the unchanged rural-postman goal from a verified compact
matching block. -/
theorem rpp_tree_matching_sharp_of_compact_mate {matching : List ArithmeticInstruction} {C : ℕ}
    (solver : CompactMateBlockSpec matching C) :
    (∀ I : Service, Rural I →
      (∃ u ts, RuralRun I u ts) ∧
      (∃ u ts, Feasible I u ts ∧ pathCost I.graph ts = optimum I) ∧
      (∀ u ts, RuralRun I u ts → Feasible I u ts ∧
        pathCost I.graph ts ≤ (3 / 2 : ℝ) * optimum I)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
      ∃ (I : Service) (u : Fin I.graph.n) (ts : List (Traversal I.graph)),
        Rural I ∧ N ≤ I.graph.n ∧ 0 < optimum I ∧ RuralRun I u ts ∧
        (3 / 2 - ε) * optimum I < pathCost I.graph ts) ∧
    (∃ (p : List ArithmeticInstruction) (C N : ℕ), RuralImplementation p C N) :=
  rpp_tree_matching_sharp_of_implementation ⟨ruralRAMProgram matching, C * 2 + 1069, 0,
    ruralRAMProgram_correct solver⟩

end VehicleRoutingSurvey.Routing
end RppSource_RuralRAMGuarantees

/-! matching/MatchingStageControl.lean -/
section RppSource_MatchingStageControl
namespace VehicleRoutingSurvey.Routing

/-- Start the stage driver and the dual selector with the permanent matching tables. -/
def resetMatchingStageControlBlock : List ArithmeticInstruction :=
  [.natConst 29 0, .natConst 34 1, .natAdd 31 55 55, .natAdd 31 31 55,
   .natAdd 31 31 31, .natAdd 31 31 34, .natConst 32 0, .natConst 33 1,
   .natConst 1 0, .natConst 9 1, .natAdd 3 58 29, .natAdd 4 59 29,
   .natAdd 5 60 29, .natAdd 8 61 29, .realConst 15 0]

structure MatchingStageControls (s t : ArithmeticState) : Prop where
  limit : t.nr 31 = 6 * s.nr 55 + 1
  tick : t.nr 32 = 0
  active : t.nr 33 = 1
  one : t.nr 34 = 1
  winner : t.nr 1 = 0
  selectorOne : t.nr 9 = 1
  identifierBase : t.nr 3 = s.nr 58
  slackBase : t.nr 4 = s.nr 59
  rateBase : t.nr 5 = s.nr 60
  count : t.nr 8 = s.nr 61
  cumulativeDelta : t.rr 15 = 0
  natural : t.nm = s.nm
  real : t.rm = s.rm
  fixed : ∀ r, r ∉ [0, 1, 3, 4, 5, 8, 9, 29, 31, 32, 33, 34] → t.nr r = s.nr r

theorem resetMatchingStageControlBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns resetMatchingStageControlBlock 15 s t ∧ t.halted = false ∧ MatchingStageControls s t := by
  let t := (arithmeticStep resetMatchingStageControlBlock)^[15] s
  have ready : t.halted = false := by
    simp [t, resetMatchingStageControlBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = resetMatchingStageControlBlock.length := by
    simp [t, resetMatchingStageControlBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_⟩
  constructor
  case fixed =>
    intro r away
    apply arithmeticRun_keeps_register _ s 15
    simp [resetMatchingStageControlBlock, naturalDestination] at away ⊢
    omega
  all_goals
    simp [t, resetMatchingStageControlBlock, arithmeticStep, entry, running, Function.iterate_succ_apply'] <;> omega

/-- Publish the final compact mate array and restore the compact row-map registers. -/
def publishCompactMateTableBlock : List ArithmeticInstruction :=
  [.natConst 0 0, .natAdd 31 56 0, .natAdd 32 55 0, .natAdd 33 50 0]

theorem publishCompactMateTableBlock_correct {s : ArithmeticState}
    (entry : s.pc = 0) (running : s.halted = false) :
    ∃ t, BlockRuns publishCompactMateTableBlock 4 s t ∧ t.halted = false ∧
      t.nr 31 = s.nr 56 ∧ t.nr 32 = s.nr 55 ∧ t.nr 33 = s.nr 50 ∧ t.nm = s.nm ∧ t.rm = s.rm ∧
      ∀ r ≥ 100, t.nr r = s.nr r := by
  let t := (arithmeticStep publishCompactMateTableBlock)^[4] s
  have ready : t.halted = false := by
    simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  have exit : t.pc = publishCompactMateTableBlock.length := by
    simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  refine ⟨t, BlockRuns.of_running_exit rfl ready exit, ready, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · simp [t, publishCompactMateTableBlock, arithmeticStep, entry, running, Function.iterate_succ_apply']
  · intro r high
    apply arithmeticRun_keeps_high_register _ s 4
    simp [publishCompactMateTableBlock, naturalDestination] <;> omega


end VehicleRoutingSurvey.Routing
end RppSource_MatchingStageControl

/-! matching/WeightedCertificate.lean -/
section RppSource_WeightedCertificate
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

theorem perfectMatching_sum_vertices {n : ℕ} {O : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    {R : Type*} [AddCommMonoid R] (f : Fin n → R) :
    (∑ e ∈ M, ∑ v ∈ e.toFinset, f v) = ∑ v ∈ O, f v := by
  have cover : M.biUnion Sym2.toFinset = O := Finset.ext fun v =>
    ⟨fun hv =>
        let ⟨e, memM, endpoint⟩ := Finset.mem_biUnion.mp hv
        (perfect.1 e memM).2 v (Sym2.mem_toFinset.mp endpoint),
      fun hv =>
        let ⟨e, incidence, _⟩ := perfect.2 v hv
        Finset.mem_biUnion.mpr ⟨e, incidence.1, Sym2.mem_toFinset.mpr incidence.2⟩⟩
  have disjoint : (M : Set (Sym2 (Fin n))).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf distinct
    apply Finset.disjoint_left.mpr
    intro v ev fv
    have ev' := Sym2.mem_toFinset.mp ev
    have fv' := Sym2.mem_toFinset.mp fv
    obtain ⟨g, _, unique⟩ := perfect.2 v ((perfect.1 e he).2 v ev')
    exact distinct ((unique e ⟨he, ev'⟩).trans (unique f ⟨hf, fv'⟩).symm)
  calc
    _ = ∑ v ∈ M.biUnion Sym2.toFinset, f v := (Finset.sum_biUnion disjoint).symm
    _ = _ := congrArg (fun vs => ∑ v ∈ vs, f v) cover

/-- A matching edge crosses a cut when exactly one of its endpoints belongs to the cut. -/
abbrev MatchingCrossesCut {n : ℕ} (S : Finset (Fin n)) (e : Sym2 (Fin n)) : Prop :=
  ¬ e.IsDiag ∧ (e.toFinset.filter (· ∈ S)).card = 1

theorem matchingCrossesCut_mk_iff {n : ℕ} (S : Finset (Fin n)) {u v : Fin n}
    (distinct : u ≠ v) : MatchingCrossesCut S s(u, v) ↔
      (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S) := by
  by_cases hu : u ∈ S <;> by_cases hv : v ∈ S <;>
    simp [MatchingCrossesCut, Sym2.mk_isDiag_iff, Sym2.toFinset_mk_eq, Finset.filter_insert,
      Finset.filter_singleton, hu, hv, distinct]

/-- Every perfect matching uses at least one edge across an odd cut. -/
theorem matching_cut_nonempty_of_odd {n : ℕ} {O S : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M) (sub : S ⊆ O)
    (odd : Odd S.card) : (M.filter (MatchingCrossesCut S)).Nonempty := by
  have filtered : O.filter (· ∈ S) = S := Finset.ext fun _ =>
    Finset.mem_filter.trans ⟨And.right, fun hv => ⟨sub hv, hv⟩⟩
  have incidence : (∑ e ∈ M, (e.toFinset.filter (· ∈ S)).card) = S.card := by
    simpa only [Finset.sum_boole, Nat.cast_id, filtered] using
      perfectMatching_sum_vertices perfect (fun v => if v ∈ S then (1 : ℕ) else 0)
  by_contra absent
  have even : (∑ e ∈ M, (e.toFinset.filter (· ∈ S)).card) ≡ 0 [MOD 2] := by
    apply Nat.ModEq.sum_zero
    intro e he
    have distinct := (perfect.1 e he).1
    have bound : (e.toFinset.filter (· ∈ S)).card ≤ 2 :=
      (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq
        (Sym2.card_toFinset_of_not_isDiag e distinct)
    have notOne : (e.toFinset.filter (· ∈ S)).card ≠ 1 := fun crosses =>
      absent ⟨e, Finset.mem_filter.mpr ⟨he, distinct, crosses⟩⟩
    change (e.toFinset.filter (· ∈ S)).card % 2 = 0
    omega
  rw [incidence] at even
  change S.card % 2 = 0 at even
  exact Nat.zero_ne_one (even.symm.trans (Nat.odd_iff.mp odd))

/-- The sum of the endpoint potentials and the cut variables on an edge. -/
noncomputable def oddCutDualEdgeValue {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) (e : Sym2 (Fin n)) : ℝ :=
  (∑ v ∈ e.toFinset, potential v) + ∑ S ∈ cuts.filter (MatchingCrossesCut · e), cutDual S

theorem oddCutDualEdgeValue_mk {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) {u v : Fin n} (distinct : u ≠ v) :
    oddCutDualEdgeValue cuts potential cutDual s(u, v) = potential u + potential v +
      ∑ S ∈ cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)), cutDual S := by
  have sameCuts : cuts.filter (MatchingCrossesCut · s(u, v)) =
      cuts.filter (fun S => (u ∈ S ∧ v ∉ S) ∨ (v ∈ S ∧ u ∉ S)) := Finset.ext fun S => by
    simp only [Finset.mem_filter, matchingCrossesCut_mk_iff S distinct]
  simp [oddCutDualEdgeValue, sameCuts, Sym2.toFinset_mk_eq, Finset.sum_insert, distinct]

private theorem sum_oddCutDualEdgeValue {n : ℕ} {O : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (cuts : Finset (Finset (Fin n))) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ) :
    (∑ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e) =
      (∑ v ∈ O, potential v) +
        ∑ S ∈ cuts, ((M.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S := by
  simp only [oddCutDualEdgeValue, Finset.sum_add_distrib, perfectMatching_sum_vertices perfect]
  congr 1
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun S _ => by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- Feasible odd-cut dual variables certify a perfect matching when its edges are tight and
each cut with a positive dual variable is crossed exactly once. -/
theorem perfectMatching_min_of_oddCut_certificate {n : ℕ} {c : Fin n → Fin n → ℝ}
    {O : Finset (Fin n)} {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (cuts : Finset (Finset (Fin n))) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (valid : ∀ S ∈ cuts, S ⊆ O ∧ Odd S.card ∧ 0 ≤ cutDual S)
    (feasible : ∀ e, ¬e.IsDiag → (∀ v ∈ e, v ∈ O) →
      oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (tight : ∀ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e = edgeCost c e)
    (once : ∀ S ∈ cuts, 0 < cutDual S → (M.filter (MatchingCrossesCut S)).card = 1) :
    IsMinMatchingOn c O M := by
  refine ⟨perfect, fun N other => ?_⟩
  have chosenCuts : (∑ S ∈ cuts, ((M.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S) =
      ∑ S ∈ cuts, cutDual S := by
    apply Finset.sum_congr rfl
    intro S hS
    by_cases positive : 0 < cutDual S
    · simp [once S hS positive]
    · simp [le_antisymm (le_of_not_gt positive) (valid S hS).2.2]
  have otherCuts : (∑ S ∈ cuts, cutDual S) ≤
      ∑ S ∈ cuts, ((N.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S := by
    apply Finset.sum_le_sum
    intro S hS
    obtain ⟨sub, odd, nonneg⟩ := valid S hS
    have count := Finset.card_pos.mpr (matching_cut_nonempty_of_odd other sub odd)
    have countReal : (1 : ℝ) ≤ (N.filter (MatchingCrossesCut S)).card := by
      exact_mod_cast count
    simpa only [one_mul] using mul_le_mul_of_nonneg_right countReal nonneg
  calc
    edgeSetWeight c M = ∑ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e :=
      (Finset.sum_congr rfl tight).symm
    _ = (∑ v ∈ O, potential v) + ∑ S ∈ cuts, cutDual S := by
      rw [sum_oddCutDualEdgeValue perfect, chosenCuts]
    _ ≤ (∑ v ∈ O, potential v) +
        ∑ S ∈ cuts, ((N.filter (MatchingCrossesCut S)).card : ℝ) * cutDual S :=
      add_le_add le_rfl otherCuts
    _ = ∑ e ∈ N, oddCutDualEdgeValue cuts potential cutDual e :=
      (sum_oddCutDualEdgeValue other cuts potential cutDual).symm
    _ ≤ edgeSetWeight c N := Finset.sum_le_sum fun e he =>
      feasible e (other.1 e he).1 (other.1 e he).2

end VehicleRoutingSurvey.Routing
end RppSource_WeightedCertificate

/-! matching/WeightedBlossomCertificate.lean -/
section RppSource_WeightedBlossomCertificate
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- If a blossom is already matched internally away from its base, only its base can be
incident to a crossing matching edge. Oddness then forces exactly one crossing. -/
theorem matching_single_crossing_of_blossom {n : ℕ} {O S : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M) (sub : S ⊆ O)
    (odd : Odd S.card) {base : Fin n} (baseMem : base ∈ S)
    (internal : ∀ v ∈ S, v ≠ base → ∃ e ∈ M, v ∈ e ∧ ∀ w ∈ e, w ∈ S) :
    (M.filter (MatchingCrossesCut S)).card = 1 := by
  have atBase : ∀ e ∈ M.filter (MatchingCrossesCut S), base ∈ e := by
    intro e he
    obtain ⟨inM, crosses⟩ := Finset.mem_filter.mp he
    obtain ⟨v, inside⟩ := Finset.card_eq_one.mp crosses.2
    have inFilter : v ∈ e.toFinset.filter (· ∈ S) := inside.symm ▸ Finset.mem_singleton_self v
    obtain ⟨endpoint, inS⟩ := Finset.mem_filter.mp inFilter
    have atEdge := Sym2.mem_toFinset.mp endpoint
    by_cases isBase : v = base
    · exact isBase ▸ atEdge
    · obtain ⟨f, hf, atInternal, contained⟩ := internal v inS isBase
      have equal := (perfect.2 v (sub inS)).unique ⟨inM, atEdge⟩ ⟨hf, atInternal⟩
      have allInside : e.toFinset.filter (· ∈ S) = e.toFinset := Finset.filter_eq_self.mpr
        fun w hw => contained w (equal ▸ Sym2.mem_toFinset.mp hw)
      have one := crosses.2
      rw [allInside, Sym2.card_toFinset_of_not_isDiag e crosses.1] at one
      omega
  obtain ⟨crossing, chosen⟩ := matching_cut_nonempty_of_odd perfect sub odd
  have singleton : M.filter (MatchingCrossesCut S) = {crossing} := Finset.ext fun e =>
    ⟨fun he => Finset.mem_singleton.mpr ((perfect.2 base (sub baseMem)).unique
        ⟨(Finset.mem_filter.mp he).1, atBase e he⟩
        ⟨(Finset.mem_filter.mp chosen).1, atBase crossing chosen⟩),
      fun he => (Finset.mem_singleton.mp he).symm ▸ chosen⟩
  rw [singleton, Finset.card_singleton]

/-- Termination with a perfect matching, feasible dual variables, tight matched edges, and
internally matched positive blossoms certifies a minimum-weight matching. -/
theorem perfectMatching_min_of_blossom_certificate {n : ℕ} {c : Fin n → Fin n → ℝ}
    {O : Finset (Fin n)} {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M)
    (cuts : Finset (Finset (Fin n))) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (valid : ∀ S ∈ cuts, S ⊆ O ∧ Odd S.card ∧ 0 ≤ cutDual S)
    (feasible : ∀ e, ¬e.IsDiag → (∀ v ∈ e, v ∈ O) →
      oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (tight : ∀ e ∈ M, oddCutDualEdgeValue cuts potential cutDual e = edgeCost c e)
    (internallyMatched : ∀ S ∈ cuts, 0 < cutDual S → ∃ base ∈ S,
      ∀ v ∈ S, v ≠ base → ∃ e ∈ M, v ∈ e ∧ ∀ w ∈ e, w ∈ S) : IsMinMatchingOn c O M := by
  refine perfectMatching_min_of_oddCut_certificate perfect cuts potential cutDual valid feasible tight ?_
  intro S hS positive
  obtain ⟨base, baseMem, internal⟩ := internallyMatched S hS positive
  exact matching_single_crossing_of_blossom perfect (valid S hS).1 (valid S hS).2.1 baseMem internal

end VehicleRoutingSurvey.Routing
end RppSource_WeightedBlossomCertificate

/-! matching/MatchingCertifiedOutput.lean -/
section RppSource_MatchingCertifiedOutput
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Publish the final original-vertex mate table. Feasibility of the dual and the
internally matched positive blossoms certify the exact optimum. -/
theorem publishCertifiedCompactMateTableBlock_correct {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {original s : ArithmeticState} {mate : Fin k → Fin k}
    (entry : s.pc = 0) (running : s.halted = false)
    (dimension : s.nr 55 = k) (mapBase : s.nr 56 = original.nr 31)
    (mateAbove : original.nr 63 ≤ s.nr 50) (mateBytes : ∀ v : Fin k, s.nm (s.nr 50 + v.val) = (mate v).val)
    (validMate : MateTableOn Finset.univ mate)
    (saved : ∀ r ≥ 100, s.nr r = original.nr r)
    (natural : ∀ a < original.nr 63, s.nm a = original.nm a)
    (real : ∀ a < original.nr 64, s.rm a = original.rm a)
    (cuts : Finset (Finset (Fin k))) (potential : Fin k → ℝ) (cutDual : Finset (Fin k) → ℝ)
    (cutValid : ∀ B ∈ cuts, Odd B.card ∧ 0 ≤ cutDual B)
    (feasible : ∀ e, ¬e.IsDiag → oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost cost e)
    (tight : ∀ e ∈ mateEdgeSet Finset.univ mate, oddCutDualEdgeValue cuts potential cutDual e = edgeCost cost e)
    (internal : ∀ B ∈ cuts, 0 < cutDual B → ∃ base ∈ B,
      ∀ v ∈ B, v ≠ base → ∃ e ∈ mateEdgeSet Finset.univ mate, v ∈ e ∧ ∀ w ∈ e, w ∈ B) :
    ∃ t, BlockRuns publishCompactMateTableBlock 4 s t ∧ t.halted = false ∧
      t.nr 31 = original.nr 31 ∧ t.nr 32 = k ∧ original.nr 63 ≤ t.nr 33 ∧
      (∀ v : Fin k, t.nm (t.nr 33 + v.val) = (mate v).val) ∧
      IsMinMatchingOn cost Finset.univ (mateEdgeSet Finset.univ mate) ∧
      (∀ r ≥ 100, t.nr r = original.nr r) ∧
      (∀ a < original.nr 63, t.nm a = original.nm a) ∧ ∀ a < original.nr 64, t.rm a = original.rm a := by
  have optimal := perfectMatching_min_of_blossom_certificate (mateEdgeSet_perfect validMate)
    cuts potential cutDual (fun B hb => ⟨Finset.subset_univ B, cutValid B hb⟩)
    (fun e legal _ => feasible e legal) tight internal
  obtain ⟨t, run, live, oddMap, size, output, natMem, realMem, fixed⟩ :=
    publishCompactMateTableBlock_correct entry running
  exact ⟨t, run, live, oddMap.trans mapBase, size.trans dimension, output.symm ▸ mateAbove,
    fun v => by rw [natMem, output]; exact mateBytes v, optimal,
    fun r hr => (fixed r hr).trans (saved r hr),
    fun a ha => (congrFun natMem a).trans (natural a ha),
    fun a ha => (congrFun realMem a).trans (real a ha)⟩


end VehicleRoutingSurvey.Routing
end RppSource_MatchingCertifiedOutput

/-! matching/WeightedDualStep.lean -/
section RppSource_WeightedDualStep
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- A linear constraint remains feasible while `step * rate ≤ slack`. -/
structure DualSlack (Event : Type*) where
  event : Event
  slack : ℝ
  rate : ℝ

structure DualBound (Event : Type*) where
  event : Event
  amount : ℝ

private noncomputable def DualSlack.limit {Event : Type*} (constraint : DualSlack Event) :
    Option (DualBound Event) :=
  if 0 < constraint.rate then some ⟨constraint.event, constraint.slack / constraint.rate⟩
  else none

/-- Scan the positive-rate constraints for the first event reached along the direction. -/
noncomputable def nextDualBound {Event : Type*} (slacks : List (DualSlack Event)) :
    Option (DualBound Event) :=
  (slacks.filterMap DualSlack.limit).minOn? DualBound.amount

theorem nextDualBound_spec {Event : Type*} {slacks : List (DualSlack Event)}
    {bound : DualBound Event} (found : nextDualBound slacks = some bound)
    (initial : ∀ c ∈ slacks, 0 ≤ c.slack) :
    0 ≤ bound.amount ∧
      (∃ c ∈ slacks, c.event = bound.event ∧ 0 < c.rate ∧ bound.amount * c.rate = c.slack) ∧
      ∀ c ∈ slacks, bound.amount * c.rate ≤ c.slack := by
  unfold nextDualBound at found
  obtain ⟨hit, member, chosen⟩ := List.mem_filterMap.mp (List.minOn?_mem found)
  have hitRate : 0 < hit.rate := by
    by_contra nonpositive
    simp [DualSlack.limit, nonpositive] at chosen
  have boundEq : (⟨hit.event, hit.slack / hit.rate⟩ : DualBound Event) = bound :=
    Option.some.inj (by simpa only [DualSlack.limit, if_pos hitRate] using chosen)
  subst bound
  have amountNonneg := div_nonneg (initial hit member) hitRate.le
  refine ⟨amountNonneg, ⟨hit, member, rfl, hitRate, div_mul_cancel₀ _ hitRate.ne'⟩, ?_⟩
  intro c hc
  by_cases positive : 0 < c.rate
  · apply (le_div_iff₀ positive).mp
    have candidate : (⟨c.event, c.slack / c.rate⟩ : DualBound Event) ∈
        slacks.filterMap DualSlack.limit :=
      List.mem_filterMap.mpr ⟨c, hc, by simp only [DualSlack.limit, if_pos positive]⟩
    have best := List.minOn_eq_of_minOn?_eq_some found
    rw [← congrArg DualBound.amount best]
    exact List.apply_minOn_le_of_mem candidate
  · exact (mul_nonpos_of_nonneg_of_nonpos amountNonneg (le_of_not_gt positive)).trans (initial c hc)

/-- If no event bounds the step, every constraint has nonincreasing demand. -/
theorem nextDualBound_eq_none {Event : Type*} (slacks : List (DualSlack Event)) :
    nextDualBound slacks = none ↔ ∀ c ∈ slacks, c.rate ≤ 0 := by
  have minNone : (slacks.filterMap DualSlack.limit).minOn? DualBound.amount = none ↔
      slacks.filterMap DualSlack.limit = [] := by
    cases slacks.filterMap DualSlack.limit <;> simp [List.minOn?_cons_eq_some_minOn]
  rw [nextDualBound, minNone, List.filterMap_eq_nil_iff]
  constructor
  · intro noEvent c hc
    have none := noEvent c hc
    by_contra bad
    simp [DualSlack.limit, lt_of_not_ge bad] at none
  · intro noIncrease c hc
    simp [DualSlack.limit, not_lt_of_ge (noIncrease c hc)]

inductive MatchingDualEvent (n : ℕ) where
  | edge (e : Sym2 (Fin n))
  | cut (S : Finset (Fin n))

noncomputable def matchingEdgeSlack {n : ℕ} (c : Fin n → Fin n → ℝ)
    (cuts : Finset (Finset (Fin n))) (potential direction : Fin n → ℝ)
    (cutDual cutDirection : Finset (Fin n) → ℝ) (e : Sym2 (Fin n)) :
    DualSlack (MatchingDualEvent n) :=
  ⟨.edge e, edgeCost c e - oddCutDualEdgeValue cuts potential cutDual e,
    oddCutDualEdgeValue cuts direction cutDirection e⟩

noncomputable def matchingCutSlack {n : ℕ} (cutDual cutDirection : Finset (Fin n) → ℝ)
    (S : Finset (Fin n)) : DualSlack (MatchingDualEvent n) :=
  ⟨.cut S, cutDual S, -cutDirection S⟩

/-- The constraints encountered by a weighted matching dual adjustment. -/
noncomputable def matchingDualSlacks {n : ℕ} (c : Fin n → Fin n → ℝ)
    (edges : List (Sym2 (Fin n))) (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ) :
    List (DualSlack (MatchingDualEvent n)) :=
  edges.map (matchingEdgeSlack c cuts potential direction cutDual cutDirection) ++
    cuts.toList.map (matchingCutSlack cutDual cutDirection)

theorem oddCutDualEdgeValue_shift {n : ℕ} (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ)
    (δ : ℝ) (e : Sym2 (Fin n)) :
    oddCutDualEdgeValue cuts (fun v => potential v + δ * direction v)
      (fun S => cutDual S + δ * cutDirection S) e =
    oddCutDualEdgeValue cuts potential cutDual e + δ * oddCutDualEdgeValue cuts direction cutDirection e := by
  simp only [oddCutDualEdgeValue, Finset.sum_add_distrib, ← Finset.mul_sum, mul_add]
  abel

theorem matchingDualSlacks_nonnegative {n : ℕ} {c : Fin n → Fin n → ℝ}
    {edges : List (Sym2 (Fin n))} {cuts : Finset (Finset (Fin n))}
    {potential direction : Fin n → ℝ} {cutDual cutDirection : Finset (Fin n) → ℝ}
    (feasible : ∀ e ∈ edges, oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (nonnegative : ∀ S ∈ cuts, 0 ≤ cutDual S) :
    ∀ d ∈ matchingDualSlacks c edges cuts potential direction cutDual cutDirection, 0 ≤ d.slack := by
  intro d hd
  simp only [matchingDualSlacks, List.mem_append, List.mem_map, Finset.mem_toList] at hd
  rcases hd with ⟨e, he, rfl⟩ | ⟨S, hS, rfl⟩
  · exact sub_nonneg.mpr (feasible e he)
  · exact nonnegative S hS

noncomputable def MatchingDualAdjustment {n : ℕ} (c : Fin n → Fin n → ℝ)
    (edges : List (Sym2 (Fin n))) (cuts : Finset (Finset (Fin n)))
    (potential direction : Fin n → ℝ) (cutDual cutDirection : Finset (Fin n) → ℝ)
    (bound : DualBound (MatchingDualEvent n)) : Prop :=
    let potential' := fun v => potential v + bound.amount * direction v
    let cutDual' := fun S => cutDual S + bound.amount * cutDirection S
    0 ≤ bound.amount ∧ (∀ e ∈ edges, oddCutDualEdgeValue cuts potential' cutDual' e ≤ edgeCost c e) ∧
      (∀ S ∈ cuts, 0 ≤ cutDual' S) ∧
      match bound.event with
      | .edge e => e ∈ edges ∧ 0 < oddCutDualEdgeValue cuts direction cutDirection e ∧
          oddCutDualEdgeValue cuts potential' cutDual' e = edgeCost c e
      | .cut S => S ∈ cuts ∧ cutDirection S < 0 ∧ cutDual' S = 0

/-- Translate the selected slack constraint into an edge or blossom event and certify the
updated dual variables. The selection can come from a full scan or a checked cache. -/
theorem matchingDualAdjustment_of_slacks {n : ℕ} {c : Fin n → Fin n → ℝ}
    {edges : List (Sym2 (Fin n))} {cuts : Finset (Finset (Fin n))}
    {potential direction : Fin n → ℝ} {cutDual cutDirection : Finset (Fin n) → ℝ}
    {bound : DualBound (MatchingDualEvent n)}
    (chosen : let slacks := matchingDualSlacks c edges cuts potential direction cutDual cutDirection
      0 ≤ bound.amount ∧
        (∃ d ∈ slacks, d.event = bound.event ∧ 0 < d.rate ∧ bound.amount * d.rate = d.slack) ∧
        ∀ d ∈ slacks, bound.amount * d.rate ≤ d.slack) :
    MatchingDualAdjustment c edges cuts potential direction cutDual cutDirection bound := by
  dsimp only [MatchingDualAdjustment]
  obtain ⟨stepNonneg, ⟨d, hd, sameEvent, positive, hit⟩, safe⟩ := chosen
  refine ⟨stepNonneg, ?_, ?_, ?_⟩
  · intro e he
    have member : matchingEdgeSlack c cuts potential direction cutDual cutDirection e ∈
        matchingDualSlacks c edges cuts potential direction cutDual cutDirection :=
      List.mem_append_left _ (List.mem_map_of_mem he)
    have stays := safe _ member
    dsimp only [matchingEdgeSlack] at stays
    rw [oddCutDualEdgeValue_shift]
    linarith only [stays]
  · intro S hS
    have member : matchingCutSlack cutDual cutDirection S ∈
        matchingDualSlacks c edges cuts potential direction cutDual cutDirection :=
      List.mem_append_right _ (List.mem_map_of_mem (Finset.mem_toList.mpr hS))
    have stays := safe _ member
    dsimp only [matchingCutSlack] at stays
    rw [mul_neg] at stays
    linarith only [stays]
  · rw [← sameEvent]
    simp only [matchingDualSlacks, List.mem_append, List.mem_map, Finset.mem_toList] at hd
    rcases hd with ⟨e, he, rfl⟩ | ⟨S, hS, rfl⟩
    · refine ⟨he, positive, ?_⟩
      dsimp only [matchingEdgeSlack] at hit
      rw [oddCutDualEdgeValue_shift]
      linarith only [hit]
    · refine ⟨hS, neg_pos.mp positive, ?_⟩
      dsimp only [matchingCutSlack] at hit
      rw [mul_neg] at hit
      linarith only [hit]

/-- Adjusting to the first event preserves feasibility and makes the selected constraint tight. -/
theorem matchingDualStep_feasible {n : ℕ} {c : Fin n → Fin n → ℝ}
    {edges : List (Sym2 (Fin n))} {cuts : Finset (Finset (Fin n))}
    {potential direction : Fin n → ℝ} {cutDual cutDirection : Finset (Fin n) → ℝ}
    (feasible : ∀ e ∈ edges, oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost c e)
    (nonneg : ∀ S ∈ cuts, 0 ≤ cutDual S) {bound : DualBound (MatchingDualEvent n)}
    (found : nextDualBound (matchingDualSlacks c edges cuts potential direction cutDual cutDirection) = some bound) :
    MatchingDualAdjustment c edges cuts potential direction cutDual cutDirection bound :=
  matchingDualAdjustment_of_slacks (nextDualBound_spec found (matchingDualSlacks_nonnegative feasible nonneg))

end VehicleRoutingSurvey.Routing
end RppSource_WeightedDualStep

/-! matching/WeightedForestSlope.lean -/
section RppSource_WeightedForestSlope
namespace VehicleRoutingSurvey.Routing

/-- The current top-level blocks group matched vertices into singleton vertices and
contracted blossoms. The nonsingleton blocks have cut variables. -/
structure TopLevelMatchingBlocks {n : ℕ} (O : Finset (Fin n))
    (cuts : Finset (Finset (Fin n))) where
  block : Fin n → Finset (Fin n)
  self_mem : ∀ v ∈ O, v ∈ block v
  same_of_mem : ∀ {v w}, v ∈ O → w ∈ block v → block w = block v
  cut_mem : ∀ {v}, v ∈ O → (block v).card ≠ 1 → block v ∈ cuts

noncomputable def forestVertexDirection {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (label : Finset (Fin n) → ℝ) (v : Fin n) : ℝ :=
  if (blocks.block v).card = 1 then label (blocks.block v) else 0

noncomputable def forestCutDirection {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    (label : Finset (Fin n) → ℝ) (S : Finset (Fin n)) : ℝ :=
  if S ∈ O.image blocks.block ∧ S.card ≠ 1 then label S else 0

private theorem forest_crossing_blocks {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} (blocks : TopLevelMatchingBlocks O cuts)
    {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    (O.image blocks.block).filter (MatchingCrossesCut · s(u, v)) =
      if blocks.block u = blocks.block v then ∅ else {blocks.block u, blocks.block v} := by
  by_cases same : blocks.block u = blocks.block v
  · rw [if_pos same]
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro S hS
    obtain ⟨top, cross⟩ := Finset.mem_filter.mp hS
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
    rcases (matchingCrossesCut_mk_iff _ distinct).mp cross with ⟨inU, outV⟩ | ⟨inV, outU⟩
    · exact outV ((same.symm.trans (blocks.same_of_mem hw inU)) ▸ blocks.self_mem v hv)
    · exact outU ((same.trans (blocks.same_of_mem hw inV)) ▸ blocks.self_mem u hu)
  · rw [if_neg same]
    ext S
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
      matchingCrossesCut_mk_iff _ distinct]
    constructor
    · rintro ⟨top, ⟨inU, _⟩ | ⟨inV, _⟩⟩
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
        exact Or.inl (blocks.same_of_mem hw inU).symm
      · obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
        exact Or.inr (blocks.same_of_mem hw inV).symm
    · rintro (rfl | rfl)
      · exact ⟨Finset.mem_image_of_mem _ hu, Or.inl ⟨blocks.self_mem u hu, fun bad =>
          same (blocks.same_of_mem hu bad).symm⟩⟩
      · exact ⟨Finset.mem_image_of_mem _ hv, Or.inr ⟨blocks.self_mem v hv, fun bad =>
          same (blocks.same_of_mem hv bad)⟩⟩

/-- The dual slope of an edge is zero within a block. Across blocks it is the sum of their
two labels, so checking one edge does not require scanning the current cut variables. -/
theorem forest_edge_slope {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ)
    {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    oddCutDualEdgeValue cuts (forestVertexDirection blocks label) (forestCutDirection blocks label)
      s(u, v) = if blocks.block u = blocks.block v then 0 else label (blocks.block u) + label (blocks.block v) := by
  have supportEq : (cuts.filter (MatchingCrossesCut · s(u, v))).filter
      (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1) =
      ((O.image blocks.block).filter (MatchingCrossesCut · s(u, v))).filter (fun S => S.card ≠ 1) := by
    ext S
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, cross⟩, top, notOne⟩
      exact ⟨⟨top, cross⟩, notOne⟩
    · rintro ⟨⟨top, cross⟩, notOne⟩
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp top
      exact ⟨⟨blocks.cut_mem hw notOne, cross⟩, top, notOne⟩
  have sumEq : (∑ S ∈ cuts.filter (MatchingCrossesCut · s(u, v)), forestCutDirection blocks label S) =
      ∑ S ∈ ((O.image blocks.block).filter (MatchingCrossesCut · s(u, v))).filter (fun S => S.card ≠ 1),
        label S := by
    calc
      _ = ∑ S ∈ (cuts.filter (MatchingCrossesCut · s(u, v))).filter
          (fun S => S ∈ O.image blocks.block ∧ S.card ≠ 1), label S :=
        (Finset.sum_filter _ _).symm
      _ = _ := congrArg (fun sets => ∑ S ∈ sets, label S) supportEq
  unfold oddCutDualEdgeValue forestVertexDirection
  rw [sumEq, forest_crossing_blocks blocks hu hv distinct, Sym2.toFinset_mk_eq]
  by_cases same : blocks.block u = blocks.block v
  · have vNotOne : (blocks.block v).card ≠ 1 := by
      intro one
      obtain ⟨w, singleton⟩ := Finset.card_eq_one.mp one
      have uIn : u ∈ blocks.block v := same ▸ blocks.self_mem u hu
      have vIn := blocks.self_mem v hv
      rw [singleton] at uIn vIn
      exact distinct ((Finset.mem_singleton.mp uIn).trans (Finset.mem_singleton.mp vIn).symm)
    simp [same, vNotOne, Finset.sum_insert, distinct]
  · by_cases uOne : (blocks.block u).card = 1 <;> by_cases vOne : (blocks.block v).card = 1 <;>
      simp [same, uOne, vOne, distinct, Finset.sum_insert, Finset.filter_insert,
        Finset.filter_singleton, add_comm]

end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestSlope

/-! matching/WeightedRootEvent.lean -/
section RppSource_WeightedRootEvent
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Updating the dual registers changes an edge's slack by the step size times its block slope.
Inside a blossom this preserves the slack of every stored cycle edge. -/
theorem forest_edge_slack_update {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (label : Finset (Fin n) → ℝ)
    (c : Fin n → Fin n → ℝ) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (δ : ℝ) {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v) :
    edgeCost c s(u, v) - oddCutDualEdgeValue cuts
      (fun x => potential x + δ * forestVertexDirection blocks label x)
      (fun S => cutDual S + δ * forestCutDirection blocks label S) s(u, v) =
    (edgeCost c s(u, v) - oddCutDualEdgeValue cuts potential cutDual s(u, v)) -
      δ * (if blocks.block u = blocks.block v then 0 else label (blocks.block u) + label (blocks.block v)) := by
  rw [oddCutDualEdgeValue_shift, forest_edge_slope blocks label hu hv distinct, sub_add_eq_sub_sub]

theorem perfectMatching_card_twice {n : ℕ} {O : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (perfect : IsPerfectMatchingOn O M) :
    O.card = 2 * M.card := by
  calc
    O.card = ∑ v ∈ O, (1 : ℕ) := by simp
    _ = ∑ e ∈ M, ∑ v ∈ e.toFinset, (1 : ℕ) := (perfectMatching_sum_vertices perfect _).symm
    _ = ∑ _e ∈ M, (2 : ℕ) := Finset.sum_congr rfl fun e he => by
      simpa using Sym2.card_toFinset_of_not_isDiag e (perfect.1 e he).1
    _ = _ := by simp [Nat.mul_comm]

/-- An incomplete matching on an even vertex set leaves at least two exposed vertices. -/
theorem two_exposed_vertices {n : ℕ} {O covered : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (matched : IsPerfectMatchingOn covered M)
    (subset : covered ⊆ O) (even : Even O.card) (incomplete : covered ≠ O) :
    ∃ u v, u ∈ O \ covered ∧ v ∈ O \ covered ∧ u ≠ v := by
  apply Finset.one_lt_card_iff.mp
  rw [Finset.card_sdiff_of_subset subset, perfectMatching_card_twice matched]
  have smaller : covered.card < O.card := by
    by_contra bad
    exact incomplete (Finset.eq_of_subset_of_card_le subset (le_of_not_gt bad))
  rw [perfectMatching_card_twice matched] at smaller
  obtain ⟨half, cardEven⟩ := even
  omega

/-- The search on a complete graph cannot run out of dual events while exposed roots
exist. The edge between two roots in distinct outer blocks has positive slope. -/
theorem matchingDualBound_exists_of_incomplete {n : ℕ} {O covered : Finset (Fin n)}
    {M : Finset (Sym2 (Fin n))} (matched : IsPerfectMatchingOn covered M)
    (subset : covered ⊆ O) (even : Even O.card) (incomplete : covered ≠ O)
    (c : Fin n → Fin n → ℝ) (edges : List (Sym2 (Fin n)))
    (complete : ∀ u ∈ O, ∀ v ∈ O, u ≠ v → s(u, v) ∈ edges)
    (cuts : Finset (Finset (Fin n))) (blocks : TopLevelMatchingBlocks O cuts)
    (label : Finset (Fin n) → ℝ) (potential : Fin n → ℝ) (cutDual : Finset (Fin n) → ℝ)
    (rootOuter : ∀ v ∈ O \ covered, label (blocks.block v) = 1)
    (blockBase : ∀ S ∈ O.image blocks.block,
      ∃ base, ∀ v ∈ S, v ≠ base → v ∈ covered) :
    ∃ bound, nextDualBound (matchingDualSlacks c edges cuts potential
      (forestVertexDirection blocks label) cutDual (forestCutDirection blocks label)) = some bound := by
  obtain ⟨u, v, hu, hv, distinct⟩ := two_exposed_vertices matched subset even incomplete
  obtain ⟨uIn, uFree⟩ := Finset.mem_sdiff.mp hu
  obtain ⟨vIn, vFree⟩ := Finset.mem_sdiff.mp hv
  have separate : blocks.block u ≠ blocks.block v := by
    intro equal
    obtain ⟨base, coveredAway⟩ := blockBase (blocks.block v) (Finset.mem_image_of_mem _ vIn)
    have uIsBase : u = base := by
      by_contra different
      exact uFree (coveredAway u (equal ▸ blocks.self_mem u uIn) different)
    have vIsBase : v = base := by
      by_contra different
      exact vFree (coveredAway v (blocks.self_mem v vIn) different)
    exact distinct (uIsBase.trans vIsBase.symm)
  let direction := forestVertexDirection blocks label
  let cutDirection := forestCutDirection blocks label
  let slacks := matchingDualSlacks c edges cuts potential direction cutDual cutDirection
  let edge := s(u, v)
  let constraint : DualSlack (MatchingDualEvent n) :=
    ⟨.edge edge, edgeCost c edge - oddCutDualEdgeValue cuts potential cutDual edge,
      oddCutDualEdgeValue cuts direction cutDirection edge⟩
  have member : constraint ∈ slacks := by
    dsimp only [slacks, matchingDualSlacks]
    exact List.mem_append_left _ (List.mem_map.mpr ⟨edge, complete u uIn v vIn distinct, rfl⟩)
  have rising : 0 < constraint.rate := by
    dsimp only [constraint, edge, direction, cutDirection]
    rw [forest_edge_slope blocks label uIn vIn distinct, if_neg separate, rootOuter u hu, rootOuter v hv]
    norm_num
  change ∃ bound, nextDualBound slacks = some bound
  cases found : nextDualBound slacks with
  | none => exact ((not_le_of_gt rising) ((nextDualBound_eq_none slacks).mp found constraint member)).elim
  | some bound => exact ⟨bound, rfl⟩

end VehicleRoutingSurvey.Routing
end RppSource_WeightedRootEvent

/-! matching/MatchingTerminalState.lean -/
section RppSource_MatchingTerminalState
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

structure MatchingTerminalCertificate (k : ℕ) (cost : Fin k → Fin k → ℝ)
    (original result : ArithmeticState) where
  mate : Fin k → Fin k
  cuts : Finset (Finset (Fin k))
  potential : Fin k → ℝ
  cutDual : Finset (Fin k) → ℝ
  dimension : result.nr 55 = k
  mapBase : result.nr 56 = original.nr 31
  mateAbove : original.nr 63 ≤ result.nr 50
  mateBytes : ∀ v : Fin k, result.nm (result.nr 50 + v.val) = (mate v).val
  validMate : MateTableOn Finset.univ mate
  saved : ∀ r ≥ 100, result.nr r = original.nr r
  natural : ∀ a < original.nr 63, result.nm a = original.nm a
  real : ∀ a < original.nr 64, result.rm a = original.rm a
  cutValid : ∀ B ∈ cuts, Odd B.card ∧ 0 ≤ cutDual B
  feasible : ∀ e, ¬e.IsDiag → oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost cost e
  tight : ∀ e ∈ mateEdgeSet Finset.univ mate, oddCutDualEdgeValue cuts potential cutDual e = edgeCost cost e
  internal : ∀ B ∈ cuts, 0 < cutDual B → ∃ base ∈ B,
    ∀ v ∈ B, v ≠ base → ∃ e ∈ mateEdgeSet Finset.univ mate, v ∈ e ∧ ∀ w ∈ e, w ∈ B

/-- Data maintained between searches. Exposed originals are outside `covered`.
Internal matchings provide the complementary-slackness condition for live cuts. -/
structure CompactMatchingPrimalDual (k : ℕ) (cost : Fin k → Fin k → ℝ) where
  covered : Finset (Fin k)
  edges : Finset (Sym2 (Fin k))
  perfect : IsPerfectMatchingOn covered edges
  cuts : Finset (Finset (Fin k))
  potential : Fin k → ℝ
  cutDual : Finset (Fin k) → ℝ
  cutValid : ∀ B ∈ cuts, Odd B.card ∧ 0 ≤ cutDual B
  feasible : ∀ e, ¬e.IsDiag → oddCutDualEdgeValue cuts potential cutDual e ≤ edgeCost cost e
  tight : ∀ e ∈ edges, oddCutDualEdgeValue cuts potential cutDual e = edgeCost cost e
  internal : ∀ B ∈ cuts, 0 < cutDual B → ∃ base ∈ B,
    ∀ v ∈ B, v ≠ base → ∃ e ∈ edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B

structure CompactMatchingPrimalDualMemory {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (original result : ArithmeticState) : Prop where
  dimension : result.nr 55 = k
  oddMap : result.nr 56 = original.nr 31
  mateAbove : original.nr 63 ≤ result.nr 50
  mate : ∀ v : Fin k, result.nm (result.nr 50 + v.val) =
    if v ∈ state.covered then (mateOfMatching state.perfect v).val else k
  saved : ∀ r ≥ 100, result.nr r = original.nr r
  natural : ∀ a < original.nr 63, result.nm a = original.nm a
  real : ∀ a < original.nr 64, result.rm a = original.rm a

noncomputable def initialCompactMatchingPrimalDual {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (nonnegative : ∀ u v, 0 ≤ cost u v) (symmetric : ∀ u v, cost u v = cost v u) :
    CompactMatchingPrimalDual k cost where
  covered := ∅
  edges := ∅
  perfect := by simp [IsPerfectMatchingOn]
  cuts := ∅
  potential := fun _ => 0
  cutDual := fun _ => 0
  cutValid := by simp
  feasible := by
    intro e legal
    induction e using Sym2.inductionOn with
    | hf u v =>
      have distinct : u ≠ v := fun same => legal (Sym2.mk_isDiag_iff.mpr same)
      rw [oddCutDualEdgeValue_mk _ _ _ distinct, edgeCost_eq_of_symmetric cost symmetric]
      simpa using nonnegative u v
  tight := by simp
  internal := by simp

/-- After `k/2` augmentations the primal state covers all `k` originals.
The array already contains the total involution used by the publishing block. -/
theorem CompactMatchingPrimalDual.toTerminal {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {original result : ArithmeticState}
    (data : CompactMatchingPrimalDualMemory state original result)
    (even : k % 2 = 0) (size : state.edges.card = k / 2) :
    Nonempty (MatchingTerminalCertificate k cost original result) := by
  have counted := perfectMatching_card_twice state.perfect
  have coveredCard : state.covered.card = k := by omega
  have full : state.covered = (Finset.univ : Finset (Fin k)) := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    simpa using coveredCard.ge
  let mate := mateOfMatching state.perfect
  have mates : ∀ v : Fin k, result.nm (result.nr 50 + v.val) = (mate v).val := by
    intro v
    have included : v ∈ state.covered := by simp [full]
    simpa only [if_pos included, mate] using data.mate v
  have isTable : MateTableOn Finset.univ mate := by
    rw [← full]
    exact mateOfMatching_valid state.perfect
  have exactEdges : mateEdgeSet Finset.univ mate = state.edges := by
    rw [← full]
    exact mateEdgeSet_mateOfMatching state.perfect
  refine ⟨⟨mate, state.cuts, state.potential, state.cutDual, data.dimension, data.oddMap,
    data.mateAbove, mates, isTable, data.saved, data.natural, data.real, state.cutValid, state.feasible, ?_, ?_⟩⟩
  · rw [exactEdges]
    exact state.tight
  · rw [exactEdges]
    exact state.internal


end VehicleRoutingSurvey.Routing
end RppSource_MatchingTerminalState

/-! matching/MatchingPartitionView.lean -/
section RppSource_MatchingPartitionView
namespace VehicleRoutingSurvey.Routing

/-- The live top partition names each block by an original port. Inside a block,
only that port can remain exposed to the rest of the matching. -/
structure CompactMatchingPartition {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) where
  blocks : TopLevelMatchingBlocks Finset.univ state.cuts
  representative : Fin k → Fin k
  inside : ∀ v, representative v ∈ blocks.block v
  constant : ∀ u v, blocks.block u = blocks.block v → representative u = representative v
  coveredAway : ∀ v w, w ∈ blocks.block v → w ≠ representative v → w ∈ state.covered

theorem CompactMatchingPartition.same_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) {u v : Fin k} :
    part.representative u = part.representative v ↔ part.blocks.block u = part.blocks.block v := by
  refine ⟨?_, part.constant u v⟩
  intro same
  have first := part.blocks.same_of_mem (Finset.mem_univ u) (part.inside u)
  have second := part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v)
  rw [same] at first
  exact first.symm.trans second

theorem CompactMatchingPartition.representative_idem {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (v : Fin k) :
    part.representative (part.representative v) = part.representative v :=
  part.same_block.mpr (part.blocks.same_of_mem (Finset.mem_univ v) (part.inside v))

theorem CompactMatchingPartition.blockBase {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {S : Finset (Fin k)} (top : S ∈ Finset.univ.image part.blocks.block) :
    ∃ base ∈ S, ∀ v ∈ S, v ≠ base → v ∈ state.covered := by
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp top
  exact ⟨part.representative u, part.inside u, part.coveredAway u⟩

theorem CompactMatchingPartition.exposed_fixed {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    {v : Fin k} (exposed : v ∉ state.covered) : part.representative v = v := by
  by_contra different
  exact exposed (part.coveredAway v v (part.blocks.self_mem v (Finset.mem_univ v)) (Ne.symm different))

/-- A search only starts in positive dimension. Extend the representative map to
arbitrary cuts for the selector's label function. The empty-set value is unused. -/
noncomputable def CompactMatchingPartition.representativeOf {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (S : Finset (Fin k)) : Fin k := by
  classical
  exact if member : S.Nonempty then part.representative member.choose else ⟨0, positive⟩

theorem CompactMatchingPartition.representativeOf_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state) (positive : 0 < k)
    (v : Fin k) : part.representativeOf positive (part.blocks.block v) = part.representative v := by
  have members : (part.blocks.block v).Nonempty := ⟨v, part.blocks.self_mem v (Finset.mem_univ v)⟩
  rw [CompactMatchingPartition.representativeOf, dif_pos members]
  exact part.constant _ _ (part.blocks.same_of_mem (Finset.mem_univ v) members.choose_spec)

noncomputable def initialCompactMatchingPartition {k : ℕ} (cost : Fin k → Fin k → ℝ)
    (nonnegative : ∀ u v, 0 ≤ cost u v) (symmetric : ∀ u v, cost u v = cost v u) :
    CompactMatchingPartition (initialCompactMatchingPrimalDual cost nonnegative symmetric) where
  blocks := ⟨fun v => {v}, by simp, by
    intro v w _ member
    simp only [Finset.mem_singleton] at member
    rw [member], by simp⟩
  representative := id
  inside := by simp
  constant := by simp
  coveredAway := by
    intro v w member different
    exact (different (Finset.mem_singleton.mp member)).elim


end VehicleRoutingSurvey.Routing
end RppSource_MatchingPartitionView

/-! matching/CompactEdges.lean -/
section RppSource_CompactEdges
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- The abstract constraint list for the complete matching problem on the compact indices. -/
def compactMatchingEdges (k : ℕ) : List (Sym2 (Fin k)) :=
  (List.finRange k).flatMap fun u =>
    ((List.finRange k).filter fun v => decide (u ≠ v)).map fun v => s(u, v)

theorem mem_compactMatchingEdges_mk {k : ℕ} {u v : Fin k} (different : u ≠ v) :
    s(u, v) ∈ compactMatchingEdges k := by
  apply List.mem_flatMap.mpr
  refine ⟨u, by simp, List.mem_map.mpr ⟨v, ?_, rfl⟩⟩
  simp [different]

theorem mem_compactMatchingEdges_iff {k : ℕ} {e : Sym2 (Fin k)} :
    e ∈ compactMatchingEdges k ↔ ¬ e.IsDiag := by
  constructor
  · intro h
    obtain ⟨u, _, row⟩ := List.mem_flatMap.mp h
    obtain ⟨v, present, rfl⟩ := List.mem_map.mp row
    have distinct : u ≠ v := of_decide_eq_true (List.mem_filter.mp present).2
    exact fun loop => distinct (Sym2.mk_isDiag_iff.mp loop)
  · induction e using Sym2.inductionOn with
    | hf u v => exact fun h => mem_compactMatchingEdges_mk (fun eq => h (Sym2.mk_isDiag_iff.mpr eq))

theorem compactMatching_zero_dual_feasible {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (nonnegative : ∀ u v, 0 ≤ cost u v) :
    ∀ e ∈ compactMatchingEdges k, oddCutDualEdgeValue ∅ (fun _ => 0) (fun _ => 0) e ≤ edgeCost cost e := by
  intro e _
  induction e using Sym2.inductionOn with
  | hf u v =>
    have zero : oddCutDualEdgeValue ∅ (fun _ => 0) (fun _ => 0) s(u, v) = 0 := by
      simp [oddCutDualEdgeValue]
    rw [zero]
    change 0 ≤ (cost u v + cost v u) / 2
    exact div_nonneg (add_nonneg (nonnegative u v) (nonnegative v u)) (by norm_num)

end VehicleRoutingSurvey.Routing
end RppSource_CompactEdges

/-! matching/AlternatingForestGrow.lean -/
section RppSource_AlternatingForestGrow
namespace VehicleRoutingSurvey.Routing

inductive AlternatingForestRole (α : Type*) where
  | unlabelled
  | outer (parent : Option α)
  | inner (parent : α)

structure AlternatingForestState (α : Type*) where
  role : α → AlternatingForestRole α
  depth : α → ℕ

/-- The parent of a marked node is closer to a root. An inner node was reached by
a tight unmatched edge, and its mate is an outer child. -/
def AlternatingForestState.valid {α : Type*} (state : AlternatingForestState α)
    (mate : α → Option α) (tight : α → α → Prop) : Prop :=
  ∀ x, match state.role x with
    | .unlabelled => True
    | .outer none => mate x = none
    | .outer (some p) => (∃ q, state.role p = .inner q) ∧ mate x = some p ∧
        mate p = some x ∧ tight p x ∧ state.depth p < state.depth x
    | .inner p => (∃ q, state.role p = .outer q) ∧ mate x ≠ some p ∧
        (∃ child, mate x = some child ∧ state.role child = .outer (some x)) ∧
        tight p x ∧ state.depth p < state.depth x

/-- Reach a matched, unlabelled pair through a tight edge from an existing outer node. -/
def AlternatingForestState.grow {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (source inner outer : α) : AlternatingForestState α where
  role x := if x = inner then .inner source else if x = outer then .outer (some inner) else state.role x
  depth x := if x = inner then state.depth source + 1
    else if x = outer then state.depth source + 2 else state.depth x

theorem AlternatingForestState.grow_valid {α : Type*} [DecidableEq α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {source inner outer : α} {parent : Option α}
    (fromRole : state.role source = .outer parent)
    (innerRole : state.role inner = .unlabelled) (outerRole : state.role outer = .unlabelled)
    (distinct : inner ≠ outer) (mateInner : mate inner = some outer) (mateOuter : mate outer = some inner)
    (tightIncoming : tight source inner) (tightMatched : tight inner outer) :
    (state.grow source inner outer).valid mate tight := by
  let after := state.grow source inner outer
  have unchanged {x} (marked : state.role x ≠ .unlabelled) :
      after.role x = state.role x ∧ after.depth x = state.depth x := by
    have notInner : x ≠ inner := fun h => marked (h.symm ▸ innerRole)
    have notOuter : x ≠ outer := fun h => marked (h.symm ▸ outerRole)
    simp [after, grow, notInner, notOuter]
  have fromMarked : state.role source ≠ .unlabelled := by simp [fromRole]
  have fromUnchanged := unchanged fromMarked
  have fromDifferent : outer ≠ source := by
    intro equal
    exact fromMarked (equal ▸ outerRole)
  have newInner : after.role inner = .inner source := by simp [after, grow]
  have newOuter : after.role outer = .outer (some inner) := by simp [after, grow, distinct.symm]
  have innerDepth : after.depth inner = state.depth source + 1 := by simp [after, grow]
  have outerDepth : after.depth outer = state.depth source + 2 := by simp [after, grow, distinct.symm]
  change after.valid mate tight
  intro x
  by_cases isInner : x = inner
  · subst x
    rw [newInner]
    refine ⟨⟨parent, fromUnchanged.1.trans fromRole⟩, ?_, ⟨outer, mateInner, newOuter⟩, tightIncoming, ?_⟩
    · exact fun h => fromDifferent (Option.some.inj (mateInner.symm.trans h))
    · rw [fromUnchanged.2, innerDepth]
      omega
  by_cases isOuter : x = outer
  · subst x
    rw [newOuter]
    refine ⟨⟨source, newInner⟩, mateOuter, mateInner, tightMatched, ?_⟩
    rw [innerDepth, outerDepth]
    omega
  have xRole : after.role x = state.role x := by simp [after, grow, isInner, isOuter]
  have xDepth : after.depth x = state.depth x := by simp [after, grow, isInner, isOuter]
  rw [xRole]
  have old := valid x
  cases kind : state.role x with
  | unlabelled => trivial
  | outer parent' =>
    try rw [kind] at old
    cases parent' with
    | none => exact old
    | some p =>
      obtain ⟨⟨q, pRole⟩, xMate, pMate, edge, earlier⟩ := old
      have pMarked : state.role p ≠ .unlabelled := by simp [pRole]
      obtain ⟨pSame, pDepth⟩ := unchanged pMarked
      exact ⟨⟨q, pSame.trans pRole⟩, xMate, pMate, edge, by simpa only [pDepth, xDepth] using earlier⟩
  | inner p =>
    try rw [kind] at old
    obtain ⟨⟨q, pRole⟩, notMate, ⟨child, childMate, childRole⟩, edge, earlier⟩ := old
    have pMarked : state.role p ≠ .unlabelled := by simp [pRole]
    have childMarked : state.role child ≠ .unlabelled := by simp [childRole]
    obtain ⟨pSame, pDepth⟩ := unchanged pMarked
    exact ⟨⟨q, pSame.trans pRole⟩, notMate, ⟨child, childMate, (unchanged childMarked).1.trans childRole⟩,
      edge, by simpa only [pDepth, xDepth] using earlier⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestGrow

/-! matching/AlternatingForestTrace.lean -/
section RppSource_AlternatingForestTrace
namespace VehicleRoutingSurvey.Routing

def AlternatingForestRole.parent {α : Type*} : AlternatingForestRole α → Option α
  | .unlabelled => none
  | .outer parent => parent
  | .inner parent => some parent

theorem AlternatingForestState.parent_valid {α : Type*}
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled) :
    match (state.role x).parent with
    | none => state.role x = .outer none ∧ mate x = none
    | some p => state.role p ≠ .unlabelled ∧ state.depth p < state.depth x ∧ tight p x := by
  have old := valid x
  cases kind : state.role x with
  | unlabelled => exact (marked kind).elim
  | outer parent =>
    try rw [kind] at old
    cases parent with
    | none => exact ⟨rfl, old⟩
    | some p =>
      obtain ⟨⟨q, pRole⟩, _, _, edge, earlier⟩ := old
      exact ⟨by simp [pRole], earlier, edge⟩
  | inner p =>
    try rw [kind] at old
    obtain ⟨⟨q, pRole⟩, _, _, edge, earlier⟩ := old
    exact ⟨by simp [pRole], earlier, edge⟩

private def AlternatingForestState.traceParents {α : Type*} (state : AlternatingForestState α) :
    ℕ → α → List α
  | 0, _ => []
  | fuel + 1, x => x :: (match (state.role x).parent with
      | none => []
      | some p => state.traceParents fuel p)

/-- Follow the marked node's parent pointers to its exposed outer root. -/
def AlternatingForestState.traceToRoot {α : Type*} (state : AlternatingForestState α) (x : α) : List α :=
  state.traceParents (state.depth x + 1) x

private theorem AlternatingForestState.traceParents_spec {α : Type*}
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled)
    {fuel : ℕ} (enough : state.depth x < fuel) :
    let trail := state.traceParents fuel x
    trail.head? = some x ∧ trail.Nodup ∧
      trail.IsChain (fun child p => (state.role child).parent = some p ∧ tight p child) ∧
      (∃ root, trail.getLast? = some root ∧ state.role root = .outer none ∧ mate root = none) ∧
      ∀ v ∈ trail, state.depth v ≤ state.depth x := by
  induction fuel generalizing x with
  | zero => omega
  | succ fuel ih =>
    have parentValid := AlternatingForestState.parent_valid valid marked
    cases parent : (state.role x).parent with
    | none =>
      try rw [parent] at parentValid
      dsimp only [traceParents]
      rw [parent]
      exact ⟨rfl, by simp, List.IsChain.singleton _,
        ⟨x, rfl, parentValid.1, parentValid.2⟩, by simp⟩
    | some p =>
      try rw [parent] at parentValid
      obtain ⟨pMarked, smaller, edge⟩ := parentValid
      have pEnough : state.depth p < fuel := by omega
      obtain ⟨headAt, distinct, chain, ⟨root, atEnd, rootRole, exposed⟩, bound⟩ := ih pMarked pEnough
      obtain ⟨rest, pFirst⟩ := List.head?_eq_some_iff.mp headAt
      have newDistinct : x ∉ state.traceParents fuel p := by
        intro present
        exact (not_le_of_gt smaller) (bound x present)
      dsimp only [traceParents]
      rw [parent]
      dsimp only
      refine ⟨rfl, List.nodup_cons.mpr ⟨newDistinct, distinct⟩, ?_, ⟨root, ?_, rootRole, exposed⟩, ?_⟩
      · rw [pFirst, List.isChain_cons_cons]
        exact ⟨⟨parent, edge⟩, by simpa only [pFirst] using chain⟩
      · simpa only [pFirst, List.getLast?_cons_cons] using atEnd
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | earlier
        · exact le_rfl
        · exact (bound v earlier).trans smaller.le

theorem AlternatingForestState.traceToRoot_spec {α : Type*} [Fintype α]
    {state : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : state.valid mate tight) {x : α} (marked : state.role x ≠ .unlabelled) :
    let trail := state.traceToRoot x
    trail.head? = some x ∧ trail.Nodup ∧ trail.length ≤ Fintype.card α ∧
      trail.IsChain (fun child p => (state.role child).parent = some p ∧ tight p child) ∧
      ∃ root, trail.getLast? = some root ∧ state.role root = .outer none ∧ mate root = none := by
  obtain ⟨headAt, distinct, chain, root, _⟩ :=
    AlternatingForestState.traceParents_spec valid marked (Nat.lt_succ_self _)
  exact ⟨headAt, distinct, distinct.length_le_card, chain, root⟩

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestTrace

/-! matching/AlternatingForestAncestor.lean -/
section RppSource_AlternatingForestAncestor
namespace VehicleRoutingSurvey.Routing

private def markForestTrace {α : Type*} [DecidableEq α] (trace : List α) : α → Bool :=
  trace.foldl (fun table v => Function.update table v true) (fun _ => false)

private theorem markForestTrace_true {α : Type*} [DecidableEq α] {trace : List α} {v : α} :
    markForestTrace trace v = true ↔ v ∈ trace := by
  have marked (table : α → Bool) (xs : List α) :
      xs.foldl (fun cells x => Function.update cells x true) table v = true ↔
        table v = true ∨ v ∈ xs := by
    induction xs generalizing table with
    | nil => simp
    | cons head tail ih =>
      simp only [List.foldl_cons, ih, Function.update_apply, List.mem_cons]
      by_cases equal : v = head <;> simp [equal]
  simpa only [markForestTrace, Bool.false_eq_true, false_or] using marked (fun _ => false) trace

/-- Mark the first parent trace, then scan the second from its endpoint towards its root. -/
def firstSharedAncestor {α : Type*} [DecidableEq α] (left right : List α) : Option α :=
  right.find? (markForestTrace left)

theorem firstSharedAncestor_eq_some_iff {α : Type*} [DecidableEq α]
    {left right : List α} {ancestor : α} : firstSharedAncestor left right = some ancestor ↔
    ancestor ∈ left ∧ ∃ before after, right = before ++ (ancestor :: after) ∧
      ∀ v ∈ before, v ∉ left := by
  rw [firstSharedAncestor, List.find?_eq_some_iff_append]
  have notMarked (v : α) : (!(markForestTrace left v)) = true ↔ v ∉ left := by
    rw [← markForestTrace_true]
    cases markForestTrace left v <;> decide
  simp only [markForestTrace_true, notMarked]

theorem firstSharedAncestor_eq_none_iff {α : Type*} [DecidableEq α] {left right : List α} :
    firstSharedAncestor left right = none ↔ ∀ v ∈ right, v ∉ left := by
  simp only [firstSharedAncestor, List.find?_eq_none, markForestTrace_true]

/-- Select the common ancestor for contraction, or report that the endpoints lie in
different trees. The mark table avoids comparing every pair of entries in the two traces. -/
def AlternatingForestState.commonAncestor {α : Type*} [DecidableEq α]
    (state : AlternatingForestState α) (u v : α) : Option α :=
  firstSharedAncestor (state.traceToRoot u) (state.traceToRoot v)

theorem AlternatingForestState.commonAncestor_iff {α : Type*} [DecidableEq α]
    (state : AlternatingForestState α) (u v : α) {ancestor : α} :
    state.commonAncestor u v = some ancestor ↔ ancestor ∈ state.traceToRoot u ∧
      ∃ before after, state.traceToRoot v = before ++ (ancestor :: after) ∧
        ∀ w ∈ before, w ∉ state.traceToRoot u :=
  firstSharedAncestor_eq_some_iff

end VehicleRoutingSurvey.Routing
end RppSource_AlternatingForestAncestor

/-! matching/WeightedForestDispatch.lean -/
section RppSource_WeightedForestDispatch
namespace VehicleRoutingSurvey.Routing

noncomputable def AlternatingForestRole.dualDirection {α : Type*} : AlternatingForestRole α → ℝ
  | .outer _ => 1
  | .inner _ => -1
  | .unlabelled => 0

/-- A positive edge rate can trigger two outer nodes, or one outer node and one unlabelled node. -/
theorem risingForestEdge_iff {α β : Type*} (left : AlternatingForestRole α) (right : AlternatingForestRole β) :
    0 < left.dualDirection + right.dualDirection ↔
      ((∃ p, left = .outer p) ∧ ((∃ q, right = .outer q) ∨ right = .unlabelled)) ∨
        (left = .unlabelled ∧ ∃ q, right = .outer q) := by
  cases left <;> cases right <;> norm_num [AlternatingForestRole.dualDirection, reduceCtorEq] <;> grind

inductive ForestEdgeAction (α : Type*) where
  | grow (source target : α)
  | contract (base : α)
  | augment

/-- Dispatch an edge between top-level nodes using their labels and common ancestor. -/
def AlternatingForestState.edgeAction {α : Type*} [DecidableEq α] (state : AlternatingForestState α)
    (u v : α) : Option (ForestEdgeAction α) :=
  match state.role u, state.role v with
  | .outer _, .unlabelled => some (.grow u v)
  | .unlabelled, .outer _ => some (.grow v u)
  | .outer _, .outer _ => some (match state.commonAncestor u v with
      | some base => .contract base
      | none => .augment)
  | _, _ => none

theorem AlternatingForestState.edgeAction_of_rising {α : Type*} [DecidableEq α]
    (state : AlternatingForestState α) {u v : α}
    (rising : 0 < (state.role u).dualDirection + (state.role v).dualDirection) :
    ∃ action, state.edgeAction u v = some action := by
  rcases (risingForestEdge_iff _ _).mp rising with ⟨⟨p, uRole⟩, ⟨q, vRole⟩ | vRole⟩ | ⟨uRole, q, vRole⟩
  · refine ⟨(match state.commonAncestor u v with
      | some base => .contract base
      | none => .augment), ?_⟩
    simp [edgeAction, uRole, vRole]
  · exact ⟨.grow u v, by simp [edgeAction, uRole, vRole]⟩
  · exact ⟨.grow v u, by simp [edgeAction, uRole, vRole]⟩

theorem forestEdgeAction_of_positive_rate {n : ℕ} {O : Finset (Fin n)}
    {cuts : Finset (Finset (Fin n))} {α : Type*} [DecidableEq α]
    (blocks : TopLevelMatchingBlocks O cuts) (state : AlternatingForestState α)
    (rep : Finset (Fin n) → α) {u v : Fin n} (hu : u ∈ O) (hv : v ∈ O) (distinct : u ≠ v)
    (rising :
      let direction := fun B => (state.role (rep B)).dualDirection
      0 < oddCutDualEdgeValue cuts (forestVertexDirection blocks direction)
        (forestCutDirection blocks direction) s(u, v)) :
    blocks.block u ≠ blocks.block v ∧ ∃ action, state.edgeAction (rep (blocks.block u)) (rep (blocks.block v)) = some action := by
  dsimp only at rising
  rw [forest_edge_slope blocks _ hu hv distinct] at rising
  by_cases same : blocks.block u = blocks.block v
  · simp [same] at rising
  · rw [if_neg same] at rising
    exact ⟨same, state.edgeAction_of_rising rising⟩

/-- A cut can limit the dual step only when its blossom is a contracted inner node. -/
theorem forestCutDirection_negative_iff {n : ℕ} {O : Finset (Fin n)} {cuts : Finset (Finset (Fin n))}
    (blocks : TopLevelMatchingBlocks O cuts) (role : Finset (Fin n) → AlternatingForestRole (Fin n))
    (S : Finset (Fin n)) :
    forestCutDirection blocks (fun B => (role B).dualDirection) S < 0 ↔
      (S ∈ O.image blocks.block ∧ S.card ≠ 1) ∧ ∃ parent, role S = .inner parent := by
  by_cases enabled : S ∈ O.image blocks.block ∧ S.card ≠ 1
  · rw [forestCutDirection, if_pos enabled]
    simp only [enabled, true_and]
    cases label : role S <;>
      norm_num [label, enabled.1, enabled.2, AlternatingForestRole.dualDirection, reduceCtorEq] <;> grind
  · have impossible : ¬((S ∈ O.image blocks.block ∧ S.card ≠ 1) ∧ ∃ parent, role S = .inner parent) :=
      fun h => enabled h.1
    simp only [forestCutDirection, if_neg enabled, lt_self_iff_false, impossible]

end VehicleRoutingSurvey.Routing
end RppSource_WeightedForestDispatch

/-! matching/MatchingSearchDual.lean -/
section RppSource_MatchingSearchDual
namespace VehicleRoutingSurvey.Routing

open SupplyChainTheory

/-- Every retained blossom has an internal near-perfect matching, including
blossoms with zero dual value that can acquire a positive value in this search. -/
def CompactMatchingPrimalDual.InternalCuts {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) : Prop :=
  ∀ B ∈ state.cuts, ∃ base ∈ B,
    ∀ v ∈ B, v ≠ base → ∃ e ∈ state.edges, v ∈ e ∧ ∀ w ∈ e, w ∈ B

/-- A crossing matched edge is represented by the two endpoints of its
quotient mate pair. Inner and outer partners take opposite dual steps. -/
structure CompactMatchingSearchForest {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (mate : Fin k → Option (Fin k))
    (tight : Fin k → Fin k → Prop) : Prop where
  valid : forest.valid mate tight
  crossing : ∀ {u v : Fin k}, s(u, v) ∈ state.edges → part.blocks.block u ≠ part.blocks.block v →
    mate (part.representative u) = some (part.representative v) ∧
      mate (part.representative v) = some (part.representative u)
  exposed : ∀ v ∉ state.covered, forest.role (part.representative v) = .outer none

theorem AlternatingForestState.mate_dualDirection_add_eq_zero {α : Type*}
    {forest : AlternatingForestState α} {mate : α → Option α} {tight : α → α → Prop}
    (valid : forest.valid mate tight) {u v : α} (uv : mate u = some v) (vu : mate v = some u) :
    (forest.role u).dualDirection + (forest.role v).dualDirection = 0 := by
  have outerPartner {x y : α} {p : Option α} (outer : forest.role x = .outer p) (xy : mate x = some y) :
      ∃ r, forest.role y = .inner r := by
    have row := valid x
    rw [outer] at row
    cases p with
    | none =>
      have impossible : some y = none := xy.symm.trans row
      simp at impossible
    | some p =>
      obtain ⟨pInner, xp, _, _, _⟩ := row
      exact (Option.some.inj (xp.symm.trans xy)) ▸ pInner
  have innerPartner {x y p : α} (inner : forest.role x = .inner p) (xy : mate x = some y) :
      forest.role y = .outer (some x) := by
    have row := valid x
    rw [inner] at row
    obtain ⟨_, _, ⟨z, xz, outer⟩, _, _⟩ := row
    exact (Option.some.inj (xz.symm.trans xy)) ▸ outer
  cases hu : forest.role u with
  | outer p =>
    obtain ⟨r, hv⟩ := outerPartner hu uv
    norm_num [hv, AlternatingForestRole.dualDirection]
  | inner p => norm_num [innerPartner hu uv, AlternatingForestRole.dualDirection]
  | unlabelled =>
    cases hv : forest.role v with
    | unlabelled => simp [AlternatingForestRole.dualDirection]
    | outer p =>
      obtain ⟨r, bad⟩ := outerPartner hv vu
      simp [hu] at bad
    | inner p =>
      have bad := innerPartner hv vu
      simp [hu] at bad

noncomputable def CompactMatchingPartition.dualLabel {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (B : Finset (Fin k)) : ℝ :=
  (forest.role (part.representativeOf positive B)).dualDirection

theorem CompactMatchingPartition.dualLabel_block {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} (part : CompactMatchingPartition state)
    (forest : AlternatingForestState (Fin k)) (positive : 0 < k) (v : Fin k) :
    part.dualLabel forest positive (part.blocks.block v) = (forest.role (part.representative v)).dualDirection := by
  rw [CompactMatchingPartition.dualLabel, part.representativeOf_block]

theorem CompactMatchingSearchForest.matched_slope_zero {k : ℕ} {cost : Fin k → Fin k → ℝ}
    {state : CompactMatchingPrimalDual k cost} {part : CompactMatchingPartition state}
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    {e : Sym2 (Fin k)} (present : e ∈ state.edges) :
    oddCutDualEdgeValue state.cuts (forestVertexDirection part.blocks (part.dualLabel forest positive))
      (forestCutDirection part.blocks (part.dualLabel forest positive)) e = 0 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have legal := (state.perfect.1 _ present).1
    have distinct : u ≠ v := fun same => legal (Sym2.mk_isDiag_iff.mpr same)
    rw [forest_edge_slope part.blocks _ (Finset.mem_univ u) (Finset.mem_univ v) distinct]
    by_cases same : part.blocks.block u = part.blocks.block v
    · rw [if_pos same]
    · rw [if_neg same, part.dualLabel_block, part.dualLabel_block]
      obtain ⟨uv, vu⟩ := search.crossing present same
      exact AlternatingForestState.mate_dualDirection_add_eq_zero search.valid uv vu

/-- The selected step keeps the primal matching and partition intact while
updating the two dual functions and exposing the newly tight event. -/
noncomputable def CompactMatchingPrimalDual.advanceSearch {k : ℕ} {cost : Fin k → Fin k → ℝ}
    (state : CompactMatchingPrimalDual k cost) (part : CompactMatchingPartition state)
    {forest : AlternatingForestState (Fin k)} {mate : Fin k → Option (Fin k)} {tight : Fin k → Fin k → Prop}
    (search : CompactMatchingSearchForest part forest mate tight) (positive : 0 < k)
    (internal : state.InternalCuts) (bound : DualBound (MatchingDualEvent k))
    (adjustment : MatchingDualAdjustment cost (compactMatchingEdges k) state.cuts state.potential
      (forestVertexDirection part.blocks (part.dualLabel forest positive)) state.cutDual
      (forestCutDirection part.blocks (part.dualLabel forest positive)) bound) : CompactMatchingPrimalDual k cost where
  covered := state.covered
  edges := state.edges
  perfect := state.perfect
  cuts := state.cuts
  potential v := state.potential v + bound.amount * forestVertexDirection part.blocks (part.dualLabel forest positive) v
  cutDual B := state.cutDual B + bound.amount * forestCutDirection part.blocks (part.dualLabel forest positive) B
  cutValid B present := ⟨(state.cutValid B present).1, adjustment.2.2.1 B present⟩
  feasible e legal := adjustment.2.1 e (mem_compactMatchingEdges_iff.mpr legal)
  tight e present := by
    rw [oddCutDualEdgeValue_shift, search.matched_slope_zero positive present, mul_zero, add_zero]
    exact state.tight e present
  internal B present _ := internal B present


end VehicleRoutingSurvey.Routing
end RppSource_MatchingSearchDual


