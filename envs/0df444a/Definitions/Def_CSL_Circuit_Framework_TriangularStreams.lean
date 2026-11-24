-- Prove2me | Definitions.Def_CSL_Circuit_Framework_TriangularStreams
-- name    : CSL_Circuit_Framework_TriangularStreams
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:08:43.975355+00:00
-- url     : https://prove2.me/theorems/59bcad76-b427-4ccd-a9b1-c4d4505d98d6
-- title:
--   Coded sorting library: Circuit / Framework / TriangularStreams
-- statement:
--   Module `CodedSorting.Circuit.Framework.TriangularStreams` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Executing a lower-triangular address change. The program updates coordinates in decreasing order. Its correctness follows from these coordinate updates.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Circuit.Framework.TriangularStreams

import Definitions.Def_CSL_Compat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fintype.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_CSL_Shared_Programs_TagErasure
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Order.PiLex
import Mathlib.Data.Finset.Sort

section TriangularProgram
/-! Executing a lower-triangular address change. The program updates coordinates in decreasing order. Its correctness follows from these coordinate updates. 





-/

namespace CSL.TriangularProgram

open scoped BigOperators Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

def lower (A : Matrix (Fin m) (Fin m) R) : Prop :=
  ∀ i j, i < j → A i j = 0

def row (A : Matrix (Fin m) (Fin m) R) (i : Fin m) (x : Fin m → R) : R :=
  ∑ j, A i j * x j

def updateCoordinate (A : Matrix (Fin m) (Fin m) R) (i : Fin m)
    (x : Fin m → R) : Fin m → R := Function.update x i (row A i x)

theorem row_unchanged_by_later_update (A : Matrix (Fin m) (Fin m) R)
    (hA : lower A) (i j : Fin m) (hij : i < j) (x : Fin m → R) :
    row A i (updateCoordinate A j x) = row A i x := by
  apply Finset.sum_congr rfl
  intro k _
  by_cases hkj : k = j
  · subst k
    simp [hA i j hij]
  · simp [updateCoordinate, Function.update_of_ne hkj]

def descending (A : Matrix (Fin m) (Fin m) R) :
    (n : ℕ) → n ≤ m → (Fin m → R) → (Fin m → R)
  | 0, _, x => x
  | n + 1, hn, x => descending A n (by omega)
      (updateCoordinate A ⟨n, by omega⟩ x)

theorem descending_correct (A : Matrix (Fin m) (Fin m) R) (hA : lower A)
    (n : ℕ) (hn : n ≤ m) (x : Fin m → R) (j : Fin m) :
    descending A n hn x j = if j.val < n then row A j x else x j := by
  induction n generalizing x with
  | zero => simp [descending]
  | succ n ih =>
    let i : Fin m := ⟨n, by omega⟩
    change descending A n _ (updateCoordinate A i x) j = _
    rw [ih]
    by_cases hj : j.val < n
    · have hji : j < i := hj
      rw [if_pos hj, row_unchanged_by_later_update A hA j i hji]
      simp only [if_pos (show j.val < n + 1 by omega)]
    · rw [if_neg hj]
      by_cases heq : j = i
      · subst j
        simp [updateCoordinate, i]
      · have hval : j.val ≠ n := by
          intro h
          apply heq
          exact Fin.ext h
        have hge : ¬j.val < n + 1 := by omega
        simp [hge, updateCoordinate, Function.update_of_ne heq]

def execute (A : Matrix (Fin m) (Fin m) R) (x : Fin m → R) : Fin m → R :=
  descending A m (Nat.le_refl m) x

/-- The actual descending program realizes the specified matrix on every input. -/
theorem execute_eq_mulVec (A : Matrix (Fin m) (Fin m) R) (hA : lower A)
    (x : Fin m → R) : execute A x = A *ᵥ x := by
  funext j
  rw [execute, descending_correct A hA, if_pos j.isLt]
  rfl

/-- The update reads only earlier coordinates and its own old coordinate. -/
theorem update_depends_only_on_prefix (A : Matrix (Fin m) (Fin m) R)
    (hA : lower A) (i : Fin m) (x y : Fin m → R)
    (hxy : ∀ j, j ≤ i → x j = y j) : row A i x = row A i y := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j ≤ i
  · rw [hxy j hji]
  · have hij : i < j := lt_of_not_ge hji
    simp [hA i j hij]

end CSL.TriangularProgram
end TriangularProgram

section TriangularStreams
/-! Global buffered coordinate changes. A single finite stream family serves all
prefixes, so the I/O bound contains no per-prefix startup term. -/

namespace CSL.TriangularStreams

open AffineStreams BucketMachine BucketReader SequentialArithmetic

variable {P Q S K : ℕ}

abbrev TripleAddress (P Q S : ℕ) := Fin P × Fin Q × Fin S

def tripleEncode : TripleAddress P Q S ≃ Fin (P * (Q * S)) :=
  (Equiv.prodCongr (Equiv.refl (Fin P)) finProdFinEquiv).trans finProdFinEquiv

@[simp] theorem tripleEncode_val (x : TripleAddress P Q S) :
    (tripleEncode x).val = x.2.2.val + S * x.2.1.val + (Q * S) * x.1.val := rfl

/-- The ordinary mixed-radix encoding orders the three fields lexicographically. -/
theorem pairEncode_lt_iff {A B : ℕ} (x y : Fin A × Fin B) :
    finProdFinEquiv x < finProdFinEquiv y ↔
      x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2) := by
  have hxb := x.2.isLt
  have hyb := y.2.isLt
  change x.2.val + B * x.1.val < y.2.val + B * y.1.val ↔ _
  constructor
  · intro h
    by_cases hp : x.1 < y.1
    · exact Or.inl hp
    · right
      have heq : x.1 = y.1 := by
        apply Fin.ext
        have hle : y.1.val ≤ x.1.val := Nat.le_of_not_gt hp
        by_contra hne
        have hstrict : y.1.val + 1 ≤ x.1.val := by omega
        have hm := Nat.mul_le_mul_left B hstrict
        rw [Nat.mul_add, Nat.mul_one] at hm
        omega
      exact ⟨heq, by simpa [heq] using h⟩
  · rintro (hp | ⟨heq, hs⟩)
    · have hm := Nat.mul_le_mul_left B (show x.1.val + 1 ≤ y.1.val from hp)
      rw [Nat.mul_add, Nat.mul_one] at hm
      omega
    · simpa [heq] using hs

theorem tripleEncode_lt_iff (x y : TripleAddress P Q S) :
    tripleEncode x < tripleEncode y ↔
      x.1 < y.1 ∨ (x.1 = y.1 ∧
        (x.2.1 < y.2.1 ∨ (x.2.1 = y.2.1 ∧ x.2.2 < y.2.2))) := by
  change finProdFinEquiv (x.1, finProdFinEquiv x.2) <
    finProdFinEquiv (y.1, finProdFinEquiv y.2) ↔ _
  rw [pairEncode_lt_iff, pairEncode_lt_iff]

def fieldEquiv (e : Fin P → Equiv.Perm (Fin Q)) : Equiv.Perm (TripleAddress P Q S) where
  toFun x := (x.1, e x.1 x.2.1, x.2.2)
  invFun x := (x.1, (e x.1).symm x.2.1, x.2.2)
  left_inv x := by simp
  right_inv x := by simp

def globalFieldEquiv (e : Fin P → Equiv.Perm (Fin Q)) :
    Equiv.Perm (Fin (P * (Q * S))) :=
  tripleEncode.symm.trans ((fieldEquiv e).trans tripleEncode)

def globalKey (key : Fin P → Fin Q → Fin K) (x : Fin (P * (Q * S))) : Fin K :=
  key (tripleEncode.symm x).1 (tripleEncode.symm x).2.1

@[simp] theorem globalFieldEquiv_encoded (e : Fin P → Equiv.Perm (Fin Q))
    (x : TripleAddress P Q S) :
    globalFieldEquiv e (tripleEncode x) = tripleEncode (x.1, e x.1 x.2.1, x.2.2) := by
  simp [globalFieldEquiv, fieldEquiv]

@[simp] theorem globalKey_encoded (key : Fin P → Fin Q → Fin K)
    (x : TripleAddress P Q S) : globalKey key (tripleEncode x) = key x.1 x.2.1 := by
  simp [globalKey]

/-- Prefix and suffix do not create additional streams. -/
theorem global_increasing_streams (e : Fin P → Equiv.Perm (Fin Q))
    (key : Fin P → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y) :
    ∀ x y : Fin (P * (Q * S)), x < y → globalKey key x = globalKey key y →
      globalFieldEquiv e x < globalFieldEquiv e y := by
  intro x y hxy hk
  obtain ⟨x, rfl⟩ := tripleEncode.surjective x
  obtain ⟨y, rfl⟩ := tripleEncode.surjective y
  simp only [globalKey_encoded] at hk
  rw [globalFieldEquiv_encoded, globalFieldEquiv_encoded, tripleEncode_lt_iff]
  rcases (tripleEncode_lt_iff x y).mp hxy with hp | ⟨hp, hfield⟩
  · exact Or.inl hp
  · right
    refine ⟨hp, ?_⟩
    rcases hfield with hc | ⟨hc, hs⟩
    · left
      have hy : e x.1 y.2.1 = e y.1 y.2.1 := by rw [hp]
      rw [← hy]
      apply hinc x.1 x.2.1 y.2.1 hc
      simpa [hp] using hk
    · right
      exact ⟨by rw [hp, hc], hs⟩

/-- One global execution, not a separate call for each prefix. -/
theorem global_reconstruction (e : Fin P → Equiv.Perm (Fin Q))
    (key : Fin P → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule ((targetSources (globalFieldEquiv (S := S) e)).map (globalKey key))
        (initialReaders (globalKey key) B (List.finRange (P * (Q * S)))) =
        some (targetSources (globalFieldEquiv e), final) ∧
      completeTransfers (globalKey key) B hB (List.finRange (P * (Q * S)))
        (targetSources (globalFieldEquiv e)) final ≤
        4 * ((P * (Q * S)) / B) + 2 * K + 2 ∧ occupiedReaders final ≤ K * B :=
  increasing_stream_reconstruction (globalFieldEquiv e) (globalKey key)
    (global_increasing_streams e key hinc) B hB

/-- Fixed multiplication in one field, across all prefixes and suffixes. -/
theorem global_multiplication_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (B : ℕ) (hB : 0 < B) :
    let e : Fin P → Equiv.Perm (Fin Q) := fun _ => multiplicationEquiv hQ hcoprime
    let key := fun (_ : Fin P) => multiplicationRun ha hQ
    ∃ final, readSchedule ((targetSources (globalFieldEquiv (S := S) e)).map (globalKey key))
        (initialReaders (globalKey key) B (List.finRange (P * (Q * S)))) =
        some (targetSources (globalFieldEquiv e), final) ∧
      completeTransfers (globalKey key) B hB (List.finRange (P * (Q * S)))
        (targetSources (globalFieldEquiv e)) final ≤
        4 * ((P * (Q * S)) / B) + 2 * a + 2 ∧ occupiedReaders final ≤ a * B := by
  try dsimp only
  apply global_reconstruction _ _ _ B hB
  exact fun _ x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr

/-- The offset may depend arbitrarily on the entire prefix; K remains exactly 2. -/
theorem global_addition_reconstruction (offset : Fin P → Fin Q)
    (B : ℕ) (hB : 0 < B) :
    let e := fun p => additionEquiv (offset p)
    let key := fun p => additionRun (offset p)
    ∃ final, readSchedule ((targetSources (globalFieldEquiv (S := S) e)).map (globalKey key))
        (initialReaders (globalKey key) B (List.finRange (P * (Q * S)))) =
        some (targetSources (globalFieldEquiv e), final) ∧
      completeTransfers (globalKey key) B hB (List.finRange (P * (Q * S)))
        (targetSources (globalFieldEquiv e)) final ≤
        4 * ((P * (Q * S)) / B) + 6 ∧ occupiedReaders final ≤ 2 * B := by
  try dsimp only
  apply global_reconstruction _ _ _ B hB
  exact fun p x y hxy hr => addition_increasing_in_run (offset p) x y hxy hr

/-- The inverse of a fixed multiplier also has one global a-stream execution. -/
theorem global_inverse_multiplication_reconstruction {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hcoprime : a.Coprime Q) (B : ℕ) (hB : 0 < B) :
    let e := multiplicationEquiv hQ hcoprime
    let maps := fun (_ : Fin P) => e.symm
    let key := fun (_ : Fin P) x => multiplicationRun ha hQ (e.symm x)
    ∃ final, readSchedule ((targetSources (globalFieldEquiv (S := S) maps)).map (globalKey key))
        (initialReaders (globalKey key) B (List.finRange (P * (Q * S)))) =
        some (targetSources (globalFieldEquiv maps), final) ∧
      completeTransfers (globalKey key) B hB (List.finRange (P * (Q * S)))
        (targetSources (globalFieldEquiv maps)) final ≤
        4 * ((P * (Q * S)) / B) + 2 * a + 2 ∧ occupiedReaders final ≤ a * B := by
  try dsimp only
  apply global_reconstruction _ _ _ B hB
  intro p
  apply inverse_increasing_streams
  exact fun x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr

/-- Payload movement for an entire address space, with no repeated-prefix cost. -/
theorem global_payload_reconstruction (e : Fin P → Equiv.Perm (Fin Q))
    (key : Fin P → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    {Value : Type*} (F : Fin (P * (Q * S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule
        ((targetRecords (globalFieldEquiv e) F).map (fun x => globalKey key x.1))
        (initialReaders (fun x => globalKey key x.1) B (inputRecords F)) =
        some (targetRecords (globalFieldEquiv e) F, final) ∧
      completeTransfers (fun x => globalKey key x.1) B hB (inputRecords F)
        (targetRecords (globalFieldEquiv e) F) final ≤
        4 * ((P * (Q * S)) / B) + 2 * K + 2 ∧ occupiedReaders final ≤ K * B :=
  payload_reconstruction (globalFieldEquiv e) (globalKey key)
    (global_increasing_streams e key hinc) F B hB

section CommonLayout

variable {m : ℕ}

/-- The common physical address order for every coordinate pass is lexicographic. -/
noncomputable def lexLayout : (Fin m → Fin Q) ≃ Fin (Q ^ m) :=
  toLex.trans (Fintype.orderIsoFinOfCardEq (Lex (Fin m → Fin Q))
    (by simp)).symm.toEquiv

@[simp] theorem lexLayout_lt (x y : Fin m → Fin Q) :
    lexLayout x < lexLayout y ↔ Pi.Lex (· < ·) (· < ·) x y := by
  exact (Fintype.orderIsoFinOfCardEq (Lex (Fin m → Fin Q))
    (by simp : Fintype.card (Lex (Fin m → Fin Q)) = Q ^ m)).symm.lt_iff_lt

/-- A field operation is permitted to depend on the preceding coordinates. -/
abbrev PrefixDependent {α : Type*} (i : Fin m) (f : (Fin m → Fin Q) → α) : Prop :=
  ∀ x y, (∀ j, j < i → x j = y j) → f x = f y

theorem prefixDependent_update {α : Type*} (i : Fin m)
    (f : (Fin m → Fin Q) → α) (hf : PrefixDependent i f)
    (x : Fin m → Fin Q) (v : Fin Q) : f (Function.update x i v) = f x := by
  apply hf
  intro j hj
  exact Function.update_of_ne (ne_of_lt hj) _ _

/-- A prefix-controlled field bijection, preserving every other coordinate. -/
def coordinateEquiv (i : Fin m) (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q))
    (he : PrefixDependent i e) : Equiv.Perm (Fin m → Fin Q) where
  toFun x := Function.update x i (e x (x i))
  invFun x := Function.update x i ((e x).symm (x i))
  left_inv x := by
    try dsimp only
    rw [prefixDependent_update i e he, Function.update_self, Equiv.symm_apply_apply]
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Function.update_of_ne hji]
  right_inv x := by
    try dsimp only
    rw [prefixDependent_update i e he, Function.update_self, Equiv.apply_symm_apply]
    ext j
    by_cases hji : j = i
    · subst j; simp
    · simp [Function.update_of_ne hji]

/-- Changing one coordinate does not disturb lexicographic order inside a stream. -/
theorem coordinate_increasing_streams (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e)
    (key : (Fin m → Fin Q) → Fin Q → Fin K) (hk : PrefixDependent i key)
    (hinc : ∀ x a b, a < b → key x a = key x b → e x a < e x b)
    (x y : Fin m → Fin Q) (hxy : Pi.Lex (· < ·) (· < ·) x y)
    (hkey : key x (x i) = key y (y i)) :
    Pi.Lex (· < ·) (· < ·) (coordinateEquiv i e he x) (coordinateEquiv i e he y) := by
  rcases hxy with ⟨j, hpre, hj⟩
  change Pi.Lex (· < ·) (· < ·) (Function.update x i (e x (x i)))
    (Function.update y i (e y (y i)))
  rcases lt_trichotomy j i with hji | hji | hij
  · refine ⟨j, ?_, ?_⟩
    · intro k hkj
      simp only [Function.update_of_ne (ne_of_lt (hkj.trans hji))]
      exact hpre k hkj
    · simpa only [Function.update_of_ne (ne_of_lt hji)] using hj
  · subst j
    have heq : e x = e y := he x y hpre
    have hkq : key x = key y := hk x y hpre
    refine ⟨i, ?_, ?_⟩
    · intro k hki
      simpa only [Function.update_of_ne (ne_of_lt hki)] using hpre k hki
    · simp only [Function.update_self]
      rw [← heq]
      apply hinc x _ _ hj
      simpa only [hkq] using hkey
  · have hp : ∀ k, k < i → x k = y k := fun k hki => hpre k (hki.trans hij)
    have heq : e x = e y := he x y hp
    have hiq : x i = y i := hpre i hij
    refine ⟨j, ?_, ?_⟩
    · intro k hkj
      by_cases hki : k = i
      · subst k; simp only [Function.update_self, heq, hiq]
      · simpa only [Function.update_of_ne hki] using hpre k hkj
    · simpa only [Function.update_of_ne (ne_of_gt hij)] using hj

noncomputable def coordinatePermutation (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e) :
    Equiv.Perm (Fin (Q ^ m)) :=
  lexLayout.symm.trans ((coordinateEquiv i e he).trans lexLayout)

noncomputable def coordinateKey (i : Fin m)
    (key : (Fin m → Fin Q) → Fin Q → Fin K) (a : Fin (Q ^ m)) : Fin K :=
  key (lexLayout.symm a) (lexLayout.symm a i)

theorem coordinatePermutation_increasing (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e)
    (key : (Fin m → Fin Q) → Fin Q → Fin K) (hk : PrefixDependent i key)
    (hinc : ∀ x a b, a < b → key x a = key x b → e x a < e x b) :
    ∀ x y, x < y → coordinateKey i key x = coordinateKey i key y →
      coordinatePermutation i e he x < coordinatePermutation i e he y := by
  intro x y hxy hkey
  obtain ⟨x, rfl⟩ := lexLayout.surjective x
  obtain ⟨y, rfl⟩ := lexLayout.surjective y
  simp only [coordinatePermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [lexLayout_lt]
  apply coordinate_increasing_streams i e he key hk hinc x y
    ((lexLayout_lt x y).mp hxy)
  simpa only [coordinateKey, Equiv.symm_apply_apply] using hkey

@[simp] theorem coordinatePermutation_encoded (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e)
    (x : Fin m → Fin Q) : coordinatePermutation i e he (lexLayout x) =
      lexLayout (Function.update x i (e x (x i))) := by
  simp [coordinatePermutation, coordinateEquiv]

/-- The stored words are only payloads; public counters provide stream indices. -/
theorem coordinate_value_reconstruction (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e)
    (key : (Fin m → Fin Q) → Fin Q → Fin K) (hk : PrefixDependent i key)
    (hinc : ∀ x a b, a < b → key x a = key x b → e x a < e x b)
    {Value : Type*} (F : Fin (Q ^ m) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final,
      TagErasure.readIndexed
        (fun y => coordinateKey i key ((coordinatePermutation i e he).symm y))
        (Q ^ m) 0 (by omega) (TagErasure.valueReaders (coordinateKey i key) F B) =
        some (TagErasure.outputValues (coordinatePermutation i e he) F, final) ∧
      TagErasure.valueTransfers (coordinatePermutation i e he) (coordinateKey i key)
        F B hB final ≤ 4 * (Q ^ m / B) + 2 * K + 2 ∧
      occupiedReaders final ≤ K * B :=
  TagErasure.increasing_value_reconstruction _ _
    (coordinatePermutation_increasing i e he key hk hinc) F B hB

/-- A fixed positive multiplier costs only a streams over the complete vector file. -/
theorem multiplication_coordinate_value {a : ℕ} (ha : 0 < a) (hQ : 0 < Q)
    (hc : a.Coprime Q) (i : Fin m)
    {Value : Type*} (F : Fin (Q ^ m) → Value) (B : ℕ) (hB : 0 < B) :
    let e := fun (_ : Fin m → Fin Q) => multiplicationEquiv hQ hc
    let key := fun (_ : Fin m → Fin Q) => multiplicationRun ha hQ
    ∃ final,
      TagErasure.readIndexed
        (fun y => coordinateKey i key ((coordinatePermutation i e (fun _ _ _ => rfl)).symm y))
        (Q ^ m) 0 (by omega) (TagErasure.valueReaders (coordinateKey i key) F B) =
        some (TagErasure.outputValues (coordinatePermutation i e (fun _ _ _ => rfl)) F, final) ∧
      TagErasure.valueTransfers (coordinatePermutation i e (fun _ _ _ => rfl))
        (coordinateKey i key) F B hB final ≤ 4 * (Q ^ m / B) + 2 * a + 2 ∧
      occupiedReaders final ≤ a * B := by
  try dsimp only
  apply coordinate_value_reconstruction i _ _ _ (fun _ _ _ => rfl) _ F B hB
  exact fun _ x y hxy hr => multiplication_increasing_in_run ha hQ x y hxy hr

/-- Prefix-dependent addition costs two streams in every coordinate of this layout. -/
theorem addition_coordinate_value (i : Fin m) (offset : (Fin m → Fin Q) → Fin Q)
    (hoffset : PrefixDependent i offset)
    {Value : Type*} (F : Fin (Q ^ m) → Value) (B : ℕ) (hB : 0 < B) :
    let e := fun x => additionEquiv (offset x)
    let he : PrefixDependent i e := fun x y hp => congrArg additionEquiv (hoffset x y hp)
    let key := fun x => additionRun (offset x)
    ∃ final,
      TagErasure.readIndexed
        (fun y => coordinateKey i key ((coordinatePermutation i e he).symm y))
        (Q ^ m) 0 (by omega) (TagErasure.valueReaders (coordinateKey i key) F B) =
        some (TagErasure.outputValues (coordinatePermutation i e he) F, final) ∧
      TagErasure.valueTransfers (coordinatePermutation i e he) (coordinateKey i key)
        F B hB final ≤ 4 * (Q ^ m / B) + 6 ∧ occupiedReaders final ≤ 2 * B := by
  try dsimp only
  apply coordinate_value_reconstruction i _ _ _ _ _ F B hB
  · intro x y hp
    exact congrArg additionRun (hoffset x y hp)
  · exact fun x a b hab hr => addition_increasing_in_run (offset x) a b hab hr

/-- An actual global buffered execution for a coordinate pass, always in the same layout. -/
theorem coordinate_reconstruction (i : Fin m)
    (e : (Fin m → Fin Q) → Equiv.Perm (Fin Q)) (he : PrefixDependent i e)
    (key : (Fin m → Fin Q) → Fin Q → Fin K) (hk : PrefixDependent i key)
    (hinc : ∀ x a b, a < b → key x a = key x b → e x a < e x b)
    {Value : Type*} (F : Fin (Q ^ m) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final, readSchedule
        ((targetRecords (coordinatePermutation i e he) F).map
          (fun x => coordinateKey i key x.1))
        (initialReaders (fun x => coordinateKey i key x.1) B (inputRecords F)) =
        some (targetRecords (coordinatePermutation i e he) F, final) ∧
      completeTransfers (fun x => coordinateKey i key x.1) B hB (inputRecords F)
        (targetRecords (coordinatePermutation i e he) F) final ≤
        4 * (Q ^ m / B) + 2 * K + 2 ∧ occupiedReaders final ≤ K * B := by
  apply payload_reconstruction _ _ _ F B hB
  intro x y hxy hkey
  obtain ⟨x, rfl⟩ := lexLayout.surjective x
  obtain ⟨y, rfl⟩ := lexLayout.surjective y
  simp only [coordinatePermutation, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [lexLayout_lt]
  apply coordinate_increasing_streams i e he key hk hinc x y
    ((lexLayout_lt x y).mp hxy)
  simpa only [coordinateKey, Equiv.symm_apply_apply] using hkey

end CommonLayout

section MatrixProgram

open scoped BigOperators Matrix

variable {R : Type*} [CommRing R] {m : ℕ}

/-- Only the strictly earlier coordinates enter the offset. -/
def prefixOffset (A : Matrix (Fin m) (Fin m) R) (i : Fin m) (x : Fin m → R) : R :=
  ∑ j, if j < i then A i j * x j else 0

theorem row_eq_scale_add_prefix (A : Matrix (Fin m) (Fin m) R)
    (hA : TriangularProgram.lower A) (i : Fin m) (x : Fin m → R) :
    TriangularProgram.row A i x = A i i * x i + prefixOffset A i x := by
  have hterm (j : Fin m) : A i j * x j =
      (if j = i then A i i * x i else 0) + (if j < i then A i j * x j else 0) := by
    rcases lt_trichotomy j i with hlt | heq | hgt
    · simp [ne_of_lt hlt, hlt]
    · subst j; simp
    · simp [ne_of_gt hgt, not_lt_of_gt hgt, hA i j hgt]
  unfold TriangularProgram.row
  calc
    (∑ j, A i j * x j) = ∑ j, ((if j = i then A i i * x i else 0) +
        (if j < i then A i j * x j else 0)) := Finset.sum_congr rfl (fun j _ => hterm j)
    _ = A i i * x i + prefixOffset A i x := by
      rw [Finset.sum_add_distrib]
      simp [prefixOffset]

theorem prefixOffset_unchanged_by_update (A : Matrix (Fin m) (Fin m) R)
    (i : Fin m) (x : Fin m → R) (value : R) :
    prefixOffset A i (Function.update x i value) = prefixOffset A i x := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j < i
  · simp [hji, Function.update_of_ne (ne_of_lt hji)]
  · simp [hji]

theorem prefixOffset_depends_only_on_prefix (A : Matrix (Fin m) (Fin m) R)
    (i : Fin m) (x y : Fin m → R) (hxy : ∀ j, j < i → x j = y j) :
    prefixOffset A i x = prefixOffset A i y := by
  apply Finset.sum_congr rfl
  intro j _
  by_cases hji : j < i
  · simp [hji, hxy j hji]
  · simp [hji]

def scaleCoordinate (a : R) (i : Fin m) (x : Fin m → R) : Fin m → R :=
  Function.update x i (a * x i)

def addPrefixCoordinate (A : Matrix (Fin m) (Fin m) R) (i : Fin m)
    (x : Fin m → R) : Fin m → R := Function.update x i (x i + prefixOffset A i x)

/-- The actual scalar multiplication followed by prefix-dependent addition
is exactly the row update used by the established descending matrix program. -/
theorem scalar_steps_eq_update (A : Matrix (Fin m) (Fin m) R)
    (hA : TriangularProgram.lower A) (i : Fin m) (x : Fin m → R) :
    addPrefixCoordinate A i (scaleCoordinate (A i i) i x) =
      TriangularProgram.updateCoordinate A i x := by
  unfold addPrefixCoordinate scaleCoordinate TriangularProgram.updateCoordinate
  rw [prefixOffset_unchanged_by_update]
  rw [Function.update_self]
  ext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self]
    exact (row_eq_scale_add_prefix A hA i x).symm
  · simp [Function.update_of_ne hji]

/-- A concrete scalar-primitive program, applied from coordinate m-1 down to 0. -/
def scalarDescending (A : Matrix (Fin m) (Fin m) R) :
    (n : ℕ) → n ≤ m → (Fin m → R) → (Fin m → R)
  | 0, _, x => x
  | n + 1, hn, x => scalarDescending A n (by omega)
      (addPrefixCoordinate A ⟨n, by omega⟩ (scaleCoordinate (A ⟨n, by omega⟩ ⟨n, by omega⟩)
        ⟨n, by omega⟩ x))

theorem scalarDescending_eq (A : Matrix (Fin m) (Fin m) R)
    (hA : TriangularProgram.lower A) (n : ℕ) (hn : n ≤ m) (x : Fin m → R) :
    scalarDescending A n hn x = TriangularProgram.descending A n hn x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [scalarDescending, TriangularProgram.descending]
    rw [scalar_steps_eq_update A hA]
    exact ih _ _

/-- All scalar primitives together compute the full lower-triangular matrix. -/
theorem scalarProgram_eq_mulVec (A : Matrix (Fin m) (Fin m) R)
    (hA : TriangularProgram.lower A) (x : Fin m → R) :
    scalarDescending A m (Nat.le_refl m) x = A.mulVec x := by
  rw [scalarDescending_eq A hA]
  exact TriangularProgram.execute_eq_mulVec A hA x

end MatrixProgram

end CSL.TriangularStreams
end TriangularStreams


