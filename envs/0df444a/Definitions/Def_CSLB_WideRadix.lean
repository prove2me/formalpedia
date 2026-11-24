-- Prove2me | Definitions.Def_CSLB_WideRadix
-- name    : CSLB_WideRadix
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:14:38.184795+00:00
-- url     : https://prove2.me/theorems/8b4cdc27-7012-42ec-913e-7ba8073f1301
-- title:
--   Coded sorting bridge: WideRadix
-- statement:
--   # Least-significant-bit radix sort on the two-word machine (wide words)
--
--   When every index `< n` fits in one word (`n ≤ 2^w`), a stable partition by one bit needs only
--   single-word cursors. For each bit `b = 0, …, w-1` the program counts the records whose bit `b`
--   is zero, scatters the records into a second array with two cursors, and copies the array back.
--   All commands, and hence the position in the program, are fixed by `(n, w)`; addresses depend on
--   the two resident words only. Disk cells: `0` zero count, `1` and `2` cursors, `3 + i` the array,
--   `3 + n + i` the buffer.
--
--   Part of the bridge from the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 to the platform model `CodedSorting_Machine` of the external-memory machine, used to prove Theorem 3.1.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, Theorem 3.1 (p.4) and Appendix D (p.39)

import Definitions.Def_CSL_Sorting_SmallMemory_NarrowWords_PublicUnrolledComplete

/-! # Least-significant-bit radix sort on the two-word machine (wide words)

When every index `< n` fits in one word (`n ≤ 2^w`), a stable partition by one bit needs only
single-word cursors. For each bit `b = 0, …, w-1` the program counts the records whose bit `b`
is zero, scatters the records into a second array with two cursors, and copies the array back.
All commands, and hence the position in the program, are fixed by `(n, w)`; addresses depend on
the two resident words only. Disk cells: `0` zero count, `1` and `2` cursors, `3 + i` the array,
`3 + n + i` the buffer. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace CSLB.WideRadix
open CSL CSL.TwoWordPhysicalAddresses CSL.TwoWordGeneralCounter

section ListLevel
variable {w : ℕ}

def zeroP (b : ℕ) (x : Word w) : Bool := !x.val.testBit b
def oneP (b : ℕ) (x : Word w) : Bool := x.val.testBit b

/-- Stable partition by bit `b`: records with bit `b` clear first. -/
def partitionBit (b : ℕ) (L : List (Word w)) : List (Word w) :=
  L.filter (zeroP b) ++ L.filter (oneP b)

/-- Apply the partitions for bits `0, …, b-1` in turn. -/
def radixList : ℕ → List (Word w) → List (Word w)
  | 0, L => L
  | b + 1, L => partitionBit b (radixList b L)

def low (b : ℕ) (x : Word w) : ℕ := x.val % 2 ^ b

theorem low_succ (b : ℕ) (x : Word w) :
    low (b + 1) x = (if x.val.testBit b then 2 ^ b else 0) + low b x := by
  unfold low
  rw [Nat.mod_pow_succ, Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x.val / 2 ^ b) with h | h <;> simp [h] <;> ring

theorem partitionBit_perm (b : ℕ) (L : List (Word w)) : (partitionBit b L).Perm L := by
  have h := List.filter_append_perm (zeroP b) L
  have he : (fun x => !zeroP b x) = oneP (w := w) b := by
    funext x; simp [zeroP, oneP]
  rw [he] at h
  exact h

theorem radixList_perm (b : ℕ) (L : List (Word w)) : (radixList b L).Perm L := by
  induction b with
  | zero => exact List.Perm.refl _
  | succ b ih => exact (partitionBit_perm b _).trans ih

theorem radixList_length (b : ℕ) (L : List (Word w)) : (radixList b L).length = L.length :=
  (radixList_perm b L).length_eq

theorem partitionBit_low (b : ℕ) (L : List (Word w))
    (hL : L.Pairwise (fun x y => low b x ≤ low b y)) :
    (partitionBit b L).Pairwise (fun x y => low (b + 1) x ≤ low (b + 1) y) := by
  unfold partitionBit
  rw [List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.pairwise_filter]
    refine hL.imp ?_
    intro x y hxy hzx hzy
    have hx : x.val.testBit b = false := by simpa [zeroP] using hzx
    have hy : y.val.testBit b = false := by simpa [zeroP] using hzy
    rw [low_succ, low_succ, hx, hy]
    simpa using hxy
  · rw [List.pairwise_filter]
    refine hL.imp ?_
    intro x y hxy hzx hzy
    have hx : x.val.testBit b = true := by simpa [oneP] using hzx
    have hy : y.val.testBit b = true := by simpa [oneP] using hzy
    rw [low_succ, low_succ, hx, hy]
    simpa using hxy
  · intro x hx y hy
    have hx' : x.val.testBit b = false := by
      have := (List.mem_filter.mp hx).2; simpa [zeroP] using this
    have hy' : y.val.testBit b = true := by
      have := (List.mem_filter.mp hy).2; simpa [oneP] using this
    rw [low_succ, low_succ, hx', hy']
    have : low b x < 2 ^ b := Nat.mod_lt _ (by positivity)
    simp only [Bool.false_eq_true, if_false, if_true, zero_add]
    omega

theorem radixList_low (b : ℕ) (L : List (Word w)) :
    (radixList b L).Pairwise (fun x y => low b x ≤ low b y) := by
  induction b with
  | zero =>
    simp only [radixList, low, pow_zero, Nat.mod_one, le_refl]
    first
    | exact List.pairwise_of_forall (fun _ _ => trivial)
    | exact List.pairwise_of_forall (fun _ _ => le_refl 0)
  | succ b ih => exact partitionBit_low b _ ih

theorem radixList_sorted (L : List (Word w)) :
    (radixList w L).Pairwise (fun x y => x.val ≤ y.val) := by
  refine (radixList_low w L).imp ?_
  intro x y h
  simpa [low, Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using h

end ListLevel

section Machine
variable (w : ℕ) (hw : 0 < w) (n : ℕ)

def oneW : Word w := ⟨1, Nat.one_lt_two_pow hw.ne'⟩

/-- `k mod 2^w` as a word. -/
def ofN (k : ℕ) : Word w := ⟨k % 2 ^ w, Nat.mod_lt _ (by positivity)⟩

theorem ofN_succ (k : ℕ) : ofN w k + oneW w hw = ofN w (k + 1) := by
  apply Fin.ext
  simp only [ofN, oneW, Fin.val_add]
  conv_rhs => rw [Nat.add_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow hw.ne')]

theorem ofN_val (k : ℕ) (hk : k < 2 ^ w) : (ofN w k).val = k := Nat.mod_eq_of_lt hk

theorem ofN_add_one (k : ℕ) : ofN w k + oneW w hw = ofN w (k + 1) := ofN_succ w hw k

/-- Cursor cell for a record: `1` when bit `b` is clear, `2` otherwise. -/
def cur (b : ℕ) (x : Word w) : ℕ := if x.val.testBit b then 2 else 1

def countOne (b i : ℕ) : List (Command (Word w)) :=
  [.readLeft (3 + i), .readRight 0,
   .localOp (fun r => (r.1, if r.1.val.testBit b then r.2 else r.2 + oneW w hw)),
   .writeRight (fun _ => 0)]

def countLoop (b : ℕ) : ℕ → List (Command (Word w))
  | 0 => []
  | i + 1 => countLoop b i ++ countOne w hw b i

def initCode : List (Command (Word w)) :=
  [.readRight 0, .writeRight (fun _ => 2), .localOp (fun r => (r.1, 0)), .writeRight (fun _ => 1)]

def scatterOne (b i : ℕ) : List (Command (Word w)) :=
  [.readLeft (3 + i), .readRightAt (fun r => cur w b r.1), .localOp (fun r => (r.2, r.1)),
   .writeRight (fun r => 3 + n + r.1.val), .localOp (fun r => (r.2, r.1 + oneW w hw)),
   .writeRight (fun r => cur w b r.1)]

def scatterLoop (b : ℕ) : ℕ → List (Command (Word w))
  | 0 => []
  | i + 1 => scatterLoop b i ++ scatterOne w hw n b i

def copyOne (i : ℕ) : List (Command (Word w)) :=
  [.readRight (3 + n + i), .writeRight (fun _ => 3 + i)]

def copyLoop : ℕ → List (Command (Word w))
  | 0 => []
  | i + 1 => copyLoop i ++ copyOne w n i

def passCode (b : ℕ) : List (Command (Word w)) :=
  [.localOp (fun r => (r.1, 0)), .writeRight (fun _ => 0)] ++ countLoop w hw b n ++
    initCode w ++ scatterLoop w hw n b n ++ copyLoop w n n

def sortCode : ℕ → List (Command (Word w))
  | 0 => []
  | b + 1 => sortCode b ++ passCode w hw n b

/-! Costs. -/

theorem countLoop_cost (b i : ℕ) : transfers (countLoop w hw b i) = 3 * i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [countLoop, transfers_append, ih]
    simp only [countOne, transfers, cost]; omega

theorem scatterLoop_cost (b i : ℕ) : transfers (scatterLoop w hw n b i) = 4 * i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [scatterLoop, transfers_append, ih]
    simp only [scatterOne, transfers, cost]; omega

theorem copyLoop_cost (i : ℕ) : transfers (copyLoop w n i) = 2 * i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [copyLoop, transfers_append, ih]
    simp only [copyOne, transfers, cost]; omega

theorem passCode_cost (b : ℕ) : transfers (passCode w hw n b) = 9 * n + 4 := by
  simp only [passCode, transfers_append, countLoop_cost, scatterLoop_cost, copyLoop_cost]
  simp only [initCode, transfers, cost]; omega

theorem sortCode_cost (b : ℕ) : transfers (sortCode w hw n b) = (9 * n + 4) * b := by
  induction b with
  | zero => rfl
  | succ b ih => rw [sortCode, transfers_append, ih, passCode_cost, Nat.mul_succ]

end Machine

/-! Correctness of one pass. -/

section Pass
variable (w : ℕ) (hw : 0 < w) (n : ℕ)

def zeros (b : ℕ) (L : List (Word w)) : ℕ := (L.filter (zeroP b)).length

/-- The array region `3, …, 3 + n - 1` holds `L`. -/
def Holds (disk : ℕ → Word w) (L : List (Word w)) : Prop :=
  ∀ i (hi : i < L.length), disk (3 + i) = L[i]

theorem count_step (b i : ℕ) (st : State (Word w)) :
    (execute (countOne w hw b i) st).disk =
      Function.update st.disk 0
        (if (st.disk (3 + i)).val.testBit b then st.disk 0 else st.disk 0 + oneW w hw) := by
  simp only [countOne, execute, step]
  congr 1

theorem countLoop_correct (b : ℕ) (L : List (Word w)) (st : State (Word w))
    (hA : Holds w st.disk L) (i : ℕ) (hi : i ≤ L.length) :
    (execute (countLoop w hw b i) st).disk 0 =
        st.disk 0 + ofN w (zeros w b (L.take i)) ∧
      ∀ a, a ≠ 0 → (execute (countLoop w hw b i) st).disk a = st.disk a := by
  induction i with
  | zero =>
    refine ⟨?_, fun a _ => rfl⟩
    apply Fin.ext
    simp [countLoop, execute, zeros, ofN, Fin.val_add]
  | succ i ih =>
    obtain ⟨h0, hfr⟩ := ih (by omega)
    rw [countLoop, execute_append, count_step]
    have hx : (execute (countLoop w hw b i) st).disk (3 + i) = L[i] := by
      rw [hfr _ (by omega)]; exact hA i (by omega)
    rw [hx, h0]
    refine ⟨?_, fun a ha => by rw [Function.update_of_ne ha, hfr a ha]⟩
    rw [Function.update_self]
    have htake : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem (by omega)
    simp only [zeros, htake, List.filter_append, List.length_append]
    by_cases hb : (L[i]).val.testBit b
    · simp [hb, zeroP]
    · simp only [hb, Bool.false_eq_true, if_false, zeroP, Bool.not_false, List.filter_cons_of_pos,
        List.filter_nil, List.length_singleton]
      rw [add_assoc, ofN_succ]

end Pass


section Scatter
variable (w : ℕ) (hw : 0 < w) (n : ℕ)

def ones (b : ℕ) (L : List (Word w)) : ℕ := (L.filter (oneP b)).length

theorem zeros_add_ones (b : ℕ) (L : List (Word w)) : zeros w b L + ones w b L = L.length := by
  have := (partitionBit_perm b L).length_eq
  simpa [partitionBit, zeros, ones] using this

theorem scatter_step (b i : ℕ) (st : State (Word w)) :
    (execute (scatterOne w hw n b i) st).disk =
      Function.update
        (Function.update st.disk (3 + n + (st.disk (cur w b (st.disk (3 + i)))).val)
          (st.disk (3 + i)))
        (cur w b (st.disk (3 + i)))
        (st.disk (cur w b (st.disk (3 + i))) + oneW w hw) := by
  simp [scatterOne, execute, step]

structure ScatInv (b : ℕ) (L : List (Word w)) (i : ℕ) (disk : ℕ → Word w) : Prop where
  holds : Holds w disk L
  c0 : disk 1 = ofN w (zeros w b (L.take i))
  c1 : disk 2 = ofN w (zeros w b L + ones w b (L.take i))
  bz : ∀ j (hj : j < ((L.take i).filter (zeroP b)).length),
    disk (3 + n + j) = ((L.take i).filter (zeroP b))[j]
  bo : ∀ j (hj : j < ((L.take i).filter (oneP b)).length),
    disk (3 + n + zeros w b L + j) = ((L.take i).filter (oneP b))[j]

theorem cur_ne (b : ℕ) (x : Word w) (a : ℕ) (ha : 3 ≤ a) : cur w b x ≠ a := by
  unfold cur; split_ifs <;> omega

theorem zeros_take_lt (b : ℕ) (L : List (Word w)) (i : ℕ) (hi : i < L.length)
    (hz : zeroP b L[i] = true) : zeros w b (L.take i) < zeros w b L := by
  have h1 : zeros w b (L.take (i + 1)) = zeros w b (L.take i) + 1 := by
    unfold zeros
    rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.length_append]
    simp [hz]
  have h2 : zeros w b (L.take (i + 1)) ≤ zeros w b L := by
    unfold zeros
    exact (List.take_sublist _ _).filter _ |>.length_le
  omega

theorem ones_take_lt (b : ℕ) (L : List (Word w)) (i : ℕ) (hi : i < L.length)
    (hz : oneP b L[i] = true) : ones w b (L.take i) < ones w b L := by
  have h1 : ones w b (L.take (i + 1)) = ones w b (L.take i) + 1 := by
    unfold ones
    rw [List.take_succ_eq_append_getElem hi, List.filter_append, List.length_append]
    simp [hz]
  have h2 : ones w b (L.take (i + 1)) ≤ ones w b L := by
    unfold ones
    exact (List.take_sublist _ _).filter _ |>.length_le
  omega

theorem filter_snoc_pos (p : Word w → Bool) (L : List (Word w)) (x : Word w) (h : p x = true) :
    (L ++ [x]).filter p = L.filter p ++ [x] := by
  rw [List.filter_append]; simp [h]

theorem filter_snoc_neg (p : Word w → Bool) (L : List (Word w)) (x : Word w) (h : p x = false) :
    (L ++ [x]).filter p = L.filter p := by
  rw [List.filter_append]; simp [h]

theorem scatter_inv_step (b : ℕ) (L : List (Word w)) (hn : L.length = n) (hcap : n ≤ 2 ^ w)
    (i : ℕ) (hi : i < n) (st : State (Word w)) (h : ScatInv w n b L i st.disk) :
    ScatInv w n b L (i + 1) (execute (scatterOne w hw n b i) st).disk := by
  rw [scatter_step]
  have hx : st.disk (3 + i) = L[i] := h.holds i (by omega)
  rw [hx]
  have htake : L.take (i + 1) = L.take i ++ [L[i]] := List.take_succ_eq_append_getElem (by omega)
  have hzo := zeros_add_ones w b L
  have hzle : zeros w b (L.take i) ≤ zeros w b L := by
    unfold zeros; exact ((List.take_sublist _ _).filter _).length_le
  have hole : ones w b (L.take i) ≤ ones w b L := by
    unfold ones; exact ((List.take_sublist _ _).filter _).length_le
  by_cases hb : (L[i]).val.testBit b
  · -- the record goes to the second group
    have hcur : cur w b L[i] = 2 := by simp [cur, hb]
    have hone : oneP b L[i] = true := by simp [oneP, hb]
    have hzero : zeroP b L[i] = false := by simp [zeroP, hb]
    have hlt := ones_take_lt w b L i (by omega) hone
    have hfz : (L.take (i + 1)).filter (zeroP b) = (L.take i).filter (zeroP b) := by
      rw [htake]; exact filter_snoc_neg w _ _ _ hzero
    have hfo : (L.take (i + 1)).filter (oneP b) = (L.take i).filter (oneP b) ++ [L[i]] := by
      rw [htake]; exact filter_snoc_pos w _ _ _ hone
    rw [hcur, h.c1]
    have hval : (ofN w (zeros w b L + ones w b (L.take i))).val =
        zeros w b L + ones w b (L.take i) := ofN_val w _ (by omega)
    rw [hval]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.holds j hj
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.c0]
      simp only [zeros, hfz]
    · rw [Function.update_self, ofN_add_one w hw]
      simp only [ones, hfo, List.length_append, List.length_singleton, Nat.add_assoc]
    · intro j hj
      simp only [hfz] at hj ⊢
      have hj2 : j < zeros w b L := lt_of_lt_of_le hj hzle
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.bz j hj
    · intro j hj
      simp only [hfo] at hj ⊢
      rw [Function.update_of_ne (by omega)]
      by_cases hje : j = ones w b (L.take i)
      · subst hje
        rw [show 3 + n + zeros w b L + ones w b (L.take i) =
            3 + n + (zeros w b L + ones w b (L.take i)) by omega, Function.update_self]
        rw [List.getElem_append_right (by unfold ones; exact le_refl _)]
        simp [ones]
      · have hj' : j < ((L.take i).filter (oneP b)).length := by
          simp only [List.length_append, List.length_singleton] at hj
          have he : ones w b (L.take i) = ((L.take i).filter (oneP b)).length := rfl
          omega
        rw [Function.update_of_ne (by omega), h.bo j hj',
          List.getElem_append_left hj']
  · -- the record goes to the first group
    have hb' : (L[i]).val.testBit b = false := by simpa using hb
    have hcur : cur w b L[i] = 1 := by simp [cur, hb']
    have hzero : zeroP b L[i] = true := by simp [zeroP, hb']
    have hone : oneP b L[i] = false := by simp [oneP, hb']
    have hlt := zeros_take_lt w b L i (by omega) hzero
    have hfz : (L.take (i + 1)).filter (zeroP b) = (L.take i).filter (zeroP b) ++ [L[i]] := by
      rw [htake]; exact filter_snoc_pos w _ _ _ hzero
    have hfo : (L.take (i + 1)).filter (oneP b) = (L.take i).filter (oneP b) := by
      rw [htake]; exact filter_snoc_neg w _ _ _ hone
    rw [hcur, h.c0]
    have hval : (ofN w (zeros w b (L.take i))).val = zeros w b (L.take i) :=
      ofN_val w _ (by omega)
    rw [hval]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.holds j hj
    · rw [Function.update_self, ofN_add_one w hw]
      simp only [zeros, hfz, List.length_append, List.length_singleton]
    · rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), h.c1]
      simp only [ones, hfo]
    · intro j hj
      simp only [hfz] at hj ⊢
      rw [Function.update_of_ne (by omega)]
      by_cases hje : j = zeros w b (L.take i)
      · subst hje
        rw [Function.update_self, List.getElem_append_right (by unfold zeros; exact le_refl _)]
        simp [zeros]
      · have hj' : j < ((L.take i).filter (zeroP b)).length := by
          simp only [List.length_append, List.length_singleton] at hj
          have he : zeros w b (L.take i) = ((L.take i).filter (zeroP b)).length := rfl
          omega
        rw [Function.update_of_ne (by omega), h.bz j hj',
          List.getElem_append_left hj']
    · intro j hj
      simp only [hfo] at hj ⊢
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h.bo j hj

theorem scatterLoop_inv (b : ℕ) (L : List (Word w)) (hn : L.length = n) (hcap : n ≤ 2 ^ w)
    (st : State (Word w)) (h : ScatInv w n b L 0 st.disk) (i : ℕ) (hi : i ≤ n) :
    ScatInv w n b L i (execute (scatterLoop w hw n b i) st).disk := by
  induction i with
  | zero => exact h
  | succ i ih =>
    rw [scatterLoop, execute_append]
    exact scatter_inv_step w hw n b L hn hcap i (by omega) _ (ih (by omega))

/-- After scattering all records the buffer holds the partition. -/
theorem scatter_result (b : ℕ) (L : List (Word w)) (hn : L.length = n) (disk : ℕ → Word w)
    (h : ScatInv w n b L n disk) :
    ∀ j (hj : j < (partitionBit b L).length), disk (3 + n + j) = (partitionBit b L)[j] := by
  have htk : L.take n = L := by rw [← hn]; exact List.take_length
  intro j hj
  unfold partitionBit at hj ⊢
  by_cases hjz : j < (L.filter (zeroP b)).length
  · rw [List.getElem_append_left hjz]
    have := h.bz j (by rw [htk]; exact hjz)
    simpa [htk] using this
  · rw [List.getElem_append_right (by omega)]
    have hj2 : j - (L.filter (zeroP b)).length < (L.filter (oneP b)).length := by
      simp only [List.length_append] at hj; omega
    have := h.bo (j - (L.filter (zeroP b)).length) (by rw [htk]; exact hj2)
    have he : 3 + n + zeros w b L + (j - (L.filter (zeroP b)).length) = 3 + n + j := by
      unfold zeros; omega
    rw [he] at this
    simpa [htk] using this

theorem copy_step (i : ℕ) (st : State (Word w)) :
    (execute (copyOne w n i) st).disk =
      Function.update st.disk (3 + i) (st.disk (3 + n + i)) := by
  simp [copyOne, execute, step]

theorem copyLoop_correct (M : List (Word w)) (hM : M.length = n) (st : State (Word w))
    (hB : ∀ j (hj : j < M.length), st.disk (3 + n + j) = M[j]) (i : ℕ) (hi : i ≤ n) :
    (∀ j (hj : j < i), (execute (copyLoop w n i) st).disk (3 + j) = M[j]'(by omega)) ∧
    (∀ a, (a < 3 + i ∨ 3 + n ≤ a) → a < 3 ∨ 3 + n ≤ a →
      (execute (copyLoop w n i) st).disk a = st.disk a) := by
  induction i with
  | zero => exact ⟨fun j hj => absurd hj (by omega), fun a _ _ => rfl⟩
  | succ i ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [copyLoop, execute_append, copy_step]
    have hb : (execute (copyLoop w n i) st).disk (3 + n + i) = M[i]'(by omega) := by
      rw [h2 _ (Or.inr (by omega)) (Or.inr (by omega))]; exact hB i (by omega)
    refine ⟨?_, ?_⟩
    · intro j hj
      by_cases hje : j = i
      · subst hje; rw [Function.update_self, hb]
      · rw [Function.update_of_ne (by omega)]; exact h1 j (by omega)
    · intro a ha1 ha2
      rw [Function.update_of_ne (by omega)]
      exact h2 a (by omega) ha2

end Scatter


section SortSection
variable (w : ℕ) (hw : 0 < w) (n : ℕ)

theorem ofN_zero : ofN w 0 = (0 : Word w) := by
  apply Fin.ext; simp [ofN]

theorem pass_correct (b : ℕ) (L : List (Word w)) (hn : L.length = n) (hcap : n ≤ 2 ^ w)
    (st : State (Word w)) (hA : Holds w st.disk L) :
    Holds w (execute (passCode w hw n b) st).disk (partitionBit b L) := by
  unfold passCode
  simp only [execute_append]
  set s1 := execute [.localOp (fun r => (r.1, (0 : Word w))), .writeRight (fun _ => 0)] st with hs1
  have hs1d : s1.disk = Function.update st.disk 0 0 := by simp [hs1, execute, step]
  have hA1 : Holds w s1.disk L := by
    intro i hi; rw [hs1d, Function.update_of_ne (by omega)]; exact hA i hi
  obtain ⟨hc0, hcfr⟩ := countLoop_correct w hw b L s1 hA1 n (by omega)
  set s2 := execute (countLoop w hw b n) s1 with hs2
  have hZ : s2.disk 0 = ofN w (zeros w b L) := by
    rw [hc0, hs1d, Function.update_self, zero_add]
    rw [show L.take n = L by rw [← hn]; exact List.take_length]
  have hA2 : Holds w s2.disk L := by
    intro i hi; rw [hcfr _ (by omega)]; exact hA1 i hi
  set s3 := execute (initCode w) s2 with hs3
  have hs3d : s3.disk = Function.update (Function.update s2.disk 2 (s2.disk 0)) 1 0 := by
    simp [hs3, initCode, execute, step]
  have hinv : ScatInv w n b L 0 s3.disk := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [hs3d, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hA2 i hi
    · rw [hs3d, Function.update_self]; simp [zeros, ofN_zero]
    · rw [hs3d, Function.update_of_ne (by omega), Function.update_self, hZ]; simp [ones]
    · intro j hj; simp at hj
    · intro j hj; simp at hj
  have hsc := scatterLoop_inv w hw n b L hn hcap s3 hinv n le_rfl
  set s4 := execute (scatterLoop w hw n b n) s3 with hs4
  have hres := scatter_result w n b L hn s4.disk hsc
  have hlenP : (partitionBit b L).length = n := (partitionBit_perm b L).length_eq.trans hn
  obtain ⟨hcp, _⟩ := copyLoop_correct w n (partitionBit b L) hlenP s4 hres n le_rfl
  intro i hi
  exact hcp i (by omega)

theorem sort_correct (L : List (Word w)) (hn : L.length = n) (hcap : n ≤ 2 ^ w)
    (st : State (Word w)) (hA : Holds w st.disk L) (b : ℕ) :
    Holds w (execute (sortCode w hw n b) st).disk (radixList b L) := by
  induction b with
  | zero => exact hA
  | succ b ih =>
    rw [sortCode, execute_append]
    exact pass_correct w hw n b _ ((radixList_length b L).trans hn) hcap _ ih

/-- The wide-word core, in the format used by `PublicUnrolledBlockSort.complete` (offset `3`). -/
theorem core_correct (hcap : n ≤ 2 ^ w)
    (s : State (Word w)) (xs : List (Word w)) (hlen : xs.length = n)
    (hin : ∀ j : Fin xs.length, s.disk (3 + j.val) = xs.get j) :
    ∃ t cost, TwoWordRadixPreparedBuild.Executes [.straight (sortCode w hw n w)] s t cost ∧
      (∀ j : Fin (radixList w xs).length, t.disk (3 + j.val) = (radixList w xs).get j) ∧
      (radixList w xs).Perm xs ∧
      (radixList w xs).Pairwise (fun x y => x.val ≤ y.val) ∧ cost ≤ (9 * n + 4) * w := by
  refine ⟨execute (sortCode w hw n w) s, transfers (sortCode w hw n w), ?_, ?_,
    radixList_perm w xs, radixList_sorted xs, by rw [sortCode_cost]⟩
  · have h := TwoWordRadixPreparedBuild.Executes.straight (sortCode w hw n w) []
      s (execute (sortCode w hw n w) s) 0
      (TwoWordRadixPreparedBuild.Executes.done _)
    simpa using h
  · have hA : Holds w s.disk xs := fun i hi => hin ⟨i, hi⟩
    have h := sort_correct w hw n xs hlen hcap s hA w
    intro j
    exact h j.val j.isLt

end SortSection

end CSLB.WideRadix


