-- Prove2me | Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux
-- name    : BCFGJPSSV26_Greedy_Alg_MergeAux
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-13T16:58:28.164073+00:00
-- url     : https://prove2.me/theorems/c05aee7c-7249-4a6b-bfea-275a53fdac38
-- title:
--   BCFGJPSSV26.Greedy.Alg.MergeAux — Auxiliary lemmas for the merge
-- statement:
--   This is module `BCFGJPSSV26.Greedy.Alg.MergeAux` of the Lean 4 formalization of *A Better-than-2 Approximation for k-Median* by R.-D. Buhai, V. Cohen-Addad, H. Fleischmann, A. Gupta, A. Jubés Monforte, M. R. Pittu, M. Stouras, O. Svensson and L. Vogl (Part I: *The Power of General Bids*, [arXiv:2610.18144](https://arxiv.org/abs/2610.18144); Part II: *Stable Instances*, [arXiv:2610.17172](https://arxiv.org/abs/2610.17172)), from the repository [raresbuhai/formalization-of-my-research](https://github.com/raresbuhai/formalization-of-my-research) (formalized with Claude Code, Apache-2.0).
--
--   Generic facts used by `Greedy/Alg/Merge.lean`: sandwiches, the binary search, flips of a list of
--   counts, common prefixes, and the validity of the sequences the merge builds from valid ones
--   (deleting atoms, appending a free atom, replacing a free copy at offset `0` by its regular
--   facility).
--
--   **Contents.** The module is published as a whole: 92 declarations (definitions, structures, instances and their supporting lemmas, with proofs). Published as separate theorems, and therefore not in this file: `BCFGJPSSV26.Greedy.Ctx.MergeH.VS.append_free`, `BCFGJPSSV26.Greedy.Ctx.MergeH.VS.of_pairs`, `BCFGJPSSV26.Greedy.Ctx.MergeH.complete_sol_pre`, `BCFGJPSSV26.Greedy.Ctx.MergeH.noOver_pre`, `BCFGJPSSV26.Greedy.Ctx.MergeH.vs_completeSeq` (together with the auxiliary lemmas that depend on them).
--
--   **Formalization Note** The source is written for Lean v4.36.0-rc2; this copy is the same text compiled in the platform environment (Lean v4.33.1, Mathlib `0df444a`), with library lemmas renamed back to their names in this Mathlib and a few proof steps adjusted; no statement is changed. It uses Lean's module system (`module`, `public import`), so import it from a `module` file or an ordinary file as `import Definitions.Def_BCFGJPSSV26_Greedy_Alg_MergeAux`.
-- source:
--   https://github.com/raresbuhai/formalization-of-my-research/blob/7abf511c7e99fd3fec3ff245a2b8d616ae17bc2c/BCFGJPSSV26/Greedy/Alg/MergeAux.lean

module

public import Definitions.Def_BCFGJPSSV26_Greedy_Alg_Complete

set_option maxSynthPendingDepth 3

/- Prove2me definition bundle for `BCFGJPSSV26.Greedy.Alg.MergeAux` — generated mechanically from
   github.com/raresbuhai/formalization-of-my-research @ 7abf511 (Apache-2.0),
   backported to Lean v4.33.1 / Mathlib 0df444a. The theorems published as separate
   Prove2me theorems, and what depends on them, are removed from this file. -/
/-!
# Auxiliary lemmas for the merge

Generic facts used by `Greedy/Alg/Merge.lean`: sandwiches, the binary search, flips of a list of
counts, common prefixes, and the validity of the sequences the merge builds from valid ones
(deleting atoms, appending a free atom, replacing a free copy at offset `0` by its regular
facility).
-/

@[expose] public section

namespace BCFGJPSSV26.Greedy.Ctx.MergeH

theorem getD_of_lt {α : Type*} {l : List α} {d : α} {n : ℕ} (h : n < l.length) :
    l.getD n d = l[n] :=
  (List.getElem_eq_getD d).symm

theorem getD_of_le {α : Type*} {l : List α} {d : α} {n : ℕ} (h : l.length ≤ n) :
    l.getD n d = d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_take {α : Type*} {l : List α} {d : α} {k q : ℕ} (h : q < k) :
    (l.take k).getD q d = l.getD q d := by
  simp [List.getD_eq_getElem?_getD, h]

theorem getD_append_left {α : Type*} {l l' : List α} {d : α} {q : ℕ} (h : q < l.length) :
    (l ++ l').getD q d = l.getD q d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_self {α : Type*} {l : List α} {a d : α} :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem modify_append_left {α : Type*} {l l' : List α} {q : ℕ} (hq : q < l.length)
    (F : α → α) : (l ++ l').modify q F = l.modify q F ++ l' := by
  rw [List.modify_eq_take_cons_drop (by simp; omega), List.modify_eq_take_cons_drop hq,
    List.take_append_of_le_length hq.le, List.getElem_append_left hq,
    List.drop_append_of_le_length (by omega)]
  simp

/-- The flattening of a list of lists around entry `t` of list `q`. -/
theorem flatten_split {α : Type*} (L : List (List α)) {q t : ℕ} (hq : q < L.length)
    (ht : t < L[q].length) :
    L.flatten = (L.take q).flatten ++ L[q].take t ++
      L[q][t] :: (L[q].drop (t + 1) ++ (L.drop (q + 1)).flatten) := by
  have h1 : L.take q ++ L[q] :: L.drop (q + 1) = L := by
    rw [← List.drop_eq_getElem_cons hq, List.take_append_drop]
  have h2 : L[q].take t ++ L[q][t] :: L[q].drop (t + 1) = L[q] := by
    rw [← List.drop_eq_getElem_cons ht, List.take_append_drop]
  calc L.flatten = (L.take q ++ L[q] :: L.drop (q + 1)).flatten := by rw [h1]
    _ = (L.take q).flatten ++ (L[q].take t ++ L[q][t] :: L[q].drop (t + 1)) ++
        (L.drop (q + 1)).flatten := by
      rw [h2, List.flatten_append, List.flatten_cons, List.append_assoc]
    _ = _ := by simp only [List.append_assoc, List.cons_append]

theorem flatten_modify_set {α : Type*} (L : List (List α)) {q t : ℕ} (hq : q < L.length)
    (ht : t < L[q].length) (a : α) :
    (L.modify q (·.set t a)).flatten = (L.take q).flatten ++ L[q].take t ++
      a :: (L[q].drop (t + 1) ++ (L.drop (q + 1)).flatten) := by
  rw [List.modify_eq_take_cons_drop hq, List.set_eq_take_cons_drop _ ht]
  simp

theorem take_succ_getD {α : Type*} {l : List α} {d : α} {q : ℕ} (h : q < l.length) :
    l.take (q + 1) = l.take q ++ [l.getD q d] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, getD_of_lt h]
  rfl

theorem modify_last {α : Type*} (l : List α) (x : α) (F : α → α) :
    (l ++ [x]).modify l.length F = l ++ [F x] := by
  rw [List.modify_eq_take_cons_drop (by simp)]
  simp

/-- The counts of the points `a, P 0, …, P n`. -/
theorem getD_cnts_zero {β : Type*} (c : β → ℕ) (a : β) (P : ℕ → β) (n : ℕ) :
    ((a :: (List.range (n + 1)).map P).map c).getD 0 0 = c a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_cnts_succ {β : Type*} (c : β → ℕ) (a : β) (P : ℕ → β) {n r : ℕ} (hr : r ≤ n) :
    ((a :: (List.range (n + 1)).map P).map c).getD (r + 1) 0 = c (P r) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range (show r < n + 1 by omega)]

theorem length_cnts {β : Type*} (c : β → ℕ) (a : β) (P : ℕ → β) (n : ℕ) :
    ((a :: (List.range (n + 1)).map P).map c).length = n + 2 := by
  simp

/-! ### Sandwiches -/

theorem sandwich_iff {a b k : ℕ} :
    sandwich a b k = true ↔ (a < k ∧ k < b) ∨ (b < k ∧ k < a) := by
  simp [sandwich]

theorem sandwich_comm (a b k : ℕ) : sandwich a b k = sandwich b a k := by
  unfold sandwich
  rw [Bool.or_comm]

/-! ### The binary search -/

theorem searchStep_some (k : ℕ) (c : ℕ → ℕ) (lo hi g : ℕ) :
    ∀ s, (searchStep k c)^[s] (lo, hi, some g) = (lo, hi, some g)
  | 0 => rfl
  | s + 1 => by
    rw [Function.iterate_succ_apply]
    exact searchStep_some k c lo hi g s

theorem searchStep_iter {k : ℕ} {c : ℕ → ℕ} : ∀ (s lo : ℕ),
    sandwich (c lo) (c (lo + 2 ^ s)) k = true →
    (∃ lo', (searchStep k c)^[s] (lo, lo + 2 ^ s, none) = (lo', lo' + 1, none) ∧ lo ≤ lo' ∧
      lo' + 1 ≤ lo + 2 ^ s ∧ sandwich (c lo') (c (lo' + 1)) k = true ∧
      decide (c lo' < k) = decide (c lo < k)) ∨
    (∃ lo' hi' g, (searchStep k c)^[s] (lo, lo + 2 ^ s, none) = (lo', hi', some g) ∧ c g = k ∧
      lo ≤ g ∧ g ≤ lo + 2 ^ s)
  | 0, lo, hs => .inl ⟨lo, rfl, le_rfl, by simp, by simpa using hs, rfl⟩
  | s + 1, lo, hs => by
    rw [Function.iterate_succ_apply]
    have hpow : 2 ^ (s + 1) = 2 ^ s + 2 ^ s := by rw [pow_succ]; omega
    have hpos : 0 < 2 ^ s := Nat.two_pow_pos s
    have hmid : (lo + (lo + 2 ^ (s + 1))) / 2 = lo + 2 ^ s := by omega
    have hstep : searchStep k c (lo, lo + 2 ^ (s + 1), none) =
        if c (lo + 2 ^ s) = k then (lo, lo + 2 ^ (s + 1), some (lo + 2 ^ s))
        else if decide (c (lo + 2 ^ s) < k) = decide (c lo < k) then
          (lo + 2 ^ s, lo + 2 ^ (s + 1), none)
        else (lo, lo + 2 ^ s, none) := by
      simp only [searchStep]
      rw [if_neg (by omega), hmid]
    rw [hstep]
    rw [sandwich_iff] at hs
    by_cases hk : c (lo + 2 ^ s) = k
    · rw [if_pos hk, searchStep_some]
      exact .inr ⟨lo, lo + 2 ^ (s + 1), lo + 2 ^ s, rfl, hk, by omega, by omega⟩
    rw [if_neg hk]
    by_cases hside : decide (c (lo + 2 ^ s) < k) = decide (c lo < k)
    · rw [if_pos hside]
      have hs' : sandwich (c (lo + 2 ^ s)) (c (lo + 2 ^ s + 2 ^ s)) k = true := by
        rw [sandwich_iff, show lo + 2 ^ s + 2 ^ s = lo + 2 ^ (s + 1) by omega]
        by_cases h1 : c lo < k <;> by_cases h2 : c (lo + 2 ^ s) < k <;> simp_all <;> omega
      rcases searchStep_iter s (lo + 2 ^ s) hs' with ⟨lo', h1, h2, h3, h4, h5⟩ |
        ⟨lo', hi', g, h1, h2, h3, h4⟩
      · rw [show lo + 2 ^ (s + 1) = lo + 2 ^ s + 2 ^ s by omega]
        exact .inl ⟨lo', h1, by omega, by omega, h4, h5.trans hside⟩
      · rw [show lo + 2 ^ (s + 1) = lo + 2 ^ s + 2 ^ s by omega]
        exact .inr ⟨lo', hi', g, h1, h2, by omega, by omega⟩
    · rw [if_neg hside]
      have hs' : sandwich (c lo) (c (lo + 2 ^ s)) k = true := by
        rw [sandwich_iff]
        by_cases h1 : c lo < k <;> by_cases h2 : c (lo + 2 ^ s) < k <;> simp_all
        all_goals omega
      rcases searchStep_iter s lo hs' with ⟨lo', h1, h2, h3, h4, h5⟩ |
        ⟨lo', hi', g, h1, h2, h3, h4⟩
      · exact .inl ⟨lo', h1, h2, by omega, h4, h5⟩
      · exact .inr ⟨lo', hi', g, h1, h2, h3, by omega⟩

/-! ### Flips -/

theorem firstFlip_some' {k : ℕ} {cs : List ℕ} {t : ℕ} (h : firstFlip k cs = some t) :
    t + 1 < cs.length ∧ sandwich (cs.getD t 0) (cs.getD (t + 1) 0) k = true := by
  unfold firstFlip at h
  have h1 := List.find?_some h
  have h2 := List.mem_of_find?_eq_some h
  rw [List.mem_range] at h2
  exact ⟨by omega, h1⟩

/-- Without a flip and without a count equal to `k`, all counts are on the side of the first. -/
theorem firstFlip_none' {k : ℕ} {cs : List ℕ} (h : firstFlip k cs = none)
    (hk : ∀ x ∈ cs, x ≠ k) :
    ∀ t, t < cs.length → decide (cs.getD t 0 < k) = decide (cs.getD 0 0 < k) := by
  unfold firstFlip at h
  rw [List.find?_eq_none] at h
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro ht
    have h1 := h t (List.mem_range.2 (by omega))
    have h2 := ih (by omega)
    have h3 : cs.getD t 0 ≠ k := by
      rw [getD_of_lt (by omega)]
      exact hk _ (List.getElem_mem _)
    have h4 : cs.getD (t + 1) 0 ≠ k := by
      rw [getD_of_lt ht]
      exact hk _ (List.getElem_mem _)
    rw [sandwich_iff] at h1
    rw [← h2, decide_eq_decide]
    generalize cs.getD t 0 = x at *
    generalize cs.getD (t + 1) 0 = y at *
    constructor <;> intro <;> omega

/-! ### Common prefixes -/

theorem cpl_le_left : ∀ l l' : List AAtom, commonPrefixLen l l' ≤ l.length
  | a :: l, b :: l' => by
    unfold commonPrefixLen
    split_ifs
    · simpa using cpl_le_left l l'
    · simp
  | [], _ => by simp [commonPrefixLen]
  | _ :: _, [] => by simp [commonPrefixLen]

theorem cpl_le_right : ∀ l l' : List AAtom, commonPrefixLen l l' ≤ l'.length
  | a :: l, b :: l' => by
    unfold commonPrefixLen
    split_ifs
    · simpa using cpl_le_right l l'
    · simp
  | [], _ => by simp [commonPrefixLen]
  | _ :: _, [] => by simp [commonPrefixLen]

theorem take_cpl : ∀ l l' : List AAtom,
    l.take (commonPrefixLen l l') = l'.take (commonPrefixLen l l')
  | a :: l, b :: l' => by
    unfold commonPrefixLen
    split_ifs with h
    · simp [h, take_cpl l l']
    · simp
  | [], _ => by simp [commonPrefixLen]
  | _ :: _, [] => by simp [commonPrefixLen]

theorem le_cpl : ∀ (l l' : List AAtom) (n : ℕ), n ≤ l.length → n ≤ l'.length →
    l.take n = l'.take n → n ≤ commonPrefixLen l l'
  | _, _, 0, _, _, _ => Nat.zero_le _
  | a :: l, b :: l', n + 1, h1, h2, h3 => by
    simp only [List.take_succ_cons, List.cons.injEq] at h3
    unfold commonPrefixLen
    rw [if_pos h3.1]
    have := le_cpl l l' n (by simpa using h1) (by simpa using h2) h3.2
    omega
  | [], _, n + 1, h1, _, _ => by simp at h1
  | _ :: _, [], n + 1, _, h2, _ => by simp at h2

theorem prefix_of_cpl {l l' : List AAtom} (h : l.length ≤ commonPrefixLen l l') : l <+: l' := by
  have h1 := cpl_le_left l l'
  have h2 := take_cpl l l'
  rw [show commonPrefixLen l l' = l.length by omega, List.take_length] at h2
  rw [h2]
  exact List.take_prefix _ _

theorem cpl_lt_of_not_prefix {l l' : List AAtom} (h : ¬ l <+: l') :
    commonPrefixLen l l' < l.length := by
  by_contra h'
  exact h (prefix_of_cpl (by omega))

/-! ### Validity of the atoms of a list -/

section AtomsValid

variable {n m : ℕ} {P : Par} {d : Fin n → Fin m → ℚ} {f η : ℚ} {p : ℕ}

/-- All atoms of `H` are valid after `pre` and the atoms of `H` before them. -/
def AtomsValid (P : Par) (d : Fin n → Fin m → ℚ) (f η : ℚ) (p : ℕ) (pre H : List (Atom m)) :
    Prop :=
  ∀ t (ht : t < H.length), ValidAt P d f η p (pre ++ H.take t) H[t]

theorem atomsValid_append {pre A B : List (Atom m)} :
    AtomsValid P d f η p pre (A ++ B) ↔
      AtomsValid P d f η p pre A ∧ AtomsValid P d f η p (pre ++ A) B := by
  constructor
  · intro h
    refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_⟩
    · have h1 := h t (by simp; omega)
      rwa [List.take_append_of_le_length ht.le, List.getElem_append_left ht] at h1
    · have h1 := h (t + A.length) (by simp; omega)
      rwa [← List.getElem_append_right' A ht, List.take_append,
        List.take_of_length_le (by omega), Nat.add_sub_cancel, ← List.append_assoc] at h1
  · rintro ⟨hA, hB⟩ t ht
    by_cases htA : t < A.length
    · rw [List.take_append_of_le_length htA.le, List.getElem_append_left htA]
      exact hA t htA
    · obtain ⟨s, rfl⟩ : ∃ s, t = s + A.length := ⟨t - A.length, by omega⟩
      have hs : s < B.length := by simp at ht; omega
      rw [← List.getElem_append_right' A hs, List.take_append,
        List.take_of_length_le (by omega), Nat.add_sub_cancel, ← List.append_assoc]
      exact hB s hs

theorem atomsValid_nil {pre : List (Atom m)} : AtomsValid P d f η p pre [] :=
  fun _ ht ↦ absurd ht (Nat.not_lt_zero _)

theorem atomsValid_singleton {pre : List (Atom m)} {a : Atom m} :
    AtomsValid P d f η p pre [a] ↔ ValidAt P d f η p pre a := by
  constructor
  · intro h
    simpa using h 0 (by simp)
  · intro h t ht
    obtain rfl : t = 0 := by simpa using ht
    simpa using h

theorem atomsValid_of_free {pre F : List (Atom m)} (hF : ∀ a ∈ F, a.free = true) :
    AtomsValid P d f η p pre F :=
  fun _ ht ↦ .inl (hF _ (List.getElem_mem ht))

theorem atomsValid_cons {pre B : List (Atom m)} {a : Atom m} :
    AtomsValid P d f η p pre (a :: B) ↔
      ValidAt P d f η p pre a ∧ AtomsValid P d f η p (pre ++ [a]) B := by
  rw [show a :: B = [a] ++ B from rfl, atomsValid_append, atomsValid_singleton]

theorem AtomsValid.mono {pre pre' H : List (Atom m)} (h : AtomsValid P d f η p pre H)
    (hsub : pairs pre' ⊆ pairs pre) : AtomsValid P d f η p pre' H := by
  intro t ht
  refine (h t ht).mono_prefix ?_
  rw [pairs_append, pairs_append]
  exact Finset.union_subset_union hsub subset_rfl

theorem AtomsValid.congr {pre pre' H : List (Atom m)} (h : AtomsValid P d f η p pre H)
    (hp : pairs pre' = pairs pre) : AtomsValid P d f η p pre' H :=
  h.mono hp.le

/-- Deleting a block of atoms keeps the other atoms valid. -/
theorem AtomsValid.delete {pre A B Cs : List (Atom m)}
    (h : AtomsValid P d f η p pre (A ++ B ++ Cs)) : AtomsValid P d f η p pre (A ++ Cs) := by
  rw [List.append_assoc, atomsValid_append, atomsValid_append] at h
  rw [atomsValid_append]
  refine ⟨h.1, h.2.2.mono ?_⟩
  rw [pairs_append (pre ++ A)]
  exact Finset.subset_union_left

/-- Appending a free atom keeps the atoms valid. -/
theorem AtomsValid.append_free {pre H : List (Atom m)} (h : AtomsValid P d f η p pre H)
    {a : Atom m} (ha : a.free = true) : AtomsValid P d f η p pre (H ++ [a]) :=
  atomsValid_append.2 ⟨h, atomsValid_singleton.2 (.inl ha)⟩

/-- Replacing an atom by one with the same pair, valid after the atoms before it. -/
theorem AtomsValid.replace {pre A B : List (Atom m)} {a a' : Atom m}
    (h : AtomsValid P d f η p pre (A ++ a :: B)) (hp : a'.pair = a.pair)
    (ha' : ValidAt P d f η p (pre ++ A) a') : AtomsValid P d f η p pre (A ++ a' :: B) := by
  rw [atomsValid_append, atomsValid_cons] at h ⊢
  refine ⟨h.1, ha', h.2.2.congr ?_⟩
  simp [pairs, hp]

theorem pairs_replace {A B : List (Atom m)} {a a' : Atom m} (hp : a'.pair = a.pair) :
    pairs (A ++ a' :: B) = pairs (A ++ a :: B) := by
  simp [pairs, hp]

theorem maximal_congr {S S' : List (Atom m)} (h : Maximal P d f p S) (hp : pairs S' = pairs S) :
    Maximal P d f p S' := by
  unfold Maximal at h ⊢
  rwa [profL_congr P.K d hp]

theorem ValidSeq.mono_η {pre H : List (Atom m)} {η' : ℚ} (h : ValidSeq P d f η p pre H)
    (hη : η ≤ η') : ValidSeq P d f η' p pre H :=
  ⟨fun t ht ↦ (h.1 t ht).mono_η hη, h.2⟩

theorem etaValid_append {L : List (List (Atom m))} {S : List (Atom m)} :
    EtaValid P d f η (L ++ [S]) ↔ EtaValid P d f η L ∧ ValidSeq P d f η L.length L.flatten S := by
  constructor
  · intro h
    refine ⟨fun q hq ↦ ?_, ?_⟩
    · have h1 := h q (by simp; omega)
      rwa [List.take_append_of_le_length hq.le, List.getElem_append_left hq] at h1
    · have h1 := h L.length (by simp)
      rw [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl] at h1
      simpa using h1
  · rintro ⟨hL, hS⟩ q hq
    by_cases hqL : q < L.length
    · rw [List.take_append_of_le_length hqL.le, List.getElem_append_left hqL]
      exact hL q hqL
    · obtain rfl : q = L.length := by simp at hq; omega
      rw [List.take_append_of_le_length le_rfl, List.take_length,
        List.getElem_append_right le_rfl]
      simpa using hS

theorem EtaValid.take {L : List (List (Atom m))} (h : EtaValid P d f η L) (k : ℕ) :
    EtaValid P d f η (L.take k) := by
  intro q hq
  have hq' : q < L.length := by simp at hq; omega
  have h1 := h q hq'
  rw [List.getElem_take, List.take_take, min_eq_left (by simp at hq; omega)]
  exact h1

theorem Sol.mono_η {L : List (List (Atom m))} (h : Sol P d f 0 L) (hη : 0 ≤ η) :
    Sol P d f η L :=
  ⟨h.1, fun q hq ↦ ValidSeq.mono_η (h.2.1 q hq) hη, h.2.2.1, h.2.2.2⟩

end AtomsValid

/-! ### Counts of atoms -/

theorem nFreeSeqA_append (S T : List AAtom) :
    nFreeSeqA (S ++ T) = nFreeSeqA S + nFreeSeqA T := by
  simp [nFreeSeqA, List.filter_append]

theorem nRegSeq_append (S T : List AAtom) : nRegSeq (S ++ T) = nRegSeq S + nRegSeq T := by
  simp [nRegSeq, List.filter_append]

theorem nFreeSeqA_eq_zero {S : List AAtom} (h : ∀ a ∈ S, a.2 = 0) : nFreeSeqA S = 0 := by
  simp only [nFreeSeqA, List.length_eq_zero_iff, List.filter_eq_nil_iff]
  intro a ha
  simp [h a ha]

theorem nFreeSeqA_free (z g : ℕ) : nFreeSeqA [(z, g + 1)] = 1 := by simp [nFreeSeqA]

theorem nRegSeq_free (z g : ℕ) : nRegSeq [(z, g + 1)] = 0 := by simp [nRegSeq]

theorem nRegSeq_reg (z : ℕ) : nRegSeq [(z, 0)] = 1 := by simp [nRegSeq]

theorem nFreeSeqA_reg (z : ℕ) : nFreeSeqA [(z, 0)] = 0 := by simp [nFreeSeqA]

theorem nRegSeq_nil : nRegSeq [] = 0 := rfl

theorem nFreeSeqA_nil : nFreeSeqA [] = 0 := rfl

theorem nRegSeq_cons_reg (z : ℕ) (S : List AAtom) : nRegSeq ((z, 0) :: S) = nRegSeq S + 1 := by
  simp [nRegSeq]

theorem nRegSeq_cons_free (z g : ℕ) (S : List AAtom) :
    nRegSeq ((z, g + 1) :: S) = nRegSeq S := by
  simp [nRegSeq]

theorem nFreeSeqA_cons_reg (z : ℕ) (S : List AAtom) :
    nFreeSeqA ((z, 0) :: S) = nFreeSeqA S := by
  simp [nFreeSeqA]

theorem nFreeSeqA_cons_free (z g : ℕ) (S : List AAtom) :
    nFreeSeqA ((z, g + 1) :: S) = nFreeSeqA S + 1 := by
  simp [nFreeSeqA]

theorem reg_of_nFreeSeqA_eq_zero {S : List AAtom} (h : nFreeSeqA S = 0) : ∀ a ∈ S, a.2 = 0 := by
  intro a ha
  by_contra h'
  have : a ∈ S.filter fun a : AAtom ↦ a.2 != 0 := List.mem_filter.2 ⟨ha, by simpa using h'⟩
  rw [nFreeSeqA, List.length_eq_zero_iff] at h
  rw [h] at this
  simp at this

theorem nRegA_eq_flatten (H : List (List AAtom)) : nRegA H = nRegSeq H.flatten := rfl

theorem length_eq_nReg_add_nFree (S : List AAtom) : S.length = nRegSeq S + nFreeSeqA S :=
  List.length_eq_length_filter_add (fun a : AAtom ↦ a.2 == 0)

theorem nFreeSeqA_le_length (S : List AAtom) : nFreeSeqA S ≤ S.length := by
  have := length_eq_nReg_add_nFree S
  omega

variable {C : Ctx}

theorem SolOK.append {H : List (List AAtom)} {W : List AAtom} (hH : C.SolOK H)
    (hW : ∀ a ∈ W, C.AtomOK a) : C.SolOK (H ++ [W]) := by
  intro a ha
  simp only [List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_append] at ha
  exact ha.elim (hH a) (hW a)

theorem SolOK.take {H : List (List AAtom)} (hH : C.SolOK H) (k : ℕ) : C.SolOK (H.take k) :=
  fun a ha ↦ hH a ((List.take_sublist k H).flatten.subset ha)

theorem SolOK.getD {H : List (List AAtom)} (hH : C.SolOK H) (q : ℕ) :
    ∀ a ∈ H.getD q [], C.AtomOK a := by
  intro a ha
  by_cases hq : q < H.length
  · rw [getD_of_lt hq] at ha
    exact hH a (List.mem_flatten.2 ⟨_, List.getElem_mem hq, ha⟩)
  · rw [getD_of_le (by omega)] at ha
    simp at ha

variable {X : Space C.ip.n C.ip.m} (hX : C.Hyp X)

/-! ### Decoding -/

theorem decS_length (S : List AAtom) : (decS hX S).length = S.length := List.length_map _

theorem decS_take (S : List AAtom) (k : ℕ) : decS hX (S.take k) = (decS hX S).take k :=
  List.map_take ..

theorem decS_cons (a : AAtom) (S : List AAtom) : decS hX (a :: S) = decA hX a :: decS hX S :=
  rfl

theorem decH_length (H : List (List AAtom)) : (decH hX H).length = H.length := List.length_map _

theorem decH_append (H H' : List (List AAtom)) : decH hX (H ++ H') = decH hX H ++ decH hX H' :=
  List.map_append ..

theorem decH_take (H : List (List AAtom)) (k : ℕ) : decH hX (H.take k) = (decH hX H).take k :=
  List.map_take ..

theorem decA_free_eq (a : AAtom) : (decA hX a).free = (a.2 != 0) := rfl

theorem decA_free (z g : ℕ) : (decA hX (z, g + 1)).free = true := by simp [decA]

theorem decA_reg (z : ℕ) : (decA hX (z, 0)).free = false := by simp [decA]

theorem decA_free_mk (z g : ℕ) :
    decA hX (z, g + 1) = ⟨⟨z % C.ip.m, Nat.mod_lt _ hX.m_pos⟩, C.off g, true⟩ := by
  simp [decA, aoff]

include hX in
theorem K_nonneg : 0 ≤ C.ip.K := by
  have h1 : 2 * C.par.θ C.par.R ≤ C.ip.K := hX.good.K_ge
  have h2 := C.par.one_le_θ C.par.R
  linarith

include hX in
theorem off_nonneg (g : ℕ) : 0 ≤ C.off g := by
  have := K_nonneg hX
  unfold off
  positivity

include hX in
theorem off_le_succ (g : ℕ) : C.off g ≤ C.off (g + 1) := by
  have := K_nonneg hX
  unfold off
  push_cast
  gcongr
  linarith

/-- A free copy at offset `0` and the regular facility have the same pair. -/
theorem decA_pair_one (z : ℕ) : (decA hX (z, 1)).pair = (decA hX (z, 0)).pair := by
  simp [decA, Atom.pair, aoff, off]

theorem nReg_decS (S : List AAtom) :
    ((decS hX S).filter fun a ↦ !a.free).length = nRegSeq S := by
  unfold decS nRegSeq
  rw [List.filter_map, List.length_map]
  congr 1
  refine List.filter_congr fun a _ ↦ ?_
  simp [decA, bne]

/-- Pairs grow when every atom has an atom with the same pair. -/
theorem pairs_subset_of {S T : List AAtom}
    (h : ∀ a ∈ S, ∃ a' ∈ T, (decA hX a).pair = (decA hX a').pair) (P : List (Atom C.ip.m)) :
    pairs (P ++ decS hX S) ⊆ pairs (P ++ decS hX T) := by
  intro x hx
  simp only [pairs, decS, List.mem_toFinset, List.mem_map, List.mem_append] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  rcases hy with hy | ⟨a, ha, rfl⟩
  · exact ⟨y, .inl hy, rfl⟩
  · obtain ⟨a', ha', he⟩ := h a ha
    exact ⟨decA hX a', .inr ⟨a', ha', rfl⟩, he.symm⟩

/-! ### Valid sequences after a prefix -/

omit hX in
theorem fhat_nonneg' (hX : C.Hyp X) (b : ℕ) : 0 ≤ C.fhat b := by
  have h1 := nη_lt_fhat hX b
  have h2 : (0 : ℚ) ≤ C.ip.n * C.ip.η := mul_nonneg (Nat.cast_nonneg _) hX.good.η_nonneg
  linarith

/-- A **valid sequence** `W` after the prefix `pre`, at `f̂ b`. -/
def VS (p b : ℕ) (pre : List (List AAtom)) (W : List AAtom) : Prop :=
  ValidSeq C.par X.d (C.fhat b) C.ip.η p (decS hX pre.flatten) (decS hX W)

variable {p b : ℕ} {pre : List (List AAtom)}

/-- The atoms of `cur`, in the form `completeSeq_validSeq` asks for. -/
theorem atomsValid_dec {f η : ℚ} {S cur : List AAtom}
    (h : AtomsValid C.par X.d f η p (decS hX S) (decS hX cur)) :
    ∀ t (ht : t < cur.length), ValidAt C.par X.d f η p (decS hX (S ++ cur.take t))
      (decA hX cur[t]) := by
  intro t ht
  have h1 := h t (by rwa [decS_length])
  rw [decS_append, decS_take]
  simpa [decS] using h1

/-- A valid sequence has at most `m` regular atoms. -/
theorem VS.nRegSeq_le {W : List AAtom} (hW : VS hX p b pre W) (hok : ∀ a ∈ W, C.AtomOK a) :
    nRegSeq W ≤ C.ip.m := by
  have h := ValidSeq.nReg_le hX.good (fun j i ↦ X.d_nonneg j i) (nη_lt_fhat hX b) hW
    (fun a ha ↦ by
      obtain ⟨a', ha', rfl⟩ := List.mem_map.1 ha
      exact decA_wf hX (hok a' ha'))
  rwa [nReg_decS] at h

/-! ### The completion after a prefix and a sequence -/

omit hX in
theorem complete_take_succ {f : ℚ} (hlen : pre.length = p) (hp : p < 2 * C.ip.R)
    (W : List AAtom) : (C.complete f (pre ++ [W])).take (p + 1) = pre ++ [W] := by
  have h := C.complete_take f (H := pre ++ [W]) (by simp; omega)
  simpa [hlen] using h

omit hX in
theorem complete_getD_le {f : ℚ} (hlen : pre.length = p) (hp : p < 2 * C.ip.R)
    (W : List AAtom) {q : ℕ} (hq : q ≤ p) :
    (C.complete f (pre ++ [W])).getD q [] = (pre ++ [W]).getD q [] := by
  rw [← getD_take (k := p + 1) (by omega), complete_take_succ hlen hp]

omit hX in
theorem complete_getD_self {f : ℚ} (hlen : pre.length = p) (hp : p < 2 * C.ip.R)
    (W : List AAtom) : (C.complete f (pre ++ [W])).getD p [] = W := by
  rw [complete_getD_le hlen hp W le_rfl, ← hlen, getD_append_self]

omit hX in
theorem complete_getD_lt {f : ℚ} (hlen : pre.length = p) (hp : p < 2 * C.ip.R)
    (W : List AAtom) {q : ℕ} (hq : q < p) :
    (C.complete f (pre ++ [W])).getD q [] = pre.getD q [] := by
  rw [complete_getD_le hlen hp W hq.le, getD_append_left (by omega)]

omit hX in
/-- The sequences added by the completion have no free atoms. -/
theorem complete_free_gt {f : ℚ} {H : List (List AAtom)} (hH : H.length ≤ 2 * C.ip.R) {q : ℕ}
    (hq : H.length ≤ q) : nFreeSeqA ((C.complete f H).getD q []) = 0 := by
  by_cases hq' : q < 2 * C.ip.R
  · rw [C.complete_getD f hq hq']
    refine nFreeSeqA_eq_zero fun a ha ↦ ?_
    have := C.completeSeq_new _ _ _ _ [] a (by simpa using ha)
    exact this.1
  · rw [getD_of_le (by rw [C.complete_length f hH]; omega)]
    rfl

omit hX in
/-- The sequences added by the completion have only regular atoms of facilities `< m`. -/
theorem complete_getD_new {f : ℚ} {H : List (List AAtom)} {q : ℕ} (hq : H.length ≤ q)
    (hq' : q < 2 * C.ip.R) : ∀ a ∈ (C.complete f H).getD q [], a.2 = 0 ∧ a.1 < C.ip.m := by
  rw [C.complete_getD f hq hq']
  intro a ha
  exact C.completeSeq_new _ _ _ _ [] a (by simpa using ha)

/-! ### Counting identities -/

omit hX in
theorem cnt_perm (f : ℚ) (pre : List (List AAtom)) {W₁ W₂ : List AAtom}
    (hmem : ∀ a, a ∈ W₁ ↔ a ∈ W₂) (hreg : nRegSeq W₁ = nRegSeq W₂) :
    C.cnt f pre W₁ = C.cnt f pre W₂ := by
  have h := C.cnt_congr f pre (W₁ := W₁) (W₂ := W₂) (C.prof_perm fun a ↦ by simp [hmem])
  omega

omit hX in
theorem cnt_swapFree' (f : ℚ) (pre : List (List AAtom)) (A B : List AAtom) (z : ℕ) :
    C.cnt f pre (A ++ (z, 0) :: B) = C.cnt f pre (A ++ B ++ [(z, 1)]) + 1 := by
  have hp : C.prof (pre.flatten ++ (A ++ (z, 0) :: B)) =
      C.prof (pre.flatten ++ (A ++ B ++ [(z, 1)])) := by
    have := C.prof_swapFree (pre.flatten ++ A) B z
    simpa only [List.append_assoc] using this
  have h := C.cnt_congr f pre hp
  simp only [nRegSeq_append, nRegSeq_cons_reg, nRegSeq_free z 0] at h
  omega

omit hX in
/-- Making a free copy at offset `0` regular raises the count by exactly one. -/
theorem cnt_toRegular (f : ℚ) (pre : List (List AAtom)) (A B : List AAtom) (z : ℕ) :
    C.cnt f pre (A ++ (z, 0) :: B) = C.cnt f pre (A ++ (z, 1) :: B) + 1 := by
  rw [cnt_swapFree']
  congr 1
  refine cnt_perm f pre (fun a ↦ ?_) ?_
  · simp only [List.mem_append, List.mem_cons]
    tauto
  · simp only [nRegSeq_append, nRegSeq_cons_free z 0, nRegSeq_nil]
    omega

include hX in
theorem cnt_append_top' (f : ℚ) (pre : List (List AAtom)) (W : List AAtom) (z : ℕ) :
    C.cnt f pre (W ++ [(z, 2 ^ C.ip.Pu + 1)]) = C.cnt f pre W := by
  have h := C.cnt_congr f pre (W₁ := W ++ [(z, 2 ^ C.ip.Pu + 1)]) (W₂ := W)
    (by rw [← List.append_assoc, C.prof_append_top hX.dist_nonneg off_top])
  simp only [nRegSeq_append, nRegSeq_free] at h
  omega

end BCFGJPSSV26.Greedy.Ctx.MergeH


