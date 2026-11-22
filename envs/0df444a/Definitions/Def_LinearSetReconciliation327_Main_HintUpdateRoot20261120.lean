-- Prove2me | Definitions.Def_LinearSetReconciliation327_Main_HintUpdateRoot20261120
-- name    : LinearSetReconciliation327_Main_HintUpdateRoot20261120
-- status  : Definition
-- author  : @djwj233
-- created : 2026-11-22T08:46:14.131051+00:00
-- url     : https://prove2.me/theorems/6b12ea47-c258-4258-8a7d-7cf32f6606d8
-- title:
--   LinearSetReconciliation327 — HintUpdateRoot (2026-11-20)
-- statement:
--   Internal dependency module `Definitions.LinearSetReconciliation327_Main_HintUpdateRoot20261120` of the LinearSetReconciliation327 development that formalizes Theorem 5.1 (Performance of HintSketch). It factors the toggle-program / decoder construction into a small node so that every node compiles well inside the platform's compilation limit; it contains only the definitions, structures, lemmas and proofs belonging to this module, and it is sorry-free. This definition is a supporting node, not a statement of independent mathematical interest.
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Theorem 5.1 (HintSketch), PDF p.19 (printed p.18)

import Definitions.Def_LinearSetReconciliation327_Main_HintUpdateLoop20261120
import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_WordRAM
import Definitions.Def_LinearSetReconciliation327_Main_Framework
import Definitions.Def_LinearSetReconciliation327_Main_HintSketch
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
open Classical in
def synLen (CR : CRFamily) : Node → ℕ
  | .store N => N
  | .cr N t => CR.rows N t
  | .direct sch t => sch.m * sch.ℓ + CR.rows sch.N t
  | .recursive sch t _ _ child => (∑ s : Fin sch.ℓ, synLen CR (child s)) + CR.rows sch.N t
open Classical in
noncomputable def bitVal (CR : CRFamily) :
    (T : Node) → Node.Seed T → Fin (synLen CR T) → Finset ℕ → ZMod 2
  | .store N, _, p, x => if (p.val : ℕ) ∈ x then 1 else 0
  | .cr N t, _, p, x => if (p.val : ℕ) ∈ CR.sketch N t x then 1 else 0
  | .direct sch t, r, p, x =>
      (Fin.append (fun q : Fin (sch.m * sch.ℓ) =>
          (fun sq : Fin sch.m × Fin sch.ℓ =>
              sch.code sq.1 (r.2 sq.1) (sch.rowOf r x sq.1) sq.2) (finProdFinEquiv.symm q))
        (fun q : Fin (CR.rows sch.N t) =>
          if (q.val : ℕ) ∈ CR.sketch sch.N t x then 1 else 0)) p
  | .recursive sch t _ _ child, r, p, x =>
      (Fin.append (fun q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s)) =>
          (fun sq : (s : Fin sch.ℓ) × Fin (synLen CR (child s)) =>
              bitVal CR (child sq.1) (r.2 sq.1) sq.2 (sch.column r.1 x sq.1))
            (finSigmaFinEquiv.symm q))
        (fun q : Fin (CR.rows sch.N t) =>
          if (q.val : ℕ) ∈ CR.sketch sch.N t x then 1 else 0)) p
def schemeNodes : Node → List Node
  | .store _ => []
  | .cr _ _ => []
  | .direct sch t => [.direct sch t]
  | .recursive sch t Xs Ys child =>
      [.recursive sch t Xs Ys child] ++
        (List.ofFn fun s : Fin sch.ℓ => schemeNodes (child s)).flatten
def nodeEll : Node → ℕ
  | .direct sch _ => sch.ℓ
  | .recursive sch _ _ _ _ => sch.ℓ
  | _ => 0
def nodeM : Node → ℕ
  | .direct sch _ => sch.m
  | .recursive sch _ _ _ _ => sch.m
  | _ => 0
def nodeNmax (v : Node) : ℕ := ⌈(v.N : ℝ) / (nodeM v : ℝ)⌉₊
def nodeCoins (v : Node) : ℕ × ℕ := (nodeM v * nodeEll v * nodeNmax v, 2)
def permSizesOf (T : Node) : List ℕ := (schemeNodes T).map Node.N
def coeffShapesOf (T : Node) : List (ℕ × ℕ) := (schemeNodes T).map nodeCoins
def hintSpec (T : Node) : TableSpec where
  permSizes := permSizesOf T
  coeffShapes := coeffShapesOf T
  coeff_pos := by
    intro p hp
    obtain ⟨v, _, rfl⟩ := List.mem_map.mp hp
    show 0 < (nodeCoins v).2
    simp [nodeCoins]
section Linearity
open Classical in
lemma rowImage_symmDiff (N m : ℕ) (hm : 0 < m) (π : Equiv.Perm (Fin N)) (j : ℕ)
    (S S' : Finset ℕ) :
    rowImage N m π j (symmDiff S S') = symmDiff (rowImage N m π j S) (rowImage N m π j S') := by
  classical
  have key : ∀ i i' : Fin N, (π i).val % m = (π i').val % m →
      (π i).val / m = (π i').val / m → i = i' := by
    intro i i' h1 h2
    have e1 := Nat.div_add_mod (π i).val m
    have e2 := Nat.div_add_mod (π i').val m
    have e : (π i).val = (π i').val := by
      rw [h1, h2] at e1
      rw [e1] at e2
      exact e2
    exact π.injective (Fin.ext e)
  ext a
  simp only [rowImage, mem_image, mem_filter, mem_univ, true_and, mem_symmDiff]
  constructor
  · rintro ⟨i, ⟨hi, hj⟩, ha⟩
    rcases hi with ⟨hS, hS'⟩ | ⟨hS, hS'⟩
    · left
      refine ⟨⟨i, ⟨hS, hj⟩, ha⟩, ?_⟩
      rintro ⟨i', ⟨hi', hj'⟩, ha'⟩
      have h : i' = i := key i' i (hj'.trans hj.symm) (ha'.trans ha.symm)
      rw [h] at hi'
      exact hS' hi'
    · right
      refine ⟨⟨i, ⟨hS, hj⟩, ha⟩, ?_⟩
      rintro ⟨i', ⟨hi', hj'⟩, ha'⟩
      have h : i' = i := key i' i (hj'.trans hj.symm) (ha'.trans ha.symm)
      rw [h] at hi'
      exact hS' hi'
  · rintro (⟨⟨i, ⟨hS, hj⟩, ha⟩, hnot⟩ | ⟨⟨i, ⟨hS, hj⟩, ha⟩, hnot⟩)
    · refine ⟨i, ⟨?_, hj⟩, ha⟩
      exact Or.inl ⟨hS, fun hc => hnot ⟨i, ⟨hc, hj⟩, ha⟩⟩
    · refine ⟨i, ⟨?_, hj⟩, ha⟩
      exact Or.inr ⟨hS, fun hc => hnot ⟨i, ⟨hc, hj⟩, ha⟩⟩
lemma zmod2_add_eq_one_iff (a b : ZMod 2) :
    a + b = 1 ↔ (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  rcases zmod2_eq_zero_or_one a with rfl | rfl <;> rcases zmod2_eq_zero_or_one b with rfl | rfl <;>
    decide
open Classical in
lemma rowsWhere_add (sch : RowScheme) (A B : Fin sch.m → ZMod 2) :
    sch.rowsWhere (fun j => A j + B j = 1) =
      symmDiff (sch.rowsWhere (fun j => A j = 1)) (sch.rowsWhere (fun j => B j = 1)) := by
  classical
  ext a
  simp only [RowScheme.rowsWhere, mem_symmDiff, mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    rcases (zmod2_add_eq_one_iff (A i) (B i)).1 hi with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · left
      refine ⟨⟨i, hA, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hB] at hi'
      exact zero_ne_one hi'
    · right
      refine ⟨⟨i, hB, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hA] at hi'
      exact zero_ne_one hi'
  · rintro (⟨⟨i, hi, hv⟩, hnot⟩ | ⟨⟨i, hi, hv⟩, hnot⟩)
    · refine ⟨i, ?_, hv⟩
      rw [zmod2_add_eq_one_iff]
      left
      refine ⟨hi, ?_⟩
      rcases zmod2_eq_zero_or_one (B i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
    · refine ⟨i, ?_, hv⟩
      rw [zmod2_add_eq_one_iff]
      right
      refine ⟨?_, hi⟩
      rcases zmod2_eq_zero_or_one (A i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
open Classical in
lemma column_symmDiff (sch : RowScheme) (lr : sch.LocalSeed) (x y : Finset ℕ) (s : Fin sch.ℓ) :
    sch.column lr (symmDiff x y) s = symmDiff (sch.column lr x s) (sch.column lr y s) := by
  classical
  rcases Nat.eq_zero_or_pos sch.m with hm | hm
  · have hempty : (univ : Finset (Fin sch.m)) = ∅ := by
      have hc : (univ : Finset (Fin sch.m)).card = 0 := by simp [hm]
      exact Finset.card_eq_zero.mp hc
    simp [RowScheme.column, RowScheme.rowsWhere, hempty]
  · unfold RowScheme.column
    have hrow : ∀ j, sch.rowOf lr (symmDiff x y) j = symmDiff (sch.rowOf lr x j) (sch.rowOf lr y j) :=
      fun j => rowImage_symmDiff sch.N sch.m hm lr.1 j x y
    have hcode : ∀ j, sch.code j (lr.2 j) (sch.rowOf lr (symmDiff x y) j) s =
        sch.code j (lr.2 j) (sch.rowOf lr x j) s + sch.code j (lr.2 j) (sch.rowOf lr y j) s := by
      intro j
      rw [hrow j, sch.code_linear]
    simp only [hcode]
    exact rowsWhere_add sch _ _
end Linearity
lemma filter_symmDiff (p : ℕ → Prop) [DecidablePred p] (A B : Finset ℕ) :
    (symmDiff A B).filter p = symmDiff (A.filter p) (B.filter p) := by
  classical
  ext a
  simp only [mem_symmDiff, mem_filter]
  tauto
lemma odd_card_symmDiff (A B : Finset ℕ) :
    Odd (symmDiff A B).card ↔ (Odd A.card ∧ ¬ Odd B.card) ∨ (Odd B.card ∧ ¬ Odd A.card) := by
  classical
  have hdisj1 : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_sdiff.mp hb).1
  have hdisj2 : Disjoint (A \ B) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).2
  have hdisj3 : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_inter.mp hb).1
  have hAB : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [symmDiff_def, sup_eq_union]
    exact Finset.card_union_of_disjoint hdisj1
  have hA : A.card = (A \ B).card + (A ∩ B).card := by
    have hunion : A \ B ∪ A ∩ B = A := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc A.card = (A \ B ∪ A ∩ B).card := by rw [hunion]
      _ = (A \ B).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj2
  have hB : B.card = (B \ A).card + (A ∩ B).card := by
    have hunion : B \ A ∪ A ∩ B = B := by
      ext a
      simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
      tauto
    calc B.card = (B \ A ∪ A ∩ B).card := by rw [hunion]
      _ = (B \ A).card + (A ∩ B).card := Finset.card_union_of_disjoint hdisj3
  rw [hAB, hA, hB, Nat.odd_add, Nat.odd_add, Nat.odd_add, ← Nat.not_odd_iff_even,
    ← Nat.not_odd_iff_even]
  tauto
open Classical in
lemma sketch_symmDiff (CR : CRFamily) (N t : ℕ) (x y : Finset ℕ) :
    CR.sketch N t (symmDiff x y) = symmDiff (CR.sketch N t x) (CR.sketch N t y) := by
  classical
  ext r
  have hfilt : (symmDiff x y).filter (fun i => r ∈ CR.col N t i) =
      symmDiff (x.filter fun i => r ∈ CR.col N t i) (y.filter fun i => r ∈ CR.col N t i) :=
    filter_symmDiff _ x y
  simp only [CRFamily.sketch, hfilt, mem_symmDiff, mem_filter, mem_range, true_and,
    odd_card_symmDiff]
  tauto
lemma ite_mem_symmDiff (A B : Finset ℕ) (a : ℕ) :
    (if a ∈ symmDiff A B then (1 : ZMod 2) else 0) =
      (if a ∈ A then 1 else 0) + (if a ∈ B then 1 else 0) := by
  classical
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;>
    simp [Finset.mem_symmDiff, hA, hB] <;> decide
theorem bitVal_symmDiff (CR : CRFamily) (T : Node) :
    ∀ (r : Node.Seed T) (p : Fin (synLen CR T)) (x y : Finset ℕ),
      bitVal CR T r p (symmDiff x y) = bitVal CR T r p x + bitVal CR T r p y := by
  induction T with
  | store N =>
      intro r p x y
      simpa only [bitVal] using ite_mem_symmDiff x y p.val
  | cr N t =>
      intro r p x y
      have hs := sketch_symmDiff CR N t x y
      simpa only [bitVal, hs] using ite_mem_symmDiff (CR.sketch N t x) (CR.sketch N t y) p.val
  | direct sch t =>
      intro r p x y
      simp only [bitVal]
      by_cases hp : p.val < sch.m * sch.ℓ
      · have hm : 0 < sch.m := by
          rcases Nat.eq_zero_or_pos sch.m with h | h
          · rw [h, Nat.zero_mul] at hp
            omega
          · exact h
        have hp' : p = Fin.castAdd (CR.rows sch.N t) ⟨p.val, hp⟩ := Fin.ext rfl
        rw [hp', Fin.append_left, Fin.append_left, Fin.append_left]
        simp only [RowScheme.rowOf]
        rw [rowImage_symmDiff sch.N sch.m hm r.1 _ x y, sch.code_linear]
      · have hlt : p.val - sch.m * sch.ℓ < CR.rows sch.N t := by
          have hp2 : p.val < sch.m * sch.ℓ + CR.rows sch.N t := p.isLt
          omega
        have hp' : p = Fin.natAdd (sch.m * sch.ℓ) ⟨p.val - sch.m * sch.ℓ, hlt⟩ := by
          apply Fin.ext
          simp only [Fin.val_natAdd]
          omega
        rw [hp', Fin.append_right, Fin.append_right, Fin.append_right, sketch_symmDiff]
        exact ite_mem_symmDiff _ _ _
  | recursive sch t Xs Ys child ih =>
      intro r p x y
      cases r with
      | mk seedOwn seedChildren =>
        simp only [bitVal]
        by_cases hp : p.val < ∑ s : Fin sch.ℓ, synLen CR (child s)
        · have hp' : p = Fin.castAdd (CR.rows sch.N t) ⟨p.val, hp⟩ := Fin.ext rfl
          rw [hp', Fin.append_left, Fin.append_left, Fin.append_left]
          rw [column_symmDiff]
          exact ih _ (seedChildren _) _ _ _
        · have hlt : p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)) < CR.rows sch.N t := by
            have hp2 : p.val < (∑ s : Fin sch.ℓ, synLen CR (child s)) + CR.rows sch.N t := p.isLt
            omega
          have hp' : p = Fin.natAdd (∑ s : Fin sch.ℓ, synLen CR (child s))
              ⟨p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)), hlt⟩ := by
            apply Fin.ext
            simp only [Fin.val_natAdd]
            omega
          rw [hp', Fin.append_right, Fin.append_right, Fin.append_right, sketch_symmDiff]
          exact ite_mem_symmDiff _ _ _
def support {N : ℕ} (x : Fin N → ZMod 2) : Finset ℕ := (univ.filter fun i => x i = 1).image Fin.val
lemma support_add {N : ℕ} (x y : Fin N → ZMod 2) :
    support (x + y) = symmDiff (support x) (support y) := by
  classical
  ext a
  simp only [support, mem_image, mem_filter, mem_univ, true_and, mem_symmDiff]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hsum : x i + y i = 1 := hi
    rcases (zmod2_add_eq_one_iff (x i) (y i)).1 hsum with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · left
      refine ⟨⟨i, hx, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hy] at hi'
      exact zero_ne_one hi'
    · right
      refine ⟨⟨i, hy, rfl⟩, ?_⟩
      rintro ⟨i', hi', hv⟩
      have h : i' = i := Fin.ext hv
      rw [h, hx] at hi'
      exact zero_ne_one hi'
  · rintro (⟨⟨i, hi, hv⟩, hnot⟩ | ⟨⟨i, hi, hv⟩, hnot⟩)
    · refine ⟨i, ?_, hv⟩
      show x i + y i = 1
      rw [zmod2_add_eq_one_iff]
      left
      refine ⟨hi, ?_⟩
      rcases zmod2_eq_zero_or_one (y i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
    · refine ⟨i, ?_, hv⟩
      show x i + y i = 1
      rw [zmod2_add_eq_one_iff]
      right
      refine ⟨?_, hi⟩
      rcases zmod2_eq_zero_or_one (x i) with h | h
      · exact h
      · exact absurd ⟨i, ⟨h, hv⟩⟩ hnot
lemma support_zero {N : ℕ} : support (0 : Fin N → ZMod 2) = ∅ := by
  classical
  ext a
  simp [support]
lemma bitVal_empty (CR : CRFamily) (T : Node) (r : Node.Seed T) (p : Fin (synLen CR T)) :
    bitVal CR T r p ∅ = 0 := by
  have h0 : symmDiff (∅ : Finset ℕ) ∅ = ∅ := by
    simp [symmDiff_def]
  have h := bitVal_symmDiff CR T r p ∅ ∅
  rw [h0] at h
  rw [h]
  exact CharTwo.add_self_eq_zero _
def hintH (CR : CRFamily) (T : Node) (κ : (hintSpec T).Seed → Node.Seed T)
    (r : (hintSpec T).Seed) :
    (Fin (Node.N T) → ZMod 2) →ₗ[ZMod 2] (Fin (synLen CR T) → ZMod 2) where
  toFun x := fun p => bitVal CR T (κ r) p (support x)
  map_add' x y := by
    funext p
    simp only [Pi.add_apply]
    rw [support_add, bitVal_symmDiff]
  map_smul' c x := by
    funext p
    simp only [Pi.smul_apply]
    rcases zmod2_eq_zero_or_one c with hc | hc
    · rw [hc]
      simp [support_zero, bitVal_empty]
    · rw [hc]
      simp
def hintHfun (CR : CRFamily) (T : Node) (κ : (hintSpec T).Seed → Node.Seed T) :
    (hintSpec T).Seed → (Fin (Node.N T) → ZMod 2) →ₗ[ZMod 2] (Fin (synLen CR T) → ZMod 2) :=
  fun r => hintH CR T κ r
inductive IsSchemeTree (P : HintParams) : Node → Type 1 where
  | store (N : ℕ) : IsSchemeTree P (.store N)
  | cr (N t : ℕ) : IsSchemeTree P (.cr N t)
  | direct (N X Y t : ℕ) : IsSchemeTree P (.direct (P.scheme N X Y) t)
  | recursive (N X Y t : ℕ) (Xs Ys : Fin (P.scheme N X Y).ℓ → ℕ)
      (child : Fin (P.scheme N X Y).ℓ → Node) (hchild : ∀ s, IsSchemeTree P (child s)) :
      IsSchemeTree P (.recursive (P.scheme N X Y) t Xs Ys child)
def NodeCoins (P : HintParams) (N X Y : ℕ) : Type :=
  Fin (P.rows X Y) → Fin (P.ell N X Y) → Fin (P.Nmax N X Y) → ZMod 2
def NodeLocalSeed (P : HintParams) (N X Y : ℕ) : Type :=
  Equiv.Perm (Fin N) × NodeCoins P N X Y
def permNode (R : Node) (r : (hintSpec R).Seed) (k N : ℕ) : Equiv.Perm (Fin N) :=
  if h : k < (hintSpec R).permSizes.length then
    if h2 : (hintSpec R).permSizes.get ⟨k, h⟩ = N then
      (h2 ▸ r.1 ⟨k, h⟩ : Equiv.Perm (Fin N))
    else 1
  else 1
def coeffAt (R : Node) (r : (hintSpec R).Seed) (k a : ℕ) : ZMod 2 :=
  if h : k < (hintSpec R).coeffShapes.length then
    if h' : a < ((hintSpec R).coeffShapes.get ⟨k, h⟩).1 then
      (((r.2 ⟨k, h⟩) ⟨a, h'⟩).val : ZMod 2)
    else 0
  else 0
def coinsNode (P : HintParams) (R : Node) (r : (hintSpec R).Seed) (N X Y : ℕ) (k : ℕ) :
    NodeCoins P N X Y :=
  fun j s v => coeffAt R r k ((j.val * P.ell N X Y + s.val) * P.Nmax N X Y + v.val)
def hintKappaAux (P : HintParams) (R : Node) (r : (hintSpec R).Seed) :
    (T : Node) → IsSchemeTree P T → ℕ → Node.Seed T
  | _, .store N, _ => ()
  | _, .cr N t, _ => ()
  | _, .direct N X Y t, k =>
      (show NodeLocalSeed P N X Y from (permNode R r k N, coinsNode P R r N X Y k))
  | _, .recursive N X Y t _ _ child hchild, k =>
      (show NodeLocalSeed P N X Y from (permNode R r k N, coinsNode P R r N X Y k),
        fun s => hintKappaAux P R r (child s) (hchild s)
          (k + 1 + ((List.ofFn fun i : Fin (P.scheme N X Y).ℓ =>
            (schemeNodes (child i)).length).take s.val).sum))
def hintKappa (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    (hintSpec T).Seed → Node.Seed T :=
  fun r => hintKappaAux P T r T hT 0
def hintH_trees (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T) :
    (hintSpec T).Seed → (Fin (Node.N T) → ZMod 2) →ₗ[ZMod 2] (Fin (synLen CR T) → ZMod 2) :=
  hintHfun CR T (hintKappa P T hT)
lemma hintH_trees_apply (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T)
    (r : (hintSpec T).Seed) (x : Fin (Node.N T) → ZMod 2) (p : Fin (synLen CR T)) :
    hintH_trees CR P T hT r x p = bitVal CR T (hintKappa P T hT r) p (support x) := rfl
lemma support_single {N : ℕ} (i : Fin N) :
    support (Pi.single i (1 : ZMod 2)) = ({i.val} : Finset ℕ) := by
  ext a
  simp only [support, mem_image, mem_filter, mem_univ, true_and, mem_singleton]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_contra h
    have hne : j ≠ i := fun he => h (by rw [he])
    rw [Pi.single_eq_of_ne hne] at hj
    exact zero_ne_one hj
  · intro h
    exact ⟨i, Pi.single_eq_same i 1, h.symm⟩
noncomputable def colSupp (CR : CRFamily) (T : Node) (r : Node.Seed T) (x : Finset ℕ) :
    Finset (Fin (synLen CR T)) :=
  univ.filter fun p => bitVal CR T r p x = 1
def ofBits (W : ℕ) (f : ℕ → Bool) : ℕ := ∑ b ∈ Finset.range W, if f b then 2 ^ b else 0
theorem geom_two (W : ℕ) : (∑ b ∈ Finset.range W, 2 ^ b) = 2 ^ W - 1 := by
  induction W with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have h : 0 < 2 ^ n := Nat.two_pow_pos n
      omega
theorem ofBits_lt (W : ℕ) (f : ℕ → Bool) : ofBits W f < 2 ^ W := by
  have h : ofBits W f ≤ ∑ b ∈ Finset.range W, 2 ^ b := by
    refine Finset.sum_le_sum ?_
    intro b _
    split_ifs with hb
    · exact le_rfl
    · exact Nat.zero_le _
  rw [geom_two] at h
  have h2 : 0 < 2 ^ W := Nat.two_pow_pos W
  omega
theorem ofBits_succ (W : ℕ) (f : ℕ → Bool) :
    ofBits (W + 1) f = (if f 0 then 1 else 0) + 2 * ofBits W (fun b => f (b + 1)) := by
  rw [ofBits, ofBits, Finset.sum_range_succ']
  have h2 : (∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ (k + 1) else 0))
      = 2 * ∑ k ∈ Finset.range W, (if f (k + 1) then 2 ^ k else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    split_ifs with hk
    · rw [pow_succ]
      ring
    · rfl
  rw [h2]
  by_cases h : f 0 = true
  · simp [h, Nat.add_comm]
  · simp [h, Nat.add_comm]
theorem ofBits_testBit (W : ℕ) (f : ℕ → Bool) (b : ℕ) (hb : b < W) :
    (ofBits W f).testBit b = f b := by
  induction W generalizing b f with
  | zero => omega
  | succ n ih =>
      rw [ofBits_succ]
      cases b with
      | zero =>
          rw [Nat.testBit_zero, Nat.add_mul_mod_self_left]
          by_cases h : f 0 = true <;> simp [h]
      | succ b =>
          rw [Nat.testBit_succ]
          have hdiv : ((if f 0 then 1 else 0) + 2 * ofBits n (fun b => f (b + 1))) / 2
              = ofBits n (fun b => f (b + 1)) := by
            rw [Nat.add_mul_div_left _ _ (by norm_num : 0 < 2)]
            by_cases h : f 0 = true <;> simp [h]
          rw [hdiv]
          exact ih (fun b => f (b + 1)) b (by omega)
theorem packMem_eq_ofBits (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a = ofBits W (fun b => decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1)) := by
  rw [packMem, ofBits]
  have hR : (∑ b ∈ Finset.range W,
        (if decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) then 2 ^ b else 0))
      = ∑ b ∈ (Finset.range W).filter
          (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1), 2 ^ b := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro b _
    by_cases h : ∃ p : Fin M, p.val = a * W + b ∧ y p = 1 <;> simp [h]
  rw [hR]
  have hL : (∑ p : Fin M, (if p.val / W = a ∧ y p = 1 then 2 ^ (p.val % W) else 0))
      = ∑ b ∈ (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
          (fun p => p.val % W), 2 ^ b := by
    rw [Finset.sum_image]
    · rw [Finset.sum_filter]
    · intro p hp p' hp' heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hp hp'
      have heq' : p.val % W = p'.val % W := heq
      refine Fin.ext ?_
      rw [← Nat.div_add_mod p.val W, hp.1, ← Nat.div_add_mod p'.val W, hp'.1, heq']
  rw [hL]
  have himg : (Finset.univ.filter (fun p : Fin M => p.val / W = a ∧ y p = 1)).image
        (fun p => p.val % W)
      = (Finset.range W).filter (fun b => ∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, Finset.mem_range, true_and,
      exists_prop]
    constructor
    · rintro ⟨p, ⟨hp1, hp2⟩, rfl⟩
      refine ⟨Nat.mod_lt _ hW, p, ?_, hp2⟩
      rw [← hp1, Nat.mul_comm]
      exact (Nat.div_add_mod p.val W).symm
    · rintro ⟨hb, p, hp, hp2⟩
      refine ⟨p, ⟨?_, hp2⟩, ?_⟩
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
      · rw [hp, Nat.mul_comm a W, Nat.mul_add_mod, Nat.mod_eq_of_lt hb]
  rw [himg]
theorem testBit_packMem (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a b : ℕ)
    (hb : b < W) :
    (packMem W y a).testBit b = decide (∃ p : Fin M, p.val = a * W + b ∧ y p = 1) := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_testBit W _ b hb
theorem packMem_lt (W : ℕ) (hW : 0 < W) {M : ℕ} (y : Fin M → ZMod 2) (a : ℕ) :
    packMem W y a < 2 ^ W := by
  rw [packMem_eq_ofBits W hW]
  exact ofBits_lt W _
theorem decide_zmod2_add (a b : ZMod 2) :
    decide (a + b = 1) = (decide (a = 1) ^^ decide (b = 1)) := by
  fin_cases a <;> fin_cases b <;> decide
theorem decide_row_add {M : ℕ} (q : ℕ) (u z : Fin M → ZMod 2) :
    decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1)
      = (decide (∃ p : Fin M, p.val = q ∧ u p = 1)
          ^^ decide (∃ p : Fin M, p.val = q ∧ z p = 1)) := by
  have hrow : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) → ∀ p' : Fin M,
      p'.val = q → y p' = 1 := by
    intro y hy p' hp'
    obtain ⟨p, hp, hpy⟩ := hy
    have : p' = p := Fin.ext (by rw [hp', hp])
    rwa [this]
  by_cases hex : ∃ p : Fin M, p.val = q
  · obtain ⟨p₀, hp₀⟩ := hex
    have e : ∀ y : Fin M → ZMod 2, (∃ p : Fin M, p.val = q ∧ y p = 1) ↔ y p₀ = 1 := by
      intro y
      exact ⟨fun hy => hrow y hy p₀ hp₀, fun hy => ⟨p₀, hp₀, hy⟩⟩
    have e1 : decide (∃ p : Fin M, p.val = q ∧ (u + z) p = 1) = decide ((u + z) p₀ = 1) := by
      by_cases h : (u + z) p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e (u + z)).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e (u + z)).mp hc))]
    have e2 : decide (∃ p : Fin M, p.val = q ∧ u p = 1) = decide (u p₀ = 1) := by
      by_cases h : u p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e u).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e u).mp hc))]
    have e3 : decide (∃ p : Fin M, p.val = q ∧ z p = 1) = decide (z p₀ = 1) := by
      by_cases h : z p₀ = 1
      · rw [decide_eq_true h, decide_eq_true ((e z).mpr h)]
      · rw [decide_eq_false h, decide_eq_false (fun hc => h ((e z).mp hc))]
    rw [e1, e2, e3]
    show decide (u p₀ + z p₀ = 1) = (decide (u p₀ = 1) ^^ decide (z p₀ = 1))
    exact decide_zmod2_add _ _
  · have h1 : ¬ ∃ p : Fin M, p.val = q ∧ (u + z) p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h2 : ¬ ∃ p : Fin M, p.val = q ∧ u p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    have h3 : ¬ ∃ p : Fin M, p.val = q ∧ z p = 1 :=
      fun hc => hex ⟨hc.choose, hc.choose_spec.1⟩
    rw [decide_eq_false h1, decide_eq_false h2, decide_eq_false h3]
    rfl
theorem packMem_add (W : ℕ) (hW : 0 < W) {M : ℕ} (u z : Fin M → ZMod 2) (a : ℕ) :
    packMem W (u + z) a = packMem W u a ^^^ packMem W z a := by
  refine Nat.eq_of_testBit_eq ?_
  intro b
  by_cases hb : b < W
  · rw [testBit_packMem W hW _ a b hb, Nat.testBit_xor, testBit_packMem W hW _ a b hb,
      testBit_packMem W hW _ a b hb, decide_row_add]
  · have hbW : W ≤ b := by omega
    have h1 : packMem W (u + z) a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h2 : packMem W u a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    have h3 : packMem W z a < 2 ^ b :=
      lt_of_lt_of_le (packMem_lt W hW _ _) (Nat.pow_le_pow_right (by norm_num) hbW)
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_xor, Nat.testBit_lt_two_pow h2,
      Nat.testBit_lt_two_pow h3]
    rfl
def upReset (N : ℕ) : UpIt := { setSt := 1, fromI := 1, m := N, ell := 1 }
def upClimb (k m ell nmax s : ℕ) : UpIt :=
  { setSt := 1, kp := k, m := m, ell := ell, nmax := nmax, kc := k, s := s }
def upStoreIt (N base : ℕ) : UpIt := { srcC := 1, m := N, ell := 1, base := base, mOn := 1 }
def upColIt (k m ell nmax base s : ℕ) : UpIt :=
  { kp := k, m := m, ell := ell, nmax := nmax, kc := k, s := s, base := base, useC := 1, mOn := 1 }
def upCrIt (cidx stride base j : ℕ) : UpIt :=
  { m := 1, ell := 1, base := base, mode := 1, mOn := 1, stride := stride, cidx := cidx, sav := j }
def schemeNmax (sch : RowScheme) : ℕ := ⌈(sch.N : ℝ) / (sch.m : ℝ)⌉₊
def upTabLen (Bc : ℕ) : Node → ℕ
  | .store _ => 0
  | .cr N _ => N * (Bc + 1)
  | .direct sch _ => sch.N * (Bc + 1)
  | .recursive sch _ _ _ child => sch.N * (Bc + 1) + ∑ s : Fin sch.ℓ, upTabLen Bc (child s)
def upHead (N k : ℕ) : List UpIt := if k = 0 then [upReset N] else []
theorem upHead_zero (N : ℕ) : upHead N 0 = [upReset N] := by
  simp [upHead]
theorem upHead_of_ne (N k : ℕ) (h : k ≠ 0) : upHead N k = [] := by
  simp [upHead, h]
def upChildSave (sav skipped : ℕ) : ℕ := sav - 2 * (skipped + 1)
def upSiblingEntry (sav childIndex : ℕ) : UpIt :=
  if childIndex = 0 then upSave sav else upRestore sav
def upSched (CR : CRFamily) (Bc colBase : ℕ) :
    (T : Node) → ℕ → ℕ → ℕ → ℕ → List UpIt → List UpIt
  | .store N, k, base, _, _, path => upHead N k ++ (path ++ [upStoreIt N base])
  | .cr N _, k, base, toff, _, path =>
      upHead N k ++ (path ++ (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) base j))
  | .direct sch _, k, base, toff, _, path =>
      upHead sch.N k ++ (path ++
        (List.range sch.ℓ).map (fun s => upColIt k sch.m sch.ℓ (schemeNmax sch) base s) ++
        (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j))
  | .recursive sch _ _ _ child, k, base, toff, sav, path =>
      upHead sch.N k ++ (path ++
        (List.range Bc).map (fun j =>
          upCrIt (colBase + toff) (Bc + 1) (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) j) ++
        (List.ofFn fun s : Fin sch.ℓ =>
          upSiblingEntry sav s.val :: upSched CR Bc colBase (child s)
            (k + 1 + ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
            (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum)
            (toff + sch.N * (Bc + 1) +
              ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take s.val).sum)
            (upChildSave sav ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
            [upClimb k sch.m sch.ℓ (schemeNmax sch) s]).flatten)
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
theorem add_mod_self (b a : ℕ) : (b + a) % a = b % a := by
  rw [Nat.add_mod, Nat.mod_self, Nat.add_zero, Nat.mod_mod]
theorem add_mod_mod (M c y : ℕ) (hc : c < M) : (c + y % M) % M = (c + y) % M := by
  simp only [Nat.add_mod, Nat.mod_eq_of_lt hc, Nat.mod_mod]
theorem add_sub_mod (M c j : ℕ) (hc : c < M) (hj : j < M) :
    (c + (j + M - c) % M) % M = j := by
  rw [add_mod_mod M c (j + M - c) hc, show c + (j + M - c) = j + M by omega, add_mod_self,
    Nat.mod_eq_of_lt hj]
theorem upClimb_apply (E : RAMEnv) (i k m ell nmax s : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W)
    (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W) (hmem : ∀ x, ab.mem x < 2 ^ E.W)
    (hπ : E.perm k ab.c < 2 ^ E.W)
    (hbit : E.perm k ab.c % m * ell + s < 2 ^ E.W) :
    upApply E i (upClimb k m ell nmax s) ab =
      { mem := ab.mem, c := E.perm k ab.c % m,
        f := ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W } := by
  rw [upApply_eq_body E i (upClimb k m ell nmax s) ab hW
    (by rw [show (upClimb k m ell nmax s).mode = 0 from rfl]; exact Nat.zero_lt_two) hmem]
  have hM : 0 < 2 ^ E.W := pow_pos (by norm_num) _
  have hset1 : (upClimb k m ell nmax s).setSt = 1 := rfl
  have hfrom0 : (upClimb k m ell nmax s).fromI = 0 := rfl
  have hsrc0 : (upClimb k m ell nmax s).srcC = 0 := rfl
  have hkp : (upClimb k m ell nmax s).kp = k := rfl
  have hmit : (upClimb k m ell nmax s).m = m := rfl
  have hellit : (upClimb k m ell nmax s).ell = ell := rfl
  have hsit : (upClimb k m ell nmax s).s = s := rfl
  have hbase0 : (upClimb k m ell nmax s).base = 0 := rfl
  have hmode0 : (upClimb k m ell nmax s).mode = 0 := rfl
  have huse0 : (upClimb k m ell nmax s).useC = 0 := rfl
  have hmn0 : (upClimb k m ell nmax s).mOn = 0 := rfl
  have hZ1 : upvZ1 E (upClimb k m ell nmax s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ1, hkp]
  have hZ2 : upvZ2 E i (upClimb k m ell nmax s) = 0 := by
    simp only [upvZ2, hfrom0, Nat.zero_mul, Nat.zero_mod]
  have hZ3 : upvZ3 E (upClimb k m ell nmax s) = 1 := by
    simp only [upvZ3, hfrom0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ4 : upvZ4 E (upClimb k m ell nmax s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ4, hZ1, hZ3, Nat.mul_one, Nat.mod_mod]
  have hZ5 : upvZ5 E i (upClimb k m ell nmax s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ5, hZ4, hZ2, Nat.add_zero, Nat.mod_mod]
  have hZ6 : upvZ6 E (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvZ6, hsrc0, Nat.zero_mul, Nat.zero_mod]
  have hZ7 : upvZ7 E (upClimb k m ell nmax s) = 1 := by
    simp only [upvZ7, hsrc0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ8 : upvZ8 E i (upClimb k m ell nmax s) ab = E.perm k ab.c % 2 ^ E.W := by
    simp only [upvZ8, hZ5, hZ7, Nat.mul_one, Nat.mod_mod]
  have hImg : upvImg E i (upClimb k m ell nmax s) ab = E.perm k ab.c := by
    simp only [upvImg, hZ8, hZ6, Nat.add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hπ]
  have hltm : E.perm k ab.c % m < 2 ^ E.W := by
    have h := Nat.mod_lt (E.perm k ab.c) hm
    omega
  have hJ0 : upvJ0 E i (upClimb k m ell nmax s) ab = E.perm k ab.c % m := by
    simp only [upvJ0, hImg, hmit, Nat.mod_eq_of_lt hltm]
  have hdv : E.perm k ab.c / m < 2 ^ E.W := by
    have h := Nat.div_le_self (E.perm k ab.c) m
    omega
  have hPos : upvPos E i (upClimb k m ell nmax s) ab = E.perm k ab.c / m := by
    simp only [upvPos, hImg, hmit, Nat.mod_eq_of_lt hdv]
  have hY1 : upvY1 E i (upClimb k m ell nmax s) ab
      = (E.perm k ab.c % m + 2 ^ E.W - ab.c) % 2 ^ E.W := by
    simp only [upvY1, hJ0]
  have hY2 : upvY2 E i (upClimb k m ell nmax s) ab
      = (E.perm k ab.c % m + 2 ^ E.W - ab.c) % 2 ^ E.W := by
    simp only [upvY2, hY1, hset1, Nat.mul_one, Nat.mod_mod]
  have hCn : upvCn E i (upClimb k m ell nmax s) ab = E.perm k ab.c % m := by
    rw [upvCn, hY2]
    exact add_sub_mod (2 ^ E.W) ab.c (E.perm k ab.c % m) hc hltm
  have hY7 : upvY7 E (upClimb k m ell nmax s) = 1 := by
    simp only [upvY7, hfrom0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hY6 : upvY6 E i (upClimb k m ell nmax s) ab
      = ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W := by
    simp only [upvY6]
  have hY8 : upvY8 E i (upClimb k m ell nmax s) ab
      = ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W := by
    simp only [upvY8, hY6, hY7, Nat.mul_one, Nat.mod_mod]
  have hY9 : upvY9 E i (upClimb k m ell nmax s) ab
      = ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W := by
    simp only [upvY9, hY8, hfrom0, Nat.add_zero, Nat.mod_mod]
  have hY10 : upvY10 E i (upClimb k m ell nmax s) ab
      = (ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W + 2 ^ E.W - ab.f)
          % 2 ^ E.W := by
    simp only [upvY10, hY9]
  have hY11 : upvY11 E i (upClimb k m ell nmax s) ab
      = (ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W + 2 ^ E.W - ab.f)
          % 2 ^ E.W := by
    simp only [upvY11, hY10, hset1, Nat.mul_one, Nat.mod_mod]
  have hFn : upvFn E i (upClimb k m ell nmax s) ab
      = ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W := by
    rw [upvFn, hY11]
    exact add_sub_mod (2 ^ E.W) ab.f
      (ab.f * upvCoin E i (upClimb k m ell nmax s) ab % 2 ^ E.W) hf (Nat.mod_lt _ hM)
  have hellt : E.perm k ab.c % m * ell < 2 ^ E.W := by omega
  have hY3 : upvY3 E i (upClimb k m ell nmax s) ab
      = E.perm k ab.c % m * ell % 2 ^ E.W := by
    simp only [upvY3, hJ0, hellit]
  have hQ : upvQ E i (upClimb k m ell nmax s) ab
      = (E.perm k ab.c % m * ell % 2 ^ E.W + s) % 2 ^ E.W := by
    simp only [upvQ, hY3, hsit]
  have hX7 : upvX7 E i (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvX7, hmode0, Nat.mul_zero, Nat.zero_mod]
  have hX8 : upvX8 E i (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvX8, hX7, hbase0, Nat.zero_add, Nat.zero_mod]
  have hBit : upvBit E i (upClimb k m ell nmax s) ab = E.perm k ab.c % m * ell + s := by
    rw [upvBit, hX8, Nat.zero_add, hQ, Nat.mod_mod, Nat.mod_eq_of_lt hellt,
      Nat.mod_eq_of_lt hbit]
  have hX1 : upvX1 E (upClimb k m ell nmax s) = 1 := by
    simp only [upvX1, huse0, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hX2 : upvX2 E i (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvX2, huse0, Nat.zero_mul, Nat.zero_mod]
  have hW0 : upvW0 E i (upClimb k m ell nmax s) ab = 1 := by
    simp only [upvW0, hX2, hX1, Nat.zero_add, Nat.mod_eq_of_lt hW]
  have hX10 : upvX10 E i (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvX10, hmode0, Nat.mul_zero, Nat.zero_mod]
  have hWt : upvWt E i (upClimb k m ell nmax s) ab = 1 := by
    simp only [upvWt, hX10, hW0, Nat.zero_add, Nat.mod_eq_of_lt hW]
  have hMask0 : upvMask0 E i (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvMask0, hmn0, Nat.mul_zero, Nat.zero_mod]
  have hMask : upvMask E i (upClimb k m ell nmax s) ab = 0 := by
    simp only [upvMask, hMask0, Nat.zero_mul, Nat.zero_mod]
  have hOld : upvOld E i (upClimb k m ell nmax s) ab
      = ab.mem (upvWi E i (upClimb k m ell nmax s) ab) :=
    Nat.mod_eq_of_lt (hmem _)
  have hNew : upvNew E i (upClimb k m ell nmax s) ab
      = ab.mem (upvWi E i (upClimb k m ell nmax s) ab) := by
    rw [upvNew, hOld, hMask, Nat.xor_zero, Nat.mod_eq_of_lt (hmem _)]
  have hMem : Function.update ab.mem (upvWi E i (upClimb k m ell nmax s) ab)
      (ab.mem (upvWi E i (upClimb k m ell nmax s) ab)) = ab.mem := by
    funext x
    by_cases hx : x = upvWi E i (upClimb k m ell nmax s) ab
    · simp [Function.update, hx]
    · simp [Function.update, hx]
  simp only [upApplyBody]
  rw [hNew, hMem, hCn, hFn]
theorem take_sum_mono (l : List ℕ) : ∀ (s s' : ℕ), s ≤ s' → (l.take s).sum ≤ (l.take s').sum := by
  induction l with
  | nil => intro s s' _; simp
  | cons a t ih =>
    intro s s' h
    cases s with
    | zero => simp
    | succ s0 =>
      cases s' with
      | zero => omega
      | succ s0' =>
        rw [List.take_succ_cons, List.take_succ_cons, List.sum_cons, List.sum_cons]
        have h' := ih s0 s0' (by omega)
        omega
theorem take_sum_succ_ofFn {ℓ : ℕ} (f : Fin ℓ → ℕ) (s : ℕ) (hs : s < ℓ) :
    ((List.ofFn f).take (s + 1)).sum = ((List.ofFn f).take s).sum + f ⟨s, hs⟩ := by
  have hlen : s < (List.ofFn f).length := by simpa [List.length_ofFn] using hs
  have htake : (List.ofFn f).take (s + 1) = (List.ofFn f).take s ++ [(List.ofFn f)[s]'hlen] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hlen, Option.toList_some]
  have hget : (List.ofFn f)[s]'hlen = f ⟨s, hs⟩ := by
    rw [List.getElem_ofFn]
  rw [htake, hget]
  simp
theorem take_sum_full_ofFn {ℓ : ℕ} (f : Fin ℓ → ℕ) :
    ((List.ofFn f).take ℓ).sum = ∑ s, f s := by
  rw [show (List.ofFn f).take ℓ = List.ofFn f from by simp, List.sum_ofFn]
def packSel (W : ℕ) (S : Finset ℕ) : ℕ → ℕ :=
  fun a => ofBits W (fun b => decide (a * W + b ∈ S))
theorem packSel_lt (W : ℕ) (S : Finset ℕ) (a : ℕ) : packSel W S a < 2 ^ W :=
  ofBits_lt W _
theorem packSel_testBit (W : ℕ) (S : Finset ℕ) (a b : ℕ) (hb : b < W) :
    (packSel W S a).testBit b = decide (a * W + b ∈ S) :=
  ofBits_testBit W _ b hb
theorem packSel_empty (W a : ℕ) : packSel W (∅ : Finset ℕ) a = 0 := by
  unfold packSel ofBits
  simp
theorem packSel_union (W : ℕ) {A B : Finset ℕ} (h : Disjoint A B) (a : ℕ) :
    packSel W (A ∪ B) a = packSel W A a ^^^ packSel W B a := by
  refine Nat.eq_of_testBit_eq (fun b => ?_)
  by_cases hb : b < W
  · rw [packSel_testBit W _ a b hb, Nat.testBit_xor, packSel_testBit W _ a b hb,
      packSel_testBit W _ a b hb]
    have hd : ¬ (a * W + b ∈ A ∧ a * W + b ∈ B) := fun hc =>
      Finset.disjoint_left.mp h hc.1 hc.2
    by_cases h1 : a * W + b ∈ A
    · by_cases h2 : a * W + b ∈ B
      · exact absurd ⟨h1, h2⟩ hd
      · simp [Finset.mem_union, h1, h2]
    · by_cases h2 : a * W + b ∈ B
      · simp [Finset.mem_union, h1, h2]
      · simp [Finset.mem_union, h1, h2]
  · have hbW : W ≤ b := by omega
    have e1 : packSel W (A ∪ B) a < 2 ^ b :=
      lt_of_lt_of_le (packSel_lt W _ a) (Nat.pow_le_pow_right (by norm_num) hbW)
    have e2 : packSel W A a < 2 ^ b :=
      lt_of_lt_of_le (packSel_lt W _ a) (Nat.pow_le_pow_right (by norm_num) hbW)
    have e3 : packSel W B a < 2 ^ b :=
      lt_of_lt_of_le (packSel_lt W _ a) (Nat.pow_le_pow_right (by norm_num) hbW)
    rw [Nat.testBit_lt_two_pow e1, Nat.testBit_xor, Nat.testBit_lt_two_pow e2,
      Nat.testBit_lt_two_pow e3]
    rfl
theorem upFold_append (E : RAMEnv) (i : ℕ) (ab : UpAbs) (l₁ l₂ : List UpIt) :
    upFold E i ab (l₁ ++ l₂) = upFold E i (upFold E i ab l₁) l₂ := by
  induction l₁ generalizing ab with
  | nil => rfl
  | cons it rest ih =>
      simp only [List.cons_append, upFold]
      exact ih (upApply E i it ab)
theorem packSel_eq_sum (W : ℕ) (hW : 0 < W) (S : Finset ℕ) (a : ℕ) :
    packSel W S a = ∑ q ∈ S.filter (fun q => q / W = a), 2 ^ (q % W) := by
  unfold packSel
  rw [ofBits, ← Finset.sum_filter]
  have hbij : (S.filter (fun q => q / W = a))
      = ((Finset.range W).filter (fun b => a * W + b ∈ S)).image (fun b => a * W + b) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨hqS, hqW⟩
      have hdm : a * W + q % W = q := by rw [← hqW, Nat.mul_comm]; exact Nat.div_add_mod q W
      exact ⟨q % W, ⟨Nat.mod_lt q hW, by rwa [hdm]⟩, hdm⟩
    · rintro ⟨b, ⟨hb, hbS⟩, rfl⟩
      refine ⟨hbS, ?_⟩
      rw [Nat.mul_comm a W, Nat.mul_add_div hW, Nat.div_eq_of_lt hb, Nat.add_zero]
  have hstep : (∑ q ∈ S.filter (fun q => q / W = a), 2 ^ (q % W))
      = ∑ b ∈ (Finset.range W).filter (fun b => a * W + b ∈ S), 2 ^ b := by
    rw [hbij]
    rw [Finset.sum_image (fun x _ y _ h => by omega)]
    refine Finset.sum_congr rfl ?_
    intro b hb
    rw [Finset.mem_filter, Finset.mem_range] at hb
    rw [Nat.mul_comm a W, Nat.mul_add_mod, Nat.mod_eq_of_lt hb.1]
  rw [hstep]
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext b
  simp only [Finset.mem_filter, decide_eq_true_eq]
theorem packMem_eq_packSel (W : ℕ) (hW : 0 < W) {M : ℕ} (z : Fin M → ZMod 2) (a : ℕ) :
    packMem W z a
      = packSel W ((Finset.univ.filter (fun p : Fin M => z p = 1)).image (fun p => p.val)) a := by
  rw [packMem, packSel_eq_sum W hW]
  have himg : ((Finset.univ.filter (fun p : Fin M => z p = 1)).image (fun p => p.val)).filter
        (fun q => q / W = a)
      = ((Finset.univ.filter (fun p : Fin M => z p = 1)).filter
          (fun p => p.val / W = a)).image (fun p => p.val) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨p, hp, rfl⟩, hq⟩
      exact ⟨p, ⟨hp, hq⟩, rfl⟩
    · rintro ⟨p, ⟨hp, hq⟩, rfl⟩
      exact ⟨⟨p, hp, rfl⟩, hq⟩
  rw [himg]
  rw [Finset.sum_image (fun x _ y _ h => Fin.ext h)]
  rw [Finset.filter_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro p _
  by_cases h1 : z p = 1 <;> by_cases h2 : p.val / W = a <;> simp [h1, h2]
def upOwnItems (CR : CRFamily) (Bc colBase : ℕ) : (T : Node) → ℕ → ℕ → ℕ → List UpIt
  | .store N, _, base, _ => [upStoreIt N base]
  | .cr N _, _, base, toff =>
      (List.range Bc).map (fun j => upCrIt (colBase + toff) (Bc + 1) base j)
  | .direct sch _, k, base, toff =>
      (List.range sch.ℓ).map (fun s => upColIt k sch.m sch.ℓ (schemeNmax sch) base s) ++
        (List.range Bc).map (fun j =>
          upCrIt (colBase + toff) (Bc + 1) (base + sch.m * sch.ℓ) j)
  | .recursive sch _ _ _ child, _, base, toff =>
      (List.range Bc).map (fun j =>
        upCrIt (colBase + toff) (Bc + 1)
          (base + ∑ s : Fin sch.ℓ, synLen CR (child s)) j)
def upKids (CR : CRFamily) (Bc colBase : ℕ) : (T : Node) → ℕ → ℕ → ℕ → ℕ → List UpIt → List UpIt
  | .store _, _, _, _, _, _ => []
  | .cr _ _, _, _, _, _, _ => []
  | .direct _ _, _, _, _, _, _ => []
  | .recursive sch _ _ _ child, k, base, toff, sav, path =>
      (List.ofFn fun s : Fin sch.ℓ =>
        upSiblingEntry sav s.val :: upSched CR Bc colBase (child s)
          (k + 1 + ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
          (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum)
          (toff + sch.N * (Bc + 1) +
            ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take s.val).sum)
          (upChildSave sav ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
          [upClimb k sch.m sch.ℓ (schemeNmax sch) s]).flatten
theorem upSched_decomp (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (k base toff sav : ℕ)
    (path : List UpIt) :
    upSched CR Bc colBase T k base toff sav path
      = upHead (Node.N T) k ++ (path ++ upOwnItems CR Bc colBase T k base toff
          ++ upKids CR Bc colBase T k base toff sav path) := by
  cases T with
  | store N =>
      simp only [upSched, upOwnItems, upKids, Node.N, List.append_nil, List.append_assoc]
  | cr N t =>
      simp only [upSched, upOwnItems, upKids, Node.N, List.append_nil, List.append_assoc]
  | direct sch t =>
      simp only [upSched, upOwnItems, upKids, Node.N, List.append_nil, List.append_assoc]
  | recursive sch t X Y child =>
      simp only [upSched, upOwnItems, upKids, Node.N, List.append_nil, List.append_assoc]
theorem upReset_apply_mod (E : RAMEnv) (i N : ℕ) (ab : UpAbs)
    (hW : 1 < 2 ^ E.W) (hN : 0 < N) (hNM : N ≤ 2 ^ E.W) (hiM : i < 2 ^ E.W)
    (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W) (hmem : ∀ x, ab.mem x < 2 ^ E.W) :
    upApply E i (upReset N) ab = { mem := ab.mem, c := i % N, f := 1 } := by
  have hset : (upReset N).setSt = 1 := rfl
  have hfrom : (upReset N).fromI = 1 := rfl
  have hsrc : (upReset N).srcC = 0 := rfl
  have hm : (upReset N).m = N := rfl
  have hmn : (upReset N).mOn = 0 := rfl
  have hlt : i % N < 2 ^ E.W := by
    have h := Nat.mod_lt i hN
    omega
  have hZ2 : upvZ2 E i (upReset N) = i := by
    simp only [upvZ2, hfrom, Nat.mod_eq_of_lt hiM, one_mul]
  have hZ3 : upvZ3 E (upReset N) = 0 := by
    simp only [upvZ3, hfrom, Nat.mod_eq_of_lt hW]
    rw [show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self]
  have hZ4 : upvZ4 E (upReset N) ab = 0 := by
    simp only [upvZ4, hZ3, Nat.mul_zero, Nat.zero_mod]
  have hZ5 : upvZ5 E i (upReset N) ab = i := by
    simp only [upvZ5, hZ4, hZ2, Nat.zero_add, Nat.mod_eq_of_lt hiM]
  have hZ6 : upvZ6 E (upReset N) ab = 0 := by
    simp only [upvZ6, hsrc, Nat.zero_mul, Nat.zero_mod]
  have hZ7 : upvZ7 E (upReset N) = 1 := by
    simp only [upvZ7, hsrc, Nat.mod_eq_of_lt hW, Nat.sub_zero]
    rw [add_mod_self, Nat.mod_eq_of_lt hW]
  have hZ8 : upvZ8 E i (upReset N) ab = i := by
    simp only [upvZ8, hZ5, hZ7, Nat.mul_one, Nat.mod_eq_of_lt hiM]
  have hImg : upvImg E i (upReset N) ab = i := by
    simp only [upvImg, hZ8, hZ6, Nat.add_zero, Nat.mod_eq_of_lt hiM]
  have hJ0 : upvJ0 E i (upReset N) ab = i % N := by
    simp only [upvJ0, hImg, hm]
    rw [Nat.mod_eq_of_lt hlt]
  have hY2 : upvY2 E i (upReset N) ab = (i % N + 2 ^ E.W - ab.c) % 2 ^ E.W := by
    simp only [upvY2, upvY1, hJ0, hset, Nat.mul_one, Nat.mod_mod]
  have hCn : upvCn E i (upReset N) ab = i % N := by
    rw [upvCn, hY2]
    exact add_sub_mod (2 ^ E.W) ab.c (i % N) hc hlt
  have hY7 : upvY7 E (upReset N) = 0 := by
    simp only [upvY7, hfrom, Nat.mod_eq_of_lt hW]
    rw [show 1 + 2 ^ E.W - 1 = 2 ^ E.W by omega, Nat.mod_self]
  have hY8 : upvY8 E i (upReset N) ab = 0 := by
    simp only [upvY8, hY7, Nat.mul_zero, Nat.zero_mod]
  have hY9 : upvY9 E i (upReset N) ab = 1 := by
    simp only [upvY9, hY8, hfrom, Nat.zero_add, Nat.mod_eq_of_lt hW]
  have hY10 : upvY10 E i (upReset N) ab = (1 + 2 ^ E.W - ab.f) % 2 ^ E.W := by
    simp only [upvY10, hY9]
  have hY11 : upvY11 E i (upReset N) ab = (1 + 2 ^ E.W - ab.f) % 2 ^ E.W := by
    simp only [upvY11, upvY10, hY9, hset, Nat.mul_one, Nat.mod_mod]
  have hFn : upvFn E i (upReset N) ab = 1 := by
    rw [upvFn, hY11]
    rw [add_sub_mod (2 ^ E.W) ab.f 1 hf hW]
  have hMask0 : upvMask0 E i (upReset N) ab = 0 := by
    simp only [upvMask0, hmn, Nat.mul_zero, Nat.zero_mod]
  have hMask : upvMask E i (upReset N) ab = 0 := by
    simp only [upvMask, hMask0, Nat.zero_mul, Nat.zero_mod]
  have hOld : upvOld E i (upReset N) ab = ab.mem (upvWi E i (upReset N) ab) :=
    Nat.mod_eq_of_lt (hmem _)
  have hNew : upvNew E i (upReset N) ab = ab.mem (upvWi E i (upReset N) ab) := by
    rw [upvNew, hOld, hMask, Nat.xor_zero, Nat.mod_eq_of_lt (hmem _)]
  have hMem : Function.update ab.mem (upvWi E i (upReset N) ab)
      (ab.mem (upvWi E i (upReset N) ab)) = ab.mem := by
    funext x
    by_cases hx : x = upvWi E i (upReset N) ab
    · simp [Function.update, hx]
    · simp [Function.update, hx]
  have hmode : (upReset N).mode < 2 := by simp [upReset]
  rw [upApply_eq_body E i (upReset N) ab hW hmode hmem]
  unfold upApplyBody
  rw [hNew, hMem, hCn, hFn]
theorem upSched_root (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (base toff sav : ℕ) :
    upSched CR Bc colBase T 0 base toff sav [] =
      upReset (Node.N T) :: (upOwnItems CR Bc colBase T 0 base toff
        ++ upKids CR Bc colBase T 0 base toff sav []) := by
  rw [upSched_decomp, upHead_zero]
  simp
theorem upSched_nonroot (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (k base toff sav : ℕ)
    (path : List UpIt) (hk : k ≠ 0) :
    upSched CR Bc colBase T k base toff sav path
      = path ++ upOwnItems CR Bc colBase T k base toff
          ++ upKids CR Bc colBase T k base toff sav path := by
  rw [upSched_decomp, upHead_of_ne _ _ hk]
  simp
theorem upFold_climb_single (E : RAMEnv) (i k m ell nmax s : ℕ) (a : UpAbs)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W)
    (hc : a.c < 2 ^ E.W) (hf : a.f < 2 ^ E.W) (hmem : ∀ x, a.mem x < 2 ^ E.W)
    (hπ : E.perm k a.c < 2 ^ E.W) (hbit : E.perm k a.c % m * ell + s < 2 ^ E.W) :
    upFold E i a [upClimb k m ell nmax s]
      = ⟨a.mem, E.perm k a.c % m, a.f * upvCoin E i (upClimb k m ell nmax s) a % 2 ^ E.W⟩ := by
  simp only [upFold]
  exact upClimb_apply E i k m ell nmax s a hW hm hmM hc hf hmem hπ hbit
noncomputable def bitBlock (CR : CRFamily) (T : Node) (r : Node.Seed T) (x : Finset ℕ) (base : ℕ) :
    Finset ℕ :=
  (colSupp CR T r x).image (fun p => base + p.val)
theorem mem_bitBlock {CR : CRFamily} {T : Node} {r : Node.Seed T} {x : Finset ℕ} {base a : ℕ} :
    a ∈ bitBlock CR T r x base ↔
      ∃ p : Fin (synLen CR T), bitVal CR T r p x = 1 ∧ a = base + p.val := by
  unfold bitBlock colSupp
  rw [Finset.mem_image]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, (Finset.mem_filter.mp hp).2, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩
theorem bitVal_rec_left {CR : CRFamily} {sch : RowScheme} {t : ℕ} {Xs Ys : Fin sch.ℓ → ℕ}
    {child : Fin sch.ℓ → Node} (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ)
    (q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s))) :
    bitVal CR (.recursive sch t Xs Ys child) r (Fin.castAdd (CR.rows sch.N t) q) x
      = bitVal CR (child (finSigmaFinEquiv.symm q).1) (r.2 (finSigmaFinEquiv.symm q).1)
          (finSigmaFinEquiv.symm q).2 (sch.column r.1 x (finSigmaFinEquiv.symm q).1) := by
  simp only [bitVal, Fin.append_left]
theorem bitVal_rec_right {CR : CRFamily} {sch : RowScheme} {t : ℕ} {Xs Ys : Fin sch.ℓ → ℕ}
    {child : Fin sch.ℓ → Node} (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ)
    (q : Fin (CR.rows sch.N t)) :
    bitVal CR (.recursive sch t Xs Ys child) r
        (Fin.natAdd (∑ s : Fin sch.ℓ, synLen CR (child s)) q) x
      = if (q.val : ℕ) ∈ CR.sketch sch.N t x then 1 else 0 := by
  simp only [bitVal, Fin.append_right]
theorem bitBlock_recursive {CR : CRFamily} {sch : RowScheme} {t : ℕ} {Xs Ys : Fin sch.ℓ → ℕ}
    {child : Fin sch.ℓ → Node} (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ)
    (base : ℕ) :
    bitBlock CR (.recursive sch t Xs Ys child) r x base
      = ((Finset.univ.filter (fun q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s)) =>
            bitVal CR (child (finSigmaFinEquiv.symm q).1) (r.2 (finSigmaFinEquiv.symm q).1)
              (finSigmaFinEquiv.symm q).2 (sch.column r.1 x (finSigmaFinEquiv.symm q).1) = 1)).image
            (fun q => base + q.val))
        ∪ ((Finset.univ.filter (fun q : Fin (CR.rows sch.N t) =>
              (q.val : ℕ) ∈ CR.sketch sch.N t x)).image
            (fun q => base + ((∑ s : Fin sch.ℓ, synLen CR (child s)) + q.val))) := by
  ext a
  rw [mem_bitBlock]
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_cases hlt : p.val < ∑ s : Fin sch.ℓ, synLen CR (child s)
    · have hp' : p = Fin.castAdd (CR.rows sch.N t) ⟨p.val, hlt⟩ := Fin.ext rfl
      rw [hp', bitVal_rec_left] at hp
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_image.mpr
        ⟨⟨p.val, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩, rfl⟩))
    · have hlt2 : p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)) < CR.rows sch.N t := by
        have := p.isLt
        simp only [synLen] at this
        omega
      have hp' : p = Fin.natAdd (∑ s : Fin sch.ℓ, synLen CR (child s))
          ⟨p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)), hlt2⟩ := by
        apply Fin.ext
        simp only [Fin.val_natAdd]
        omega
      rw [hp', bitVal_rec_right] at hp
      have hmem : ((⟨p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)), hlt2⟩ :
          Fin (CR.rows sch.N t)).val : ℕ) ∈ CR.sketch sch.N t x := by
        by_cases hc : ((⟨p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)), hlt2⟩ :
            Fin (CR.rows sch.N t)).val : ℕ) ∈ CR.sketch sch.N t x
        · exact hc
        · rw [if_neg hc] at hp
          exact absurd hp zero_ne_one
      refine Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr
        ⟨⟨p.val - (∑ s : Fin sch.ℓ, synLen CR (child s)), hlt2⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩, ?_⟩))
      show base + ((∑ s : Fin sch.ℓ, synLen CR (child s))
        + (p.val - ∑ s : Fin sch.ℓ, synLen CR (child s))) = base + p.val
      omega
  · intro h
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      exact ⟨Fin.castAdd (CR.rows sch.N t) q,
        by rw [bitVal_rec_left]; exact (Finset.mem_filter.mp hq).2, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp h
      refine ⟨Fin.natAdd (∑ s : Fin sch.ℓ, synLen CR (child s)) q, ?_, ?_⟩
      · rw [bitVal_rec_right, if_pos (Finset.mem_filter.mp hq).2]
      · simp only [Fin.val_natAdd]
universe u
theorem schemeNodes_recursive (sch : RowScheme) (t : ℕ) (Xs Ys : Fin sch.ℓ → ℕ)
    (child : Fin sch.ℓ → Node) :
    schemeNodes (.recursive sch t Xs Ys child)
      = [.recursive sch t Xs Ys child]
        ++ (List.ofFn fun i : Fin sch.ℓ => schemeNodes (child i)).flatten := rfl
theorem take_sum_add_getElem_le : ∀ (l : List ℕ) (s v : ℕ), l[s]? = some v →
    (l.take s).sum + v ≤ l.sum
  | [], s, v, h => by simp at h
  | a :: t, 0, v, h => by
      have hv : a = v := by simpa using h
      simp only [List.take_zero, List.sum_nil, Nat.zero_add, List.sum_cons]
      omega
  | a :: t, (s + 1), v, h => by
      have h' : t[s]? = some v := by simpa using h
      have ih := take_sum_add_getElem_le t s v h'
      have htake : (a :: t).take (s + 1) = a :: t.take s := rfl
      have hsum : (a :: t).sum = a + t.sum := rfl
      rw [htake, hsum, List.sum_cons]
      omega
theorem getElem?_ofFn' {α : Type u} {n : ℕ} (f : Fin n → α) (s : Fin n) :
    (List.ofFn f)[s.val]? = some (f s) := by
  rw [List.getElem?_ofFn, dif_pos s.isLt]
theorem flatten_length_eq_sum {α : Type u} :
    ∀ (n : ℕ) (f : Fin n → List α),
      (List.ofFn f).flatten.length = (List.ofFn fun i : Fin n => (f i).length).sum
  | 0, _ => rfl
  | n + 1, f => by
      have ih := flatten_length_eq_sum n (fun i : Fin n => f i.succ)
      simp only [List.ofFn_succ, List.flatten_cons, List.length_append, List.sum_cons] at ih ⊢
      omega
theorem colSupp_empty (CR : CRFamily) (T : Node) (r : Node.Seed T) :
    colSupp CR T r ∅ = ∅ := by
  refine Finset.eq_empty_iff_forall_notMem.mpr ?_
  intro p hp
  rw [colSupp, Finset.mem_filter] at hp
  rw [bitVal_empty] at hp
  exact zero_ne_one hp.2
theorem bitBlock_empty (CR : CRFamily) (T : Node) (r : Node.Seed T) (base : ℕ) :
    bitBlock CR T r ∅ base = ∅ := by
  unfold bitBlock
  rw [colSupp_empty, Finset.image_empty]
theorem take_sum_ofFn_eq_sum_fin {n : ℕ} (f : Fin n → ℕ) {s : ℕ} (hs : s ≤ n) :
    ((List.ofFn f).take s).sum
      = ∑ i : Fin s, f ⟨i.val, lt_of_lt_of_le i.isLt hs⟩ := by
  induction s with
  | zero => simp
  | succ k ih =>
      rw [take_sum_succ_ofFn f k (by omega), ih (by omega), Fin.sum_univ_castSucc]
      simp
theorem finSigmaFinEquiv_val {m : ℕ} (n : Fin m → ℕ) (s : Fin m) (j : Fin (n s)) :
    (finSigmaFinEquiv (⟨s, j⟩ : Sigma fun i => Fin (n i))).val
      = ((List.ofFn n).take s.val).sum + j.val := by
  rw [finSigmaFinEquiv_apply, take_sum_ofFn_eq_sum_fin n (le_of_lt s.isLt)]
  congr 1
theorem finSigmaFinEquiv_symm_val {m : ℕ} (n : Fin m → ℕ) (q : Fin (∑ i, n i)) :
    q.val = ((List.ofFn n).take (finSigmaFinEquiv.symm q).1.val).sum
      + (finSigmaFinEquiv.symm q).2.val := by
  conv_lhs => rw [← Equiv.apply_symm_apply finSigmaFinEquiv q]
  exact finSigmaFinEquiv_val n (finSigmaFinEquiv.symm q).1 (finSigmaFinEquiv.symm q).2
theorem take_sum_ofFn_mono {n : ℕ} (f : Fin n → ℕ) {s s' : ℕ} (h : s ≤ s') :
    ((List.ofFn f).take s).sum ≤ ((List.ofFn f).take s').sum :=
  take_sum_mono (List.ofFn f) s s' h
theorem take_sum_kids_succ {CR : CRFamily} {sch : RowScheme} {child : Fin sch.ℓ → Node}
    (s : Fin sch.ℓ) :
    ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take (s.val + 1)).sum
      = ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum
        + synLen CR (child s) := by
  rw [take_sum_succ_ofFn (fun i : Fin sch.ℓ => synLen CR (child i)) s.val s.isLt]
theorem take_sum_kids_block_le {CR : CRFamily} {sch : RowScheme} {child : Fin sch.ℓ → Node}
    {s s' : Fin sch.ℓ} (h : s.val < s'.val) :
    ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum
        + synLen CR (child s)
      ≤ ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s'.val).sum := by
  have h1 := take_sum_kids_succ (CR := CR) (sch := sch) (child := child) s
  have h2 := take_sum_ofFn_mono (fun i : Fin sch.ℓ => synLen CR (child i))
    (s := s.val + 1) (s' := s'.val) (by omega)
  omega
theorem kids_take_sum_succ_le {CR : CRFamily} {sch : RowScheme} {child : Fin sch.ℓ → Node}
    (s : Fin sch.ℓ) :
    ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum
        + synLen CR (child s)
      ≤ ∑ i : Fin sch.ℓ, synLen CR (child i) := by
  have h1 := take_sum_kids_succ (CR := CR) (sch := sch) (child := child) s
  have h2 := take_sum_ofFn_mono (fun i : Fin sch.ℓ => synLen CR (child i))
    (s := s.val + 1) (s' := sch.ℓ) (by omega)
  have h3 := take_sum_full_ofFn (fun i : Fin sch.ℓ => synLen CR (child i))
  omega
theorem bitBlock_recursive_kids {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ) (base : ℕ) :
    ((Finset.univ.filter (fun q : Fin (∑ s : Fin sch.ℓ, synLen CR (child s)) =>
        bitVal CR (child (finSigmaFinEquiv.symm q).1) (r.2 (finSigmaFinEquiv.symm q).1)
          (finSigmaFinEquiv.symm q).2 (sch.column r.1 x (finSigmaFinEquiv.symm q).1) = 1)).image
        (fun q => base + q.val))
      = Finset.univ.biUnion (fun s : Fin sch.ℓ =>
          bitBlock CR (child s) (r.2 s) (sch.column r.1 x s)
            (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum)) := by
  ext a
  rw [Finset.mem_image, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨-, hb⟩ := Finset.mem_filter.mp hq
    refine ⟨(finSigmaFinEquiv.symm q).1, Finset.mem_univ _, ?_⟩
    rw [mem_bitBlock]
    exact ⟨(finSigmaFinEquiv.symm q).2, hb, by rw [finSigmaFinEquiv_symm_val]; omega⟩
  · rintro ⟨s, -, ha⟩
    rw [mem_bitBlock] at ha
    obtain ⟨p, hp, rfl⟩ := ha
    refine ⟨finSigmaFinEquiv (⟨s, p⟩ : Sigma fun i => Fin (synLen CR (child i))), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.symm_apply_apply]
      exact hp
    · rw [finSigmaFinEquiv_val]
      omega
theorem disjoint_bitBlock_kids {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ) (base : ℕ)
    {s s' : Fin sch.ℓ} (h : s ≠ s') :
    Disjoint (bitBlock CR (child s) (r.2 s) (sch.column r.1 x s)
        (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum))
      (bitBlock CR (child s') (r.2 s') (sch.column r.1 x s')
        (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s'.val).sum)) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  rw [mem_bitBlock] at ha hb
  obtain ⟨p, -, rfl⟩ := ha
  obtain ⟨p', -, rfl⟩ := hb
  have hne : s.val ≠ s'.val := fun he => h (Fin.ext he)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := take_sum_kids_block_le (CR := CR) (sch := sch) (child := child) hlt
    have hp : p.val < synLen CR (child s) := p.isLt
    have hp' : p'.val < synLen CR (child s') := p'.isLt
    omega
  · have h1 := take_sum_kids_block_le (CR := CR) (sch := sch) (child := child) hlt
    have hp : p.val < synLen CR (child s) := p.isLt
    have hp' : p'.val < synLen CR (child s') := p'.isLt
    omega
theorem disjoint_bitBlock_own_kids {CR : CRFamily} {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (r : Node.Seed (.recursive sch t Xs Ys child)) (x : Finset ℕ) (base : ℕ) :
    Disjoint ((Finset.univ.filter (fun q : Fin (CR.rows sch.N t) =>
        (q.val : ℕ) ∈ CR.sketch sch.N t x)).image
        (fun q => base + ((∑ i : Fin sch.ℓ, synLen CR (child i)) + q.val)))
      (Finset.univ.biUnion (fun s : Fin sch.ℓ =>
        bitBlock CR (child s) (r.2 s) (sch.column r.1 x s)
          (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum))) := by
  rw [Finset.disjoint_iff_ne]
  intro a ha b hb
  rw [Finset.mem_image] at ha
  obtain ⟨q, -, rfl⟩ := ha
  rw [Finset.mem_biUnion] at hb
  obtain ⟨s, -, hb⟩ := hb
  rw [mem_bitBlock] at hb
  obtain ⟨p, -, rfl⟩ := hb
  have h1 := kids_take_sum_succ_le (CR := CR) (sch := sch) (child := child) s
  have hp : p.val < synLen CR (child s) := p.isLt
  omega
theorem foldl_xor_const {β : Type} (f : β → ℕ) (c : ℕ) :
    ∀ (l : List β), l.foldl (fun acc x => acc ^^^ f x) c
      = c ^^^ l.foldl (fun acc x => acc ^^^ f x) 0
  | [] => by simp
  | x :: rest => by
      have h1 : (x :: rest).foldl (fun acc x => acc ^^^ f x) c
          = rest.foldl (fun acc x => acc ^^^ f x) (c ^^^ f x) := rfl
      have h2 : (x :: rest).foldl (fun acc x => acc ^^^ f x) 0
          = rest.foldl (fun acc x => acc ^^^ f x) (0 ^^^ f x) := rfl
      rw [h1, h2, foldl_xor_const f (c ^^^ f x) rest, foldl_xor_const f (0 ^^^ f x) rest,
        Nat.zero_xor, Nat.xor_assoc]
theorem packSel_biUnion_ofFn (W : ℕ) :
    ∀ (ℓ : ℕ) (B : Fin ℓ → Finset ℕ),
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      ∀ a : ℕ, packSel W (Finset.univ.biUnion B) a
        = (List.ofFn B).foldl (fun acc A => acc ^^^ packSel W A a) 0
  | 0, B, _, a => by simp [packSel_empty]
  | n + 1, B, hdisj, a => by
      have hstep : (Finset.univ : Finset (Fin (n + 1))).biUnion B
          = B 0 ∪ Finset.univ.biUnion (fun i : Fin n => B i.succ) := by
        ext x
        rw [Finset.mem_union, Finset.mem_biUnion, Finset.mem_biUnion]
        constructor
        · rintro ⟨s, -, hs⟩
          match s with
          | ⟨0, _⟩ => exact Or.inl hs
          | ⟨k + 1, hk⟩ => exact Or.inr ⟨⟨k, by omega⟩, Finset.mem_univ _, hs⟩
        · rintro (h | ⟨i, -, hi⟩)
          · exact ⟨0, Finset.mem_univ _, h⟩
          · exact ⟨Fin.succ i, Finset.mem_univ _, hi⟩
      have hdisj' : Disjoint (B 0) (Finset.univ.biUnion (fun i : Fin n => B i.succ)) := by
        rw [Finset.disjoint_iff_ne]
        intro x hx y hy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨i, -, hi⟩ := hy
        intro hxy
        subst hxy
        exact absurd hi
          (Finset.disjoint_left.mp (hdisj 0 (Fin.succ i) (Ne.symm (Fin.succ_ne_zero i))) hx)
      rw [hstep, packSel_union W hdisj' a,
        packSel_biUnion_ofFn W n (fun i : Fin n => B i.succ)
          (fun i j hij => hdisj (Fin.succ i) (Fin.succ j) (fun he => hij (Fin.succ_inj.mp he))) a,
        List.ofFn_succ]
      show packSel W (B 0) a
            ^^^ (List.ofFn fun i : Fin n => B i.succ).foldl
                  (fun acc A => acc ^^^ packSel W A a) 0
          = (List.ofFn fun i : Fin n => B i.succ).foldl
              (fun acc A => acc ^^^ packSel W A a) (0 ^^^ packSel W (B 0) a)
      rw [Nat.zero_xor, foldl_xor_const (fun A => packSel W A a) (packSel W (B 0) a)]
theorem packMem_H_single (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T)
    (r : (hintSpec T).Seed) (W : ℕ) (hW : 0 < W) (i : Fin (Node.N T)) (a : ℕ) :
    packMem W (hintH_trees CR P T hT r (Pi.single i 1)) a
      = packSel W (bitBlock CR T (hintKappa P T hT r) ({i.val} : Finset ℕ) 0) a := by
  rw [packMem_eq_packSel W hW]
  have hpred : ∀ p : Fin (synLen CR T),
      (hintH_trees CR P T hT r (Pi.single i 1) p = 1)
        ↔ (bitVal CR T (hintKappa P T hT r) p ({i.val} : Finset ℕ) = 1) := by
    intro p
    rw [hintH_trees_apply, support_single]
  have hset : (Finset.univ.filter (fun p : Fin (synLen CR T) =>
        hintH_trees CR P T hT r (Pi.single i 1) p = 1)).image Fin.val
      = (Finset.univ.filter (fun p : Fin (synLen CR T) =>
          bitVal CR T (hintKappa P T hT r) p ({i.val} : Finset ℕ) = 1)).image Fin.val := by
    ext v
    rw [Finset.mem_image, Finset.mem_image]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hpred p).mp (Finset.mem_filter.mp hp).2⟩, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        (hpred p).mpr (Finset.mem_filter.mp hp).2⟩, rfl⟩
  rw [hset]
  simp only [bitBlock, colSupp, Nat.zero_add]
theorem packMem_add_H_single (CR : CRFamily) (P : HintParams) (T : Node) (hT : IsSchemeTree P T)
    (r : (hintSpec T).Seed) (W : ℕ) (hW : 0 < W) (y : Fin (synLen CR T) → ZMod 2)
    (i : Fin (Node.N T)) (a : ℕ) :
    packMem W (y + hintH_trees CR P T hT r (Pi.single i 1)) a
      = packMem W y a
        ^^^ packSel W (bitBlock CR T (hintKappa P T hT r) ({i.val} : Finset ℕ) 0) a := by
  rw [packMem_add W hW, packMem_H_single CR P T hT r W hW i a]
theorem upvRt_of_setSt0 (E : RAMEnv) (it : UpIt) (hst : it.setSt = 0) :
    upvRt E it = 0 := by
  unfold upvRt
  rw [hst, Nat.zero_mul, Nat.zero_mod]
theorem upvCnf_of_setSt0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hst : it.setSt = 0) : upvCnf E i it ab = upvCn E i it ab := by
  unfold upvCnf
  rw [upvRt_of_setSt0 E it hst, Nat.mul_zero, Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos E.W))
theorem upvFnf_of_setSt0 (E : RAMEnv) (i : ℕ) (it : UpIt) (ab : UpAbs)
    (hst : it.setSt = 0) : upvFnf E i it ab = upvFn E i it ab := by
  unfold upvFnf
  rw [upvRt_of_setSt0 E it hst, Nat.mul_zero, Nat.zero_mod, Nat.add_zero]
  exact Nat.mod_eq_of_lt (Nat.mod_lt _ (Nat.two_pow_pos E.W))
theorem upFold_cf_of_setSt0 (E : RAMEnv) (i : ℕ) :
    ∀ (L : List UpIt) (ab : UpAbs), ab.c < 2 ^ E.W → ab.f < 2 ^ E.W →
      (∀ it ∈ L, it.setSt = 0 ∧ it.mode < 2) →
      (upFold E i ab L).c = ab.c ∧ (upFold E i ab L).f = ab.f := by
  intro L
  induction L with
  | nil => intro ab _ _ _; exact ⟨rfl, rfl⟩
  | cons it rest ih =>
      intro ab hc hf hset
      have hst : it.setSt = 0 := (hset it (List.mem_cons_self ..)).1
      have hset' : ∀ x ∈ rest, x.setSt = 0 ∧ x.mode < 2 :=
        fun x hx => hset x (List.mem_cons_of_mem _ hx)
      have hc' : (upApply E i it ab).c = ab.c := by
        show upvCnf E i it ab = ab.c
        rw [upvCnf_of_setSt0 E i it ab hst]
        exact upvCn_of_setSt0 E i it ab hst hc
      have hf' : (upApply E i it ab).f = ab.f := by
        show upvFnf E i it ab = ab.f
        rw [upvFnf_of_setSt0 E i it ab hst]
        exact upvFn_of_setSt0 E i it ab hst hf
      obtain ⟨h1, h2⟩ :=
        ih (upApply E i it ab) (by rw [hc']; exact hc) (by rw [hf']; exact hf) hset'
      refine ⟨?_, ?_⟩
      · show (upFold E i (upApply E i it ab) rest).c = ab.c
        rw [h1, hc']
      · show (upFold E i (upApply E i it ab) rest).f = ab.f
        rw [h2, hf']
theorem upOwnItems_setSt0 (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (k base toff : ℕ) :
    ∀ it ∈ upOwnItems CR Bc colBase T k base toff, it.setSt = 0 ∧ it.mode < 2 := by
  cases T with
  | store N =>
      intro it hit
      simp only [upOwnItems, List.mem_singleton] at hit
      subst hit
      exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
  | cr N t =>
      intro it hit
      simp only [upOwnItems, List.mem_map] at hit
      obtain ⟨j, -, rfl⟩ := hit
      exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
  | direct sch t =>
      intro it hit
      simp only [upOwnItems, List.mem_append, List.mem_map] at hit
      rcases hit with ⟨s, -, rfl⟩ | ⟨j, -, rfl⟩ <;> exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
  | recursive sch t Xs Ys child =>
      intro it hit
      simp only [upOwnItems, List.mem_map] at hit
      obtain ⟨j, -, rfl⟩ := hit
      exact ⟨rfl, by simp [upStoreIt, upCrIt, upColIt]⟩
theorem upFold_ownItems_cf (CR : CRFamily) (Bc colBase : ℕ) (E : RAMEnv) (i : ℕ)
    (T : Node) (k base toff : ℕ) (ab : UpAbs)
    (hc : ab.c < 2 ^ E.W) (hf : ab.f < 2 ^ E.W) :
    (upFold E i ab (upOwnItems CR Bc colBase T k base toff)).c = ab.c ∧
      (upFold E i ab (upOwnItems CR Bc colBase T k base toff)).f = ab.f :=
  upFold_cf_of_setSt0 E i _ ab hc hf (upOwnItems_setSt0 CR Bc colBase T k base toff)
set_option autoImplicit false
theorem upChildSave_pair_below {sav skipped : ℕ} (h : 2 * (skipped + 1) ≤ sav) :
    upChildSave sav skipped + 2 ≤ sav := by
  unfold upChildSave
  omega
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
def UpMemBound (E : RAMEnv) (a : UpAbs) : Prop := ∀ x, a.mem x < 2 ^ E.W
theorem upApply_mem_bound (E : RAMEnv) (i : ℕ) (it : UpIt) (a : UpAbs) (h : UpMemBound E a) :
    UpMemBound E (upApply E i it a) := by
  intro x
  change (Function.update (Function.update (Function.update a.mem (upvWi E i it a) (upvNew E i it a))
    it.sav (upvV0 E i it a)) (it.sav + 1) (upvV1 E i it a)) x < 2 ^ E.W
  rw [Function.update_apply]
  split
  · exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
  · rw [Function.update_apply]
    split
    · exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
    · rw [Function.update_apply]
      split
      · exact Nat.mod_lt _ (Nat.two_pow_pos E.W)
      · exact h x
theorem upFold_mem_bound (E : RAMEnv) (i : ℕ) (L : List UpIt) :
    ∀ a : UpAbs, UpMemBound E a → UpMemBound E (upFold E i a L) := by
  induction L with
  | nil => intro a h; exact h
  | cons it L ih => intro a h; exact ih _ (upApply_mem_bound E i it a h)
def upSiblingSchedule (sav : ℕ) : ℕ → List (List UpIt × (ℕ → ℕ)) → List UpIt
  | _, [] => []
  | start, item :: rest => upSiblingEntry sav start :: (item.1 ++ upSiblingSchedule sav (start + 1) rest)
def upChildMasks : List (List UpIt × (ℕ → ℕ)) → ℕ → ℕ
  | [], _ => 0
  | item :: rest, a => item.2 a ^^^ upChildMasks rest a
def UpChildEffect (E : RAMEnv) (i payload sav c f : ℕ) (item : List UpIt × (ℕ → ℕ)) : Prop :=
  ∀ mem : ℕ → ℕ, (∀ a, mem a < 2 ^ E.W) →
    (∀ a, a < payload → (upFold E i ⟨mem, c, f⟩ item.1).mem a = mem a ^^^ item.2 a) ∧
    (∀ a, sav ≤ a → (upFold E i ⟨mem, c, f⟩ item.1).mem a = mem a)
theorem upFold_restored_siblings (E : RAMEnv) (i payload sav c f : ℕ)
    (hW : 1 < 2 ^ E.W) :
    ∀ (L : List (List UpIt × (ℕ → ℕ))) (start : ℕ) (a : UpAbs),
      0 < start → UpMemBound E a → a.mem sav = c → a.mem (sav + 1) = f →
      (∀ item ∈ L, UpChildEffect E i payload sav c f item) →
      (∀ x, x < payload → (upFold E i a (upSiblingSchedule sav start L)).mem x =
        a.mem x ^^^ upChildMasks L x) ∧
      (∀ x, sav ≤ x → (upFold E i a (upSiblingSchedule sav start L)).mem x = a.mem x) := by
  intro L
  induction L with
  | nil =>
      intro start a hs hm hc hf hL
      constructor
      · intro x hx; simp only [upSiblingSchedule, upFold, upChildMasks, Nat.xor_zero]
      · intro x hx; rfl
  | cons item rest ih =>
      intro start a hs hm hc hf hL
      have hrestore : upApply E i (upSiblingEntry sav start) a = ⟨a.mem, c, f⟩ := by
        rw [upSiblingEntry, if_neg (by omega), upRestore_apply E i sav a hW hm, hc, hf]
      let z := upFold E i ⟨a.mem, c, f⟩ item.1
      have hchild := hL item (List.mem_cons_self ..) a.mem hm
      have hzm : UpMemBound E z := upFold_mem_bound E i item.1 _ hm
      have hzc : z.mem sav = c := (hchild.2 sav (by omega)).trans hc
      have hzf : z.mem (sav + 1) = f := (hchild.2 (sav + 1) (by omega)).trans hf
      have hrest := ih (start + 1) z (by omega) hzm hzc hzf
        (fun it hit => hL it (List.mem_cons_of_mem _ hit))
      have hsplit : upFold E i a (upSiblingSchedule sav start (item :: rest)) =
          upFold E i z (upSiblingSchedule sav (start + 1) rest) := by
        rw [upSiblingSchedule, upFold, hrestore, upFold_append]
      rw [hsplit]
      constructor
      · intro x hx
        rw [hrest.1 x hx, hchild.1 x hx]
        exact Nat.xor_assoc _ _ _
      · intro x hx
        exact (hrest.2 x hx).trans (hchild.2 x hx)
theorem upFold_saved_siblings (E : RAMEnv) (i payload sav c f : ℕ)
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W)
    (hPayload : payload ≤ sav) (L : List (List UpIt × (ℕ → ℕ)))
    (hL : ∀ item ∈ L, UpChildEffect E i payload sav c f item)
    (mem : ℕ → ℕ) (hm : ∀ x, mem x < 2 ^ E.W) :
    (∀ x, x < payload → (upFold E i ⟨mem, c, f⟩ (upSiblingSchedule sav 0 L)).mem x =
      mem x ^^^ upChildMasks L x) ∧
    (∀ x, sav + 2 ≤ x → (upFold E i ⟨mem, c, f⟩ (upSiblingSchedule sav 0 L)).mem x = mem x) := by
  cases L with
  | nil =>
      constructor
      · intro x hx; simp only [upSiblingSchedule, upFold, upChildMasks, Nat.xor_zero]
      · intro x hx; rfl
  | cons item rest =>
      let saved : ℕ → ℕ := Function.update (Function.update mem sav c) (sav + 1) f
      have hsave : upApply E i (upSiblingEntry sav 0) (⟨mem, c, f⟩ : UpAbs) = ⟨saved, c, f⟩ := by
        rw [upSiblingEntry, if_pos rfl, upSave_apply E i sav _ hW hc hf hm]
      have hsm : ∀ x, saved x < 2 ^ E.W := by
        have hh := upApply_mem_bound E i (upSiblingEntry sav 0) ⟨mem, c, f⟩ hm
        rw [hsave] at hh
        exact hh
      have hsc : saved sav = c := by simp [saved]
      have hsf : saved (sav + 1) = f := by simp [saved]
      have hslow (x : ℕ) (hx : x < payload) : saved x = mem x := by
        have h0 : x ≠ sav := by omega
        have h1 : x ≠ sav + 1 := by omega
        simp [saved, h0, h1]
      have hshigh (x : ℕ) (hx : sav + 2 ≤ x) : saved x = mem x := by
        have h0 : x ≠ sav := by omega
        have h1 : x ≠ sav + 1 := by omega
        simp [saved, h0, h1]
      let z := upFold E i ⟨saved, c, f⟩ item.1
      have hchild := hL item (List.mem_cons_self ..) saved hsm
      have hzm : UpMemBound E z := upFold_mem_bound E i item.1 _ hsm
      have hzc : z.mem sav = c := (hchild.2 sav (by omega)).trans hsc
      have hzf : z.mem (sav + 1) = f := (hchild.2 (sav + 1) (by omega)).trans hsf
      have hrest := upFold_restored_siblings E i payload sav c f hW rest 1 z (by omega) hzm hzc hzf
        (fun it hit => hL it (List.mem_cons_of_mem _ hit))
      have hsplit : upFold E i (⟨mem, c, f⟩ : UpAbs) (upSiblingSchedule sav 0 (item :: rest)) =
          upFold E i z (upSiblingSchedule sav 1 rest) := by
        rw [upSiblingSchedule, upFold, hsave, upFold_append]
      rw [hsplit]
      constructor
      · intro x hx
        rw [hrest.1 x hx, hchild.1 x hx, hslow x hx]
        exact Nat.xor_assoc _ _ _
      · intro x hx
        exact (hrest.2 x (by omega)).trans ((hchild.2 x (by omega)).trans (hshigh x hx))
theorem upSiblingSchedule_ofFn (sav : ℕ) :
    ∀ (n : ℕ) (blocks : Fin n → List UpIt × (ℕ → ℕ)) (start : ℕ),
      upSiblingSchedule sav start (List.ofFn blocks) =
        (List.ofFn fun s : Fin n => upSiblingEntry sav (start + s.val) :: (blocks s).1).flatten
  | 0, blocks, start => by simp [upSiblingSchedule]
  | n + 1, blocks, start => by
      simp only [List.ofFn_succ, upSiblingSchedule, List.flatten_cons, List.cons_append,
        Fin.val_zero, Nat.add_zero]
      rw [upSiblingSchedule_ofFn sav n (fun s => blocks s.succ) (start + 1)]
      apply congrArg (fun tail => upSiblingEntry sav start :: ((blocks 0).1 ++ tail))
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext s
      rw [show start + 1 + s.val = start + s.succ.val by simp only [Fin.val_succ]; omega]
theorem upChildMasks_foldl (L : List (List UpIt × (ℕ → ℕ))) (a : ℕ) :
    ∀ z : ℕ, L.foldl (fun acc item => acc ^^^ item.2 a) z = z ^^^ upChildMasks L a := by
  induction L with
  | nil => intro z; exact (Nat.xor_zero z).symm
  | cons item rest ih =>
      intro z
      simp only [List.foldl, upChildMasks]
      rw [ih]
      exact Nat.xor_assoc _ _ _
end LinearSetReconciliation327.Main
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem up_words_cover (W M : ℕ) (hW : 0 < W) : M ≤ wordsOf W M * W := by
  have hdiv := Nat.mod_add_div (M + W - 1) W
  have hmod := Nat.mod_lt (M + W - 1) hW
  rw [Nat.mul_comm W _] at hdiv
  unfold wordsOf
  omega
theorem up_packSel_above (W payload : ℕ) (S : Finset ℕ)
    (hS : ∀ b ∈ S, b < payload * W) (a : ℕ) (ha : payload ≤ a) : packSel W S a = 0 := by
  classical
  unfold packSel ofBits
  apply Finset.sum_eq_zero
  intro b hb
  have hn : a * W + b ∉ S := by
    intro hi
    have hbit := hS _ hi
    have hmul := Nat.mul_le_mul_right W ha
    omega
  simp [hn]
def UpSaveRoom (payload sav : ℕ) (T : Node) : Prop :=
  payload + 2 * (schemeNodes T).length ≤ sav
theorem upSaveRoom_child {payload sav : ℕ} {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (h : UpSaveRoom payload sav (.recursive sch t Xs Ys child)) (s : Fin sch.ℓ) :
    UpSaveRoom payload
      (upChildSave sav ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
      (child s) := by
  have hprefix := take_sum_add_getElem_le (List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length)
    s.val (schemeNodes (child s)).length (getElem?_ofFn' _ s)
  unfold UpSaveRoom at h ⊢
  rw [schemeNodes_recursive, List.length_append, List.length_singleton, flatten_length_eq_sum] at h
  unfold upChildSave
  omega
theorem upSaveRoom_child_pair_below {payload sav : ℕ} {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (h : UpSaveRoom payload sav (.recursive sch t Xs Ys child)) (s : Fin sch.ℓ) :
    upChildSave sav ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum + 2 ≤ sav := by
  have hprefix := take_sum_add_getElem_le (List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length)
    s.val (schemeNodes (child s)).length (getElem?_ofFn' _ s)
  apply upChildSave_pair_below
  unfold UpSaveRoom at h
  rw [schemeNodes_recursive, List.length_append, List.length_singleton, flatten_length_eq_sum] at h
  omega
end LinearSetReconciliation327.Main
set_option autoImplicit false
noncomputable section
open Finset
namespace LinearSetReconciliation327.Main
def upKidProgram (CR : CRFamily) (Bc colBase : ℕ) (sch : RowScheme) (child : Fin sch.ℓ → Node)
    (k base toff sav : ℕ) (s : Fin sch.ℓ) : List UpIt :=
  upSched CR Bc colBase (child s)
    (k + 1 + ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
    (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum)
    (toff + sch.N * (Bc + 1) + ((List.ofFn fun i : Fin sch.ℓ => upTabLen Bc (child i)).take s.val).sum)
    (upChildSave sav ((List.ofFn fun i : Fin sch.ℓ => (schemeNodes (child i)).length).take s.val).sum)
    [upClimb k sch.m sch.ℓ (schemeNmax sch) s]
theorem upKids_saved_layout (CR : CRFamily) (Bc colBase : ℕ) (sch : RowScheme) (t : ℕ)
    (Xs Ys : Fin sch.ℓ → ℕ) (child : Fin sch.ℓ → Node) (k base toff sav : ℕ)
    (mask : Fin sch.ℓ → ℕ → ℕ) :
    upKids CR Bc colBase (.recursive sch t Xs Ys child) k base toff sav [] =
      upSiblingSchedule sav 0 (List.ofFn fun s => (upKidProgram CR Bc colBase sch child k base toff sav s, mask s)) := by
  rw [upSiblingSchedule_ofFn]
  simp only [Nat.zero_add, upKids, upKidProgram]
def upRecOwnBits (CR : CRFamily) (sch : RowScheme) (t : ℕ) (child : Fin sch.ℓ → Node) (base c : ℕ) : Finset ℕ :=
  (Finset.univ.filter (fun q : Fin (CR.rows sch.N t) => q.val ∈ CR.sketch sch.N t {c})).image
    (fun q => base + ((∑ s : Fin sch.ℓ, synLen CR (child s)) + q.val))
def upRecKidBits (CR : CRFamily) {sch : RowScheme} {t : ℕ} {Xs Ys : Fin sch.ℓ → ℕ}
    {child : Fin sch.ℓ → Node} (r : Node.Seed (.recursive sch t Xs Ys child)) (base c : ℕ) (s : Fin sch.ℓ) : Finset ℕ :=
  bitBlock CR (child s) (r.2 s) (sch.column r.1 {c} s)
    (base + ((List.ofFn fun i : Fin sch.ℓ => synLen CR (child i)).take s.val).sum)
theorem upChildMasks_packSel_ofFn (W : ℕ) (a : ℕ) :
    ∀ (n : ℕ) (programs : Fin n → List UpIt) (B : Fin n → Finset ℕ),
      (∀ i j, i ≠ j → Disjoint (B i) (B j)) →
      upChildMasks (List.ofFn fun s => (programs s, packSel W (B s))) a = packSel W (Finset.univ.biUnion B) a := by
  intro n programs B hd
  rw [packSel_biUnion_ofFn W n B hd a]
  have hfold : ∀ (m : ℕ) (L : Fin m → List UpIt) (S : Fin m → Finset ℕ) (z : ℕ),
      (List.ofFn fun s => (L s, packSel W (S s))).foldl (fun acc item => acc ^^^ item.2 a) z =
        (List.ofFn S).foldl (fun acc A => acc ^^^ packSel W A a) z := by
    intro m
    induction m with
    | zero => intro L S z; rfl
    | succ m ih =>
        intro L S z
        simp only [List.ofFn_succ, List.foldl]
        exact ih (fun s => L s.succ) (fun s => S s.succ) _
  have hm := upChildMasks_foldl (List.ofFn fun s => (programs s, packSel W (B s))) a 0
  rw [Nat.zero_xor] at hm
  exact hm.symm.trans (hfold n programs B 0)
theorem upRecursiveMask_split (CR : CRFamily) (W : ℕ) {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (r : Node.Seed (.recursive sch t Xs Ys child)) (base c f : ℕ) (programs : Fin sch.ℓ → List UpIt) (a : ℕ) :
    packSel W (if f = 1 then bitBlock CR (.recursive sch t Xs Ys child) r {c} base else ∅) a =
      packSel W (if f = 1 then upRecOwnBits CR sch t child base c else ∅) a ^^^
        upChildMasks (List.ofFn fun s => (programs s, packSel W (if f = 1 then upRecKidBits CR r base c s else ∅))) a := by
  classical
  by_cases hf : f = 1
  · simp only [if_pos hf]
    rw [bitBlock_recursive, bitBlock_recursive_kids, Finset.union_comm]
    rw [packSel_union W (disjoint_bitBlock_own_kids r {c} base)]
    apply congrArg (fun z => packSel W (upRecOwnBits CR sch t child base c) a ^^^ z)
    exact (upChildMasks_packSel_ofFn W a sch.ℓ programs (upRecKidBits CR r base c)
      (fun i j hij => disjoint_bitBlock_kids r {c} base hij)).symm
  · simp only [if_neg hf, packSel_empty, Nat.zero_xor]
    have h := upChildMasks_packSel_ofFn W a sch.ℓ programs (fun _ => ∅) (by intro i j hij; simp)
    have he : (Finset.univ : Finset (Fin sch.ℓ)).biUnion (fun _ => (∅ : Finset ℕ)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨s, hs, hx0⟩ := Finset.mem_biUnion.mp hx
      simpa using hx0
    rw [he, packSel_empty] at h
    exact h.symm
theorem upAbs_eta_coords (z : UpAbs) (c f : ℕ) (hc : z.c = c) (hf : z.f = f) : z = ⟨z.mem, c, f⟩ := by
  cases z with
  | mk mem c0 f0 =>
    dsimp only at hc hf
    subst c0
    subst f0
    rfl
theorem upFold_node_recursive_of_children (CR : CRFamily) (E : RAMEnv)
    (i Bc colBase k base toff payload sav c f : ℕ) {sch : RowScheme} {t : ℕ}
    {Xs Ys : Fin sch.ℓ → ℕ} {child : Fin sch.ℓ → Node}
    (r : Node.Seed (.recursive sch t Xs Ys child))
    (hW : 1 < 2 ^ E.W) (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W) (hPayload : payload ≤ sav)
    (hOwnBits : ∀ b ∈ (if f = 1 then upRecOwnBits CR sch t child base c else ∅), b < payload * E.W)
    (hChild : ∀ s : Fin sch.ℓ, UpChildEffect E i payload sav c f
      (upKidProgram CR Bc colBase sch child k base toff sav s,
        packSel E.W (if f = 1 then upRecKidBits CR r base c s else ∅)))
    (mem : ℕ → ℕ) (hm : ∀ a, mem a < 2 ^ E.W) (ownState : UpAbs)
    (hRunOwn : upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff) = ownState)
    (hOwnC : ownState.c = c) (hOwnF : ownState.f = f)
    (hOwnMem : ∀ a, ownState.mem a = mem a ^^^ packSel E.W
      (if f = 1 then upRecOwnBits CR sch t child base c else ∅) a) :
    (∀ a, a < payload →
      (upFold E i ⟨mem, c, f⟩
        (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff ++
          upKids CR Bc colBase (.recursive sch t Xs Ys child) k base toff sav [])).mem a =
        mem a ^^^ packSel E.W (if f = 1 then bitBlock CR (.recursive sch t Xs Ys child) r {c} base else ∅) a) ∧
    (∀ a, sav + 2 ≤ a →
      (upFold E i ⟨mem, c, f⟩
        (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff ++
          upKids CR Bc colBase (.recursive sch t Xs Ys child) k base toff sav [])).mem a = mem a) := by
  let programs := upKidProgram CR Bc colBase sch child k base toff sav
  let masks := fun s : Fin sch.ℓ => packSel E.W (if f = 1 then upRecKidBits CR r base c s else ∅)
  let tagged := List.ofFn fun s => (programs s, masks s)
  have hbound : ∀ a, ownState.mem a < 2 ^ E.W := by
    have hh := upFold_mem_bound E i (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff) (⟨mem, c, f⟩ : UpAbs) hm
    rw [hRunOwn] at hh
    exact hh
  have hentry := upAbs_eta_coords ownState c f hOwnC hOwnF
  have hk := upFold_saved_siblings E i payload sav c f hW hc hf hPayload tagged
    (by intro item hit; obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hit; exact hChild s) ownState.mem hbound
  have hsplit : upFold E i ⟨mem, c, f⟩
      (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff ++
        upKids CR Bc colBase (.recursive sch t Xs Ys child) k base toff sav []) =
      upFold E i ⟨ownState.mem, c, f⟩ (upSiblingSchedule sav 0 tagged) := by
    rw [upFold_append, hRunOwn, hentry, upKids_saved_layout CR Bc colBase sch t Xs Ys child k base toff sav masks]
  rw [hsplit]
  constructor
  · intro a ha
    rw [hk.1 a ha, hOwnMem a, Nat.xor_assoc]
    exact congrArg (fun z => mem a ^^^ z) (upRecursiveMask_split CR E.W r base c f programs a).symm
  · intro a ha
    rw [hk.2 a ha, hOwnMem a, up_packSel_above E.W payload _ hOwnBits a (by omega), Nat.xor_zero]
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upvCoin_mem_irrel (E : RAMEnv) (i : ℕ) (it : UpIt) (c f : ℕ) (mem mem' : ℕ → ℕ) :
    upvCoin E i it (⟨mem, c, f⟩ : UpAbs) = upvCoin E i it (⟨mem', c, f⟩ : UpAbs) := rfl
theorem upKids_path_irrel (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (k base toff sav : ℕ)
    (path path' : List UpIt) :
    upKids CR Bc colBase T k base toff sav path = upKids CR Bc colBase T k base toff sav path' := by
  cases T <;> rfl
theorem up_gate_child_set (W f coin g d : ℕ) (G : Finset ℕ → Finset ℕ) (J : Finset ℕ)
    (hW : 1 < 2 ^ W) (hf : f = 0 ∨ f = 1) (hcoin : coin = 0 ∨ coin = 1)
    (hg : g = f * coin % 2 ^ W) (hJ : J = if coin = 1 then {d} else ∅) (hEmpty : G ∅ = ∅) :
    (if g = 1 then G {d} else ∅) = (if f = 1 then G J else ∅) := by
  rw [hg, hJ]
  rcases hf with rfl | rfl <;> rcases hcoin with rfl | rfl <;>
    simp [hEmpty, Nat.mod_eq_of_lt hW]
theorem upClimb_child_effect (CR : CRFamily) (E : RAMEnv)
    (i Bc colBase k m ell nmax s childK base toff childSav payload sav c f d coin g : ℕ)
    (T : Node) (r : Node.Seed T) (J : Finset ℕ)
    (hW : 1 < 2 ^ E.W) (hm : 0 < m) (hmM : m ≤ 2 ^ E.W)
    (hc : c < 2 ^ E.W) (hf : f < 2 ^ E.W) (hf01 : f = 0 ∨ f = 1)
    (hperm : E.perm k c < 2 ^ E.W) (hbit : E.perm k c % m * ell + s < 2 ^ E.W)
    (hk : childK ≠ 0) (hSlots : childSav + 2 ≤ sav)
    (hd : d = E.perm k c % m)
    (hCoin : upvCoin E i (upClimb k m ell nmax s) (⟨fun _ => 0, c, f⟩ : UpAbs) = coin)
    (hCoin01 : coin = 0 ∨ coin = 1) (hg : g = f * coin % 2 ^ E.W)
    (hJ : J = if coin = 1 then {d} else ∅) (hEmpty : bitBlock CR T r ∅ base = ∅)
    (hNode : ∀ mem : ℕ → ℕ, (∀ a, mem a < 2 ^ E.W) →
      (∀ a, a < payload →
        (upFold E i ⟨mem, d, g⟩ (upOwnItems CR Bc colBase T childK base toff ++
          upKids CR Bc colBase T childK base toff childSav [])).mem a =
        mem a ^^^ packSel E.W (if g = 1 then bitBlock CR T r {d} base else ∅) a) ∧
      (∀ a, childSav + 2 ≤ a →
        (upFold E i ⟨mem, d, g⟩ (upOwnItems CR Bc colBase T childK base toff ++
          upKids CR Bc colBase T childK base toff childSav [])).mem a = mem a)) :
    UpChildEffect E i payload sav c f
      (upSched CR Bc colBase T childK base toff childSav [upClimb k m ell nmax s],
        packSel E.W (if f = 1 then bitBlock CR T r J base else ∅)) := by
  have hGate := up_gate_child_set E.W f coin g d (fun S => bitBlock CR T r S base) J
    hW hf01 hCoin01 hg hJ hEmpty
  intro mem hmem
  have hCoinMem : upvCoin E i (upClimb k m ell nmax s) (⟨mem, c, f⟩ : UpAbs) = coin :=
    (upvCoin_mem_irrel E i (upClimb k m ell nmax s) c f mem (fun _ => 0)).trans hCoin
  have hClimb : upFold E i (⟨mem, c, f⟩ : UpAbs) [upClimb k m ell nmax s] = ⟨mem, d, g⟩ := by
    have hh := upFold_climb_single E i k m ell nmax s (⟨mem, c, f⟩ : UpAbs)
      hW hm hmM hc hf hmem hperm hbit
    rw [hCoinMem, ← hd, ← hg] at hh
    exact hh
  have hRun : upFold E i (⟨mem, c, f⟩ : UpAbs)
      (upSched CR Bc colBase T childK base toff childSav [upClimb k m ell nmax s]) =
      upFold E i (⟨mem, d, g⟩ : UpAbs)
        (upOwnItems CR Bc colBase T childK base toff ++ upKids CR Bc colBase T childK base toff childSav []) := by
    rw [upSched_nonroot CR Bc colBase T childK base toff childSav _ hk,
      upKids_path_irrel CR Bc colBase T childK base toff childSav _ [], List.append_assoc,
      upFold_append, hClimb]
  have hn := hNode mem hmem
  constructor
  · intro a ha
    rw [hRun, hn.1 a ha, hGate]
  · intro a ha
    rw [hRun]
    exact hn.2 a (by omega)
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
open Finset
namespace LinearSetReconciliation327.Main
def upNodeLocalBits (CR : CRFamily) : (T : Node) → T.Seed → ℕ → ℕ → Finset ℕ
  | .recursive sch t Xs Ys child, _, base, c => upRecOwnBits CR sch t child base c
  | T, r, base, c => bitBlock CR T r {c} base
def UpLocalBitsCorrect (CR : CRFamily) (E : RAMEnv) (i Bc colBase : ℕ)
    (T : Node) (r : T.Seed) (k base toff : ℕ) : Prop :=
  ∀ c f, c < T.N → c < 2 ^ E.W → f < 2 ^ E.W → (f = 0 ∨ f = 1) →
    ∀ mem : ℕ → ℕ, (∀ a, mem a < 2 ^ E.W) → ∀ a,
      (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff)).mem a =
        mem a ^^^ packSel E.W (if f = 1 then upNodeLocalBits CR T r base c else ∅) a
structure UpEdgeData (E : RAMEnv) (i k : ℕ) (sch : RowScheme)
    (lr : sch.LocalSeed) (s : Fin sch.ℓ) (c f : ℕ) : Prop where
  mpos : 0 < sch.m
  mword : sch.m ≤ 2 ^ E.W
  perm : E.perm k c < 2 ^ E.W
  bit : E.perm k c % sch.m * sch.ℓ + s.val < 2 ^ E.W
  coin : let b := upvCoin E i (upClimb k sch.m sch.ℓ (schemeNmax sch) s) ⟨fun _ => 0, c, f⟩
    b = 0 ∨ b = 1
  column : sch.column lr {c} s =
    if upvCoin E i (upClimb k sch.m sch.ℓ (schemeNmax sch) s) ⟨fun _ => 0, c, f⟩ = 1
    then {E.perm k c % sch.m} else ∅
def UpLocalTree (CR : CRFamily) (E : RAMEnv) (i Bc colBase : ℕ) :
    (T : Node) → T.Seed → ℕ → ℕ → ℕ → Prop
  | .recursive sch t Xs Ys child, r, k, base, toff =>
      UpLocalBitsCorrect CR E i Bc colBase (.recursive sch t Xs Ys child) r k base toff ∧
      (∀ s, (child s).N = sch.m) ∧
      (∀ c f, c < sch.N → c < 2 ^ E.W → f < 2 ^ E.W → (f = 0 ∨ f = 1) →
        ∀ s, UpEdgeData E i k sch r.1 s c f) ∧
      ∀ s : Fin sch.ℓ, UpLocalTree CR E i Bc colBase (child s) (r.2 s)
        (k + 1 + ((List.ofFn fun j : Fin sch.ℓ => (schemeNodes (child j)).length).take s.val).sum)
        (base + ((List.ofFn fun j : Fin sch.ℓ => synLen CR (child j)).take s.val).sum)
        (toff + sch.N * (Bc + 1) + ((List.ofFn fun j : Fin sch.ℓ => upTabLen Bc (child j)).take s.val).sum)
  | T, r, k, base, toff => UpLocalBitsCorrect CR E i Bc colBase T r k base toff
theorem up_bitBlock_fits (CR : CRFamily) (W payload : ℕ) (T : Node) (r : T.Seed)
    (base : ℕ) (x : Finset ℕ) (hfit : base + synLen CR T ≤ payload * W) :
    ∀ b ∈ bitBlock CR T r x base, b < payload * W := by
  intro b hb
  obtain ⟨p, hp, rfl⟩ := mem_bitBlock.mp hb
  have hh := p.isLt
  omega
theorem up_xor_effect_frame (W payload sav : ℕ) (S : Finset ℕ) (mem out : ℕ → ℕ)
    (hEffect : ∀ a, out a = mem a ^^^ packSel W S a)
    (hBits : ∀ b ∈ S, b < payload * W) (hRoom : payload ≤ sav) :
    (∀ a, a < payload → out a = mem a ^^^ packSel W S a) ∧
      (∀ a, sav + 2 ≤ a → out a = mem a) := by
  constructor
  · intro a ha; exact hEffect a
  · intro a ha
    rw [hEffect a, up_packSel_above W payload S hBits a (by omega), Nat.xor_zero]
theorem upFold_tree_of_local (CR : CRFamily) (E : RAMEnv) (i Bc colBase payload : ℕ)
    (hW : 1 < 2 ^ E.W) :
    ∀ (T : Node) (r : T.Seed) (k base toff sav : ℕ),
      UpLocalTree CR E i Bc colBase T r k base toff →
      base + synLen CR T ≤ payload * E.W → UpSaveRoom payload sav T →
      ∀ c f, c < T.N → c < 2 ^ E.W → f < 2 ^ E.W → (f = 0 ∨ f = 1) →
      ∀ mem : ℕ → ℕ, (∀ a, mem a < 2 ^ E.W) →
      (∀ a, a < payload →
        (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff ++
          upKids CR Bc colBase T k base toff sav [])).mem a =
            mem a ^^^ packSel E.W (if f = 1 then bitBlock CR T r {c} base else ∅) a) ∧
      (∀ a, sav + 2 ≤ a →
        (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase T k base toff ++
          upKids CR Bc colBase T k base toff sav [])).mem a = mem a) := by
  intro T
  induction T with
  | store N =>
      intro r k base toff sav hLocal hFit hRoom c f hcN hc hf hf01 mem hm
      have hh := hLocal c f hcN hc hf hf01 mem hm
      change ∀ a, (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase (.store N) k base toff)).mem a =
        mem a ^^^ packSel E.W (if f = 1 then bitBlock CR (.store N) r {c} base else ∅) a at hh
      simp only [upKids, List.append_nil]
      apply up_xor_effect_frame E.W payload sav _ mem _ hh
      · intro b hb; split_ifs at hb with hflag
        · exact up_bitBlock_fits CR E.W payload _ r base {c} hFit b hb
        · simpa using hb
      · exact le_trans (Nat.le_add_right _ _) hRoom
  | cr N t =>
      intro r k base toff sav hLocal hFit hRoom c f hcN hc hf hf01 mem hm
      have hh := hLocal c f hcN hc hf hf01 mem hm
      change ∀ a, (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase (.cr N t) k base toff)).mem a =
        mem a ^^^ packSel E.W (if f = 1 then bitBlock CR (.cr N t) r {c} base else ∅) a at hh
      simp only [upKids, List.append_nil]
      apply up_xor_effect_frame E.W payload sav _ mem _ hh
      · intro b hb; split_ifs at hb with hflag
        · exact up_bitBlock_fits CR E.W payload _ r base {c} hFit b hb
        · simpa using hb
      · exact le_trans (Nat.le_add_right _ _) hRoom
  | direct sch t =>
      intro r k base toff sav hLocal hFit hRoom c f hcN hc hf hf01 mem hm
      have hh := hLocal c f hcN hc hf hf01 mem hm
      change ∀ a, (upFold E i ⟨mem, c, f⟩ (upOwnItems CR Bc colBase (.direct sch t) k base toff)).mem a =
        mem a ^^^ packSel E.W (if f = 1 then bitBlock CR (.direct sch t) r {c} base else ∅) a at hh
      simp only [upKids, List.append_nil]
      apply up_xor_effect_frame E.W payload sav _ mem _ hh
      · intro b hb; split_ifs at hb with hflag
        · exact up_bitBlock_fits CR E.W payload _ r base {c} hFit b hb
        · simpa using hb
      · exact le_trans (Nat.le_add_right _ _) hRoom
  | recursive sch t Xs Ys child ih =>
      intro r k base toff sav hLocal hFit hRoom c f hcN hc hf hf01 mem hm
      obtain ⟨hOwn, hChildN, hEdge, hChild⟩ := hLocal
      have hPayload : payload ≤ sav := le_trans (Nat.le_add_right _ _) hRoom
      have hOwnMem := hOwn c f hcN hc hf hf01 mem hm
      let q := upFold E i (⟨mem, c, f⟩ : UpAbs)
        (upOwnItems CR Bc colBase (.recursive sch t Xs Ys child) k base toff)
      have hcf := upFold_ownItems_cf CR Bc colBase E i (.recursive sch t Xs Ys child) k base toff
        (⟨mem, c, f⟩ : UpAbs) hc hf
      apply upFold_node_recursive_of_children CR E i Bc colBase k base toff payload sav c f r
        hW hc hf hPayload _ _ mem hm q rfl hcf.1 hcf.2 hOwnMem
      · intro b hb
        split_ifs at hb with hflag
        · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
          have hqa := a.isLt
          change base + ((∑ s : Fin sch.ℓ, synLen CR (child s)) + a.val) < payload * E.W
          simp only [synLen] at hFit
          omega
        · simpa using hb
      · intro s
        have he := hEdge c f hcN hc hf hf01 s
        let d := E.perm k c % sch.m
        let coin := upvCoin E i (upClimb k sch.m sch.ℓ (schemeNmax sch) s) (⟨fun _ => 0, c, f⟩ : UpAbs)
        let g := f * coin % 2 ^ E.W
        have hcoin : coin = 0 ∨ coin = 1 := he.coin
        have hg01 : g = 0 ∨ g = 1 := by
          dsimp only [g]
          rcases hf01 with hf' | hf' <;> rcases hcoin with hb' | hb' <;>
            simp only [hf', hb', Nat.zero_mul, Nat.one_mul, Nat.mul_zero,
              Nat.mul_one, Nat.zero_mod, Nat.mod_eq_of_lt hW, or_true, true_or]
        have hdN : d < (child s).N := by rw [hChildN s]; exact Nat.mod_lt _ he.mpos
        have hd : d < 2 ^ E.W := lt_of_lt_of_le (Nat.mod_lt _ he.mpos) he.mword
        have hg : g < 2 ^ E.W := Nat.mod_lt _ (by positivity)
        have hSum := take_sum_add_getElem_le
          (List.ofFn fun j : Fin sch.ℓ => synLen CR (child j)) s.val (synLen CR (child s))
          (getElem?_ofFn' _ s)
        rw [List.sum_ofFn] at hSum
        have hFitChild : base + ((List.ofFn fun j : Fin sch.ℓ => synLen CR (child j)).take s.val).sum +
            synLen CR (child s) ≤ payload * E.W := by
          simp only [synLen] at hFit
          omega
        unfold upKidProgram upRecKidBits
        apply upClimb_child_effect CR E i Bc colBase k sch.m sch.ℓ (schemeNmax sch) s
          (k + 1 + ((List.ofFn fun j : Fin sch.ℓ => (schemeNodes (child j)).length).take s.val).sum)
          _ _ _ payload sav c f d coin g (child s) (r.2 s) (sch.column r.1 {c} s)
          hW he.mpos he.mword hc hf hf01 he.perm he.bit (by omega)
          (upSaveRoom_child_pair_below hRoom s) rfl rfl hcoin rfl
          he.column (bitBlock_empty CR (child s) (r.2 s) _) _
        intro mem' hm'
        exact ih s (r.2 s) _ _ _ _ (hChild s) hFitChild
          (upSaveRoom_child hRoom s) d g hdN hd hg hg01 mem' hm'
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
namespace LinearSetReconciliation327.Main
theorem upOwnItems_sav_le (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (k base toff : ℕ) :
    ∀ it ∈ upOwnItems CR Bc colBase T k base toff, it.sav ≤ Bc := by
  cases T with
  | store N =>
      intro it hi
      simp only [upOwnItems, List.mem_singleton] at hi
      subst it
      exact Nat.zero_le _
  | cr N t =>
      intro it hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact Nat.le_of_lt (List.mem_range.mp hj)
  | direct sch t =>
      intro it hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
        exact Nat.zero_le _
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact Nat.le_of_lt (List.mem_range.mp hj)
  | recursive sch t Xs Ys child =>
      intro it hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact Nat.le_of_lt (List.mem_range.mp hj)
theorem upSched_sav_le_of_kids (CR : CRFamily) (Bc colBase : ℕ) (T : Node)
    (k base toff sav : ℕ) (path : List UpIt)
    (hp : ∀ it ∈ path, it.sav ≤ max sav Bc)
    (hk : ∀ it ∈ upKids CR Bc colBase T k base toff sav path, it.sav ≤ max sav Bc) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav path, it.sav ≤ max sav Bc := by
  intro it hi
  rw [upSched_decomp] at hi
  rcases List.mem_append.mp hi with hh | ht
  · unfold upHead at hh
    split_ifs at hh with hzero
    · rw [List.mem_singleton] at hh
      subst it
      exact Nat.zero_le _
    · simp at hh
  · rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with hp' | ho
      · exact hp it hp'
      · exact (upOwnItems_sav_le CR Bc colBase T k base toff it ho).trans (le_max_right _ _)
    · exact hk it ht
theorem upSched_sav_le (CR : CRFamily) (Bc colBase : ℕ) (T : Node)
    (k base toff sav : ℕ) (path : List UpIt)
    (hp : ∀ it ∈ path, it.sav ≤ max sav Bc) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav path, it.sav ≤ max sav Bc := by
  induction T generalizing k base toff sav path with
  | store N =>
      apply upSched_sav_le_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      simp [upKids] at hi
  | cr N t =>
      apply upSched_sav_le_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      simp [upKids] at hi
  | direct sch t =>
      apply upSched_sav_le_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      simp [upKids] at hi
  | recursive sch t Xs Ys child ih =>
      apply upSched_sav_le_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      unfold upKids at hi
      obtain ⟨L, hL, hit⟩ := List.mem_flatten.mp hi
      obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hL
      rcases List.mem_cons.mp hit with he | hrest
      · subst it
        unfold upSiblingEntry
        split_ifs <;> exact le_max_left _ _
      · have hh := ih s
          (k + 1 + ((List.ofFn fun j : Fin sch.ℓ => (schemeNodes (child j)).length).take s.val).sum)
          (base + ((List.ofFn fun j : Fin sch.ℓ => synLen CR (child j)).take s.val).sum)
          (toff + sch.N * (Bc + 1) + ((List.ofFn fun j : Fin sch.ℓ => upTabLen Bc (child j)).take s.val).sum)
          (upChildSave sav ((List.ofFn fun j : Fin sch.ℓ => (schemeNodes (child j)).length).take s.val).sum)
          [upClimb k sch.m sch.ℓ (schemeNmax sch) s]
          (by intro u hu; rw [List.mem_singleton] at hu; subst u; exact Nat.zero_le _) it hrest
        exact hh.trans (max_le_max (Nat.sub_le _ _) le_rfl)
theorem upSched_sav_word (CR : CRFamily) (Bc colBase : ℕ) (T : Node)
    (k base toff sav W : ℕ) (hSav : sav + 1 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav [], it.sav + 1 < 2 ^ W := by
  intro it hi
  have hh := upSched_sav_le CR Bc colBase T k base toff sav [] (by simp) it hi
  omega
end LinearSetReconciliation327.Main
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upFold_root_of_local (CR : CRFamily) (E : RAMEnv) (Bc colBase payload sav : ℕ)
    (T : Node) (r : T.Seed) (i : ℕ) (hW : 1 < 2 ^ E.W) (hN : 0 < T.N) (hNM : T.N ≤ 2 ^ E.W)
    (hLocal : UpLocalTree CR E i Bc colBase T r 0 0 0)
    (hFit : synLen CR T ≤ payload * E.W) (hRoom : UpSaveRoom payload sav T)
    (hi : i < T.N) (mem : ℕ → ℕ) (hm : ∀ a, mem a < 2 ^ E.W) :
    ∀ a, a < payload →
      (upFold E i (⟨mem, 0, 1⟩ : UpAbs) (upSched CR Bc colBase T 0 0 0 sav [])).mem a =
        mem a ^^^ packSel E.W (bitBlock CR T r {i} 0) a := by
  have hiW : i < 2 ^ E.W := lt_of_lt_of_le hi hNM
  have hreset := upReset_apply_mod E i T.N (⟨mem, 0, 1⟩ : UpAbs)
    hW hN hNM hiW (by change 0 < 2 ^ E.W; omega) hW hm
  rw [Nat.mod_eq_of_lt hi] at hreset
  have hh := upFold_tree_of_local CR E i Bc colBase payload hW T r 0 0 0 sav
    hLocal (by simpa only [Nat.zero_add] using hFit) hRoom i 1 hi hiW hW (Or.inr rfl) mem hm
  intro a ha
  rw [upSched_root, upFold, hreset]
  simpa only [if_pos rfl, if_pos trivial] using hh.1 a ha
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
open scoped ENNReal
open Finset
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
universe u
set_option autoImplicit false
end LinearSetReconciliation327.Main
end
set_option autoImplicit false
noncomputable section
namespace LinearSetReconciliation327.Main
theorem upOwnItems_kind (CR : CRFamily) (Bc colBase : ℕ) (T : Node) (k base toff : ℕ) :
    ∀ it ∈ upOwnItems CR Bc colBase T k base toff, UpItemKind it := by
  cases T with
  | store N =>
      intro it hi
      rw [upOwnItems, List.mem_singleton] at hi
      subst it
      exact Or.inl (by norm_num [upStoreIt])
  | cr N t =>
      intro it hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact Or.inl (by norm_num [upCrIt])
  | direct sch t =>
      intro it hi
      rcases List.mem_append.mp hi with hi | hi
      · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
        exact Or.inl (by norm_num [upColIt])
      · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
        exact Or.inl (by norm_num [upCrIt])
  | recursive sch t Xs Ys child =>
      intro it hi
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
      exact Or.inl (by norm_num [upCrIt])
theorem upSiblingEntry_kind (sav s : ℕ) : UpItemKind (upSiblingEntry sav s) := by
  unfold upSiblingEntry
  split_ifs
  · exact Or.inr ⟨sav, Or.inl rfl⟩
  · exact Or.inr ⟨sav, Or.inr rfl⟩
theorem upSched_kind_of_kids (CR : CRFamily) (Bc colBase : ℕ) (T : Node)
    (k base toff sav : ℕ) (path : List UpIt)
    (hp : ∀ it ∈ path, UpItemKind it)
    (hk : ∀ it ∈ upKids CR Bc colBase T k base toff sav path, UpItemKind it) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav path, UpItemKind it := by
  intro it hi
  rw [upSched_decomp] at hi
  rcases List.mem_append.mp hi with hh | ht
  · unfold upHead at hh
    split_ifs at hh
    · rw [List.mem_singleton] at hh
      subst it
      exact Or.inl (by norm_num [upReset])
    · simp at hh
  · rcases List.mem_append.mp ht with ht | ht
    · rcases List.mem_append.mp ht with hpath | hown
      · exact hp it hpath
      · exact upOwnItems_kind CR Bc colBase T k base toff it hown
    · exact hk it ht
theorem upSched_kind (CR : CRFamily) (Bc colBase : ℕ) (T : Node)
    (k base toff sav : ℕ) (path : List UpIt) (hp : ∀ it ∈ path, UpItemKind it) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav path, UpItemKind it := by
  induction T generalizing k base toff sav path with
  | store N =>
      apply upSched_kind_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      simp [upKids] at hi
  | cr N t =>
      apply upSched_kind_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      simp [upKids] at hi
  | direct sch t =>
      apply upSched_kind_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      simp [upKids] at hi
  | recursive sch t Xs Ys child ih =>
      apply upSched_kind_of_kids CR Bc colBase _ k base toff sav path hp
      intro it hi
      unfold upKids at hi
      obtain ⟨L, hL, hit⟩ := List.mem_flatten.mp hi
      obtain ⟨s, rfl⟩ := List.mem_ofFn.mp hL
      rcases List.mem_cons.mp hit with he | hrest
      · subst it
        exact upSiblingEntry_kind sav s.val
      · exact ih s _ _ _ _ _
          (by intro u hu; rw [List.mem_singleton] at hu; subst u; exact Or.inl (by norm_num [upClimb])) it hrest
theorem upSched_valid_records (CR : CRFamily) (Bc colBase : ℕ) (T : Node)
    (k base toff sav W : ℕ) (hSav : sav + 1 < 2 ^ W) (hBc : Bc + 1 < 2 ^ W) :
    ∀ it ∈ upSched CR Bc colBase T k base toff sav [],
      UpItemKind it ∧ it.sav + 1 < 2 ^ W := by
  intro it hi
  exact ⟨upSched_kind CR Bc colBase T k base toff sav [] (by simp) it hi,
    upSched_sav_word CR Bc colBase T k base toff sav W hSav hBc it hi⟩
end LinearSetReconciliation327.Main
end

#print axioms LinearSetReconciliation327.Main.upFold_root_of_local


