-- Prove2me | Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffRestriction
-- name    : PretorsionImageClosed_LinearQuiver_CutoffRestriction
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-25T06:36:01.110887+00:00
-- url     : https://prove2.me/theorems/72f0d85a-0370-597c-b98f-e6653c4bb53c
-- title:
--   Cutoff Restriction
-- statement:
--   Definitions and structural lemmas for Cutoff Restriction, from Haruhisa Enomoto (haruhisa-enomoto/pretorsion-image-closed; see pinned Apache-2.0 LICENSE)'s pinned Pretorsion theories and image-closed subcategories of finite-dimensional algebras development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/haruhisa-enomoto/pretorsion-image-closed/blob/e803b5d1325bc1ce2b779efbff157b6cd3234bc8/PretorsionImageClosed/LinearQuiver/CutoffRestriction.lean

module
public import Definitions.Def_PretorsionImageClosed_LinearQuiver_CutoffWeights
public import Definitions.Def_PretorsionImageClosed_Gandhi_ColumnSum
public import Theorems.Thm_PretorsionImageClosed_Statement_PretorsionTheory_ext

set_option autoImplicit true
@[expose] public section
@[expose] public section
set_option autoImplicit false
noncomputable section
namespace PretorsionImageClosed
open Statement Polynomial Finset
namespace LinearQuiver
variable {n : ℕ}
noncomputable instance : DecidableEq (CutoffPair n) := Classical.decEq _
def RowCutoff.restrict (β : RowCutoff (n + 1)) : RowCutoff n where
  β a := min (β.β a.castSucc) n
  le_β a := le_min (by simpa using β.le_β a.castSucc) a.isLt.le
  β_le _ := min_le_right _ _
def ColCutoff.restrict (α : ColCutoff (n + 1)) : ColCutoff n where
  α d := α.α d.castSucc
  α_le d := by simpa using α.α_le d.castSucc
theorem criterion_restrict {β : RowCutoff (n + 1)} {α : ColCutoff (n + 1)} (h : Criterion β α) :
    Criterion β.restrict α.restrict := by
  intro d
  rcases h d.castSucc with h0 | ⟨e, he, hde, hprev⟩
  · exact Or.inl h0
  · right
    have hα := α.α_le d.castSucc
    simp only [Fin.val_castSucc] at hα hde
    have hed : e.val < n := by omega
    refine ⟨⟨e.val, hed⟩, he, ?_, ?_⟩
    · show d.val < min (β.β (Fin.castSucc ⟨e.val, hed⟩)) n
      have hcast : Fin.castSucc (⟨e.val, hed⟩ : Fin n) = e := Fin.ext rfl
      rw [hcast]
      exact lt_min hde d.isLt
    · intro a ha hβ
      have hβ' : min (β.β a.castSucc) n = d.val := hβ
      have hlt : a.castSucc < e := by
        rw [Fin.lt_def] at ha ⊢
        simpa using ha
      have := hprev a.castSucc hlt
      simp only [Fin.val_castSucc] at this
      have hd := d.isLt
      omega
def CutoffPair.restrict (x : CutoffPair (n + 1)) : CutoffPair n :=
  ⟨(x.1.1.restrict, x.1.2.restrict), criterion_restrict x.2⟩
def βext (p : CutoffPair n) : Fin (n + 1) → ℕ := Fin.snoc (α := fun _ => ℕ) p.1.1.β n
@[simp] theorem βext_castSucc (p : CutoffPair n) (a : Fin n) : βext p a.castSucc = p.1.1.β a :=
  Fin.snoc_castSucc _ _ _
@[simp] theorem βext_last (p : CutoffPair n) : βext p (Fin.last n) = n := Fin.snoc_last _ _
theorem βext_le (p : CutoffPair n) (a : Fin (n + 1)) : βext p a ≤ n := by
  induction a using Fin.lastCases with
  | last => simp
  | cast a => simp [p.1.1.β_le a]
theorem le_βext (p : CutoffPair n) (a : Fin (n + 1)) : a.val ≤ βext p a := by
  induction a using Fin.lastCases with
  | last => simp
  | cast a => simpa using p.1.1.le_β a
def candRows (p : CutoffPair n) : Finset (Fin (n + 1)) := univ.filter (fun a => βext p a = n)
theorem mem_candRows {p : CutoffPair n} {a : Fin (n + 1)} : a ∈ candRows p ↔ βext p a = n := by
  simp [candRows]
def Allowed (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) : Option (Fin (n + 1)) → Prop
  | none => True
  | some e => e ∈ Cont ∧ ∀ a ∈ candRows p, a < e → a ∈ Cont
def colValue : Option (Fin (n + 1)) → ℕ
  | none => 0
  | some e => e.val + 1
theorem colValue_le (c : Option (Fin (n + 1))) : colValue c ≤ n + 1 := by
  cases c with
  | none => exact Nat.zero_le _
  | some e => exact e.isLt
def glueRow (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) : RowCutoff (n + 1) where
  β a := if a ∈ Cont then n + 1 else βext p a
  le_β a := by
    split_ifs with h
    · exact a.isLt.le
    · exact le_βext p a
  β_le a := by
    split_ifs with h
    · exact le_rfl
    · exact Nat.le_succ_of_le (βext_le p a)
def glueCol (p : CutoffPair n) (c : Option (Fin (n + 1))) : ColCutoff (n + 1) where
  α d := Fin.snoc (α := fun _ => ℕ) p.1.2.α (colValue c) d
  α_le d := by
    induction d using Fin.lastCases with
    | last => simpa using colValue_le c
    | cast d => simpa using p.1.2.α_le d
theorem glueRow_apply_of_mem {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)}
    (h : a ∈ Cont) : (glueRow p Cont).β a = n + 1 := if_pos h
theorem glueRow_apply_of_notMem {p : CutoffPair n} {Cont : Finset (Fin (n + 1))} {a : Fin (n + 1)}
    (h : a ∉ Cont) : (glueRow p Cont).β a = βext p a := if_neg h
@[simp] theorem glueCol_castSucc (p : CutoffPair n) (c : Option (Fin (n + 1))) (d : Fin n) :
    (glueCol p c).α d.castSucc = p.1.2.α d := by simp [glueCol]
@[simp] theorem glueCol_last (p : CutoffPair n) (c : Option (Fin (n + 1))) :
    (glueCol p c).α (Fin.last n) = colValue c := by simp [glueCol]
theorem criterion_glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : Criterion (glueRow p Cont) (glueCol p c) := by
  intro d
  induction d using Fin.lastCases with
  | last =>
    cases c with
    | none => exact Or.inl (by simp [colValue])
    | some e =>
      right
      obtain ⟨heC, hpre⟩ := hc
      refine ⟨e, by simp [colValue], ?_, ?_⟩
      · rw [Fin.val_last, glueRow_apply_of_mem heC]
        exact Nat.lt_succ_self _
      · intro a hae hβ
        rw [Fin.val_last] at hβ
        by_cases haC : a ∈ Cont
        · rw [glueRow_apply_of_mem haC] at hβ
          omega
        · rw [glueRow_apply_of_notMem haC] at hβ
          exact haC (hpre a (mem_candRows.2 hβ) hae)
  | cast d =>
    rcases p.2 d with h0 | ⟨e, he, hde, hprev⟩
    · left
      simpa using h0
    · right
      refine ⟨e.castSucc, by simpa using he, ?_, ?_⟩
      · simp only [Fin.val_castSucc]
        by_cases heC : e.castSucc ∈ Cont
        · rw [glueRow_apply_of_mem heC]
          have := d.isLt
          omega
        · rw [glueRow_apply_of_notMem heC, βext_castSucc]
          exact hde
      · intro a hae hβ
        simp only [Fin.val_castSucc] at hβ
        have hd := d.isLt
        by_cases haC : a ∈ Cont
        · rw [glueRow_apply_of_mem haC] at hβ
          omega
        · rw [glueRow_apply_of_notMem haC] at hβ
          induction a using Fin.lastCases with
          | last => exact absurd hae (not_lt.2 (Fin.le_last _))
          | cast a =>
            rw [βext_castSucc] at hβ
            exact hprev a (Fin.castSucc_lt_castSucc_iff.1 hae) hβ
def glue (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) (c : Option (Fin (n + 1)))
    (hc : Allowed p Cont c) : CutoffPair (n + 1) :=
  ⟨(glueRow p Cont, glueCol p c), criterion_glue p Cont c hc⟩
def contOf (x : CutoffPair (n + 1)) : Finset (Fin (n + 1)) :=
  univ.filter (fun a => x.1.1.β a = n + 1)
theorem mem_contOf {x : CutoffPair (n + 1)} {a : Fin (n + 1)} : a ∈ contOf x ↔ x.1.1.β a = n + 1 := by
  simp [contOf]
def colOf (x : CutoffPair (n + 1)) : Option (Fin (n + 1)) :=
  if h : x.1.2.α (Fin.last n) = 0 then none
  else some ⟨x.1.2.α (Fin.last n) - 1, by have := x.1.2.α_le (Fin.last n); rw [Fin.val_last] at this; omega⟩
theorem βext_restrict (x : CutoffPair (n + 1)) (a : Fin (n + 1)) :
    βext x.restrict a = min (x.1.1.β a) n := by
  induction a using Fin.lastCases with
  | last =>
    rw [βext_last]
    have := x.1.1.le_β (Fin.last n)
    rw [Fin.val_last] at this
    omega
  | cast a =>
    rw [βext_castSucc]
    rfl
theorem allowed_colOf (x : CutoffPair (n + 1)) : Allowed x.restrict (contOf x) (colOf x) := by
  unfold colOf
  split_ifs with h0
  · trivial
  · rcases x.2 (Fin.last n) with h | ⟨e, he, hne, hprev⟩
    · exact absurd h h0
    · rw [Fin.val_last] at hne hprev
      have hee : (⟨x.1.2.α (Fin.last n) - 1, by have := x.1.2.α_le (Fin.last n); rw [Fin.val_last] at this; omega⟩ :
          Fin (n + 1)) = e := Fin.ext (by simp only; omega)
      show Allowed x.restrict (contOf x) (some _)
      rw [hee]
      refine ⟨mem_contOf.2 ?_, ?_⟩
      · have := x.1.1.β_le e
        omega
      · intro a ha hae
        rw [mem_candRows, βext_restrict] at ha
        rw [mem_contOf]
        have h1 := hprev a hae
        have h2 := x.1.1.β_le a
        omega
def choices (p : CutoffPair n) (Cont : Finset (Fin (n + 1))) : Finset (Option (Fin (n + 1))) :=
  insert none ((Cont.filter (fun e => ∀ a ∈ candRows p, a < e → a ∈ Cont)).image some)
def model (p : CutoffPair n) : Finset (Σ _ : Finset (Fin (n + 1)), Option (Fin (n + 1))) :=
  (candRows p).powerset.sigma (fun Cont => choices p Cont)
def cpSum (n : ℕ) : Rq[X] := ∑ p : CutoffPair n, cpWeight p
def cutoffPairZero : CutoffPair 0 :=
  ⟨(⟨fun a => a.elim0, fun a => a.elim0, fun a => a.elim0⟩, ⟨fun d => d.elim0, fun d => d.elim0⟩),
    fun d => d.elim0⟩
instance : Subsingleton (CutoffPair 0) :=
  ⟨fun _ _ => Subtype.ext (Prod.ext (RowCutoff.ext (funext fun a => a.elim0))
    (ColCutoff.ext (funext fun d => d.elim0)))⟩
end LinearQuiver
end PretorsionImageClosed


