-- Prove2me | Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge
-- name    : Submission_ThreeSumApsp_Lang_Lib_Merge
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-03T07:51:53.850363+00:00
-- url     : https://prove2.me/theorems/45d0e84c-5a53-4008-844e-c5ea59fce0c0
-- title:
--   Merge
-- statement:
--   Shared definitions for the weighted-cache 3SUM development.
-- source:
--   https://github.com/Wang-jiong-han/3sum-weighted-cache/blob/ac885d10bdbf723c3e0549198f9345bedf2a4131/Submission/ThreeSumApsp/Lang/Lib/Merge.lean

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
public import Theorems.Thm_Light_Ends_set
public import Theorems.Thm_Light_Ends_store
public import Theorems.Thm_Light_sameFrame_cons_cons
public import Theorems.Thm_Light_sameFrame_cons_nil
public import Theorems.Thm_Light_sameFrame_nil
public import Theorems.Thm_Light_sameFrame_nil_cons
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast


set_option autoImplicit false
@[expose] public section
namespace Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Merge
variable {l r : List ℤ} {i j : ℕ}
end Merge
namespace Merge
abbrev ListA : ℕ := 0
@[inherit_doc ListA] abbrev LenA : ℕ := 1
@[inherit_doc ListA] abbrev ListB : ℕ := 2
@[inherit_doc ListA] abbrev LenB : ℕ := 3
@[inherit_doc ListA] abbrev Dest : ℕ := 4
@[inherit_doc ListA] abbrev DoneA : ℕ := 5
@[inherit_doc ListA] abbrev DoneB : ℕ := 6
end Merge
open Merge in
/-- The next output is the head of the first list: dst[i + j] := a[i]; i := i + 1. -/
def mergeTakeLeft : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListA +' v DoneA)) ;;
  .set DoneA (v DoneA +' k 1)
open Merge in
/-- The next output is the head of the second list: dst[i + j] := b[j]; j := j + 1. -/
def mergeTakeRight : Stmt :=
  .store (v Dest +' v DoneA +' v DoneB) (M (v ListB +' v DoneB)) ;;
  .set DoneB (v DoneB +' k 1)
open Merge in
/-- merge(a, na, b, nb, dst). -/
def mergeBody : Stmt :=
  .set DoneA (k 0) ;;
  .set DoneB (k 0) ;;
  .while (v DoneA +' v DoneB <' v LenA +' v LenB) (
    .ite (v DoneA <' v LenA)
      (.ite (v DoneB <' v LenB)
        (.ite (M (v ListB +' v DoneB) <' M (v ListA +' v DoneA)) mergeTakeRight mergeTakeLeft)
        mergeTakeLeft)
      mergeTakeRight)
namespace Merge
structure Pre (lim : Limits) (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  segL : Seg μ a l
  segR : Seg μ b r
  spaceL : a + l.length ≤ lim.space
  spaceR : b + r.length ≤ lim.space
  spaceD : dst + (l.length + r.length) ≤ lim.space
  sepL : Apart a l.length dst (l.length + r.length)
  sepR : Apart b r.length dst (l.length + r.length)
def Inv (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (i j : ℕ) (σ : State) : Prop :=
  ∃ (μ' : ℕ → ℤ) (out : List ℤ), σ = ⟨frame [a, l.length, b, r.length, dst, i, j], μ'⟩ ∧
    i ≤ l.length ∧ j ≤ r.length ∧ SameOutside μ μ' dst (l.length + r.length) ∧
    out.length = i + j ∧ Seg μ' dst out ∧ out ++ (l.drop i).merge (r.drop j) = l.merge r
def Taken (μ : ℕ → ℤ) (a b dst : ℕ) (l r : List ℤ) (t : ℕ) (σ : State) : Prop :=
  ∃ i j, i + j = t ∧ Inv μ a b dst l r i j σ
variable {μ : ℕ → ℤ} {a b dst : ℕ} {l r : List ℤ} {i j : ℕ}
@[simp] def _root_.Light.mergeTime (n : ℕ) : ℕ := 40 * n + 12
end Merge
end Light


