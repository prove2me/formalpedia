-- Prove2me | Definitions.Def_CSL_Shared_Records_KeyRecordWords
-- name    : CSL_Shared_Records_KeyRecordWords
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:57:05.407856+00:00
-- url     : https://prove2.me/theorems/10a98206-277e-4467-87e7-a502135a6fd9
-- title:
--   Coded sorting library: Shared / Records / KeyRecordWords
-- statement:
--   Module `CodedSorting.Shared.Records.KeyRecordWords` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   List/key-payload interface for the finite-array recursive sorter.
--   Sentinels are separate constructors and cannot be confused with integer data.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Records.KeyRecordWords

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Sorting_Local_Framework_LocalSortingCost
import Definitions.Def_CSL_Sorting_Radix_Model_ExternalMSD
import Mathlib.Data.Prod.Lex
import Definitions.Def_CSL_Shared_Words_WordConvention

section KeyRecords
/-! List/key-payload interface for the finite-array recursive sorter.
Sentinels are separate constructors and cannot be confused with integer data. -/
namespace CSL.KeyRecords
open RecursiveColumnsort

abbrev Record := WithBot (WithTop (ℕ ×ₗ ℕ))

def encode (key : ℕ → ℕ) (x : ℕ) : Record :=
  ↑((↑(toLex (key x, x)) : WithTop (ℕ ×ₗ ℕ)))

def decode (r : Record) : ℕ :=
  (ofLex ((r.unbotD ⊤).untopD (toLex (0, 0)))).2

@[simp] theorem decode_encode (key : ℕ → ℕ) (x : ℕ) : decode (encode key x) = x := by
  simp [decode, encode]

theorem encode_key_order (key : ℕ → ℕ) (x y : ℕ) (h : encode key x ≤ encode key y) :
    key x ≤ key y := by
  have h' : toLex (key x, x) ≤ toLex (key y, y) := by simpa [encode] using h
  exact Prod.Lex.monotone_fst _ _ h'

def input (key : ℕ → ℕ) (xs : List ℕ) : Fin xs.length → Record :=
  fun i => encode key xs[i.val]

theorem input_list (key : ℕ → ℕ) (xs : List ℕ) : List.ofFn (input key xs) = xs.map (encode key) :=
  List.ofFn_getElem_eq_map xs (encode key)

def adapt (sorter : Sorter Record) : MSD.LocalSorter := fun key xs =>
  (List.ofFn (sorter xs.length (input key xs)).output).map decode

/-- The decoder never silently drops or fabricates a record: the actual
output is a permutation of encoded ordinary records, hence contains no
sentinels introduced by the sorting construction. -/
theorem adapt_correct (sorter : Sorter Record)
    (hc : ∀ n (f : Fin n → Record), Correct f (sorter n f).output) :
    MSD.LocalCorrect (adapt sorter) := by
  intro key xs
  have hs := hc xs.length (input key xs)
  have hp : (List.ofFn (sorter xs.length (input key xs)).output).Perm (xs.map (encode key)) := by
    simpa only [input_list] using hs.2
  constructor
  · have h := hp.map decode
    simpa [adapt, List.map_map, Function.comp_def] using h
  · change ((List.ofFn (sorter xs.length (input key xs)).output).map decode).Pairwise _
    rw [List.pairwise_map]
    apply hs.1.ofFn_sorted.imp_of_mem
    intro a b ha hb hab
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp ha)
    obtain ⟨y, _, rfl⟩ := List.mem_map.mp (hp.mem_iff.mp hb)
    simpa using encode_key_order key x y hab

/-- Cost and output refer to the same invocation and its emitted trace. -/
def adaptCost (B : ℕ) (exchangeCost : LocalSortingCost.InterchangeCost)
    (sorter : Sorter Record) : MSD.LocalCost := fun key xs =>
  LocalSortingCost.traceCost B exchangeCost (sorter xs.length (input key xs)).trace

end CSL.KeyRecords
end KeyRecords

section KeyRecordWords
/-! The key, associated data, and the two Columnsort sentinels have an explicit encoding in three machine words. This representation supplies the record format used by the sorting simulation. 


-/
set_option autoImplicit false
namespace CSL.KeyRecordWords
open WordControl

inductive Record (w : ℕ) where
  | bottom
  | data (key payload : Word w)
  | top
  deriving DecidableEq

def abstract {w : ℕ} : Record w → KeyRecords.Record
  | .bottom => ⊥
  | .data key payload =>
      ↑((↑(toLex (key.val,payload.val)) : WithTop (ℕ ×ₗ ℕ)))
  | .top => ↑(⊤ : WithTop (ℕ ×ₗ ℕ))

private theorem tag_bound (w : ℕ) (hw : 2≤w) : 2<2^w := by
  have h := Nat.pow_le_pow_right (by decide : 0<2) hw
  norm_num at h
  omega

/-- Tag 0 means bottom, tag 1 an ordinary record, and tag 2 top.
The other two words always hold the unchanged key and payload. -/
def encode (w : ℕ) (hw : 2≤w) : Record w → Words 3 w
  | .bottom => ![0,0,0]
  | .data key payload => ![⟨1,by have h:=tag_bound w hw; omega⟩,key,payload]
  | .top => ![⟨2,tag_bound w hw⟩,0,0]

def decode {w : ℕ} (words : Words 3 w) : Record w :=
  if (words 0).val=1 then .data (words 1) (words 2)
  else if (words 0).val=2 then .top else .bottom

@[simp] theorem decode_encode (w : ℕ) (hw : 2≤w) (r : Record w) :
    decode (encode w hw r)=r := by
  cases r <;> simp [encode,decode]

theorem encode_injective (w : ℕ) (hw : 2≤w) :
    Function.Injective (encode w hw) := by
  intro r s h
  simpa only [decode_encode] using congrArg decode h

theorem abstract_injective (w : ℕ) : Function.Injective (@abstract w) := by
  intro r s h
  cases r with
  | bottom => cases s <;> simp_all [abstract]
  | top => cases s <;> simp_all [abstract]
  | data key payload =>
    cases s with
    | bottom => simp [abstract] at h
    | top => simp [abstract] at h
    | data key' payload' =>
      have hp : toLex (key.val,payload.val)=toLex (key'.val,payload'.val) := by
        simpa only [abstract,WithBot.coe_eq_coe,WithTop.coe_eq_coe] using h
      have hp' := congrArg ofLex hp
      have hk : key=key' := Fin.ext (congrArg Prod.fst hp')
      have hv : payload=payload' := Fin.ext (congrArg Prod.snd hp')
      subst key'
      subst payload'
      rfl

/-- The encoding used by the existing key-payload sorter is exactly the
ordinary-record case when both components are bounded by the global word. -/
theorem abstract_data (w : ℕ) (key : ℕ→ℕ) (x : ℕ)
    (hx : x<2^w) (hk : key x<2^w) :
    abstract (Record.data ⟨key x,hk⟩ ⟨x,hx⟩)=KeyRecords.encode key x := rfl

theorem list_roundtrip (w : ℕ) (hw : 2≤w) (rs : List (Record w)) :
    (rs.map (encode w hw)).map decode=rs := by
  simp [List.map_map,Function.comp_def]

def words (w : ℕ) (hw : 2≤w) (rs : List (Record w)) : List (Word w) :=
  rs.flatMap (fun r => List.ofFn (encode w hw r))

theorem words_length (w : ℕ) (hw : 2≤w) (rs : List (Record w)) :
    (words w hw rs).length=3*rs.length := by
  induction rs with
  | nil => simp [words]
  | cons r rs ih =>
    simp only [words,List.flatMap_cons,List.length_append,List.length_ofFn,
      Fintype.card_fin,List.length_cons] at *
    omega

end CSL.KeyRecordWords
end KeyRecordWords


