-- Prove2me | Definitions.Def_CSL_Shared_Programs_DigitMove
-- name    : CSL_Shared_Programs_DigitMove
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:22:55.992805+00:00
-- url     : https://prove2.me/theorems/592bc9fd-5f36-4f2f-963c-4397d2fe1a6e
-- title:
--   Coded sorting library: Shared / Programs / DigitMove
-- statement:
--   Module `CodedSorting.Shared.Programs.DigitMove` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   A one-digit move used by Appendix C is a real q-stream distribution and
--   reconstruction. The key is the moved digit; the relative order of every
--   other coordinate is unchanged inside each stream.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Shared.Programs.DigitMove

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_TriangularStreams
import Definitions.Def_CSL_Shared_Memory_DiskStreamPass

/-! A one-digit move used by Appendix C is a real q-stream distribution and
reconstruction. The key is the moved digit; the relative order of every
other coordinate is unchanged inside each stream. -/

namespace CSL.DigitMove

open TriangularStreams TagErasure BucketReader AffineStreams

def swapLeading (P q S : ℕ) : TripleAddress P q S ≃ TripleAddress q P S where
  toFun x := (x.2.1,x.1,x.2.2)
  invFun x := (x.2.1,x.1,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

def toFront (P q S : ℕ) : Equiv.Perm (Fin (P*(q*S))) :=
  tripleEncode.symm.trans ((swapLeading P q S).trans
    (tripleEncode.trans (finCongr (by ring))))

def digitKey (P q S : ℕ) (x : Fin (P*(q*S))) : Fin q :=
  (tripleEncode.symm x).2.1

theorem toFront_encoded (P q S : ℕ) (x : TripleAddress P q S) :
    toFront P q S (tripleEncode x) =
      (finCongr (by ring : q*(P*S)=P*(q*S))) (tripleEncode (x.2.1,x.1,x.2.2)) := by
  simp [toFront, swapLeading]

theorem toFront_increasing (P q S : ℕ) :
    ∀ x y, x < y → digitKey P q S x = digitKey P q S y →
      toFront P q S x < toFront P q S y := by
  intro x y hxy hk
  obtain ⟨x,rfl⟩ := tripleEncode.surjective x
  obtain ⟨y,rfl⟩ := tripleEncode.surjective y
  simp only [digitKey, Equiv.symm_apply_apply] at hk
  rw [toFront_encoded, toFront_encoded]
  change tripleEncode (x.2.1,x.1,x.2.2) < tripleEncode (y.2.1,y.1,y.2.2)
  rw [tripleEncode_lt_iff]
  right
  refine ⟨hk, ?_⟩
  rcases (tripleEncode_lt_iff x y).mp hxy with hp | ⟨hp,hrest⟩
  · exact Or.inl hp
  · right
    refine ⟨hp, ?_⟩
    rcases hrest with hbad | ⟨_,hs⟩
    · exact False.elim ((lt_irrefl _ : ¬x.2.1<x.2.1) (by simpa [← hk] using hbad))
    · exact hs

/-- The actual payload-only writer/reader program uses q buffers and has
one global scan bound, with no factor for the number of prefixes. -/
theorem toFront_execution {Value : Type*} (P q S : ℕ)
    (F : Fin (P*(q*S)) → Value) (B : ℕ) (hB : 0<B) :
    ∃ final,
      readIndexed (fun y => digitKey P q S ((toFront P q S).symm y))
        (P*(q*S)) 0 (by omega) (valueReaders (digitKey P q S) F B) =
          some (outputValues (toFront P q S) F,final) ∧
      valueTransfers (toFront P q S) (digitKey P q S) F B hB final ≤
        4*((P*(q*S))/B)+2*q+2 ∧
      occupiedReaders final ≤ q*B :=
  increasing_value_reconstruction _ _ (toFront_increasing P q S) F B hB

theorem fromFront_execution {Value : Type*} (P q S : ℕ)
    (F : Fin (P*(q*S)) → Value) (B : ℕ) (hB : 0<B) :
    ∃ final,
      readIndexed (fun y => digitKey P q S y)
        (P*(q*S)) 0 (by omega)
        (valueReaders (fun y => digitKey P q S ((toFront P q S).symm y)) F B) =
          some (outputValues (toFront P q S).symm F,final) ∧
      valueTransfers (toFront P q S).symm
        (fun y => digitKey P q S ((toFront P q S).symm y)) F B hB final ≤
        4*((P*(q*S))/B)+2*q+2 ∧
      occupiedReaders final ≤ q*B := by
  have h := increasing_value_reconstruction (toFront P q S).symm
    (fun y => digitKey P q S ((toFront P q S).symm y))
    (inverse_increasing_streams _ _ (toFront_increasing P q S)) F B hB
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using h

/-- The outer prefixes stay in their original order while the digit moves
within each prefix. All prefixes still share the same q physical streams. -/
def insidePrefix (Outer P q S : ℕ) : Equiv.Perm (Fin (Outer*(P*(q*S)))) :=
  finProdFinEquiv.symm.trans
    ((Equiv.prodCongr (Equiv.refl (Fin Outer)) (toFront P q S)).trans finProdFinEquiv)

def insideKey (Outer P q S : ℕ) (x : Fin (Outer*(P*(q*S)))) : Fin q :=
  digitKey P q S (finProdFinEquiv.symm x).2

theorem insidePrefix_encoded (Outer P q S : ℕ) (p : Fin Outer)
    (x : Fin (P*(q*S))) :
    insidePrefix Outer P q S (finProdFinEquiv (p,x)) =
      finProdFinEquiv (p,toFront P q S x) := by
  simp [insidePrefix]

theorem insidePrefix_increasing (Outer P q S : ℕ) :
    ∀ x y, x < y → insideKey Outer P q S x = insideKey Outer P q S y →
      insidePrefix Outer P q S x < insidePrefix Outer P q S y := by
  intro x y hxy hk
  obtain ⟨⟨p,x⟩,rfl⟩ := finProdFinEquiv.surjective x
  obtain ⟨⟨r,y⟩,rfl⟩ := finProdFinEquiv.surjective y
  simp only [insideKey, Equiv.symm_apply_apply] at hk
  rw [insidePrefix_encoded, insidePrefix_encoded, pairEncode_lt_iff]
  rcases (pairEncode_lt_iff (p,x) (r,y)).mp hxy with hp | ⟨hp,hxy⟩
  · exact Or.inl hp
  · exact Or.inr ⟨hp,toFront_increasing P q S x y hxy hk⟩

theorem insidePrefix_execution {Value : Type*} (Outer P q S : ℕ)
    (F : Fin (Outer*(P*(q*S))) → Value) (B : ℕ) (hB : 0<B) :
    ∃ final,
      readIndexed (fun y => insideKey Outer P q S ((insidePrefix Outer P q S).symm y))
        (Outer*(P*(q*S))) 0 (by omega) (valueReaders (insideKey Outer P q S) F B) =
          some (outputValues (insidePrefix Outer P q S) F,final) ∧
      valueTransfers (insidePrefix Outer P q S) (insideKey Outer P q S) F B hB final ≤
        4*((Outer*(P*(q*S)))/B)+2*q+2 ∧ occupiedReaders final ≤ q*B :=
  increasing_value_reconstruction _ _ (insidePrefix_increasing Outer P q S) F B hB

theorem insidePrefix_inverse_execution {Value : Type*} (Outer P q S : ℕ)
    (F : Fin (Outer*(P*(q*S))) → Value) (B : ℕ) (hB : 0<B) :
    ∃ final,
      readIndexed (fun y => insideKey Outer P q S y)
        (Outer*(P*(q*S))) 0 (by omega)
        (valueReaders (fun y => insideKey Outer P q S
          ((insidePrefix Outer P q S).symm y)) F B) =
          some (outputValues (insidePrefix Outer P q S).symm F,final) ∧
      valueTransfers (insidePrefix Outer P q S).symm
        (fun y => insideKey Outer P q S ((insidePrefix Outer P q S).symm y)) F B hB final ≤
        4*((Outer*(P*(q*S)))/B)+2*q+2 ∧ occupiedReaders final ≤ q*B := by
  have h := increasing_value_reconstruction (insidePrefix Outer P q S).symm
    (fun y => insideKey Outer P q S ((insidePrefix Outer P q S).symm y))
    (inverse_increasing_streams _ _ (insidePrefix_increasing Outer P q S)) F B hB
  simpa only [Equiv.symm_symm, Equiv.symm_apply_apply] using h

/-- The actual source reader, bucket files, and output writer implement
the move. Its finished disk can feed the next pass without a free repack. -/
theorem insidePrefix_disk_execution {Value : Type*} (Outer P q S : ℕ)
    (F : Fin (Outer*(P*(q*S))) → Value) (B : ℕ) (hB : 0<B) :
    ∃ result,
      DiskStreamPass.run (insidePrefix Outer P q S) (insideKey Outer P q S) B
        (BucketMachine.pack B hB (inputValues F)) = some result ∧
      result.output.finish = BucketMachine.pack B hB (outputValues (insidePrefix Outer P q S) F) ∧
      result.transfers ≤ 4*((Outer*(P*(q*S)))/B)+2*q+2 ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) :=
  DiskStreamPass.run_packed_canonical _ _ (insidePrefix_increasing Outer P q S) F B hB

theorem insidePrefix_inverse_disk_execution {Value : Type*} (Outer P q S : ℕ)
    (F : Fin (Outer*(P*(q*S))) → Value) (B : ℕ) (hB : 0<B) :
    ∃ result,
      DiskStreamPass.run (insidePrefix Outer P q S).symm
        (fun y => insideKey Outer P q S ((insidePrefix Outer P q S).symm y)) B
        (BucketMachine.pack B hB (inputValues F)) = some result ∧
      result.output.finish = BucketMachine.pack B hB
        (outputValues (insidePrefix Outer P q S).symm F) ∧
      result.transfers ≤ 4*((Outer*(P*(q*S)))/B)+2*q+2 ∧
      result.output.Valid B ∧ (∀ k, (result.readers k).Valid B) :=
  DiskStreamPass.run_packed_canonical _ _
    (inverse_increasing_streams _ _ (insidePrefix_increasing Outer P q S)) F B hB

end CSL.DigitMove


