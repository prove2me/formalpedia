-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Fields_FieldReflection
-- name    : CSL_Interchange_Framework_Fields_FieldReflection
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:23:08.244983+00:00
-- url     : https://prove2.me/theorems/29045fe1-47be-44ac-8caf-d04b55be669e
-- title:
--   Coded sorting library: Interchange / Framework / Fields / FieldReflection
-- statement:
--   Module `CodedSorting.Interchange.Framework.Fields.FieldReflection` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Reversing the selected field takes two real segment-reversal passes.
--   Neither the number of prefixes nor the modulus enters the number of buffers.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Fields.FieldReflection

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_TriangularStreams
import Definitions.Def_CSL_Interchange_Framework_Memory_LayoutMachine

/-! Reversing the selected field takes two real segment-reversal passes.
Neither the number of prefixes nor the modulus enters the number of buffers. -/

namespace CSL.FieldReflection

open TriangularStreams BlockReflection

variable {P Q S : ℕ}

theorem rev_pair (c : Fin Q) (s : Fin S) :
    (finProdFinEquiv (c,s)).rev = finProdFinEquiv (c.rev,s.rev) := by
  apply Fin.ext
  have hc : c.rev.val + c.val + 1 = Q := by simp only [Fin.val_rev]; omega
  have hs : s.rev.val + s.val + 1 = S := by simp only [Fin.val_rev]; omega
  have hp : (finProdFinEquiv (c,s)).rev.val + s.val + S * c.val + 1 = Q * S := by
    have h := (finProdFinEquiv (c,s)).isLt
    change s.val + S * c.val < Q * S at h
    simp only [Fin.val_rev]
    change Q * S - (s.val + S * c.val + 1) + s.val + S * c.val + 1 = Q * S
    omega
  change (finProdFinEquiv (c,s)).rev.val = s.rev.val + S * c.rev.val
  nlinarith

theorem reassociate (p : Fin P) (c : Fin Q) (s : Fin S) :
    finCongr (Nat.mul_assoc P Q S) (finProdFinEquiv (finProdFinEquiv (p,c),s)) =
      tripleEncode (p,c,s) := by
  apply Fin.ext
  change s.val + S * (c.val + Q * p.val) = s.val + S * c.val + (Q * S) * p.val
  ring

def suffixReverse : Equiv.Perm (Fin (P * (Q * S))) :=
  (finCongr (Nat.mul_assoc P Q S)).symm.trans
    ((segmentReverseEquiv (P * Q) S).trans (finCongr (Nat.mul_assoc P Q S)))

@[simp] theorem suffixReverse_triple (p : Fin P) (c : Fin Q) (s : Fin S) :
    suffixReverse (tripleEncode (p,c,s)) = tripleEncode (p,c,s.rev) := by
  simp only [suffixReverse, Equiv.trans_apply]
  rw [← reassociate p c s, Equiv.symm_apply_apply, segmentReverse_pair, reassociate]

@[simp] theorem bigReverse_triple (p : Fin P) (c : Fin Q) (s : Fin S) :
    segmentReverseEquiv P (Q*S) (tripleEncode (p,c,s)) =
      tripleEncode (p,c.rev,s.rev) := by
  change segmentReverseEquiv P (Q*S) (finProdFinEquiv (p,finProdFinEquiv (c,s))) = _
  rw [segmentReverse_pair,rev_pair]
  rfl

/-- Two real passes reverse the field and restore every suffix coordinate. -/
theorem two_reversals :
    (segmentReverseEquiv P (Q*S)).trans suffixReverse =
      globalFieldEquiv (S := S) (fun (_ : Fin P) => Fin.revPerm) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨p,c,s⟩,rfl⟩ := tripleEncode.surjective x
  simp only [Equiv.trans_apply,bigReverse_triple,suffixReverse_triple,Fin.rev_rev,
    globalFieldEquiv_encoded]
  rfl

theorem reversals_commute :
    suffixReverse.trans (segmentReverseEquiv P (Q*S)) =
      globalFieldEquiv (S := S) (fun (_ : Fin P) => Fin.revPerm) := by
  apply Equiv.ext
  intro x
  obtain ⟨⟨p,c,s⟩,rfl⟩ := tripleEncode.surjective x
  simp only [Equiv.trans_apply,bigReverse_triple,suffixReverse_triple,Fin.rev_rev,
    globalFieldEquiv_encoded]
  rfl

variable {Value : Type*}

/-- The first disk is completed before the second pass begins, allowing the
same five block buffers to be reused. Intermediate data are external files. -/
def execute (source target : Disk Value) (B P Q S : ℕ) (hB : 0 < B) : Execution Value :=
  let n := (P * (Q * S) + B - 1) / B
  let first := run source B (Q*S) hB n ⟨target,[]⟩
  let second := run first.disk B S hB n ⟨target,[]⟩
  ⟨second.disk,first.trace ++ second.trace⟩

/-- Actual output values and actual transfer trace for field reflection. -/
theorem global_field_reversal (source target : Disk Value) (B P Q S : ℕ)
    (hB : 0 < B) (hQ : 0 < Q) (hS : 0 < S) :
    (∀ y : Fin (P * (Q*S)), (execute source target B P Q S hB).disk y.val =
      source ((globalFieldEquiv (S := S) (fun (_ : Fin P) => Fin.revPerm)) y).val) ∧
    (execute source target B P Q S hB).trace.length =
      10 * ((P * (Q*S) + B - 1) / B) := by
  let n := (P * (Q*S) + B - 1) / B
  let first := run source B (Q*S) hB n ⟨target,[]⟩
  have hfirst := (full_reversal source target B P (Q*S) hB (Nat.mul_pos hQ hS)).1
  have hsecond := (full_reversal first.disk target B (P*Q) S hB hS).1
  constructor
  · intro y
    let z : Fin ((P*Q)*S) := (finCongr (Nat.mul_assoc P Q S)).symm y
    have hz := hsecond z
    have he : (P*Q)*S = P*(Q*S) := Nat.mul_assoc P Q S
    simp only [he] at hz
    change (execute source target B P Q S hB).disk y.val =
      first.disk (segmentReverseEquiv (P*Q) S z).val at hz
    rw [hz]
    let w : Fin (P*(Q*S)) := finCongr he (segmentReverseEquiv (P*Q) S z)
    have hw := hfirst w
    change first.disk w.val = _ at hw
    rw [show (segmentReverseEquiv (P*Q) S z).val = w.val from rfl, hw]
    congr 2
    change segmentReverseEquiv P (Q*S) (suffixReverse y) = _
    exact congrArg (fun e : Equiv.Perm (Fin (P*(Q*S))) => e y) reversals_commute
  · simp only [execute, List.length_append,run_transfers,List.length_nil,Nat.zero_add]
    omega

end CSL.FieldReflection


