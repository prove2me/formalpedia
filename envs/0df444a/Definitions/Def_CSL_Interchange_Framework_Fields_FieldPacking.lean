-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Fields_FieldPacking
-- name    : CSL_Interchange_Framework_Fields_FieldPacking
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:23:31.235922+00:00
-- url     : https://prove2.me/theorems/cc4a13da-8971-4e8c-93b1-03e5be442c1f
-- title:
--   Coded sorting library: Interchange / Framework / Fields / FieldPacking
-- statement:
--   Module `CodedSorting.Interchange.Framework.Fields.FieldPacking` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # Canonical packing of consecutive scalar fields
--
--   Earlier coordinates are more significant digits. These equivalences only
--   regroup one linear base-q address; they do not move any payload or reorder
--   spectator coordinates.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Fields.FieldPacking

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Shared_Indexing_LexBlocks
import Mathlib.Algebra.BigOperators.Fin

/-!
# Canonical packing of consecutive scalar fields

Earlier coordinates are more significant digits. These equivalences only
regroup one linear base-q address; they do not move any payload or reorder
spectator coordinates.
-/

set_option autoImplicit false

namespace CSL.FieldPacking

open CSL.Address
open scoped BigOperators

variable {q m f : ℕ}

/-- Reverse the indexing convention of mathlib's least-significant-first
finite-function encoding, so the first coordinate is the highest digit. -/
def digitPacking (Q m : ℕ) : (Fin m → Fin Q) ≃ Fin (Q ^ m) :=
  (Equiv.arrowCongr Fin.revPerm (Equiv.refl (Fin Q))).trans finFunctionFinEquiv

@[simp] theorem digitPacking_val (x : Fin m → Fin q) :
    (digitPacking q m x).val = ∑ i : Fin m, (x i.rev).val * q ^ i.val := rfl

@[simp] theorem digitPacking_symm_val (x : Fin (q ^ m)) (i : Fin m) :
    ((digitPacking q m).symm x i).val = x.val / q ^ i.rev.val % q := rfl

/-- The significance of original coordinate i is q^(m-1-i). -/
theorem digitPacking_val_high (x : Fin m → Fin q) :
    (digitPacking q m x).val = ∑ i : Fin m, (x i).val * q ^ i.rev.val := by
  rw [digitPacking_val]
  simpa only [Fin.revPerm_apply, Fin.rev_rev] using
    (Equiv.sum_comp Fin.revPerm (fun i : Fin m => (x i).val * q ^ i.rev.val))

theorem digitPacking_succ_val (x : Fin (m + 1) → Fin q) :
    (digitPacking q (m + 1) x).val =
      (x 0).val * q ^ m + (digitPacking q m (fun i => x i.succ)).val := by
  rw [digitPacking_val, Fin.sum_univ_castSucc, digitPacking_val]
  simp only [Fin.rev_castSucc, Fin.coe_castSucc, Fin.rev_last, Fin.val_last]
  omega

theorem digitPacking_increasing (x y : Fin m → Fin q)
    (hxy : Pi.Lex (· < ·) (· < ·) x y) : digitPacking q m x < digitPacking q m y := by
  induction m with
  | zero => obtain ⟨j,_,_⟩ := hxy; exact j.elim0
  | succ m ih =>
    obtain ⟨j,hpre,hj⟩ := hxy
    change (digitPacking q (m + 1) x).val < (digitPacking q (m + 1) y).val
    rw [digitPacking_succ_val,digitPacking_succ_val]
    rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j,rfl⟩
    · have hx := (digitPacking q m (fun i => x i.succ)).isLt
      have hhead : (x 0).val < (y 0).val := hj
      nlinarith
    · have hhead : x 0 = y 0 := hpre 0 (Fin.succ_pos j)
      rw [hhead]
      apply Nat.add_lt_add_left
      apply ih
      exact ⟨j,fun k hk => hpre k.succ (Fin.succ_lt_succ_iff.mpr hk),hj⟩

/-- The explicit digit encoding is exactly the common lexicographic disk
layout used for the physical coordinate scans. -/
theorem digitPacking_eq_lexLayout : digitPacking q m = TriangularStreams.lexLayout := by
  let e : Equiv.Perm (Fin (q ^ m)) :=
    TriangularStreams.lexLayout.symm.trans (digitPacking q m)
  have hemono : StrictMono e := by
    intro a b hab
    apply digitPacking_increasing
    apply (TriangularStreams.lexLayout_lt _ _).mp
    simpa only [Equiv.apply_symm_apply] using hab
  have he : (e : Fin (q ^ m) → Fin (q ^ m)) = id :=
    (hemono.range_inj strictMono_id).mp (by simp only [Equiv.range_eq_univ, Set.range_id])
  apply Equiv.ext
  intro x
  have h := congrFun he (TriangularStreams.lexLayout x)
  simpa only [e, Equiv.trans_apply, Equiv.symm_apply_apply, id_eq] using h

noncomputable def orderedDigitPacking (I : Type*) [Fintype I] [LinearOrder I]
    (Q : ℕ) : (I → Fin Q) ≃ Fin (Q ^ Fintype.card I) :=
  (Equiv.arrowCongr (Fintype.orderIsoFinOfCardEq I rfl).symm.toEquiv
    (Equiv.refl (Fin Q))).trans (digitPacking Q (Fintype.card I))

theorem orderedDigitPacking_increasing (I : Type*) [Fintype I] [LinearOrder I]
    (Q : ℕ) (x y : I → Fin Q) (hxy : Pi.Lex (· < ·) (· < ·) x y) :
    orderedDigitPacking I Q x < orderedDigitPacking I Q y := by
  apply digitPacking_increasing
  let enum := Fintype.orderIsoFinOfCardEq I rfl
  change Pi.Lex (· < ·) (· < ·) (fun i => x (enum i)) (fun i => y (enum i))
  obtain ⟨j,hpre,hj⟩ := hxy
  refine ⟨enum.symm j,?_,?_⟩
  · intro k hk
    apply hpre
    exact (enum.lt_symm_apply).mp hk
  · simpa only [OrderIso.apply_symm_apply] using hj

/-- The ordered digit formula and the rank of the lexicographic subvector
coincide, including the before/after subvectors around a selected field. -/
theorem orderedDigitPacking_eq_subvectorEncode (I : Type*) [Fintype I] [LinearOrder I]
    [WellFoundedLT I] (Q : ℕ) :
    orderedDigitPacking I Q = LexBlocks.subvectorEncode := by
  let e : Equiv.Perm (Fin (Q ^ Fintype.card I)) :=
    LexBlocks.subvectorEncode.symm.trans (orderedDigitPacking I Q)
  have hemono : StrictMono e := by
    intro a b hab
    apply orderedDigitPacking_increasing
    apply (LexBlocks.subvectorEncode_lt _ _).mp
    simpa only [Equiv.apply_symm_apply] using hab
  have he : (e : Fin (Q ^ Fintype.card I) → Fin (Q ^ Fintype.card I)) = id :=
    (hemono.range_inj strictMono_id).mp (by simp only [Equiv.range_eq_univ, Set.range_id])
  apply Equiv.ext
  intro x
  have h := congrFun he (LexBlocks.subvectorEncode x)
  simpa only [e, Equiv.trans_apply, Equiv.symm_apply_apply, id_eq] using h

instance powerNeZero (q f : ℕ) [NeZero q] : NeZero (q ^ f) :=
  ⟨pow_ne_zero _ (NeZero.ne q)⟩

@[simp] theorem finEquiv_val (n : ℕ) [NeZero n] (x : Fin n) :
    (ZMod.finEquiv n x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

@[simp] theorem finEquiv_symm_val (n : ℕ) [NeZero n] (x : ZMod n) :
    ((ZMod.finEquiv n).symm x).val = x.val := by
  cases n with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

/-- Canonical base-q^f packing of m adjacent scalar fields. -/
def packing (q m f : ℕ) [NeZero q] :
    (Fin m → ZMod (q ^ f)) ≃ ZMod (q ^ (m * f)) :=
  (Equiv.arrowCongr (Equiv.refl (Fin m)) (ZMod.finEquiv (q ^ f)).symm.toEquiv).trans
    ((digitPacking (q ^ f) m).trans
      ((finCongr (by rw [← pow_mul, Nat.mul_comm f m])).trans
        (ZMod.finEquiv (q ^ (m * f))).toEquiv))

theorem packing_val_eq [NeZero q] (x : Fin m → ZMod (q ^ f)) :
    (packing q m f x).val =
      (digitPacking (q ^ f) m (fun i => (ZMod.finEquiv (q ^ f)).symm (x i))).val := by
  simp only [packing, Equiv.trans_apply, RingEquiv.toEquiv_eq_coe, Equiv.coe_fn_mk,
    RingEquiv.coe_toEquiv, finEquiv_val, finCongr_apply]
  rfl

/-- Exact physical number of the grouped field in the original digit order. -/
theorem packing_val [NeZero q] (x : Fin m → ZMod (q ^ f)) :
    (packing q m f x).val =
      ∑ i : Fin m, (x i).val * (q ^ f) ^ i.rev.val := by
  rw [packing_val_eq,digitPacking_val_high]
  simp only [finEquiv_symm_val]

/-- Splitting recovers the indicated contiguous block of f base-q digits. -/
theorem packing_digit [NeZero q] (x : Fin m → ZMod (q ^ f)) (i : Fin m) :
    (x i).val = (packing q m f x).val / (q ^ f) ^ i.rev.val % (q ^ f) := by
  rw [packing_val_eq]
  have h := digitPacking_symm_val
    (digitPacking (q ^ f) m (fun j => (ZMod.finEquiv (q ^ f)).symm (x j))) i
  simpa only [Equiv.symm_apply_apply, finEquiv_symm_val] using h

/-- An arbitrary ordered finite coordinate set is enumerated in its actual
order, not by an arbitrary cardinality equivalence. -/
noncomputable def vectorFinPacking (I : Type*) [Fintype I] [LinearOrder I]
    (q f : ℕ) [NeZero q] :
    (I → ZMod (q ^ f)) ≃ Fin ((q ^ f) ^ Fintype.card I) :=
  (Equiv.arrowCongr (Fintype.orderIsoFinOfCardEq I rfl).symm.toEquiv
    (ZMod.finEquiv (q ^ f)).symm.toEquiv).trans
      (digitPacking (q ^ f) (Fintype.card I))

theorem vectorFinPacking_val (I : Type*) [Fintype I] [LinearOrder I]
    (q f : ℕ) [NeZero q] (x : I → ZMod (q ^ f)) :
    (vectorFinPacking I q f x).val =
      ∑ i : Fin (Fintype.card I),
        ((ZMod.finEquiv (q ^ f)).symm
          (x ((Fintype.orderIsoFinOfCardEq I rfl) i))).val *
            (q ^ f) ^ i.rev.val := by
  exact digitPacking_val_high _

theorem vectorFinPacking_eq_subvectorEncode (I : Type*) [Fintype I] [LinearOrder I]
    [WellFoundedLT I] (q f : ℕ) [NeZero q] (x : I → ZMod (q ^ f)) :
    vectorFinPacking I q f x = LexBlocks.subvectorEncode
      (fun i => (ZMod.finEquiv (q ^ f)).symm (x i)) := by
  exact congrArg (fun e : (I → Fin (q ^ f)) ≃ Fin ((q ^ f) ^ Fintype.card I) =>
    e (fun i => (ZMod.finEquiv (q ^ f)).symm (x i)))
      (orderedDigitPacking_eq_subvectorEncode I (q ^ f))

/-- Lift a field conversion in place, retaining P,H,G,D,S order. -/
def fieldEquiv {A A' Prefix Gap Suffix : Type*} (e : A ≃ A') :
    FullAddress Prefix A Gap Suffix ≃ FullAddress Prefix A' Gap Suffix where
  toFun a := ⟨a.prefixCoord, e a.high, a.gap, e a.low, a.suffix⟩
  invFun a := ⟨a.prefixCoord, e.symm a.high, a.gap, e.symm a.low, a.suffix⟩
  left_inv a := by cases a; simp only [Equiv.symm_apply_apply]
  right_inv a := by cases a; simp only [Equiv.apply_symm_apply]

@[simp] theorem fieldEquiv_exchange {A A' Prefix Gap Suffix : Type*}
    (e : A ≃ A') (a : FullAddress Prefix A Gap Suffix) :
    fieldEquiv e (exchange a) = exchange (fieldEquiv e a) := rfl

/-- Packing or unpacking the fields commutes with their recursive exchange. -/
theorem exchange_conjugacy {A A' Prefix Gap Suffix : Type*} (e : A ≃ A') :
    (fieldEquiv (Prefix := Prefix) (Gap := Gap) (Suffix := Suffix) e).trans
      (exchangeEquiv.trans (fieldEquiv e).symm) = exchangeEquiv := by
  apply Equiv.ext
  intro a
  cases a
  simp [fieldEquiv,exchangeEquiv,exchange]

theorem transport_exchange {A A' Prefix Gap Suffix Value : Type*} (e : A ≃ A')
    (F : FullAddress Prefix A Gap Suffix → Value) :
    (fun a => (transport exchangeEquiv (fun b => F ((fieldEquiv e).symm b)))
      (fieldEquiv e a)) = transport exchangeEquiv F := by
  funext a
  cases a
  simp [transport,fieldEquiv,exchangeEquiv,exchange]

end CSL.FieldPacking


