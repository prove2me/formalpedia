-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Fields_BinaryPaddingScan
-- name    : CSL_Interchange_Framework_Fields_BinaryPaddingScan
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T13:55:46.630859+00:00
-- url     : https://prove2.me/theorems/9389210b-5adb-4b4e-9c61-6babf8b57ecd
-- title:
--   Coded sorting library: Interchange / Framework / Fields / BinaryPaddingScan
-- statement:
--   Module `CodedSorting.Interchange.Framework.Fields.BinaryPaddingScan` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   # A recursive child exchanges exactly one selected coordinate pair
--
--   For the original order P,H,G,D,S and chosen H_i,D_j, the new prefix is
--   P,H_{<i}; the new gap is H_{>i},G,D_{<j}; and the new suffix is D_{>j},S.
--   This is a regrouping of the same coordinate string, not a permutation of
--   all spectator coordinates into the prefix.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Fields.BinaryPaddingScan

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Circuit_Framework_MatrixFactorization
import Mathlib.Data.Nat.Log
import Definitions.Def_CSL_Shared_Programs_ScanProgramLift

section SingleCoordinate
/-!
# A recursive child exchanges exactly one selected coordinate pair

For the original order P,H,G,D,S and chosen H_i,D_j, the new prefix is
P,H_{<i}; the new gap is H_{>i},G,D_{<j}; and the new suffix is D_{>j},S.
This is a regrouping of the same coordinate string, not a permutation of
all spectator coordinates into the prefix.
-/

set_option autoImplicit false

namespace CSL.SingleCoordinate

open CSL.Address

variable {I R Prefix Gap Suffix : Type*} [LinearOrder I]

abbrev Before (i : I) := {k : I // k < i}
abbrev After (i : I) := {k : I // i < k}

def splitVector (i : I) : (I → R) ≃ ((Before i → R) × R × (After i → R)) where
  toFun x := (fun k => x k.val, x i, fun k => x k.val)
  invFun parts k :=
    if hk : k < i then parts.1 ⟨k,hk⟩
    else if he : k = i then parts.2.1
    else parts.2.2 ⟨k, lt_of_le_of_ne (le_of_not_gt hk) (Ne.symm he)⟩
  left_inv x := by
    funext k
    by_cases hk : k < i
    · simp only [dif_pos hk]
    · simp only [dif_neg hk]
      by_cases he : k = i
      · subst k
        simp
      · simp [he]
  right_inv parts := by
    rcases parts with ⟨before,selected,after⟩
    apply Prod.ext
    · funext k
      simp only [dif_pos k.property]
    · apply Prod.ext
      · simp
      · funext k
        have hn : ¬ k.val < i := not_lt_of_ge (le_of_lt k.property)
        have he : k.val ≠ i := ne_of_gt k.property
        simp [hn,he]

abbrev ShortPrefix (i : I) := Prefix × (Before i → R)
abbrev ShortGap (i j : I) := (After i → R) × Gap × (Before j → R)
abbrev ShortSuffix (j : I) := (After j → R) × Suffix

/-- Exactly the original coordinate order, with two scalar fields exposed. -/
def repack (i j : I) :
    FullAddress Prefix (I → R) Gap Suffix ≃
      FullAddress (ShortPrefix (Prefix := Prefix) (R := R) i) R
        (ShortGap (Gap := Gap) (R := R) i j) (ShortSuffix (Suffix := Suffix) (R := R) j) where
  toFun a :=
    let h := splitVector i a.high
    let d := splitVector j a.low
    ⟨(a.prefixCoord,h.1),h.2.1,(h.2.2,a.gap,d.1),d.2.1,(d.2.2,a.suffix)⟩
  invFun a :=
    ⟨a.prefixCoord.1, (splitVector i).symm (a.prefixCoord.2,a.high,a.gap.1),
      a.gap.2.1, (splitVector j).symm (a.gap.2.2,a.low,a.suffix.1),a.suffix.2⟩
  left_inv a := by
    cases a with
    | mk p h g d s =>
      change FullAddress.mk p ((splitVector i).symm ((splitVector i) h)) g
        ((splitVector j).symm ((splitVector j) d)) s = _
      simp only [Equiv.symm_apply_apply]
  right_inv a := by
    rcases a with ⟨⟨p,beforeH⟩,h,⟨afterH,g,beforeD⟩,d,⟨afterD,s⟩⟩
    try dsimp only
    simp only [Equiv.apply_symm_apply]

/-- Modify only H_i and D_j, preserving every other address coordinate. -/
def modifySelected (i j : I) (op : R × R → R × R)
    (a : FullAddress Prefix (I → R) Gap Suffix) : FullAddress Prefix (I → R) Gap Suffix :=
  let result := op (a.high i,a.low j)
  ⟨a.prefixCoord,Function.update a.high i result.1,a.gap,
    Function.update a.low j result.2,a.suffix⟩

theorem modifySelected_comp (i j : I) (op₁ op₂ : R × R → R × R)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    modifySelected i j op₂ (modifySelected i j op₁ a) =
      modifySelected i j (op₂ ∘ op₁) a := by
  cases a
  simp [modifySelected,Function.comp_def,Function.update_idem]

theorem modifySelected_id (i j : I) (a : FullAddress Prefix (I → R) Gap Suffix) :
    modifySelected i j id a = a := by
  cases a
  simp [modifySelected,Function.update_eq_self]

theorem splitVector_update (i : I) (x : I → R) (a : R) :
    splitVector i (Function.update x i a) =
      ((splitVector i x).1,a,(splitVector i x).2.2) := by
  apply Prod.ext
  · funext k
    exact Function.update_of_ne (ne_of_lt k.property) _ _
  · apply Prod.ext
    · exact Function.update_self _ _ _
    · funext k
      exact Function.update_of_ne (ne_of_gt k.property) _ _

def shortExchange (i j : I) : Equiv.Perm (FullAddress Prefix (I → R) Gap Suffix) where
  toFun := modifySelected i j Prod.swap
  invFun := modifySelected i j Prod.swap
  left_inv a := by
    rw [modifySelected_comp]
    change modifySelected i j id a = a
    exact modifySelected_id i j a
  right_inv a := by
    rw [modifySelected_comp]
    change modifySelected i j id a = a
    exact modifySelected_id i j a

/-- After the order-preserving regrouping, a recursive child is literally
the scalar-field exchange, not the exchange of whole vectors H and D. -/
theorem repack_shortExchange (i j : I)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    repack i j (shortExchange i j a) = exchange (repack i j a) := by
  simp only [shortExchange,modifySelected,repack,Equiv.coe_fn_mk]
  simp only [splitVector_update,exchange,Prod.swap_prod_mk]
  rfl

/-- The physical child swap is exactly the selected-coordinate permutation. -/
theorem shortExchange_eq_regrouped (i j : I) :
    (repack (Prefix := Prefix) (R := R) (Gap := Gap) (Suffix := Suffix) i j).trans
      (exchangeEquiv.trans (repack i j).symm) = shortExchange i j := by
  apply Equiv.ext
  intro a
  apply (repack i j).injective
  first
  | exact (repack_shortExchange i j a).symm
  | (have h_sx := (repack_shortExchange i j a).symm; simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at h_sx ⊢; exact h_sx)
  | (have h_sx := (repack_shortExchange i j a).symm; simp only [Equiv.trans_apply,Equiv.apply_symm_apply] at h_sx; exact h_sx)
  | (simp only [Equiv.trans_apply,Equiv.apply_symm_apply]; exact (repack_shortExchange i j a).symm)

theorem shortExchange_high (i j : I)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    (shortExchange i j a).high i = a.low j := by
  simp [shortExchange,modifySelected]

theorem shortExchange_low (i j : I)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    (shortExchange i j a).low j = a.high i := by
  simp [shortExchange,modifySelected]

theorem shortExchange_other_high (i j k : I) (hk : k ≠ i)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    (shortExchange i j a).high k = a.high k := by
  simp [shortExchange,modifySelected,hk]

theorem shortExchange_other_low (i j k : I) (hk : k ≠ j)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    (shortExchange i j a).low k = a.low k := by
  simp [shortExchange,modifySelected,hk]

section Addition

variable [AddCommGroup R]

/-- Before the child: D_j ← D_j + H_i. -/
def beforeScan (i j : I) :=
  modifySelected (Prefix := Prefix) (R := R) (Gap := Gap) (Suffix := Suffix) i j lowerAdd

/-- After the child: D_j ← H_i - D_j, using the current coordinates. -/
def afterScan (i j : I) :=
  modifySelected (Prefix := Prefix) (R := R) (Gap := Gap) (Suffix := Suffix) i j lowerReflect

/-- The required elementary shear H_i ← H_i + D_j. -/
def coordinateShear (i j : I) :=
  modifySelected (Prefix := Prefix) (R := R) (Gap := Gap) (Suffix := Suffix) i j upperAdd

/-- One scalar-field recursive exchange, between its two actual scalar
updates, realizes exactly one elementary coordinate shear. -/
theorem one_short_exchange (i j : I)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    afterScan i j (shortExchange i j (beforeScan i j a)) = coordinateShear i j a := by
  change modifySelected i j lowerReflect
    (modifySelected i j Prod.swap (modifySelected i j lowerAdd a)) = _
  rw [modifySelected_comp,modifySelected_comp]
  have hop : (lowerReflect ∘ Prod.swap) ∘ lowerAdd = (upperAdd : R × R → R × R) := by
    funext x
    exact short_addition_via_exchange x
  rw [hop]
  rfl

end Addition

section Matrix

variable [Fintype I] [CommRing R]

/-- The scalar child corresponds to the actual unit-entry matrix used by
the rank-factorization program. All spectators and other coordinates remain. -/
theorem coordinateShear_eq_unitEntry (i j : I)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    coordinateShear i j a =
      mapPairEquiv (shear (MatrixFactorization.unitEntry R i j).mulVec) a := by
  cases a with
  | mk p h g d s =>
    simp only [coordinateShear,modifySelected,upperAdd,mapPairEquiv,mapPair,shear,
      Equiv.coe_fn_mk,Function.update_eq_self]
    congr 1
    funext k
    by_cases hk : k = i
    · subst k
      simp [MatrixFactorization.unitEntry_mulVec]
    · simp [Function.update_of_ne hk,MatrixFactorization.unitEntry_mulVec,hk]

/-- Complete selected-field reduction, expressed in the same matrix-shear
interface as the actual coded simulation and specialization modules. -/
theorem one_short_exchange_matrix (i j : I)
    (a : FullAddress Prefix (I → R) Gap Suffix) :
    afterScan i j (shortExchange i j (beforeScan i j a)) =
      mapPairEquiv (shear (MatrixFactorization.unitEntry R i j).mulVec) a := by
  rw [one_short_exchange,coordinateShear_eq_unitEntry]

end Matrix
end CSL.SingleCoordinate
end SingleCoordinate

section CoordinateScans
/-!
# Payload-only global scans for the scalar child's surrounding arithmetic

The stream family is shared over all prefixes. Its startup/buffer cost is
constant in the number of prefixes, rather than restarting a scan separately
for every prefix/suffix slice.
-/

set_option autoImplicit false

namespace CSL.CoordinateScans

open CSL.Address CSL.AffineStreams CSL.TagErasure
open CSL.BucketReader CSL.TriangularStreams
open CSL.SequentialArithmetic

variable {P Q G S K : ℕ} {Value : Type*}

theorem global_value_reconstruction (e : Fin P → Equiv.Perm (Fin Q))
    (key : Fin P → Fin Q → Fin K)
    (hinc : ∀ p x y, x < y → key p x = key p y → e p x < e p y)
    (F : Fin (P * (Q * S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final,
      readIndexed (Q := P * (Q * S))
        (fun y => globalKey (S := S) key ((globalFieldEquiv (S := S) e).symm y))
        (P * (Q * S)) 0 (by omega) (valueReaders (globalKey key) F B) =
        some (outputValues (globalFieldEquiv e) F,final) ∧
      valueTransfers (globalFieldEquiv e) (globalKey key) F B hB final ≤
        4 * ((P * (Q * S)) / B) + 2 * K + 2 ∧
      occupiedReaders final ≤ K * B :=
  increasing_value_reconstruction (globalFieldEquiv e) (globalKey key)
    (global_increasing_streams e key hinc) F B hB

/-- Expose the low scalar field without rearranging any coordinates:
its complete prefix is (P,H,G), and its suffix is S. -/
def lowLayout : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S) ≃
    Fin ((P * (Q * G)) * (Q * S)) where
  toFun a := tripleEncode (tripleEncode (a.prefixCoord,a.high,a.gap),a.low,a.suffix)
  invFun x :=
    let outer := tripleEncode.symm x
    let pre := tripleEncode.symm outer.1
    ⟨pre.1,pre.2.1,pre.2.2,outer.2.1,outer.2.2⟩
  left_inv a := by
    cases a
    simp only [Equiv.symm_apply_apply]
  right_inv x := by
    simp only [Prod.mk.eta,Equiv.apply_symm_apply]

@[simp] theorem lowLayout_val (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    (lowLayout a).val = a.suffix.val + S * a.low.val +
      (Q * S) * (a.gap.val + G * a.high.val + (Q * G) * a.prefixCoord.val) := rfl

@[simp] theorem additionEquiv_apply_add (c x : Fin Q) : additionEquiv c x = x + c := by
  apply Fin.ext
  rfl

section ScalarAddition

variable [NeZero Q]

def lowerAddPerm : Equiv.Perm (Fin Q × Fin Q) where
  toFun := lowerAdd
  invFun := lowerSubtract
  left_inv x := by cases x; simp [lowerAdd,lowerSubtract]
  right_inv x := by cases x; simp [lowerAdd,lowerSubtract]

/-- The offset depends only on the preceding high field, so all prefixes
share the same two quotient streams. -/
def lowOffset (p : Fin (P * (Q * G))) : Fin Q :=
  (tripleEncode.symm p).2.1

noncomputable def globalLowAdd : Equiv.Perm (Fin ((P * (Q * G)) * (Q * S))) :=
  globalFieldEquiv (fun p => additionEquiv (lowOffset p))

def globalLowAddKey : Fin ((P * (Q * G)) * (Q * S)) → Fin 2 :=
  globalKey (fun p => additionRun (lowOffset p))

/-- The same physical ordering before and after the scan realizes precisely
D←D+H, leaving P,H,G,S unchanged. -/
theorem globalLowAdd_encoded (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    globalLowAdd (lowLayout a) = lowLayout (mapPairEquiv lowerAddPerm a) := by
  change globalFieldEquiv (fun p => additionEquiv (lowOffset p))
      (tripleEncode (tripleEncode (a.prefixCoord,a.high,a.gap),a.low,a.suffix)) = _
  rw [globalFieldEquiv_encoded]
  simp only [lowOffset,Equiv.symm_apply_apply,additionEquiv_apply_add]
  rfl

/-- One global value-only two-buffer pass implements the pre-child scalar
update across every prefix, gap and suffix, with no per-slice overhead. -/
theorem before_low_value_reconstruction
    (F : Fin ((P * (Q * G)) * (Q * S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final,
      readIndexed (Q := (P * (Q * G)) * (Q * S))
        (fun y => globalLowAddKey (P := P) (Q := Q) (G := G) (S := S)
          ((globalLowAdd (P := P) (Q := Q) (G := G) (S := S)).symm y))
        ((P * (Q * G)) * (Q * S)) 0 (by omega) (valueReaders globalLowAddKey F B) =
        some (outputValues globalLowAdd F,final) ∧
      valueTransfers globalLowAdd globalLowAddKey F B hB final ≤
        4 * (((P * (Q * G)) * (Q * S)) / B) + 6 ∧
      occupiedReaders final ≤ 2 * B := by
  apply global_value_reconstruction (fun p => additionEquiv (lowOffset p))
    (fun p => additionRun (lowOffset p)) _ F B hB
  exact fun p x y hxy hr => addition_increasing_in_run (lowOffset p) x y hxy hr

/-- Reversal plus the offset H+1 is the required affine reflection H-D. -/
theorem reverse_add_offset (h d : Fin Q) : d.rev + (h + 1) = h - d := by
  have hQ : 0 < Q := NeZero.pos Q
  have hr : d.rev + d + 1 = (0 : Fin Q) := by
    apply Fin.ext
    change (((Q - (d.val + 1)) + d.val) % Q + (1 % Q)) % Q = 0
    rw [← Nat.add_mod]
    have hh : Q - (d.val + 1) + d.val + 1 = Q := by have := d.isLt; omega
    rw [hh,Nat.mod_self]
  calc
    d.rev + (h + 1) = h + (d.rev + d + 1) - d := by abel
    _ = h - d := by rw [hr]; simp

noncomputable def globalLowReverse : Equiv.Perm (Fin ((P * (Q * G)) * (Q * S))) :=
  globalFieldEquiv (fun _ => Fin.revPerm)

noncomputable def globalLowAfterAdd : Equiv.Perm (Fin ((P * (Q * G)) * (Q * S))) :=
  globalFieldEquiv (fun p => additionEquiv (lowOffset p + 1))

def globalLowAfterAddKey : Fin ((P * (Q * G)) * (Q * S)) → Fin 2 :=
  globalKey (fun p => additionRun (lowOffset p + 1))

noncomputable def globalLowReflect : Equiv.Perm (Fin ((P * (Q * G)) * (Q * S))) :=
  globalLowReverse.trans globalLowAfterAdd

def lowerReflectPerm : Equiv.Perm (Fin Q × Fin Q) where
  toFun := lowerReflect
  invFun := lowerReflect
  left_inv x := by cases x; simp [lowerReflect]
  right_inv x := by cases x; simp [lowerReflect]

/-- The post-child arithmetic is a field reversal followed by one shared
prefix-dependent addition pass, and preserves all other fields. -/
theorem globalLowReflect_encoded
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    globalLowReflect (lowLayout a) = lowLayout (mapPairEquiv lowerReflectPerm a) := by
  simp only [globalLowReflect,Equiv.trans_apply,globalLowAfterAdd,globalLowReverse,
    lowLayout,Equiv.coe_fn_mk,globalFieldEquiv_encoded,lowOffset,
    Equiv.symm_apply_apply,additionEquiv_apply_add,Fin.revPerm_apply,reverse_add_offset]
  rfl

theorem after_add_value_reconstruction
    (F : Fin ((P * (Q * G)) * (Q * S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ final,
      readIndexed (Q := (P * (Q * G)) * (Q * S))
        (fun y => globalLowAfterAddKey (P := P) (Q := Q) (G := G) (S := S)
          ((globalLowAfterAdd (P := P) (Q := Q) (G := G) (S := S)).symm y))
        ((P * (Q * G)) * (Q * S)) 0 (by omega) (valueReaders globalLowAfterAddKey F B) =
        some (outputValues globalLowAfterAdd F,final) ∧
      valueTransfers globalLowAfterAdd globalLowAfterAddKey F B hB final ≤
        4 * (((P * (Q * G)) * (Q * S)) / B) + 6 ∧
      occupiedReaders final ≤ 2 * B := by
  apply global_value_reconstruction (fun p => additionEquiv (lowOffset p + 1))
    (fun p => additionRun (lowOffset p + 1)) _ F B hB
  exact fun p x y hxy hr => addition_increasing_in_run (lowOffset p + 1) x y hxy hr

/-- The output of the actual two-pass field reversal is the input of the
following addition scan. No intermediate permutation is supplied as an oracle. -/
def afterReverseDisk (source target : BlockReflection.Disk Value)
    (B : ℕ) (hB : 0 < B) : BlockReflection.Execution Value :=
  FieldReflection.execute source target B (P * (Q * G)) Q S hB

theorem globalLowReverse_symm (y : Fin ((P * (Q * G)) * (Q * S))) :
    globalLowReverse.symm y = globalLowReverse y := by
  obtain ⟨⟨p,d,s⟩,rfl⟩ := tripleEncode.surjective y
  rfl

/-- Physical field reversal followed by the shared addition reader realizes
the full post-child operation D←H-D. The cost counts the real reversal trace
and the real value-only writer/reader transfers. -/
theorem after_low_value_reconstruction
    (source target : BlockReflection.Disk Value) (B : ℕ) (hB : 0 < B)
    (hS : 0 < S) :
    let reversed := afterReverseDisk (P := P) (Q := Q) (G := G) (S := S)
      source target B hB
    let F := fun x : Fin ((P * (Q * G)) * (Q * S)) => reversed.disk x.val
    ∃ final,
      readIndexed (fun y => globalLowAfterAddKey (P := P) (Q := Q) (G := G) (S := S)
          (globalLowAfterAdd.symm y))
        ((P * (Q * G)) * (Q * S)) 0 (by omega)
        (valueReaders globalLowAfterAddKey F B) =
        some (outputValues (globalLowReflect (P := P) (Q := Q) (G := G) (S := S))
          (fun x => source x.val), final) ∧
      reversed.trace.length +
        valueTransfers globalLowAfterAdd globalLowAfterAddKey F B hB final ≤
        10 * ((((P * (Q * G)) * (Q * S)) + B - 1) / B) +
          4 * (((P * (Q * G)) * (Q * S)) / B) + 6 ∧
      occupiedReaders final ≤ 2 * B := by
  try dsimp only
  let reversed := afterReverseDisk (P := P) (Q := Q) (G := G) (S := S)
    source target B hB
  let F := fun x : Fin ((P * (Q * G)) * (Q * S)) => reversed.disk x.val
  obtain ⟨hvalue,htrace⟩ := FieldReflection.global_field_reversal source target B
    (P * (Q * G)) Q S hB (NeZero.pos Q) hS
  obtain ⟨final,hread,hcost,hmem⟩ :=
    after_add_value_reconstruction (P := P) (Q := Q) (G := G) (S := S) F B hB
  refine ⟨final,?_,?_,hmem⟩
  · have hout : outputValues (globalLowAfterAdd (P := P) (Q := Q) (G := G) (S := S)) F =
        outputValues (globalLowReflect (P := P) (Q := Q) (G := G) (S := S))
          (fun x => source x.val) := by
      apply List.map_congr_left
      intro y _
      change reversed.disk (globalLowAfterAdd.symm y).val =
        source (globalLowReverse.symm (globalLowAfterAdd.symm y)).val
      rw [globalLowReverse_symm]
      exact hvalue _
    exact hread.trans (congrArg (fun out => some (out, final)) hout)
  · change reversed.trace.length + _ ≤ _
    change reversed.trace.length = _ at htrace
    try dsimp only [F, reversed] at hcost htrace ⊢
    omega

end ScalarAddition
end CSL.CoordinateScans
end CoordinateScans

section BinaryPadding
/-! Binary field ranges may be enlarged to a fixed-prime power. The valid
addresses form an increasing subsequence of the enlarged physical layout;
exchange preserves that set. StreamMask supplies the actual insertion and
erasure scans, including canonical output files and bounded buffers. -/

set_option autoImplicit false
namespace CSL.BinaryPadding
open Address CoordinateScans TriangularStreams
variable {P G S n m : ℕ} {Value : Type*}

abbrev Volume (P Q G S : ℕ) := (P*(Q*G))*(Q*S)
abbrev Addr (P Q G S : ℕ) := FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)

def embed (h : n ≤ m) (a : Addr P n G S) : Addr P m G S :=
  ⟨a.prefixCoord,a.high.castLE h,a.gap,a.low.castLE h,a.suffix⟩

def valid (n : ℕ) (a : Addr P m G S) : Prop := a.high.val<n ∧ a.low.val<n
instance (n : ℕ) (a : Addr P m G S) : Decidable (valid n a) :=
  inferInstanceAs (Decidable (a.high.val<n ∧ a.low.val<n))

def restrict (a : Addr P m G S) (h : valid n a) : Addr P n G S :=
  ⟨a.prefixCoord,⟨a.high.val,h.1⟩,a.gap,⟨a.low.val,h.2⟩,a.suffix⟩

@[simp] theorem valid_embed (h : n ≤ m) (a : Addr P n G S) : valid n (embed h a) :=
  ⟨a.high.isLt,a.low.isLt⟩

@[simp] theorem restrict_embed (h : n ≤ m) (a : Addr P n G S) :
    restrict (embed h a) (valid_embed h a) = a := by cases a; rfl

@[simp] theorem embed_restrict (h : n ≤ m) (a : Addr P m G S) (ha : valid n a) :
    embed h (restrict a ha) = a := by cases a; rfl

@[simp] theorem embed_exchange (h : n ≤ m) (a : Addr P n G S) :
    embed h (exchange a) = exchange (embed h a) := rfl

@[simp] theorem valid_exchange (a : Addr P m G S) :
    valid n (exchange a) ↔ valid n a := by simp [valid,exchange,and_comm]

def pad (h : n ≤ m) (padding : Value) (F : Addr P n G S → Value) :
    Addr P m G S → Value :=
  fun a => if ha : valid n a then F (restrict a ha) else padding

@[simp] theorem pad_embed (h : n ≤ m) (padding : Value)
    (F : Addr P n G S → Value) (a : Addr P n G S) :
    pad h padding F (embed h a) = F a := by simp [pad]

/-- Padding, actual full-field exchange, and restriction move exactly the
original values. Padding never becomes an ordinary output value. -/
theorem exchange_after_padding (h : n ≤ m) (padding : Value)
    (F : Addr P n G S → Value) (a : Addr P n G S) :
    transport exchangeEquiv (pad h padding F) (embed h a) =
      transport exchangeEquiv F a := by
  change pad h padding F (exchange (embed h a)) = F (exchange a)
  rw [← embed_exchange,pad_embed]

def physicalEmbed (h : n ≤ m) : Fin (Volume P n G S) → Fin (Volume P m G S) :=
  fun x => lowLayout (embed h (lowLayout.symm x))

theorem embed_order (h : n ≤ m) (a b : Addr P n G S) :
    lowLayout (embed h a) < lowLayout (embed h b) ↔ lowLayout a < lowLayout b := by
  change tripleEncode (tripleEncode ((embed h a).prefixCoord,(embed h a).high,(embed h a).gap),
      (embed h a).low,(embed h a).suffix) <
    tripleEncode (tripleEncode ((embed h b).prefixCoord,(embed h b).high,(embed h b).gap),
      (embed h b).low,(embed h b).suffix) ↔
    tripleEncode (tripleEncode (a.prefixCoord,a.high,a.gap),a.low,a.suffix) <
    tripleEncode (tripleEncode (b.prefixCoord,b.high,b.gap),b.low,b.suffix)
  simp only [tripleEncode_lt_iff,embed,Equiv.apply_eq_iff_eq,Prod.mk.injEq]
  simp

theorem physicalEmbed_strictMono (h : n ≤ m) :
    StrictMono (physicalEmbed (P:=P) (G:=G) (S:=S) h) := by
  intro a b hab
  unfold physicalEmbed
  rw [embed_order]
  simpa only [Equiv.apply_symm_apply] using hab

theorem physicalEmbed_range (h : n ≤ m) (y : Fin (Volume P m G S)) :
    (∃ x, physicalEmbed (P:=P) (G:=G) (S:=S) h x = y) ↔ valid n (lowLayout.symm y) := by
  constructor
  · rintro ⟨x,rfl⟩
    simpa [physicalEmbed] using valid_embed h (lowLayout.symm x : Addr P n G S)
  · intro hv
    refine ⟨lowLayout (restrict (lowLayout.symm y) hv),?_⟩
    simp [physicalEmbed]

/-- The compact order is the valid subsequence of the enlarged order.
Thus insertion/erasure are scans; no hidden permutation is required. -/
theorem physical_sequence (h : n ≤ m) :
    (List.finRange (Volume P m G S)).filter
      (fun y => decide (valid n (lowLayout.symm y : Addr P m G S))) =
    (List.finRange (Volume P n G S)).map (physicalEmbed h) := by
  have hs : List.Sorted (· < ·)
      ((List.finRange (Volume P n G S)).map (physicalEmbed (P:=P) (G:=G) (S:=S) h)) := by
    rw [List.Sorted,List.pairwise_map]
    exact (List.pairwise_lt_finRange _).imp (fun hxy => physicalEmbed_strictMono h hxy)
  apply List.Sorted.eq_of_mem_iff
    ((List.pairwise_lt_finRange _).filter _) hs
  intro y
  simp only [List.mem_filter,List.mem_finRange,true_and,decide_eq_true_eq,List.mem_map]
  simpa only [List.mem_finRange,true_and] using (physicalEmbed_range h y).symm

def exponent (q u : ℕ) := Nat.clog q (2^u)

theorem binary_range_fits (q u : ℕ) (hq : 1<q) : 2^u ≤ q^(exponent q u) :=
  Nat.le_pow_clog hq _

theorem binary_width_bound (q u : ℕ) (hq : 1<q) : exponent q u ≤ u := by
  apply (Nat.le_pow_iff_clog_le hq).mp
  exact Nat.pow_le_pow_left (by omega) u

theorem binary_range_growth (q u : ℕ) (hq : 1<q) : q^(exponent q u) < q*2^u := by
  by_cases hu : u=0
  · subst u
    simp [exponent,hq]
  · have htwo : 1<2^u := by
      exact one_lt_pow₀ (by norm_num) (by omega)
    have he : 0 < exponent q u := Nat.clog_pos hq (by omega)
    have h := Nat.pow_pred_clog_lt_self hq htwo
    have hm := Nat.mul_lt_mul_of_pos_left h (show 0<q by omega)
    have hp : q^(exponent q u) = q*q^((exponent q u)-1) := by
      rw [← pow_succ',Nat.sub_add_cancel (by omega)]
    change q*q^((exponent q u)-1) < q*2^u at hm
    rw [← hp] at hm
    exact hm

/-- The scan volume grows by less than q², uniformly in the input width. -/
theorem binary_volume_growth (P G S q u : ℕ) (hq : 1<q)
    (hP : 0<P) (hG : 0<G) (hS : 0<S) :
    Volume P (q^(exponent q u)) G S < q^2 * Volume P (2^u) G S := by
  have h := binary_range_growth q u hq
  have hsquare : (q^(exponent q u))^2 < (q*2^u)^2 := Nat.pow_lt_pow_left h (by omega)
  have hmult := Nat.mul_lt_mul_of_pos_left hsquare
    (Nat.mul_pos (Nat.mul_pos hP hG) hS)
  try dsimp [Volume]
  nlinarith only [hmult]

end CSL.BinaryPadding
end BinaryPadding

section ScalarCoordinateProgram
/-! Actual programs surrounding one recursive scalar-coordinate exchange.
The two programs cost fixed constants 10 and 20, independently of prefixes,
gaps, suffixes and the modulus. -/

namespace CSL.ScalarCoordinateProgram

open Address CoordinateScans TriangularStreams SequentialArithmetic AffineStreams
open ScanProgram ScanProgramLift

variable {P Q G S : ℕ} [NeZero Q]

noncomputable def before : List (Pass ((P*(Q*G))*(Q*S))) :=
  [.streams 2 globalLowAdd globalLowAddKey
    (global_increasing_streams (fun p => additionEquiv (lowOffset p))
      (fun p => additionRun (lowOffset p))
      (fun p x y hxy hr => addition_increasing_in_run (lowOffset p) x y hxy hr))]

noncomputable def after (hS : 0 < S) : List (Pass ((P*(Q*G))*(Q*S))) :=
  fieldReflections (P*(Q*G)) Q S (NeZero.pos Q) hS rfl ++
    [.streams 2 globalLowAfterAdd globalLowAfterAddKey
      (global_increasing_streams (fun p => additionEquiv (lowOffset p+1))
        (fun p => additionRun (lowOffset p+1))
        (fun p x y hxy hr => addition_increasing_in_run (lowOffset p+1) x y hxy hr))]

@[simp] theorem before_destination :
    destination (before (P := P) (Q := Q) (G := G) (S := S)) = globalLowAdd := rfl

theorem after_destination (hS : 0 < S) :
    destination (after (P := P) (Q := Q) (G := G) hS) = globalLowReflect := by
  rw [after,ScanProgramLift.destination_append]
  apply Equiv.ext
  intro y
  change (globalLowAfterAdd : Equiv.Perm (Fin ((P*(Q*G))*(Q*S))))
      (destination (fieldReflections (P*(Q*G)) Q S (NeZero.pos Q) hS rfl) y) = _
  have h := fieldReflections_destination (P*(Q*G)) Q S (NeZero.pos Q) hS rfl y
  change destination (fieldReflections (P*(Q*G)) Q S (NeZero.pos Q) hS rfl) y =
    globalLowReverse y at h
  rw [h]
  rfl

/-- Before the child exchange: D is replaced by D+H. -/
theorem before_encoded (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    destination before (lowLayout a) = lowLayout (mapPairEquiv lowerAddPerm a) :=
  globalLowAdd_encoded a

/-- After the child exchange: D is replaced by H-D. -/
theorem after_encoded (hS : 0 < S)
    (a : FullAddress (Fin P) (Fin Q) (Fin G) (Fin S)) :
    destination (after hS) (lowLayout a) = lowLayout (mapPairEquiv lowerReflectPerm a) := by
  rw [after_destination]
  exact globalLowReflect_encoded a

@[simp] theorem before_constant :
    totalConstant (before (P := P) (Q := Q) (G := G) (S := S)) = 10 := rfl

@[simp] theorem after_constant (hS : 0 < S) :
    totalConstant (after (P := P) (Q := Q) (G := G) hS) = 20 := rfl

theorem before_execution {Value : Type*} [Inhabited Value]
    (input : Fin ((P*(Q*G))*(Q*S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB before input cost ∧
      cost ≤ 10*(((P*(Q*G))*(Q*S))/B+1) := by
  simpa only [before_constant] using program_correct before input B hB

theorem after_execution {Value : Type*} [Inhabited Value] (hS : 0 < S)
    (input : Fin ((P*(Q*G))*(Q*S)) → Value) (B : ℕ) (hB : 0 < B) :
    ∃ cost, Execution B hB (after hS) input cost ∧
      cost ≤ 20*(((P*(Q*G))*(Q*S))/B+1) := by
  simpa only [after_constant] using program_correct (after hS) input B hB

theorem before_buffers (p : Pass ((P*(Q*G))*(Q*S))) (hp : p ∈ before) (B : ℕ) :
    p.buffers*B ≤ 10*B := by
  apply Nat.mul_le_mul_right B
  simpa only [before_constant] using member_buffers_le_total before p hp

theorem after_buffers (hS : 0 < S) (p : Pass ((P*(Q*G))*(Q*S)))
    (hp : p ∈ after hS) (B : ℕ) : p.buffers*B ≤ 20*B := by
  apply Nat.mul_le_mul_right B
  simpa only [after_constant] using member_buffers_le_total (after hS) p hp

end CSL.ScalarCoordinateProgram
end ScalarCoordinateProgram

section BinaryPaddingScan
/-! The binary padding reduction connected to the actual Reader/Writer
machines. These scans consume the previous physical file and return a
canonical next file; the exchange algorithm can run between the two scans. -/

set_option autoImplicit false
namespace CSL.BinaryPaddingScan
open BinaryPadding Address CoordinateScans StreamMask BucketMachine BucketReader StreamCopy
variable {P G S n m Q : ℕ} {Value : Type*}

def extendNat (fallback : Value) (F : Fin Q → Value) (i : ℕ) : Value :=
  if hi : i<Q then F ⟨i,hi⟩ else fallback

def maskNat (keep : Fin Q → Bool) (i : ℕ) : Bool :=
  if hi : i<Q then keep ⟨i,hi⟩ else false

@[simp] theorem extendNat_at (fallback : Value) (F : Fin Q → Value) (i : Fin Q) :
    extendNat fallback F i.val = F i := by simp [extendNat,i.isLt]

@[simp] theorem maskNat_at (keep : Fin Q → Bool) (i : Fin Q) :
    maskNat keep i.val = keep i := by simp [maskNat,i.isLt]

theorem finite_positions : positions Q 0 = (List.finRange Q).map Fin.val := by
  simp [positions,List.map_coe_finRange,List.range_eq_range']

theorem finite_values (fallback : Value) (F : Fin Q → Value) :
    (positions Q 0).map (extendNat fallback F) = (List.finRange Q).map F := by
  rw [finite_positions,List.map_map]
  simp only [Function.comp_def,extendNat_at]

theorem finite_kept (fallback : Value) (keep : Fin Q → Bool) (F : Fin Q → Value) :
    kept (maskNat keep) (extendNat fallback F) Q 0 =
      ((List.finRange Q).filter keep).map F := by
  rw [kept,finite_positions,List.filter_map,List.map_map]
  simp only [Function.comp_def,maskNat_at,extendNat_at]

def keep (n : ℕ) (y : Fin (Volume P m G S)) : Bool :=
  decide (valid n (lowLayout.symm y : Addr P m G S))

def expanded (h : n≤m) (padding : Value) (F : Fin (Volume P n G S) → Value) :
    Fin (Volume P m G S) → Value :=
  fun y => pad h padding (fun a => F (lowLayout a)) (lowLayout.symm y)

theorem expanded_at (h : n≤m) (padding : Value)
    (F : Fin (Volume P n G S) → Value) (y : Fin (Volume P n G S)) :
    expanded h padding F (physicalEmbed h y) = F y := by
  simp [expanded,physicalEmbed]

theorem expanded_invalid (h : n≤m) (padding : Value)
    (F : Fin (Volume P n G S) → Value) (y : Fin (Volume P m G S))
    (hy : keep (P:=P) (m:=m) (G:=G) (S:=S) n y = false) : expanded h padding F y = padding := by
  have hn : ¬ valid n (lowLayout.symm y : Addr P m G S) := by simpa [keep] using hy
  simp [expanded,pad,hn]

theorem compact_sequence (h : n≤m) (padding : Value)
    (F : Fin (Volume P n G S) → Value) :
    kept (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) (extendNat padding (expanded h padding F))
      (Volume P m G S) 0 = (List.finRange (Volume P n G S)).map F := by
  rw [finite_kept]
  change ((List.finRange _).filter (fun y => decide (valid n (lowLayout.symm y)))).map _ = _
  rw [physical_sequence h,List.map_map]
  simp only [Function.comp_def,expanded_at]

theorem expanded_sequence (h : n≤m) (padding : Value)
    (F : Fin (Volume P n G S) → Value) :
    padded (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) padding (extendNat padding (expanded h padding F))
      (Volume P m G S) 0 =
        (List.finRange (Volume P m G S)).map (expanded h padding F) := by
  rw [padded,finite_positions,List.map_map]
  apply List.map_congr_left
  intro y _
  simp only [Function.comp_def,maskNat_at,extendNat_at]
  cases hy : keep (P:=P) (m:=m) (G:=G) (S:=S) n y with
  | true => simp
  | false => simp only [Bool.false_eq_true,↓reduceIte]; exact (expanded_invalid h padding F y hy).symm

/-- One input scan plus one enlarged-output scan, with two payload buffers. -/
theorem insert_physical (h : n≤m) (padding : Value) (B : ℕ) (hB : 0<B)
    (F : Fin (Volume P n G S) → Value) (file : List (List Value))
    (hv : (Reader.fromDisk file).Valid B)
    (hf : file.flatten = (List.finRange (Volume P n G S)).map F) :
    ∃ t, insert (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) padding B (Volume P m G S) 0
        ⟨Reader.fromDisk file,Writer.empty⟩ = some t ∧
      t.target.finish = pack B hB
        ((List.finRange (Volume P m G S)).map (expanded h padding F)) ∧
      t.source.reads+t.target.finish.length = file.length+(Volume P m G S+B-1)/B ∧
      t.Valid B ∧ t.memory≤2*B := by
  obtain ⟨t,ht,hvalid,hout,hcost,hmem⟩ := insert_file (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) padding B
    (Volume P m G S) hB (extendNat padding (expanded h padding F)) file hv
    (by rw [compact_sequence h padding F]; exact hf)
  exact ⟨t,ht,by rwa [expanded_sequence] at hout,hcost,hvalid,hmem⟩

/-- Restriction of an arbitrary full-field result is a real erase scan.
The caller may use this for the output of the independently verified
exchange program; invalid locations need not contain zero. -/
theorem erase_physical (h : n≤m) (fallback : Value) (B : ℕ) (hB : 0<B)
    (F : Fin (Volume P m G S) → Value) (file : List (List Value))
    (hv : (Reader.fromDisk file).Valid B)
    (hf : file.flatten = (List.finRange (Volume P m G S)).map F) :
    ∃ t, erase (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) B (Volume P m G S) 0
        ⟨Reader.fromDisk file,Writer.empty⟩ = some t ∧
      t.target.finish = pack B hB
        ((List.finRange (Volume P n G S)).map (fun y => F (physicalEmbed h y))) ∧
      t.source.reads+t.target.finish.length = file.length+(Volume P n G S+B-1)/B ∧
      t.Valid B ∧ t.memory≤2*B := by
  have hseq : kept (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) (extendNat fallback F) (Volume P m G S) 0 =
      (List.finRange (Volume P n G S)).map (fun y => F (physicalEmbed h y)) := by
    rw [finite_kept]
    change ((List.finRange _).filter (fun y => decide (valid n (lowLayout.symm y)))).map _ = _
    rw [physical_sequence h,List.map_map]
    rfl
  obtain ⟨t,ht,hvalid,hout,hcost,hmem⟩ := erase_file (maskNat (keep (P:=P) (m:=m) (G:=G) (S:=S) n)) B
    (Volume P m G S) hB (extendNat fallback F) file hv (by rw [finite_values]; exact hf)
  refine ⟨t,ht,by rwa [hseq] at hout,?_,hvalid,hmem⟩
  simpa only [hseq,List.length_map,List.length_finRange] using hcost

end CSL.BinaryPaddingScan
end BinaryPaddingScan


