-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Fields_ScalarLayoutBridge
-- name    : CSL_Interchange_Framework_Fields_ScalarLayoutBridge
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T15:22:01.400585+00:00
-- url     : https://prove2.me/theorems/8e29948c-7e59-4a35-96e0-ce5c751ceba0
-- title:
--   Coded sorting library: Interchange / Framework / Fields / ScalarLayoutBridge
-- statement:
--   Module `CodedSorting.Interchange.Framework.Fields.ScalarLayoutBridge` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   The four actual triangular disk programs use the same physical address
--   encoding as the selected-coordinate recursive scans.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Fields.ScalarLayoutBridge

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Recursion_RecursiveExchangeCost
import Definitions.Def_CSL_Interchange_Framework_Memory_AddressLayout

section CoordinateLayoutBridge
/-! The four actual triangular disk programs use the same physical address
encoding as the selected-coordinate recursive scans. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CSL.CoordinateLayoutBridge
open RecursiveExchange RecursiveExchangeCost TriangularStreams
open ScanProgram Address
noncomputable section

section Enumeration
variable {I : Type*} [Fintype I] [LinearOrder I] [WellFoundedLT I]
variable {m Q : ℕ}

/-- An increasing enumeration only renames digits; it does not permute their
physical lexicographic ranks. -/
theorem enumeration_code_val (e : Fin m ≃o I) (x : I → Fin Q) :
    (lexLayout (fun i => x (e i))).val = (LexBlocks.subvectorEncode x).val := by
  have hcard : Fintype.card I = m := by
    simpa only [Fintype.card_fin] using Fintype.card_congr e.symm.toEquiv
  let code : (I → Fin Q) ≃ Fin (Q^m) :=
    (Equiv.arrowCongr e.symm.toEquiv (Equiv.refl (Fin Q))).trans lexLayout
  let compare : Equiv.Perm (Fin (Q^m)) :=
    (finCongr (congrArg (fun n => Q^n) hcard)).symm.trans
      (LexBlocks.subvectorEncode.symm.trans code)
  have hi : StrictMono compare := by
    intro a b hab
    change lexLayout (fun i => LexBlocks.subvectorEncode.symm
        ((finCongr (congrArg (fun n => Q^n) hcard)).symm a) (e i)) <
      lexLayout (fun i => LexBlocks.subvectorEncode.symm
        ((finCongr (congrArg (fun n => Q^n) hcard)).symm b) (e i))
    apply (lexLayout_lt _ _).mpr
    have hxy : Pi.Lex (· < ·) (· < ·)
        (LexBlocks.subvectorEncode.symm
          ((finCongr (congrArg (fun n => Q^n) hcard)).symm a))
        (LexBlocks.subvectorEncode.symm
          ((finCongr (congrArg (fun n => Q^n) hcard)).symm b)) := by
      apply (LexBlocks.subvectorEncode_lt _ _).mp
      first
      | exact hab
      | (have h_sx := hab; simp only [Equiv.apply_symm_apply] at h_sx ⊢; exact h_sx)
      | (have h_sx := hab; simp only [Equiv.apply_symm_apply] at h_sx; exact h_sx)
      | (simp only [Equiv.apply_symm_apply]; exact hab)
    obtain ⟨j,hpre,hj⟩ := hxy
    refine ⟨e.symm j,?_,?_⟩
    · intro k hk
      exact hpre (e k) ((e.lt_symm_apply).mp hk)
    · simpa only [OrderIso.apply_symm_apply] using hj
  have he : (compare : Fin (Q^m) → Fin (Q^m)) = id :=
    (hi.range_inj strictMono_id).mp (by simp only [Equiv.range_eq_univ,Set.range_id])
  have hp := congrFun he ((finCongr (congrArg (fun n => Q^n) hcard))
    (LexBlocks.subvectorEncode x))
  try dsimp only [compare,code] at hp
  simp only [Equiv.trans_apply,Equiv.symm_apply_apply] at hp
  change lexLayout (fun i => x (e i)) =
    finCongr (congrArg (fun n => Q^n) hcard) (LexBlocks.subvectorEncode x) at hp
  exact congrArg Fin.val hp

end Enumeration

local instance : LinearOrder Index := RecursiveExchange.indexOrder
local instance : LE Index := RecursiveExchange.indexOrder.toLE
local instance : LT Index := RecursiveExchange.indexOrder.toLT
local instance : WellFoundedLT Index :=
  @Finite.to_wellFoundedLT Index inferInstance RecursiveExchange.indexOrder.toPreorder

def digitVector (f : ℕ) : Field f ≃ (Index → Fin (radix^f)) :=
  Equiv.arrowCongr (Equiv.refl Index) (ZMod.finEquiv (radix^f)).symm.toEquiv

theorem field_code_val (f : ℕ) (x : Field f) :
    (lexLayout (fieldVector f x)).val = (LexBlocks.subvectorEncode (digitVector f x)).val :=
  enumeration_code_val indexEnumeration (digitVector f x)

theorem volume_eq (f P G S : ℕ) :
    CommonAddressLayout.Volume Index P (radix^f) G S = longVolume f P G S := by
  simp only [CommonAddressLayout.Volume,CommonAddressLayout.FieldCount,
    StageLabels.actual_matrix_card,longVolume]
  ring

def commonLayout (f P G S : ℕ) :
    LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f ≃
      Fin (longVolume f P G S) :=
  (CommonAddressLayout.shape (Equiv.refl _) (digitVector f)
    (Equiv.refl _) (Equiv.refl _)).trans
      (CommonAddressLayout.longLayout.trans (finCongr (volume_eq f P G S)))

theorem commonLayout_apply (f P G S : ℕ)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    commonLayout f P G S a = finCongr (volume_eq f P G S)
      (CommonAddressLayout.longLayout (CommonAddressLayout.shape (Equiv.refl _)
        (digitVector f) (Equiv.refl _) (Equiv.refl _) a)) := rfl

theorem commonLayout_val (f P G S : ℕ)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    (commonLayout f P G S a).val =
      a.suffix.val+S*(lexLayout (fieldVector f a.low)).val+
      ((radix^f)^Parameters.m*S)*(a.gap.val+
        G*(lexLayout (fieldVector f a.high)).val+
        ((radix^f)^Parameters.m*G)*a.prefixCoord.val) := by
  calc
    _ = a.suffix.val+S*(LexBlocks.subvectorEncode (digitVector f a.low)).val+
        ((radix^f)^Fintype.card Index*S)*(a.gap.val+
          G*(LexBlocks.subvectorEncode (digitVector f a.high)).val+
          ((radix^f)^Fintype.card Index*G)*a.prefixCoord.val) :=
      (congrArg Fin.val (commonLayout_apply f P G S a)).trans
        ((finCongr_apply_coe (volume_eq f P G S) _).trans
          (CommonAddressLayout.longLayout_val
            (CommonAddressLayout.shape (Equiv.refl _) (digitVector f)
              (Equiv.refl _) (Equiv.refl _) a)))
    _ = _ := by
      rw [← field_code_val f a.low,← field_code_val f a.high,StageLabels.actual_matrix_card]

theorem commonLayout_high (f P G S : ℕ)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    commonLayout f P G S a = tripleEncode
      (a.prefixCoord,lexLayout (fieldVector f a.high),
        tripleEncode (a.gap,lexLayout (fieldVector f a.low),a.suffix)) := by
  apply Fin.ext
  rw [commonLayout_val]
  simp only [tripleEncode_val]
  ring

theorem lowVolume_eq (f P G S : ℕ) :
    (P*((radix^f)^Parameters.m*G))*((radix^f)^Parameters.m*S) =
      longVolume f P G S := by unfold longVolume; ring

theorem commonLayout_low (f P G S : ℕ)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    commonLayout f P G S a = finCongr (lowVolume_eq f P G S)
      (tripleEncode (tripleEncode (a.prefixCoord,lexLayout (fieldVector f a.high),a.gap),
        lexLayout (fieldVector f a.low),a.suffix)) := by
  apply Fin.ext
  rw [commonLayout_val]
  rfl

theorem castProgram_destination {V W : ℕ} (h : V = W)
    (ps : List (Pass V)) (x : Fin V) :
    destination (castProgram h ps) (finCongr h x) = finCongr h (destination ps x) := by
  subst W
  rfl

/-- The factor changes exactly one whole address field; spectators retain
their literal physical digit order. -/
def factorAddress (f : ℕ) (e : Edge) (which : Factor) {P G S : ℕ}
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f :=
  match which with
  | .left | .leftInverse =>
    FullAddress.mk a.prefixCoord ((factorMatrix f e which).mulVec a.high) a.gap a.low a.suffix
  | .right | .rightInverse =>
    FullAddress.mk a.prefixCoord a.high a.gap ((factorMatrix f e which).mulVec a.low) a.suffix

theorem coordinate_destination (f : ℕ) (e : Edge) (which : Factor)
    (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    destination (coordinateProgram f e which P G S hG hS) (commonLayout f P G S a) =
      commonLayout f P G S (factorAddress f e which a) := by
  cases which with
  | left =>
    rw [commonLayout_high,commonLayout_high]
    exact factorProgram_destination f e .left P _ _ a.prefixCoord a.high
      (tripleEncode (a.gap,lexLayout (fieldVector f a.low),a.suffix))
  | leftInverse =>
    rw [commonLayout_high,commonLayout_high]
    exact factorProgram_destination f e .leftInverse P _ _ a.prefixCoord a.high
      (tripleEncode (a.gap,lexLayout (fieldVector f a.low),a.suffix))
  | right =>
    rw [commonLayout_low,commonLayout_low]
    change destination (castProgram (lowVolume_eq f P G S)
      (factorProgram f e .right (P*((radix^f)^Parameters.m*G)) S hS)) _ = _
    rw [castProgram_destination,factorProgram_destination]
    rfl
  | rightInverse =>
    rw [commonLayout_low,commonLayout_low]
    change destination (castProgram (lowVolume_eq f P G S)
      (factorProgram f e .rightInverse (P*((radix^f)^Parameters.m*G)) S hS)) _ = _
    rw [castProgram_destination,factorProgram_destination]
    rfl

def beforeProgram (f : ℕ) (e : Edge) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :=
  coordinateProgram f e .leftInverse P G S hG hS ++ coordinateProgram f e .right P G S hG hS

def afterProgram (f : ℕ) (e : Edge) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S) :=
  coordinateProgram f e .left P G S hG hS ++ coordinateProgram f e .rightInverse P G S hG hS

theorem destination_append {V : ℕ} (xs ys : List (Pass V)) :
    destination (xs++ys) = (destination xs).trans (destination ys) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.cons_append,destination,ih]
    rfl

theorem before_destination (f : ℕ) (e : Edge) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    destination (beforeProgram f e P G S hG hS) (commonLayout f P G S a) =
      commonLayout f P G S (coordinatePermutation f e a) := by
  rw [beforeProgram,destination_append,Equiv.trans_apply,coordinate_destination,coordinate_destination]
  rfl

theorem after_destination (f : ℕ) (e : Edge) (P G S : ℕ) (hG : 0 < G) (hS : 0 < S)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    destination (afterProgram f e P G S hG hS) (commonLayout f P G S a) =
      commonLayout f P G S ((coordinatePermutation f e).symm a) := by
  rw [afterProgram,destination_append,Equiv.trans_apply,coordinate_destination,coordinate_destination]
  rfl

end
end CSL.CoordinateLayoutBridge
end CoordinateLayoutBridge

section ScalarLayoutBridge
/-! The actual jointly specialized network's scalar scans use the same
physical file layout as its triangular factors. All conversions below are
coordinate encodings or equal-length Fin casts, with no disk permutation. -/

set_option autoImplicit false
set_option maxRecDepth 4096
namespace CSL.ScalarLayoutBridge
open Address RecursiveExchange RecursiveExchangeCost CoordinateLayoutBridge
open CommonAddressLayout SingleCoordinate ScanProgram CoordinateScans
noncomputable section

local instance : LinearOrder Index := RecursiveExchange.indexOrder
local instance : LE Index := RecursiveExchange.indexOrder.toLE
local instance : LT Index := RecursiveExchange.indexOrder.toLT
local instance : WellFoundedLT Index :=
  @Finite.to_wellFoundedLT Index inferInstance RecursiveExchange.indexOrder.toPreorder

/-- The same residue-to-Fin map is used for scalar and vector fields. -/
def digit (f : ℕ) : Scalar f ≃ Fin (radix^f) := (ZMod.finEquiv (radix^f)).symm.toEquiv

def digits (f : ℕ) (J : Type*) : (J → Scalar f) ≃ (J → Fin (radix^f)) :=
  Equiv.arrowCongr (Equiv.refl _) (digit f)

theorem childP_eq (f P : ℕ) (c : Child) :
    childP f P c = CommonAddressLayout.ChildPrefix P (radix^f) (childRow c) := by
  simp only [childP,RecursiveExchangeCost.ChildPrefix,ShortPrefix,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_fun,short_field_card,
    CommonAddressLayout.ChildPrefix,BeforeCount]

theorem childG_eq (f G : ℕ) (c : Child) :
    childG f G c = CommonAddressLayout.ChildGap G (radix^f) (childRow c) (childCol c) := by
  simp only [childG,RecursiveExchangeCost.ChildGap,ShortGap,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_fun,short_field_card,
    CommonAddressLayout.ChildGap,BeforeCount,AfterCount]

theorem childS_eq (f S : ℕ) (c : Child) :
    childS f S c = CommonAddressLayout.ChildSuffix S (radix^f) (childCol c) := by
  simp only [childS,RecursiveExchangeCost.ChildSuffix,ShortSuffix,Fintype.card_prod,
    Fintype.card_fin,Fintype.card_fun,short_field_card,
    CommonAddressLayout.ChildSuffix,AfterCount]

def prefixDigits (f P : ℕ) (c : Child) :=
  Equiv.prodCongr (Equiv.refl (Fin P)) (digits f (Before (childRow c)))

def gapDigits (f G : ℕ) (c : Child) :=
  Equiv.prodCongr (digits f (After (childRow c)))
    (Equiv.prodCongr (Equiv.refl (Fin G)) (digits f (Before (childCol c))))

def suffixDigits (f S : ℕ) (c : Child) :=
  Equiv.prodCongr (digits f (After (childCol c))) (Equiv.refl (Fin S))

def prefixCode (f P : ℕ) (c : Child) : RecursiveExchangeCost.ChildPrefix f P c ≃ Fin (childP f P c) :=
  (prefixDigits f P c).trans ((CommonAddressLayout.prefixEncoding (Q := radix^f) (childRow c)).trans
    (finCongr (childP_eq f P c).symm))

def gapCode (f G : ℕ) (c : Child) : RecursiveExchangeCost.ChildGap f G c ≃ Fin (childG f G c) :=
  (gapDigits f G c).trans ((CommonAddressLayout.gapEncoding (Q := radix^f) (childRow c) (childCol c)).trans
    (finCongr (childG_eq f G c).symm))

def suffixCode (f S : ℕ) (c : Child) : RecursiveExchangeCost.ChildSuffix f S c ≃ Fin (childS f S c) :=
  (suffixDigits f S c).trans ((CommonAddressLayout.suffixEncoding (Q := radix^f) (childCol c)).trans
    (finCongr (childS_eq f S c).symm))

abbrev ChildAddress (f P G S : ℕ) (c : Child) :=
  FullAddress (RecursiveExchangeCost.ChildPrefix f P c) (Scalar f)
    (RecursiveExchangeCost.ChildGap f G c) (RecursiveExchangeCost.ChildSuffix f S c)

def childCodec (f P G S : ℕ) (c : Child) : ChildAddress f P G S c ≃
    FullAddress (Fin (childP f P c)) (Fin (radix^f)) (Fin (childG f G c)) (Fin (childS f S c)) :=
  CommonAddressLayout.shape (prefixCode f P c) (digit f) (gapCode f G c) (suffixCode f S c)

def childLayout (f P G S : ℕ) (c : Child) : ChildAddress f P G S c ≃
    Fin ((childP f P c*(radix^f*childG f G c))*(radix^f*childS f S c)) :=
  (childCodec f P G S c).trans lowLayout

def childDigits (f P G S : ℕ) (c : Child) :=
  CommonAddressLayout.shape (prefixDigits f P c) (digit f) (gapDigits f G c) (suffixDigits f S c)

theorem childLayout_val (f P G S : ℕ) (c : Child) (a : ChildAddress f P G S c) :
    (childLayout f P G S c a).val =
      (CommonAddressLayout.childLayout (childRow c) (childCol c) (childDigits f P G S c a)).val := by
  simp only [childLayout,childCodec,Equiv.trans_apply,lowLayout_val,
    CommonAddressLayout.childLayout,CommonAddressLayout.shape,Equiv.coe_fn_mk,
    childDigits,Equiv.refl_apply,prefixCode,gapCode,suffixCode,finCongr_apply_coe]
  rw [childG_eq,childS_eq]

theorem repack_digits (f P G S : ℕ) (c : Child)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    childDigits f P G S c (childRepack f c a) =
      repack (childRow c) (childCol c)
        (CommonAddressLayout.shape (Equiv.refl _) (digitVector f) (Equiv.refl _) (Equiv.refl _) a) := by
  rfl

/-- Literal equality of linear file addresses on entry to every scalar child. -/
theorem child_common (f P G S : ℕ) (c : Child)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    finCongr (child_volume f P G S c) (childLayout f P G S c (childRepack f c a)) =
      commonLayout f P G S a := by
  apply Fin.ext
  rw [finCongr_apply_coe,childLayout_val,repack_digits]
  rw [CommonAddressLayout.childLayout_repack_val]
  rw [commonLayout_apply,finCongr_apply_coe]

/-- Scalar encodings preserve the actual modular addition on the edge field. -/
theorem before_encoded (f P G S : ℕ) (c : Child)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    childCodec f P G S c (childRepack f c (beforeScan (childRow c) (childCol c) a)) =
      mapPairEquiv lowerAddPerm (childCodec f P G S c (childRepack f c a)) := by
  simp only [beforeScan,childRepack,repack,modifySelected,splitVector_update,
    childCodec,CommonAddressLayout.shape,Equiv.coe_fn_mk,mapPairEquiv,mapPair,lowerAddPerm,lowerAdd]
  congr 1
  exact map_add (ZMod.finEquiv (radix^f)).symm _ _

/-- The reflected subtraction uses the same residue map and same spectators. -/
theorem after_encoded (f P G S : ℕ) (c : Child)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    childCodec f P G S c (childRepack f c (afterScan (childRow c) (childCol c) a)) =
      mapPairEquiv lowerReflectPerm (childCodec f P G S c (childRepack f c a)) := by
  simp only [afterScan,childRepack,repack,modifySelected,splitVector_update,
    childCodec,CommonAddressLayout.shape,Equiv.coe_fn_mk,mapPairEquiv,mapPair,lowerReflectPerm,lowerReflect]
  congr 1
  exact map_sub (ZMod.finEquiv (radix^f)).symm _ _

/-- The actual pre-child program has the required address action in the
same common file layout used by all four triangular factor programs. -/
theorem scalar_before_destination (f P G S : ℕ) (c : Child)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    destination (scalarBefore f P G S c) (commonLayout f P G S a) =
      commonLayout f P G S (beforeScan (childRow c) (childCol c) a) := by
  rw [← child_common f P G S c a,scalarBefore,castProgram_destination]
  have he := ScalarCoordinateProgram.before_encoded (childCodec f P G S c (childRepack f c a))
  change destination (ScalarCoordinateProgram.before (P := childP f P c) (Q := radix^f)
    (G := childG f G c) (S := childS f S c)) (childLayout f P G S c (childRepack f c a)) = _ at he
  rw [he,← before_encoded]
  exact child_common f P G S c _

theorem scalar_after_destination (f P G S : ℕ) (c : Child) (hS : 0 < S)
    (a : LongAddress (Prefix := Fin P) (Gap := Fin G) (Suffix := Fin S) f) :
    destination (scalarAfter f P G S c hS) (commonLayout f P G S a) =
      commonLayout f P G S (afterScan (childRow c) (childCol c) a) := by
  rw [← child_common f P G S c a,scalarAfter,castProgram_destination]
  have he := ScalarCoordinateProgram.after_encoded (childS_pos f S c hS)
    (childCodec f P G S c (childRepack f c a))
  change destination (ScalarCoordinateProgram.after (P := childP f P c) (Q := radix^f)
    (G := childG f G c) (childS_pos f S c hS)) (childLayout f P G S c (childRepack f c a)) = _ at he
  rw [he,← after_encoded]
  exact child_common f P G S c _

end
end CSL.ScalarLayoutBridge
end ScalarLayoutBridge


