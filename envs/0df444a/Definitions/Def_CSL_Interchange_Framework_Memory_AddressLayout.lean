-- Prove2me | Definitions.Def_CSL_Interchange_Framework_Memory_AddressLayout
-- name    : CSL_Interchange_Framework_Memory_AddressLayout
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-24T14:39:31.433842+00:00
-- url     : https://prove2.me/theorems/5ae826a7-c90d-413d-8d90-9399b186603e
-- title:
--   Coded sorting library: Interchange / Framework / Memory / AddressLayout
-- statement:
--   Module `CodedSorting.Interchange.Framework.Memory.AddressLayout` of the Lean development accompanying B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079, ported to Lean v4.33.1 and Mathlib `0df444a` (namespace `CodedSorting` renamed to `CSL`).
--
--   Exposing a selected high/low coordinate changes only the grouping of the
--   same address digits. The physical file index is unchanged: no implicit
--   repacking pass is used by the recursive scalar calls.
--
--   This module is part of the machine-checked proof of Theorem 3.1 (external-memory integer sorting) and is imported by the later modules of that development.
-- source:
--   B. Li, Z. Li, S. Liu, *Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting*, arXiv:2610.20079 (Theorem 3.1, p.4, and Appendix D); Lean development https://github.com/rtyu-1/coded-sorting-lean, module CodedSorting.Interchange.Framework.Memory.AddressLayout

import Definitions.Def_CSL_Compat
import Definitions.Def_CSL_Interchange_Framework_Fields_FieldPacking
import Definitions.Def_CSL_Interchange_Framework_Fields_BinaryPaddingScan

/-! Exposing a selected high/low coordinate changes only the grouping of the
same address digits. The physical file index is unchanged: no implicit
repacking pass is used by the recursive scalar calls. -/

set_option autoImplicit false
namespace CSL.CommonAddressLayout
open Address SingleCoordinate LexBlocks TriangularStreams CoordinateScans

variable {I : Type*} [Fintype I] [LinearOrder I] [WellFoundedLT I]
variable {P Q G S : ℕ}

abbrev FieldCount (I : Type*) [Fintype I] (Q : ℕ) := Q^Fintype.card I
abbrev BeforeCount (Q : ℕ) (i : I) := Q^Fintype.card (Before i)
abbrev AfterCount (Q : ℕ) (i : I) := Q^Fintype.card (After i)

noncomputable def splitEncoded (i : I) : (I → Fin Q) ≃
    TripleAddress (BeforeCount Q i) Q (AfterCount Q i) :=
  (splitVector (R := Fin Q) i).trans
    (Equiv.prodCongr (subvectorEncode (J := Before i) (Q := Q))
      (Equiv.prodCongr (Equiv.refl (Fin Q)) (subvectorEncode (J := After i) (Q := Q))))

noncomputable def blockEncode (i : I) : (I → Fin Q) ≃
    Fin (BeforeCount Q i*(Q*AfterCount Q i)) := (splitEncoded i).trans tripleEncode

@[simp] theorem blockEncode_apply (i : I) (x : I → Fin Q) :
    blockEncode i x = tripleEncode (subvectorEncode (fun j : Before i => x j.val),
      x i,subvectorEncode (fun j : After i => x j.val)) := rfl

theorem blockCard (i : I) : BeforeCount Q i*(Q*AfterCount Q i) = FieldCount I Q := by
  have h := Fintype.card_congr (blockEncode (Q := Q) i)
  simpa only [Fintype.card_fin,Fintype.card_fun] using h.symm

theorem blockEncode_increasing (i : I) (x y : I → Fin Q)
    (hxy : Pi.Lex (· < ·) (· < ·) x y) : blockEncode i x < blockEncode i y := by
  rw [blockEncode_apply,blockEncode_apply,tripleEncode_lt_iff]
  rcases hxy with ⟨j,hpre,hj⟩
  rcases lt_trichotomy j i with hji | hji | hij
  · left
    apply subvectorEncode_lt _ _ |>.mpr
    exact ⟨⟨j,hji⟩,fun k hk => hpre k.val hk,hj⟩
  · subst j
    right
    refine ⟨?_,Or.inl hj⟩
    apply congrArg subvectorEncode
    funext k
    exact hpre k.val k.property
  · right
    refine ⟨?_,Or.inr ⟨hpre i hij,?_⟩⟩
    · apply congrArg subvectorEncode
      funext k
      exact hpre k.val (k.property.trans hij)
    · apply subvectorEncode_lt _ _ |>.mpr
      exact ⟨⟨j,hij⟩,fun k hk => hpre k.val hk,hj⟩

/-- This generalizes the finite-coordinate lex-layout identity to the actual
ordered network index type and its before/after subtypes. -/
theorem blockPhysical_eq_subvectorEncode (i : I) :
    (blockEncode (Q := Q) i).trans (finCongr (blockCard i)) = subvectorEncode := by
  let e : Equiv.Perm (Fin (FieldCount I Q)) :=
    subvectorEncode.symm.trans ((blockEncode i).trans (finCongr (blockCard i)))
  have hm : StrictMono e := by
    intro a b hab
    apply blockEncode_increasing
    apply (subvectorEncode_lt _ _).mp
    simpa only [Equiv.apply_symm_apply] using hab
  have he : (e : Fin (FieldCount I Q) → Fin (FieldCount I Q)) = id :=
    (hm.range_inj strictMono_id).mp (by simp only [Equiv.range_eq_univ,Set.range_id])
  apply Equiv.ext
  intro x
  have h := congrFun he (subvectorEncode x)
  simpa only [e,Equiv.trans_apply,Equiv.symm_apply_apply,id_eq] using h

/-- Literal mixed-radix address of one vector split around a selected field. -/
theorem field_layout_val (i : I) (x : I → Fin Q) :
    (subvectorEncode x).val =
      (subvectorEncode (fun j : After i => x j.val)).val+
      AfterCount Q i*(x i).val+(Q*AfterCount Q i)*
        (subvectorEncode (fun j : Before i => x j.val)).val := by
  have h := congrArg (fun e : (I → Fin Q) ≃ Fin (FieldCount I Q) => (e x).val)
    (blockPhysical_eq_subvectorEncode (Q := Q) i)
  change (blockEncode i x).val = (subvectorEncode x).val at h
  exact h.symm

/-- Map address fields independently, preserving their order. -/
def shape {A B C D A' B' C' D' : Type*}
    (ep : A ≃ A') (eh : B ≃ B') (eg : C ≃ C') (es : D ≃ D') :
    FullAddress A B C D ≃ FullAddress A' B' C' D' where
  toFun a := ⟨ep a.prefixCoord,eh a.high,eg a.gap,eh a.low,es a.suffix⟩
  invFun a := ⟨ep.symm a.prefixCoord,eh.symm a.high,eg.symm a.gap,eh.symm a.low,es.symm a.suffix⟩
  left_inv a := by cases a; simp
  right_inv a := by cases a; simp

abbrev Volume (I : Type*) [Fintype I] (P Q G S : ℕ) :=
  (P*(FieldCount I Q*G))*(FieldCount I Q*S)

noncomputable def longLayout : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S) ≃
    Fin (Volume I P Q G S) :=
  (shape (Equiv.refl _) subvectorEncode (Equiv.refl _) (Equiv.refl _)).trans lowLayout

@[simp] theorem longLayout_val (a : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)) :
    (longLayout a).val = a.suffix.val+S*(subvectorEncode a.low).val+
      (FieldCount I Q*S)*(a.gap.val+G*(subvectorEncode a.high).val+
        (FieldCount I Q*G)*a.prefixCoord.val) := rfl

abbrev ChildPrefix (P Q : ℕ) (i : I) := P*BeforeCount Q i
abbrev ChildGap (G Q : ℕ) (i j : I) := AfterCount Q i*(G*BeforeCount Q j)
abbrev ChildSuffix (S Q : ℕ) (j : I) := AfterCount Q j*S

noncomputable def prefixEncoding (i : I) :
    ShortPrefix (Prefix := Fin P) (R := Fin Q) i ≃ Fin (ChildPrefix P Q i) :=
  (Equiv.prodCongr (Equiv.refl _) subvectorEncode).trans finProdFinEquiv

noncomputable def gapEncoding (i j : I) :
    ShortGap (Gap := Fin G) (R := Fin Q) i j ≃ Fin (ChildGap G Q i j) :=
  (Equiv.prodCongr subvectorEncode (Equiv.prodCongr (Equiv.refl _) subvectorEncode)).trans tripleEncode

noncomputable def suffixEncoding (j : I) :
    ShortSuffix (Suffix := Fin S) (R := Fin Q) j ≃ Fin (ChildSuffix S Q j) :=
  (Equiv.prodCongr subvectorEncode (Equiv.refl _)).trans finProdFinEquiv

noncomputable def childShape (i j : I) :
    FullAddress (ShortPrefix (Prefix := Fin P) (R := Fin Q) i) (Fin Q)
      (ShortGap (Gap := Fin G) (R := Fin Q) i j) (ShortSuffix (Suffix := Fin S) (R := Fin Q) j) ≃
    FullAddress (Fin (ChildPrefix P Q i)) (Fin Q) (Fin (ChildGap G Q i j))
      (Fin (ChildSuffix S Q j)) :=
  shape (prefixEncoding i) (Equiv.refl _) (gapEncoding i j) (suffixEncoding j)

noncomputable def childLayout (i j : I) :
    FullAddress (ShortPrefix (Prefix := Fin P) (R := Fin Q) i) (Fin Q)
      (ShortGap (Gap := Fin G) (R := Fin Q) i j) (ShortSuffix (Suffix := Fin S) (R := Fin Q) j) ≃
    Fin ((ChildPrefix P Q i*(Q*ChildGap G Q i j))*(Q*ChildSuffix S Q j)) :=
  (shape (prefixEncoding i) (Equiv.refl _) (gapEncoding i j) (suffixEncoding j)).trans lowLayout

/-- Main no-repacking identity. The selected coordinates are exposed inside
exactly the same linear file, even with arbitrary nonempty or empty spectators. -/
theorem childLayout_repack_val (i j : I)
    (a : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)) :
    (childLayout i j (repack i j a)).val = (longLayout a).val := by
  let hb := (subvectorEncode (fun k : Before i => a.high k.val)).val
  let ha := (subvectorEncode (fun k : After i => a.high k.val)).val
  let db := (subvectorEncode (fun k : Before j => a.low k.val)).val
  let da := (subvectorEncode (fun k : After j => a.low k.val)).val
  calc
    (childLayout i j (repack i j a)).val =
      a.suffix.val+S*(da+AfterCount Q j*(a.low j).val+(Q*AfterCount Q j)*db)+
        ((BeforeCount Q j*(Q*AfterCount Q j))*S)*
          (a.gap.val+G*(ha+AfterCount Q i*(a.high i).val+(Q*AfterCount Q i)*hb)+
            ((BeforeCount Q i*(Q*AfterCount Q i))*G)*a.prefixCoord.val) := by
      simp only [childLayout,Equiv.trans_apply,shape,Equiv.coe_fn_mk,repack,splitVector,
        prefixEncoding,gapEncoding,suffixEncoding,Equiv.prodCongr_apply,Equiv.refl_apply,
        lowLayout_val,tripleEncode_val,Prod.map_apply]
      simp only [finProdFinEquiv,Equiv.coe_fn_mk,Equiv.refl_apply,Prod.map_apply]
      try dsimp only [hb,ha,db,da,ChildPrefix,ChildGap,ChildSuffix]
      ring
    _ = (longLayout a).val := by
      rw [blockCard i,blockCard j,longLayout_val,field_layout_val i a.high,field_layout_val j a.low]

/-- Equality of file lengths supplies only a Fin cast, never a data move. -/
theorem childVolume (i j : I) :
    (ChildPrefix P Q i*(Q*ChildGap G Q i j))*(Q*ChildSuffix S Q j) = Volume I P Q G S := by
  unfold ChildPrefix ChildGap ChildSuffix Volume
  have hi := blockCard (Q := Q) i
  have hj := blockCard (Q := Q) j
  calc
    _ = (P*((BeforeCount Q i*(Q*AfterCount Q i))*G))*
      ((BeforeCount Q j*(Q*AfterCount Q j))*S) := by ring
    _ = _ := by rw [hi,hj]

theorem childLayout_repack (i j : I)
    (a : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)) :
    finCongr (childVolume (P := P) (G := G) (S := S) (Q := Q) i j)
      (childLayout i j (repack i j a)) = longLayout a :=
  Fin.ext (childLayout_repack_val i j a)

/-- Coordinate operations commute with regrouping and spectator encoding. -/
theorem selected_encoded (i j : I) (op : Equiv.Perm (Fin Q × Fin Q))
    (a : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)) :
    childShape i j (repack i j (modifySelected i j op a)) =
      mapPairEquiv op (childShape i j (repack i j a)) := by
  simp only [repack,modifySelected,Equiv.coe_fn_mk,splitVector_update,childShape,
    shape,mapPairEquiv,mapPair,Equiv.refl_apply]
  rfl

section ScalarScans
variable [NeZero Q]

/-- The pre-child addition runs in the same physical file layout. -/
theorem scalar_before_destination (i j : I)
    (a : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)) :
    finCongr (childVolume (P := P) (G := G) (S := S) (Q := Q) i j)
      (ScanProgram.destination (ScalarCoordinateProgram.before
        (P := ChildPrefix P Q i) (Q := Q) (G := ChildGap G Q i j) (S := ChildSuffix S Q j))
        ((finCongr (childVolume i j)).symm (longLayout a))) =
      longLayout (beforeScan i j a) := by
  rw [← childLayout_repack i j a,Equiv.symm_apply_apply]
  have hop := selected_encoded i j CoordinateScans.lowerAddPerm a
  change childShape i j (repack i j (beforeScan i j a)) =
    mapPairEquiv CoordinateScans.lowerAddPerm (childShape i j (repack i j a)) at hop
  calc
    _ = finCongr (childVolume i j) (lowLayout
        (mapPairEquiv CoordinateScans.lowerAddPerm (childShape i j (repack i j a)))) := by
      apply congrArg (finCongr (childVolume i j))
      exact ScalarCoordinateProgram.before_encoded (childShape i j (repack i j a))
    _ = finCongr (childVolume i j) (childLayout i j (repack i j (beforeScan i j a))) := by
      rw [← hop]
      rfl
    _ = _ := childLayout_repack i j (beforeScan i j a)

/-- The post-child reflected addition also preserves that layout. -/
theorem scalar_after_destination (i j : I) (hS : 0 < S)
    (a : FullAddress (Fin P) (I → Fin Q) (Fin G) (Fin S)) :
    finCongr (childVolume (P := P) (G := G) (S := S) (Q := Q) i j)
      (ScanProgram.destination (ScalarCoordinateProgram.after
        (P := ChildPrefix P Q i) (Q := Q) (G := ChildGap G Q i j)
        (mul_pos (pow_pos (NeZero.pos Q) _) hS))
        ((finCongr (childVolume i j)).symm (longLayout a))) =
      longLayout (afterScan i j a) := by
  rw [← childLayout_repack i j a,Equiv.symm_apply_apply]
  have hop := selected_encoded i j CoordinateScans.lowerReflectPerm a
  change childShape i j (repack i j (afterScan i j a)) =
    mapPairEquiv CoordinateScans.lowerReflectPerm (childShape i j (repack i j a)) at hop
  calc
    _ = finCongr (childVolume i j) (lowLayout
        (mapPairEquiv CoordinateScans.lowerReflectPerm (childShape i j (repack i j a)))) := by
      apply congrArg (finCongr (childVolume i j))
      exact ScalarCoordinateProgram.after_encoded (mul_pos (pow_pos (NeZero.pos Q) _) hS)
        (childShape i j (repack i j a))
    _ = finCongr (childVolume i j) (childLayout i j (repack i j (afterScan i j a))) := by
      rw [← hop]
      rfl
    _ = _ := childLayout_repack i j (afterScan i j a)
end ScalarScans

end CSL.CommonAddressLayout


