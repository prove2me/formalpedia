-- Prove2me | Definitions.Def_SharpIntermediateSubgroupBounds_Escape
-- name    : SharpIntermediateSubgroupBounds_Escape
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-26T05:42:00.72224+00:00
-- url     : https://prove2.me/theorems/1c388c1f-807a-5b7d-b7e0-0dc501f10efa
-- title:
--   Escape
-- statement:
--   Definitions and structural lemmas for Escape, from Sébastien Palcoux (sebastienpalcoux/sharp-intermediate-subgroup-bounds; see pinned Apache-2.0 LICENSE and formalization.yaml)'s pinned Sharp bounds for intervals in finite subgroup lattices development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/sebastienpalcoux/sharp-intermediate-subgroup-bounds/blob/522d6dfcb5d25d47455375e3df0f8a561b7b780b/SharpIntermediateSubgroupBounds/Escape.lean

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero


set_option autoImplicit true
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
local instance subgroupDecidableEq : DecidableEq (Subgroup G) := Classical.decEq _
def generatedFrom (H : Subgroup G) {r : ℕ} (x : Fin r → G) : Subgroup G :=
  H ⊔ Subgroup.closure (Set.range x)
theorem generatedFrom_mul_right (H : Subgroup G) {r : ℕ}
    (x : Fin r → G) (h : Fin r → H) :
    generatedFrom H (fun i => x i * (h i : G)) = generatedFrom H x := by
  apply le_antisymm
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).2
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    apply (generatedFrom H x).mul_mem
    · exact (show Subgroup.closure (Set.range x) ≤ generatedFrom H x from
        le_sup_right) (Subgroup.subset_closure ⟨i, rfl⟩)
    · exact (show H ≤ generatedFrom H x from le_sup_left) (h i).2
  · apply sup_le le_sup_left
    apply (Subgroup.closure_le _).2
    intro y hy
    obtain ⟨i, rfl⟩ := hy
    have hxmul : x i * (h i : G) ∈
        Subgroup.closure (Set.range (fun j => x j * (h j : G))) :=
      Subgroup.subset_closure ⟨i, rfl⟩
    have hh : ((h i : H) : G)⁻¹ ∈ H := H.inv_mem (h i).2
    have hprod : (x i * (h i : G)) * (h i : G)⁻¹ ∈
        generatedFrom H (fun j => x j * (h j : G)) :=
      (generatedFrom H (fun j => x j * (h j : G))).mul_mem
        ((show Subgroup.closure (Set.range (fun j => x j * (h j : G))) ≤
            generatedFrom H (fun j => x j * (h j : G)) from le_sup_right) hxmul)
        ((show H ≤ generatedFrom H (fun j => x j * (h j : G)) from
            le_sup_left) hh)
    simpa [generatedFrom] using hprod
def RawRelGen (H K : Subgroup G) (r : ℕ) :=
  {x : Fin r → G // (∀ i, x i ∈ K) ∧ generatedFrom H x = K}
def CosetTuple (H K : Subgroup G) (r : ℕ) : Type u :=
  Fin r → (K ⧸ H.subgroupOf K)
def cosetRepTuple (H K : Subgroup G) {r : ℕ} (q : CosetTuple H K r) :
    Fin r → G :=
  fun i => ((Quotient.out (q i) : K) : G)
def CosetRelGen (H K : Subgroup G) (r : ℕ) : Type u :=
  {q : CosetTuple H K r // generatedFrom H (cosetRepTuple H K q) = K}
def rawCosetTuple (H K : Subgroup G) {r : ℕ}
    (x : RawRelGen H K r) : CosetTuple H K r :=
  fun i => QuotientGroup.mk ⟨x.1 i, x.2.1 i⟩
def cosetAdjustment (H K : Subgroup G) (b : K) : H := by
  let a : K := Quotient.out (QuotientGroup.mk b : K ⧸ H.subgroupOf K)
  refine ⟨((a⁻¹ * b : K) : G), ?_⟩
  apply Subgroup.mem_subgroupOf.mp
  apply QuotientGroup.leftRel_apply.mp
  exact Quotient.exact' (Quotient.out_eq'
    (QuotientGroup.mk b : K ⧸ H.subgroupOf K))
@[simp]
theorem cosetRep_mul_cosetAdjustment (H K : Subgroup G) (b : K) :
    ((Quotient.out (QuotientGroup.mk b : K ⧸ H.subgroupOf K) : K) : G) *
        (cosetAdjustment H K b : G) = (b : G) := by
  simp [cosetAdjustment]
theorem generatedFrom_cosetRep_raw (H K : Subgroup G) {r : ℕ}
    (x : RawRelGen H K r) :
    generatedFrom H (cosetRepTuple H K (rawCosetTuple H K x)) = K := by
  let h : Fin r → H := fun i =>
    cosetAdjustment H K ⟨x.1 i, x.2.1 i⟩
  have htuple :
      (fun i => cosetRepTuple H K (rawCosetTuple H K x) i * (h i : G)) =
        x.1 := by
    funext i
    exact cosetRep_mul_cosetAdjustment H K ⟨x.1 i, x.2.1 i⟩
  rw [← generatedFrom_mul_right H
    (cosetRepTuple H K (rawCosetTuple H K x)) h, htuple, x.2.2]
def rawToCosetRelGen (H K : Subgroup G) {r : ℕ} :
    RawRelGen H K r → CosetRelGen H K r :=
  fun x => ⟨rawCosetTuple H K x, generatedFrom_cosetRep_raw H K x⟩
def cosetRelGenProdToRaw {H K : Subgroup G} (hHK : H ≤ K) {r : ℕ} :
    CosetRelGen H K r × (Fin r → H) → RawRelGen H K r :=
  fun z => ⟨fun i => cosetRepTuple H K z.1.1 i * (z.2 i : G),
    fun i => K.mul_mem (Quotient.out (z.1.1 i) : K).2 (hHK (z.2 i).2), by
      rw [generatedFrom_mul_right H (cosetRepTuple H K z.1.1) z.2,
        z.1.2]⟩
theorem rawCosetTuple_cosetRelGenProdToRaw {H K : Subgroup G}
    (hHK : H ≤ K) {r : ℕ} (z : CosetRelGen H K r × (Fin r → H)) :
    rawCosetTuple H K (cosetRelGenProdToRaw hHK z) = z.1.1 := by
  funext i
  let a : K := Quotient.out (z.1.1 i)
  let b : K := ⟨(a : G) * (z.2 i : G),
    K.mul_mem a.2 (hHK (z.2 i).2)⟩
  change QuotientGroup.mk b = z.1.1 i
  calc
    QuotientGroup.mk b = QuotientGroup.mk a := by
      apply Quotient.sound'
      apply QuotientGroup.leftRel_apply.mpr
      apply Subgroup.mem_subgroupOf.mpr
      change ((a : G) * (z.2 i : G))⁻¹ * (a : G) ∈ H
      simpa using H.inv_mem (z.2 i).2
    _ = z.1.1 i := Quotient.out_eq' _
theorem cosetAdjustment_reconstructed {H K : Subgroup G}
    (hHK : H ≤ K) (q : K ⧸ H.subgroupOf K) (h : H) :
    cosetAdjustment H K
        ⟨((Quotient.out q : K) : G) * (h : G),
          K.mul_mem (Quotient.out q : K).2 (hHK h.2)⟩ = h := by
  let a : K := Quotient.out q
  let b : K := ⟨(a : G) * (h : G), K.mul_mem a.2 (hHK h.2)⟩
  have hmk :
      (QuotientGroup.mk b : K ⧸ H.subgroupOf K) = q := by
    calc
      QuotientGroup.mk b = QuotientGroup.mk a := by
        apply Quotient.sound'
        apply QuotientGroup.leftRel_apply.mpr
        apply Subgroup.mem_subgroupOf.mpr
        change ((a : G) * (h : G))⁻¹ * (a : G) ∈ H
        simpa using H.inv_mem h.2
      _ = q := Quotient.out_eq' _
  have hout :
      Quotient.out (QuotientGroup.mk b : K ⧸ H.subgroupOf K) = a := by
    exact congrArg Quotient.out hmk
  apply Subtype.ext
  change (((Quotient.out (QuotientGroup.mk b : K ⧸ H.subgroupOf K) : K)⁻¹ *
    b : K) : G) = (h : G)
  rw [hout]
  simp [b]
def rawRelGenEquivCosetRelGenProd {H K : Subgroup G} (hHK : H ≤ K)
    {r : ℕ} :
    RawRelGen H K r ≃ CosetRelGen H K r × (Fin r → H) where
  toFun x := ⟨rawToCosetRelGen H K x,
    fun i => cosetAdjustment H K ⟨x.1 i, x.2.1 i⟩⟩
  invFun := cosetRelGenProdToRaw hHK
  left_inv := by
    intro x
    apply Subtype.ext
    funext i
    exact cosetRep_mul_cosetAdjustment H K ⟨x.1 i, x.2.1 i⟩
  right_inv := by
    intro z
    apply Prod.ext
    · apply Subtype.ext
      exact rawCosetTuple_cosetRelGenProdToRaw hHK z
    · funext i
      exact cosetAdjustment_reconstructed hHK (z.1.1 i) (z.2 i)
theorem minFac_le_relIndex_of_lt {H A B : Subgroup G}
    (hHA : H ≤ A) (hAB : A < B) :
    H.index.minFac ≤ A.relIndex B := by
  apply Nat.minFac_le_of_dvd
  · letI : A.IsFiniteRelIndex B := A.isFiniteRelIndex_of_finiteIndex
    have hzero : A.relIndex B ≠ 0 := Subgroup.relIndex_ne_zero
    have hone : A.relIndex B ≠ 1 := by
      intro h
      exact hAB.not_ge (Subgroup.relIndex_eq_one.mp h)
    omega
  · exact (A.relIndex_dvd_index_of_le hAB.le).trans
      (Subgroup.index_dvd_of_le hHA)
abbrev EscapeState (K : Subgroup G) : Type u := Set.Iic K
def EscapeChoice (K : Subgroup G) (s : EscapeState K) : Type u :=
  {x : K // s.1 = K ∨ (x.1 : G) ∉ s.1}
instance escapeChoiceFintype (K : Subgroup G) (s : EscapeState K) :
    Fintype (EscapeChoice K s) := by
  letI : Finite (EscapeChoice K s) := Finite.of_injective
    (fun x : EscapeChoice K s => (x.1.1 : G)) (by
      intro x y h
      exact Subtype.ext (Subtype.ext h))
  exact Fintype.ofFinite _
instance escapeChoiceNonempty (K : Subgroup G) (s : EscapeState K) :
    Nonempty (EscapeChoice K s) := by
  classical
  by_cases hs : s.1 = K
  · exact ⟨⟨1, Or.inl hs⟩⟩
  · have hlt : s.1 < K := lt_of_le_of_ne s.2 hs
    obtain ⟨x, hxK, hxM⟩ := SetLike.exists_of_lt hlt
    exact ⟨⟨⟨x, hxK⟩, Or.inr hxM⟩⟩
def gammaProdQ (p r : ℕ) : ℚ :=
  ∏ j ∈ Finset.range r, (1 - 1 / (p : ℚ) ^ (j + 1))
@[simp]
theorem gammaQ_zero (p : ℕ) : gammaQ p 0 = 1 := by
  simp [gammaQ, gammaNum, gammaDen]
def escapeNext (K : Subgroup G) (s : EscapeState K) (x : EscapeChoice K s) :
    EscapeState K :=
  ⟨s.1 ⊔ Subgroup.closure {(x.1 : G)}, by
    change s.1 ⊔ Subgroup.closure {(x.1 : G)} ≤ K
    apply sup_le s.2
    apply (Subgroup.closure_le K).2
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact x.1.2⟩
@[simp]
theorem escapeNext_of_eq (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 = K) (x : EscapeChoice K s) :
    (escapeNext K s x).1 = K := by
  apply le_antisymm (escapeNext K s x).2
  have hKs : K ≤ s.1 := hs.symm.le
  exact hKs.trans le_sup_left
theorem lt_escapeNext_of_ne (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 ≠ K) (x : EscapeChoice K s) :
    s.1 < (escapeNext K s x).1 := by
  apply lt_of_le_of_ne le_sup_left
  intro heq
  have hxcl : (x.1 : G) ∈ Subgroup.closure ({(x.1 : G)} : Set G) :=
    Subgroup.subset_closure (Set.mem_singleton _)
  have hxnext : (x.1 : G) ∈ (escapeNext K s x).1 := by
    exact (show Subgroup.closure ({(x.1 : G)} : Set G) ≤
      s.1 ⊔ Subgroup.closure ({(x.1 : G)} : Set G) from le_sup_right) hxcl
  have hnot : (x.1 : G) ∉ s.1 := x.2.resolve_left hs
  let g : G := x.1
  have hxnext' : g ∈ (escapeNext K s x).1 := hxnext
  have hnot' : g ∉ s.1 := hnot
  apply hnot'
  rw [heq]
  exact hxnext'
abbrev EscapePath (K : Subgroup G) (r : ℕ) (s : EscapeState K) : Type u :=
  BranchingTree.Path (EscapeChoice K) (escapeNext K) r s
def escapeCons (K : Subgroup G) {r : ℕ} {s : EscapeState K}
    (x : EscapeChoice K s) (z : EscapePath K r (escapeNext K s x)) :
    EscapePath K (r + 1) s := by
  change Σ x : EscapeChoice K s, EscapePath K r (escapeNext K s x)
  exact ⟨x, z⟩
def escapeEnd (K : Subgroup G) : ∀ {r : ℕ} {s : EscapeState K},
    EscapePath K r s → EscapeState K
  | 0, s, _ => s
  | _ + 1, _, ⟨x, z⟩ => escapeEnd K z
@[simp]
theorem escapeEnd_cons (K : Subgroup G) {r : ℕ} {s : EscapeState K}
    (x : EscapeChoice K s) (z : EscapePath K r (escapeNext K s x)) :
    escapeEnd K (escapeCons K x z) = escapeEnd K z := rfl
def escapeStrictCount (K : Subgroup G) : ∀ {r : ℕ} {s : EscapeState K},
    EscapePath K r s → ℕ
  | 0, _, _ => 0
  | _ + 1, s, ⟨x, z⟩ =>
      if s.1 = K then escapeStrictCount K z else escapeStrictCount K z + 1
@[simp]
theorem escapeStrictCount_cons (K : Subgroup G) {r : ℕ} {s : EscapeState K}
    (x : EscapeChoice K s) (z : EscapePath K r (escapeNext K s x)) :
    escapeStrictCount K (escapeCons K x z) =
      if s.1 = K then escapeStrictCount K z else escapeStrictCount K z + 1 := rfl
theorem escapeEnd_of_top (K : Subgroup G) {r : ℕ}
    (s : EscapeState K) (hs : s.1 = K) (z : EscapePath K r s) :
    (escapeEnd K z).1 = K := by
  induction r generalizing s with
  | zero => simpa [escapeEnd]
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change (escapeEnd K (escapeCons K x z)).1 = K
      rw [escapeEnd_cons]
      exact ih (escapeNext K s x) (escapeNext_of_eq K s hs x) z
theorem escapeStrictCount_eq_length_of_end_ne (K : Subgroup G)
    {r : ℕ} {s : EscapeState K} (z : EscapePath K r s)
    (hend : (escapeEnd K z).1 ≠ K) :
    escapeStrictCount K z = r := by
  induction r generalizing s with
  | zero => simp [escapeStrictCount]
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change (escapeEnd K (escapeCons K x z)).1 ≠ K at hend
      have hs : s.1 ≠ K := by
        intro hs
        exact hend (escapeEnd_of_top K s hs (escapeCons K x z))
      have hend' : (escapeEnd K z).1 ≠ K := hend
      change escapeStrictCount K (escapeCons K x z) = r + 1
      rw [escapeStrictCount_cons, if_neg hs]
      rw [ih z hend']
theorem escapeStrictCount_of_top (K : Subgroup G) {r : ℕ}
    (s : EscapeState K) (hs : s.1 = K) (z : EscapePath K r s) :
    escapeStrictCount K z = 0 := by
  induction r generalizing s with
  | zero => rfl
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change escapeStrictCount K (escapeCons K x z) = 0
      rw [escapeStrictCount_cons, if_pos hs]
      exact ih (escapeNext K s x) (escapeNext_of_eq K s hs x) z
def escapeTuple (K : Subgroup G) : ∀ {r : ℕ} {s : EscapeState K},
    EscapePath K r s → Fin r → G
  | 0, _, _ => Fin.elim0
  | _ + 1, _, ⟨x, z⟩ => Fin.cons (x.1 : G) (escapeTuple K z)
@[simp]
theorem escapeTuple_cons (K : Subgroup G) {r : ℕ} {s : EscapeState K}
    (x : EscapeChoice K s) (z : EscapePath K r (escapeNext K s x)) :
    escapeTuple K (escapeCons K x z) =
      Fin.cons (x.1 : G) (escapeTuple K z) := rfl
theorem escapeTuple_mem (K : Subgroup G) {r : ℕ} {s : EscapeState K}
    (z : EscapePath K r s) (i : Fin r) : escapeTuple K z i ∈ K := by
  induction r generalizing s with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      refine Fin.cases x.1.2 (fun j => ?_) i
      simpa [escapeTuple] using ih z j
theorem escapeEnd_eq_generated (K : Subgroup G) {r : ℕ}
    {s : EscapeState K} (z : EscapePath K r s) :
    (escapeEnd K z).1 = s.1 ⊔ Subgroup.closure (Set.range (escapeTuple K z)) := by
  induction r generalizing s with
  | zero =>
      have hrange : Set.range (escapeTuple K z) = ∅ := by
        ext y
        constructor
        · rintro ⟨i, -⟩
          exact Fin.elim0 i
        · simp
      rw [hrange]
      simp [escapeEnd]
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change (escapeEnd K (escapeCons K x z)).1 =
        s.1 ⊔ Subgroup.closure (Set.range (escapeTuple K (escapeCons K x z)))
      rw [escapeEnd_cons, ih z]
      simp only [escapeNext, escapeTuple_cons, Fin.range_cons, Set.insert_eq,
        Subgroup.closure_union]
      ac_rfl
theorem escapeEnd_eq_generatedFrom (K : Subgroup G) {H : Subgroup G}
    (hHK : H ≤ K) {r : ℕ} (z : EscapePath K r ⟨H, hHK⟩) :
    (escapeEnd K z).1 = generatedFrom H (escapeTuple K z) := by
  exact escapeEnd_eq_generated K z
theorem escape_chain_bound {H K : Subgroup G} (hHK : H ≤ K)
    {r : ℕ} {s : EscapeState K} (hHs : H ≤ s.1)
    (z : EscapePath K r s) :
    H.index.minFac ^ escapeStrictCount K z *
        (escapeEnd K z).1.relIndex K ≤ s.1.relIndex K := by
  induction r generalizing s with
  | zero => simp [escapeStrictCount, escapeEnd]
  | succ r ih =>
      obtain ⟨x, z⟩ := z
      change H.index.minFac ^ escapeStrictCount K (escapeCons K x z) *
        (escapeEnd K (escapeCons K x z)).1.relIndex K ≤ s.1.relIndex K
      by_cases hs : s.1 = K
      · have hend : (escapeEnd K (escapeCons K x z)).1 = K :=
          escapeEnd_of_top K s hs (escapeCons K x z)
        have hcount : escapeStrictCount K (escapeCons K x z) = 0 :=
          escapeStrictCount_of_top K s hs (escapeCons K x z)
        have hendz : (escapeEnd K z).1 = K := by
          simpa only [escapeEnd_cons] using hend
        simp [hcount, hendz, hs]
      · have hstrict : s.1 < (escapeNext K s x).1 :=
          lt_escapeNext_of_ne K s hs x
        have hHnext : H ≤ (escapeNext K s x).1 := hHs.trans le_sup_left
        have htail := ih hHnext z
        have hstep : H.index.minFac ≤
            s.1.relIndex (escapeNext K s x).1 :=
          minFac_le_relIndex_of_lt hHs hstrict
        have htower := Subgroup.relIndex_mul_relIndex s.1 (escapeNext K s x).1 K
          hstrict.le (escapeNext K s x).2
        rw [escapeStrictCount_cons, if_neg hs, escapeEnd_cons, pow_succ']
        calc
          H.index.minFac * H.index.minFac ^ escapeStrictCount K z *
                (escapeEnd K z).1.relIndex K =
              H.index.minFac *
                (H.index.minFac ^ escapeStrictCount K z *
                  (escapeEnd K z).1.relIndex K) := by ac_rfl
          _ ≤ s.1.relIndex (escapeNext K s x).1 *
                (escapeNext K s x).1.relIndex K :=
              Nat.mul_le_mul hstep htail
          _ = s.1.relIndex K := htower
theorem escapeEnd_eq_target {H K : Subgroup G} (hHK : H ≤ K)
    {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1))
    (z : EscapePath K r ⟨H, hHK⟩) :
    (escapeEnd K z).1 = K := by
  by_contra hend
  have hcount : escapeStrictCount K z = r :=
    escapeStrictCount_eq_length_of_end_ne K z hend
  have hHend : H ≤ (escapeEnd K z).1 := by
    rw [escapeEnd_eq_generatedFrom K hHK z]
    exact le_sup_left
  have hendlt : (escapeEnd K z).1 < K :=
    lt_of_le_of_ne (escapeEnd K z).2 hend
  have hpEnd : H.index.minFac ≤ (escapeEnd K z).1.relIndex K :=
    minFac_le_relIndex_of_lt hHend hendlt
  have hchain := escape_chain_bound hHK (le_refl H) z
  rw [hcount] at hchain
  have : H.index.minFac ^ (r + 1) ≤ H.relIndex K := by
    rw [pow_succ]
    exact le_trans (Nat.mul_le_mul_left _ hpEnd) hchain
  omega
def escapePathToRawRelGen {H K : Subgroup G} (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    EscapePath K r ⟨H, hHK⟩ → RawRelGen H K r :=
  fun z => ⟨escapeTuple K z, escapeTuple_mem K z, by
    rw [← escapeEnd_eq_generatedFrom K hHK z]
    exact escapeEnd_eq_target hHK hhi z⟩
end
end SharpIntermediateSubgroupBounds


