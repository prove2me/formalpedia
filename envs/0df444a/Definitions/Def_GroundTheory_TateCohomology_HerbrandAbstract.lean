-- Prove2me | Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
-- name    : GroundTheory_TateCohomology_HerbrandAbstract
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-23T05:06:34.556444+00:00
-- url     : https://prove2.me/theorems/8d5b4f6a-8e2c-4c42-ac2c-418ac1382013
-- title:
--   Herbrand Abstract
-- statement:
--   Definitions and structural lemmas for Herbrand Abstract, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/HerbrandAbstract.lean

import Mathlib
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
namespace GroundTheory.GroupCoh
section Card
end Card
section Defs
variable {A : Type*} [AddCommGroup A]
abbrev KerModRange (f g : A →+ A) : Type _ :=
  f.ker ⧸ g.range.addSubgroupOf f.ker
def HasHerbrandQuotient (f g : A →+ A) : Prop :=
  Finite (KerModRange f g) ∧ Finite (KerModRange g f)
noncomputable def herbrandQuotient (f g : A →+ A) : ℚ :=
  (Nat.card (KerModRange f g) : ℚ) / Nat.card (KerModRange g f)
theorem KerModRange.mk_eq_zero_iff {f g : A →+ A} (x : f.ker) :
    (QuotientAddGroup.mk x : KerModRange f g) = 0 ↔ (x : A) ∈ g.range := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
end Defs
section Maps
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
def kerMap {fA : A →+ A} {fB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a)) :
    fA.ker →+ fB.ker :=
  (i.comp fA.ker.subtype).codRestrict fB.ker fun a => by
    rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, ← hf,
      AddMonoidHom.mem_ker.1 a.2, map_zero]
@[simp]
theorem kerMap_apply {fA : A →+ A} {fB : B →+ B} (i : A →+ B) (hf : ∀ a, i (fA a) = fB (i a))
    (a : fA.ker) : (kerMap i hf a : B) = i a :=
  rfl
def KerModRange.map {fA gA : A →+ A} {fB gB : B →+ B} (i : A →+ B)
    (hf : ∀ a, i (fA a) = fB (i a)) (hg : ∀ a, i (gA a) = gB (i a)) :
    KerModRange fA gA →+ KerModRange fB gB :=
  QuotientAddGroup.map _ _ (kerMap i hf) fun a ha => by
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf, kerMap_apply]
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.1 ha
    exact AddMonoidHom.mem_range.2 ⟨i x, by rw [← hg, hx]⟩
end Maps
section Hexagon
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
def connDomain (fB : B →+ B) (i : A →+ B) : AddSubgroup B :=
  i.range.comap fB
theorem connDomain_mem_ker (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b))
    (s : connDomain fB i) : p s ∈ fC.ker := by
  have : p (fB s) = 0 := (hex _).2 (AddMonoidHom.mem_range.1 (AddSubgroup.mem_comap.1 s.2))
  rw [AddMonoidHom.mem_ker, ← hfp, this]
def connLeft (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b)) :
    connDomain fB i →+ KerModRange fC gC :=
  (QuotientAddGroup.mk' _).comp <|
    (p.comp (connDomain fB i).subtype).codRestrict fC.ker (connDomain_mem_ker hex hfp)
theorem connLeft_apply (hex : Function.Exact i p) (hfp : ∀ b, p (fB b) = fC (p b))
    (s : connDomain fB i) :
    (connLeft hex hfp s : KerModRange fC gC) =
      QuotientAddGroup.mk (⟨p s, connDomain_mem_ker hex hfp s⟩ : fC.ker) :=
  rfl
noncomputable def connInv (hi : Function.Injective i) : connDomain fB i →+ A :=
  (AddMonoidHom.ofInjective hi).symm.toAddMonoidHom.comp <|
    (fB.comp (connDomain fB i).subtype).codRestrict i.range fun s => s.2
theorem apply_connInv (hi : Function.Injective i) (s : connDomain fB i) :
    i (connInv hi s) = fB s :=
  AddMonoidHom.apply_ofInjective_symm hi _
theorem connInv_mem_ker (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a))
    (hgfB : ∀ b, gB (fB b) = 0) (s : connDomain fB i) : connInv hi s ∈ gA.ker := by
  rw [AddMonoidHom.mem_ker]
  apply hi
  rw [hgi, apply_connInv, hgfB, map_zero]
noncomputable def connRight (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a))
    (hgfB : ∀ b, gB (fB b) = 0) : connDomain fB i →+ KerModRange gA fA :=
  (QuotientAddGroup.mk' _).comp <| (connInv hi).codRestrict gA.ker (connInv_mem_ker hi hgi hgfB)
theorem connRight_apply (hi : Function.Injective i) (hgi : ∀ a, i (gA a) = gB (i a))
    (hgfB : ∀ b, gB (fB b) = 0) (s : connDomain fB i) :
    (connRight hi hgi hgfB s : KerModRange gA fA) =
      QuotientAddGroup.mk (⟨connInv hi s, connInv_mem_ker hi hgi hgfB s⟩ : gA.ker) :=
  rfl
theorem connLeft_surjective (hp : Function.Surjective p) (hex : Function.Exact i p)
    (hfp : ∀ b, p (fB b) = fC (p b)) :
    Function.Surjective (connLeft hex hfp : connDomain fB i →+ KerModRange fC gC) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H z =>
  obtain ⟨c, hc⟩ := z
  obtain ⟨b, rfl⟩ := hp c
  have hb : b ∈ connDomain fB i :=
    AddSubgroup.mem_comap.2 (AddMonoidHom.mem_range.2
      ((hex _).1 (by rw [hfp]; exact AddMonoidHom.mem_ker.1 hc)))
  exact ⟨⟨b, hb⟩, rfl⟩
theorem ker_connLeft_le (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    (connLeft hex hfp : connDomain fB i →+ KerModRange fC gC).ker ≤
      (connRight hi hgi hgfB : connDomain fB i →+ KerModRange gA fA).ker := by
  intro s hs
  rw [AddMonoidHom.mem_ker, connLeft_apply, KerModRange.mk_eq_zero_iff] at hs
  rw [AddMonoidHom.mem_ker, connRight_apply, KerModRange.mk_eq_zero_iff]
  obtain ⟨c, hc⟩ := AddMonoidHom.mem_range.1 hs
  obtain ⟨b', rfl⟩ := hp c
  obtain ⟨a, ha⟩ : (s : B) - gB b' ∈ Set.range i :=
    (hex _).1 (by rw [map_sub, hgp, hc]; exact sub_self _)
  refine AddMonoidHom.mem_range.2 ⟨a, hi ?_⟩
  rw [hfi, ha, apply_connInv, map_sub, hfgB, sub_zero]
noncomputable def connecting (hi : Function.Injective i) (hp : Function.Surjective p)
    (hex : Function.Exact i p) (hfi : ∀ a, i (fA a) = fB (i a))
    (hgi : ∀ a, i (gA a) = gB (i a)) (hfp : ∀ b, p (fB b) = fC (p b))
    (hgp : ∀ b, p (gB b) = gC (p b)) (hfgB : ∀ b, fB (gB b) = 0) (hgfB : ∀ b, gB (fB b) = 0) :
    KerModRange fC gC →+ KerModRange gA fA :=
  (QuotientAddGroup.lift _ (connRight hi hgi hgfB : connDomain fB i →+ KerModRange gA fA)
      (ker_connLeft_le hi hp hex hfi hgi hfp hgp hfgB hgfB)).comp
    (QuotientAddGroup.quotientKerEquivOfSurjective _
      (connLeft_surjective hp hex hfp)).symm.toAddMonoidHom
end Hexagon
section ShortExact
variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  {fA gA : A →+ A} {fB gB : B →+ B} {fC gC : C →+ C} {i : A →+ B} {p : B →+ C}
end ShortExact
section FiniteIndex
variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
def restrictEnd (f : B →+ B) (S : AddSubgroup B) (hS : ∀ x ∈ S, f x ∈ S) : S →+ S :=
  (f.comp S.subtype).codRestrict S fun x => hS x x.2
end FiniteIndex
end GroundTheory.GroupCoh


