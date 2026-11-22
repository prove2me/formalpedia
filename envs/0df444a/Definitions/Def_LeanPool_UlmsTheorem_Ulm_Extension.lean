-- Prove2me | Definitions.Def_LeanPool_UlmsTheorem_Ulm_Extension
-- name    : LeanPool_UlmsTheorem_Ulm_Extension
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T17:56:14.998312+00:00
-- url     : https://prove2.me/theorems/abe20dec-9e89-4919-add4-db6a8c792c88
-- title:
--   Extension
-- statement:
--   Definitions and structural lemmas for Extension, from Elan Roth; LeanPool contributors's pinned Ulm’s theorem for abelian p-groups development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/UlmsTheorem/Ulm/Extension.lean

module
public import Mathlib.RingTheory.TwoSidedIdeal.Operations
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Definitions.Def_LeanPool_UlmsTheorem_PGroups_UlmInvariants
public import Definitions.Def_LeanPool_UlmsTheorem_Ulm_Pure
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theorems.Thm_UlmsTheorem_mem_pImage
public import Theorems.Thm_UlmsTheorem_mem_ulmSubgroup_add_one_iff
public import Theorems.Thm_UlmsTheorem_pHeight_zero
public import Theorems.Thm_UlmsTheorem_pOrder_zero
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_antitone
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_succ
public import Theorems.Thm_UlmsTheorem_ulmSubgroup_zero
attribute [local simp] UlmsTheorem.mem_pImage
attribute [local simp] UlmsTheorem.mem_ulmSubgroup_add_one_iff
attribute [local simp] UlmsTheorem.pHeight_zero
attribute [local simp] UlmsTheorem.pOrder_zero
attribute [local simp] UlmsTheorem.ulmSubgroup_zero


set_option autoImplicit true
@[expose] public section
@[expose] public section
namespace UlmsTheorem
open Ordinal
universe u
variable (p : ℕ) [hp : Fact p.Prime]
variable {G : Type u} [AddCommGroup G]
variable {H : Type u} [AddCommGroup H]
noncomputable def stageAt (S : AddSubgroup G) (α : Ordinal) : AddSubgroup G :=
  S ⊓ ulmSubgroup p α
noncomputable def kaplanskyStar (S : AddSubgroup G) (α : Ordinal) : AddSubgroup G where
  carrier := {x | x ∈ S ∧ x ∈ ulmSubgroup p α ∧
    p • x ∈ ulmSubgroup p (Order.succ (Order.succ α))}
  zero_mem' := ⟨S.zero_mem, (ulmSubgroup p α).zero_mem, by
    simp⟩
  add_mem' := by
    rintro x y ⟨hxS, hxα, hpx⟩ ⟨hyS, hyα, hpy⟩
    exact ⟨S.add_mem hxS hyS, (ulmSubgroup p α).add_mem hxα hyα, by
      rw [smul_add]
      exact (ulmSubgroup p (Order.succ (Order.succ α))).add_mem hpx hpy⟩
  neg_mem' := by
    rintro x ⟨hxS, hxα, hpx⟩
    exact ⟨S.neg_mem hxS, (ulmSubgroup p α).neg_mem hxα, by
      rw [smul_neg]
      exact (ulmSubgroup p (Order.succ (Order.succ α))).neg_mem hpx⟩
noncomputable def stageAtSuccInStar (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (kaplanskyStar p S α) :=
  (stageAt p S (Order.succ α)).comap (kaplanskyStar p S α).subtype
noncomputable def kaplanskyDomainQuotient (S : AddSubgroup G) (α : Ordinal) : Type u :=
  kaplanskyStar p S α ⧸ stageAtSuccInStar p S α
noncomputable instance (S : AddSubgroup G) (α : Ordinal) :
    AddCommGroup (kaplanskyDomainQuotient p S α) := by
  unfold kaplanskyDomainQuotient
  infer_instance
omit hp in
/-- Every class in Kaplansky's source quotient is killed by `p`. -/
lemma kaplanskyDomainQuotient_orderOf_dvd_p
    (S : AddSubgroup G) (α : Ordinal)
    (x : kaplanskyDomainQuotient p S α) :
    p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  change QuotientAddGroup.mk' (stageAtSuccInStar p S α) (p • a) =
    QuotientAddGroup.mk' (stageAtSuccInStar p S α) 0
  apply (QuotientAddGroup.mk'_eq_mk' _).2
  refine ⟨-(p • a), ?_, by simp⟩
  change (-(p • (a : G))) ∈ stageAt p S (Order.succ α)
  refine ⟨S.neg_mem (S.nsmul_mem a.property.1 p), ?_⟩
  apply (ulmSubgroup p (Order.succ α)).neg_mem
  exact ulmSubgroup_antitone p (Order.le_succ (Order.succ α)) a.property.2.2
noncomputable instance kaplanskyDomainQuotientModule
    (S : AddSubgroup G) (α : Ordinal) :
    Module (ZMod p) (kaplanskyDomainQuotient p S α) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := kaplanskyDomainQuotient p S α) ?_
  intro x
  exact kaplanskyDomainQuotient_orderOf_dvd_p p S α x
noncomputable def kaplanskyLinearMap
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    kaplanskyDomainQuotient p S α →ₗ[ZMod p] ulmQuotient p α (G := G) :=
  U.toZModLinearMap p
noncomputable def kaplanskyOccupiedSubmodule
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  LinearMap.range (kaplanskyLinearMap p S α U)
abbrev kaplanskyRoomQuotient
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) : Type _ :=
  ulmQuotient p α (G := G) ⧸ kaplanskyOccupiedSubmodule p S α U
noncomputable def kaplanskyRoomInvariant
    (S : AddSubgroup G) (α : Ordinal)
    (U : kaplanskyDomainQuotient p S α →+ ulmQuotient p α (G := G)) :
    Cardinal :=
  Module.rank (ZMod p) (kaplanskyRoomQuotient p S α U)
omit hp in
/-- A chosen correction one level higher, with the same `p`-multiple as an
element of `S_α*`.  The eventual quotient class is independent of this choice. -/
lemma exists_kaplanskyCorrection
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    ∃ y : G, y ∈ ulmSubgroup p (Order.succ α) ∧ p • y = p • (x : G) := by
  have hx := x.property.2.2
  rw [ulmSubgroup_succ] at hx
  exact hx
noncomputable def kaplanskyCorrection
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) : G :=
  Classical.choose (exists_kaplanskyCorrection p S α x)
omit hp in
lemma kaplanskyCorrection_mem
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    kaplanskyCorrection p S α x ∈ ulmSubgroup p (Order.succ α) :=
  (Classical.choose_spec (exists_kaplanskyCorrection p S α x)).1
omit hp in
lemma kaplanskyCorrection_smul
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    p • kaplanskyCorrection p S α x = p • (x : G) :=
  (Classical.choose_spec (exists_kaplanskyCorrection p S α x)).2
noncomputable def kaplanskySocleRep
    (S : AddSubgroup G) (α : Ordinal) (x : kaplanskyStar p S α) :
    pSocleAt p α (G := G) := by
  refine ⟨(x : G) - kaplanskyCorrection p S α x, ?_⟩
  rw [mem_pSocleAt]
  constructor
  · rw [smul_sub, kaplanskyCorrection_smul]
    simp
  · exact (ulmSubgroup p α).sub_mem x.property.2.1
      (ulmSubgroup_antitone p (Order.le_succ α)
        (kaplanskyCorrection_mem p S α x))
noncomputable def kaplanskyPreMap
    (S : AddSubgroup G) (α : Ordinal) :
    kaplanskyStar p S α →+ ulmQuotient p α (G := G) where
  toFun x := (ulmDenSubmodule p α).mkQ (kaplanskySocleRep p S α x)
  map_zero' := by
    apply (Submodule.Quotient.mk_eq_zero _).2
    change (kaplanskySocleRep p S α 0 : G) ∈
      pSocleAt p (Order.succ α) (G := G)
    rw [mem_pSocleAt]
    refine ⟨(kaplanskySocleRep p S α 0).property.1, ?_⟩
    change (0 : G) - kaplanskyCorrection p S α 0 ∈
      ulmSubgroup p (Order.succ α)
    simpa using (ulmSubgroup p (Order.succ α)).neg_mem
      (kaplanskyCorrection_mem p S α 0)
  map_add' x y := by
    rw [← LinearMap.map_add]
    apply (Submodule.Quotient.eq _).2
    change ((kaplanskySocleRep p S α (x + y) -
      (kaplanskySocleRep p S α x + kaplanskySocleRep p S α y) :
        pSocleAt p α (G := G)) : G) ∈
      pSocleAt p (Order.succ α) (G := G)
    rw [mem_pSocleAt]
    refine ⟨by
      have h := (kaplanskySocleRep p S α (x + y) -
        (kaplanskySocleRep p S α x + kaplanskySocleRep p S α y)).property
      exact h.1, ?_⟩
    change ((x : G) + y - kaplanskyCorrection p S α (x + y)) -
        (((x : G) - kaplanskyCorrection p S α x) +
          ((y : G) - kaplanskyCorrection p S α y)) ∈
      ulmSubgroup p (Order.succ α)
    have hx := kaplanskyCorrection_mem p S α x
    have hy := kaplanskyCorrection_mem p S α y
    have hxy := kaplanskyCorrection_mem p S α (x + y)
    have hmem :
        kaplanskyCorrection p S α x + kaplanskyCorrection p S α y -
            kaplanskyCorrection p S α (x + y) ∈
          ulmSubgroup p (Order.succ α) :=
      (ulmSubgroup p (Order.succ α)).sub_mem
        ((ulmSubgroup p (Order.succ α)).add_mem hx hy) hxy
    convert hmem using 1
    abel
noncomputable def kaplanskyMap
    (S : AddSubgroup G) (α : Ordinal) :
    kaplanskyDomainQuotient p S α →+
      ulmQuotient p α (G := G) :=
  QuotientAddGroup.lift (stageAtSuccInStar p S α)
    (kaplanskyPreMap p S α) (by
      intro x hx
      rw [AddMonoidHom.mem_ker]
      apply (Submodule.Quotient.mk_eq_zero _).2
      change (kaplanskySocleRep p S α x : G) ∈
        pSocleAt p (Order.succ α) (G := G)
      rw [mem_pSocleAt]
      refine ⟨(kaplanskySocleRep p S α x).property.1, ?_⟩
      exact (ulmSubgroup p (Order.succ α)).sub_mem hx.2
        (kaplanskyCorrection_mem p S α x))
structure UlmStage where
  /-- The finite source subgroup. -/
  A : AddSubgroup G
  /-- The finite target subgroup. -/
  B : AddSubgroup H
  hAfinite : Set.Finite (A : Set G)
  hBfinite : Set.Finite (B : Set H)
  /-- The partial additive equivalence between the stage subgroups. -/
  e : A ≃+ B
  hφ : IsHeightPresOn p e.toAddMonoidHom
structure UlmStageAt (α : Ordinal.{0}) where
  /-- The finite source subgroup. -/
  A : AddSubgroup G
  /-- The finite target subgroup. -/
  B : AddSubgroup H
  hAfinite : Set.Finite (A : Set G)
  hBfinite : Set.Finite (B : Set H)
  /-- The partial additive equivalence between the stage subgroups. -/
  e : A ≃+ B
  hφ_at : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p α (G := G) ↔
      (e x : H) ∈ ulmSubgroup p α (G := H))
  hφ_succ : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p (Order.succ α) (G := G) ↔
      (e x : H) ∈ ulmSubgroup p (Order.succ α) (G := H))
  hφ_succSucc : ∀ x : A,
    ((x : G) ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := G) ↔
      (e x : H) ∈ ulmSubgroup p (Order.succ (Order.succ α)) (G := H))
def UlmStage.at (s : UlmStage p (G := G) (H := H)) (α : Ordinal.{0}) :
    UlmStageAt p (G := G) (H := H) α where
  A := s.A
  B := s.B
  hAfinite := s.hAfinite
  hBfinite := s.hBfinite
  e := s.e
  hφ_at := fun x ↦ s.hφ x α
  hφ_succ := fun x ↦ s.hφ x (Order.succ α)
  hφ_succSucc := fun x ↦ s.hφ x (Order.succ (Order.succ α))
noncomputable def UlmStage.symm (s : UlmStage p (G := G) (H := H)) :
    UlmStage p (G := H) (H := G) where
  A := s.B
  B := s.A
  hAfinite := s.hBfinite
  hBfinite := s.hAfinite
  e := s.e.symm
  hφ := by
    intro b α
    simpa using (s.hφ (s.e.symm b) α).symm
noncomputable def kaplanskyStarEquiv
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    kaplanskyStar p s.A α ≃+ kaplanskyStar p s.B α where
  toFun x := by
    refine ⟨(s.e ⟨(x : G), x.property.1⟩ : H), ?_⟩
    refine ⟨(s.e ⟨(x : G), x.property.1⟩).prop,
      (s.hφ_at ⟨(x : G), x.property.1⟩).mp x.property.2.1, ?_⟩
    have hpxA : p • (x : G) ∈ s.A := s.A.nsmul_mem x.property.1 p
    have hmap :
        p • (s.e ⟨(x : G), x.property.1⟩ : H) =
          (s.e ⟨p • (x : G), hpxA⟩ : H) := by
      exact
        (congrArg Subtype.val
          (map_nsmul s.e p ⟨(x : G), x.property.1⟩)).symm
    rw [hmap]
    exact
      (s.hφ_succSucc ⟨p • (x : G), hpxA⟩).mp x.property.2.2
  invFun y := by
    refine ⟨(s.e.symm ⟨(y : H), y.property.1⟩ : G), ?_⟩
    have heinv :
        s.e (s.e.symm ⟨(y : H), y.property.1⟩) =
          ⟨(y : H), y.property.1⟩ := s.e.apply_symm_apply _
    refine ⟨(s.e.symm ⟨(y : H), y.property.1⟩).prop, ?_, ?_⟩
    · apply (s.hφ_at (s.e.symm ⟨(y : H), y.property.1⟩)).mpr
      simpa [heinv] using y.property.2.1
    · have hpxA :
          p • (s.e.symm ⟨(y : H), y.property.1⟩ : G) ∈ s.A :=
        s.A.nsmul_mem (s.e.symm ⟨(y : H), y.property.1⟩).prop p
      apply
        (s.hφ_succSucc
          ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩).mpr
      have hmap :
          (s.e
            ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩ : H) =
            p • (y : H) := by
        calc
          (s.e
              ⟨p • (s.e.symm ⟨(y : H), y.property.1⟩ : G), hpxA⟩ : H) =
              p • (s.e (s.e.symm ⟨(y : H), y.property.1⟩) : H) := by
                exact congrArg Subtype.val
                  (map_nsmul s.e
                    p (s.e.symm ⟨(y : H), y.property.1⟩))
          _ = p • (y : H) := by
                rw [congrArg Subtype.val heinv]
      simpa only [hmap] using y.property.2.2
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp
  map_add' x y := by
    ext
    simpa using congrArg Subtype.val
      (s.e.map_add ⟨(x : G), x.property.1⟩ ⟨(y : G), y.property.1⟩)
omit hp in
lemma kaplanskyStarEquiv_map_stageAtSucc
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    (stageAtSuccInStar p s.A α).map
        (kaplanskyStarEquiv p s).toAddMonoidHom =
      stageAtSuccInStar p s.B α := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change
      ((kaplanskyStarEquiv p s x : kaplanskyStar p s.B α) : H) ∈
        stageAt p s.B (Order.succ α)
    change (x : G) ∈ stageAt p s.A (Order.succ α) at hx
    refine ⟨(kaplanskyStarEquiv p s x).property.1, ?_⟩
    change
      (s.e ⟨(x : G), x.property.1⟩ : H) ∈
        ulmSubgroup p (Order.succ α)
    exact (s.hφ_succ ⟨(x : G), x.property.1⟩).mp hx.2
  · intro hy
    let x : kaplanskyStar p s.A α :=
      (kaplanskyStarEquiv p s).symm y
    refine ⟨x, ?_, (kaplanskyStarEquiv p s).apply_symm_apply y⟩
    change (x : G) ∈ stageAt p s.A (Order.succ α)
    change (y : H) ∈ stageAt p s.B (Order.succ α) at hy
    refine ⟨x.property.1, ?_⟩
    apply (s.hφ_succ ⟨(x : G), x.property.1⟩).mpr
    have heq :
        (s.e ⟨(x : G), x.property.1⟩ : H) = (y : H) := by
      simp [x, kaplanskyStarEquiv]
    change
      (s.e ⟨(x : G), x.property.1⟩ : H) ∈
        ulmSubgroup p (Order.succ α)
    rw [heq]
    exact hy.2
noncomputable def kaplanskyDomainEquiv
    {α : Ordinal.{0}} (s : UlmStageAt p (G := G) (H := H) α) :
    kaplanskyDomainQuotient p s.A α ≃+
      kaplanskyDomainQuotient p s.B α :=
  QuotientAddGroup.congr
    (stageAtSuccInStar p s.A α)
    (stageAtSuccInStar p s.B α)
    (kaplanskyStarEquiv p s)
    (kaplanskyStarEquiv_map_stageAtSucc p s)
def adjoinElem (A : AddSubgroup G) (g : G) : AddSubgroup G :=
  A ⊔ AddSubgroup.closure ({g} : Set G)
lemma le_adjoinElem (A : AddSubgroup G) (g : G) : A ≤ adjoinElem A g := by
  exact le_sup_left
lemma mem_adjoinElem_right (A : AddSubgroup G) (g : G) :
    g ∈ adjoinElem A g := by
  exact
    (show AddSubgroup.closure ({g} : Set G) ≤ adjoinElem A g from le_sup_right)
      (AddSubgroup.subset_closure (by simp))
end UlmsTheorem


