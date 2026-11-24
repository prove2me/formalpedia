-- Prove2me | Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
-- name    : GroundTheory_ArithmeticGeometry_SchemeCohomology_CechLeray
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-11-24T00:50:36.302736+00:00
-- url     : https://prove2.me/theorems/e2150220-a75a-4332-807f-df4d921550cb
-- title:
--   Cech Leray
-- statement:
--   Definitions and structural lemmas for Cech Leray, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ArithmeticGeometry/SchemeCohomology/CechLeray.lean

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_CechToDerived
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_SheafH
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_constCochain
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_exists_glue
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_inter_mem
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_le_inter_const
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_comp
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_d
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_push_injective
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_exact__02328f27094f
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_H_exact__598dfd24061d
import Theorems.Thm_P2M_GroundTheory_Arith_SchemeCoh_push_zero__4bd36dbeb085

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
namespace GroundTheory.Arith.SchemeCoh
noncomputable section
open CategoryTheory Opposite TopologicalSpace Limits Abelian
universe w w' u
variable {X : TopCat.{u}}
section Groups
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
def cocycles (n : ℕ) : AddSubgroup (Cochain P U n) := (d P U n).ker
def coboundaries : (n : ℕ) → AddSubgroup (Cochain P U n)
  | 0 => ⊥
  | n + 1 => (d P U n).range
lemma coboundaries_zero : coboundaries P U 0 = ⊥ := rfl
lemma coboundaries_succ (n : ℕ) : coboundaries P U (n + 1) = (d P U n).range := rfl
abbrev cechH (n : ℕ) : Type (max w u) :=
  cocycles P U n ⧸ (coboundaries P U n).addSubgroupOf (cocycles P U n)
variable {P U}
lemma mem_cocycles {n : ℕ} (σ : Cochain P U n) : σ ∈ cocycles P U n ↔ d P U n σ = 0 :=
  AddMonoidHom.mem_ker
def cls {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) : cechH P U n :=
  QuotientAddGroup.mk (⟨σ, (mem_cocycles σ).2 hσ⟩ : cocycles P U n)
lemma cls_eq_zero_iff {n : ℕ} (σ : Cochain P U n) (hσ : d P U n σ = 0) :
    cls σ hσ = 0 ↔ σ ∈ coboundaries P U n := by
  rw [cls, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
lemma cls_zero {n : ℕ} : cls (0 : Cochain P U n) (map_zero _) = 0 :=
  QuotientAddGroup.mk_zero _
lemma cls_add {n : ℕ} (σ σ' : Cochain P U n) (hσ : d P U n σ = 0) (hσ' : d P U n σ' = 0)
    (h : d P U n (σ + σ') = 0) : cls (σ + σ') h = cls σ hσ + cls σ' hσ' :=
  rfl
lemma cls_eq_cls_iff {n : ℕ} (σ σ' : Cochain P U n) (hσ : d P U n σ = 0)
    (hσ' : d P U n σ' = 0) : cls σ hσ = cls σ' hσ' ↔ σ' - σ ∈ coboundaries P U n := by
  rw [cls, cls, QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
  rfl
lemma exists_cls {n : ℕ} (c : cechH P U n) :
    ∃ σ hσ, cls (P := P) (U := U) (n := n) σ hσ = c := by
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := QuotientAddGroup.mk_surjective c
  exact ⟨σ, (mem_cocycles σ).1 hσ, rfl⟩
end Groups
section Connecting
variable {ι : Type w} (U : ι → Opens X) {F I Q : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}}
structure IsCechShortExact (f : F ⟶ I) (g : I ⟶ Q) : Prop where
  zero : f ≫ g = 0
  injective : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Injective (f.app (op (inter U i)))
  exact : ∀ {n : ℕ} (i : Fin (n + 1) → ι) (y : I.obj (op (inter U i))),
    g.app _ y = 0 → ∃ x, f.app _ x = y
  surjective : ∀ {n : ℕ} (i : Fin (n + 1) → ι), Function.Surjective (g.app (op (inter U i)))
def DeltaRel (f : F ⟶ I) (g : I ⟶ Q) (n : ℕ) (σ : Cochain Q U n) (c : cechH F U (n + 1)) :
    Prop :=
  ∃ (τ : Cochain I U n) (ρ : Cochain F U (n + 1)) (hρ : d F U (n + 1) ρ = 0),
    push U g n τ = σ ∧ push U f (n + 1) ρ = d I U n τ ∧ c = cls ρ hρ
variable {U} {f : F ⟶ I} {g : I ⟶ Q}
lemma DeltaRel.add {n : ℕ} {σ σ' : Cochain Q U n} {c c' : cechH F U (n + 1)}
    (h : DeltaRel U f g n σ c) (h' : DeltaRel U f g n σ' c') :
    DeltaRel U f g n (σ + σ') (c + c') := by
  obtain ⟨τ, ρ, hρ, hτ, hρτ, rfl⟩ := h
  obtain ⟨τ', ρ', hρ', hτ', hρτ', rfl⟩ := h'
  exact ⟨τ + τ', ρ + ρ', by rw [map_add, hρ, hρ', add_zero], by rw [map_add, hτ, hτ'],
    by rw [map_add, map_add, hρτ, hρτ'], (cls_add _ _ hρ hρ' _).symm⟩
namespace IsCechShortExact
variable (hS : IsCechShortExact U f g)
include hS
lemma push_injective' (n : ℕ) : Function.Injective (push U f n) :=
  push_injective U f n fun i => hS.injective i
lemma push_surjective (n : ℕ) (σ : Cochain Q U n) : ∃ τ, push U g n τ = σ := by
  choose τ hτ using fun i => hS.surjective i (σ i)
  exact ⟨τ, funext hτ⟩
lemma push_exact (n : ℕ) (τ : Cochain I U n) (hτ : push U g n τ = 0) :
    ∃ α, push U f n α = τ := by
  choose α hα using fun i => hS.exact i (τ i) (congrFun hτ i)
  exact ⟨α, funext hα⟩
lemma push_push (n : ℕ) (α : Cochain F U n) : push U g n (push U f n α) = 0 := by
  rw [push_comp, hS.zero, push_zero']
lemma exists_deltaRel {n : ℕ} (σ : Cochain Q U n) (hσ : d Q U n σ = 0) :
    ∃ c, DeltaRel U f g n σ c := by
  obtain ⟨τ, hτ⟩ := hS.push_surjective n σ
  have h0 : push U g (n + 1) (d I U n τ) = 0 := by rw [push_d, hτ, hσ]
  obtain ⟨ρ, hρ⟩ := hS.push_exact (n + 1) _ h0
  have hρc : d F U (n + 1) ρ = 0 := by
    apply hS.push_injective' (n + 2)
    rw [map_zero, push_d, hρ, d_d]
  exact ⟨cls ρ hρc, τ, ρ, hρc, hτ, hρ, rfl⟩
lemma deltaRel_unique {n : ℕ} {σ : Cochain Q U n} {c c' : cechH F U (n + 1)}
    (h : DeltaRel U f g n σ c) (h' : DeltaRel U f g n σ c') : c = c' := by
  obtain ⟨τ, ρ, hρ, hτ, hρτ, rfl⟩ := h
  obtain ⟨τ', ρ', hρ', hτ', hρτ', rfl⟩ := h'
  rw [cls_eq_cls_iff, coboundaries_succ]
  obtain ⟨α, hα⟩ := hS.push_exact n (τ' - τ) (by rw [map_sub, hτ, hτ', sub_self])
  refine AddMonoidHom.mem_range.2 ⟨α, ?_⟩
  apply hS.push_injective' (n + 1)
  rw [push_d, hα, map_sub, map_sub, hρτ, hρτ']
def deltaFun (n : ℕ) (σ : cocycles Q U n) : cechH F U (n + 1) :=
  Classical.choose (hS.exists_deltaRel σ.1 ((mem_cocycles _).1 σ.2))
lemma deltaFun_spec (n : ℕ) (σ : cocycles Q U n) : DeltaRel U f g n σ.1 (hS.deltaFun n σ) :=
  Classical.choose_spec (hS.exists_deltaRel σ.1 ((mem_cocycles _).1 σ.2))
def delta (n : ℕ) : cocycles Q U n →+ cechH F U (n + 1) where
  toFun := hS.deltaFun n
  map_zero' := hS.deltaRel_unique (hS.deltaFun_spec n 0)
    ⟨0, 0, map_zero _, map_zero _, by rw [map_zero, map_zero], cls_zero.symm⟩
  map_add' σ σ' := hS.deltaRel_unique (hS.deltaFun_spec n (σ + σ'))
    ((hS.deltaFun_spec n σ).add (hS.deltaFun_spec n σ'))
lemma delta_spec (n : ℕ) (σ : cocycles Q U n) : DeltaRel U f g n σ.1 (hS.delta n σ) :=
  hS.deltaFun_spec n σ
lemma delta_surjective (hI : CechAcyclic I U) (n : ℕ) : Function.Surjective (hS.delta n) := by
  intro c
  obtain ⟨ρ, hρ, rfl⟩ := exists_cls c
  obtain ⟨τ, hτ⟩ := hI n (push U f (n + 1) ρ) (by rw [← push_d, hρ, map_zero])
  have hσ : d Q U n (push U g n τ) = 0 := by rw [← push_d, hτ, hS.push_push]
  exact ⟨⟨push U g n τ, (mem_cocycles _).2 hσ⟩,
    hS.deltaRel_unique (hS.delta_spec n _) ⟨τ, ρ, hρ, rfl, hτ.symm, rfl⟩⟩
lemma delta_eq_zero_iff (n : ℕ) (σ : cocycles Q U n) :
    hS.delta n σ = 0 ↔ ∃ κ : Cochain I U n, d I U n κ = 0 ∧ push U g n κ = σ := by
  constructor
  · intro h0
    obtain ⟨τ, ρ, hρ, hτ, hρτ, hc⟩ := hS.delta_spec n σ
    rw [h0, eq_comm, cls_eq_zero_iff, coboundaries_succ] at hc
    obtain ⟨β, hβ⟩ := AddMonoidHom.mem_range.1 hc
    refine ⟨τ - push U f n β, ?_, ?_⟩
    · rw [map_sub, ← hρτ, ← hβ, push_d, sub_self]
    · rw [map_sub, hS.push_push, sub_zero, hτ]
  · rintro ⟨κ, hκ, hgκ⟩
    exact hS.deltaRel_unique (hS.delta_spec n σ)
      ⟨κ, 0, map_zero _, hgκ, by rw [map_zero, hκ], cls_zero.symm⟩
lemma ker_delta_succ (hI : CechAcyclic I U) (m : ℕ) :
    (hS.delta (m + 1)).ker =
      (coboundaries Q U (m + 1)).addSubgroupOf (cocycles Q U (m + 1)) := by
  ext σ
  rw [AddMonoidHom.mem_ker, hS.delta_eq_zero_iff, AddSubgroup.mem_addSubgroupOf,
    coboundaries_succ]
  constructor
  · rintro ⟨κ, hκ, hgκ⟩
    obtain ⟨θ, hθ⟩ := hI m κ hκ
    exact AddMonoidHom.mem_range.2 ⟨push U g m θ, by rw [← push_d, hθ, hgκ]⟩
  · intro hσ
    obtain ⟨θ, hθ⟩ := AddMonoidHom.mem_range.1 hσ
    obtain ⟨θ', hθ'⟩ := hS.push_surjective m θ
    exact ⟨d I U m θ', d_d I U m θ', by rw [push_d, hθ', hθ]⟩
def deltaEquiv (hI : CechAcyclic I U) (m : ℕ) :
    cechH Q U (m + 1) ≃+ cechH F U (m + 2) :=
  (QuotientAddGroup.quotientAddEquivOfEq (hS.ker_delta_succ hI m).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective _ (hS.delta_surjective hI (m + 1)))
end IsCechShortExact
end Connecting
section Sections
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
def globalCocycle : P.obj (op ⊤) →+ cocycles P U 0 where
  toFun s := ⟨constCochain P U (fun _ => le_top) s,
    (mem_cocycles _).2 (d_constCochain P U (fun _ => le_top) s)⟩
  map_zero' := Subtype.ext (funext fun _ => map_zero _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add _ _ _)
variable (hP : Presheaf.IsSheaf (Opens.grothendieckTopology X) P) (hU : iSup U = ⊤)
include hP hU
lemma globalCocycle_surjective : Function.Surjective (globalCocycle P U) := by
  rintro ⟨κ, hκ⟩
  obtain ⟨t, ht⟩ := exists_glue P hP U ⊤ (fun _ => le_top) hU.ge κ ((mem_cocycles κ).1 hκ)
  exact ⟨t, Subtype.ext (funext ht)⟩
lemma globalCocycle_injective : Function.Injective (globalCocycle P U) := by
  refine (injective_iff_map_eq_zero _).2 fun s hs => ?_
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨P, hP⟩ : TopCat.Sheaf AddCommGrpCat.{u} X) U ⊤
    (fun _ => homOfLE le_top) hU.ge
  intro a
  have h1 := congrFun (congrArg Subtype.val hs) (fun _ : Fin 1 => a)
  have h2 := congrArg (res P (le_inter_const U a)) h1
  change res P (le_inter_const U a) (res P _ s) = res P (le_inter_const U a) 0 at h2
  rw [res_res, map_zero] at h2
  change res P le_top s = res P le_top 0
  rw [map_zero]
  exact h2
def globalCocycleEquiv : P.obj (op ⊤) ≃+ cocycles P U 0 :=
  AddEquiv.ofBijective (globalCocycle P U)
    ⟨globalCocycle_injective P U hP hU, globalCocycle_surjective P U hP hU⟩
def cechHZeroEquiv : cechH P U 0 ≃+ P.obj (op ⊤) :=
  ((QuotientAddGroup.quotientAddEquivOfEq
    (by rw [coboundaries_zero, AddSubgroup.bot_addSubgroupOf])).trans
      QuotientAddGroup.quotientBot).trans (globalCocycleEquiv P U hP hU).symm
end Sections
section Cartan
structure IsCoverSystem (B : Opens X → Prop)
    (Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop) : Prop where
  iSup_eq : ∀ (V : Opens X) {κ : Type u} (U : κ → Opens X), Good V U → iSup U = V
  inter_mem : ∀ (V : Opens X) {κ : Type u} (U : κ → Opens X), Good V U →
    ∀ {n : ℕ} (i : Fin (n + 1) → κ), B (inter U i)
  exists_refinement : ∀ V, B V → ∀ O : V → Opens X, (∀ x, x.1 ∈ O x) →
    ∃ (κ : Type u) (_ : Finite κ) (U : κ → Opens X), Good V U ∧ ∀ a, ∃ x, U a ≤ O x
variable (B : Opens X → Prop) (Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop)
def GoodAcyclic (G : TopCat.Sheaf AddCommGrpCat.{u} X) : Prop :=
  ∀ V, B V → ∀ (κ : Type u) [Finite κ] (U : κ → Opens X), Good V U → CechAcyclic G.obj U
variable {B Good} (hC : IsCoverSystem B Good)
  {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X)} (hS : S.ShortExact)
include hC hS
end Cartan
section Leray
variable {ι : Type w}
variable [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
def cechHZeroEquivH (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (U : ι → Opens X)
    (hU : iSup U = ⊤) : cechH G.obj U 0 ≃+ Sheaf.H.{w'} G 0 :=
  (cechHZeroEquiv G.obj U G.property hU).trans (Sheaf.H.equiv₀ G isTerminalTop).symm
variable {S : ShortComplex (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
  (hS : S.ShortExact) [Injective S.X₂]
def hDeltaEquiv (m : ℕ) : Sheaf.H.{w'} S.X₃ (m + 1) ≃+ Sheaf.H.{w'} S.X₁ (m + 2) :=
  AddEquiv.ofBijective (H.δ hS (m + 1) (m + 2) rfl)
    ⟨(injective_iff_map_eq_zero _).2 fun y hy => by
        obtain ⟨x, hx⟩ := H.exact₃ hS rfl y hy
        rw [← hx, H.eq_zero_of_injective S.X₂ x, map_zero],
      fun x => H.exact₁ hS rfl x (H.eq_zero_of_injective S.X₂ _)⟩
end Leray
section LerayTheorem
variable {ι : Type w} [HasExt.{w'} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  {B : Opens X → Prop} {Good : ∀ {κ : Type u}, Opens X → (κ → Opens X) → Prop}
end LerayTheorem
end
end GroundTheory.Arith.SchemeCoh


