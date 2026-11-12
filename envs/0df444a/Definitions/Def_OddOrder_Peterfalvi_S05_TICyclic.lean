-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S05_TICyclic
-- name    : OddOrder_Peterfalvi_S05_TICyclic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:41:55.509196+00:00
-- url     : https://prove2.me/theorems/6e857ae0-f319-4c49-b324-cf0785499f50
-- title:
--   Peterfalvi §5: TI-subsets with cyclic normalizers
-- statement:
--   The formal interface for the TI-cyclic normalizer setup of Peterfalvi (3.1), §5 (pp. 15–20). The setup gives a canonical TI-specialized instance of the §4 Dade hypothesis, so the §4 Dade-isometry packages are reused for the maps in (3.2)–(3.5).
--
--   Main definitions: `TICyclicHypothesis` (the ambient data of (3.1)), `toDadeHypothesis` ((3.1) as the $H(a)=1$ specialization of Hypothesis (2.2)), `SupportedOnV` (the space $\mathrm{CF}(W,V)$ used in (3.2)–(3.5)), `DadeApplication` (a TI-cyclic setup with a Dade map) and `FullDadeApplication` (including the virtual-character part).
--
--   The bundle also proves 57 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S05_TICyclic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S05_TICyclic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S03_PreliminaryCharacter
import Definitions.Def_OddOrder_Peterfalvi_S04_DadeIsometry
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_LinearCharacter
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace OddOrder.Peterfalvi.S05

open OddOrder.RepresentationTheory

open scoped Pointwise

variable {G : Type*} [Group G] [Fintype G]

/-- The ambient data in Peterfalvi (3.1).

`V` is kept as a field instead of being defined from `W`, `W1`, and `W2` so that
later sections can use the same interface for the slightly varied normalizer
setups that occur in §6 and §8. -/
structure TICyclicHypothesis (G : Type*) [Group G] [Fintype G] where
  W : Subgroup G
  W1 : Subgroup G
  W2 : Subgroup G
  W1_le_W : W1 ≤ W
  W2_le_W : W2 ≤ W
  W1_nontrivial : W1 ≠ ⊥
  W2_nontrivial : W2 ≠ ⊥
  W_sup : W1 ⊔ W2 = W
  W_disjoint : Disjoint W1 W2
  W_card_coprime : Nat.Coprime (Nat.card W1) (Nat.card W2)
  W_card_odd : Odd (Nat.card W)
  /-- (3.1): `W = W₁ × W₂` is cyclic.  Cyclicity is part of Peterfalvi's Hypothesis (3.1)
  ("`W` is cyclic of odd order"); it makes `W` abelian, so `Irr(W)` consists of linear
  characters (used to build the `ω_{ij}` family in (3.3)).  It also forces `W₁` and `W₂`
  to be cyclic and `W = W₁ × W₂` to be an internal direct product. -/
  W_cyclic : IsCyclic W
  V : Set G
  V_subset_sharp : V ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G)
  V_subset_W : V ⊆ W
  W_normalizes_V :
    ∀ (w : W) ⦃v : G⦄, v ∈ V → (w : G) * v * (w : G)⁻¹ ∈ V
  V_ti : OddOrder.GroupTheory.IsTISubset V W

namespace TICyclicHypothesis

/-- Peterfalvi (3.1), viewed as the `H(a)=1` specialization of §4 Hypothesis
(2.2). -/
def toDadeHypothesis (hyp : TICyclicHypothesis G) :
    OddOrder.Peterfalvi.S04.Hypothesis G hyp.V hyp.W :=
  OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
    hyp.V_subset_sharp hyp.V_subset_W hyp.W_normalizes_V hyp.V_ti

@[simp] theorem toDadeHypothesis_H (hyp : TICyclicHypothesis G)
    (a : {a : G // a ∈ hyp.V}) :
    (hyp.toDadeHypothesis).H a = ⊥ :=
  rfl

/-- The supported class-function space `CF(W,V)` used by (3.2)-(3.5). -/
abbrev SupportedOnV (k : Type*) [CommRing k] (hyp : TICyclicHypothesis G) :=
  OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) k hyp.V hyp.W

variable {k : Type*} [CommRing k] [StarRing k]

variable [Invertible (Nat.card G : k)]

/-- A §5 application package: a TI-cyclic setup together with a Dade map for
the induced §4 `H(a)=1` hypothesis. -/
structure DadeApplication (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)] where
  tau : OddOrder.Peterfalvi.S04.DadeIsometryData
    (G := G) (k := k) hyp.toDadeHypothesis

instance (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)] :
    CoeFun (DadeApplication (G := G) (k := k) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem coe_mk (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : k)]
    (tau : OddOrder.Peterfalvi.S04.DadeIsometryData
      (G := G) (k := k) hyp.toDadeHypothesis) :
    ((DadeApplication.mk tau : DadeApplication (G := G) (k := k) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) k hyp.V hyp.W) = tau.toDadeMap :=
  rfl

variable [Invertible (Nat.card G : ℂ)]

/-- A complex §5 application package including the virtual-character part of
the §4 Dade isometry theorem. -/
structure FullDadeApplication (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] where
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData
    (G := G) hyp.toDadeHypothesis

instance (hyp : TICyclicHypothesis G) [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)] :
    CoeFun (FullDadeApplication (G := G) hyp)
      (fun _ => OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ hyp.V hyp.W) :=
  ⟨fun app => app.tau.toDadeMap⟩

@[simp] theorem full_coe_mk (hyp : TICyclicHypothesis G)
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData
      (G := G) hyp.toDadeHypothesis) :
    ((FullDadeApplication.mk tau : FullDadeApplication (G := G) hyp) :
      OddOrder.Peterfalvi.S04.DadeMap (G := G) ℂ hyp.V hyp.W) = tau.toDadeMap :=
  rfl

theorem full_map_eq_of_mem_V {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV (G := G) ℂ hyp) {v : G} (hv : v ∈ hyp.V) :
    app.tau.toDadeMap α v =
      (α : ClassFunction hyp.W ℂ) ⟨v, hyp.V_subset_W hv⟩ := by
  exact OddOrder.Peterfalvi.S04.map_eq_of_mem_A_of_forall_H_eq_bot
    app.tau.toDadeIsometryData.isDadeMap
    (fun a => hyp.toDadeHypothesis_H a) α hv

theorem full_map_eq_zero_of_not_mem_conjugatesOfSet_V {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α : SupportedOnV (G := G) ℂ hyp) {g : G}
    (hg : g ∉ Group.conjugatesOfSet hyp.V) :
    app.tau.toDadeMap α g = 0 :=
  OddOrder.Peterfalvi.S04.map_eq_zero_of_not_mem_conjugatesOfSet_of_forall_H_eq_bot
    app.tau.toDadeIsometryData.isDadeMap
    (fun a => hyp.toDadeHypothesis_H a) α hg

theorem full_inner_eq {hyp : TICyclicHypothesis G}
    [Fintype hyp.W] [Invertible (Nat.card hyp.W : ℂ)]
    (app : FullDadeApplication (G := G) hyp)
    (α β : SupportedOnV (G := G) ℂ hyp) :
    ClassFunction.inner (app.tau.toDadeMap α) (app.tau.toDadeMap β) =
      ClassFunction.inner (α : ClassFunction hyp.W ℂ) (β : ClassFunction hyp.W ℂ) :=
  app.tau.inner_eq α β

end TICyclicHypothesis

section SupportedDimension

open scoped IsMulCommutative

open Module (finrank)

set_option backward.isDefEq.respectTransparency false in
/-- For a finite **commutative** group `H`, the class functions supported on `A ⊆ H` form a space
of dimension `|A|`.  For commutative `H` conjugation is trivial, so every function on `H` is a class
function; restriction to `A` and extension-by-zero then give a linear isomorphism
`CF(H, A) ≃ (↥A → ℂ)`.  This is the dimension input for Peterfalvi (3.4)
(`dim CF(W, V) = (w₁−1)(w₂−1)`). -/
theorem finrank_supportedSubmodule_eq_card {H : Type*} [Group H] [Finite H] [IsMulCommutative H]
    (A : Set H) :
    finrank ℂ (ClassFunction.supportedSubmodule (G := H) (k := ℂ) A) = Nat.card A := by
  classical
  have : Fintype H := Fintype.ofFinite _
  have : Fintype A := Fintype.ofFinite _
  let restr : ClassFunction.supportedSubmodule (G := H) (k := ℂ) A →ₗ[ℂ] (A → ℂ) :=
    { toFun := fun φ a => (φ : ClassFunction H ℂ) (a : H)
      map_add' := fun φ ψ => by funext a; rfl
      map_smul' := fun c φ => by funext a; rfl }
  have hbij : Function.Bijective restr := by
    constructor
    · intro φ ψ h
      apply Subtype.ext
      apply ClassFunction.ext
      intro w
      by_cases hw : w ∈ A
      · exact congrFun h ⟨w, hw⟩
      · have hφ0 : (φ : ClassFunction H ℂ) w = 0 := by
          by_contra hne
          exact hw (ClassFunction.mem_supportedSubmodule.mp φ.2 (ClassFunction.mem_support.mpr hne))
        have hψ0 : (ψ : ClassFunction H ℂ) w = 0 := by
          by_contra hne
          exact hw (ClassFunction.mem_supportedSubmodule.mp ψ.2 (ClassFunction.mem_support.mpr hne))
        rw [hφ0, hψ0]
    · intro g
      refine ⟨⟨⟨fun w => if hw : w ∈ A then g ⟨w, hw⟩ else 0, ?_⟩, ?_⟩, ?_⟩
      · intro x y
        have hxy : y * x * y⁻¹ = x := by rw [mul_comm y x, mul_inv_cancel_right]
        rw [hxy]
      · intro w hw
        rw [ClassFunction.mem_support] at hw
        by_contra hwA
        exact hw (dif_neg hwA)
      · funext a
        change (if hw : (a : H) ∈ A then g ⟨(a : H), hw⟩ else 0) = g a
        rw [dif_pos a.2]
  rw [(LinearEquiv.ofBijective restr hbij).finrank_eq, Module.finrank_fintype_fun_eq_card,
    Nat.card_eq_fintype_card]

end SupportedDimension

namespace TICyclicHypothesis

/-- **Peterfalvi (3.1)/(3.3)**: `W` is commutative.  It is cyclic by `W_cyclic`, and a cyclic
group is abelian (`MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center`).  This is
what makes every irreducible character of `W` linear, so that the `ω_{ij}` of (3.3) exhaust
`Irr(W)` (`omegaEquiv`). -/
theorem isMulCommutative_W (hyp : TICyclicHypothesis G) : IsMulCommutative hyp.W :=
  haveI := hyp.W_cyclic
  MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
    (MonoidHom.id hyp.W)
    (by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
      rw [hx]
      exact Subgroup.one_mem _)

/-- **Peterfalvi (3.3)**: the irreducible character `ω(χ)` of `W` attached to a linear character
`χ : W →* ℂˣ`.  Since `W` is abelian, every irreducible character of `W` is of this form
(`omega_surjective`) and distinct linear characters give distinct irreducible characters
(`omega_injective`); the two facts are packaged as the bijection `omegaEquiv`.  In Peterfalvi's
notation these are the `ω_{ij}` (`0 ≤ i < w₁`, `0 ≤ j < w₂`). -/
noncomputable def omega (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    IrreducibleCharacter hyp.W :=
  linearIrreducibleCharacter χ

@[simp] theorem omega_apply (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) (w : hyp.W) :
    ((hyp.omega χ : ClassFunction hyp.W ℂ)) w = (χ w : ℂ) :=
  linearClassFunction_apply χ w

/-- (3.3): each `ω(χ)` has degree one. -/
@[simp] theorem omega_apply_one (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    ((hyp.omega χ : ClassFunction hyp.W ℂ)) 1 = 1 := by
  rw [omega_apply, map_one, Units.val_one]

theorem omega_injective (hyp : TICyclicHypothesis G) :
    Function.Injective hyp.omega :=
  linearIrreducibleCharacter_injective

theorem omega_surjective (hyp : TICyclicHypothesis G) :
    Function.Surjective hyp.omega := by
  have := hyp.isMulCommutative_W
  intro χ
  obtain ⟨h, hh⟩ := χ.2.exists_linearIrreducibleCharacter_eq_of_isMulCommutative
  exact ⟨h, Subtype.ext hh⟩

/-- **Peterfalvi (3.3)**: `Irr(W) = {ω_{ij}}`, packaged as the bijection `Hom(W, ℂˣ) ≃ Irr(W)`.
Every irreducible character of the cyclic group `W` is the linear character `ω(χ)` of a unique
`χ : W →* ℂˣ`. -/
noncomputable def omegaEquiv (hyp : TICyclicHypothesis G) :
    (hyp.W →* ℂˣ) ≃ IrreducibleCharacter hyp.W :=
  Equiv.ofBijective hyp.omega ⟨hyp.omega_injective, hyp.omega_surjective⟩

@[simp] theorem omegaEquiv_apply (hyp : TICyclicHypothesis G) (χ : hyp.W →* ℂˣ) :
    hyp.omegaEquiv χ = hyp.omega χ :=
  rfl

/-- `W₁` and `W₂`, viewed inside `↥W`, intersect trivially (from `W_disjoint`). -/
theorem W1_subgroupOf_inf_W2_subgroupOf_eq_bot (hyp : TICyclicHypothesis G) :
    hyp.W1.subgroupOf hyp.W ⊓ hyp.W2.subgroupOf hyp.W = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
  have hxbot : (x : G) ∈ hyp.W1 ⊓ hyp.W2 := hx
  rw [disjoint_iff.mp hyp.W_disjoint, Subgroup.mem_bot] at hxbot
  rw [Subgroup.mem_bot]
  exact Subtype.ext hxbot

/-- `W₁` and `W₂`, viewed inside `↥W`, generate `↥W` (from `W_sup`). -/
theorem W1_subgroupOf_sup_W2_subgroupOf_eq_top (hyp : TICyclicHypothesis G) :
    hyp.W1.subgroupOf hyp.W ⊔ hyp.W2.subgroupOf hyp.W = ⊤ := by
  rw [← Subgroup.subgroupOf_sup hyp.W1_le_W hyp.W2_le_W, hyp.W_sup, Subgroup.subgroupOf_self]

section

open scoped IsMulCommutative

/-- **Peterfalvi (3.1)/(3.3)**: `W = W₁ × W₂` is an internal direct product — the multiplication
map `↥W₁ × ↥W₂ → ↥W` is a group isomorphism (`W` is abelian, `W₁ ⊓ W₂ = 1`, `W₁ ⊔ W₂ = W`).
This is what lets a linear character `ω` of `W` split as `ω_{i0}·ω_{0j}` with `ω_{i0}` trivial on
`W₂` and `ω_{0j}` trivial on `W₁`. -/
noncomputable def wProdEquiv (hyp : TICyclicHypothesis G) :
    (hyp.W1.subgroupOf hyp.W) × (hyp.W2.subgroupOf hyp.W) ≃* hyp.W :=
  haveI := hyp.isMulCommutative_W
  MulEquiv.ofBijective
    (MonoidHom.coprod (hyp.W1.subgroupOf hyp.W).subtype (hyp.W2.subgroupOf hyp.W).subtype) <| by
    constructor
    · rw [injective_iff_map_eq_one]
      rintro ⟨a, b⟩ hab
      rw [MonoidHom.coprod_apply, Subgroup.coe_subtype, Subgroup.coe_subtype] at hab
      have hain : (a : hyp.W) ∈ hyp.W1.subgroupOf hyp.W ⊓ hyp.W2.subgroupOf hyp.W := by
        refine ⟨a.2, ?_⟩
        have hinv : (a : hyp.W) = ((b : hyp.W))⁻¹ := mul_eq_one_iff_eq_inv.mp hab
        rw [hinv]
        exact (hyp.W2.subgroupOf hyp.W).inv_mem b.2
      rw [hyp.W1_subgroupOf_inf_W2_subgroupOf_eq_bot, Subgroup.mem_bot] at hain
      have hb1 : (b : hyp.W) = 1 := by rw [hain, one_mul] at hab; exact hab
      exact Prod.ext (Subtype.ext hain) (Subtype.ext hb1)
    · intro w
      have hw : w ∈ hyp.W1.subgroupOf hyp.W ⊔ hyp.W2.subgroupOf hyp.W := by
        rw [hyp.W1_subgroupOf_sup_W2_subgroupOf_eq_top]; exact Subgroup.mem_top w
      rw [Subgroup.mem_sup] at hw
      obtain ⟨x, hx, y, hy, hxy⟩ := hw
      refine ⟨(⟨x, hx⟩, ⟨y, hy⟩), ?_⟩
      rw [MonoidHom.coprod_apply, Subgroup.coe_subtype, Subgroup.coe_subtype]
      exact hxy

@[simp] theorem wProdEquiv_apply (hyp : TICyclicHypothesis G)
    (p : (hyp.W1.subgroupOf hyp.W) × (hyp.W2.subgroupOf hyp.W)) :
    (hyp.wProdEquiv p : hyp.W) = (p.1 : hyp.W) * (p.2 : hyp.W) := by
  have := hyp.isMulCommutative_W
  rfl

end

/-- Projection `↥W →* ↥W` onto the `W₁`-component (image in `W₁`, kills the `W₂`-component),
through the internal-product iso `wProdEquiv`. -/
noncomputable def wProj1 (hyp : TICyclicHypothesis G) : hyp.W →* hyp.W :=
  (hyp.W1.subgroupOf hyp.W).subtype.comp
    ((MonoidHom.fst _ _).comp hyp.wProdEquiv.symm.toMonoidHom)

/-- Projection `↥W →* ↥W` onto the `W₂`-component. -/
noncomputable def wProj2 (hyp : TICyclicHypothesis G) : hyp.W →* hyp.W :=
  (hyp.W2.subgroupOf hyp.W).subtype.comp
    ((MonoidHom.snd _ _).comp hyp.wProdEquiv.symm.toMonoidHom)

@[simp] theorem wProj1_apply (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wProj1 w = ((hyp.wProdEquiv.symm w).1 : hyp.W) := rfl

@[simp] theorem wProj2_apply (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wProj2 w = ((hyp.wProdEquiv.symm w).2 : hyp.W) := rfl

/-- Reconstruction from the internal direct product: `w = (W₁-part of w) · (W₂-part of w)`. -/
theorem wProj1_mul_wProj2 (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wProj1 w * hyp.wProj2 w = w := by
  rw [wProj1_apply, wProj2_apply, ← hyp.wProdEquiv_apply, MulEquiv.apply_symm_apply]

/-- Factor projection `↥W →* ↥W₁`, used to lift a character `χ₁ : ↥W₁ →* ℂˣ` to the `ω_{i0}` of
`W` as `χ₁.comp wFst` (`χ₁` on the `W₁`-component, trivial on `W₂`). -/
noncomputable def wFst (hyp : TICyclicHypothesis G) :
    hyp.W →* hyp.W1.subgroupOf hyp.W :=
  (MonoidHom.fst _ _).comp hyp.wProdEquiv.symm.toMonoidHom

/-- Factor projection `↥W →* ↥W₂`. -/
noncomputable def wSnd (hyp : TICyclicHypothesis G) :
    hyp.W →* hyp.W2.subgroupOf hyp.W :=
  (MonoidHom.snd _ _).comp hyp.wProdEquiv.symm.toMonoidHom

@[simp] theorem wFst_apply (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wFst w = (hyp.wProdEquiv.symm w).1 := rfl

@[simp] theorem wSnd_apply (hyp : TICyclicHypothesis G) (w : hyp.W) :
    hyp.wSnd w = (hyp.wProdEquiv.symm w).2 := rfl

/-- `wFst` kills `W₂`: hence `χ₁.comp wFst` (an `ω_{i0}`) is trivial on `W₂`. -/
theorem wFst_eq_one_of_mem_W2 (hyp : TICyclicHypothesis G) {w : hyp.W}
    (hw : w ∈ hyp.W2.subgroupOf hyp.W) : hyp.wFst w = 1 := by
  have hsymm : hyp.wProdEquiv.symm w = (1, ⟨w, hw⟩) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  simp [wFst_apply, hsymm]

/-- `wSnd` kills `W₁`: hence `χ₂.comp wSnd` (an `ω_{0j}`) is trivial on `W₁`. -/
theorem wSnd_eq_one_of_mem_W1 (hyp : TICyclicHypothesis G) {w : hyp.W}
    (hw : w ∈ hyp.W1.subgroupOf hyp.W) : hyp.wSnd w = 1 := by
  have hsymm : hyp.wProdEquiv.symm w = (⟨w, hw⟩, 1) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  simp [wSnd_apply, hsymm]

/-- The TI-subset `V = W ∖ (W₁ ∪ W₂)` of Peterfalvi (3.4).  The field `hyp.V` is kept abstract so
that §6/§8 can reuse the same interface; the (3.x) results that need the explicit shape take the
hypothesis `hVeq : hyp.V = hyp.Vdiff`. -/
def Vdiff (hyp : TICyclicHypothesis G) : Set G :=
  (hyp.W : Set G) \ ((hyp.W1 : Set G) ∪ (hyp.W2 : Set G))

@[simp] theorem mem_Vdiff (hyp : TICyclicHypothesis G) {g : G} :
    g ∈ hyp.Vdiff ↔ g ∈ hyp.W ∧ g ∉ hyp.W1 ∧ g ∉ hyp.W2 := by
  simp only [Vdiff, Set.mem_sdiff, Set.mem_union, SetLike.mem_coe, not_or]

section

open scoped IsMulCommutative

/-- **Peterfalvi (3.4)**: the class function `α = (1_W - ω_{i0})(1_W - ω_{0j})` on `W`, where
`ω_{i0} = χ₁ ∘ wFst` is trivial on `W₂` and `ω_{0j} = χ₂ ∘ wSnd` is trivial on `W₁`.  Expanding the
product gives Peterfalvi's `α_{ij} = 1_W - ω_{i0} - ω_{0j} + ω_{ij}`.  For nontrivial `χ₁` and `χ₂`
the family `(α_{ij})` is a basis of `CF(W, V)` with `V = W ∖ (W₁ ∪ W₂)`; the product shape makes
`α` vanish on `W₁ ∪ W₂`, hence supported on `V` (`alphaCF_mem_supportedSubmodule`). -/
noncomputable def alphaCF (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ClassFunction hyp.W ℂ :=
  ⟨fun w => (1 - (χ₁ (hyp.wFst w) : ℂ)) * (1 - (χ₂ (hyp.wSnd w) : ℂ)), by
    have := hyp.isMulCommutative_W
    intro g h
    have hg : (h * g * h⁻¹ : hyp.W) = g := by rw [mul_comm h g, mul_inv_cancel_right]
    rw [hg]⟩

end

@[simp] theorem alphaCF_apply (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    (w : hyp.W) :
    (hyp.alphaCF χ₁ χ₂ : ClassFunction hyp.W ℂ) w
      = (1 - (χ₁ (hyp.wFst w) : ℂ)) * (1 - (χ₂ (hyp.wSnd w) : ℂ)) :=
  rfl

/-- `α` vanishes on `W₂`: there the `(1_W - ω_{i0})` factor is `0`, because `wFst` kills `W₂`. -/
theorem alphaCF_eq_zero_of_mem_W2_subgroupOf (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W2.subgroupOf hyp.W) :
    (hyp.alphaCF χ₁ χ₂ : ClassFunction hyp.W ℂ) w = 0 := by
  rw [alphaCF_apply, hyp.wFst_eq_one_of_mem_W2 hw, map_one, Units.val_one, sub_self, zero_mul]

/-- `α` vanishes on `W₁`: there the `(1_W - ω_{0j})` factor is `0`, because `wSnd` kills `W₁`. -/
theorem alphaCF_eq_zero_of_mem_W1_subgroupOf (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ)
    {w : hyp.W} (hw : w ∈ hyp.W1.subgroupOf hyp.W) :
    (hyp.alphaCF χ₁ χ₂ : ClassFunction hyp.W ℂ) w = 0 := by
  rw [alphaCF_apply, hyp.wSnd_eq_one_of_mem_W1 hw, map_one, Units.val_one, sub_self, mul_zero]

/-- **Peterfalvi (3.4)**: `α = (1_W - ω_{i0})(1_W - ω_{0j})` is supported on `V = W ∖ (W₁ ∪ W₂)`,
hence lies in `CF(W, V)`.  This is the membership `α_{ij} ∈ CF(W, V)` of (3.4). -/
theorem alphaCF_mem_supportedSubmodule (hyp : TICyclicHypothesis G)
    (hVeq : hyp.V = hyp.Vdiff)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (hyp.alphaCF χ₁ χ₂ : ClassFunction hyp.W ℂ) ∈
      ClassFunction.supportedSubmodule
        (OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W) := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro w hw
  rw [ClassFunction.mem_support] at hw
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hVeq, mem_Vdiff]
  refine ⟨w.2, ?_, ?_⟩
  · intro h1
    exact hw (hyp.alphaCF_eq_zero_of_mem_W1_subgroupOf χ₁ χ₂
      ((Subgroup.mem_subgroupOf).mpr h1))
  · intro h2
    exact hw (hyp.alphaCF_eq_zero_of_mem_W2_subgroupOf χ₁ χ₂
      ((Subgroup.mem_subgroupOf).mpr h2))

/-- **Peterfalvi (3.4)**: `α_{ij}` packaged as an element of `CF(W, V) = SupportedOnV`. -/
noncomputable def alpha (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    SupportedOnV ℂ hyp :=
  ⟨hyp.alphaCF χ₁ χ₂, hyp.alphaCF_mem_supportedSubmodule hVeq χ₁ χ₂⟩

@[simp] theorem alpha_coe (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    ((hyp.alpha hVeq χ₁ χ₂ : SupportedOnV ℂ hyp) : ClassFunction hyp.W ℂ)
      = hyp.alphaCF χ₁ χ₂ :=
  rfl

@[simp] theorem wFst_wProdEquiv (hyp : TICyclicHypothesis G)
    (p : (hyp.W1.subgroupOf hyp.W) × (hyp.W2.subgroupOf hyp.W)) :
    hyp.wFst (hyp.wProdEquiv p) = p.1 := by
  rw [wFst_apply, MulEquiv.symm_apply_apply]

@[simp] theorem wSnd_wProdEquiv (hyp : TICyclicHypothesis G)
    (p : (hyp.W1.subgroupOf hyp.W) × (hyp.W2.subgroupOf hyp.W)) :
    hyp.wSnd (hyp.wProdEquiv p) = p.2 := by
  rw [wSnd_apply, MulEquiv.symm_apply_apply]

/-- Reconstruction `x = (W₁-part) · (W₂-part)` through `wFst`/`wSnd`. -/
theorem eq_wFst_mul_wSnd (hyp : TICyclicHypothesis G) (x : hyp.W) :
    x = (hyp.wFst x : hyp.W) * (hyp.wSnd x : hyp.W) := by
  conv_lhs => rw [← hyp.wProdEquiv.apply_symm_apply x]
  rw [hyp.wProdEquiv_apply]
  rfl

/-- `x` lies in `W₂` iff its `W₁`-component is trivial. -/
theorem mem_W2_subgroupOf_iff_wFst_eq_one (hyp : TICyclicHypothesis G) {x : hyp.W} :
    x ∈ hyp.W2.subgroupOf hyp.W ↔ hyp.wFst x = 1 := by
  refine ⟨hyp.wFst_eq_one_of_mem_W2, fun h => ?_⟩
  have hx := hyp.eq_wFst_mul_wSnd x
  rw [h] at hx
  simp only [OneMemClass.coe_one, one_mul] at hx
  rw [hx]
  exact SetLike.coe_mem _

/-- `x` lies in `W₁` iff its `W₂`-component is trivial. -/
theorem mem_W1_subgroupOf_iff_wSnd_eq_one (hyp : TICyclicHypothesis G) {x : hyp.W} :
    x ∈ hyp.W1.subgroupOf hyp.W ↔ hyp.wSnd x = 1 := by
  refine ⟨hyp.wSnd_eq_one_of_mem_W1, fun h => ?_⟩
  have hx := hyp.eq_wFst_mul_wSnd x
  rw [h] at hx
  simp only [OneMemClass.coe_one, mul_one] at hx
  rw [hx]
  exact SetLike.coe_mem _

/-- The bijection behind the count `|V| = (w₁−1)(w₂−1)`: via the internal product `W = W₁ × W₂`,
an element of `V = W ∖ (W₁ ∪ W₂)` is exactly a pair of a nontrivial `W₁`-component and a nontrivial
`W₂`-component. -/
noncomputable def supportInVdiffEquiv (hyp : TICyclicHypothesis G) :
    ↥(OddOrder.Peterfalvi.S04.supportInSubgroup hyp.Vdiff hyp.W) ≃
      ({a : (hyp.W1.subgroupOf hyp.W) // a ≠ 1} ×
        {b : (hyp.W2.subgroupOf hyp.W) // b ≠ 1}) where
  toFun := fun x =>
    have hx : (x.1 : G) ∈ hyp.W ∧ (x.1 : G) ∉ hyp.W1 ∧ (x.1 : G) ∉ hyp.W2 :=
      hyp.mem_Vdiff.mp (OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp x.2)
    (⟨hyp.wFst x.1, fun h =>
        hx.2.2 ((Subgroup.mem_subgroupOf).mp ((hyp.mem_W2_subgroupOf_iff_wFst_eq_one).mpr h))⟩,
     ⟨hyp.wSnd x.1, fun h =>
        hx.2.1 ((Subgroup.mem_subgroupOf).mp ((hyp.mem_W1_subgroupOf_iff_wSnd_eq_one).mpr h))⟩)
  invFun := fun p =>
    ⟨hyp.wProdEquiv (p.1.1, p.2.1), by
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, hyp.mem_Vdiff]
      refine ⟨SetLike.coe_mem _, ?_, ?_⟩
      · intro hW1
        refine p.2.2 ?_
        have h := (hyp.mem_W1_subgroupOf_iff_wSnd_eq_one).mp ((Subgroup.mem_subgroupOf).mpr hW1)
        rwa [hyp.wSnd_wProdEquiv] at h
      · intro hW2
        refine p.1.2 ?_
        have h := (hyp.mem_W2_subgroupOf_iff_wFst_eq_one).mp ((Subgroup.mem_subgroupOf).mpr hW2)
        rwa [hyp.wFst_wProdEquiv] at h⟩
  left_inv := fun x => by
    apply Subtype.ext
    change hyp.wProdEquiv (hyp.wFst x.1, hyp.wSnd x.1) = x.1
    rw [wFst_apply, wSnd_apply, Prod.mk.eta, MulEquiv.apply_symm_apply]
  right_inv := fun p => by
    apply Prod.ext
    · apply Subtype.ext
      change hyp.wFst (hyp.wProdEquiv (p.1.1, p.2.1)) = p.1.1
      rw [wFst_wProdEquiv]
    · apply Subtype.ext
      change hyp.wSnd (hyp.wProdEquiv (p.1.1, p.2.1)) = p.2.1
      rw [wSnd_wProdEquiv]

/-- The count `|V| = (w₁ − 1)(w₂ − 1)`, `V = W ∖ (W₁ ∪ W₂)`. -/
theorem card_supportInSubgroup_Vdiff (hyp : TICyclicHypothesis G) :
    Nat.card ↥(OddOrder.Peterfalvi.S04.supportInSubgroup hyp.Vdiff hyp.W)
      = (Nat.card hyp.W1 - 1) * (Nat.card hyp.W2 - 1) := by
  classical
  have : Finite G := Finite.of_fintype G
  have : Fintype ↥(hyp.W1.subgroupOf hyp.W) := Fintype.ofFinite _
  have : Fintype ↥(hyp.W2.subgroupOf hyp.W) := Fintype.ofFinite _
  rw [Nat.card_congr hyp.supportInVdiffEquiv, Nat.card_prod]
  have h1 : Nat.card {a : (hyp.W1.subgroupOf hyp.W) // a ≠ 1} = Nat.card hyp.W1 - 1 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.W1_le_W).toEquiv,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  have h2 : Nat.card {b : (hyp.W2.subgroupOf hyp.W) // b ≠ 1} = Nat.card hyp.W2 - 1 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.W2_le_W).toEquiv,
      Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [h1, h2]

/-- **Peterfalvi (3.4)**: `dim_ℂ CF(W, V) = (w₁ − 1)(w₂ − 1)` with `V = W ∖ (W₁ ∪ W₂)` and
`w_k = |W_k|`.  Together with the linear independence of the `α_{ij}`, this dimension count gives
that the family `(α_{ij})` (`1 ≤ i < w₁`, `1 ≤ j < w₂`) is a basis of `CF(W, V)`. -/
theorem finrank_supportedOnV (hyp : TICyclicHypothesis G) (hVeq : hyp.V = hyp.Vdiff) :
    Module.finrank ℂ (SupportedOnV ℂ hyp) = (Nat.card hyp.W1 - 1) * (Nat.card hyp.W2 - 1) := by
  have : Finite G := Finite.of_fintype G
  have : Fintype ↥hyp.W := Fintype.ofFinite _
  have : IsMulCommutative ↥hyp.W := hyp.isMulCommutative_W
  change Module.finrank ℂ
      ↥(ClassFunction.supportedSubmodule (G := ↥hyp.W)
        (OddOrder.Peterfalvi.S04.supportInSubgroup hyp.V hyp.W))
      = (Nat.card hyp.W1 - 1) * (Nat.card hyp.W2 - 1)
  rw [finrank_supportedSubmodule_eq_card, hVeq, hyp.card_supportInSubgroup_Vdiff]

/-- **Peterfalvi (3.4)**: `α_{ij} = 1_W - ω_{i0} - ω_{0j} + ω_{ij}` as the expansion of the product
`(1_W - ω_{i0})(1_W - ω_{0j})` into the `ω`-family, where `ω_{i0} = ω(χ₁∘wFst)`,
`ω_{0j} = ω(χ₂∘wSnd)`, `ω_{ij} = ω((χ₁∘wFst)·(χ₂∘wSnd))` and `1_W = ω(1)`.  This is the bridge from
the product definition `alphaCF` to the linear `Irr(W)`-combination used in the Fourier argument. -/
theorem alphaCF_eq_omega_combination (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.alphaCF χ₁ χ₂ =
      (hyp.omega 1 : ClassFunction hyp.W ℂ) - hyp.omega (χ₁.comp hyp.wFst)
        - hyp.omega (χ₂.comp hyp.wSnd) + hyp.omega ((χ₁.comp hyp.wFst) * (χ₂.comp hyp.wSnd)) := by
  ext w
  simp only [alphaCF_apply, ClassFunction.sub_apply, ClassFunction.add_apply, omega_apply,
    MonoidHom.comp_apply, MonoidHom.one_apply, MonoidHom.mul_apply, Units.val_mul, Units.val_one]
  ring

/-- The `ω`-family is orthonormal (diagonal): `⟨ω(χ), ω(χ)⟩ = 1`. -/
theorem omega_inner_self (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (χ : hyp.W →* ℂˣ) :
    ClassFunction.inner (hyp.omega χ : ClassFunction hyp.W ℂ)
      (hyp.omega χ : ClassFunction hyp.W ℂ) = 1 := by
  rw [irreducibleCharacter_inner, if_pos rfl]

/-- The `ω`-family is orthonormal (off-diagonal): distinct linear characters give distinct
irreducible characters (`omega_injective`), so `⟨ω(χ), ω(χ')⟩ = 0` for `χ ≠ χ'`. -/
theorem omega_inner_ne (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] {χ χ' : hyp.W →* ℂˣ} (h : χ ≠ χ') :
    ClassFunction.inner (hyp.omega χ : ClassFunction hyp.W ℂ)
      (hyp.omega χ' : ClassFunction hyp.W ℂ) = 0 := by
  rw [irreducibleCharacter_inner, if_neg (fun hc => h (hyp.omega_injective hc))]

/-- `wFst` restricted to `W₁` is the identity (the `W₁`-component of a `W₁`-element is itself). -/
theorem wFst_W1_subtype (hyp : TICyclicHypothesis G)
    (w : (hyp.W1.subgroupOf hyp.W)) :
    hyp.wFst ((hyp.W1.subgroupOf hyp.W).subtype w) = w := by
  have hsymm : hyp.wProdEquiv.symm ((hyp.W1.subgroupOf hyp.W).subtype w) = (w, 1) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  rw [wFst_apply, hsymm]

/-- `wSnd` kills `W₁` (the `W₂`-component of a `W₁`-element is trivial). -/
theorem wSnd_W1_subtype (hyp : TICyclicHypothesis G)
    (w : (hyp.W1.subgroupOf hyp.W)) :
    hyp.wSnd ((hyp.W1.subgroupOf hyp.W).subtype w) = 1 := by
  have hsymm : hyp.wProdEquiv.symm ((hyp.W1.subgroupOf hyp.W).subtype w) = (w, 1) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  rw [wSnd_apply, hsymm]

/-- `wFst` kills `W₂`. -/
theorem wFst_W2_subtype (hyp : TICyclicHypothesis G)
    (w : (hyp.W2.subgroupOf hyp.W)) :
    hyp.wFst ((hyp.W2.subgroupOf hyp.W).subtype w) = 1 := by
  have hsymm : hyp.wProdEquiv.symm ((hyp.W2.subgroupOf hyp.W).subtype w) = (1, w) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  rw [wFst_apply, hsymm]

/-- `wSnd` restricted to `W₂` is the identity. -/
theorem wSnd_W2_subtype (hyp : TICyclicHypothesis G)
    (w : (hyp.W2.subgroupOf hyp.W)) :
    hyp.wSnd ((hyp.W2.subgroupOf hyp.W).subtype w) = w := by
  have hsymm : hyp.wProdEquiv.symm ((hyp.W2.subgroupOf hyp.W).subtype w) = (1, w) := by
    apply hyp.wProdEquiv.injective
    rw [MulEquiv.apply_symm_apply, hyp.wProdEquiv_apply]
    simp
  rw [wSnd_apply, hsymm]

/-- **Injectivity of the dual `Ŵ₁ × Ŵ₂ → Ŵ`** (`(χ₁, χ₂) ↦ χ₁∘wFst · χ₂∘wSnd`): composing with the
`W₁`- and `W₂`-inclusions recovers `χ₁` and `χ₂`.  This is the character-group counterpart of the
internal product `W = W₁ × W₂` (`wProdEquiv`) and is what makes the `ω_{ij}` pairwise distinct. -/
theorem comp_mul_injective (hyp : TICyclicHypothesis G)
    {χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (h : χ₁.comp hyp.wFst * χ₂.comp hyp.wSnd = χ₁'.comp hyp.wFst * χ₂'.comp hyp.wSnd) :
    χ₁ = χ₁' ∧ χ₂ = χ₂' := by
  refine ⟨MonoidHom.ext fun w => ?_, MonoidHom.ext fun w => ?_⟩
  · have hw := congrArg (fun f : hyp.W →* ℂˣ => f ((hyp.W1.subgroupOf hyp.W).subtype w)) h
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, hyp.wFst_W1_subtype,
      hyp.wSnd_W1_subtype, map_one, mul_one] at hw
    exact hw
  · have hw := congrArg (fun f : hyp.W →* ℂˣ => f ((hyp.W2.subgroupOf hyp.W).subtype w)) h
    simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, hyp.wFst_W2_subtype,
      hyp.wSnd_W2_subtype, map_one, one_mul] at hw
    exact hw

/-- `ω_{ij} = χ₁∘wFst · χ₂∘wSnd`, the linear character of `W` whose value at `Irr(W)` is `ω_{ij}`;
its image under `ω` is Peterfalvi's `ω_{ij}`. -/
noncomputable def omegaProdChar (hyp : TICyclicHypothesis G) (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ)
    (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) : hyp.W →* ℂˣ :=
  χ₁.comp hyp.wFst * χ₂.comp hyp.wSnd

theorem omegaProdChar_one_left (hyp : TICyclicHypothesis G)
    (χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdChar 1 χ₂ = χ₂.comp hyp.wSnd := by
  rw [omegaProdChar, MonoidHom.one_comp]
  exact one_mul (χ₂.comp hyp.wSnd)

theorem omegaProdChar_one_right (hyp : TICyclicHypothesis G)
    (χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) :
    hyp.omegaProdChar χ₁ 1 = χ₁.comp hyp.wFst := by
  rw [omegaProdChar, MonoidHom.one_comp]
  exact mul_one (χ₁.comp hyp.wFst)

theorem omegaProdChar_one_one (hyp : TICyclicHypothesis G) :
    hyp.omegaProdChar 1 1 = 1 := by
  rw [omegaProdChar, MonoidHom.one_comp, MonoidHom.one_comp]
  exact one_mul (1 : hyp.W →* ℂˣ)

theorem omegaProdChar_inj (hyp : TICyclicHypothesis G)
    {χ₁ χ₁' : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {χ₂ χ₂' : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (h : hyp.omegaProdChar χ₁ χ₂ = hyp.omegaProdChar χ₁' χ₂') : χ₁ = χ₁' ∧ χ₂ = χ₂' :=
  hyp.comp_mul_injective h

/-- `1_W ≠ ω_{ij}` for `i ≠ 0` (i.e. `a₁ ≠ 1`): `ω_{ij}` is nontrivial unless both indices are. -/
theorem one_ne_omegaProdChar (hyp : TICyclicHypothesis G)
    {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (ha₁ : a₁ ≠ 1)
    (a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) :
    (1 : hyp.W →* ℂˣ) ≠ hyp.omegaProdChar a₁ a₂ := by
  intro h
  rw [← hyp.omegaProdChar_one_one] at h
  exact ha₁ (hyp.omegaProdChar_inj h).1.symm

/-- `ω_{i0} ≠ ω_{kl}` when `l ≠ 0` (`a₂ ≠ 1`): a `W₂`-trivial character is not an `ω_{kl}` with a
nontrivial `W₂`-part. -/
theorem comp_wFst_ne_omegaProdChar (hyp : TICyclicHypothesis G)
    (b₁ a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ) {a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (ha₂ : a₂ ≠ 1) :
    b₁.comp hyp.wFst ≠ hyp.omegaProdChar a₁ a₂ := by
  intro h
  rw [← hyp.omegaProdChar_one_right b₁] at h
  exact ha₂ (hyp.omegaProdChar_inj h).2.symm

/-- `ω_{0j} ≠ ω_{kl}` when `k ≠ 0` (`a₁ ≠ 1`). -/
theorem comp_wSnd_ne_omegaProdChar (hyp : TICyclicHypothesis G)
    (b₂ a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ) {a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ}
    (ha₁ : a₁ ≠ 1) :
    b₂.comp hyp.wSnd ≠ hyp.omegaProdChar a₁ a₂ := by
  intro h
  rw [← hyp.omegaProdChar_one_left b₂] at h
  exact ha₁ (hyp.omegaProdChar_inj h).1.symm

/-- Distinct index pairs give distinct `ω_{ij}` (`omegaProdChar` is injective). -/
theorem omegaProdChar_ne (hyp : TICyclicHypothesis G)
    {b₁ a₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {b₂ a₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (h : ¬ (b₁ = a₁ ∧ b₂ = a₂)) :
    hyp.omegaProdChar b₁ b₂ ≠ hyp.omegaProdChar a₁ a₂ :=
  fun heq => h (hyp.omegaProdChar_inj heq)

/-- **Peterfalvi (3.4), diagonal**: `⟨α_{ij}, ω_{ij}⟩ = 1` for `i, j ≥ 1`.  Computed from the
expansion `α = 1 - ω_{i0} - ω_{0j} + ω_{ij}` and orthonormality: only the `ω_{ij}` term survives. -/
theorem alpha_inner_omega_self (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    {p₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} (hp₁ : p₁ ≠ 1)
    {p₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ} (hp₂ : p₂ ≠ 1) :
    ClassFunction.inner (hyp.alphaCF p₁ p₂)
      (hyp.omega (hyp.omegaProdChar p₁ p₂) : ClassFunction hyp.W ℂ) = 1 := by
  rw [alphaCF_eq_omega_combination, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_left,
    show p₁.comp hyp.wFst * p₂.comp hyp.wSnd = hyp.omegaProdChar p₁ p₂ from rfl,
    hyp.omega_inner_ne (hyp.one_ne_omegaProdChar hp₁ p₂),
    hyp.omega_inner_ne (hyp.comp_wFst_ne_omegaProdChar p₁ p₁ hp₂),
    hyp.omega_inner_ne (hyp.comp_wSnd_ne_omegaProdChar p₂ p₂ hp₁),
    hyp.omega_inner_self]
  ring

/-- **Peterfalvi (3.4), off-diagonal**: `⟨α_{kl}, ω_{ij}⟩ = 0` for `(k,l) ≠ (i,j)` (`i, j ≥ 1`).
All four `ω`-terms of `α_{kl}` are orthogonal to `ω_{ij}`. -/
theorem alpha_inner_omega_ne (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)]
    {q₁ p₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ} {q₂ p₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ}
    (hp₁ : p₁ ≠ 1) (hp₂ : p₂ ≠ 1) (hne : ¬ (q₁ = p₁ ∧ q₂ = p₂)) :
    ClassFunction.inner (hyp.alphaCF q₁ q₂)
      (hyp.omega (hyp.omegaProdChar p₁ p₂) : ClassFunction hyp.W ℂ) = 0 := by
  rw [alphaCF_eq_omega_combination, ClassFunction.inner_add_left, ClassFunction.inner_sub_left,
    ClassFunction.inner_sub_left,
    show q₁.comp hyp.wFst * q₂.comp hyp.wSnd = hyp.omegaProdChar q₁ q₂ from rfl,
    hyp.omega_inner_ne (hyp.one_ne_omegaProdChar hp₁ p₂),
    hyp.omega_inner_ne (hyp.comp_wFst_ne_omegaProdChar q₁ p₁ hp₂),
    hyp.omega_inner_ne (hyp.comp_wSnd_ne_omegaProdChar q₂ p₂ hp₁),
    hyp.omega_inner_ne (hyp.omegaProdChar_ne hne)]
  ring

/-- **Pontryagin self-duality** for the cyclic factors: the character group of `W_k` (viewed inside
`W`) has the same cardinality as `W_k`.  Since `W` is cyclic, `W_k.subgroupOf W` is cyclic, hence a
finite commutative group, and `ℂ` (being algebraically closed) has enough roots of unity, so
`|Hom(W_k, ℂˣ)| = |W_k|`.  This is the count of the nontrivial-character index set behind the
`(w₁−1)(w₂−1)` basis. -/
theorem card_charGroup_subgroupOf (hyp : TICyclicHypothesis G) {H : Subgroup G}
    (hHW : H ≤ hyp.W) :
    Nat.card ((H.subgroupOf hyp.W) →* ℂˣ) = Nat.card H := by
  have := hyp.W_cyclic
  have : Finite G := Finite.of_fintype G
  have key : Nat.card ((H.subgroupOf hyp.W) →* ℂˣ) = Nat.card (H.subgroupOf hyp.W) := by
    let : CommGroup ↥(H.subgroupOf hyp.W) := IsCyclic.commGroup
    have : NeZero ((Monoid.exponent ↥(H.subgroupOf hyp.W) : ℂ)) :=
      ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
    exact CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥(H.subgroupOf hyp.W) ℂ
  rw [key, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHW).toEquiv]

/-- **Pontryagin self-duality, cyclicity half**: the character group of a cyclic factor of `W` is
itself cyclic — it is (noncanonically) isomorphic to the underlying group
(`CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity`; `ℂˣ` has enough roots of unity).  With
`card_charGroup_subgroupOf` this pins the dual as cyclic of order `|H|`, so it admits a
*power enumeration* by a generator — the structure-preserving grid indexing of Peterfalvi (3.5)
under which index negation is character inversion ((3.9.a)). -/
theorem isCyclic_charGroup_subgroupOf (hyp : TICyclicHypothesis G) {H : Subgroup G}
    (_hHW : H ≤ hyp.W) :
    IsCyclic ((H.subgroupOf hyp.W) →* ℂˣ) := by
  have := hyp.W_cyclic
  have : Finite G := Finite.of_fintype G
  let : CommGroup ↥(H.subgroupOf hyp.W) := IsCyclic.commGroup
  have : NeZero ((Monoid.exponent ↥(H.subgroupOf hyp.W) : ℂ)) :=
    ⟨Nat.cast_ne_zero.2 (NeZero.ne _)⟩
  obtain ⟨e⟩ :=
    CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity ↥(H.subgroupOf hyp.W) ℂ
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

/-- **Peterfalvi (3.4), linear independence**: the family `(α_{ij})` (`1 ≤ i < w₁`, `1 ≤ j < w₂`,
indexed by nontrivial character pairs) is linearly independent in `CF(W, V)`.  Proof by the
biorthogonal system: the dual functional `⟨·, ω_{ij}⟩` evaluates `α_{kl}` to `δ_{(k,l),(i,j)}`
(`alpha_inner_omega_self`/`_ne`). -/
theorem alphaLinearIndependent (hyp : TICyclicHypothesis G) [Finite hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff) :
    LinearIndependent ℂ
      (fun p : {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} ×
          {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} =>
        hyp.alpha hVeq p.1.1 p.2.1) := by
  have : Fintype hyp.W := Fintype.ofFinite _
  refine LinearIndependent.of_pairwise_dual_eq_zero_one _
    (fun p => (innerDual (hyp.omega (hyp.omegaProdChar p.1.1 p.2.1))).comp
      (Submodule.subtype _)) (fun p q hpq => ?_) (fun p => ?_)
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerDual_apply, alpha_coe]
    exact hyp.alpha_inner_omega_ne p.1.2 p.2.2
      (fun heq => hpq (Prod.ext (Subtype.ext heq.1) (Subtype.ext heq.2)).symm)
  · simp only [LinearMap.comp_apply, Submodule.subtype_apply, innerDual_apply, alpha_coe]
    exact hyp.alpha_inner_omega_self p.1.2 p.2.2

/-- A nontrivial subgroup of `W` has a nontrivial character (its character group is nontrivial,
having the same cardinality `> 1`).  Gives `Nonempty` of the index set of nontrivial characters. -/
theorem nonempty_charNeOne (hyp : TICyclicHypothesis G) {H : Subgroup G} (hHW : H ≤ hyp.W)
    (hH : H ≠ ⊥) : Nonempty {χ : (H.subgroupOf hyp.W) →* ℂˣ // χ ≠ 1} := by
  have : Finite G := Finite.of_fintype G
  have : Fintype ((H.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  have : Nontrivial ↥H := (Subgroup.nontrivial_iff_ne_bot H).mpr hH
  have hcard : 1 < Fintype.card ((H.subgroupOf hyp.W) →* ℂˣ) := by
    rw [← Nat.card_eq_fintype_card, hyp.card_charGroup_subgroupOf hHW]
    exact Finite.one_lt_card
  have : Nontrivial ((H.subgroupOf hyp.W) →* ℂˣ) :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨χ, hχ⟩ := exists_ne (1 : (H.subgroupOf hyp.W) →* ℂˣ)
  exact ⟨⟨χ, hχ⟩⟩

/-- **Peterfalvi (3.4)**: the family `(α_{ij})` (`1 ≤ i < w₁`, `1 ≤ j < w₂`) is a basis of
`CF(W, V)`.  Linear independence (`alphaLinearIndependent`) together with the matching count
`|{(i,j)}| = (w₁−1)(w₂−1) = dim CF(W, V)` (`card_charGroup_subgroupOf`, `finrank_supportedOnV`)
gives the basis. -/
noncomputable def alphaBasis (hyp : TICyclicHypothesis G) [Fintype hyp.W]
    [Invertible (Nat.card hyp.W : ℂ)] (hVeq : hyp.V = hyp.Vdiff) :
    Module.Basis ({χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} ×
        {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1}) ℂ (SupportedOnV ℂ hyp) := by
  classical
  haveI : Finite G := Finite.of_fintype G
  haveI : Fintype ((hyp.W1.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype ((hyp.W2.subgroupOf hyp.W) →* ℂˣ) := Fintype.ofFinite _
  haveI : Fintype {χ₁ : (hyp.W1.subgroupOf hyp.W) →* ℂˣ // χ₁ ≠ 1} := Fintype.ofFinite _
  haveI : Fintype {χ₂ : (hyp.W2.subgroupOf hyp.W) →* ℂˣ // χ₂ ≠ 1} := Fintype.ofFinite _
  haveI := hyp.nonempty_charNeOne hyp.W1_le_W hyp.W1_nontrivial
  haveI := hyp.nonempty_charNeOne hyp.W2_le_W hyp.W2_nontrivial
  refine basisOfLinearIndependentOfCardEqFinrank (hyp.alphaLinearIndependent hVeq) ?_
  rw [Fintype.card_prod, hyp.finrank_supportedOnV hVeq]
  congr 1
  · rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W1_le_W]
  · rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
      hyp.card_charGroup_subgroupOf hyp.W2_le_W]

end TICyclicHypothesis

end OddOrder.Peterfalvi.S05


