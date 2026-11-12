-- Prove2me | Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
-- name    : OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:04:31.440006+00:00
-- url     : https://prove2.me/theorems/ba30a843-c71f-4d50-badf-c2b11d643837
-- title:
--   Isaacs Ch. 3 §3E: coprime action, Glauberman's lemma, and $A$-invariant Sylow subgroups
-- statement:
--   Implements results of Isaacs, *Finite Group Theory*, §3E (coprime action), which belong to Chapter 4 but need only Schur–Zassenhaus, Sylow and Frattini: Lemma 3.24 (Glauberman: existence and conjugacy of fixed points), and Thm 3.23 (existence and conjugacy of $A$-invariant Sylow subgroups).
--
--   Main definitions: `IsCompatibleMulAction` (an automorphic action of $A$ on $G$ together with actions of both on a common set $\Omega$ that are compatible), its induced permutation representation `toPermHom` and action `toMulAction` of $G\rtimes A$ on $\Omega$, plus lemmas on solvability of $G$ and quotients inside $\Gamma=G\rtimes A$ and on the index of $G$ in $\Gamma$.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Isaacs/Ch04_Commutators/ForwardFromCh03.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_FixedSubgroup
import Definitions.Def_OddOrder_Isaacs_Ch03_SplitExtensions_Main
import Definitions.Def_OddOrder_Mathlib_SchurZassenhausConj
import Definitions.Def_OddOrder_Mathlib_SemidirectProduct

namespace OddOrder.Isaacs.Ch04

open scoped Pointwise

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open Subgroup

variable {G : Type*} [Group G]

section CompatibleAction

variable {A : Type*} [Group A] (φ : A →* MulAut G) (Ω : Type*)

/-- **Compatible action**: `A` が `G` に自己同型で作用 (`φ`), `A` と `G` が共通の
集合 `Ω` に作用しているとき, `a • (g • ω) = (φ a g) • (a • ω)` (`g` の `a` による
twist と作用が可換) を満たす条件. これは `G ⋊[φ] A` が `Ω` に自然に作用する
ための同値条件. -/
def IsCompatibleMulAction [MulAction G Ω] [MulAction A Ω] : Prop :=
  ∀ (a : A) (g : G) (ω : Ω), a • (g • ω) = (φ a g) • (a • ω)

variable {φ Ω}

/-- Compatible action から `SemidirectProduct G A φ →* Equiv.Perm Ω` を構成.
`SemidirectProduct.lift` を `(MulAction.toPermHom G Ω, MulAction.toPermHom A Ω)`
で呼ぶ. -/
noncomputable def IsCompatibleMulAction.toPermHom
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) :
    SemidirectProduct G A φ →* Equiv.Perm Ω :=
  SemidirectProduct.lift (MulAction.toPermHom G Ω) (MulAction.toPermHom A Ω) (fun a => by
    ext g ω
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAction.toPermHom_apply, MulAction.toPerm_apply, MulAut.conj_apply,
      Equiv.Perm.mul_apply]
    -- Goal: (φ a g) • ω = a • g • (a⁻¹ • ω) (RHS uses MulAut.conj which inverts).
    -- Use compatibility: a • (g • α) = (φ a g) • (a • α) with α = a⁻¹ • ω.
    have heq := h a g (a⁻¹ • ω)
    rw [smul_smul, mul_inv_cancel, one_smul] at heq
    exact heq.symm)

/-- Compatible action から `MulAction (G ⋊[φ] A) Ω` を構成 (非 instance).
`Equiv.Perm Ω` の自明作用と `compHom` の合成. -/
@[reducible]
noncomputable def IsCompatibleMulAction.toMulAction
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) :
    MulAction (SemidirectProduct G A φ) Ω :=
  MulAction.compHom Ω h.toPermHom

@[simp] lemma IsCompatibleMulAction.toMulAction_inl_smul
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) (g : G) (ω : Ω) :
    letI := h.toMulAction
    (SemidirectProduct.inl g : SemidirectProduct G A φ) • ω = g • ω := by
  let := h.toMulAction
  change h.toPermHom (SemidirectProduct.inl g) ω = g • ω
  simp [IsCompatibleMulAction.toPermHom, SemidirectProduct.lift_inl]

@[simp] lemma IsCompatibleMulAction.toMulAction_inr_smul
    [MulAction G Ω] [MulAction A Ω] (h : IsCompatibleMulAction φ Ω) (a : A) (ω : Ω) :
    letI := h.toMulAction
    (SemidirectProduct.inr a : SemidirectProduct G A φ) • ω = a • ω := by
  let := h.toMulAction
  change h.toPermHom (SemidirectProduct.inr a) ω = a • ω
  simp [IsCompatibleMulAction.toPermHom, SemidirectProduct.lift_inr]

end CompatibleAction

section Glauberman

variable {A : Type*} [Group A] [Finite A] [Finite G]

omit [Finite A] in
omit [Finite G] in
/-- `Group.IsSolvable G ⇒ Group.IsSolvable inl.range` (inl の rangeRestrict 経由). -/
private lemma isSolvable_inlRange_of_isSolvable {φ : A →* MulAut G} [Group.IsSolvable G] :
    Group.IsSolvable (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range :=
  Group.isSolvable_of_surjective (MonoidHom.rangeRestrict_surjective
    (SemidirectProduct.inl : G →* SemidirectProduct G A φ))

omit [Finite A] in
omit [Finite G] in
/-- `Group.IsSolvable A ⇒ Group.IsSolvable (Γ ⧸ inl.range)`.
`rightHom` の核が `inl.range` で `rightHom` は全射, 第一同型定理 + 同型による Group.IsSolvable
の移送. -/
private lemma isSolvable_quotient_inlRange_of_isSolvable
    {φ : A →* MulAut G} [Group.IsSolvable A] :
    Group.IsSolvable (SemidirectProduct G A φ ⧸
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range) := by
  -- Compose two isos: Γ⧸inl.range ≃ Γ⧸rightHom.ker ≃ A.
  have h_ker_eq : (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range =
      (SemidirectProduct.rightHom : SemidirectProduct G A φ →* A).ker :=
    SemidirectProduct.range_inl_eq_ker_rightHom
  have h_iso1 : SemidirectProduct G A φ ⧸
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range ≃*
      SemidirectProduct G A φ ⧸
      (SemidirectProduct.rightHom : SemidirectProduct G A φ →* A).ker :=
    QuotientGroup.quotientMulEquivOfEq h_ker_eq
  have h_iso2 :
      SemidirectProduct G A φ ⧸
        (SemidirectProduct.rightHom : SemidirectProduct G A φ →* A).ker ≃* A :=
    QuotientGroup.quotientKerEquivOfSurjective _ SemidirectProduct.rightHom_surjective
  let h_iso : A ≃* SemidirectProduct G A φ ⧸
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range :=
    (h_iso1.trans h_iso2).symm
  exact Group.isSolvable_of_surjective (f := h_iso.toMonoidHom) h_iso.surjective

omit [Finite A] in
/-- `inl.range` の `Γ = G ⋊ A` における index は `Nat.card A`. -/
private lemma inlRange_index_eq_card_A {φ : A →* MulAut G} :
    (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range.index = Nat.card A := by
  have h_card_Gamma : Nat.card (SemidirectProduct G A φ) = Nat.card G * Nat.card A :=
    SemidirectProduct.card
  have h_card_inlG : Nat.card
      (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range = Nat.card G :=
    Nat.card_range_of_injective SemidirectProduct.inl_injective
  have key := Subgroup.card_mul_index
    (H := (SemidirectProduct.inl : G →* SemidirectProduct G A φ).range)
  rw [h_card_inlG, h_card_Gamma] at key
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos key

/-- **Isaacs Lemma 3.24(a) Glauberman fixed-point lemma**:
Let `A` act via automorphisms on `G`, where `A`, `G` are finite groups with `(|A|, |G|) = 1`,
and at least one of `A` or `G` is solvable.
Suppose `A` and `G` both act on a nonempty set `Ω`, where `G` acts transitively, and the
compatibility condition `a • (g • ω) = (φ a g) • (a • ω)` holds.
Then there exists an `A`-invariant element `α ∈ Ω`.

**証明** (Isaacs p.98): `Γ := G ⋊[φ] A`, choose `α ∈ Ω`, `U := stabilizer Γ α`.
`UG = Γ` (since `G` transitive). `U ∩ G ⊴ U`, `|U:U∩G| = |Γ:G| = |A|` coprime to `|U∩G|`.
Schur-Zassenhaus existence in `U` gives complement `H` of `U ∩ G` in `U`. `H` is also
complement of `G` in `Γ`. `inr(A)` is too. SZ conjugacy: `H = (inr A)^x` for `x ∈ inl(G)`.
Then `x⁻¹ • α` is `A`-invariant. -/
theorem glauberman_fixed_point_exists
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {Ω : Type*} [MulAction G Ω] [MulAction A Ω] [Nonempty Ω]
    (h : IsCompatibleMulAction φ Ω) (hG_trans : MulAction.IsPretransitive G Ω) :
    ∃ α : Ω, ∀ a : A, a • α = α := by
  let := h.toMulAction
  -- Notation.
  set α₀ : Ω := Classical.arbitrary Ω with hα₀_def
  set Γ := SemidirectProduct G A φ with hΓ_def
  set inlG : Subgroup Γ := (SemidirectProduct.inl : G →* Γ).range with hinlG_def
  set inrA : Subgroup Γ := (SemidirectProduct.inr : A →* Γ).range with hinrA_def
  set U : Subgroup Γ := MulAction.stabilizer Γ α₀ with hU_def
  -- inlG normal in Γ.
  have hinlG_normal : inlG.Normal := by
    rw [hinlG_def, SemidirectProduct.range_inl_eq_ker_rightHom]; infer_instance
  -- inlG.index = Nat.card A.
  have h_index_A : inlG.index = Nat.card A := inlRange_index_eq_card_A
  -- Nat.card inlG = Nat.card G.
  have h_card_inlG : Nat.card inlG = Nat.card G := by
    rw [hinlG_def]; exact Nat.card_range_of_injective SemidirectProduct.inl_injective
  -- Coprime |inlG| |inlG.index|.
  have h_coprime_inlG : Nat.Coprime (Nat.card inlG) inlG.index := by
    rw [h_card_inlG, h_index_A]; exact hCop.symm
  -- Solvability transfer to inlG or Γ/inlG.
  have hSolv_inlG : Group.IsSolvable inlG ∨ Group.IsSolvable (Γ ⧸ inlG) := by
    rcases hSolv with hA | hG
    · exact Or.inr (isSolvable_quotient_inlRange_of_isSolvable (φ := φ))
    · exact Or.inl (isSolvable_inlRange_of_isSolvable (φ := φ))
  -- Step 1: U ⊔ inlG = ⊤.
  have h_UG_top : U ⊔ inlG = ⊤ := by
    rw [eq_top_iff]; intro γ _
    obtain ⟨g, hg⟩ := hG_trans.exists_smul_eq α₀ (γ • α₀)
    -- inl(g) • α₀ = γ • α₀.
    have h_eq : (SemidirectProduct.inl g : Γ) • α₀ = γ • α₀ := by
      rw [show ((SemidirectProduct.inl g : Γ) • α₀ : Ω) = g • α₀ from
        IsCompatibleMulAction.toMulAction_inl_smul h g α₀]
      exact hg
    -- inl(g)⁻¹ * γ ∈ U.
    have h_in_U : (SemidirectProduct.inl g : Γ)⁻¹ * γ ∈ U := by
      rw [hU_def, MulAction.mem_stabilizer_iff, mul_smul]
      rw [show (γ • α₀ : Ω) = (SemidirectProduct.inl g : Γ) • α₀ from h_eq.symm]
      rw [← mul_smul, inv_mul_cancel, one_smul]
    -- inl(g) ∈ inlG.
    have h_in_inlG : (SemidirectProduct.inl g : Γ) ∈ inlG := ⟨g, rfl⟩
    -- γ = inl(g) * (inl(g)⁻¹ * γ).
    have h_decomp : γ = (SemidirectProduct.inl g : Γ) * ((SemidirectProduct.inl g : Γ)⁻¹ * γ) := by
      group
    rw [h_decomp, sup_comm]
    exact Subgroup.mul_mem_sup h_in_inlG h_in_U
  -- Step 2: inlG.relIndex U = Nat.card A.
  have h_relIndex : inlG.relIndex U = Nat.card A := by
    rw [← Subgroup.relIndex_sup_right (H := U) (K := inlG), h_UG_top,
        Subgroup.relIndex_top_right, h_index_A]
  -- Step 3: SZ apply in U. First, Coprime (Nat.card (inlG.subgroupOf U)) (...).index = |A|.
  have h_card_subof_dvd_G : Nat.card (inlG.subgroupOf U) ∣ Nat.card G := by
    -- inlG.subgroupOf U ≃ inlG ⊓ U (as subgroups, same elements via U.subtype).
    have h_iso : (inlG.subgroupOf U : Subgroup U) ≃* ((U ⊓ inlG).subgroupOf U) := by
      rw [Subgroup.inf_subgroupOf_left]
    have h_card_eq : Nat.card (inlG.subgroupOf U) = Nat.card (U ⊓ inlG : Subgroup Γ) := by
      rw [Nat.card_congr h_iso.toEquiv]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    rw [h_card_eq, ← h_card_inlG]
    exact Subgroup.card_dvd_of_le inf_le_right
  have h_subof_index : (inlG.subgroupOf U).index = Nat.card A := by
    change inlG.relIndex U = Nat.card A
    exact h_relIndex
  have h_coprime_subof : Nat.Coprime (Nat.card (inlG.subgroupOf U)) (inlG.subgroupOf U).index := by
    rw [h_subof_index]
    exact hCop.symm.coprime_dvd_left h_card_subof_dvd_G
  have hU_finite : Finite U := Subtype.finite
  obtain ⟨H_in_U, hH_compl_in_U⟩ :=
    Subgroup.exists_right_complement'_of_coprime (N := inlG.subgroupOf U) h_coprime_subof
  -- Step 4: H := H_in_U.map U.subtype is a complement of inlG in Γ.
  set H : Subgroup Γ := H_in_U.map U.subtype with hH_def
  -- 4a: Nat.card H = Nat.card A.
  have h_card_H : Nat.card H = Nat.card A := by
    rw [hH_def, Subgroup.card_subtype]
    exact hH_compl_in_U.symm.index_eq_card.symm.trans h_subof_index
  -- 4b: H ≤ U.
  have h_H_le_U : H ≤ U := by rintro x ⟨y, _, rfl⟩; exact y.property
  -- 4c: H is a complement of inlG in Γ.
  have hH_compl_inlG : inlG.IsComplement' H := by
    rw [Subgroup.isComplement'_iff_card_mul_and_disjoint]
    refine ⟨?_, ?_⟩
    · -- Nat.card inlG * Nat.card H = Nat.card Γ.
      rw [h_card_inlG, h_card_H, hΓ_def, SemidirectProduct.card]
    · -- Disjoint inlG H.
      rw [disjoint_iff]
      ext x
      simp only [Subgroup.mem_inf, Subgroup.mem_bot]
      refine ⟨?_, fun hx => by rw [hx]; exact ⟨Subgroup.one_mem _, Subgroup.one_mem _⟩⟩
      rintro ⟨hx_inlG, ⟨y, hy_in, rfl⟩⟩
      -- y.val ∈ inlG ∧ y ∈ H_in_U ⇒ y ∈ inlG.subgroupOf U.
      have hy_in_subof : y ∈ inlG.subgroupOf U := hx_inlG
      have h_disj_in_U : Disjoint (inlG.subgroupOf U) H_in_U := hH_compl_in_U.disjoint
      rw [disjoint_iff] at h_disj_in_U
      have : y ∈ (inlG.subgroupOf U) ⊓ H_in_U := ⟨hy_in_subof, hy_in⟩
      rw [h_disj_in_U, Subgroup.mem_bot] at this
      rw [this]; rfl
  -- Step 5: inrA is a complement of inlG in Γ (from Ch.3).
  have h_inrA_compl : inlG.IsComplement' inrA := by
    rw [hinlG_def, hinrA_def]
    exact OddOrder.Isaacs.Ch03.inl_range_isComplement_inr_range φ
  -- Step 6: SZ conjugacy: ∃ n ∈ inlG, inrA.map (conj n).toMonoidHom = H.
  have hΓ_finite : Finite Γ := by rw [hΓ_def]; infer_instance
  obtain ⟨n, hn_in_inlG, hn_conj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime h_coprime_inlG hSolv_inlG
      h_inrA_compl hH_compl_inlG
  -- Extract g ∈ G with n = inl g.
  obtain ⟨g, rfl⟩ := hn_in_inlG
  -- Step 7: The A-fixed element is (inl g)⁻¹ • α₀ = g⁻¹ • α₀.
  refine ⟨g⁻¹ • α₀, ?_⟩
  intro a
  -- a • (g⁻¹ • α₀) = (inr a * (inl g)⁻¹) • α₀ (action via SDP).
  have h_a_smul : (a • (g⁻¹ • α₀) : Ω) = ((SemidirectProduct.inr a : Γ) *
      (SemidirectProduct.inl g : Γ)⁻¹) • α₀ := by
    rw [mul_smul, ← map_inv,
        IsCompatibleMulAction.toMulAction_inl_smul h g⁻¹ α₀,
        IsCompatibleMulAction.toMulAction_inr_smul h a (g⁻¹ • α₀)]
  rw [h_a_smul]
  -- inr a * (inl g)⁻¹ = (inl g)⁻¹ * (inl g * inr a * (inl g)⁻¹).
  have h_rewrite : (SemidirectProduct.inr a : Γ) * (SemidirectProduct.inl g : Γ)⁻¹ =
      (SemidirectProduct.inl g : Γ)⁻¹ *
        ((SemidirectProduct.inl g : Γ) * (SemidirectProduct.inr a : Γ) *
          (SemidirectProduct.inl g : Γ)⁻¹) := by group
  rw [h_rewrite, mul_smul]
  -- inl g * inr a * (inl g)⁻¹ ∈ H (from hn_conj : inrA.map (conj (inl g)) = H).
  have h_h_in_H : (SemidirectProduct.inl g : Γ) * (SemidirectProduct.inr a : Γ) *
      (SemidirectProduct.inl g : Γ)⁻¹ ∈ H := by
    rw [← hn_conj]
    exact ⟨SemidirectProduct.inr a, ⟨a, rfl⟩, rfl⟩
  -- H ⊆ U, so this element fixes α₀.
  have h_fixes : ((SemidirectProduct.inl g : Γ) * (SemidirectProduct.inr a : Γ) *
      (SemidirectProduct.inl g : Γ)⁻¹) • α₀ = α₀ :=
    h_H_le_U h_h_in_H
  rw [h_fixes]
  -- (inl g)⁻¹ • α₀ = g⁻¹ • α₀.
  rw [← map_inv, IsCompatibleMulAction.toMulAction_inl_smul h g⁻¹ α₀]

/-- **Isaacs Lemma 3.24(b)**: 同じ前提下で, 2 つの A-invariant 元 α, β ∈ Ω に対し,
`∃ c ∈ C_G(A), c • α = β`.

**証明戦略**: `X := { g | g • α = β }` (transporter, nonempty by G transitive).
`H := stabilizer G β` acts on `X` transitively by left multiplication.
`A` acts on `X` via φ (well-defined since α, β A-inv).
`A` acts on `H` via φ (well-defined since β A-inv).
Apply 3.24(a) with (A, H, X) to get x ∈ X A-fixed, i.e., x ∈ C_G(A) ∩ X. -/
theorem glauberman_fixed_points_conj
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {Ω : Type*} [MulAction G Ω] [MulAction A Ω]
    (h : IsCompatibleMulAction φ Ω) (hG_trans : MulAction.IsPretransitive G Ω)
    {α β : Ω} (hα : ∀ a : A, a • α = α) (hβ : ∀ a : A, a • β = β) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ c • α = β := by
  -- H := stabilizer G β (subgroup, A-invariant via hβ).
  set H : Subgroup G := MulAction.stabilizer G β with hH_def
  have hH_inv : IsAInvariant φ H := by
    intro a
    ext g
    constructor
    · rintro ⟨g', hg'_in_H, rfl⟩
      change ((φ a) g') • β = β
      have hg' : g' • β = β := hg'_in_H
      have hcomp := h a g' β
      rw [hg', hβ a] at hcomp
      exact hcomp.symm
    · intro hg_in_H
      refine ⟨(φ a)⁻¹ g, ?_, by simp⟩
      change ((φ a)⁻¹ g) • β = β
      have hg : g • β = β := hg_in_H
      have hcomp := h a⁻¹ g β
      rw [hg, hβ a⁻¹] at hcomp
      -- hcomp : β = (φ a⁻¹) g • β. Convert φ a⁻¹ to (φ a)⁻¹.
      have hphi : (φ a⁻¹ : MulAut G) = (φ a)⁻¹ := map_inv φ a
      rw [hphi] at hcomp
      exact hcomp.symm
  -- X := transporter from α to β: { g : G // g • α = β }.
  let X := { g : G // g • α = β }
  -- X nonempty by G transitive.
  have hX_nonempty : Nonempty X := by
    obtain ⟨g, hg⟩ := hG_trans.exists_smul_eq α β
    exact ⟨⟨g, hg⟩⟩
  -- H acts on X by left multiplication.
  let mulH : MulAction ↥H X := {
    smul := fun h x => ⟨h.val * x.val, by
      rw [mul_smul, x.property]
      exact h.property⟩
    one_smul := fun x => Subtype.ext (one_mul _)
    mul_smul := fun h₁ h₂ x => Subtype.ext (by
      change (h₁ * h₂).val * x.val = h₁.val * (h₂.val * x.val)
      rw [Subgroup.coe_mul, mul_assoc])
  }
  -- A acts on X via φ.
  let mulA : MulAction A X := {
    smul := fun a x => ⟨(φ a) x.val, by
      have hcompat := h a x.val α
      rw [x.property] at hcompat
      rw [hα a] at hcompat
      rw [← hcompat, hβ a]⟩
    one_smul := fun x => Subtype.ext (by change (φ 1) x.val = x.val; simp)
    mul_smul := fun a b x => Subtype.ext (by
      change (φ (a * b)) x.val = (φ a) ((φ b) x.val)
      simp [map_mul])
  }
  -- Compatibility: a • (h • x) = (hH_inv.restrict a h) • (a • x).
  have hcompat_X : IsCompatibleMulAction (hH_inv.restrict) X := by
    intro a h_elem x
    apply Subtype.ext
    change (φ a) (h_elem.val * x.val) = ((hH_inv.restrict a) h_elem).val * (φ a) x.val
    rw [map_mul]; rfl
  -- H acts transitively on X.
  have hH_trans : MulAction.IsPretransitive ↥H X := by
    constructor
    intro x₁ x₂
    -- x₁, x₂ ∈ X with x_i • α = β. Want h ∈ H with h * x₁ = x₂.
    -- h := x₂ * x₁⁻¹. Then h • β = (x₂ * x₁⁻¹) • β = x₂ • (x₁⁻¹ • β).
    -- x₁ • α = β, so x₁⁻¹ • β = α. Then x₂ • α = β. So h • β = β.
    have hx₁_inv : x₁.val⁻¹ • β = α :=
      ((smul_eq_iff_eq_inv_smul x₁.val).mp x₁.property).symm
    refine ⟨⟨x₂.val * x₁.val⁻¹, ?_⟩, ?_⟩
    · change (x₂.val * x₁.val⁻¹) • β = β
      rw [mul_smul, hx₁_inv, x₂.property]
    · apply Subtype.ext
      change (x₂.val * x₁.val⁻¹) * x₁.val = x₂.val
      rw [mul_assoc, inv_mul_cancel, mul_one]
  -- Coprime |A| |H|.
  have hCop' : Nat.Coprime (Nat.card A) (Nat.card ↥H) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card H)
  -- Solvable A ∨ Solvable H.
  have hSolv' : Group.IsSolvable A ∨ Group.IsSolvable ↥H := by
    rcases hSolv with hA | hG
    · exact Or.inl hA
    · have := hG; exact Or.inr inferInstance
  have hH_finite : Finite ↥H := Subtype.finite
  -- Apply Glauberman 3.24(a) with (↥H, A, X).
  obtain ⟨x₀, hx₀_fix⟩ :=
    glauberman_fixed_point_exists (G := ↥H) (A := A) (φ := hH_inv.restrict)
      hCop' hSolv' (Ω := X) hcompat_X hH_trans
  -- x₀ ∈ X is A-fixed. So x₀.val ∈ C_G(A) and x₀.val • α = β.
  refine ⟨x₀.val, ?_, x₀.property⟩
  intro a
  have hfix : (a • x₀ : X) = x₀ := hx₀_fix a
  have h_eq : ((a • x₀ : X) : G) = (φ a) x₀.val := rfl
  rw [← h_eq, hfix]

end Glauberman

section AInvariantSylow

variable {A : Type*} [Group A] [Finite A] [Finite G]

/-- **Isaacs Thm 3.23(a)**: A-invariant Sylow p-subgroup の存在.
`Glauberman 3.24(a)` を `Ω = Sylow p G` に適用 (G 推移 by Sylow C). -/
theorem exists_aInvariant_sylow
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∃ P : Sylow p G, IsAInvariant φ (P : Subgroup G) := by
  -- A acts on G via φ as MulDistribMulAction.
  let mdma : MulDistribMulAction A G := MulDistribMulAction.compHom G φ
  -- This gives MulAction A (Sylow p G) via Sylow.pointwiseMulAction.
  -- G acts on Sylow p G via conjugation (Sylow.mulAction).
  -- Compatibility: a • (g • P) = (φ a g) • (a • P).
  have hcompat : IsCompatibleMulAction φ (Sylow p G) := by
    intro a g P
    apply Sylow.ext
    -- Goal: ↑(a • (g • P)) = ↑((φ a g) • (a • P)) as Subgroup G.
    show (a • (g • P) : Sylow p G).toSubgroup = ((φ a g) • (a • P)).toSubgroup
    rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul,
        Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def]
    -- Goal: φ a • (MulAut.conj g • P.toSubgroup) = MulAut.conj (φ a g) • (φ a • P.toSubgroup).
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      -- y = (MulAut.conj g) z = g * z * g⁻¹, x = (φ a) y = (φ a)(g z g⁻¹) = (φ a g) (φ a z) (φ a
      -- g)⁻¹
      refine ⟨(φ a) z, ⟨z, hz, rfl⟩, ?_⟩
      change MulAut.conj (φ a g) ((φ a) z) = (φ a) ((MulAut.conj g) z)
      simp [MulAut.conj_apply, map_mul, map_inv]
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(MulAut.conj g) z, ⟨z, hz, rfl⟩, ?_⟩
      change (φ a) ((MulAut.conj g) z) = MulAut.conj (φ a g) ((φ a) z)
      simp [MulAut.conj_apply, map_mul, map_inv]
  -- G transitive on Sylow p G.
  have hSyl_nonempty : Nonempty (Sylow p G) := inferInstance
  have hSyl_finite : Finite (Sylow p G) := inferInstance
  have hG_trans : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  -- Apply Glauberman 3.24(a).
  obtain ⟨P, hP_fix⟩ :=
    glauberman_fixed_point_exists (G := G) (A := A) (φ := φ) hCop hSolv (Ω := Sylow p G)
      hcompat hG_trans
  -- hP_fix : ∀ a : A, a • P = P (in Sylow type). Translate to IsAInvariant on Subgroup.
  refine ⟨P, ?_⟩
  intro a
  -- IsAInvariant: (φ a) • (P : Subgroup G) = P.
  have h_pt : a • P = P := hP_fix a
  -- a • P in Sylow has carrier (φ a) • (P : Set G) = (φ a) • (P : Subgroup G) (as set).
  have h_coe : ((a • P : Sylow p G) : Subgroup G) = ((P : Sylow p G) : Subgroup G) := by
    rw [h_pt]
  rw [Sylow.pointwise_smul_def] at h_coe
  -- h_coe : (φ a) • (P : Subgroup G) = (P : Subgroup G).
  -- IsAInvariant says (φ a) • P = P (as Subgroup), which by smul_def is the same.
  change (φ a : MulAut G) • (P : Subgroup G) = (P : Subgroup G)
  exact h_coe

/-- **Isaacs Thm 3.23(b)**: 2 つの A-invariant Sylow p-subgroup は C_G(A) で共役.
`Glauberman 3.24(b)` の Sylow p G 版. -/
theorem aInvariant_sylow_conj
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    {S T : Sylow p G} (hS_inv : IsAInvariant φ (S : Subgroup G))
    (hT_inv : IsAInvariant φ (T : Subgroup G)) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ (MulAut.conj c • (S : Subgroup G) = T) := by
  -- Re-establish the Sylow MulAction setup (same as 3.23(a)).
  let mdma : MulDistribMulAction A G := MulDistribMulAction.compHom G φ
  have hcompat : IsCompatibleMulAction φ (Sylow p G) := by
    intro a g P
    apply Sylow.ext
    show (a • (g • P) : Sylow p G).toSubgroup = ((φ a g) • (a • P)).toSubgroup
    rw [Sylow.pointwise_smul_def, Sylow.coe_subgroup_smul,
        Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def]
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(φ a) z, ⟨z, hz, rfl⟩, ?_⟩
      change MulAut.conj (φ a g) ((φ a) z) = (φ a) ((MulAut.conj g) z)
      simp [MulAut.conj_apply, map_mul, map_inv]
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      refine ⟨(MulAut.conj g) z, ⟨z, hz, rfl⟩, ?_⟩
      change (φ a) ((MulAut.conj g) z) = MulAut.conj (φ a g) ((φ a) z)
      simp [MulAut.conj_apply, map_mul, map_inv]
  have hG_trans : MulAction.IsPretransitive G (Sylow p G) := Sylow.isPretransitive_of_finite
  -- A-invariance of S, T as Sylow: a • S = S (in Sylow type).
  have hS_fix : ∀ a : A, a • S = S := by
    intro a
    apply Sylow.ext
    show (a • S : Sylow p G).toSubgroup = S.toSubgroup
    rw [Sylow.pointwise_smul_def]
    exact hS_inv a
  have hT_fix : ∀ a : A, a • T = T := by
    intro a
    apply Sylow.ext
    show (a • T : Sylow p G).toSubgroup = T.toSubgroup
    rw [Sylow.pointwise_smul_def]
    exact hT_inv a
  -- Apply Glauberman 3.24(b).
  obtain ⟨c, hc_fix, hc_smul⟩ :=
    glauberman_fixed_points_conj (G := G) (A := A) (φ := φ) hCop hSolv (Ω := Sylow p G)
      hcompat hG_trans hS_fix hT_fix
  -- hc_smul : c • S = T in Sylow. Translate to Subgroup.
  refine ⟨c, hc_fix, ?_⟩
  have h_coe : ((c • S : Sylow p G) : Subgroup G) = (T : Subgroup G) := by rw [hc_smul]
  rwa [Sylow.coe_subgroup_smul] at h_coe

/-- **Isaacs Cor 3.25**: A-invariant p-subgroup is contained in some A-invariant Sylow.

**証明骨子**:
1. `P` を含む A-不変 p-部分群の中で極大なもの `Q` を取る (`Finite.exists_le_maximal`).
2. `N := N_G(Q)` は A-不変 (`IsAInvariant.normalizer`). 3.23(a) を `N` の制限作用に
   適用して A-不変 Sylow `R_in_N` を得る.
3. `R := R_in_N.map N.subtype ≤ N ≤ G` も A-不変 p-部分群. `R ≤ N(Q)` なので
   `Q ⊔ R` も p-部分群 (`IsPGroup.to_sup_of_normal_left'`). 極大性で `Q ⊔ R = Q`,
   よって `R ≤ Q`. Sylow の極大性で `Q.subgroupOf N = R_in_N`, つまり `Q = R` が
   `N` 内で Sylow.
4. **Normalizer grow**: 任意の p-部分群 `T ⊇ Q` に対し, `T` が p-群 ⇒
   `NormalizerCondition T` (`IsPGroup.isNilpotent` + `Group.normalizerCondition_of_isNilpotent`).
   `Q.subgroupOf T < ⊤` ⇒ `Q.subgroupOf T < normalizer = N.subgroupOf T`, 翻訳して
   `Q < N ⊓ T`. `N ⊓ T ≤ N` は p-部分群で `Q` Sylow に矛盾. よって `T = Q`,
   つまり `Q` は `G` の Sylow. -/
theorem aInvariant_pSubgroup_le_aInvariant_sylow
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G) {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP_pgrp : IsPGroup p P) (hP_inv : IsAInvariant φ P) :
    ∃ S : Sylow p G, IsAInvariant φ (S : Subgroup G) ∧ P ≤ S := by
  classical
  -- Step 1: 極大 A-不変 p-部分群 Q ⊇ P を取る.
  obtain ⟨Q, hPQ, hQ_max⟩ :=
    Finite.exists_le_maximal (α := Subgroup G)
      (p := fun Q => IsPGroup p Q ∧ IsAInvariant φ Q ∧ P ≤ Q)
      ⟨hP_pgrp, hP_inv, le_refl P⟩
  obtain ⟨hQ_pgrp, hQ_inv, hPQ_le⟩ := hQ_max.prop
  -- Step 2: N := N_G(Q). A-不変. 3.23(a) を制限作用に適用.
  set N : Subgroup G := Subgroup.normalizer Q with hN_def
  have hQN : Q ≤ N := Subgroup.le_normalizer
  have hN_inv : IsAInvariant φ N := IsAInvariant.normalizer hQ_inv
  have hN_finite : Finite ↥N := Subtype.finite
  have hCop_N : Nat.Coprime (Nat.card A) (Nat.card ↥N) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
  have hSolv_N : Group.IsSolvable A ∨ Group.IsSolvable ↥N := by
    rcases hSolv with hA | hG
    · exact Or.inl hA
    · have := hG; exact Or.inr inferInstance
  obtain ⟨R_in_N, hR_in_N_inv⟩ :=
    exists_aInvariant_sylow (G := ↥N) (A := A) (φ := hN_inv.restrict)
      hCop_N hSolv_N p
  -- Step 3: R := R_in_N を G の部分群に持ち上げる.
  set R : Subgroup G := (R_in_N : Subgroup ↥N).map N.subtype with hR_def
  have hR_le_N : R ≤ N := by
    rintro x ⟨y, _, rfl⟩
    exact y.property
  have hR_pgrp : IsPGroup p R := R_in_N.isPGroup'.map _
  have hR_inv_G : IsAInvariant φ R := by
    rw [OddOrder.Isaacs.Ch03.isAInvariant_iff_smul_mem]
    intro a x hx
    -- hx : x ∈ R. Decompose: x = z.val for z ∈ R_in_N.
    obtain ⟨z, hz_in, hz_eq⟩ := hx
    -- (hN_inv.restrict a) z ∈ R_in_N because R_in_N is A-inv under restricted action.
    have hRzn : (hN_inv.restrict a) z ∈ R_in_N := hR_in_N_inv.smul_mem a hz_in
    -- (φ a) x = ((hN_inv.restrict a) z).val (since x = z.val and restrict_apply_val).
    refine ⟨(hN_inv.restrict a) z, hRzn, ?_⟩
    change ((hN_inv.restrict a) z).val = (φ a) x
    rw [← hz_eq]
    rfl
  -- Step 4: R ≤ N(Q), so Q ⊔ R is a p-group; A-inv; ⊇ P. Maximality ⇒ R ≤ Q.
  have hR_le_NQ : R ≤ Subgroup.normalizer Q := hR_le_N
  have hQR_pgrp : IsPGroup p ((Q ⊔ R : Subgroup G) : Subgroup G) :=
    hQ_pgrp.to_sup_of_normal_left' hR_pgrp hR_le_NQ
  have hQR_inv : IsAInvariant φ (Q ⊔ R : Subgroup G) := IsAInvariant.sup hQ_inv hR_inv_G
  have hPQR : P ≤ Q ⊔ R := hPQ_le.trans le_sup_left
  -- Maximality: hQ_max.eq_of_le gives Q = Q ⊔ R for any candidate ≥ Q satisfying p.
  have hQ_eq_QR : Q = Q ⊔ R :=
    hQ_max.eq_of_le ⟨hQR_pgrp, hQR_inv, hPQR⟩ le_sup_left
  have hR_le_Q : R ≤ Q := by
    have : R ≤ Q ⊔ R := le_sup_right
    rwa [← hQ_eq_QR] at this
  -- Step 5: Q.subgroupOf N is p-subgroup ⊇ R_in_N. By R_in_N Sylow maximality, equal.
  have hQN_pgrp : IsPGroup p (Q.subgroupOf N) := hQ_pgrp.comap_subtype
  have hR_in_N_le_QN : (R_in_N : Subgroup ↥N) ≤ Q.subgroupOf N := by
    intro x hx
    change x.val ∈ Q
    have : x.val ∈ R := ⟨x, hx, rfl⟩
    exact hR_le_Q this
  have hQN_eq_R_in_N : Q.subgroupOf N = R_in_N :=
    R_in_N.3 hQN_pgrp hR_in_N_le_QN
  -- Translate back: Q = R as subgroups of G.
  have hQ_eq_R : Q = R := by
    have h1 : (Q.subgroupOf N).map N.subtype = Q :=
      Subgroup.map_subgroupOf_eq_of_le hQN
    have h2 : ((R_in_N : Subgroup ↥N) : Subgroup ↥N).map N.subtype = R := rfl
    rw [hQN_eq_R_in_N] at h1
    rw [h2] at h1
    exact h1.symm
  -- Step 6: Q is Sylow of G via normalizer-grow argument.
  let S : Sylow p G := {
    toSubgroup := Q
    isPGroup' := hQ_pgrp
    is_maximal' := by
      intro T hT_pgrp hQT
      -- Show T = Q.
      by_contra hT_ne_Q
      have hQT_lt : Q < T := lt_of_le_of_ne hQT (Ne.symm hT_ne_Q)
      have hT_finite : Finite ↥T := Subtype.finite
      have hT_nilp : Group.IsNilpotent ↥T := hT_pgrp.isNilpotent
      have hT_nc : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent
      -- Q.subgroupOf T < ⊤ in T.
      have hQT_subOf_lt : Q.subgroupOf T < (⊤ : Subgroup ↥T) := by
        rw [lt_top_iff_ne_top]
        intro h_top
        apply hT_ne_Q
        refine le_antisymm ?_ hQT
        intro x hx
        have : (⟨x, hx⟩ : ↥T) ∈ Q.subgroupOf T := by rw [h_top]; trivial
        exact this
      -- NormalizerCondition gives strict inclusion in normalizer.
      have hQT_lt_norm : Q.subgroupOf T < Subgroup.normalizer (Q.subgroupOf T) :=
        hT_nc _ hQT_subOf_lt
      -- normalizer (Q.subgroupOf T) = N.subgroupOf T.
      have h_norm_eq : Subgroup.normalizer (Q.subgroupOf T) = N.subgroupOf T := by
        rw [← Subgroup.subgroupOf_normalizer_eq hQT]
      -- So Q.subgroupOf T < N.subgroupOf T. Translate: Q < N ⊓ T.
      have hQ_lt_NT : Q < N ⊓ T := by
        refine lt_of_le_of_ne (le_inf hQN hQT) ?_
        intro h_eq
        apply hQT_lt_norm.ne
        rw [h_norm_eq]
        ext ⟨x, hx⟩
        simp only [Subgroup.mem_subgroupOf]
        constructor
        · intro hxQ; exact hQN hxQ
        · intro hxN
          have : x ∈ (N ⊓ T : Subgroup G) := ⟨hxN, hx⟩
          rw [← h_eq] at this
          exact this
      -- N ⊓ T is a p-subgroup of N. (N ⊓ T).subgroupOf N is p-subgroup of N.
      have hNT_le_N : (N ⊓ T : Subgroup G) ≤ N := inf_le_left
      have hNT_subOf_N_pgrp : IsPGroup p ((N ⊓ T).subgroupOf N) :=
        (hT_pgrp.to_le inf_le_right).comap_subtype
      -- Q.subgroupOf N ≤ (N ⊓ T).subgroupOf N (from Q ≤ N ⊓ T).
      have hQN_le_NT_subOf : Q.subgroupOf N ≤ (N ⊓ T).subgroupOf N :=
        Subgroup.subgroupOf_mono N hQ_lt_NT.le
      -- Since Q.subgroupOf N = R_in_N, R_in_N ≤ (N ⊓ T).subgroupOf N.
      rw [hQN_eq_R_in_N] at hQN_le_NT_subOf
      -- Sylow maximality of R_in_N:
      have h_NT_sub_eq : (N ⊓ T).subgroupOf N = R_in_N :=
        R_in_N.3 hNT_subOf_N_pgrp hQN_le_NT_subOf
      -- Translate back: N ⊓ T = Q.
      have h_NT_eq_Q : (N ⊓ T : Subgroup G) = Q := by
        have h_map : ((N ⊓ T).subgroupOf N).map N.subtype = N ⊓ T :=
          Subgroup.map_subgroupOf_eq_of_le hNT_le_N
        rw [h_NT_sub_eq, ← hQN_eq_R_in_N, Subgroup.map_subgroupOf_eq_of_le hQN] at h_map
        exact h_map.symm
      exact hQ_lt_NT.ne h_NT_eq_Q.symm
  }
  exact ⟨S, hQ_inv, hPQ_le⟩

end AInvariantSylow

section CosetFixed

variable {A : Type*} [Group A] [Finite A] [Finite G]

/-- **Isaacs Thm 3.27**: A-invariant coset gN は C_G(A) の元を含む.

`gN` が A-不変 (条件 `∀ a, ∃ n ∈ N, φ a g = g * n`) のとき, ∃ c ∈ gN かつ ∀ a, φ a c = c. -/
theorem aInvariant_coset_mem_centralizer_of_coprime_subgroup
    {φ : A →* MulAut G} {N : Subgroup G}
    (hCop : Nat.Coprime (Nat.card A) (Nat.card ↥N))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable ↥N)
    (hN_inv : IsAInvariant φ N) {g : G}
    (hgN_inv : ∀ a : A, ∃ n ∈ N, φ a g = g * n) :
    ∃ c : G, (∃ n ∈ N, c = g * n) ∧ ∀ a : A, (φ a) c = c := by
  -- Ω := subtype of gN.
  let Ω := { x : G // ∃ n ∈ N, x = g * n }
  have hΩ_nonempty : Nonempty Ω := ⟨⟨g, 1, N.one_mem, (mul_one g).symm⟩⟩
  -- N acts on Ω by right multiplication of inverse (to make it a left action).
  let mulN : MulAction ↥N Ω := {
    smul := fun n ω => ⟨ω.val * n.val⁻¹, by
      obtain ⟨m, hm, hω_eq⟩ := ω.property
      refine ⟨m * n.val⁻¹, N.mul_mem hm (N.inv_mem n.property), ?_⟩
      rw [hω_eq, mul_assoc]⟩
    one_smul := fun ω => Subtype.ext (by
      change ω.val * (1 : ↥N).val⁻¹ = ω.val
      simp)
    mul_smul := fun m n ω => Subtype.ext (by
      change ω.val * (m * n).val⁻¹ = ω.val * n.val⁻¹ * m.val⁻¹
      rw [Subgroup.coe_mul, mul_inv_rev, mul_assoc])
  }
  -- A acts on Ω via φ.
  let mulA : MulAction A Ω := {
    smul := fun a ω => ⟨φ a ω.val, by
      obtain ⟨n, hn, hω_eq⟩ := ω.property
      obtain ⟨m, hm, hg_eq⟩ := hgN_inv a
      refine ⟨m * (φ a n), N.mul_mem hm (hN_inv.smul_mem a hn), ?_⟩
      rw [hω_eq, map_mul, hg_eq, mul_assoc]⟩
    one_smul := fun ω => Subtype.ext (by
      change (φ 1) ω.val = ω.val
      rw [map_one]; rfl)
    mul_smul := fun a b ω => Subtype.ext (by
      change (φ (a * b)) ω.val = (φ a) ((φ b) ω.val)
      rw [map_mul]; rfl)
  }
  -- Compatibility: a • (n • ω) = (hN_inv.restrict a n) • (a • ω).
  have hcompat : IsCompatibleMulAction (hN_inv.restrict) Ω := by
    intro a n ω
    apply Subtype.ext
    change (φ a) (ω.val * n.val⁻¹) = (φ a) ω.val * ((hN_inv.restrict a) n).val⁻¹
    rw [map_mul, map_inv]
    rfl
  -- N transitive on Ω.
  have hN_trans : MulAction.IsPretransitive ↥N Ω := by
    constructor
    intro ω₁ ω₂
    obtain ⟨n₁, hn₁, hω₁_eq⟩ := ω₁.property
    obtain ⟨n₂, hn₂, hω₂_eq⟩ := ω₂.property
    -- Want n with n • ω₁ = ω₂, i.e., ω₁.val * n⁻¹ = ω₂.val.
    -- So n⁻¹ = ω₁⁻¹ * ω₂ = (g * n₁)⁻¹ * (g * n₂) = n₁⁻¹ * n₂. Thus n = n₂⁻¹ * n₁.
    refine ⟨⟨n₂⁻¹ * n₁, N.mul_mem (N.inv_mem hn₂) hn₁⟩, ?_⟩
    apply Subtype.ext
    change ω₁.val * (n₂⁻¹ * n₁)⁻¹ = ω₂.val
    rw [hω₁_eq, hω₂_eq, mul_inv_rev, inv_inv, mul_assoc, ← mul_assoc n₁, mul_inv_cancel, one_mul]
  -- Finite N.
  have hN_finite : Finite ↥N := Subtype.finite
  -- Apply Glauberman 3.24(a).
  obtain ⟨ω₀, hω₀_fix⟩ :=
    glauberman_fixed_point_exists (G := ↥N) (A := A) (φ := hN_inv.restrict)
      hCop hSolv (Ω := Ω) hcompat hN_trans
  -- Extract: c := ω₀.val ∈ gN and ∀ a, φ a c = c.
  refine ⟨ω₀.val, ω₀.property, ?_⟩
  intro a
  have := hω₀_fix a
  -- this : (a • ω₀ : Ω) = ω₀ as Subtype.
  -- (a • ω₀).val = φ a ω₀.val by definition.
  have h_eq : ((a • ω₀ : Ω) : G) = (φ a) ω₀.val := rfl
  rw [← h_eq, this]

/-- **Isaacs Cor 3.28 (transitive blocker for Ch.4)**: 商の固定点は底群の固定点像.

`N ⊴ G` A-不変, coprime + solvable のとき, `Ḡ = G/N` 上の A-fixed 元は `C_G(A)` の像と一致.
ステートメント: A-fixed `ḡ ∈ Ḡ` ⇒ ∃ c ∈ C_G(A), c·N = g·N. -/
theorem coprime_fixedPoints_quotient_of_coprime_normal
    {φ : A →* MulAut G}
    {N : Subgroup G} [N.Normal]
    (hCop : Nat.Coprime (Nat.card A) (Nat.card ↥N))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable ↥N)
    (hN_inv : IsAInvariant φ N) {g : G}
    (hg_fix : ∀ a : A, ∃ n ∈ N, φ a g = g * n) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ (∃ n ∈ N, c = g * n) := by
  obtain ⟨c, hc_coset, hc_fixed⟩ :=
    aInvariant_coset_mem_centralizer_of_coprime_subgroup hCop hSolv hN_inv hg_fix
  exact ⟨c, hc_fixed, hc_coset⟩

/-- Backwards-compatible form of Isaacs Cor 3.28 using the stronger `(|A|, |G|)=1`
hypothesis. -/
theorem coprime_fixedPoints_quotient
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    {N : Subgroup G} [N.Normal] (hN_inv : IsAInvariant φ N) {g : G}
    (hg_fix : ∀ a : A, ∃ n ∈ N, φ a g = g * n) :
    ∃ c : G, (∀ a : A, (φ a) c = c) ∧ (∃ n ∈ N, c = g * n) := by
  have hCopN : Nat.Coprime (Nat.card A) (Nat.card ↥N) :=
    hCop.coprime_dvd_right (Subgroup.card_subgroup_dvd_card N)
  have hSolvN : Group.IsSolvable A ∨ Group.IsSolvable ↥N := by
    rcases hSolv with hA | hG
    · exact Or.inl hA
    · have := hG
      exact Or.inr inferInstance
  exact coprime_fixedPoints_quotient_of_coprime_normal
    hCopN hSolvN hN_inv hg_fix

end CosetFixed

section FrattiniAction

variable {A : Type*} [Group A] [Finite A] [Finite G]

/-- **Isaacs Cor 3.29 (可解性仮定つき補助形)**: A が `G/Φ(G)` に自明作用 ⇒ A が G に自明作用.

`G = C·Φ(G)` ⇒ `C ⊔ Φ = ⊤` ⇒ `C = ⊤` (Frattini non-generating).

⚠ 書籍 3.29 自身は可解性を仮定しない — 本補助形の `hSolv` を巡回還元で外したものが
`aFixed_quotient_frattini` (下)。 -/
theorem aFixed_quotient_frattini_of_isSolvable
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable G)
    (h_triv_quot : ∀ a : A, ∀ g : G, ∃ x ∈ (_root_.frattini G), (φ a) g = g * x) :
    ∀ a : A, ∀ g : G, (φ a) g = g := by
  set C : Subgroup G := fixedPointsOfMulAut φ with hC_def
  have hΦ_inv : IsAInvariant φ (_root_.frattini G) := IsAInvariant.frattini φ
  -- Step 1: C ⊔ Φ(G) = ⊤ via Cor 3.28.
  have hCΦ_top : C ⊔ _root_.frattini G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    obtain ⟨c, hc_fix, hc_coset⟩ :=
      coprime_fixedPoints_quotient hCop hSolv hΦ_inv (fun a => h_triv_quot a g)
    obtain ⟨n, hn_in, hc_eq⟩ := hc_coset
    have hg_eq : g = c * n⁻¹ := by rw [hc_eq]; group
    rw [hg_eq]
    refine Subgroup.mul_mem_sup ?_ ?_
    · -- c ∈ C
      exact hc_fix
    · -- n⁻¹ ∈ Φ
      exact Subgroup.inv_mem _ hn_in
  -- Step 2: Frattini non-generating ⇒ C = ⊤.
  have : IsCoatomic (Subgroup G) := inferInstance
  have hC_top : C = ⊤ := frattini_nongenerating hCΦ_top
  -- Step 3: ∀ a g, φ a g = g.
  intro a g
  have hg_in_C : g ∈ C := by rw [hC_top]; exact Subgroup.mem_top g
  exact hg_in_C a

/-- **Isaacs Cor 3.29** (書籍どおり、可解性仮定なし): 互いに素な作用で A が `G/Φ(G)` に
自明作用するなら A は G に自明作用する.

⚠ **書籍 3.29 は 3.23/3.25/3.26/3.27/3.28 と違って「A または G が可解」を仮定しない**。
Isaacs の証明がその仮説を巡回還元で外すからである — 「it is no loss to assume that
`A = ⟨a⟩`. Since `A` is cyclic, it is certainly solvable, and thus Corollary 3.28 applies」。
ここでも同じことをする: `a : A` を固定して `φ` を `⟨a⟩` に制限すると、`⟨a⟩` は巡回ゆえ
可解で、位数は `|A|` を割るので互いに素性も保たれ、補助形が適用できる。 -/
theorem aFixed_quotient_frattini
    {φ : A →* MulAut G} (hCop : Nat.Coprime (Nat.card A) (Nat.card G))
    (h_triv_quot : ∀ a : A, ∀ g : G, ∃ x ∈ (_root_.frattini G), (φ a) g = g * x) :
    ∀ a : A, ∀ g : G, (φ a) g = g := by
  intro a g
  have : Group.IsSolvable ↥(Subgroup.zpowers a) := by
    let : CommGroup ↥(Subgroup.zpowers a) := IsCyclic.commGroup
    infer_instance
  have hcop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers a)) (Nat.card G) :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _) hCop
  have hres := aFixed_quotient_frattini_of_isSolvable
    (φ := φ.comp (Subgroup.zpowers a).subtype) hcop' (Or.inl inferInstance)
    (fun b g' => h_triv_quot (b : A) g')
  exact hres ⟨a, Subgroup.mem_zpowers a⟩ g

end FrattiniAction

end OddOrder.Isaacs.Ch04


