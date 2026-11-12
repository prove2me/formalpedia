-- Prove2me | Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupTypeConj
-- name    : OddOrder_GroupTheory_MaximalSubgroupTypeConj
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:38:35.799654+00:00
-- url     : https://prove2.me/theorems/dbcfacaa-8c7b-4a32-ab0f-dfb0eb9a828a
-- title:
--   Conjugation invariance of the maximal-subgroup types
-- statement:
--   The Peterfalvi maximal-subgroup taxonomy (`IsTypeF`, `IsTypeI`, …, `IsTypeV`) is defined intrinsically from a subgroup $M\le G$ via constructions (the Fitting kernel `maxNilpotentNormalHall M`, complements, centralizers, exponents, ranks) that are natural under automorphisms of $G$. This file makes that precise: each type predicate is invariant under the pointwise `MulAut` action, via equivariance lemmas for the constructions involved.
--
--   Main declarations: `conjSubgroupEquiv` (The restricted isomorphism `↥K ≃* ↥(φ • K)` induced by `φ : MulAut G`); `conj` (`TypeFData` is automorphism-equivariant); `conj` (`TypeIData` is automorphism-equivariant); `conj` (`TypePData` is automorphism-equivariant); and 11 more.
--
--   The bundle also proves 29 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/MaximalSubgroupTypeConj.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType

namespace OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

section Toolkit

variable (φ : MulAut G)

/-- The restricted isomorphism `↥K ≃* ↥(φ • K)` induced by `φ : MulAut G`. -/
noncomputable def conjSubgroupEquiv (K : Subgroup G) : ↥K ≃* ↥(φ • K) :=
  (Subgroup.equivMapOfInjective K (φ : G →* G) φ.injective).trans
    (MulEquiv.subgroupCongr (pointwise_mulAut_smul_eq_map φ K).symm)

/-- `|φ • K| = |K|`: the pointwise `MulAut` action preserves cardinality. -/
theorem card_pointwise_smul (K : Subgroup G) :
    Nat.card ↥(φ • K) = Nat.card ↥K := by
  rw [pointwise_mulAut_smul_eq_map]; exact Subgroup.card_map_of_injective φ.injective

/-- The pointwise `MulAut` action preserves the trivial subgroup test. -/
@[simp] theorem pointwise_smul_eq_bot_iff {K : Subgroup G} :
    φ • K = ⊥ ↔ K = ⊥ := by
  rw [pointwise_mulAut_smul_eq_map, Subgroup.map_eq_bot_iff_of_injective _ φ.injective]

/-- `IsCyclic` transfers along the pointwise `MulAut` action. -/
theorem isCyclic_pointwise_smul {K : Subgroup G} (h : IsCyclic ↥K) :
    IsCyclic ↥(φ • K) :=
  isCyclic_of_surjective _ (conjSubgroupEquiv φ K).surjective

/-- `IsMulCommutative` transfers along any group isomorphism. -/
theorem isMulCommutative_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : IsMulCommutative A) : IsMulCommutative B :=
  ⟨⟨fun a b => e.symm.injective (by rw [map_mul, map_mul, h.is_comm.comm])⟩⟩

/-- `IsMulCommutative` transfers along the pointwise `MulAut` action. -/
theorem isMulCommutative_pointwise_smul {K : Subgroup G} (h : IsMulCommutative ↥K) :
    IsMulCommutative ↥(φ • K) :=
  isMulCommutative_of_mulEquiv (conjSubgroupEquiv φ K) h

/-- `Monoid.exponent` is invariant under any group isomorphism. -/
theorem exponent_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Monoid.exponent A = Monoid.exponent B :=
  Monoid.exponent_eq_of_mulEquiv e

/-- `Monoid.exponent` is invariant under the pointwise `MulAut` action. -/
theorem exponent_pointwise_smul (K : Subgroup G) :
    Monoid.exponent ↥(φ • K) = Monoid.exponent ↥K :=
  (exponent_of_mulEquiv (conjSubgroupEquiv φ K)).symm

/-- The coercion of `φ • K` to a set is the `φ`-image of `K`. -/
theorem coe_pointwise_smul (K : Subgroup G) :
    ((φ • K : Subgroup G) : Set G) = φ '' (K : Set G) := by
  rw [pointwise_mulAut_smul_eq_map]; exact Subgroup.coe_map _ _

/-- The pointwise `MulAut` action commutes with the centralizer of a set. -/
theorem centralizer_pointwise_smul (X : Set G) :
    φ • Subgroup.centralizer X = Subgroup.centralizer (φ '' X) := by
  rw [pointwise_mulAut_smul_eq_map]
  exact Subgroup.map_centralizer_eq_of_bijective X (φ : G →* G) φ.bijective

/-- The pointwise `MulAut` action commutes with the normalizer of a subgroup. -/
theorem normalizer_pointwise_smul (H : Subgroup G) :
    φ • Subgroup.normalizer (H : Set G) = Subgroup.normalizer ((φ • H : Subgroup G) : Set G) := by
  rw [pointwise_mulAut_smul_eq_map φ (Subgroup.normalizer (H : Set G)),
    show (φ • H : Subgroup G) = H.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ H]
  exact Subgroup.map_normalizer_eq_of_bijective H φ.bijective

/-- `sharpSubgroup` (nonidentity elements) is equivariant under the pointwise `MulAut` action. -/
theorem image_sharpSubgroup (H : Subgroup G) :
    φ '' sharpSubgroup H = sharpSubgroup (φ • H) := by
  unfold sharpSubgroup
  rw [Set.image_sdiff φ.injective, coe_pointwise_smul]
  congr 1
  rw [Set.image_singleton, map_one]

/-- The pointwise `MulAut` action commutes with the normalizer of an arbitrary subset:
`φ • normalizer X = normalizer (φ '' X)`.  (The subgroup version `normalizer_pointwise_smul` is the
special case `X = (H : Set G)`.) -/
theorem normalizer_image_pointwise_smul (X : Set G) :
    φ • Subgroup.normalizer X = Subgroup.normalizer (φ '' X) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, Subgroup.mem_set_normalizer_iff,
    Subgroup.mem_set_normalizer_iff]
  -- `φ⁻¹ • g` acts as `φ.symm g`; membership `z ∈ φ '' X` is `φ.symm z ∈ X`.
  have hg : (φ⁻¹ • g : G) = φ.symm g := rfl
  have himg : ∀ z : G, z ∈ φ '' X ↔ φ.symm z ∈ X := fun z => by
    constructor
    · rintro ⟨w, hw, rfl⟩; rwa [φ.symm_apply_apply]
    · intro hz; exact ⟨φ.symm z, hz, φ.apply_symm_apply z⟩
  rw [hg]
  constructor
  · intro h y
    rw [himg y, himg (g * y * g⁻¹)]
    have key := h (φ.symm y)
    have e2 : φ.symm (g * y * g⁻¹) = φ.symm g * φ.symm y * (φ.symm g)⁻¹ := by
      simp [map_mul, map_inv]
    rw [e2]; exact key
  · intro h y
    have key := h (φ y)
    rw [himg (φ y), himg (g * φ y * g⁻¹), φ.symm_apply_apply,
      show φ.symm (g * φ y * g⁻¹) = φ.symm g * y * (φ.symm g)⁻¹ by
        simp [map_mul, map_inv, φ.symm_apply_apply]] at key
    exact key

/-- `IsTISubset` transfers along the pointwise `MulAut` action. -/
theorem isTISubset_pointwise_smul {A : Set G} {L : Subgroup G} (h : IsTISubset A L) :
    IsTISubset (φ '' A) (φ • L) := by
  rintro g ⟨a', ⟨a, ha, rfl⟩, b, hb, hgb⟩
  rw [pointwise_mulAut_smul_eq_map]
  refine ⟨φ.symm g, h (φ.symm g) ⟨a, ha, ?_⟩, φ.apply_symm_apply g⟩
  -- `hgb : φ b = g * φ a * g⁻¹`; apply `φ⁻¹` to read off the conjugate of `a` by `φ.symm g`.
  have hconj : φ.symm g * a * (φ.symm g)⁻¹ = b := by
    apply φ.injective
    rw [map_mul, map_mul, map_inv, φ.apply_symm_apply]
    exact hgb.symm
  rw [hconj]; exact hb

/-- `IsCoatom` (maximality) transfers along the pointwise `MulAut` action: conjugates of a
maximal subgroup are maximal.  Reusable replacement for the downstream `private`
`isCoatom_conj_smul` copies (S10/S11/S12). -/
theorem isCoatom_pointwise_smul {M : Subgroup G} (h : IsCoatom M) :
    IsCoatom (φ • M) := by
  rw [pointwise_mulAut_smul_eq_map]
  exact (OrderIso.isCoatom_iff (φ.mapSubgroup) M).mpr h

end Toolkit

section TransferAlongMulEquiv

variable {A B : Type*} [Group A] [Group B]

/-- `IsComplement'` transfers along a group isomorphism (finite source). -/
theorem isComplement'_map_of_mulEquiv [Finite A] (e : A ≃* B) {N K : Subgroup A}
    (h : N.IsComplement' K) :
    (N.map (e : A →* B)).IsComplement' (K.map (e : A →* B)) := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  rw [Subgroup.isComplement'_iff_card_mul_and_disjoint] at h ⊢
  obtain ⟨hcard, hdisj⟩ := h
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective e.injective, Subgroup.card_map_of_injective e.injective,
      ← Nat.card_congr e.toEquiv]
    exact hcard
  · rw [disjoint_iff, ← Subgroup.map_inf_eq N K (e : A →* B) e.injective, disjoint_iff.mp hdisj,
      Subgroup.map_bot]

/-- `IsFrobeniusGroup` transfers along a group isomorphism (finite source). -/
theorem isFrobeniusGroup_map_of_mulEquiv [Finite A] (e : A ≃* B) {N K : Subgroup A}
    (h : Ch06.IsFrobeniusGroup A N K) :
    Ch06.IsFrobeniusGroup B (N.map (e : A →* B)) (K.map (e : A →* B)) := by
  refine ⟨h.isNormal.map (e : A →* B) e.surjective, isComplement'_map_of_mulEquiv e h.isComplement,
    mt (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h.ne_bot_kernel,
    mt (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h.ne_bot_complement, ?_⟩
  intro a ha hane n hn hnne
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
  have ha₀ne : a₀ ≠ 1 := fun h => hane (by rw [h, map_one])
  have hn₀ne : n₀ ≠ 1 := fun h => hnne (by rw [h, map_one])
  intro hcontra
  apply h.conj_frobenius a₀ ha₀ ha₀ne n₀ hn₀ hn₀ne
  apply e.injective
  rw [map_mul, map_mul, map_inv]
  exact hcontra

/-- The `p`-rank is invariant under a group isomorphism (finite source). -/
theorem pRank_eq_of_mulEquiv [Finite A] (e : A ≃* B) (p : ℕ) :
    pRank A p = pRank B p := by
  have : Finite B := Finite.of_equiv A e.toEquiv
  exact le_antisymm (pRank_le_of_injective (f := e.toMonoidHom) e.injective)
    (pRank_le_of_injective (f := e.symm.toMonoidHom) e.symm.injective)

/-- The group rank `r(G)` is invariant under a group isomorphism (finite source). -/
theorem rank_of_mulEquiv [Finite A] (e : A ≃* B) : rank A = rank B :=
  iSup_congr fun p => pRank_eq_of_mulEquiv e p.1

end TransferAlongMulEquiv

section OpiCore

variable [Finite G] (φ : MulAut G)

omit [Finite G] in
/-- **`opiCoreInG` is `MulAut`-equivariant**: `φ • O_π(H) = O_π(φ • H)`.  The `π`-core
`oPiCore π ↥H` is characteristic, so the iso `↥H ≃* ↥(φ•H)` induced by `φ` carries it onto
`oPiCore π ↥(φ•H)`. -/
theorem opiCoreInG_pointwise_smul (π : Set ℕ) (H : Subgroup G) :
    φ • opiCoreInG π H = opiCoreInG π (φ • H) := by
  have hHmap : H.map (φ : G →* G) = φ • H := (pointwise_mulAut_smul_eq_map φ H).symm
  let e : ↥H ≃* ↥(φ • H) :=
    (Subgroup.equivMapOfInjective H (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hHmap)
  have hcomp : (φ • H).subtype.comp (e : ↥H →* ↥(φ • H)) = (φ : G →* G).comp H.subtype := by
    ext x; rfl
  calc φ • opiCoreInG π H
      = (opiCoreInG π H).map (φ : G →* G) := pointwise_mulAut_smul_eq_map φ _
    _ = ((Ch03.oPiCore π ↥H).map H.subtype).map (φ : G →* G) := rfl
    _ = (Ch03.oPiCore π ↥H).map ((φ : G →* G).comp H.subtype) := by rw [Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥H).map ((φ • H).subtype.comp (e : ↥H →* ↥(φ • H))) := by rw [hcomp]
    _ = ((Ch03.oPiCore π ↥H).map (e : ↥H →* ↥(φ • H))).map (φ • H).subtype := by
        rw [← Subgroup.map_map]
    _ = (Ch03.oPiCore π ↥(φ • H)).map (φ • H).subtype := by
        rw [Ch03.oPiCore.map_eq_of_mulEquiv]
    _ = opiCoreInG π (φ • H) := rfl

end OpiCore

section SubgroupOfTransfer

variable [Finite G] (φ : MulAut G)

/-- `IsComplement'` of `subgroupOf`-subgroups transfers along the pointwise `MulAut` action. -/
theorem isComplement'_subgroupOf_pointwise_smul {H U M : Subgroup G}
    (h : Subgroup.IsComplement' (H.subgroupOf M) (U.subgroupOf M)) :
    Subgroup.IsComplement' ((φ • H).subgroupOf (φ • M)) ((φ • U).subgroupOf (φ • M)) := by
  rw [show (φ • H : Subgroup G) = H.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ H,
    show (φ • U : Subgroup G) = U.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ U,
    show (φ • M : Subgroup G) = M.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ M,
    ← map_subgroupMap_subgroupOf, ← map_subgroupMap_subgroupOf]
  exact isComplement'_map_of_mulEquiv (φ.subgroupMap M) h

omit [Finite G] in
/-- Normality of a `subgroupOf`-subgroup transfers along the pointwise `MulAut` action. -/
theorem normal_subgroupOf_pointwise_smul {N U : Subgroup G} (h : (N.subgroupOf U).Normal) :
    ((φ • N).subgroupOf (φ • U)).Normal := by
  rw [show (φ • N : Subgroup G) = N.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ N,
    show (φ • U : Subgroup G) = U.map (φ : G →* G) from pointwise_mulAut_smul_eq_map φ U,
    ← map_subgroupMap_subgroupOf]
  exact h.map (φ.subgroupMap U : ↥U →* ↥(U.map (φ : G →* G))) (φ.subgroupMap U).surjective

/-- The Frobenius witness `IsFrobeniusGroup ↥(H ⊔ U0) (H.subgroupOf _) (U0.subgroupOf _)` transfers
along the pointwise `MulAut` action. -/
theorem isFrobeniusGroup_subgroupOf_pointwise_smul {H U0 : Subgroup G}
    (h : Ch06.IsFrobeniusGroup ↥(H ⊔ U0) (H.subgroupOf (H ⊔ U0)) (U0.subgroupOf (H ⊔ U0))) :
    Ch06.IsFrobeniusGroup ↥(φ • H ⊔ φ • U0)
      ((φ • H).subgroupOf (φ • H ⊔ φ • U0)) ((φ • U0).subgroupOf (φ • H ⊔ φ • U0)) := by
  have e := isFrobeniusGroup_map_of_mulEquiv (φ.subgroupMap (H ⊔ U0)) h
  rw [map_subgroupMap_subgroupOf, map_subgroupMap_subgroupOf,
    ← pointwise_mulAut_smul_eq_map φ H, ← pointwise_mulAut_smul_eq_map φ U0,
    ← pointwise_mulAut_smul_eq_map φ (H ⊔ U0), Subgroup.smul_sup] at e
  exact e

omit [Finite G] in
/-- The centralizer-bound field of `TypeFData` transfers along the pointwise `MulAut` action. -/
theorem inf_centralizer_le_pointwise_smul {H U U1 : Subgroup G}
    (h : ∀ x ∈ H, x ≠ 1 → U ⊓ Subgroup.centralizer ({x} : Set G) ≤ U1) :
    ∀ x ∈ φ • H, x ≠ 1 → (φ • U) ⊓ Subgroup.centralizer ({x} : Set G) ≤ φ • U1 := by
  intro x hx hxne
  rw [pointwise_mulAut_smul_eq_map] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyne : y ≠ 1 := fun hy1 => hxne (by rw [← hyx, hy1, map_one])
  have hxset : ({x} : Set G) = φ '' ({y} : Set G) := by rw [Set.image_singleton, ← hyx]; rfl
  rw [hxset, ← centralizer_pointwise_smul, ← Subgroup.smul_inf]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr (h y hy hyne)

omit [Finite G] in
/-- **`derivedInG` is `MulAut`-equivariant**: `φ • M' = (φ • M)'`.  The derived subgroup
`commutator ↥M` transports along the iso `↥M ≃* ↥(φ•M)` induced by `φ`, and the composition
`(φ•M).subtype ∘ conjSubgroupEquiv = φ ∘ M.subtype` carries it to `derivedInG (φ • M)`.  Reproved
locally so this file does not depend on the private `smul_derivedInG_conj` of `S13_PrimeAction`. -/
theorem derivedInG_pointwise_smul (M : Subgroup G) :
    φ • derivedInG M = derivedInG (φ • M) := by
  have hMmap : M.map (φ : G →* G) = φ • M := (pointwise_mulAut_smul_eq_map φ M).symm
  let e : ↥M ≃* ↥(φ • M) :=
    (Subgroup.equivMapOfInjective M (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hMmap)
  have hcomp : (φ • M).subtype.comp (e : ↥M →* ↥(φ • M)) = (φ : G →* G).comp M.subtype := by
    ext x; rfl
  have hcomm : (commutator ↥M).map (e : ↥M →* ↥(φ • M)) = commutator ↥(φ • M) := by
    rw [map_commutator_eq, MonoidHom.range_eq_map, Subgroup.map_top_of_surjective _ e.surjective]
    rfl
  calc φ • derivedInG M
      = (derivedInG M).map (φ : G →* G) := pointwise_mulAut_smul_eq_map φ _
    _ = ((commutator ↥M).map M.subtype).map (φ : G →* G) := rfl
    _ = (commutator ↥M).map ((φ : G →* G).comp M.subtype) := by rw [Subgroup.map_map]
    _ = (commutator ↥M).map ((φ • M).subtype.comp (e : ↥M →* ↥(φ • M))) := by rw [hcomp]
    _ = ((commutator ↥M).map (e : ↥M →* ↥(φ • M))).map (φ • M).subtype := by rw [← Subgroup.map_map]
    _ = (commutator ↥(φ • M)).map (φ • M).subtype := by rw [hcomm]
    _ = derivedInG (φ • M) := rfl

omit [Finite G] in
/-- **`secondDerivedInAmbient` is `MulAut`-equivariant**: `φ • M'' = (φ • M)''`.  Immediate from
applying `derivedInG_pointwise_smul` twice (`M'' = (M')'`). -/
theorem secondDerivedInAmbient_pointwise_smul (M : Subgroup G) :
    φ • secondDerivedInAmbient M = secondDerivedInAmbient (φ • M) := by
  unfold secondDerivedInAmbient
  rw [derivedInG_pointwise_smul, derivedInG_pointwise_smul]

omit [Finite G] in
/-- **Nilpotency transfers along the pointwise `MulAut` action**: if `↥K` is nilpotent then so is
`↥(φ • K)`, via the iso `conjSubgroupEquiv φ K : ↥K ≃* ↥(φ • K)`. -/
theorem isNilpotent_pointwise_smul {K : Subgroup G} (h : Group.IsNilpotent ↥K) :
    Group.IsNilpotent ↥(φ • K) :=
  Group.nilpotent_of_mulEquiv (conjSubgroupEquiv φ K)

/-- **The ambient Fitting subgroup `F(↥M).map M.subtype` is `MulAut`-equivariant**:
`(F(↥(φ•M))).map (φ•M).subtype = φ • ((F(↥M)).map M.subtype)`.  The Fitting subgroup is functorial
under the iso `conjSubgroupEquiv φ M : ↥M ≃* ↥(φ•M)` (`fitting_map_eq_of_mulEquiv'`), and the
composition `(φ•M).subtype ∘ conjSubgroupEquiv = φ ∘ M.subtype` relocates the image. -/
theorem fitting_map_subtype_pointwise_smul (M : Subgroup G) :
    (OddOrder.Isaacs.Ch01.fitting ↥(φ • M)).map (φ • M).subtype =
      φ • ((OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype) := by
  have hMmap : M.map (φ : G →* G) = φ • M := (pointwise_mulAut_smul_eq_map φ M).symm
  let e : ↥M ≃* ↥(φ • M) :=
    (Subgroup.equivMapOfInjective M (φ : G →* G) φ.injective).trans
      (MulEquiv.subgroupCongr hMmap)
  have hcomp : (φ • M).subtype.comp (e : ↥M →* ↥(φ • M)) = (φ : G →* G).comp M.subtype := by
    ext x; rfl
  -- `F(↥M)` transports along the iso `e`.
  have hfit : (OddOrder.Isaacs.Ch01.fitting ↥M).map (e : ↥M →* ↥(φ • M)) =
      OddOrder.Isaacs.Ch01.fitting ↥(φ • M) := by
    refine le_antisymm ?_ ?_
    · have : ((OddOrder.Isaacs.Ch01.fitting ↥M).map (e : ↥M →* ↥(φ • M))).Normal :=
        Subgroup.Normal.map inferInstance (e : ↥M →* ↥(φ • M)) e.surjective
      have : Group.IsNilpotent ↥((OddOrder.Isaacs.Ch01.fitting ↥M).map (e : ↥M →* ↥(φ • M))) :=
        Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ (e : ↥M →* ↥(φ • M))
            e.injective)
      exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    · -- pull back along `e.symm`
      have h2 : (OddOrder.Isaacs.Ch01.fitting ↥(φ • M)).map (e.symm : ↥(φ • M) →* ↥M) ≤
          OddOrder.Isaacs.Ch01.fitting ↥M := by
        have : ((OddOrder.Isaacs.Ch01.fitting ↥(φ • M)).map (e.symm : ↥(φ • M) →* ↥M)).Normal :=
          Subgroup.Normal.map inferInstance (e.symm : ↥(φ • M) →* ↥M) e.symm.surjective
        have : Group.IsNilpotent
            ↥((OddOrder.Isaacs.Ch01.fitting ↥(φ • M)).map (e.symm : ↥(φ • M) →* ↥M)) :=
          Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ (e.symm : ↥(φ • M) →* ↥M)
            e.symm.injective)
        exact OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
      have h3 := Subgroup.map_mono (f := (e : ↥M →* ↥(φ • M))) h2
      rwa [Subgroup.map_map, ← MulEquiv.coe_monoidHom_trans, MulEquiv.symm_trans_self,
        MulEquiv.coe_monoidHom_refl, Subgroup.map_id] at h3
  calc (OddOrder.Isaacs.Ch01.fitting ↥(φ • M)).map (φ • M).subtype
      = ((OddOrder.Isaacs.Ch01.fitting ↥M).map (e : ↥M →* ↥(φ • M))).map (φ • M).subtype := by
        rw [hfit]
    _ = (OddOrder.Isaacs.Ch01.fitting ↥M).map ((φ • M).subtype.comp (e : ↥M →* ↥(φ • M))) := by
        rw [Subgroup.map_map]
    _ = (OddOrder.Isaacs.Ch01.fitting ↥M).map ((φ : G →* G).comp M.subtype) := by rw [hcomp]
    _ = ((OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype).map (φ : G →* G) := by
        rw [← Subgroup.map_map]
    _ = φ • ((OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype) :=
        (pointwise_mulAut_smul_eq_map φ _).symm

end SubgroupOfTransfer

variable [Finite G]

/-- **`TypeFData` is automorphism-equivariant.**  All structural data of a type-`F` subgroup
transfers along `φ : MulAut G`, giving type-`F` data for `φ • M`. -/
def TypeFData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeFData M) :
    TypeFData (φ • M) where
  H := φ • data.H
  U := φ • data.U
  U1 := φ • data.U1
  U0 := φ • data.U0
  H_eq := by rw [data.H_eq, maxNilpotentNormalHall_pointwise_smul]
  H_nontrivial := mt (pointwise_smul_eq_bot_iff φ).mp data.H_nontrivial
  U_nontrivial := mt (pointwise_smul_eq_bot_iff φ).mp data.U_nontrivial
  H_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.H_le
  U_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U_le
  U1_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U1_le
  U0_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U0_le
  complement := isComplement'_subgroupOf_pointwise_smul φ data.complement
  U1_normal := normal_subgroupOf_pointwise_smul φ data.U1_normal
  U1_commutative := isMulCommutative_pointwise_smul φ data.U1_commutative
  centralizer_le_U1 := inf_centralizer_le_pointwise_smul φ data.centralizer_le_U1
  exponent_eq := by rw [exponent_pointwise_smul, exponent_pointwise_smul]; exact data.exponent_eq
  frobenius_HU0 := isFrobeniusGroup_subgroupOf_pointwise_smul φ data.frobenius_HU0

/-- **`TypeIData` is automorphism-equivariant.** -/
def TypeIData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeIData M) :
    TypeIData (φ • M) where
  typeF := data.typeF.conj φ
  alternative := by
    rcases data.alternative with h | h | h
    · left
      have hti := isTISubset_pointwise_smul φ h
      rwa [image_sharpSubgroup, normalizer_pointwise_smul] at hti
    · right; left
      refine ⟨isMulCommutative_pointwise_smul φ h.1, ?_⟩
      change rank ↥(φ • data.typeF.H) = 2
      rw [← rank_of_mulEquiv (conjSubgroupEquiv φ data.typeF.H)]; exact h.2
    · right; right
      obtain ⟨h1, p, hp, hpmem, hcyc⟩ := h
      have hcard : Nat.card ↥(φ • data.typeF.H) = Nat.card ↥data.typeF.H := card_pointwise_smul φ _
      change (∀ q : ℕ, q.Prime → q ∈ (Nat.card ↥(φ • data.typeF.H)).primeFactors →
          Monoid.exponent ↥(φ • data.typeF.U) ∣ q - 1) ∧
        ∃ q : ℕ, q.Prime ∧ q ∈ (Nat.card ↥(φ • data.typeF.H)).primeFactors ∧
          IsCyclic ↥(opiCoreInG {q}ᶜ (φ • data.typeF.H))
      refine ⟨fun q hq hqmem => ?_, p, hp, by rwa [hcard], ?_⟩
      · rw [exponent_pointwise_smul]; exact h1 q hq (by rwa [hcard] at hqmem)
      · rw [← opiCoreInG_pointwise_smul]; exact isCyclic_pointwise_smul φ hcyc

/-- **`IsTypeI` is invariant under the pointwise `MulAut` action.** -/
theorem isTypeI_pointwise_smul (φ : MulAut G) {M : Subgroup G} (h : IsTypeI M) :
    IsTypeI (φ • M) :=
  ⟨h.some.conj φ⟩

omit [Finite G] in
/-- The centralizer of the `φ`-image of a subgroup is the `φ`-image of the centralizer:
`centralizer ((φ • H : Subgroup G) : Set G) = φ • centralizer (H : Set G)`.  A convenience
repackaging of `centralizer_pointwise_smul` with `coe_pointwise_smul` for the `TypePData` fields. -/
private theorem centralizer_coe_pointwise_smul (φ : MulAut G) (H : Subgroup G) :
    Subgroup.centralizer ((φ • H : Subgroup G) : Set G) = φ • Subgroup.centralizer (H : Set G) := by
  rw [centralizer_pointwise_smul, coe_pointwise_smul]

/-- **`TypePData` is automorphism-equivariant.**  All structural data of a type-`P` subgroup
(the derived-series presentation `M = M' ⋊ W₁`, `M' = M_F ⋊ U`, `W = W₁ × W₂`, the Fitting
identity `F(M) = H · C_U(H)`, and the exceptional set's normalizer) transfers along `φ : MulAut G`,
giving type-`P` data for `φ • M`. -/
def TypePData.conj (φ : MulAut G) {M : Subgroup G} (data : TypePData M) :
    TypePData (φ • M) where
  H := φ • data.H
  U := φ • data.U
  W1 := φ • data.W1
  W2 := φ • data.W2
  W := φ • data.W
  H_eq := by rw [data.H_eq, maxNilpotentNormalHall_pointwise_smul]
  H_le := by
    rw [← derivedInG_pointwise_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.H_le
  U_le := by
    rw [← derivedInG_pointwise_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.U_le
  W1_le := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.W1_le
  W2_le := by
    rw [← secondDerivedInAmbient_pointwise_smul, ← Subgroup.smul_inf]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.W2_le
  W_eq := by rw [data.W_eq, Subgroup.smul_sup]
  W_cyclic := isCyclic_pointwise_smul φ data.W_cyclic
  W1_nontrivial := mt (pointwise_smul_eq_bot_iff φ).mp data.W1_nontrivial
  W2_nontrivial := mt (pointwise_smul_eq_bot_iff φ).mp data.W2_nontrivial
  W1_cyclic := isCyclic_pointwise_smul φ data.W1_cyclic
  W2_cyclic := isCyclic_pointwise_smul φ data.W2_cyclic
  M_complement := by
    rw [← derivedInG_pointwise_smul]
    exact isComplement'_subgroupOf_pointwise_smul φ data.M_complement
  W1_normalizes_U := by
    rw [← normalizer_pointwise_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.W1_normalizes_U
  U_nilpotent := isNilpotent_pointwise_smul φ data.U_nilpotent
  derived_complement := by
    rw [← derivedInG_pointwise_smul]
    exact isComplement'_subgroupOf_pointwise_smul φ data.derived_complement
  H_noncyclic := by
    intro hcyc
    apply data.H_noncyclic
    have := isCyclic_pointwise_smul φ⁻¹ hcyc
    rwa [inv_smul_smul] at this
  secondDerived_le_fitting := by
    rw [← secondDerivedInAmbient_pointwise_smul, centralizer_coe_pointwise_smul,
      ← Subgroup.smul_inf, ← Subgroup.smul_sup]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.secondDerived_le_fitting
  fitting_eq := by
    rw [fitting_map_subtype_pointwise_smul, data.fitting_eq, Subgroup.smul_sup, Subgroup.smul_inf,
      centralizer_coe_pointwise_smul]
  centralizer_W1 := by
    intro x hx hxne
    rw [pointwise_mulAut_smul_eq_map] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyne : y ≠ 1 := fun hy1 => hxne (by rw [← hyx, hy1, map_one])
    have hxset : ({x} : Set G) = φ '' ({y} : Set G) := by rw [Set.image_singleton, ← hyx]; rfl
    rw [hxset, ← centralizer_pointwise_smul, ← derivedInG_pointwise_smul, ← Subgroup.smul_inf,
      data.centralizer_W1 y hy hyne]
  normalizer_V := by
    intro X hXne hXsub
    -- pull `X` back to `Y = φ.symm '' X` and apply `data.normalizer_V`
    set Y : Set G := φ.symm '' X with hY
    have hYne : Y.Nonempty := hXne.image _
    -- every `data.K` is the `φ.symm`-image of `φ • data.K`
    have hback : ∀ K : Subgroup G,
        ((K : Subgroup G) : Set G) = φ.symm '' ((φ • K : Subgroup G) : Set G) := fun K => by
      rw [coe_pointwise_smul, ← Set.image_comp]; simp [Function.comp]
    have hYsub : Y ⊆ (data.W : Set G) \ ((data.W1 : Set G) ∪ (data.W2 : Set G)) := by
      rw [hback data.W, hback data.W1, hback data.W2, hY, ← Set.image_union,
        ← Set.image_sdiff φ.symm.injective]
      exact Set.image_mono hXsub
    have hnorm := data.normalizer_V Y hYne hYsub
    -- `X = φ '' Y`, so `normalizer X = φ • normalizer Y = φ • W`.
    have hXeq : X = φ '' Y := by
      rw [hY, ← Set.image_comp]; simp [Function.comp]
    rw [hXeq, ← normalizer_image_pointwise_smul, hnorm]

/-- **`TypePNontrivialCore` transfers along the pointwise `MulAut` action.**  The common type II–IV
hypotheses (`U ≠ 1`, `|W₁|` prime, and the TI condition on `M_F#`) hold for `(φ • M)` with the
conjugated witness `data.conj φ`. -/
theorem typePNontrivialCore_conj (φ : MulAut G) {M : Subgroup G} {data : TypePData M}
    (h : TypePNontrivialCore M data) : TypePNontrivialCore (φ • M) (data.conj φ) := by
  refine ⟨mt (pointwise_smul_eq_bot_iff φ).mp h.1, ?_, ?_⟩
  · rw [show (data.conj φ).W1 = φ • data.W1 from rfl, card_pointwise_smul]; exact h.2.1
  · have hti := isTISubset_pointwise_smul φ h.2.2
    rwa [image_sharpSubgroup, normalizer_pointwise_smul, maxNilpotentNormalHall_pointwise_smul]
      at hti

/-- **`TypeIIData` is automorphism-equivariant.** -/
def TypeIIData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeIIData M) :
    TypeIIData (φ • M) where
  typeP := data.typeP.conj φ
  common := typePNontrivialCore_conj φ data.common
  U_commutative := isMulCommutative_pointwise_smul φ data.U_commutative
  normalizer_not_le := by
    intro hle
    apply data.normalizer_not_le
    -- from `normalizer (φ•U) ≤ φ•M` deduce `normalizer U ≤ M` via `φ.symm`
    rw [show (data.typeP.conj φ).U = φ • data.typeP.U from rfl, ← normalizer_pointwise_smul] at hle
    have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := φ⁻¹).mpr hle
    rwa [inv_smul_smul, inv_smul_smul] at this
  derived_typeF := by
    rw [← derivedInG_pointwise_smul]
    exact ⟨data.derived_typeF.some.conj φ⟩
  derived_fitting_eq := by
    rw [show (data.typeP.conj φ).H = φ • data.typeP.H from rfl, ← derivedInG_pointwise_smul,
      ← maxNilpotentNormalHall_pointwise_smul, data.derived_fitting_eq]

/-- **`TypeIIIData` is automorphism-equivariant.** -/
def TypeIIIData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeIIIData M) :
    TypeIIIData (φ • M) where
  typeP := data.typeP.conj φ
  common := typePNontrivialCore_conj φ data.common
  U_commutative := isMulCommutative_pointwise_smul φ data.U_commutative
  normalizer_le := by
    rw [show (data.typeP.conj φ).U = φ • data.typeP.U from rfl, ← normalizer_pointwise_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.normalizer_le

/-- **`TypeIVData` is automorphism-equivariant.** -/
def TypeIVData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeIVData M) :
    TypeIVData (φ • M) where
  typeP := data.typeP.conj φ
  common := typePNontrivialCore_conj φ data.common
  U_not_commutative := by
    intro hcomm
    apply data.U_not_commutative
    have := isMulCommutative_pointwise_smul φ⁻¹ hcomm
    rwa [show (data.typeP.conj φ).U = φ • data.typeP.U from rfl, inv_smul_smul] at this
  normalizer_le := by
    rw [show (data.typeP.conj φ).U = φ • data.typeP.U from rfl, ← normalizer_pointwise_smul]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr data.normalizer_le

/-- **`TypeVData` is automorphism-equivariant.** -/
def TypeVData.conj (φ : MulAut G) {M : Subgroup G} (data : TypeVData M) :
    TypeVData (φ • M) where
  typeP := data.typeP.conj φ
  U_eq_bot := by
    rw [show (data.typeP.conj φ).U = φ • data.typeP.U from rfl, data.U_eq_bot,
      Subgroup.smul_bot]
  alternative := by
    have hH : (data.typeP.conj φ).H = φ • data.typeP.H := rfl
    have hW1 : (data.typeP.conj φ).W1 = φ • data.typeP.W1 := rfl
    have hcardH : Nat.card ↥(φ • data.typeP.H) = Nat.card ↥data.typeP.H := card_pointwise_smul φ _
    have hcardW1 : Nat.card ↥(φ • data.typeP.W1) = Nat.card ↥data.typeP.W1 :=
      card_pointwise_smul φ _
    rcases data.alternative with h | h | h
    · left
      have hti := isTISubset_pointwise_smul φ h
      rw [hH]
      rwa [image_sharpSubgroup, normalizer_pointwise_smul] at hti
    · right; left
      obtain ⟨p, hp, hpmem, hdvd, hcyc⟩ := h
      rw [hH, hW1]
      refine ⟨p, hp, by rwa [hcardH], by rwa [hcardW1], ?_⟩
      rw [← opiCoreInG_pointwise_smul]; exact isCyclic_pointwise_smul φ hcyc
    · right; right
      obtain ⟨p, hp, hpmem, hcube, hdvd, hcyc⟩ := h
      rw [hH, hW1]
      refine ⟨p, hp, by rwa [hcardH], ?_, by rwa [hcardW1], ?_⟩
      · rw [← opiCoreInG_pointwise_smul, card_pointwise_smul]; exact hcube
      · rw [← opiCoreInG_pointwise_smul]; exact isCyclic_pointwise_smul φ hcyc

/-- **`IsTypeII` is invariant under the pointwise `MulAut` action.** -/
theorem isTypeII_pointwise_smul (φ : MulAut G) {M : Subgroup G} (h : IsTypeII M) :
    IsTypeII (φ • M) :=
  ⟨h.some.conj φ⟩

/-- **`IsTypeIII` is invariant under the pointwise `MulAut` action.** -/
theorem isTypeIII_pointwise_smul (φ : MulAut G) {M : Subgroup G} (h : IsTypeIII M) :
    IsTypeIII (φ • M) :=
  ⟨h.some.conj φ⟩

/-- **`IsTypeIV` is invariant under the pointwise `MulAut` action.** -/
theorem isTypeIV_pointwise_smul (φ : MulAut G) {M : Subgroup G} (h : IsTypeIV M) :
    IsTypeIV (φ • M) :=
  ⟨h.some.conj φ⟩

/-- **`IsTypeV` is invariant under the pointwise `MulAut` action.** -/
theorem isTypeV_pointwise_smul (φ : MulAut G) {M : Subgroup G} (h : IsTypeV M) :
    IsTypeV (φ • M) :=
  ⟨h.some.conj φ⟩

/-- **`HasPeterfalviType` is invariant under the pointwise `MulAut` action.**  For every one of the
five Peterfalvi types `tau`, conjugate maximal subgroups have the same type.  This is the general
form needed at Peterfalvi (8.17.a) `exists_second_maximal`, where the covering maximal subgroup
`L₀` of BG Theorem E has an arbitrary type `tau` that must be preserved under the Sylow conjugation
relocating `P₀` into `L₀`. -/
theorem hasPeterfalviType_pointwise_smul (φ : MulAut G) (tau : PeterfalviType) {M : Subgroup G}
    (h : HasPeterfalviType tau M) : HasPeterfalviType tau (φ • M) := by
  cases tau with
  | I => exact isTypeI_pointwise_smul φ h
  | II => exact isTypeII_pointwise_smul φ h
  | III => exact isTypeIII_pointwise_smul φ h
  | IV => exact isTypeIV_pointwise_smul φ h
  | V => exact isTypeV_pointwise_smul φ h

/-- **`mainSubgroup` is `MulAut`-equivariant**: `φ • mainSubgroup M tau = mainSubgroup (φ • M) tau`
for every Peterfalvi type `tau`.  The subgroup `M_s` is `M_F` (types I, II, V) or `M'` (types III,
IV), both of which transport along `φ` (`maxNilpotentNormalHall_pointwise_smul` /
`derivedInG_pointwise_smul`). -/
theorem mainSubgroup_pointwise_smul (φ : MulAut G) (M : Subgroup G) (tau : PeterfalviType) :
    φ • mainSubgroup M tau = mainSubgroup (φ • M) tau := by
  cases tau with
  | I => exact maxNilpotentNormalHall_pointwise_smul φ M
  | II => exact maxNilpotentNormalHall_pointwise_smul φ M
  | III => exact derivedInG_pointwise_smul φ M
  | IV => exact derivedInG_pointwise_smul φ M
  | V => exact maxNilpotentNormalHall_pointwise_smul φ M

end OddOrder.GroupTheory


