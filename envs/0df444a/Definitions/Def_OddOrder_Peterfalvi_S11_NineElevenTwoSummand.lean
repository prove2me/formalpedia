-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTwoSummand
-- name    : OddOrder_Peterfalvi_S11_NineElevenTwoSummand
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:28:33.650767+00:00
-- url     : https://prove2.me/theorems/9c1d6c56-abae-4d5a-8165-18c75ce033d2
-- title:
--   Peterfalvi (9.11.2): two-summand inertia inputs $[U:K_1]=[U:K_2]=a$
-- statement:
--   Formalizes the two-summand inertia inputs of Peterfalvi (9.11.2) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §9, p. 56): $[U:K_1]=[U:K_2]=a$ and $C=K_1\cap K_2$.
--
--   Main declarations: `hInHu_inf_cuInHuPair_eq_bot` (`H ⊓ (C_U(H_i) ⊓ C_U(H_j)) = ⊥`); `hInHu_isComplement'_cuInHuPair` (`H` and `C_U(H_i) ⊓ C_U(H_j)` are complementary inside `H·K`); `nineElevenTwoThetaHom` (The `θ₀`-extension hom `H·K → ℂˣ`); `nineElevenTwoThetaHom_inclusion_hInHu` (`nineElevenTwoThetaHom` restricts to `θ₀` on `H`).
--
--   The bundle also proves 14 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenTwoSummand.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenTwoSummand.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCoherence

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

section NineElevenTwoSummandCharacter

variable [Finite G] {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

omit [Finite G] in
/-- **`H ⊓ (C_U(H_i) ⊓ C_U(H_j)) = ⊥`** realized (`hInHu ⊓ cuInHuPair = ⊥`).  Since
`C_U(H_i) ⊓ C_U(H_j) ≤ U`, an element of the intersection has `G`-image in `H ⊓ U = ⊥`
(`typeP_H_inf_U`).  Mirror of `hInHu_inf_cuInHu_eq_bot` for the pair centralizer; the
trivial-intersection input of the semidirect complement `hInHu_isComplement'_cuInHuPair`. -/
theorem hInHu_inf_cuInHuPair_eq_bot (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    hInHu data ⊓ cuInHuPair caseA i j = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxU := cuInHuPair_le_uInHu caseA i j hxC
  rw [Subgroup.mem_bot]
  have hxH' : x ∈ (data.H.subgroupOf M).subgroupOf (huSub data) := hxH
  have hxU' : x ∈ (data.U.subgroupOf M).subgroupOf (huSub data) := hxU
  have keyH : ((x : ↥M) : G) ∈ data.H :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxH')
  have keyU : ((x : ↥M) : G) ∈ data.U :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp hxU')
  have key : ((x : ↥M) : G) ∈ data.typeP.H ⊓ data.typeP.U := ⟨keyH, keyU⟩
  rw [typeP_H_inf_U data.typeP, Subgroup.mem_bot] at key
  exact Subtype.ext (Subtype.ext key)

omit [Finite G] in
/-- **`H` and `C_U(H_i) ⊓ C_U(H_j)` are complementary inside `H·K`** (`IsComplement'` of the two
`subgroupOf`-realizations in the join): `H ⊓ K = ⊥` (`hInHu_inf_cuInHuPair_eq_bot`) gives
disjointness, `H ⊔ K` is the whole ambient by construction.  The complement input to
`SemidirectProduct.mulEquivSubgroup`, exhibiting `H·K ≃* H ⋊[φ] K`.  Mirror of
`hInHu_isComplement'_cuInHu_in_hcuInHu`. -/
theorem hInHu_isComplement'_cuInHuPair (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    ((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)).IsComplement'
      ((cuInHuPair caseA i j).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)) := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)).Normal :=
    (hInHu_normal data).subgroupOf _
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · rw [disjoint_iff]
    change (hInHu data).comap _ ⊓ (cuInHuPair caseA i j).comap _ = ⊥
    rw [← Subgroup.comap_inf (hInHu data) (cuInHuPair caseA i j)
      (hInHu data ⊔ cuInHuPair caseA i j).subtype, hInHu_inf_cuInHuPair_eq_bot caseA i j]
    simp
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, Subgroup.coe_top]

/-- **`hcuSeedHom`-invariance under the two-summand centralizer** (Peterfalvi (9.11.2)): for a
two-summand-supported `θ` (trivial off `H_i`, `H_j`), the seed hom `θ₀ = θ ∘ mk'(N) ∘ hInHuEquivH`
is invariant under conjugation by `K = cuInHuPair`-elements.  The `ClassFunction`-level invariance
is the landed `cuInHuPair_le_inertia` (`K` centralizes both supporting summands, hence fixes `θ`);
it descends to the hom level because `θ₀` is the `linearClassFunction` of `hcuSeedHom θ` and
`ℂˣ → ℂ` is injective.  Mirror of `hcuSeedHom_invariance_of_cuInHu_le_inertia`; the `lift`
compatibility of `nineElevenTwoThetaHom`. -/
theorem hcuSeedHom_two_summand_invariance (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, θ x = 1) :
    ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h := by
  have := hInHu_normal data
  have hle := cuInHuPair_le_inertia caseA θ hsupp
  intro c h
  have hconj : ClassFunction.conjBy (c : ↥(huSub data))
      (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :=
    ClassFunction.mem_inertia.mp (hle c.2)
  have hval := congrFun (congrArg (fun f : ClassFunction ↥(hInHu data) ℂ =>
    (f : ↥(hInHu data) → ℂ)) hconj) h
  simp only [ClassFunction.conjBy_apply, ClassFunction.compHom_linearIrreducibleCharacter,
    linearIrreducibleCharacter_apply] at hval
  refine Units.val_injective ?_
  simpa only [hcuSeedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hval

/-- **The `θ₀`-extension hom `H·K →* ℂˣ`** (Peterfalvi (9.11.2)): the extension of the seed hom
`θ ∘ mk'(N) ∘ hInHuEquivH` from the normal factor `H` to `H·K` (`K = cuInHuPair`, the two-summand
centralizer), trivial on the complement `K`.  Built by `SemidirectProduct.lift` through the
complement iso `hInHu_isComplement'_cuInHuPair`; the `lift` `φ`-compatibility is the
`K`-invariance of `θ₀` (`hinv`, supplied by `hcuSeedHom_two_summand_invariance`), using that the
codomain `ℂˣ` is abelian.  Restricts to `θ₀` on `H` (`nineElevenTwoThetaHom_inclusion_hInHu`).
Mirror of the (9.8.d) `hcuThetaHom` with `C_U(S₀)` replaced by the pair centralizer — this is the
book's `θ ∈ Irr(H̄C)` with `H₃⋯H_qC ⊆ Ker θ`, realized on the full inertia subgroup `H·K`. -/
noncomputable def nineElevenTwoThetaHom (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h) :
    ↥(hInHu data ⊔ cuInHuPair caseA i j) →* ℂˣ :=
  haveI := hInHu_normal data
  haveI : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)).Normal :=
    (hInHu_normal data).subgroupOf _
  (SemidirectProduct.lift
      ((hcuSeedHom (chief := chief) θ).comp
        (Subgroup.subgroupOfEquivOfLe
          (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j)).toMonoidHom)
      (1 : ↥((cuInHuPair caseA i j).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)) →* ℂˣ)
      (by
        intro c
        ext h
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.one_apply, map_one,
          MulAut.one_apply]
        set c' := (Subgroup.subgroupOfEquivOfLe
          (le_sup_right : cuInHuPair caseA i j ≤ hInHu data ⊔ cuInHuPair caseA i j)) c with hc'
        set h' := (Subgroup.subgroupOfEquivOfLe
          (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j)) h with hh'
        have harg : (Subgroup.subgroupOfEquivOfLe
              (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j))
            ((((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)).normalizerMonoidHom
              ((Subgroup.inclusion (((hInHu data).subgroupOf
                (hInHu data ⊔ cuInHuPair caseA i j)).normalizer_eq_top ▸ le_top)) c)) h)
            = ⟨(c' : ↥(huSub data)) * (h' : ↥(huSub data)) * (c' : ↥(huSub data))⁻¹,
                (hInHu_normal data).conj_mem _ h'.2 (c' : ↥(huSub data))⟩ := by
          apply Subtype.ext
          simp only [hc', hh', Subgroup.subgroupOfEquivOfLe_apply_coe,
            Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion,
            Subgroup.coe_mul, Subgroup.coe_inv]
        rw [harg]
        exact congrArg (Units.val) (hinv c' h'))).comp
    (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHuPair caseA i j)).symm.toMonoidHom

set_option backward.isDefEq.respectTransparency false in
/-- **`nineElevenTwoThetaHom` restricts to `θ₀` on `H`**: on the inclusion of `h ∈ H` into `H·K`,
the extension returns the seed value `hcuSeedHom θ h`.  Via `SemidirectProduct.lift_inl` after
`(mulEquivSubgroup).symm (inclusion h) = inl h`.  Mirror of `hcuThetaHom_inclusion_hInHu`. -/
theorem nineElevenTwoThetaHom_inclusion_hInHu (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (h : ↥(hInHu data)) :
    nineElevenTwoThetaHom caseA θ hinv (Subgroup.inclusion
        (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h)
      = hcuSeedHom (chief := chief) θ h := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)).Normal :=
    (hInHu_normal data).subgroupOf _
  have hsymm : (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHuPair caseA i j)).symm
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h)
      = SemidirectProduct.inl
        (⟨Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h,
          Subgroup.mem_subgroupOf.mpr h.2⟩ :
          ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j))) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [SemidirectProduct.mulEquivSubgroup, MulEquiv.ofBijective_apply,
      SemidirectProduct.monoidHomSubgroup_apply, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, OneMemClass.coe_one, mul_one]
  simp only [nineElevenTwoThetaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    SemidirectProduct.lift_inl]
  congr 1

set_option backward.isDefEq.respectTransparency false in
/-- **`nineElevenTwoThetaHom` kills the complement `K = C_U(H_i) ⊓ C_U(H_j)`**: on the inclusion
of `c ∈ cuInHuPair` into `H·K`, the extension returns `1` (its complement-part hom in the
`SemidirectProduct.lift` is `1`).  Via `SemidirectProduct.lift_inr`.  Mirror of
`hcuThetaHom_inclusion_cuInHu`; in particular the extension kills `C ≤ K`, giving the book's
`C ⊆ Ker θ`. -/
theorem nineElevenTwoThetaHom_inclusion_cuInHuPair (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (c : ↥(cuInHuPair caseA i j)) :
    nineElevenTwoThetaHom caseA θ hinv (Subgroup.inclusion
        (le_sup_right : cuInHuPair caseA i j ≤ hInHu data ⊔ cuInHuPair caseA i j) c) = 1 := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j)).Normal :=
    (hInHu_normal data).subgroupOf _
  have hsymm : (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHuPair caseA i j)).symm
      (Subgroup.inclusion (le_sup_right : cuInHuPair caseA i j
        ≤ hInHu data ⊔ cuInHuPair caseA i j) c)
      = SemidirectProduct.inr
        (⟨Subgroup.inclusion (le_sup_right : cuInHuPair caseA i j
            ≤ hInHu data ⊔ cuInHuPair caseA i j) c,
          Subgroup.mem_subgroupOf.mpr c.2⟩ :
          ↥((cuInHuPair caseA i j).subgroupOf (hInHu data ⊔ cuInHuPair caseA i j))) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [SemidirectProduct.mulEquivSubgroup, MulEquiv.ofBijective_apply,
      SemidirectProduct.monoidHomSubgroup_apply, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, OneMemClass.coe_one, one_mul]
  simp only [nineElevenTwoThetaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    SemidirectProduct.lift_inr, MonoidHom.one_apply]

/-- **The `H·K`-linear character `ψ`** of the (9.11.2) construction: the linear (degree-one)
irreducible character of the inertia subgroup `H·K` with hom `nineElevenTwoThetaHom` — the book's
`θ ∈ Irr(H̄C)` with `H₃⋯H_qC ⊆ Ker θ`, extended to its full `HU`-inertia.  Mirror of `hcuPsiPair`
(with trivial `λ`-factor). -/
noncomputable def nineElevenTwoPsi (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h) :
    IrreducibleCharacter ↥(hInHu data ⊔ cuInHuPair caseA i j) :=
  linearIrreducibleCharacter (nineElevenTwoThetaHom caseA θ hinv)

/-- **`ψ|_H = θ₀`** (pointwise): on the inclusion of `h ∈ H` the (9.11.2) character equals the
seed's inflation `θ₀`.  Mirror of `hcuPsiPair_apply_inclusion` (no `λ`-factor). -/
theorem nineElevenTwoPsi_apply_inclusion (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (h : ↥(hInHu data)) :
    (nineElevenTwoPsi caseA θ hinv : ClassFunction ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h)
      = (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        h := by
  simp only [nineElevenTwoPsi, linearIrreducibleCharacter_apply,
    nineElevenTwoThetaHom_inclusion_hInHu, hcuSeedHom, MonoidHom.comp_apply,
    ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom, linearIrreducibleCharacter_apply]

/-- **Restriction-inertia `inertia(ψ) ≤ inertia(θ₀)`**: an element fixing the (9.11.2) character
also fixes its `H`-restriction `θ₀` (`nineElevenTwoPsi_apply_inclusion`).  Mirror of
`hcuPsiPair_inertia_le`. -/
theorem nineElevenTwoPsi_inertia_le (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [(hInHu data ⊔ cuInHuPair caseA i j).Normal] :
    ClassFunction.inertia (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)
      ≤ ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  have := hInHu_normal data
  intro g hg
  rw [ClassFunction.mem_inertia] at hg ⊢
  ext h
  have key : (ClassFunction.conjBy g (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ))
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h)
      = (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h) := by
    rw [hg]
  rw [ClassFunction.conjBy_apply] at key ⊢
  rw [← nineElevenTwoPsi_apply_inclusion caseA θ hinv,
    ← nineElevenTwoPsi_apply_inclusion caseA θ hinv, ← key]
  congr 1

/-- **`inertia(ψ) = H·K`** (Peterfalvi (9.11.2), `I(θ) = H·(U₁ ∩ U₁^w)`): with the landed seed
inertia `inertia(θ₀) = H·K` (`caseA_inertia_eq_hcuInHuPair`, for `θ` regular on `H_i`, `H_j` and
trivial elsewhere), the (9.11.2) character's `HU`-inertia is exactly the subgroup it lives on.
Mirror of `hcuPsiPair_inertia_eq_hcu`.  Feeds `isIrreducibleCharacter_induce_of_inertia_eq`. -/
theorem nineElevenTwoPsi_inertia_eq (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [(hInHu data ⊔ cuInHuPair caseA i j).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHuPair caseA i j) :
    ClassFunction.inertia (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)
      = hInHu data ⊔ cuInHuPair caseA i j := by
  apply le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  refine le_trans (nineElevenTwoPsi_inertia_le caseA θ hinv) ?_
  rw [hθ₀]

/-- **`ζ = Ind_{HK}^{HU} ψ` is irreducible** (Peterfalvi (9.11.2), the (1.6)/(1.7.c) step): direct
from `isIrreducibleCharacter_induce_of_inertia_eq` and `inertia(ψ) = H·K`
(`nineElevenTwoPsi_inertia_eq`).  The linear source induced from its **full inertia group** is
irreducible with degree exactly the index — the realized form of the book's "`χ(1) =
|U : I(θ) ∩ U|·θ(1)` by (1.6) and (1.7.c) applied to `(HU)/(H₀C)`". -/
theorem nineElevenTwoZeta_irreducible (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ)]
    [(hInHu data ⊔ cuInHuPair caseA i j).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHuPair caseA i j) :
    IsIrreducibleCharacter (ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
      (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHuPair caseA i j) := Fintype.ofFinite _
  exact OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq
    (nineElevenTwoPsi caseA θ hinv)
    (nineElevenTwoPsi_inertia_eq caseA θ hinv hθ₀)

/-- **`ζ(1) = [U : C_U(H_i) ⊓ C_U(H_j)]`** (Peterfalvi (9.11.2), the induced degree): the source
character has degree `[HU : H·K]·ψ(1) = [U:K]·1`, via the landed index chain
`index_hcuInHuPair_eq_relindex_cuInHuPair` + `index_cuInHuPair_subgroupOf_uInHu_eq_relIndex`.
Mirror of `hcuZetaPair_apply_one`. -/
theorem nineElevenTwoZeta_apply_one (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ)] :
    ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)
        (1 : ↥(huSub data))
      = (((cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U : ℕ) : ℂ) := by
  rw [ClassFunction.induce_apply_one, index_hcuInHuPair_eq_relindex_cuInHuPair caseA i j,
    index_cuInHuPair_subgroupOf_uInHu_eq_relIndex caseA i j,
    show (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)
        (1 : ↥(hInHu data ⊔ cuInHuPair caseA i j)) = 1 from by
      simp [nineElevenTwoPsi], mul_one]

/-- **`Ind_{HU}^M ζ (1) = q·[U : C_U(H_i) ⊓ C_U(H_j)]`** (Peterfalvi (9.11.2), full member
degree): `[M:HU]·ζ(1) = q·[U:K]`.  Mirror of `hcuZetaPair_induceHU_apply_one`.  Under the
(9.11.1) equality configuration this member degree is `qu` or `qa`, forcing
`[U:K] ∈ {u, a}` — the (9.11.2) dichotomy. -/
theorem nineElevenTwoZeta_induceHU_apply_one (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ)] :
    induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ) : ClassFunction ↥(huSub data) ℂ) (1 : ↥M)
      = ((data.q * ((cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U) : ℕ) : ℂ) := by
  rw [induceHU_apply_one_eq_q_mul, nineElevenTwoZeta_apply_one, Nat.cast_mul]

/-- **`realized H₀C ≤ H·K`**: the (9.11.2) kernel subgroup `H₀C` realized inside `HU` lies in the
inertia subgroup `H·K`.  `H₀ ≤ H ⟶ hInHu` and `C ≤ K` (`cInHu_le_cuInHuPair`), through the
decomposition `realized H₀C = realized H₀ ⊔ cInHu`.  Mirror of `realizedH0supUprime_le_hcuInHu`. -/
theorem realizedH0supC_le_hcuInHuPair (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data ⊔ cuInHuPair caseA i j := by
  rw [realizedH0supC_eq_realizedH0_sup_cInHu]
  refine sup_le (le_trans ?_ le_sup_left)
    (le_trans (cInHu_le_cuInHuPair caseA i j) le_sup_right)
  exact Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ chief.H0_lt_H.le)

/-- **The extension kills `H₀C`** (hom-level, pointwise): every `x` in the realized `H₀C` inside
`H·K` lies in the kernel of `nineElevenTwoThetaHom`.  Decompose `x = h₀·c`
(`realizedH0supC_eq_realizedH0_sup_cInHu`, `H₀ ◁ HU`): the seed kills `h₀ ∈ H₀`
(`hcuSeedHom_eq_one_of_mem_realizedH0`) and the extension dies on `c ∈ C ≤ K`
(`nineElevenTwoThetaHom_inclusion_cuInHuPair`).  Mirror of
`hcuPairHom_eq_one_of_mem_realizedH0supUprime` (no `λ`-factor). -/
theorem nineElevenTwoThetaHom_eq_one_of_mem_realizedH0supC (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    {x : ↥(hInHu data ⊔ cuInHuPair caseA i j)}
    (hx : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ cuInHuPair caseA i j)) :
    nineElevenTwoThetaHom caseA θ hinv x = 1 := by
  have := hInHu_normal data
  have hval : (x : ↥(huSub data))
      ∈ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.mem_subgroupOf.mp hx
  rw [realizedH0supC_eq_realizedH0_sup_cInHu] at hval
  have hH0n : ((chief.H0.subgroupOf M).subgroupOf (huSub data)).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (chief.H0_lt_H.le.trans (H_le_M data))).mpr
      chief.H0_normalized_by_M).subgroupOf (huSub data)
  obtain ⟨h₀, hh₀, c, hc, hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hval
  have hh₀H : h₀ ∈ hInHu data :=
    Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ chief.H0_lt_H.le) hh₀
  have hcK : c ∈ cuInHuPair caseA i j := cInHu_le_cuInHuPair caseA i j hc
  have hxfact : x = Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data))
      * Subgroup.inclusion le_sup_right (⟨c, hcK⟩ : ↥(cuInHuPair caseA i j)) :=
    Subtype.ext hxeq.symm
  have h1 : nineElevenTwoThetaHom caseA θ hinv
      (Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data)))
      = hcuSeedHom (chief := chief) θ ⟨h₀, hh₀H⟩ :=
    nineElevenTwoThetaHom_inclusion_hInHu caseA θ hinv ⟨h₀, hh₀H⟩
  have h1' : hcuSeedHom (chief := chief) θ (⟨h₀, hh₀H⟩ : ↥(hInHu data)) = 1 :=
    hcuSeedHom_eq_one_of_mem_realizedH0 chief θ (Subgroup.mem_subgroupOf.mpr hh₀)
  have h2 : nineElevenTwoThetaHom caseA θ hinv
      (Subgroup.inclusion le_sup_right (⟨c, hcK⟩ : ↥(cuInHuPair caseA i j))) = 1 :=
    nineElevenTwoThetaHom_inclusion_cuInHuPair caseA θ hinv ⟨c, hcK⟩
  rw [hxfact, map_mul, h1, h1', one_mul, h2]

/-- **`H₀C ⊆ Ker ψ`** as a `Set` inclusion (`H·K`-level): the realized `H₀C` is contained in the
character kernel of the (9.11.2) character (pointwise
`nineElevenTwoThetaHom_eq_one_of_mem_realizedH0supC`).  Mirror of
`hcuPsiPair_realizedH0supUprime_subgroupOf_subset_characterKernel`. -/
theorem nineElevenTwoPsi_realizedH0supC_subgroupOf_subset_characterKernel
    (caseA : CliffordCaseAData chars) {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h) :
    ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ cuInHuPair caseA i j) :
        Set ↥(hInHu data ⊔ cuInHuPair caseA i j)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (nineElevenTwoPsi caseA θ hinv) := by
  intro x hx
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [nineElevenTwoPsi]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one,
    nineElevenTwoThetaHom_eq_one_of_mem_realizedH0supC caseA θ hinv (SetLike.mem_coe.mp hx),
    Units.val_one]

set_option maxHeartbeats 1000000 in
-- the induced-kernel transfer elaborates the full `subgroupOf`-realization chain
-- (same cost profile as the mirror `hcuZetaPair_H0supUprime_subset_ker`)
/-- **`H₀C ⊆ Ker ζ`**: the realized `H₀C` lies in the character kernel of
`ζ = Ind_{HK}^{HU} ψ`.  Since `ψ` is `1` on `H₀C` and `H₀C ◁ HU`
(`realizedH0supC_normal_huSub`), the normal subgroup lands in the induced kernel
(`subsetCharacterKernel_induce_of_subgroupOf`).  Mirror of `hcuZetaPair_H0supUprime_subset_ker`. -/
theorem nineElevenTwoZeta_H0supC_subset_ker (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ)] :
    ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHuPair caseA i j) := Fintype.ofFinite _
  have := realizedH0supC_normal_huSub chief
  exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ cuInHuPair caseA i j)
    (realizedH0supC_le_hcuInHuPair caseA i j)
    (nineElevenTwoPsi caseA θ hinv)
    (nineElevenTwoPsi_realizedH0supC_subgroupOf_subset_characterKernel caseA θ hinv)

set_option maxHeartbeats 1000000 in
-- the `LiesOver` extraction re-elaborates the bundled induced irreducible over the
-- realized join (same cost profile as the mirror `hcZetaPair_mem_xiSet`)
/-- **`H ⊄ Ker ζ`** (`ζ ∈ 𝒳`): the irreducible `ζ = Ind_{HK}^{HU} ψ` is nontrivial on
`H = hInHu`.  The induced character lies over `ψ` (Frobenius reciprocity), whose `hInHu`-values
are the inflation `θ₀`; `H ⊆ Ker` would force `θ = 1`.  Mirror of `hcZetaPair_mem_xiSet`. -/
theorem nineElevenTwoZeta_mem_xiSet (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ)]
    [(hInHu data ⊔ cuInHuPair caseA i j).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHuPair caseA i j) :
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ),
        nineElevenTwoZeta_irreducible caseA θ hinv hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  classical
  have : Fintype ↥(hInHu data ⊔ cuInHuPair caseA i j) := Fintype.ofFinite _
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
      (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ),
      nineElevenTwoZeta_irreducible caseA θ hinv hθ₀⟩ with hζdef
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ cuInHuPair caseA i j) ζ (nineElevenTwoPsi caseA θ hinv) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  rw [xiSet, Set.mem_ofPred_eq]
  intro hsub
  apply hθnt
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  refine MonoidHom.ext fun q => ?_
  obtain ⟨h, hhq⟩ := hfsurj q
  have hgmem : ((Subgroup.inclusion
      (le_sup_left :
        hInHu data ≤ hInHu data ⊔ cuInHuPair caseA i j) h :
        ↥(hInHu data ⊔ cuInHuPair caseA i j)) : ↥(huSub data)) ∈ hInHu data := by
    rw [Subgroup.coe_inclusion]; exact SetLike.coe_mem h
  have hψker := liesOver_mem_characterKernel hlo (hsub hgmem)
  have hψ1 : (nineElevenTwoPsi caseA θ hinv : ClassFunction
      ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ) 1 = 1 := by
    simp [nineElevenTwoPsi]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    nineElevenTwoPsi_apply_inclusion caseA θ hinv h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = q := hhq
  rw [hqeq] at hψker
  change θ q = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

set_option maxHeartbeats 1000000 in
-- re-elaborates the two bundled membership components over the realized join
-- (same cost profile as the mirror `hcZetaPair_mem_xiOf`)
/-- **`ζ ∈ 𝒳(H₀C)`**: combining `H ⊄ Ker` (`nineElevenTwoZeta_mem_xiSet`) and `H₀C ⊆ Ker`
(`nineElevenTwoZeta_H0supC_subset_ker`).  This is the source character of the (9.11.2)
`𝒮(H₀C)`-member `Ind_{HU}^M ζ` of degree `q·[U : C_U(H_i) ⊓ C_U(H_j)]`.  Mirror of
`hcZetaPair_mem_xiOf`. -/
theorem nineElevenTwoZeta_mem_xiOf (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1)
    (hinv : ∀ c : ↥(cuInHuPair caseA i j), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ)]
    [(hInHu data ⊔ cuInHuPair caseA i j).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHuPair caseA i j) :
    (⟨ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ),
        nineElevenTwoZeta_irreducible caseA θ hinv hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiOf data (chief.H0 ⊔ cSub data chief) := by
  rw [mem_xiOf]
  exact ⟨nineElevenTwoZeta_mem_xiSet caseA θ hθnt hinv hθ₀,
    nineElevenTwoZeta_H0supC_subset_ker caseA θ hinv⟩

end NineElevenTwoSummandCharacter

section CentralizerIntersection

variable [Finite G] {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

/-- **Centralizing every summand ⟹ centralizing the chief factor** (action level): a `U`-element
acting trivially on every Clifford summand `H_k` (`aInvariantRestrictAut … = 1` for all `k`) acts
trivially on all of `H̄` (`uActionHom g = 1`), since the summands span (`Hpart_iSup`,
`Subgroup.iSup_induction`).  Converse of `centralizes_all_imp_centralizes_summand`; the
`⋂ₖ C_U(H_k) ≤ C` direction of the book's `C = ⋂_{1≤i≤q} C_U(H_i)` in (9.11.2). -/
theorem uActionHom_eq_one_of_forall_summand (caseA : CliffordCaseAData chars)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hg : ∀ k, aInvariantRestrictAut (caseA.Hpart_aInvariant k) g = 1) :
    (uActionHom data chief) g = 1 := by
  ext x
  rw [MulAut.one_apply]
  have hx : x ∈ ⨆ k, caseA.Hpart k := caseA.Hpart_iSup ▸ Subgroup.mem_top x
  refine Subgroup.iSup_induction (C := fun z => (uActionHom data chief) g z = z)
    caseA.Hpart hx (fun k z hz => ?_) (map_one _) (fun y z hy hz => by rw [map_mul, hy, hz])
  have h := aInvariantRestrictAut_coe (caseA.Hpart_aInvariant k) g ⟨z, hz⟩
  rw [hg k] at h
  simpa [MulAut.one_apply] using h.symm

/-- **`⋂ₖ C_U(H_k) ≤ C` realized**: a `G`-element lying in every single-factor centralizer
`cuSubOf caseA k` lies in `C = cSub`.  Extracts the abstract `U`-element witness through the
double-`subtype` realization (`mem_ker_of_realized_mem_cuSubOf` per summand), applies the
action-level span argument (`uActionHom_eq_one_of_forall_summand`), and rebuilds the `cSub`
membership.  With `cSub_le_cuSubOf` this is the realized `C = ⋂ₖ C_U(H_k)` of (9.11.2). -/
theorem mem_cSub_of_forall_mem_cuSubOf (caseA : CliffordCaseAData chars) {g : G}
    (hg : ∀ k, g ∈ cuSubOf caseA k) : g ∈ cSub data chief := by
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hgU : g ∈ data.typeP.U := cuSubOf_le_U caseA ⟨0, hq⟩ (hg ⟨0, hq⟩)
  have hgUW1 : g ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨g, hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : g = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hker : ∀ k, aInvariantRestrictAut (caseA.Hpart_aInvariant k) a = 1 := fun k =>
    MonoidHom.mem_ker.mp (mem_ker_of_realized_mem_cuSubOf caseA k a (hag ▸ hg k))
  have hact : (uActionHom data chief) a = 1 :=
    uActionHom_eq_one_of_forall_summand caseA a hker
  exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨a, MonoidHom.mem_ker.mpr hact, rfl⟩, rfl⟩

end CentralizerIntersection

section NineElevenTwoInertiaIdentity

variable [Finite G] {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

/-- **Peterfalvi (9.11.2), the index dichotomy `[U : C_U(H_i) ⊓ C_U(H_j)] ∈ {u, a}`.**

Book: *"Let `χ` be an irreducible component of `Ind_{HC}^{HU} θ`.  By (1.6) and (1.7.c) applied
to the group `(HU)/(H₀C)`, `χ(1) = |U : I(θ) ∩ U|·θ(1) = |U : U₁ ∩ U₁^w|`.  By (9.11.1),
`χ(1) = u` or `a`."*  The two-summand character `θ` (`exists_caseA_two_summand_char`) extends to
the linear `ψ` on its inertia `H·K` (`nineElevenTwoPsi`; invariance from
`cuInHuPair_le_inertia`), whose induction `ζ` is irreducible of degree `[U:K]`
(`nineElevenTwoZeta_irreducible`/`_apply_one`, seed inertia `caseA_inertia_eq_hcuInHuPair`) and
lies in `𝒳(H₀C)` (`nineElevenTwoZeta_mem_xiOf`); the member `Ind_{HU}^M ζ ∈ 𝒮(H₀C)` has degree
`q·[U:K]`, which `hdeg` pins to `qu` or `qa`; cancel `q`. -/
theorem nineElevenTwo_relIndex_dichotomy (caseA : CliffordCaseAData chars)
    {i j : Fin data.q} (hij : i ≠ j)
    (hdeg : ∀ φ ∈ sOf data (chief.H0 ⊔ cSub data chief),
      (φ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U = chars.u ∨
      (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U = caseA.a := by
  classical
  have : Fintype ↥M := Fintype.ofFinite _
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ cuInHuPair caseA i j) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Invertible (Nat.card ↥(hInHu data ⊔ cuInHuPair caseA i j) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ cuInHuPair caseA i j).Normal := hcuInHuPair_normal caseA i j
  -- the two-summand character and its regularity/support data
  obtain ⟨θ, hθi, hθj, hθtriv⟩ := exists_caseA_two_summand_char caseA hij
  have hθne : θ ≠ 1 := by
    obtain ⟨x, -, hxne⟩ := hθi
    exact fun h1 => hxne (by rw [h1, MonoidHom.one_apply])
  have hregi : ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    obtain ⟨x, hx, hxne⟩ := hθi
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      Units.val_one]
    exact fun h => hxne (Units.val_eq_one.mp h)
  have hregj : ∃ x ∈ caseA.Hpart j,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    obtain ⟨x, hx, hxne⟩ := hθj
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      Units.val_one]
    exact fun h => hxne (Units.val_eq_one.mp h)
  have hinv := hcuSeedHom_two_summand_invariance caseA θ hθtriv
  have hθ₀ := caseA_inertia_eq_hcuInHuPair caseA θ hθtriv hregi hregj
  -- the (9.11.2) member of `𝒮(H₀C)` and its degree `q·[U:K]`
  have hmem : induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
      (nineElevenTwoPsi caseA θ hinv : ClassFunction
        ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ) : ClassFunction ↥(huSub data) ℂ)
      ∈ sOf data (chief.H0 ⊔ cSub data chief) :=
    ⟨⟨ClassFunction.induce (hInHu data ⊔ cuInHuPair caseA i j)
        (nineElevenTwoPsi caseA θ hinv : ClassFunction
          ↥(hInHu data ⊔ cuInHuPair caseA i j) ℂ),
        nineElevenTwoZeta_irreducible caseA θ hinv hθ₀⟩,
      nineElevenTwoZeta_mem_xiOf caseA θ hθne hinv hθ₀, rfl⟩
  have hφ1 := nineElevenTwoZeta_induceHU_apply_one caseA θ hinv
  have hqpos : 0 < data.q := data.nontrivial.2.1.pos
  rcases hdeg _ hmem with h | h
  · exact Or.inl (Nat.eq_of_mul_eq_mul_left hqpos
      (Nat.cast_injective (hφ1.symm.trans h)))
  · exact Or.inr (Nat.eq_of_mul_eq_mul_left hqpos
      (Nat.cast_injective (hφ1.symm.trans h)))

/-- **Peterfalvi (9.11.2), the two-summand inertia inputs `[U:K₁] = [U:K₂] = a`, `C = K₁ ⊓ K₂`**
(issue 9083 Phase B).

Book: *"if `w ∈ W₁^#` then `U₁ ∩ U₁^w = C`; moreover `u ≤ a²`"* — exactly the `hK₁`/`hK₂`/`hCinf`
inputs of `nineElevenCaseA_equality_refutation` (whose `nineElevenTwo_u_le_a_sq` derives
`u ≤ a²`).  The degree-dichotomy hypothesis `hdeg` is the (9.11.1) equality-configuration fact
that every member of `𝒮(H₀C) ⊆ 𝒮(H₀C′)` has degree `qu` or `qa` (the `𝒮₃`-side is the landed
squeeze output `hS3deg`; the `𝒮₂`-side is the `𝒮₂ = 𝒮₁` saturated-bound extraction, issue 9083
Phase E).

Resolution of the per-pair dichotomy `[U : C_U(H_i) ⊓ C_U(H_j)] ∈ {u, a}`
(`nineElevenTwo_relIndex_dichotomy`), pair-uniformly:

* if **some** pair has index `u`: then `C ≤ C_U(H_i) ⊓ C_U(H_j)` with equal relative index
  `[U:C] = u` (`relIndex_cSub_U_eq_u`), so `C = C_U(H_i) ⊓ C_U(H_j)` (strict index monotonicity
  `relIndex_lt_relIndex_of_le_of_ne`), and `K₁ = C_U(H_i)`, `K₂ = C_U(H_j)` have `[U:K] = a`
  (`relIndex_cuSubOf_U_eq_a`);
* if **every** pair has index `a`: then each `C_U(H_i) ⊓ C_U(H_j)` equals both factors (index
  `a` each, strict monotonicity), so all `C_U(H_k)` coincide, and `C = ⋂ₖ C_U(H_k)`
  (`mem_cSub_of_forall_mem_cuSubOf` + `cSub_le_cuSubOf`) equals the common centralizer; take
  `K₁ = K₂ = C_U(H_0)` (then `C = K₁ ⊓ K₂` with `[U:K] = a`, and downstream `u = [U:C] = a ≤ a²`
  holds trivially — the book's `u ≠ a` contradiction is absorbed, not needed). -/
theorem nineElevenTwo_two_summand_inertia (caseA : CliffordCaseAData chars)
    (hdeg : ∀ φ ∈ sOf data (chief.H0 ⊔ cSub data chief),
      (φ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    ∃ K₁ K₂ : Subgroup G, K₁.relIndex data.U = caseA.a ∧ K₂.relIndex data.U = caseA.a ∧
      chars.C = K₁ ⊓ K₂ := by
  classical
  have hq1 : 1 < data.q := data.nontrivial.2.1.one_lt
  by_cases hex : ∃ i j : Fin data.q, i ≠ j ∧
      (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U = chars.u
  · -- some pair has index `u`: `C = C_U(H_i) ⊓ C_U(H_j)` by index equality
    obtain ⟨i, j, hij, hu⟩ := hex
    refine ⟨cuSubOf caseA i, cuSubOf caseA j, relIndex_cuSubOf_U_eq_a caseA i,
      relIndex_cuSubOf_U_eq_a caseA j, ?_⟩
    have hCle : cSub data chief ≤ cuSubOf caseA i ⊓ cuSubOf caseA j :=
      le_inf (cSub_le_cuSubOf caseA i) (cSub_le_cuSubOf caseA j)
    have hCeq : cSub data chief = cuSubOf caseA i ⊓ cuSubOf caseA j := by
      by_contra hne
      have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne hCle
        (inf_le_left.trans (cuSubOf_le_U caseA i)) (fun h => hne h.symm)
      rw [hu, relIndex_cSub_U_eq_u chars] at hlt
      exact lt_irrefl _ hlt
    simp only [Section11CharacterData.C]
    exact hCeq
  · -- every pair has index `a`: all single-factor centralizers coincide with `C`
    push Not at hex
    have hall : ∀ i j : Fin data.q, i ≠ j →
        (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U = caseA.a := by
      intro i j hij
      rcases nineElevenTwo_relIndex_dichotomy caseA hij hdeg with h | h
      · exact absurd h (hex i j hij)
      · exact h
    -- pairwise equality of the single-factor centralizers
    have heq : ∀ i j : Fin data.q, i ≠ j → cuSubOf caseA i = cuSubOf caseA j := by
      intro i j hij
      have hi : cuSubOf caseA i ⊓ cuSubOf caseA j = cuSubOf caseA i := by
        by_contra hne
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_left : cuSubOf caseA i ⊓ cuSubOf caseA j ≤ cuSubOf caseA i)
          (cuSubOf_le_U caseA i) (fun h => hne h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA i, hall i j hij] at hlt
        exact lt_irrefl _ hlt
      have hj : cuSubOf caseA i ⊓ cuSubOf caseA j = cuSubOf caseA j := by
        by_contra hne
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_right : cuSubOf caseA i ⊓ cuSubOf caseA j ≤ cuSubOf caseA j)
          (cuSubOf_le_U caseA j) (fun h => hne h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA j, hall i j hij] at hlt
        exact lt_irrefl _ hlt
      rw [← hi, hj]
    have hq0 : 0 < data.q := lt_trans one_pos hq1
    -- `C` equals the common single-factor centralizer
    have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ := by
      apply le_antisymm (cSub_le_cuSubOf caseA ⟨0, hq0⟩)
      intro g hg
      have hgall : ∀ k, g ∈ cuSubOf caseA k := by
        intro k
        by_cases hk : k = ⟨0, hq0⟩
        · rwa [hk]
        · rw [← heq ⟨0, hq0⟩ k (fun h => hk h.symm)]; exact hg
      exact mem_cSub_of_forall_mem_cuSubOf caseA hgall
    refine ⟨cuSubOf caseA ⟨0, hq0⟩, cuSubOf caseA ⟨0, hq0⟩,
      relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, ?_⟩
    simp only [Section11CharacterData.C]
    rw [inf_idem]
    exact hCeq

end NineElevenTwoInertiaIdentity

end OddOrder.Peterfalvi.S11


