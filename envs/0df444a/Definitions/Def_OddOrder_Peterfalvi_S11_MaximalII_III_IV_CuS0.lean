-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:47:45.622506+00:00
-- url     : https://prove2.me/theorems/ffccec7f-5200-4a34-9f1c-2e7697653cb5
-- title:
--   Peterfalvi (9.8.d): $C_U(S_0)$, pair characters and case (a) data (continuation)
-- statement:
--   A continuation of the $C_U(S_0)$ development for maximal subgroups of types II, III and IV. It builds the pair homomorphism and pair character for Peterfalvi (9.8.d) and packages the case (a) data of Peterfalvi (9.7).
--
--   Main declarations: `hcuThetaHom_inclusion_hInHu` (`hcuThetaHom` restricts to `θ₀` on `H`); `hcuPairHom` (The (9.8.d) pair hom `θ₁·λ : H·C_U(S₀) → ℂˣ`); `hcuPsiPair` (The `H·C_U(S₀)`-linear pair character `ψ_{θ₁,λ}`); `clifford_caseA_data` (Peterfalvi (9.7) case (a) carrier).
--
--   The bundle also proves 23 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/CuS0.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/CuS0.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InertiaLift
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0Basic

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- **`hcuThetaHom` restricts to `θ₀` on `H`**: on the inclusion of `h ∈ H` into `H·C_U(S₀)`, the
extension returns the seed value `hcuSeedHom θ h`.  Via `SemidirectProduct.lift_inl` after
`(mulEquivSubgroup).symm (inclusion h) = inl h` (the complement iso sends the normal factor to
`inl`).
This is the single-factor analog of `hcHom_inclusion`, feeding the restriction-inertia argument. -/
theorem hcuThetaHom_inclusion_hInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (h : ↥(hInHu data)) :
    hcuThetaHom caseA θ hinv (Subgroup.inclusion
        (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = hcuSeedHom (chief := chief) θ h := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  -- `(mulEquivSubgroup).symm (inclusion h) = inl ⟨incl h, h ∈ H⟩`.
  have hsymm : (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHu_in_hcuInHu caseA)).symm
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = SemidirectProduct.inl
        (⟨Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h,
          Subgroup.mem_subgroupOf.mpr h.2⟩ :
          ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [SemidirectProduct.mulEquivSubgroup, MulEquiv.ofBijective_apply,
      SemidirectProduct.monoidHomSubgroup_apply, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, OneMemClass.coe_one, mul_one]
  simp only [hcuThetaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    SemidirectProduct.lift_inl]
  congr 1

/-- **The (9.8.d) pair hom `θ₁·λ : H·C_U(S₀) →* ℂˣ`**: the product of the `θ₀`-extension
`hcuThetaHom` (the single-factor analog of the `θ`-inflation, restricting to `θ₀` on `H`) and the
`λ`-lift `hcuLambdaHom λ` (trivial on `H`). On `H` it agrees with `hcuThetaHom` (= `θ₀`) alone; on
`C_U(S₀)` it
is `λ` (the extension is trivial there by construction).  Mirror of `hcPairHom`, single-factor. -/
noncomputable def hcuPairHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    ↥(hInHu data ⊔ cuInHu caseA) →* ℂˣ :=
  hcuThetaHom caseA θ hinv * hcuLambdaHom caseA lam

/-- **The `H·C_U(S₀)`-linear pair character `ψ_{θ₁,λ}`** of the (9.8.d) construction: the linear
(degree-one) irreducible character with hom `hcuPairHom`.  Mirror of `hcPsiPair`, single-factor. -/
noncomputable def hcuPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    IrreducibleCharacter ↥(hInHu data ⊔ cuInHu caseA) :=
  linearIrreducibleCharacter (hcuPairHom caseA θ hinv lam)

/-- **`ψ_{θ₁,λ}|_hInHu = θ₀`** (pointwise): on the inclusion of `h ∈ H` the pair character equals
the seed's inflation `θ₀`. The `λ`-factor dies (`hcuLambdaHom_eq_one_of_mem_hInHu`) and the
`θ`-factor is
the extension's restriction (`hcuThetaHom_inclusion_hInHu`), which by
`compHom_linearIrreducibleCharacter` is exactly the ClassFunction seed `θ₀`.  Same right-hand side
as the seed of `inertia_eq_hcuInHu`, so the restriction-inertia argument applies to the pair
verbatim.
-/
theorem hcuPsiPair_apply_inclusion [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) (h : ↥(hInHu data)) :
    (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        h := by
  have hlam1 : hcuLambdaHom caseA lam
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h) = 1 :=
    hcuLambdaHom_eq_one_of_mem_hInHu caseA lam (Subgroup.mem_subgroupOf.mpr h.2)
  simp only [hcuPsiPair, hcuPairHom, linearIrreducibleCharacter_apply, MonoidHom.mul_apply,
    hcuThetaHom_inclusion_hInHu, hlam1, mul_one, hcuSeedHom,
    MonoidHom.comp_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply]

/-- **Restriction-inertia `inertia(ψ_{θ₁,λ}) ≤ inertia(θ₀)`** (Peterfalvi (9.8.d)): an element
fixing the pair character also fixes its `H`-restriction `θ₀` (`hcuPsiPair_apply_inclusion`).
Single-factor mirror of `hcPsiPair_inertia_le` — the `λ`-factor is invisible on the restriction. -/
theorem hcuPsiPair_inertia_le [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [(hInHu data ⊔ cuInHu caseA).Normal] :
    ClassFunction.inertia (hcuPsiPair caseA θ hinv lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      ≤ ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  have := hInHu_normal data
  intro g hg
  rw [ClassFunction.mem_inertia] at hg ⊢
  ext h
  have key : (ClassFunction.conjBy g (hcuPsiPair caseA θ hinv lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ))
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
      = (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h) := by
    rw [hg]
  rw [ClassFunction.conjBy_apply] at key ⊢
  rw [← hcuPsiPair_apply_inclusion caseA θ hinv lam,
    ← hcuPsiPair_apply_inclusion caseA θ hinv lam, ← key]
  congr 1

/-- **`inertia(ψ_{θ₁,λ}) = H·C_U(S₀)`** (Peterfalvi (9.8.d)): with the seed inertia
`inertia(θ₀) = H·C_U(S₀)` (`inertia_eq_hcuInHu` for `θ` nontrivial on `S₀`, trivial on the
complement),
the pair character's `HU`-inertia is exactly `H·C_U(S₀)`.  Single-factor mirror of
`hcPsiPair_inertia_eq_hc`.  Feeds `isIrreducibleCharacter_induce_of_inertia_eq` for the degree-`a`
irreducible. -/
theorem hcuPsiPair_inertia_eq_hcu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    ClassFunction.inertia (hcuPsiPair caseA θ hinv lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      = hInHu data ⊔ cuInHu caseA := by
  apply le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  refine le_trans (hcuPsiPair_inertia_le caseA θ hinv lam) ?_
  rw [hθ₀]

/-- **`ζ_{θ₁,λ} = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})` is irreducible** (Peterfalvi (9.8.d), degree `a`):
direct from `isIrreducibleCharacter_induce_of_inertia_eq` and `inertia(ψ_{θ₁,λ}) = H·C_U(S₀)`
(`hcuPsiPair_inertia_eq_hcu`).  The (9.8.d) irreducible source character over the extension `θ₀`.
Its degree is `[HU : H·C_U(S₀)] · 1 = a` (`hcuZetaPair_apply_one`). -/
theorem hcuZetaPair_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    IsIrreducibleCharacter (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  exact OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq
    (hcuPsiPair caseA θ hinv lam)
    (hcuPsiPair_inertia_eq_hcu caseA θ hinv lam hθ₀)

/-- **`ζ_{θ₁,λ}(1) = a`** (Peterfalvi (9.8.d), source degree): the induced source character has
degree `[HU : H·C_U(S₀)] · ψ(1) = a · 1 = a`, since `ψ_{θ₁,λ}` is linear
(`ClassFunction.induce_apply_one` +
`index_hcuInHu_eq_caseA_a`).  The `M`-induction then has degree `q·a`
(`hcuZetaPair_induceHU_apply_one`). -/
theorem hcuZetaPair_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (1 : ↥(huSub data))
      = (caseA.a : ℂ) := by
  rw [ClassFunction.induce_apply_one, index_hcuInHu_eq_caseA_a,
    show (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (1 : ↥(hInHu data ⊔ cuInHu caseA)) = 1 from by
      simp [hcuPsiPair], mul_one]

/-- **`Ind_{HU}^M ζ_{θ₁,λ}(1) = q·a`** (Peterfalvi (9.8.d), full degree): `[M:HU]·ζ(1) = q·a`, from
`induceHU_apply_one_eq_q_mul` and the source degree `a` (`hcuZetaPair_apply_one`).  This is the
degree-`qa` claimed by (9.8.d) for the members of `𝒮(H₀U')`. -/
theorem hcuZetaPair_induceHU_apply_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
        (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) (1 : ↥M)
      = ((data.q * caseA.a : ℕ) : ℂ) := by
  rw [induceHU_apply_one_eq_q_mul, hcuZetaPair_apply_one, Nat.cast_mul]

/-- **`hcuSeedHom`-invariance from the `C_U(S₀)`-inertia of `θ₀`** (Peterfalvi (9.8.d)): the
`ClassFunction`-level invariance `conjBy c θ₀ = θ₀` (available as
`cuInHu_le_inertia_of_complement_triv`)
descends to the hom-level invariance `hinv` required by `hcuThetaHom`, because `θ₀` is the
`linearClassFunction` of `hcuSeedHom θ` (via `compHom_linearIrreducibleCharacter`) and the coercion
`ℂˣ → ℂ` is injective.  This bridges the substrate to the extension construction. -/
theorem hcuSeedHom_invariance_of_cuInHu_le_inertia [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hle : cuInHu caseA ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))) :
    ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h := by
  have := hInHu_normal data
  intro c h
  -- `θ₀ = linearClassFunction (hcuSeedHom θ)` and `conjBy (c:huSub) θ₀ = θ₀`.
  have hconj : ClassFunction.conjBy (c : ↥(huSub data))
      (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :=
    ClassFunction.mem_inertia.mp (hle c.2)
  -- evaluate both sides at `h`; the seed-ClassFunction is `hcuSeedHom θ`.
  have hval := congrFun (congrArg (fun f : ClassFunction ↥(hInHu data) ℂ => (f : ↥(hInHu data) → ℂ))
    hconj) h
  simp only [ClassFunction.conjBy_apply,
    ClassFunction.compHom_linearIrreducibleCharacter, linearIrreducibleCharacter_apply] at hval
  -- `hval : (θ (mk' N (hInHuEquivH ⟨c·h·c⁻¹⟩)) : ℂ) = (θ (mk' N (hInHuEquivH h)) : ℂ)`.
  refine Units.val_injective ?_
  simpa only [hcuSeedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hval

/-- **Inertia lift `I_{HU}(θ₀) = HC`, parametrized over the hard direction** `I(θ₀) ⊓ U ≤ C`.  The
case-agnostic assembly: `⊇` from `H ≤ I(θ₀)` (`subgroup_le_inertia`) and `cInHu_le_inertia` (both
case-independent), `⊆` by the modular decomposition `g = h·u` (`H ⊔ U = ⊤`, `H ◁ HU`) with the
`U`-part `u ∈ I(θ₀) ⊓ U ≤ C` supplied by `hinf`.  Both Clifford cases instantiate `hinf`: case (b)
via `inertia_inf_uInHu_le_cInHu` (`U`-irreducible), case (a) via the non-Galois `Hpart` analysis. -/
theorem inertia_eq_hcInHu_of_inf_le [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hinf : ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cInHu data chief) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  apply le_antisymm
  · intro g hg
    have hgtop : g ∈ hInHu data ⊔ uInHu data := hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hgtop
    obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
    have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      ClassFunction.subgroup_le_inertia θ₀ hh
    have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
      have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
        mul_mem (inv_mem hh_in) hg
      rwa [inv_mul_cancel_left] at hmem
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (hinf ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, cInHu_le_inertia data chief⟩

/-- **Peterfalvi (9.9.a), the inertia lift: `I_{HU}(θ₀) = HC`.**  The inertia in `HU` of the
realized chief-factor character `θ₀` is exactly the inertia subgroup `HC = hInHu ⊔ cInHu`.  `⊇` from
`H ≤ I(θ₀)` (automatic) and `cInHu_le_inertia`; `⊆` by decomposing `g ∈ I(θ₀)` as `h·u`
(`H ⊔ U = ⊤`, `H ◁ HU`), where `u = h⁻¹ g ∈ I(θ₀) ⊓ U ≤ C` (`inertia_inf_uInHu_le_cInHu`).  With
`HC ◁ HU` (`hcInHu_normal`) this makes `Ind_{HC}^{HU}` of an `HC`-character over `θ₀` irreducible.
-/
theorem inertia_eq_hcInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hθbar : (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) ≠ trivialClassFunction _) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_of_inf_le data chief (inertia_inf_uInHu_le_cInHu data chief hcaseB hθbar)

/-- **Inertia lift `I_{HU}(θ₀) = HC`, generic over the factor family.**  As
`inertia_eq_hcInHu_caseA` but taking the order-`p`, `U`-invariant, spanning family `Hpart` directly
(via `chiefFactor_caseA_char_inertia_gen`), so the `W1`-conjugates `{S₀^w}` — not the producer's
`caseA.Hpart` — drive the inertia lift for the free-`W1`-orbit character of (9.8.c). -/
theorem inertia_eq_hcInHu_gen [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data)
    {ι : Type*} (Hpart : ι → Subgroup (↥data.H ⧸ chief.N))
    (hp_order : ∀ i, Nat.card ↥(Hpart i) = chief.p)
    (hspan : ⨆ i, Hpart i = ⊤)
    (haInv : ∀ i, IsAInvariant (uActionHom data chief) (Hpart i))
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ Hpart i,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_of_inf_le data chief
    (inertia_inf_uInHu_le_cInHu_of_realized data chief
      (fun a g hag hfix =>
        caseB_inertia_realized_of_charInertia
          (fun g' hfix' =>
            caseB_char_inertia_inflation_of_core
              (fun g'' hinv =>
                chiefFactor_caseA_char_inertia_gen Hpart hp_order hspan haInv hreg g'' hinv)
              g' hfix')
          a g hag hfix))

/-- **Inertia lift `I_{HU}(θ₀) = HC` in Clifford case (a)** — the non-Galois analog of
`inertia_eq_hcInHu`.  For a **regular** chief-factor character `θ̄` (nontrivial on each order-`p`
Clifford summand `Hpart i`), the inertia of its inflation `θ₀` in `HU` is `HC`.  Feeds the proven
case-(a) core `chiefFactor_caseA_char_inertia` through the same case-agnostic plumbing
(`caseB_char_inertia_inflation_of_core` → `caseB_inertia_realized_of_charInertia` →
`inertia_inf_uInHu_le_cInHu_of_realized` → `inertia_eq_hcInHu_of_inf_le`) that case (b) uses with
`chiefFactor_caseB_char_inertia`.  This is the (9.8.b)/(9.8.c) degree input for the reducible
(= regular) characters. -/
theorem inertia_eq_hcInHu_caseA [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∀ i, ∃ x ∈ caseA.Hpart i,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief :=
  inertia_eq_hcInHu_gen data chief caseA.Hpart caseA.Hpart_order caseA.Hpart_iSup
    caseA.Hpart_aInvariant hreg

/-- **Peterfalvi (9.7) case (b) carrier.**  When `U` acts irreducibly on the chief factor
`H̄ = H/H₀` (Clifford case (b), the left branch of `chiefFactor_clifford_U_dichotomy`), the
field-model divisibilities of `CliffordCaseBData` hold: with `chars.u = |Ū|` (pinned in
`Section11CharacterData.u_eq_card_quotient`), `Coprime |Ū| (p-1)` and `|Ū| ∣ (p^q-1)/(p-1)` are the
unconditional `chiefFactor_caseB_image_coprime` / `chiefFactor_caseB_image_dvd_norm`.

⚠ A `theorem`, not a `def`: since the vestigial free `field_model : Prop` field was removed
(2026-07-27) every field of `CliffordCaseBData` is propositional, so the structure itself lives
in `Prop` — which is the honest reading, the case-(b) *data* (the `GF(p^q)` model) being
`S11_GaloisFieldModel.caseB_exists_galoisField_repr_withAut`. -/
theorem clifford_caseB_data [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (hcaseB : ∀ J : Subgroup (↥data.H ⧸ chief.N),
        IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype) J → J = ⊥ ∨ J = ⊤) :
    CliffordCaseBData chars where
  Ubar_cyclic := (chiefFactor_caseB_image_cyclic chief hcaseB).1
  u_coprime_p_sub_one := by
    rw [chars.u_eq_card_quotient]; exact chiefFactor_caseB_image_coprime chief hcaseB
  u_dvd_norm_quotient := by
    rw [chars.u_eq_card_quotient]; exact chiefFactor_caseB_image_dvd_norm chief hcaseB
  actsIrreducibly := hcaseB

/-- **Peterfalvi (9.7) case (a) carrier.**  When `H̄` contains a `U`-invariant order-`p` factor `S₀`
(Clifford case (a), the right branch of `chiefFactor_clifford_U_dichotomy`), the chief factor splits
as the internal direct product of `q = |W₁|` order-`p` factors — the `U W₁`-orbit of `S₀`, packaged
as a `Fin q`-family via the `SupIndep` partition of `exists_supIndep_aInvariant_family_of_iSup` —
and
the `U`-action on `S₀` has image of order `a ∣ p - 1` (`aInvariantRestrictAut_range_card_dvd`). -/
noncomputable def clifford_caseA_data [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    {S₀ : Subgroup (↥data.H ⧸ chief.N)} (hS₀ne : S₀ ≠ ⊥)
    (hS₀inv : IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) S₀)
    (hS₀card : Nat.card ↥S₀ = chief.p)
    (hirr₀ : ∀ J, IsAInvariant ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) J → J ≤ S₀ → J = ⊥ ∨ J = S₀) :
    CliffordCaseAData chars := by
  classical
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  haveI : chief.N.Normal := chief.N_normal
  set act := typeP_quotientCoprimeAction data.typeP hU chief.N_aInvariant with hact
  set φU := act.φ.comp act.U.subtype with hφU
  have hUnorm : act.U.Normal := (typeP_uW1_frobenius data.typeP hU).isNormal
  -- The `U W₁`-orbit of `S₀` spans `H̄` (irreducibility), giving a `SupIndep` family of order-`p`
  -- factors whose count `k` satisfies `|H̄| = |S₀|^k`.
  have hspan : ⨆ a, act.φ a • S₀ = ⊤ :=
    iSup_smul_eq_top_of_irreducible (φ := act.φ) chief.quotient_chiefFactor hS₀ne
  -- (`Exists` cannot be destructured into the `Type`-valued `CliffordCaseAData`; use `choose`.)
  have hexist := exists_supIndep_aInvariant_family_of_iSup
    (φ := φU) (S := fun a => act.φ a • S₀) (n := Nat.card ↥S₀)
    (fun x y => chief.quotient_elementaryAbelian.comm x y) hspan
    (fun a => isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv a)
    (fun a J hJinv hJle => forall_aInvariant_le_pointwise_smul hUnorm hirr₀ a J hJinv hJle)
    (fun a _ => card_pointwise_smul act.φ a S₀)
  let t : Finset ↥(data.typeP.U ⊔ data.typeP.W1) := hexist.choose
  have ht_card : Nat.card (↥data.H ⧸ chief.N) = Nat.card ↥S₀ ^ t.card := hexist.choose_spec.2.2.2
  -- `|H̄| = p^t.card` and `|H̄| = p^q`, so `t.card = q`.
  rw [hS₀card, chiefFactor_quotient_card chief] at ht_card
  have ht_card_q : t.card = data.q :=
    (Nat.pow_right_injective chief.p_prime.two_le ht_card).symm
  -- Reindex the `q`-element orbit family by `Fin q`.
  let e : ↥t ≃ Fin data.q := t.equivFin.trans (finCongr ht_card_q)
  refine
    { Hpart := fun j => act.φ ↑(e.symm j) • S₀
      Hpart_order := fun j => (card_pointwise_smul act.φ _ S₀).trans hS₀card
      Hpart_iSup := by
        rw [← hexist.choose_spec.2.2.1]
        refine le_antisymm (iSup_le fun j => le_iSup₂_of_le _ (e.symm j).2 le_rfl) ?_
        exact iSup₂_le fun i hi =>
          le_iSup_of_le (e ⟨i, hi⟩) (le_of_eq (by rw [Equiv.symm_apply_apply]))
      Hpart_aInvariant := fun j =>
        isAInvariant_comp_subtype_pointwise_smul hUnorm hS₀inv ↑(e.symm j)
      Hpart_iSupIndep := hexist.choose_spec.1.independent.comp e.symm.injective
      S0 := S₀
      S0_aInvariant := hS₀inv
      orbitRep := fun j => ↑(e.symm j)
      Hpart_orbit := fun j => rfl
      a := Nat.card ↥(aInvariantRestrictAut hS₀inv).range
      a_pos := Nat.card_pos
      a_dvd_p_sub_one := ?_
      a_eq_card_restrictAut_range := rfl }
  -- `a = |U-image on S₀| ∣ |S₀| - 1 = p - 1` (the order-`p` factor is cyclic, `Aut ≅ (ZMod p)ˣ`).
  have hdvd := aInvariantRestrictAut_range_card_dvd hS₀inv (hS₀card ▸ chief.p_prime)
  rwa [hS₀card] at hdvd

/-- **`|S₀| = p`**: the orbit generator `S₀` (`CliffordCaseAData.S0`) has order `p`.  Each summand
`Hpart j = φ(orbitRep j) • S₀` (`Hpart_orbit`) is an automorphic image of `S₀` under the
chief-factor
action `φ = quotientMulAutHom`, hence has the same order (`card_pointwise_smul`), which is `p`
(`Hpart_order`).  A foundational input for the (9.8.c) constant-factor-data construction (`S₀ ≅ ℤ/p`
has exactly `p` characters, `p-1` of them nontrivial). -/
theorem caseA_S0_card [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Nat.card ↥caseA.S0 = chief.p := by
  have h := caseA.Hpart_order ⟨0, data.nontrivial.2.1.pos⟩
  rwa [caseA.Hpart_orbit ⟨0, data.nontrivial.2.1.pos⟩, card_pointwise_smul] at h

/-- The `W₁`-orbit family of `S₀` (indexed by `W₁` realized inside `U ⊔ W₁`), `w ↦ S₀^w`. -/
noncomputable def caseA_wOrbit [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) → Subgroup (↥data.H ⧸ chief.N) :=
  fun w => quotientMulAutHom chief.N_aInvariant ↑w • caseA.S0

/-- `caseA_wOrbit caseA 1 = S₀` (identity element gives the generator). -/
theorem caseA_wOrbit_one [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    caseA_wOrbit caseA 1 = caseA.S0 := by
  rw [caseA_wOrbit]
  have : chief.N.Normal := chief.N_normal
  change quotientMulAutHom chief.N_aInvariant
      ↑(1 : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))) • caseA.S0 = caseA.S0
  rw [Subgroup.coe_one, map_one, one_smul]

/-- **The `W₁`-orbit of `S₀` spans `H̄`** (Peterfalvi (9.7.a)): the `U W₁`-orbit of `S₀` (spanning
by `U W₁`-irreducibility `chief.quotient_chiefFactor`) collapses to the `W₁`-orbit
(`iSup_phi_smul_eq_iSup_W_of_normal`, `U`-invariance), which therefore spans. -/
theorem caseA_wOrbit_iSup [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ⨆ w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
      caseA_wOrbit caseA w = ⊤ := by
  have : chief.N.Normal := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hS0card : Nat.card ↥caseA.S0 = chief.p := caseA_S0_card caseA
  have hS0ne : caseA.S0 ≠ ⊥ := by
    intro h0; rw [h0, Subgroup.card_bot] at hS0card
    exact chief.p_prime.one_lt.ne' hS0card.symm
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hS0inv : IsAInvariant
      ((quotientMulAutHom chief.N_aInvariant).comp
        (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype) caseA.S0 :=
    caseA.S0_aInvariant
  have hsup : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊔ (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hspan_amb : ⨆ a : ↥(data.typeP.U ⊔ data.typeP.W1),
      quotientMulAutHom chief.N_aInvariant a • caseA.S0 = ⊤ :=
    iSup_smul_eq_top_of_irreducible chief.quotient_chiefFactor hS0ne
  have hcollapse := iSup_phi_smul_eq_iSup_W_of_normal (φ := quotientMulAutHom chief.N_aInvariant)
    (U := data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
    (W := data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) hUnorm hS0inv
  have hL : ⨆ a : ↥((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
        ⊔ (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
      quotientMulAutHom chief.N_aInvariant ↑a • caseA.S0 = ⊤ := by
    have hcongr : ⨆ a : ↥((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
          ⊔ (data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))),
        quotientMulAutHom chief.N_aInvariant ↑a • caseA.S0
        = ⨆ a : ↥(data.typeP.U ⊔ data.typeP.W1),
          quotientMulAutHom chief.N_aInvariant a • caseA.S0 :=
      Equiv.iSup_congr (((MulEquiv.subgroupCongr hsup).trans Subgroup.topEquiv).toEquiv)
        (fun a => rfl)
    rw [hcongr, hspan_amb]
  rw [hcollapse] at hL
  exact hL

/-- **Peterfalvi (9.7.a): the `W₁`-orbit of `S₀` is `iSupIndep`** (free internal direct product).
The `q` conjugates `S₀^w` (`w ∈ W₁`), each of order `p`, span `H̄` (`caseA_wOrbit_iSup`) and satisfy
`∏ |S₀^w| = p^q = |H̄|`; so `Subgroup.noncommPiCoprod` is bijective
(`noncommPiCoprod_bijective_of_card`), giving independence
(`iSupIndep_of_noncommPiCoprod_injective_comm`).  This is the free `W₁`-indexing
`{Hᵢ} = {S₀^w | w ∈ W₁}` of Peterfalvi (9.7.a). -/
theorem caseA_wOrbit_iSupIndep [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Finite ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1))] :
    iSupIndep (caseA_wOrbit caseA) := by
  have : Fintype ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    Fintype.ofFinite _
  classical
  have : chief.N.Normal := chief.N_normal
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  let : CommGroup (↥data.H ⧸ chief.N) :=
    { (inferInstance : Group (↥data.H ⧸ chief.N)) with
      mul_comm := chief.quotient_elementaryAbelian.comm }
  have hS0card : Nat.card ↥caseA.S0 = chief.p := caseA_S0_card caseA
  have hspanW := caseA_wOrbit_iSup caseA
  have hcardW1 : Fintype.card ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      = data.q := by
    rw [TypesIIIIIIVSetup.q, ← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : data.typeP.W1 ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv
  have hprodcard : ∏ w : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
      Nat.card ↥(caseA_wOrbit caseA w) = Nat.card (↥data.H ⧸ chief.N) := by
    have hval : ∀ w, Nat.card ↥(caseA_wOrbit caseA w) = chief.p := fun w => by
      rw [caseA_wOrbit, card_pointwise_smul, hS0card]
    simp only [hval]
    rw [Finset.prod_const, Finset.card_univ, hcardW1, chiefFactor_quotient_card chief]
  have hcomm : Pairwise fun i j : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) =>
      ∀ x y : (↥data.H ⧸ chief.N), x ∈ caseA_wOrbit caseA i → y ∈ caseA_wOrbit caseA j →
        Commute x y :=
    fun i j _ x y _ _ => chief.quotient_elementaryAbelian.comm x y
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm) :=
    noncommPiCoprod_bijective_of_card hcomm hspanW hprodcard
  exact iSupIndep_of_noncommPiCoprod_injective_comm hcomm hbij.injective

/-- **Peterfalvi (9.7.a) summand-complement `W = ⨆_{w∈W₁#} S₀^w`** (`H₂…H_q` of Peterfalvi): the
join of the nontrivial `W₁`-conjugates of `S₀`.  Complements `S₀` in `H̄`
(`caseA_S0_sup_wComplement`, `caseA_S0_inf_wComplement`) and contains every `S₀^w` with `w ≠ 1`
(used for `horbit`). -/
noncomputable def caseA_wComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Subgroup (↥data.H ⧸ chief.N) :=
  ⨆ (w) (_ : w ≠ 1), caseA_wOrbit caseA w

/-- The summand-complement `W` is `U`-invariant (a join of `U`-invariant conjugates). -/
theorem caseA_wComplement_aInvariant [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    IsAInvariant (uActionHom data chief) (caseA_wComplement caseA) := by
  have : chief.N.Normal := chief.N_normal
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  refine OddOrder.Isaacs.Ch03.IsAInvariant.iSup
    (fun w => OddOrder.Isaacs.Ch03.IsAInvariant.iSup (fun _ => ?_))
  rw [caseA_wOrbit]
  exact isAInvariant_comp_subtype_pointwise_smul hUnorm caseA.S0_aInvariant ↑w

/-- **`S₀ ⊔ W = ⊤`** (Peterfalvi (9.7.a) spanning): `S₀ = S₀^1` together with the `w ≠ 1`
conjugates gives the full `W₁`-orbit, which spans `H̄` (`caseA_wOrbit_iSup`). -/
theorem caseA_S0_sup_wComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    caseA.S0 ⊔ caseA_wComplement caseA = ⊤ := by
  have hspanW := caseA_wOrbit_iSup caseA
  rw [← caseA_wOrbit_one caseA, caseA_wComplement, ← hspanW]
  refine le_antisymm
    (sup_le (le_iSup (caseA_wOrbit caseA) 1)
      (iSup₂_le fun w _ => le_iSup (caseA_wOrbit caseA) w)) ?_
  refine iSup_le fun w => ?_
  by_cases hw : w = 1
  · rw [hw]; exact le_sup_left
  · exact le_sup_of_le_right (le_iSup₂ (f := fun w (_ : w ≠ 1) => caseA_wOrbit caseA w) w hw)

/-- **`S₀ ⊓ W = ⊥`** (Peterfalvi (9.7.a) freeness): from the independence of the `W₁`-orbit
(`caseA_wOrbit_iSupIndep`), the generator `S₀ = S₀^1` is disjoint from the join of the other
conjugates `W = ⨆_{w≠1} S₀^w`.  Together with `caseA_S0_sup_wComplement` this exhibits
`H̄ = S₀ ⊕ W`, `[H̄ : W] = p`. -/
theorem caseA_S0_inf_wComplement [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Finite ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1))] :
    caseA.S0 ⊓ caseA_wComplement caseA = ⊥ := by
  have hdisj : Disjoint (caseA_wOrbit caseA 1) (⨆ (w) (_ : w ≠ 1), caseA_wOrbit caseA w) :=
    (iSupIndep_def.mp (caseA_wOrbit_iSupIndep caseA)) 1
  rw [caseA_wOrbit_one caseA] at hdisj
  exact disjoint_iff.mp hdisj

/-- **Reducible induction ⟹ full inertia** (prime-index Clifford dichotomy): if `Ind_{HU}^M χ` is
reducible for `χ ∈ Irr(HU)`, then `I_M(χ) = ⊤` (`χ` is `M`-invariant).  `HU ◁ M` with `[M:HU] = q`
prime (`huSub_index_eq_q`), so `HU ≤ I_M(χ) ≤ M` forces `I_M(χ) ∈ {HU, M}`
(`eq_of_le_of_prime_index`); reducibility excludes `I_M(χ) = HU` (contrapositive of
`isIrreducibleCharacter_induce_of_inertia_eq`).  The `M`-fixedness feeding the (9.8.c) `Xmu`
injectivity (`induce_injective_of_inertia_stable`) in the surjectivity route to `|Xmu| = p-1`. -/
theorem inertia_eq_top_of_induceHU_not_irreducible [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    (χ : IrreducibleCharacter ↥(huSub data))
    (hred : ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ))) :
    ClassFunction.inertia (χ : ClassFunction ↥(huSub data) ℂ) = ⊤ := by
  have := huSub_normal data
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hne : ClassFunction.inertia (χ : ClassFunction ↥(huSub data) ℂ) ≠ huSub data :=
    mt (isIrreducibleCharacter_induce_of_inertia_eq χ) hred
  have hle : huSub data ≤ ClassFunction.inertia (χ : ClassFunction ↥(huSub data) ℂ) :=
    ClassFunction.subgroup_le_inertia _
  have hprime : (huSub data).index.Prime := by rw [huSub_index_eq_q]; exact data.nontrivial.2.1
  by_contra hnt
  exact hne (eq_of_le_of_prime_index hle hprime hnt)

/-- **`Ind_{HU}^M` is injective on reducible-inducing characters** (`Xmu` injectivity): if
`Ind_{HU}^M χ` is reducible and `Ind_{HU}^M χ = Ind_{HU}^M ψ`, then `ψ = χ`.  Reducibility makes `χ`
`M`-invariant (`inertia_eq_top_of_induceHU_not_irreducible`), and a full-inertia character is
`Ind`-injective (`induce_injective_of_inertia_stable`, via `induce_eq_induce_iff_conj`).  Combined
with `reducible_count_sOf_H0C` (`|reducibles| = p-1`) this gives `|Xmu| = p-1` for the (9.8.c)
parity dichotomy (`Xmu = {ζ ∈ Xθ | Ind_M ζ reducible}`), the surjectivity route to conjunct (c). -/
theorem caseA_induceHU_inj_of_reducible [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {χ ψ : IrreducibleCharacter ↥(huSub data)}
    (hχred : ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)))
    (h : ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.induce (huSub data) (ψ : ClassFunction ↥(huSub data) ℂ)) :
    ψ = χ := by
  have := huSub_normal data
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hinertia := inertia_eq_top_of_induceHU_not_irreducible data χ hχred
  refine induce_injective_of_inertia_stable (fun g => ?_) h
  apply IrreducibleCharacter.ext
  rw [IrreducibleCharacter.coe_conjBy]
  exact ClassFunction.mem_inertia.mp (by rw [hinertia]; exact Subgroup.mem_top g)

/-- **`Ū`-invariance of nontriviality on any `U`-invariant subgroup**: for a `U`-invariant subgroup
`K ≤ H̄` (`IsAInvariant (uActionHom data chief) K`), a character `θ` is nontrivial on `K` iff its
`U`-translate `θ ∘ φ_U(a)` is. Since `φ_U(a)` restricts to a bijection of `K` (`hK`, invertible),
the
two restrictions have the same triviality.  Generalises `caseA_uActionHom_comp_subtype_eq_one_iff`
(the `Hpart i` case) to any `U`-invariant `K` — used on the `W₁`-conjugates `q(w) • S₀` (also
`U`-invariant, `U ◁ U W₁`) in the (9.8.c) surjectivity regularity argument. -/
theorem comp_uActionHom_comp_subtype_eq_one_iff_of_aInvariant [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {K : Subgroup (↥data.H ⧸ chief.N)} (hK : IsAInvariant (uActionHom data chief) K)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    (θ.comp (uActionHom data chief a).toMonoidHom).comp K.subtype = 1
      ↔ θ.comp K.subtype = 1 := by
  constructor
  · intro h
    refine MonoidHom.ext fun y => ?_
    have hval := DFunLike.congr_fun h ⟨_, hK.inv_smul_mem a y.2⟩
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom, MulAut.apply_inv_self] at hval ⊢
    exact hval
  · intro h
    refine MonoidHom.ext fun x => ?_
    have hval := DFunLike.congr_fun h ⟨_, hK.smul_mem a x.2⟩
    simpa only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply,
      MulEquiv.coe_toMonoidHom] using hval

/-- **Peterfalvi (9.7)**: the Clifford-theory dichotomy for the action on the chief factor `H/H_0`.

The case split is `chiefFactor_clifford_U_dichotomy`: `U` acts on `H̄ = H/H₀` either irreducibly
(case (b)) or with a `U`-invariant order-`p` factor (case (a)).  Each branch is packaged into its
carrier: `clifford_caseB_data` (the Singer field-model divisibilities `Coprime |Ū| (p-1)`,
`|Ū| ∣ (p^q-1)/(p-1)`, with `chars.u = |Ū|` pinned in `Section11CharacterData.u_eq_card_quotient`)
and `clifford_caseA_data` (the `q` order-`p` Clifford factors and the bound `a ∣ p-1`). -/
theorem clifford_dichotomy [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    Nonempty (CliffordCaseAData chars) ∨ Nonempty (CliffordCaseBData chars) := by
  rcases chiefFactor_clifford_U_dichotomy chief with hcaseB | ⟨S₀, hS₀ne, hS₀inv, hS₀card, hirr₀⟩
  · exact Or.inr ⟨clifford_caseB_data chars hcaseB⟩
  · exact Or.inl ⟨clifford_caseA_data chars hS₀ne hS₀inv hS₀card hirr₀⟩

end OddOrder.Peterfalvi.S11


