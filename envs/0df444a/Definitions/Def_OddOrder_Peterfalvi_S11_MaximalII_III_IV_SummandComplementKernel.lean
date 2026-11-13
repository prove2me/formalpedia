-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:12:21.396973+00:00
-- url     : https://prove2.me/theorems/36249ef3-0c82-4ebf-9ac5-fffb9dda83e4
-- title:
--   Peterfalvi (9.8.d): summand-complement kernel and $\theta$-counts (continuation)
-- statement:
--   A continuation file for the Clifford case (a) analysis. It proves lies-over transitivity results, the homomorphism and $\theta$-counts of Peterfalvi (9.8.d), and the assembly of the reducible $M$-fixed character as an induced character.
--
--   Main declarations: `liesOver_of_liesOver_liesOver_subgroupOf` (Lies-over transitivity, composing down); `hcuZetaPair_liesOver_hInHu` (`ζ_{θ₁,λ}` lies over the chief-factor inflation `θ₀` at `hInHu`); `card_hom_triv_W_eq_card_quotient` (Homs trivial on `W` biject with homs of the quotient `H̄/W`); `card_theta_triv_W_nontriv_S0` (θ-count).
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/SummandComplementKernel.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/SummandComplementKernel.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_InnerCompHom

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- **Inner product is preserved under `compHom` by a group isomorphism**.  Generalises
`inner_compHom_of_bijective` (an endomorphism) to a `MulEquiv A ≃* B`.  Used in the lies-over
transitivity of the (9.8.c) Clifford-correspondence step 5, where the intermediate subgroup
`H.subgroupOf K ≃* H` transports the restriction. -/
theorem inner_compHom_mulEquiv {A B : Type*} [Group A] [Group B] [Fintype A] [Fintype B]
    [Invertible (Nat.card A : ℂ)] [Invertible (Nat.card B : ℂ)] (e : A ≃* B)
    (a b : ClassFunction B ℂ) :
    ClassFunction.inner (ClassFunction.compHom e.toMonoidHom a)
        (ClassFunction.compHom e.toMonoidHom b) = ClassFunction.inner a b := by
  have hcard : (Nat.card A : ℂ) = Nat.card B := by rw [Nat.card_congr e.toEquiv]
  rw [ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.inner_eq_inv_card_mul_innerSum,
    innerSum_compHom_mulEquiv]
  congr 1
  rw [invOf_eq_inv, invOf_eq_inv, hcard]

/-- **Lies-over transitivity** (general Clifford): for `H ≤ K ≤ Γ`, if the irreducible `χ` of `Γ`
lies over `θ ∈ Irr H`, then there is an intermediate irreducible `ψ ∈ Irr K` such that `χ` lies over
`ψ` and `ψ` lies over `θ` (transported to `H.subgroupOf K` by `subgroupOfEquivOfLe`).  The
`Res_H χ = Res_{H.subgroupOf K}(Res_K χ)` transitivity (`restrict_restrict_subgroupOf`,
`inner_compHom_mulEquiv`) plus the `K`-irreducible decomposition `Res_K χ = Σ_ψ ⟨Res_K χ, ψ⟩ ψ`
(`sum_inner_irreducibleCharacter_smul`) split the nonzero multiplicity `⟨Res_H χ, θ⟩` as
`Σ_ψ ⟨Res_K χ, ψ⟩ · ⟨Res_{H.sK} ψ, θ'⟩`, so some `ψ` has both factors nonzero.  This is the (a)
input
to the (9.8.c) Clifford-correspondence step 5 (a reducible `ξ` over `θ₀ ∈ Irr H` factors through an
`HC`-constituent). -/
theorem exists_liesOver_intermediate {Γ : Type*} [Group Γ] [Finite Γ]
    {H K : Subgroup Γ} (hHK : H ≤ K)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(H.subgroupOf K)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf K) : ℂ)]
    (χ : IrreducibleCharacter Γ) (θ : IrreducibleCharacter ↥H)
    (hover : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver H χ θ) :
    ∃ ψ : IrreducibleCharacter ↥K,
      OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver K χ ψ ∧
      OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (H.subgroupOf K) ψ
        ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
            (θ : ClassFunction ↥H ℂ),
          θ.isIrreducible.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHK).surjective⟩ := by
  classical
  have : Fintype (IrreducibleCharacter ↥K) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hHK with hedef
  set θ' : IrreducibleCharacter ↥(H.subgroupOf K) :=
    ⟨ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ),
      θ.isIrreducible.compHom_of_surjective e.surjective⟩ with hθ'def
  -- Transport `⟨Res_H χ, θ⟩` to `⟨Res_{H.sK}(Res_K χ), θ'⟩`.
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def] at hover
  have htrans : ClassFunction.inner
      (ClassFunction.restrict (H.subgroupOf K) (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
      (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) ≠ 0 := by
    rw [restrict_restrict_subgroupOf hHK (χ : ClassFunction Γ ℂ),
      show (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
        = ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ) from rfl,
      inner_compHom_mulEquiv e (ClassFunction.restrict H (χ : ClassFunction Γ ℂ))
        (θ : ClassFunction ↥H ℂ)]
    exact hover
  -- Decompose `Res_K χ = Σ_ψ ⟨Res_K χ, ψ⟩ ψ` and split the inner product.
  have hkey : ClassFunction.inner
      (ClassFunction.restrict (H.subgroupOf K) (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
      (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
      = ∑ ψ : IrreducibleCharacter ↥K,
          ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
              (ψ : ClassFunction ↥K ℂ)
            * ClassFunction.inner
              (ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ))
              (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) := by
    conv_lhs => rw [← sum_inner_irreducibleCharacter_smul
      (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))]
    have hrs : ClassFunction.restrict (H.subgroupOf K)
          (∑ ψ : IrreducibleCharacter ↥K,
            ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                (ψ : ClassFunction ↥K ℂ) • (ψ : ClassFunction ↥K ℂ))
        = ∑ ψ : IrreducibleCharacter ↥K,
            ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                (ψ : ClassFunction ↥K ℂ)
              • ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ) := by
      ext x
      simp only [ClassFunction.restrict_apply, ClassFunction.finset_sum_apply,
        ClassFunction.smul_apply]
    rw [hrs, OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_congr rfl (fun ψ _ => ?_)
    rw [ClassFunction.inner_smul_left]
  rw [hkey] at htrans
  obtain ⟨ψ, -, hψ⟩ := Finset.exists_ne_zero_of_sum_ne_zero htrans
  refine ⟨ψ, ?_, ?_⟩
  · rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
      ClassFunction.restrictionMultiplicity_def]
    exact fun h => hψ (by rw [h, zero_mul])
  · rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
      ClassFunction.restrictionMultiplicity_def]
    exact fun h => hψ (by rw [h, mul_zero])

open scoped ComplexOrder in
/-- **Lies-over transitivity, composing *down*** (general Clifford): for `H ≤ K ≤ Γ`, if the
irreducible `χ` lies over `ψ ∈ Irr K` and `ψ` lies over the (transported) `θ' ∈ Irr(H.subgroupOf
K)`,
then `χ` lies over `θ ∈ Irr H`.  The converse direction of `exists_liesOver_intermediate`: expand
`⟨Res_H χ, θ⟩ = ⟨Res_{H.sK}(Res_K χ), θ'⟩` (transitivity `restrict_restrict_subgroupOf` +
`inner_compHom_mulEquiv`) and decompose `Res_K χ = Σ_ρ ⟨Res_K χ,ρ⟩ ρ`, giving
`Σ_ρ ⟨Res_K χ,ρ⟩·⟨Res_{H.sK}ρ,θ'⟩`.  Every term is a product of non-negative restriction
multiplicities (`restrictionMultiplicity_nonneg`), and the `ρ = ψ` term is *strictly* positive (both
factors nonzero), so the whole sum is `> 0`, hence `⟨Res_H χ, θ⟩ ≠ 0`.  This is the tool that
pushes a
lies-over relation at an intermediate subgroup down to `H` — used to see the (9.8.d) `Ind_{HU}^M
ζ`'s
source `ζ` as lying over the chief-factor inflation `θ₀` at `hInHu`. -/
theorem liesOver_of_liesOver_liesOver_subgroupOf {Γ : Type*} [Group Γ] [Finite Γ]
    [Invertible (Nat.card Γ : ℂ)] {H K : Subgroup Γ} (hHK : H ≤ K)
    [Fintype ↥H] [Fintype ↥K] [Fintype ↥(H.subgroupOf K)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    [Invertible (Nat.card ↥(H.subgroupOf K) : ℂ)]
    (χ : IrreducibleCharacter Γ) (ψ : IrreducibleCharacter ↥K) (θ : IrreducibleCharacter ↥H)
    (hχψ : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver K χ ψ)
    (hψθ : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (H.subgroupOf K) ψ
      ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom
          (θ : ClassFunction ↥H ℂ),
        θ.isIrreducible.compHom_of_surjective (Subgroup.subgroupOfEquivOfLe hHK).surjective⟩) :
    OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver H χ θ := by
  classical
  have : Fintype (IrreducibleCharacter ↥K) := Fintype.ofFinite _
  set e := Subgroup.subgroupOfEquivOfLe hHK with hedef
  set θ' : IrreducibleCharacter ↥(H.subgroupOf K) :=
    ⟨ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ),
      θ.isIrreducible.compHom_of_surjective e.surjective⟩ with hθ'def
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def]
  -- `⟨Res_H χ, θ⟩ = ⟨Res_{H.sK}(Res_K χ), θ'⟩`.
  rw [show ClassFunction.inner (ClassFunction.restrict H (χ : ClassFunction Γ ℂ))
        (θ : ClassFunction ↥H ℂ)
      = ClassFunction.inner (ClassFunction.restrict (H.subgroupOf K)
          (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) from ?_]
  · -- expand `Res_K χ = Σ_ρ ⟨Res_K χ, ρ⟩ ρ`.
    have hkey : ClassFunction.inner (ClassFunction.restrict (H.subgroupOf K)
          (ClassFunction.restrict K (χ : ClassFunction Γ ℂ)))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
        = ∑ ρ : IrreducibleCharacter ↥K,
            ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                (ρ : ClassFunction ↥K ℂ)
              * ClassFunction.inner
                (ClassFunction.restrict (H.subgroupOf K) (ρ : ClassFunction ↥K ℂ))
                (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) := by
      conv_lhs => rw [← sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))]
      have hrs : ClassFunction.restrict (H.subgroupOf K)
            (∑ ρ : IrreducibleCharacter ↥K,
              ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                  (ρ : ClassFunction ↥K ℂ) • (ρ : ClassFunction ↥K ℂ))
          = ∑ ρ : IrreducibleCharacter ↥K,
              ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
                  (ρ : ClassFunction ↥K ℂ)
                • ClassFunction.restrict (H.subgroupOf K) (ρ : ClassFunction ↥K ℂ) := by
        ext x
        simp only [ClassFunction.restrict_apply, ClassFunction.finset_sum_apply,
          ClassFunction.smul_apply]
      rw [hrs, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_congr rfl (fun ρ _ => ?_)
      rw [ClassFunction.inner_smul_left]
    rw [hkey]
    -- every term `≥ 0`; the `ψ`-term is `> 0`, so the sum is `> 0`, hence `≠ 0`.
    refine ne_of_gt (lt_of_lt_of_le ?_ (Finset.single_le_sum
      (f := fun ρ : IrreducibleCharacter ↥K =>
      ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
          (ρ : ClassFunction ↥K ℂ)
        * ClassFunction.inner
          (ClassFunction.restrict (H.subgroupOf K) (ρ : ClassFunction ↥K ℂ))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ))
      (fun ρ _ => ?_) (Finset.mem_univ ψ)))
    · -- `0 < ψ`-term.
      have h1 : (0 : ℂ) ≤ ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
          (ψ : ClassFunction ↥K ℂ) :=
        ClassFunction.restrictionMultiplicity_nonneg K χ.isIrreducible ψ.isIrreducible
      have h1ne : ClassFunction.inner (ClassFunction.restrict K (χ : ClassFunction Γ ℂ))
          (ψ : ClassFunction ↥K ℂ) ≠ 0 := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
          ClassFunction.restrictionMultiplicity_def] at hχψ; exact hχψ
      have h2 : (0 : ℂ) ≤ ClassFunction.inner
          (ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) :=
        ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf K) ψ.isIrreducible
          θ'.isIrreducible
      have h2ne : ClassFunction.inner
          (ClassFunction.restrict (H.subgroupOf K) (ψ : ClassFunction ↥K ℂ))
          (θ' : ClassFunction ↥(H.subgroupOf K) ℂ) ≠ 0 := by
        rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
          ClassFunction.restrictionMultiplicity_def] at hψθ; exact hψθ
      exact mul_pos (lt_of_le_of_ne h1 (Ne.symm h1ne)) (lt_of_le_of_ne h2 (Ne.symm h2ne))
    · -- every term `≥ 0`.
      exact mul_nonneg
        (ClassFunction.restrictionMultiplicity_nonneg K χ.isIrreducible ρ.isIrreducible)
        (ClassFunction.restrictionMultiplicity_nonneg (H.subgroupOf K) ρ.isIrreducible
          θ'.isIrreducible)
  · rw [restrict_restrict_subgroupOf hHK (χ : ClassFunction Γ ℂ),
      show (θ' : ClassFunction ↥(H.subgroupOf K) ℂ)
        = ClassFunction.compHom e.toMonoidHom (θ : ClassFunction ↥H ℂ) from rfl,
      inner_compHom_mulEquiv e (ClassFunction.restrict H (χ : ClassFunction Γ ℂ))
        (θ : ClassFunction ↥H ℂ)]

/-- **`ψ_{θ₁,λ}` restricts on `hInHu` to the seed inflation `θ₀`** (`subgroupOf` form, (9.8.d)).
Restricting the pair character `hcuPsiPair` to `hInHu.subgroupOf (H·C_U(S₀))` equals the inflation
`θ₀ = linearIrr(θ ∘ mk'_N ∘ hInHuEquivH)` transported along `subgroupOfEquivOfLe`.  Single-factor
mirror of `hcPsi_restrict_hInHu_subgroupOf`, from the pointwise `hcuPsiPair_apply_inclusion`.
Feeds the lies-over descent of `ζ_{θ₁,λ}` onto `θ₀` at `hInHu`. -/
theorem hcuPsiPair_restrict_hInHu_subgroupOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) :
    ClassFunction.restrict ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))
        (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
            hInHu data ≤ hInHu data ⊔ cuInHu caseA)).toMonoidHom
          (linearIrreducibleCharacter (θ.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ) := by
  ext x
  rw [ClassFunction.restrict_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
  set h := (Subgroup.subgroupOfEquivOfLe (le_sup_left :
    hInHu data ≤ hInHu data ⊔ cuInHu caseA)) x with hh
  have hxeq : (x : ↥(hInHu data ⊔ cuInHu caseA))
      = Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_inclusion, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [hxeq, hcuPsiPair_apply_inclusion caseA θ hinv lam h]
  simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

open OddOrder.RepresentationTheory in
/-- **`ζ_{θ₁,λ}` lies over the chief-factor inflation `θ₀` at `hInHu`** (Peterfalvi (9.8.d)).  The
source `ζ = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})` lies over `ψ_{θ₁,λ}` at `H·C_U(S₀)` (Frobenius
reciprocity, `inner_induce_ne_zero_iff_liesOver`), and `ψ_{θ₁,λ}` restricts on `hInHu` to `θ₀`
(`hcuPsiPair_restrict_hInHu_subgroupOf`, a single irreducible), so `lies-over` descends
(`liesOver_of_liesOver_liesOver_subgroupOf`) to give `ζ` over the inflation `θ₀` at `hInHu`.  The
`hlo` input that lets `caseA_reducible_theta_regular` force the seed `θ` to be regular when `ζ` is
`W₁`-fixed — the crux of the `hIM` discharge. -/
theorem hcuZetaPair_liesOver_hInHu [Finite G] {M : Subgroup G}
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
    [Fintype ↥(hInHu data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    IrreducibleCharacter.LiesOver (hInHu data)
      (⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
        hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ : IrreducibleCharacter ↥(huSub data))
      (linearIrreducibleCharacter ((θ.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom)))) := by
  classical
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  have : Fintype ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ with hζdef
  -- `ζ` lies over `ψ = hcuPsiPair` at `H·C_U(S₀)` (Frobenius reciprocity).
  have hlo0 : IrreducibleCharacter.LiesOver (hInHu data ⊔ cuInHu caseA) ζ
      (hcuPsiPair caseA θ hinv lam) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam) := by rw [hζdef]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  -- `ψ` restricts on `hInHu` to the inflation `θ₀` (single irreducible), so `ψ` lies over `θ₀`.
  set θ'irr : IrreducibleCharacter ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hInHu data ≤ hInHu data ⊔ cuInHu caseA)).toMonoidHom
        (linearIrreducibleCharacter ((θ.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom))) : ClassFunction ↥(hInHu data) ℂ),
      (linearIrreducibleCharacter _).isIrreducible.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe _).surjective⟩ with hθ'irr
  have hψθ : IrreducibleCharacter.LiesOver
      ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))
      (hcuPsiPair caseA θ hinv lam) θ'irr := by
    rw [IrreducibleCharacter.liesOver_iff, ClassFunction.restrictionMultiplicity_def]
    have hres : ClassFunction.restrict ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA))
        (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        = (θ'irr : ClassFunction ↥((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)) ℂ) :=
      hcuPsiPair_restrict_hInHu_subgroupOf caseA θ hinv lam
    rw [hres, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite θ'irr θ'irr,
      if_pos rfl]
    exact one_ne_zero
  exact liesOver_of_liesOver_liesOver_subgroupOf (le_sup_left :
    hInHu data ≤ hInHu data ⊔ cuInHu caseA) ζ (hcuPsiPair caseA θ hinv lam)
    (linearIrreducibleCharacter ((θ.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom)))) hlo0 hψθ

/-- **Conjugation-stable kernel-containment** (Peterfalvi (9.8.d) count substrate, intrinsic-family
`T`-invariance primitive).  For a class function `χ` on a normal subgroup `K ⊴ G` and a subset
`A ⊆ ↥K` that is *invariant* under conjugation-by-`g` (`conjByMulEquiv g` maps `A` into `A`), the
kernel-containment `A ⊆ Ker χ` transfers to the conjugate `χ^g`: `A ⊆ Ker (conjBy g χ)`.

Pointwise: `(conjBy g χ) y = χ (g·y·g⁻¹)` and `characterDegree (conjBy g χ) = characterDegree χ`
(conjugation fixes the value at `1`), so for `y ∈ A` the conjugate `g·y·g⁻¹ ∈ A ⊆ Ker χ` gives
`(conjBy g χ) y = χ (g·y·g⁻¹) = characterDegree χ = characterDegree (conjBy g χ)`, i.e.
`y ∈ Ker (conjBy g χ)`.

This is the linchpin of the *intrinsic* characterization of the (9.8.d) pair-family
`T = {ψ_{θ₁,λ}}` as `{χ ∈ Irr(H·C_U(S₀)) | linear ∧ H₀-realized ⊆ Ker χ ∧ W-lifted ⊆ Ker χ ∧
χ|_H ≠ 1 ∧ U'-realized ⊆ Ker χ}`: each realized kernel condition `N-realized ⊆ Ker χ` for an
`HU`-normal `N` (H₀-realized, W-lifted, U'-realized — all `◁ HU`) is `HU`-conjugation-stable,
because
the ambient normality makes `N-realized ∩ (H·C_U(S₀))` a `conjByMulEquiv g`-invariant set for every
`g ∈ HU`.  Hence `T` is conjugation-closed, the input `hT` of `card_image_induce_eq_div` for the
`|image| = |T|/a` orbit step — without a `hcuPsiPair`-conjBy-descent lemma. -/
theorem subsetCharacterKernel_conjBy_of_invariant {K : Subgroup G} [K.Normal]
    (g : G) (χ : ClassFunction ↥K ℂ) (A : Set ↥K)
    (hAinv : ∀ a ∈ A, ClassFunction.conjByMulEquiv g a ∈ A)
    (hker : A ⊆ OddOrder.Peterfalvi.S03.characterKernel χ) :
    A ⊆ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.conjBy g χ) := by
  intro y hy
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  have hy' : ClassFunction.conjByMulEquiv g y ∈ A := hAinv y hy
  have hdeg : OddOrder.Peterfalvi.S03.characterDegree (ClassFunction.conjBy g χ)
      = OddOrder.Peterfalvi.S03.characterDegree χ := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, OddOrder.Peterfalvi.S03.characterDegree_def]
    change (ClassFunction.conjBy g χ) 1 = χ 1
    rw [ClassFunction.conjBy_apply]
    refine congrArg χ (Subtype.ext ?_)
    simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel]
  change (ClassFunction.conjBy g χ) y
    = OddOrder.Peterfalvi.S03.characterDegree (ClassFunction.conjBy g χ)
  rw [ClassFunction.conjBy_apply, hdeg]
  have hmem := hker hy'
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
  rw [← hmem]
  congr 1

/-- **Pointwise kernel transport under conjugation** (`cfker_conjg`, Peterfalvi (9.8.d) (γ)
substrate).  For a class function `χ` on a normal subgroup `K ⊴ G` and `w : G`, an element
`n ∈ ↥K` lies in the kernel of the conjugate `χ^w` iff its `w`-conjugate `w·n·w⁻¹` (as an element
of `↥K`, `conjByMulEquiv w n`) lies in the kernel of `χ`:

`n ∈ Ker (χ^w) ↔ conjByMulEquiv w n ∈ Ker χ`.

Elementary: `(χ^w) n = χ (w·n·w⁻¹)` (`conjBy_apply`) and `characterDegree (χ^w) = characterDegree χ`
(conjugation fixes the value at `1`).  This is the *non-invariant* counterpart of
`subsetCharacterKernel_conjBy_of_invariant` — instead of assuming a `conjByMulEquiv w`-invariant
set,
it tracks exactly where conjugation moves the kernel.  It is the genuinely-absent `cfker_conjg`
brick underlying the (9.8.d) `W₁`-injectivity (Coq `injXtheta`, `cfker_conjg`): a `W₁`-conjugate of
a family member's kernel is the kernel of the conjugate, so a summand `S₀ = H₁` moved into
`W = H₂…H_q` by a nontrivial `w₁ ∈ W₁` lands in the kernel, forcing the family member trivial on
`H̄` — the contradiction that pins `w₁ = 1`. -/
theorem mem_characterKernel_conjBy {K : Subgroup G} [K.Normal]
    (w : G) (χ : ClassFunction ↥K ℂ) (n : ↥K) :
    n ∈ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.conjBy w χ)
      ↔ ClassFunction.conjByMulEquiv w n
        ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.mem_characterKernel]
  have hdeg : OddOrder.Peterfalvi.S03.characterDegree (ClassFunction.conjBy w χ)
      = OddOrder.Peterfalvi.S03.characterDegree χ := by
    rw [OddOrder.Peterfalvi.S03.characterDegree_def, OddOrder.Peterfalvi.S03.characterDegree_def]
    change (ClassFunction.conjBy w χ) 1 = χ 1
    rw [ClassFunction.conjBy_apply]
    refine congrArg χ (Subtype.ext ?_)
    simp only [OneMemClass.coe_one, mul_one, mul_inv_cancel]
  rw [hdeg, ClassFunction.conjBy_apply]
  constructor
  · intro h; rw [← h]; congr 1
  · intro h; rw [← h]; congr 1

/-- **Subgroup-level kernel transport under conjugation** (`cfker_conjg` subset form, Peterfalvi
(9.8.d) (γ) substrate).  A subgroup `N ≤ ↥K` (`K ⊴ G`) is contained in the kernel of the conjugate
`χ^w` iff every `w`-conjugate `conjByMulEquiv w n` (`n ∈ N`) lies in the kernel of `χ`.  Immediate
from the pointwise `mem_characterKernel_conjBy`.  The form consumed by the (9.8.d) injectivity: to
show `H₁ = S₀ ⊆ Ker (ζ₂^{w₁})` it suffices that `w₁·S₀·w₁⁻¹` — a Clifford `W₁`-conjugate of `S₀`,
contained in `W = H₂…H_q` for `w₁ ≠ 1` — is in `Ker ζ₂` (which it is, `W ⊆ Ker ζ₂`). -/
theorem subsetCharacterKernel_conjBy_iff {K : Subgroup G} [K.Normal]
    (w : G) (χ : ClassFunction ↥K ℂ) (N : Subgroup ↥K) :
    (N : Set ↥K) ⊆ OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.conjBy w χ)
      ↔ ∀ n ∈ N, ClassFunction.conjByMulEquiv w n
        ∈ OddOrder.Peterfalvi.S03.characterKernel χ := by
  constructor
  · intro h n hn; exact (mem_characterKernel_conjBy w χ n).mp (h hn)
  · intro h n hn; exact (mem_characterKernel_conjBy w χ n).mpr (h n hn)

/-- **`induceHU χ = Ind_{HU}^M χ`** (unfold the wrapper).  `induceHU` is definitionally
`ClassFunction.induce (huSub data)` with an internally-chosen `Invertible` instance; that instance
is
propositional (`Subsingleton`), so the wrapper equals the raw induction for any ambient instance.
Lets the `induceHU`-injectivity frame reuse the `induce_eq_induce_iff_conj` orbit machinery. -/
theorem induceHU_eq_induce [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    [Fintype ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ = ClassFunction.induce (huSub data) χ := by
  unfold induceHU
  convert rfl using 2
  exact Subsingleton.elim (α := Invertible (Nat.card ↥(huSub data) : ℂ)) _ _

/-- **`induceHU`-equality gives an `M`-conjugation of the sources** (Peterfalvi (9.8.d) (γ) frame).
If two irreducible `HU`-characters `χ, ψ` have equal `M`-inductions `Ind_{HU}^M`, then some
`w ∈ M` conjugates `ψ` to `χ` (`induce_eq_induce_iff_conj` at the `induceHU` wrapper level).  The
raw first step of the (9.8.d) injectivity: distinct inductions ⟺ distinct `M`-conjugacy orbits. -/
theorem induceHU_eq_imp_exists_conj [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    [Finite ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {χ ψ : IrreducibleCharacter ↥(huSub data)}
    (h : induceHU data (χ : ClassFunction ↥(huSub data) ℂ)
      = induceHU data (ψ : ClassFunction ↥(huSub data) ℂ)) :
    ∃ w : ↥M, IrreducibleCharacter.conjBy w ψ = χ := by
  have : Fintype ↥M := Fintype.ofFinite _
  have := huSub_normal data
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [induceHU_eq_induce data (χ : ClassFunction ↥(huSub data) ℂ),
    induceHU_eq_induce data (ψ : ClassFunction ↥(huSub data) ℂ)] at h
  obtain ⟨w, hw⟩ := (induce_eq_induce_iff_conj ψ χ).mp h.symm
  exact ⟨w, hw⟩

/-- **`induceHU` injective on irreducibles when the conjugator lies in `HU`** (Peterfalvi (9.8.d)
(γ) reduction — the honest frame isolating the `W₁`-content).  Given a criterion `hcrit` that *any*
`M`-conjugation carrying `ψ` to `χ` must be by an element of `HU` (`w ∈ huSub`), the `M`-induction
map `induceHU` is injective at `{χ, ψ}`: an `HU`-conjugation of an `HU`-character is inner
(`conjBy_eq_self_of_mem`), so `χ = conjBy w ψ = ψ`.

This reduces (9.8.d) (γ) — `Ind_{HU}^M` injective on the `ζ_{θ₁,λ}`-family up to `W₁` — to the pure
group/kernel statement `hcrit`: two family members are non-`W₁`-conjugate.  In the Coq proof
(`injXtheta`, `PFsection9.v` L1233-1253) `hcrit` is exactly the Frobenius `Ū ⋊ W₁` +
`cfker`-under-`W₁`-conjugation argument: decompose `w = y·w₁` (`M = HU ⋊ W₁`), `conjBy y` inner, so
`conjBy w₁ ψ = χ`; then `W = H₂…H_q ⊆ Ker ψ,Ker χ` (family members trivial on the summand
complement)
while a nontrivial `w₁` moves `S₀ = H₁` into `W` (Clifford permutation `H̄ = ⊕ S₀^{w}`), forcing
`H̄ ⊆ Ker χ` (via `mem_characterKernel_conjBy`) — contradicting `H ⊄ Ker χ`; hence `w₁ = 1`,
`w ∈ HU`.
The `cfker`-conjugation half (`mem_characterKernel_conjBy` / `subsetCharacterKernel_conjBy_iff`),
the `W = H₂…H_q ⊆ Ker` propagation (core (1), `hcuZetaPair_summandComplement_subset_ker`), and the
full `hcrit` reduction (`hcrit_of_summand_orbit`) are now all landed; the sole residual is the
(9.7.a) `W₁`-free-orbit datum `horbit` (`S₀^{w₁} ⊆ W`), absent from `CliffordCaseAData` (issue
1018). -/
theorem induceHU_inj_of_conj_mem_huSub [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    [Finite ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {χ ψ : IrreducibleCharacter ↥(huSub data)}
    (hcrit : ∀ w : ↥M, IrreducibleCharacter.conjBy w ψ = χ → (w : ↥M) ∈ huSub data)
    (h : induceHU data (χ : ClassFunction ↥(huSub data) ℂ)
      = induceHU data (ψ : ClassFunction ↥(huSub data) ℂ)) :
    χ = ψ := by
  have : Fintype ↥M := Fintype.ofFinite _
  have := huSub_normal data
  obtain ⟨w, hw⟩ := induceHU_eq_imp_exists_conj data h
  have hwHU : (w : ↥M) ∈ huSub data := hcrit w hw
  have hfix : IrreducibleCharacter.conjBy w ψ = ψ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.coe_conjBy]
    exact ClassFunction.conjBy_eq_self_of_mem hwHU (ψ : ClassFunction ↥(huSub data) ℂ)
  rw [← hw, hfix]

/-- **The `hcrit` of (9.8.d) (γ) from the Clifford data** (Peterfalvi (9.8.d), Coq `injXtheta`
`PFsection9.v` L1233-1253).  For two family members `ζ₁, ζ₂` with:
* `hS0notker`: `ζ₁`'s seed is nontrivial on the realized generator summand `S₀ = H₁`
  (`realized S₀ ⊄ Ker ζ₁` — true for a member, whose `θ₁ ≠ 1` on `S₀`);
* `hkerW₂`: `ζ₂` is trivial on the realized summand-complement `W = H₂…H_q` (core (1),
  `hcuZetaPair_summandComplement_subset_ker`);
* `horbit`: the (9.7.a) `W₁`-free-orbit datum — a nontrivial `w₁ ∈ W₁` moves `realized S₀` into
  `realized W`;

any `M`-conjugation `conjBy w ζ₂ = ζ₁` has `w ∈ HU`.  The honest reduction of `hcrit`:

* decompose `w = a·w₁` with `a ∈ HU`, `w₁ ∈ W₁` (`M = HU ⋊ W₁`, `data.typeP.M_complement`);
* `conjBy a` is inner (`a ∈ HU`, `conjBy_eq_self_of_mem`), so `conjBy w₁ ζ₂ = ζ₁`;
* if `w₁ ≠ 1`: for `s ∈ realized S₀`, `s ∈ Ker ζ₁ = Ker (conjBy w₁ ζ₂) ⟺ w₁·s·w₁⁻¹ ∈ Ker ζ₂`
  (`mem_characterKernel_conjBy`, `cfker_conjg`), and `w₁·s·w₁⁻¹ ∈ realized W` (`horbit`) `⊆ Ker ζ₂`
  (`hkerW₂`); so `realized S₀ ⊆ Ker ζ₁`, contradicting `hS0notker`;
* so `w₁ = 1`, `w = a ∈ HU`.

This is the exact `injXtheta` logic (`H₁ ⊆ Ker (χ^w)` for `w ∈ W₁#`, using `H₁^w ⊆ H₂…H_q ⊆ Ker`).
The `horbit` datum — a nontrivial `w₁ ∈ W₁` moving `S₀` into `W` — is the Peterfalvi (9.7.a)
free-`W₁`-orbit structure `H̄ = ⊕_{w ∈ W₁} S₀^w`; it is **reconstructed** from the stored `S₀`
(order `p`, `U`-invariant) and `chief.quotient_chiefFactor` (`U W₁`-irreducibility) by
`caseA_wOrbit_horbit` (with `W = caseA_wComplement caseA`), so the unconditional `hcrit`
(`horbit` discharged) is `caseA_hcrit_of_member`.  (`CliffordCaseAData` carries the summands only as
an *arbitrary* `U`-supindep family (`clifford_caseA_data`, `orbitRep : Fin q → U ⊔ W₁` from a choice
function), *not* the `W₁`-conjugate orbit; the orbit is re-derived rather than read off the carrier
—
no structure enrichment is needed, see issue 1018.) -/
theorem hcrit_of_summand_orbit [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    {chief : ChiefFactorData data} [Finite ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {S₀ W : Subgroup (↥data.H ⧸ chief.N)}
    {ζ₁ ζ₂ : IrreducibleCharacter ↥(huSub data)}
    (hS0notker : ¬ (((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₁ : ClassFunction ↥(huSub data) ℂ))
    (hkerW₂ : (((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₂ : ClassFunction ↥(huSub data) ℂ))
    (horbit : ∀ w₁ : ↥M, ((w₁ : ↥M) : G) ∈ data.typeP.W1 → w₁ ≠ 1 →
      ∀ s ∈ ((caseA_realizedComplement chief S₀).subgroupOf M).subgroupOf (huSub data),
        ClassFunction.conjByMulEquiv (H := huSub data) (w₁ : ↥M) s
          ∈ ((caseA_realizedComplement chief W).subgroupOf M).subgroupOf (huSub data)) :
    ∀ w : ↥M, IrreducibleCharacter.conjBy w ζ₂ = ζ₁ → (w : ↥M) ∈ huSub data := by
  have : Fintype ↥M := Fintype.ofFinite _
  have := huSub_normal data
  intro w hw
  -- decompose `w = a·w₁`, `a ∈ HU`, `w₁ ∈ W₁` (`M = HU ⋊ W₁`).
  have hcompl : Subgroup.IsComplement' (huSub data) (data.typeP.W1.subgroupOf M) := by
    rw [huSub_eq_derivedInG_subgroupOf]; exact data.typeP.M_complement
  obtain ⟨⟨a, w₁⟩, hprod⟩ := (hcompl.existsUnique w).exists
  simp only at hprod
  -- `conjBy w ζ₂ = conjBy w₁ ζ₂` (the `HU`-part `a` is inner).
  have hconjw₁ : IrreducibleCharacter.conjBy (w₁ : ↥M) ζ₂ = ζ₁ := by
    apply IrreducibleCharacter.ext
    rw [IrreducibleCharacter.coe_conjBy]
    have hstep : ClassFunction.conjBy ((a : ↥M) * (w₁ : ↥M)) (ζ₂ : ClassFunction ↥(huSub data) ℂ)
        = ClassFunction.conjBy (w₁ : ↥M) (ζ₂ : ClassFunction ↥(huSub data) ℂ) := by
      rw [ClassFunction.conjBy_mul, ClassFunction.conjBy_eq_self_of_mem a.2]
    rw [← hstep, hprod, ← IrreducibleCharacter.coe_conjBy, hw]
  -- suffices `w₁ = 1`, since then `w = a·1 = a ∈ HU`.
  suffices hw₁ : (w₁ : ↥M) = 1 by
    have : w = (a : ↥M) := by rw [← hprod, hw₁, mul_one]
    rw [this]; exact a.2
  by_contra hw₁ne
  -- if `w₁ ≠ 1`: realized `S₀ ⊆ Ker ζ₁`, contradicting `hS0notker` (`θ₁ ≠ 1` on `S₀`).
  apply hS0notker
  intro s hs
  -- `ζ₁ = conjBy w₁ ζ₂`, so `s ∈ Ker ζ₁ ⟺ w₁·s·w₁⁻¹ ∈ Ker ζ₂` (`cfker_conjg`).
  have hζ₁coe : (ζ₁ : ClassFunction ↥(huSub data) ℂ)
      = ClassFunction.conjBy (w₁ : ↥M) (ζ₂ : ClassFunction ↥(huSub data) ℂ) := by
    rw [← IrreducibleCharacter.coe_conjBy, hconjw₁]
  rw [SetLike.mem_coe] at hs
  rw [hζ₁coe]
  refine (mem_characterKernel_conjBy (w₁ : ↥M) (ζ₂ : ClassFunction ↥(huSub data) ℂ) s).mpr ?_
  -- `w₁·s·w₁⁻¹ ∈ realized W` (core (2), `horbit`) `⊆ Ker ζ₂` (core (1), `hkerW₂`).
  exact hkerW₂ (horbit w₁ w₁.2 hw₁ne s hs)

/-- **(9.8.d) (γ) `hcrit`, `horbit` discharged** (Peterfalvi (9.8.d), Coq `injXtheta`).  The
unconditional form of `hcrit_of_summand_orbit` with the summand-complement fixed to the genuine
`(9.7.a)` free-`W₁`-orbit complement `W = caseA_wComplement caseA = ⨆_{w∈W₁#} S₀^w` and its `horbit`
datum supplied by the reconstructed `caseA_wOrbit_horbit` (a nontrivial `w₁ ∈ W₁` moves the realized
`S₀` into the realized `W`).  Thus the `hcrit` for the (γ) `W₁`-injectivity now needs only the two
character-kernel facts that hold for a family member `ζ₁, ζ₂` (`realized S₀ ⊄ Ker ζ₁`,
`realized W ⊆ Ker ζ₂`); the `(9.7.a)` prerequisite is fully discharged (no `horbit` hypothesis
remains).  Combined with `induceHU_inj_of_conj_mem_huSub` this closes (γ) of Peterfalvi (9.8.d) once
`hkerW₂` is instantiated at `W = caseA_wComplement caseA` (via
`hcuZetaPair_summandComplement_subset_ker`
with `θ|_W = 1`, which holds since a member's seed `θ₁ ∈ Irr(H̄/W)`). -/
theorem caseA_hcrit_of_member [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) [Finite ↥M] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    {ζ₁ ζ₂ : IrreducibleCharacter ↥(huSub data)}
    (hS0notker : ¬
      (((caseA_realizedComplement chief caseA.S0).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₁ : ClassFunction ↥(huSub data) ℂ))
    (hkerW₂ : (((caseA_realizedComplement chief (caseA_wComplement caseA)).subgroupOf M).subgroupOf
          (huSub data) : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ₂ : ClassFunction ↥(huSub data) ℂ)) :
    ∀ w : ↥M, IrreducibleCharacter.conjBy w ζ₂ = ζ₁ → (w : ↥M) ∈ huSub data := by
  have : Fintype ↥M := Fintype.ofFinite _
  exact hcrit_of_summand_orbit data hS0notker hkerW₂ (caseA_wOrbit_horbit caseA)

set_option backward.isDefEq.respectTransparency false in
/-- **Homs trivial on `W` biject with homs of the quotient `H̄/W`** (Peterfalvi (9.8.d) (β)
substrate).
A hom `θ : H̄ →* ℂˣ` with `W ≤ Ker θ` descends uniquely to `H̄/W →* ℂˣ` (`QuotientGroup.lift`,
inverse `comp (mk' W)`), giving `|{θ | W ≤ Ker θ}| = |H̄/W →* ℂˣ|`.  The counting bridge for the
`θ`-numerator of the (9.8.d) domain count. -/
theorem card_hom_triv_W_eq_card_quotient [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (W : Subgroup (↥data.H ⧸ chief.N)) [W.Normal] :
    Nat.card {θ : (↥data.H ⧸ chief.N) →* ℂˣ // W ≤ θ.ker}
      = Nat.card ((↥data.H ⧸ chief.N) ⧸ W →* ℂˣ) := by
  refine Nat.card_congr
    { toFun := fun θ => QuotientGroup.lift W θ.1
        (fun x hx => MonoidHom.mem_ker.mp (θ.2 hx))
      invFun := fun ρ => ⟨ρ.comp (QuotientGroup.mk' W), fun x hx => ?_⟩
      left_inv := fun θ => ?_
      right_inv := fun ρ => ?_ }
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx, map_one]
  · apply Subtype.ext; apply MonoidHom.ext; intro x; dsimp only
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  · apply MonoidHom.ext; intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective W x
    dsimp only
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply]

open scoped Classical in
/-- **θ-count** (Peterfalvi (9.8.d) (β) numerator): the number of homs `θ : H̄ →* ℂˣ` *trivial on
the
summand complement* `W` and *nontrivial on `S₀`* equals `p − 1`.

Since `S₀ ⊔ W = ⊤`, `S₀ ⊓ W = ⊥` with `|S₀| = p`, the quotient `H̄/W ≅ S₀` (via the complement,
`IsComplement'.QuotientMulEquiv`) has order `p`.  Homs trivial on `W` are exactly homs of `H̄/W`
(`card_hom_triv_W_eq_card_quotient`), numbering `|H̄/W| = p` (Pontryagin,
`card_monoidHom_of_hasEnoughRootsOfUnity`); among them a hom is nontrivial on `S₀` iff it is nonzero
(a `W`-trivial, `S₀`-trivial hom is trivial on `S₀ ⊔ W = ⊤`, hence `= 1`), removing the single
trivial hom: `p − 1`.  This is the `(p-1)` factor of the (9.8.d) domain count `(p-1)·[C_U(S₀):U']`,
the `θ₁`-parameter count for the pair family `ψ_{θ₁,λ}` (`θ₁ ∈ Irr(H̄/W) \ {1}`). -/
theorem card_theta_triv_W_nontriv_S0 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    {W : Subgroup (↥data.H ⧸ chief.N)} [W.Normal]
    (hinf : caseA.S0 ⊓ W = ⊥) (hsup : caseA.S0 ⊔ W = ⊤)
    (hS0card : Nat.card ↥caseA.S0 = chief.p) :
    (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
        W ≤ θ.ker ∧ θ.comp caseA.S0.subtype ≠ 1).card = chief.p - 1 := by
  let : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  let : CommGroup ((↥data.H ⧸ chief.N) ⧸ W) :=
    { (inferInstance : Group ((↥data.H ⧸ chief.N) ⧸ W)) with
      mul_comm := fun a b => by
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective W a
        obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective W b
        rw [← map_mul, ← map_mul, chief.quotient_elementaryAbelian.1 x y] }
  have : NeZero (Monoid.exponent ((↥data.H ⧸ chief.N) ⧸ W)) :=
    ⟨Monoid.exponent_ne_zero_of_finite⟩
  -- `#{θ | W ≤ ker θ} = |H̄/W →* ℂˣ| = |H̄/W| = p`.
  have hcardWhom : (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => W ≤ θ.ker).card
      = chief.p := by
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card,
      card_hom_triv_W_eq_card_quotient W,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ((↥data.H ⧸ chief.N) ⧸ W) ℂ]
    let : Fintype (↥data.H ⧸ chief.N) := Fintype.ofFinite _
    have hcompl : Subgroup.IsComplement' caseA.S0 W :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.mpr hinf)
        (by rw [← Subgroup.normal_mul, hsup, Subgroup.coe_top])
    rw [← hS0card]
    exact Nat.card_congr hcompl.QuotientMulEquiv.toEquiv
  -- The set is `{θ | W ≤ ker θ} \ {1}` (a `W`-trivial, `S₀`-trivial hom is trivial on `⊤`).
  have hkey : (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
        W ≤ θ.ker ∧ θ.comp caseA.S0.subtype ≠ 1)
      = (Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ => W ≤ θ.ker).erase 1 := by
    ext θ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    constructor
    · rintro ⟨hW, hS0⟩
      exact ⟨fun h1 => hS0 (by rw [h1]; ext x; simp), hW⟩
    · rintro ⟨hne, hW⟩
      refine ⟨hW, fun hS0 => hne ?_⟩
      have hkerS0 : caseA.S0 ≤ θ.ker := fun x hx => by
        rw [MonoidHom.mem_ker]; simpa using DFunLike.congr_fun hS0 ⟨x, hx⟩
      have hker_top : (⊤ : Subgroup (↥data.H ⧸ chief.N)) ≤ θ.ker := by
        rw [← hsup]; exact sup_le hkerS0 hW
      refine MonoidHom.ext (fun x => ?_)
      have hxk : x ∈ θ.ker := hker_top (Subgroup.mem_top x)
      rw [MonoidHom.mem_ker] at hxk
      rw [hxk, MonoidHom.one_apply]
  rw [hkey, Finset.card_erase_of_mem, hcardWhom]
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [show ((1 : (↥data.H ⧸ chief.N) →* ℂˣ)).ker = ⊤ from MonoidHom.ker_one]
  exact le_top

/-- **step 5 (g): a `hcHom`-kernel-trivial `HC`-character is `hcPsi θbar`** (Peterfalvi (9.8.c)).
An irreducible `HC`-character `ψ` trivial on `Ker hcHom` (`= H₀C`) inflates from `H̄ = HC/H₀C`
(`exists_compHom_eq_of_subset_characterKernel`, `hcHom` surjective); since `H̄` is abelian the
inflation is *linear*, so `ψ = hcPsi θbar` for a hom-form seed `θbar : H̄ →* ℂˣ`.  This collapses
the
step-5 (e)(linear)/(f)(trivial)/(g)(identification) chain: the reducible `ξ`'s `HC`-constituent
`ψ'`,
being trivial on `H₀C` (from `ξ ∈ 𝒳(H₀C)`), is automatically linear and of `hcPsi` form. -/
theorem exists_hcPsi_eq_of_hcHom_ker_subset [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (ψ : IrreducibleCharacter
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
    (hker : ((hcHom chief).ker : Set ↥(hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ : ClassFunction _ ℂ)) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ,
      (ψ : ClassFunction _ ℂ) = (hcPsi chief θbar : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  obtain ⟨θbar_irr, heq⟩ :=
    OddOrder.RepresentationTheory.exists_compHom_eq_of_subset_characterKernel
      (hcHom_surjective chief) ψ hker
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  obtain ⟨θbar, hθbarval⟩ :=
    exists_units_monoidHom_of_isIrreducibleCharacter_of_isMulCommutative θbar_irr.isIrreducible
  refine ⟨θbar, ?_⟩
  have hθbar_eq : (θbar_irr : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) := by
    ext g
    rw [linearIrreducibleCharacter_apply, hθbarval]
  rw [← heq, hθbar_eq, ClassFunction.compHom_linearIrreducibleCharacter]
  rfl

/-- **`hcPsi θ` restricts on `hInHu` to the seed inflation `θ₀`** (`subgroupOf` form).  Restricting
the `HC`-linear character `hcPsi θ` to `hInHu.subgroupOf HC` equals the inflation
`θ₀ = linearIrr(θ ∘ mk'_N ∘ hInHuEquivH)` transported along `subgroupOfEquivOfLe`.  This is the
`subgroupOf`-form of `hcPsi_apply_inclusion`, matching the intermediate-character shape produced by
`exists_liesOver_intermediate` in the (9.8.c) Clifford-correspondence step 5.  Feeds the seed
identification `θbar'' = θbar` (`Res ψ' = θ₀'` at the intermediate constituent). -/
theorem hcPsi_restrict_hInHu_subgroupOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    ClassFunction.restrict ((hInHu data).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (hcPsi chief θ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
            hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data))).toMonoidHom
          (linearIrreducibleCharacter (θ.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ) := by
  ext x
  rw [ClassFunction.restrict_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom]
  set h := (Subgroup.subgroupOfEquivOfLe (le_sup_left :
    hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data))) x with hh
  have hxeq : (x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)))
      = Subgroup.inclusion (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) h := by
    apply Subtype.ext
    simp only [hh, Subgroup.coe_inclusion, Subgroup.subgroupOfEquivOfLe_apply_coe]
  rw [hxeq, hcPsi_apply_inclusion chief θ h]
  simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

/-- **A lies-over character whose restriction is irreducible identifies the constituent** (general
Clifford orthonormality): if the irreducible `χ` of `Γ` lies over `θ ∈ Irr K` and `Res_K χ` equals a
*single* irreducible character `η ∈ Irr K`, then `η = θ`.  `⟨Res_K χ, θ⟩ ≠ 0` becomes `⟨η, θ⟩ ≠ 0`,
which forces `η = θ` (distinct irreducibles orthogonal, `irreducibleCharacter_inner_eq_ite`). Used
to
identify the intermediate constituent's seed in the (9.8.c) step-5 assembly (a linear `ψ'` restricts
to a single character, pinning its inflation seed). -/
theorem eq_of_liesOver_of_restrict_eq_irr {Γ : Type*} [Group Γ] [Finite Γ]
    [Invertible (Nat.card Γ : ℂ)] {K : Subgroup Γ} [Fintype ↥K] [Invertible (Nat.card ↥K : ℂ)]
    {χ : IrreducibleCharacter Γ} {θ η : IrreducibleCharacter ↥K}
    (hover : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver K χ θ)
    (hres : ClassFunction.restrict K (χ : ClassFunction Γ ℂ) = (η : ClassFunction ↥K ℂ)) :
    η = θ := by
  have : Fintype Γ := Fintype.ofFinite Γ
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def, hres] at hover
  by_contra h
  exact hover (by rw [OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite η θ,
    if_neg h])

/-- **The seed is determined by the `hInHu`-restriction of `hcPsi`**: if `hcPsi θ₁` restricted to
`hInHu.subgroupOf HC` equals the transported inflation of `θ₂`, then `θ₁ = θ₂`.  By
`hcPsi_restrict_hInHu_subgroupOf` the left side is the transported inflation of `θ₁`, so the two
inflations agree; the descent hom `mk'_N ∘ hInHuEquivH ∘ subgroupOfEquivOfLe` is surjective, so
`θ₁ = θ₂` pointwise. This is the (g′) identification of the (9.8.c) step-5 assembly: the
intermediate
constituent `ψ' = hcPsi θbar''` lying over `θ₀ = infl θbar` forces `θbar'' = θbar`. -/
theorem hcPsi_seed_eq_of_restrict_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ₁ θ₂ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (h : ClassFunction.restrict ((hInHu data).subgroupOf
          (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (hcPsi chief θ₁ : ClassFunction
          ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
            hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
              (huSub data))).toMonoidHom
          (linearIrreducibleCharacter (θ₂.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)) :
    θ₁ = θ₂ := by
  have key := (hcPsi_restrict_hInHu_subgroupOf chief θ₁).symm.trans h
  have hsurj : Function.Surjective (fun z => (QuotientGroup.mk' chief.N)
      ((hInHuEquivH data) ((Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) z))) :=
    (QuotientGroup.mk'_surjective chief.N).comp
      ((hInHuEquivH data).surjective.comp (Subgroup.subgroupOfEquivOfLe _).surjective)
  refine MonoidHom.ext fun w => ?_
  obtain ⟨y, hy⟩ := hsurj w
  have hval : (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data))).toMonoidHom
        (linearIrreducibleCharacter (θ₁.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)) y
      = (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
          hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
            (huSub data))).toMonoidHom
        (linearIrreducibleCharacter (θ₂.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)) y := by rw [key]
  simp only [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply, MonoidHom.comp_apply] at hval
  simp only [] at hy
  rw [hy] at hval
  exact Units.val_injective hval

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **step 5 (assembly): the reducible `M`-fixed `ζ` is `Ind_{HC}^{HU}(hcPsi θbar)`** (Peterfalvi
(9.8.c), `Xmu` surjectivity).  A reducible (`M`-fixed) `ζ ∈ 𝒳(H₀C)` lying over the seed inflation
`θ₀` (`hlo`; the seed `θbar` is regular by `caseA_reducible_theta_regular`, `≠ 1` by `hnt`) equals
the
(9.8.c) construction `Ind_{HC}^{HU}(hcPsi θbar)`.

Chain: lies-over transitivity (`exists_liesOver_intermediate`) yields an `HC`-constituent `ψ'` with
`ζ` over `ψ'` and `ψ'` over `θ₀'`; `ζ ∈ 𝒳(H₀C)` (`hH0C`, trivial on `H₀C = Ker hcHom`) descends
(`liesOver_mem_characterKernel`) to `Ker hcHom ⊆ Ker ψ'`, so `ψ' = hcPsi θbar''`
(`exists_hcPsi_eq_of_hcHom_ker_subset`; `H̄` abelian ⟹ automatically linear).  Its restriction to
`hInHu` is `θ₀''` (`hcPsi_restrict_hInHu_subgroupOf`), a single irreducible (linear), so `ψ'` over
`θ₀'` forces `θ₀'' = θ₀'` (`eq_of_liesOver_of_restrict_eq_irr`), i.e. `θbar'' = θbar`
(`hcPsi_seed_eq_of_restrict_eq`).  Then `ζ` over `hcPsi θbar` and `Ind_{HC}(hcPsi θbar)` irreducible
(`hcZeta_irreducible`, foundation `caseA_reducible_inflation_inertia_eq`) give
`ζ = Ind_{HC}(hcPsi θbar)` (`coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce`). This is
the
surjectivity input to `|Xmu| = p-1`. -/
theorem caseA_reducible_eq_hcZeta [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θbar : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (ζ : IrreducibleCharacter ↥(huSub data))
    (hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver (hInHu data) ζ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hMfix : ClassFunction.inertia (ζ : ClassFunction ↥(huSub data) ℂ) = ⊤)
    (hnt : θbar ≠ 1)
    (hH0C : (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ζ : ClassFunction ↥(huSub data) ℂ)) :
    (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θbar) := by
  classical
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  have : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  let : Fintype ↥((hInHu data).subgroupOf (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥((hInHu data).subgroupOf (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- foundation `I_{HU}(θ₀) = HC`, hence `Ind_{HC}(hcPsi θbar)` irreducible.
  have hθ₀ := caseA_reducible_inflation_inertia_eq caseA θbar ζ hlo hMfix hnt
  have hind := hcZeta_irreducible chief θbar hθ₀
  -- intermediate `HC`-constituent `ψ'`.
  obtain ⟨ψ', hζψ', hψ'θ₀⟩ := exists_liesOver_intermediate
    (le_sup_left : hInHu data ≤ hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ζ
    (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom))) hlo
  -- (f) `Ker hcHom ⊆ Ker ψ'` from `ζ` trivial on `H₀C`.
  have hker : ((hcHom chief).ker : Set ↥(hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      ⊆ OddOrder.Peterfalvi.S03.characterKernel (ψ' : ClassFunction _ ℂ) := by
    intro g hg
    rw [SetLike.mem_coe, MonoidHom.mem_ker] at hg
    refine liesOver_mem_characterKernel hζψ' (hH0C ?_)
    rw [SetLike.mem_coe, ← Subgroup.mem_subgroupOf]
    simp only [hcHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at hg
    rwa [map_eq_one_iff _ (hcQuotientEquivHbar chief).injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hg
  -- (g) `ψ' = hcPsi θbar''`.
  obtain ⟨θbar'', hψ'eq⟩ := exists_hcPsi_eq_of_hcHom_ker_subset chief ψ' hker
  -- (g′) `θbar'' = θbar` via the restriction identity + orthonormality.
  set η : IrreducibleCharacter ↥((hInHu data).subgroupOf (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :=
    ⟨ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe (le_sup_left :
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))).toMonoidHom
      (linearIrreducibleCharacter (θbar''.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ),
      (linearIrreducibleCharacter (θbar''.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom))).isIrreducible.compHom_of_surjective
        (Subgroup.subgroupOfEquivOfLe _).surjective⟩ with hηdef
  have hres_eq : ClassFunction.restrict ((hInHu data).subgroupOf (hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (ψ' : ClassFunction _ ℂ) = (η : ClassFunction _ ℂ) := by
    rw [hψ'eq, hcPsi_restrict_hInHu_subgroupOf chief θbar'']
  have hη := eq_of_liesOver_of_restrict_eq_irr hψ'θ₀ hres_eq
  have hθbar : θbar'' = θbar := by
    refine hcPsi_seed_eq_of_restrict_eq chief θbar'' θbar ?_
    rw [hcPsi_restrict_hInHu_subgroupOf chief θbar'']
    exact congrArg IrreducibleCharacter.toClassFunction hη
  -- conclude `ζ = Ind_{HC}(hcPsi θbar)`.
  refine coe_eq_induce_of_liesOver_of_isIrreducibleCharacter_induce ζ (hcPsi chief θbar) hind ?_
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def]
  rw [OddOrder.RepresentationTheory.IrreducibleCharacter.liesOver_iff,
    ClassFunction.restrictionMultiplicity_def] at hζψ'
  rwa [hψ'eq, hθbar] at hζψ'

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **step 5 consequence (caseA): a reducible `𝒮(H₀)`-member is `Ind_{HU}^M(Ind_{HC}(hcPsi θbar))`
for
a regular seed `θbar`.**  A reducible `φ = Ind_{HU}^M χ ∈ 𝒮(H₀)` has `M`-fixed source `χ`
(`inertia_eq_top_of_induceHU_not_irreducible`); the case-agnostic cardinality argument
`reducible_mem_sOf_H0C` places `φ ∈ 𝒮(H₀C)`, and `Ind`-injectivity on reducibles
(`caseA_induceHU_inj_of_reducible`) upgrades `χ`'s kernel to `H₀C ⊆ Ker χ` (`χ ∈ 𝒳(H₀C)`).  The seed
`θbar` (`exists_hom_constituent_of_mem_xiSet_H0`, nontrivial) is regular by the `M`-fixedness
(`caseA_reducible_theta_regular`), so `caseA_reducible_eq_hcZeta` identifies
`χ = Ind_{HC}(hcPsi θbar)`.  The shared extraction behind the (9.8.b) degree
(`caseA_reducible_induceHU_apply_one_eq_qu`) and the (9.8.c) `Xmu`-surjectivity. -/
theorem caseA_reducible_source_eq_hcZeta [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (φ : ClassFunction ↥M ℂ) (hφ : φ ∈ sOf data chief.H0)
    (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ θbar : (↥data.H ⧸ chief.N) →* ℂˣ, (∀ i, θbar.comp (caseA.Hpart i).subtype ≠ 1) ∧
      φ = induceHU data (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsi chief θbar)) := by
  classical
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥(hInHu data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
    hcInHu_realized_normal chief
  obtain ⟨χ, hχ, rfl⟩ := hφ
  have hind_red : ¬ IsIrreducibleCharacter
      (ClassFunction.induce (huSub data) (χ : ClassFunction ↥(huSub data) ℂ)) := hred
  have hMfix := inertia_eq_top_of_induceHU_not_irreducible data χ hind_red
  obtain ⟨θbar, hnt, hlo⟩ := exists_hom_constituent_of_mem_xiSet_H0 hχ.1 hχ.2
  -- C-kernel: `χ ∈ 𝒳(H₀C)` via cardinality membership + `Ind`-injectivity.
  obtain ⟨χ', hχ'C, hχ'eq⟩ := reducible_mem_sOf_H0C hG chars
    (induceHU data (χ : ClassFunction ↥(huSub data) ℂ)) ⟨χ, hχ, rfl⟩ hred
  have hχ'χ : χ' = χ := caseA_induceHU_inj_of_reducible data hind_red hχ'eq
  have hH0C := (hχ'χ ▸ hχ'C : χ ∈ xiOf data (chief.H0 ⊔ chars.C)).2
  refine ⟨θbar, caseA_reducible_theta_regular caseA θbar χ hlo hMfix hnt, ?_⟩
  exact congrArg (induceHU data) (caseA_reducible_eq_hcZeta caseA θbar χ hlo hMfix hnt hH0C)

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Peterfalvi (13.3.a) core, case (a)** (the (9.8.b)-side `isIndHC`): in Clifford case (a),
every *reducible* member of `𝒮(H₀)` is induced from a linear character of `HC` at the
`M`-level.  `caseA_reducible_source_eq_hcZeta` identifies the source as
`Ind_{HC}(hcPsi θbar)` (regular seed), and the stages-flattening
(`isIndHC_of_source_eq_induce_hcPsi`) concludes. -/
theorem caseA_reducible_sOf_H0_isIndHC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Fintype ↥M] [Finite ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data chief.H0) (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      φ = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  classical
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Fintype ↥(hInHu data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)).Normal := hcInHu_realized_normal chief
  obtain ⟨θbar, hreg, hφeq⟩ := caseA_reducible_source_eq_hcZeta caseA hG φ hφ hred
  have hreg' : ∀ i, ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro i
    obtain ⟨x, hx, hne⟩ := (comp_subtype_ne_one_iff_exists caseA θbar i).mp (hreg i)
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      Units.val_one]
    simpa using hne
  have hθ₀ := inertia_eq_hcInHu_caseA data chief caseA hreg'
  obtain ⟨ψ, hψirr, hψone, hψeq⟩ := isIndHC_of_source_eq_induce_hcPsi
    (ζ' := ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θbar), hcZeta_irreducible chief θbar hθ₀⟩) (θbar := θbar) rfl
  exact ⟨ψ, hψirr, hψone, hφeq.trans hψeq⟩

set_option maxHeartbeats 1600000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Peterfalvi (13.3.a) core, case-agnostic (Coq `isIndHC`)**: every *reducible* member of
`𝒮(H₀)` is induced from a linear character of `HC` at the `M`-level — in either Clifford case
(`clifford_dichotomy`; case (a) = `caseA_reducible_sOf_H0_isIndHC` via (9.8.b), case (b) =
`caseB_reducible_sOf_H0_isIndHC` via (9.9.b)).  In the §13 `S`-instantiation `HC = PC`, so
this is exactly (13.3.a)'s "`μ_j` is induced from a linear character of `PC`". -/
theorem reducible_sOf_H0_isIndHC [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    [Fintype ↥M] [Finite ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)) : ℂ)]
    [Invertible (Nat.card ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
      M).subgroupOf (huSub data)).map (huSub data).subtype) : ℂ)]
    {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ sOf data chief.H0) (hred : ¬ IsIrreducibleCharacter φ) :
    ∃ ψ : ClassFunction
        ↥((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter ψ ∧
      ψ 1 = 1 ∧
      φ = ClassFunction.induce
        ((hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)).map (huSub data).subtype) ψ := by
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  rcases clifford_dichotomy hG chars with hA | hB
  · obtain ⟨caseA⟩ := hA
    exact caseA_reducible_sOf_H0_isIndHC hG caseA hφ hred
  · obtain ⟨caseB⟩ := hB
    exact caseB_reducible_sOf_H0_isIndHC hG chars caseB hφ hred

/-- **step 5 consequence (9.8.b degree, caseA): a reducible `𝒮(H₀)`-member has degree `qu`.**  By
`caseA_reducible_source_eq_hcZeta` the reducible `φ = Ind_{HU}^M(Ind_{HC}(hcPsi θbar))`, whose
degree
is `q·u` (`hcZeta_induceHU_apply_one`).  The degree half of `caseA_character_counts` conjunct
(b). -/
theorem caseA_reducible_induceHU_apply_one_eq_qu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (φ : ClassFunction ↥M ℂ) (hφ : φ ∈ sOf data chief.H0)
    (hred : ¬ IsIrreducibleCharacter φ) :
    φ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) := by
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨θbar, _, rfl⟩ := caseA_reducible_source_eq_hcZeta caseA hG φ hφ hred
  exact hcZeta_induceHU_apply_one chars θbar

/-- **A regular seed's inflation `θ₀` has `HU`-inertia `HC`** (caseA).  Converts the hom-form
regularity (`θ` nontrivial on each Clifford summand `Hpart i`) to `inertia_eq_hcInHu_caseA`'s
pointwise form via `comp_subtype_ne_one_iff_exists`.  The direct-seed analogue of
`caseA_reducible_inflation_inertia_eq` (which routes through `caseA_reducible_theta_regular`);
supplies the `hθ₀` of `hcZeta_irreducible` / `hcZeta_induceHU_mem_sOf` for `Xθ`-members. -/
theorem caseA_regular_inflation_inertia_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hreg : ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1)
    [Finite ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)] :
    ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cInHu data chief := by
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  exact inertia_eq_hcInHu_caseA data chief caseA (fun i => by
    obtain ⟨x, hx, hne⟩ := (comp_subtype_ne_one_iff_exists caseA θ i).mp (hreg i)
    exact ⟨x, hx, by
      rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
        Units.val_one]
      simpa using hne⟩)

/-- **A regular seed's `Ind_{HC}(hcPsi θ)` is irreducible** (caseA `Xθ`-member irreducibility).  The
inflation `θ₀` has `HU`-inertia `HC` (`caseA_regular_inflation_inertia_eq`), so
`Ind_{HC}^{HU}(hcPsi θ)` is irreducible (`hcZeta_irreducible`).  Bundles every `Xθ`-member as an
`IrreducibleCharacter`, the input to the (9.8.c) `|Xmu| = p-1` bijection. -/
theorem caseA_hcZeta_irreducible_of_regular [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hreg : ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1)
    [Finite ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)] [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    IsIrreducibleCharacter (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ)) := by
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  exact hcZeta_irreducible chief θ (caseA_regular_inflation_inertia_eq caseA θ hreg)

set_option linter.style.openClassical false in
set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **|Xmu| = p-1** (Peterfalvi (9.8.c), the reducible-inducing regular seeds).  `Xmu` = the
`Xθ`-members `ζ = Ind_{HC}(hcPsi θ)` (regular `θ`) whose `M`-induction `Ind_{HU}^M ζ` is
*reducible*.
The map `ζ ↦ Ind_{HU}^M ζ` is a bijection `Xmu ≃ {reducible 𝒮(H₀)-members}`: injective on reducibles
(`caseA_induceHU_inj_of_reducible`) and surjective (every reducible `𝒮(H₀)`-member is
`Ind_{HU}^M(Ind_{HC}(hcPsi θbar))` for a regular seed, `caseA_reducible_source_eq_hcZeta`), so
`|Xmu| = |{reducibles}| = p-1` (`reducible_count_sOf_H0`).  The `|Xmu|` half of the (9.8.c) parity
dichotomy `exists_regular_not_reducible_of_odd`. -/
theorem caseA_Xmu_card_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Fintype ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Finite ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    (((Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
          ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1).image fun θ =>
        ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) (hcPsi chief θ).toClassFunction).filter fun ζ =>
        ¬ IsIrreducibleCharacter (induceHU data ζ)).card
      = chief.p - 1 := by
  classical
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set Xθ := RegF.image fun θ =>
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  -- `Ind_{HU}^M` is injective on `Xmu` (its members induce reducibly).
  have hinj : Set.InjOn (induceHU data) ↑Xmu := by
    intro ζ₁ hζ₁ ζ₂ hζ₂ heq
    rw [Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image] at hζ₁ hζ₂
    obtain ⟨⟨θ₁, hθ₁, rfl⟩, hred₁⟩ := hζ₁
    obtain ⟨⟨θ₂, hθ₂, rfl⟩, _⟩ := hζ₂
    have hirr₁ := caseA_hcZeta_irreducible_of_regular caseA θ₁ (Finset.mem_filter.mp hθ₁).2
    have hirr₂ := caseA_hcZeta_irreducible_of_regular caseA θ₂ (Finset.mem_filter.mp hθ₂).2
    have hχ := caseA_induceHU_inj_of_reducible data (χ := ⟨_, hirr₁⟩) (ψ := ⟨_, hirr₂⟩) hred₁ heq
    exact congrArg IrreducibleCharacter.toClassFunction hχ.symm
  -- `Ind_{HU}^M '' Xmu = {reducible 𝒮(H₀)-members}`.
  have himg : induceHU data '' ↑Xmu = {φ ∈ sOf data chief.H0 | ¬ IsIrreducibleCharacter φ} := by
    ext φ
    simp only [Set.mem_image, Finset.mem_coe, hXmu, Finset.mem_filter, hXθ, Finset.mem_image,
      Set.mem_ofPred_eq]
    constructor
    · rintro ⟨_, ⟨⟨θ, hθ, rfl⟩, hζred⟩, rfl⟩
      have hreg := (Finset.mem_filter.mp hθ).2
      have hnt : θ ≠ 1 := fun h => hreg ⟨0, hq⟩ (by rw [h]; exact MonoidHom.one_comp _)
      exact ⟨sOf_antitone data le_sup_left
        (hcZeta_induceHU_mem_sOf chars θ hnt (caseA_regular_inflation_inertia_eq caseA θ hreg)),
        hζred⟩
    · rintro ⟨hφS, hφred⟩
      obtain ⟨θbar, hreg, rfl⟩ := caseA_reducible_source_eq_hcZeta caseA hG φ hφS hφred
      exact ⟨_, ⟨⟨θbar, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hreg⟩, rfl⟩, hφred⟩, rfl⟩
  rw [← Set.ncard_coe_finset Xmu, ← hinj.ncard_image, himg,
    reducible_count_sOf_H0 hG chief]

set_option linter.style.openClassical false in
set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
open scoped Classical in
/-- **Peterfalvi (9.8.c): `𝒮(H₀C)` contains an irreducible character of degree `qu`.**  The parity
dichotomy `exists_regular_not_reducible_of_odd` applied to `X = Xθ` (`u·|Xθ| = (p-1)^q` by
`oXtheta_count`, `p-1` even as `p ∤ |G|` is odd, `u` odd by `u_odd`) and its `p-1`-element subfamily
`Xmu` (`caseA_Xmu_card_eq`) yields a regular seed's `ζ = Ind_{HC}(hcPsi θ)` outside `Xmu`, i.e. with
`Ind_{HU}^M ζ` *irreducible*.  That `Ind_{HU}^M ζ` is the required member: in `𝒮(H₀C)`
(`hcZeta_induceHU_mem_sOf`), irreducible, of degree `q·u` (`hcZeta_induceHU_apply_one`). -/
theorem caseA_exists_irreducible_sOf_H0C [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    [Finite ((↥data.H ⧸ chief.N) →* ℂˣ)]
    [Finite ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [Finite ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ∃ χ ∈ sOf data (chief.H0 ⊔ chars.C), IsIrreducibleCharacter χ ∧
      χ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) := by
  have : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
    (huSub data)) := Fintype.ofFinite _
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  -- `p ∣ |G|` (odd), so `p` is odd and `p-1` even.
  have hpq : chief.p ^ data.q ∣ Nat.card ↥data.H := ⟨Nat.card ↥chief.H0, chief.quotient_order⟩
  have hp_dvd : chief.p ∣ Nat.card G :=
    (dvd_pow_self chief.p hq.ne').trans (hpq.trans (Subgroup.card_subgroup_dvd_card data.H))
  have hp_ne2 : chief.p ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hG.odd) (even_iff_two_dvd.mpr (h ▸ hp_dvd))
  have hp1_even : Even (chief.p - 1) := by
    obtain ⟨k, hk⟩ := chief.p_prime.odd_of_ne_two hp_ne2
    exact ⟨k, by omega⟩
  set RegF := Finset.univ.filter fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
    ∀ i, θ.comp (caseA.Hpart i).subtype ≠ 1 with hRegF
  set Xθ := RegF.image fun θ =>
      ClassFunction.induce (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
        (huSub data)) (hcPsi chief θ).toClassFunction with hXθ
  set Xmu := Xθ.filter fun ζ => ¬ IsIrreducibleCharacter (induceHU data ζ) with hXmu
  -- a regular seed inducing irreducibly (`ζ ∈ Xθ \ Xmu`).
  have hcard : (↑Xmu : Set (ClassFunction ↥(huSub data) ℂ)).ncard = chief.p - 1 := by
    rw [Set.ncard_coe_finset]; exact caseA_Xmu_card_eq caseA hG
  have hcount : chars.u * (↑Xθ : Set (ClassFunction ↥(huSub data) ℂ)).ncard
      = (chief.p - 1) ^ data.q := by
    rw [Set.ncard_coe_finset]; exact oXtheta_count caseA
  obtain ⟨ζ, hζ, hζn⟩ := exists_regular_not_reducible_of_odd Xθ.finite_toSet
    (Finset.coe_subset.mpr (Finset.filter_subset _ _)) hcard hcount
    (Nat.sub_pos_of_lt chief.p_prime.one_lt) hp1_even (u_odd hG chars) data.nontrivial.2.1.two_le
  rw [Finset.mem_coe, hXθ, Finset.mem_image] at hζ
  obtain ⟨θ, hθ, rfl⟩ := hζ
  have hreg := (Finset.mem_filter.mp hθ).2
  have hnt : θ ≠ 1 := fun h => hreg ⟨0, hq⟩ (by rw [h]; exact MonoidHom.one_comp _)
  have hirr : IsIrreducibleCharacter (induceHU data (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ).toClassFunction)) := by
    by_contra h
    refine hζn ?_
    simp only [Finset.mem_coe, Finset.mem_filter, hXθ, Finset.mem_image]
    exact ⟨⟨θ, hθ, rfl⟩, h⟩
  exact ⟨_, hcZeta_induceHU_mem_sOf chars θ hnt (caseA_regular_inflation_inertia_eq caseA θ hreg),
    hirr, hcZeta_induceHU_apply_one chars θ⟩

end OddOrder.Peterfalvi.S11


