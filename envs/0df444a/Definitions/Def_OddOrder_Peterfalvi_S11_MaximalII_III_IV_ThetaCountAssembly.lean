-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:15:25.567525+00:00
-- url     : https://prove2.me/theorems/5aed9410-e9f0-459f-a7bc-6855008b1bcc
-- title:
--   Peterfalvi (9.8.d): $\theta$-count, $I_\theta$ reconstruction and assembly
-- statement:
--   Formalizes the count substrate for Peterfalvi (9.8.d): generic homomorphism counts through a normal quotient and commutator containment in the realized $U'$.
--
--   Main declarations: `card_hom_triv_N_eq_card_quotient_general` (Peterfalvi (9.8.d)); `commutator_cuInHu_le_uprimeRealized` (Peterfalvi (9.8.d)).
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/ThetaCountAssembly.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/ThetaCountAssembly.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- **Peterfalvi (9.8.d)** (count substrate). Uniform hinv for a family θ: W = caseA_wComplement, θ
trivial on W. -/
theorem hcuSeedHom_hinv_of_wComplement_triv [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Finite ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1))]
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hθW : caseA_wComplement caseA ≤ θ.ker) :
    ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h := by
  have : Fintype ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    Fintype.ofFinite _
  have htriv : ∀ w ∈ caseA_wComplement caseA,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
        = (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro w hw
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      MonoidHom.mem_ker.mp (hθW hw), Units.val_one]
  exact hcuSeedHom_invariance_of_cuInHu_le_inertia caseA θ
    (cuInHu_le_inertia_of_complement_triv caseA (caseA_wComplement_aInvariant caseA)
      (caseA_S0_sup_wComplement caseA) htriv)

/-- **Peterfalvi (9.8.d)** (count substrate). hcuSeedHom is injective in θ (mk' surjective,
hInHuEquivH iso). -/
theorem hcuSeedHom_injective [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Function.Injective (hcuSeedHom (chief := chief) (data := data)) := by
  have := chief.N_normal
  intro θ₁ θ₂ h12
  have hsurj : Function.Surjective ((QuotientGroup.mk' chief.N).comp (hInHuEquivH
      data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  apply MonoidHom.ext
  intro x
  obtain ⟨y, rfl⟩ := hsurj x
  exact DFunLike.congr_fun h12 y

/-- **Peterfalvi (9.8.d)** (count substrate). The pair character recovers λ on C. -/
theorem hcuPsiPair_apply_inclusion_cuInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ) (c : ↥(cuInHu caseA)) :
    (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
        (Subgroup.inclusion (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA) c)
      = (lam c : ℂ) := by
  simp only [hcuPsiPair, hcuPairHom, linearIrreducibleCharacter_apply, MonoidHom.mul_apply,
    hcuThetaHom_inclusion_cuInHu, one_mul, hcuLambdaHom_inclusion]

/-- **Peterfalvi (9.8.d)** (count substrate).  Injectivity of the pair-parametrization:
distinct `(θ,λ)` give distinct pair characters (restrictions recover `θ`, `λ`). -/
theorem hcuPsiPair_injective_pair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    {θ₁ θ₂ : (↥data.H ⧸ chief.N) →* ℂˣ}
    {hinv₁ : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ₁
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ₁ h}
    {hinv₂ : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ₂
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ₂ h}
    {lam₁ lam₂ : ↥(cuInHu caseA) →* ℂˣ}
    (heq : hcuPsiPair caseA θ₁ hinv₁ lam₁ = hcuPsiPair caseA θ₂ hinv₂ lam₂) :
    θ₁ = θ₂ ∧ lam₁ = lam₂ := by
  have hcoe : (hcuPsiPair caseA θ₁ hinv₁ lam₁ : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      = (hcuPsiPair caseA θ₂ hinv₂ lam₂ : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ) := by
    rw [heq]
  constructor
  · -- θ from H-restriction: hcuSeedHom θ₁ = hcuSeedHom θ₂, then injectivity.
    apply hcuSeedHom_injective chief
    apply MonoidHom.ext; intro h
    have h1 := hcuPsiPair_apply_inclusion caseA θ₁ hinv₁ lam₁ h
    have h2 := hcuPsiPair_apply_inclusion caseA θ₂ hinv₂ lam₂ h
    have := congrFun (congrArg (fun η : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ =>
      (η : ↥(hInHu data ⊔ cuInHu caseA) → ℂ)) hcoe)
      (Subgroup.inclusion (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h)
    rw [h1, h2] at this
    simp only [ClassFunction.compHom_linearIrreducibleCharacter,
      linearIrreducibleCharacter_apply] at this
    refine Units.val_injective ?_
    simpa only [hcuSeedHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      QuotientGroup.mk'_apply] using this
  · -- λ from C-restriction.
    apply MonoidHom.ext; intro c
    have h1 := hcuPsiPair_apply_inclusion_cuInHu caseA θ₁ hinv₁ lam₁ c
    have h2 := hcuPsiPair_apply_inclusion_cuInHu caseA θ₂ hinv₂ lam₂ c
    have := congrFun (congrArg (fun η : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ =>
      (η : ↥(hInHu data ⊔ cuInHu caseA) → ℂ)) hcoe)
      (Subgroup.inclusion (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA) c)
    rw [h1, h2] at this
    exact Units.val_injective this

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (9.8.d)** (count substrate).  Generic hom-count through a normal quotient: homs
`f : K →* ℂˣ` with `N ≤ Ker f` biject with homs of `K/N` (`QuotientGroup.lift`).  The group-agnostic
form of `card_hom_triv_W_eq_card_quotient`, for the `λ`-numerator over `cuInHu/U'`. -/
theorem card_hom_triv_N_eq_card_quotient_general {K : Type*} [Group K] [Finite K]
    (N : Subgroup K) [N.Normal] :
    Nat.card {f : K →* ℂˣ // N ≤ f.ker} = Nat.card (K ⧸ N →* ℂˣ) := by
  refine Nat.card_congr
    { toFun := fun f => QuotientGroup.lift N f.1 (fun x hx => MonoidHom.mem_ker.mp (f.2 hx))
      invFun := fun ρ => ⟨ρ.comp (QuotientGroup.mk' N), fun x hx => ?_⟩
      left_inv := fun f => ?_
      right_inv := fun ρ => ?_ }
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff x).mpr hx, map_one]
  · apply Subtype.ext; apply MonoidHom.ext; intro x; dsimp only
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']
  · apply MonoidHom.ext; intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N x
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply]

open scoped commutatorElement in
/-- **Peterfalvi (9.8.d)** (count substrate).  `⁅cuInHu, cuInHu⁆ ≤ U'` realized: the derived
subgroup
of the realized `C_U(S₀)` lands in the realized `U' = [U,U]`, since `C_U(S₀) ≤ U`. Makes the
quotient
`C_U(S₀)/U'` abelian, so its linear characters number `[C_U(S₀):U']` (Pontryagin). -/
theorem commutator_cuInHu_le_uprimeRealized [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ⁅cuInHu caseA, cuInHu caseA⁆
      ≤ (((uprimeSub data).subgroupOf M).subgroupOf (huSub data)) := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  -- (a:G),(b:G) ∈ U
  have haU : (((a : ↥(huSub data)) : ↥M) : G) ∈ data.U := by
    have : a ∈ uInHu data := cuInHu_le_uInHu caseA ha
    simpa only [uInHu, Subgroup.mem_subgroupOf] using this
  have hbU : (((b : ↥(huSub data)) : ↥M) : G) ∈ data.U := by
    have : b ∈ uInHu data := cuInHu_le_uInHu caseA hb
    simpa only [uInHu, Subgroup.mem_subgroupOf] using this
  -- coe of ⁅a,b⁆ to G is ⁅(a:G),(b:G)⁆
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
    show uprimeSub data = ⁅data.U, data.U⁆ from derivedInG_eq_commutator _]
  have hcoeM : (((⁅a, b⁆ : ↥(huSub data)) : ↥M))
      = ⁅((a : ↥(huSub data)) : ↥M), ((b : ↥(huSub data)) : ↥M)⁆ :=
    map_commutatorElement (huSub data).subtype a b
  have hcoeG : ((((⁅a, b⁆ : ↥(huSub data)) : ↥M)) : G)
      = ⁅(((a : ↥(huSub data)) : ↥M) : G), (((b : ↥(huSub data)) : ↥M) : G)⁆ := by
    rw [hcoeM]; exact map_commutatorElement M.subtype _ _
  rw [hcoeG]
  exact Subgroup.commutator_mem_commutator haU hbU

/-- **Peterfalvi (9.8.d)** (count substrate).  The `λ`-numerator: linear characters
`λ : C_U(S₀) →* ℂˣ` trivial on `U'` number `[C_U(S₀):U']`.  The realized `U'` (as a subgroup of
`cuInHu`) contains the derived subgroup (`commutator_cuInHu_le_uprimeRealized`), so it is normal
with
abelian quotient `cuInHu/U'`; hence `#{λ | U'-realized ⊆ Ker λ} = |cuInHu/U' →* ℂˣ| = |cuInHu/U'|`
(Pontryagin) `= (U'-realized).relIndex(cuInHu) = (uprimeSub).relIndex(cuSub)` (`relIndex_subgroupOf`
twice).  The `λ`-factor count of the (9.8.d) domain `(p-1)·[C_U(S₀):U']`. -/
theorem card_lambda_triv_uprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Nat.card {lam : ↥(cuInHu caseA) →* ℂˣ //
        (((uprimeSub data).subgroupOf M).subgroupOf (huSub data)).subgroupOf (cuInHu caseA)
          ≤ lam.ker}
      = (uprimeSub data).relIndex (cuSub caseA) := by
  set N := (((uprimeSub data).subgroupOf M).subgroupOf (huSub data)).subgroupOf (cuInHu caseA) with
      hN
  have hcomm : _root_.commutator ↥(cuInHu caseA) ≤ N := by
    rw [hN]
    rw [Subgroup.subgroupOf, ← Subgroup.map_le_iff_le_comap]
    refine le_trans (le_of_eq (Subgroup.map_subtype_commutator _)) ?_
    exact commutator_cuInHu_le_uprimeRealized caseA
  have hNnorm : N.Normal := Subgroup.Normal.of_commutator_le (h := hcomm)
  have hcommM : IsMulCommutative (↥(cuInHu caseA) ⧸ N) :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le).mpr hcomm
  let : CommGroup (↥(cuInHu caseA) ⧸ N) :=
    { (inferInstance : Group (↥(cuInHu caseA) ⧸ N)) with
      mul_comm := isMulCommutative_iff.mp hcommM }
  have : NeZero (Monoid.exponent (↥(cuInHu caseA) ⧸ N)) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  rw [card_hom_triv_N_eq_card_quotient_general N,
    CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (↥(cuInHu caseA) ⧸ N) ℂ,
    ← Subgroup.index_eq_card]
  -- N.index (in ↥cuInHu) = (uprime-realized).relIndex(cuInHu) = (uprimeSub).relIndex(cuSub).
  have h1 : N.index = (((uprimeSub data).subgroupOf M).subgroupOf (huSub data)).relIndex
      (cuInHu caseA) := by rw [Subgroup.relIndex, hN]
  rw [h1, show cuInHu caseA = ((cuSub caseA).subgroupOf M).subgroupOf (huSub data) from rfl,
    show huSub data = (data.H ⊔ data.U).subgroupOf M from rfl,
    Subgroup.relIndex_subgroupOf (Subgroup.subgroupOf_mono M
      ((cuSub_le_U caseA).trans (le_sup_right : data.U ≤ data.H ⊔ data.U))),
    Subgroup.relIndex_subgroupOf ((cuSub_le_U caseA).trans (U_le_M data))]

/-- **Peterfalvi (9.8.d)** (count substrate).  For a seed `θ` trivial on `W = caseA_wComplement` and
nontrivial on `S₀`, the pair character `ψ_{θ,λ}` has `HU`-inertia exactly `H·C_U(S₀)`
(`inertia_eq_hcuInHu` at `W = caseA_wComplement` feeds `hcuPsiPair_inertia_eq_hcu`).  Feeds
`card_image_induce_mul_index_eq` for the family fold. -/
theorem hcuPsiPair_family_inertia_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    [Finite ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1))]
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hθW : caseA_wComplement caseA ≤ θ.ker)
    (hθS0 : θ.comp caseA.S0.subtype ≠ 1)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    [Finite ↥(huSub data)] [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal] :
    ClassFunction.inertia (hcuPsiPair caseA θ
        (hcuSeedHom_hinv_of_wComplement_triv caseA θ hθW) lam : ClassFunction
        ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      = hInHu data ⊔ cuInHu caseA := by
  have : Fintype ↥((data.typeP.W1).subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    Fintype.ofFinite _
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  have htriv : ∀ w ∈ caseA_wComplement caseA,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
        = (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro w hw
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      MonoidHom.mem_ker.mp (hθW hw), Units.val_one]
  have hreg : ∃ x ∈ caseA.S0,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    rw [Ne, MonoidHom.ext_iff, not_forall] at hθS0
    obtain ⟨x, hx⟩ := hθS0
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] at hx
    refine ⟨x, x.2, ?_⟩
    simp only [linearIrreducibleCharacter_apply, map_one, Units.val_one, ne_eq,
      Units.val_eq_one]
    exact hx
  have hθ₀ := inertia_eq_hcuInHu caseA (caseA_wComplement_aInvariant caseA)
    (caseA_S0_sup_wComplement caseA) hreg htriv
  exact hcuPsiPair_inertia_eq_hcu caseA θ (hcuSeedHom_hinv_of_wComplement_triv caseA θ hθW) lam hθ₀

/-- **Peterfalvi (9.8.d)** (count substrate, `hS0notker` member fact).  A member `ζ_{θ,λ} =
Ind_{H·C_U(S₀)}^{HU} ψ_{θ,λ}` whose seed `θ` is *nontrivial on `S₀`* is **not** trivial on the
realized `S₀`: `realized S₀ ⊄ Ker ζ`.  If it were, then (`liesOver_mem_characterKernel`, `ζ` lying
over `ψ`) `ψ` would vanish on the realized `S₀ ⊆ H·C_U(S₀)`, i.e. `θ₀ = 1` on `S₀`
(`hcuPsiPair_apply_inclusion`, with `mk'(N)∘hInHuEquivH` surjective onto `S₀`), contradicting
`θ|_S₀ ≠ 1`.  Single-`S₀` restriction of the `H ⊄ Ker` argument `hcuZetaPair_mem_xiSet`; supplies
the
`hS0notker` input of `caseA_hcrit_of_member` (the (γ) `W₁`-injectivity). -/
theorem caseA_hcuZetaPair_realizedS0_not_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hθS0 : θ.comp caseA.S0.subtype ≠ 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    ¬ (((caseA_realizedComplement chief caseA.S0).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
          (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ) := by
  classical
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam),
      hcuZetaPair_irreducible caseA θ hinv lam hθ₀⟩ with hζdef
  have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
      (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam) := by rw [hζdef]
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ cuInHu caseA) ζ (hcuPsiPair caseA θ hinv lam) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    rw [← hcoe, OddOrder.RepresentationTheory.irreducibleCharacter_inner_eq_ite ζ ζ, if_pos rfl]
    exact one_ne_zero
  intro hsub
  apply hθS0
  have hfsurj : Function.Surjective
      ((QuotientGroup.mk' chief.N).comp (hInHuEquivH data).toMonoidHom) :=
    (QuotientGroup.mk'_surjective chief.N).comp (hInHuEquivH data).surjective
  refine MonoidHom.ext fun s => ?_
  obtain ⟨h, hhs⟩ := hfsurj (caseA.S0.subtype s)
  have hgmem : ((Subgroup.inclusion
      (le_sup_left : hInHu data ≤ hInHu data ⊔ cuInHu caseA) h :
      ↥(hInHu data ⊔ cuInHu caseA)) : ↥(huSub data))
      ∈ (((caseA_realizedComplement chief caseA.S0).subgroupOf M).subgroupOf (huSub data)) := by
    rw [Subgroup.coe_inclusion, ← Subgroup.mem_subgroupOf,
      caseA_realizedComplement_subgroupOf_hInHu_eq_comap chief caseA.S0, Subgroup.mem_comap, hhs]
    exact s.2
  have hψker := liesOver_mem_characterKernel hlo (by rw [hcoe]; exact hsub hgmem)
  have hψ1 : (hcuPsiPair caseA θ hinv lam : ClassFunction ↥(hInHu data ⊔ cuInHu caseA) ℂ)
      1 = 1 := by simp [hcuPsiPair]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    hcuPsiPair_apply_inclusion caseA θ hinv lam h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = caseA.S0.subtype s := hhs
  rw [hqeq] at hψker
  change θ (caseA.S0.subtype s) = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

/-- **Peterfalvi (9.8.d)** (count substrate, per-member irreducibility).  For a member seed `θ`
trivial on the `W₁`-orbit complement `caseA_wComplement` and nontrivial on `S₀`, the double
induction `Ind_{HU}^M (Ind_{H·C_U(S₀)}^{HU} ψ_{θ,λ})` is *irreducible*.  If `ζ = Ind ψ` were
`M`-fixed (`inertia ζ = ⊤`), then for a nontrivial `w₁ ∈ W₁` the orbit summand
`caseA_wOrbit w₁ = w₁•S₀ ≤ caseA_wComplement ≤ Ker θ`, so `(θ∘aut w₁)|_{S₀} = 1`, which for a fixed
`ζ` (`caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed`) forces `θ|_{S₀} = 1` — contradicting the
member's `θ|_{S₀} ≠ 1`; hence `inertia ζ ≠ ⊤` and `induceHU ζ` is irreducible
(`hcuZetaPair_induceHU_irreducible`).  The `W₁`-orbit analogue of the `Hpart`-based
`hcuZetaPair_induceHU_irreducible_of_nonRegular` (whose `hnonreg` on an arbitrary *carrier* summand
is not available for a `caseA_wComplement`-trivial member — the two summand systems differ). -/
theorem caseA_member_induceHU_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hθW : caseA_wComplement caseA ≤ θ.ker)
    (hθS0 : θ.comp caseA.S0.subtype ≠ 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Finite ↥(hInHu data)]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    [(hInHu data ⊔ cuInHu caseA).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cuInHu caseA) :
    IsIrreducibleCharacter (induceHU data (ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      (hcuPsiPair caseA θ hinv lam) : ClassFunction ↥(huSub data) ℂ)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  refine hcuZetaPair_induceHU_irreducible caseA θ hinv lam hθ₀ ?_
  intro hMfix
  have hlo := hcuZetaPair_liesOver_hInHu caseA θ hinv lam hθ₀
  -- a nontrivial `w₁ ∈ W₁` (as an index of the `W₁`-orbit `caseA_wOrbit`).
  obtain ⟨wg, hwgW1, hwgne⟩ :=
    (data.typeP.W1.bot_or_exists_ne_one).resolve_left data.typeP.W1_nontrivial
  set w₁ : ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    ⟨⟨wg, Subgroup.mem_sup_right hwgW1⟩, Subgroup.mem_subgroupOf.mpr hwgW1⟩ with hw₁def
  have hw₁ne : w₁ ≠ 1 := by
    intro h
    refine hwgne ?_
    have h2 : ((w₁ : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) = wg := rfl
    rw [h] at h2; simpa using h2.symm
  -- `caseA_wOrbit w₁ = w₁•S₀ ≤ caseA_wComplement ≤ Ker θ`.
  have hle : caseA_wOrbit caseA w₁ ≤ θ.ker :=
    (le_iSup₂ (f := fun w (_ : w ≠ 1) => caseA_wOrbit caseA w) w₁ hw₁ne).trans hθW
  have hwtriv : θ.comp (caseA_wOrbit caseA w₁).subtype = 1 := by
    ext s; simpa using MonoidHom.mem_ker.mp (hle s.2)
  rw [caseA_wOrbit, comp_subtype_pointwise_smul_eq_one_iff,
    caseA_theta_comp_quotient_on_S0_eq_one_iff_of_fixed caseA θ _ hlo hMfix ↑w₁] at hwtriv
  exact hθS0 hwtriv

/-- **Peterfalvi (9.8.d)** (count substrate, member seed inertia).  For a member seed `θ` trivial on
`caseA_wComplement` and nontrivial on `S₀`, the inflation `θ₀`'s `HU`-inertia is `H·C_U(S₀)`
(`inertia_eq_hcuInHu` at `W = caseA_wComplement`, `H̄ = S₀ ⊕ W`).  Deduplicates the `hθ₀` input
shared by `caseA_hcuZetaPair_realizedS0_not_subset_ker`, `caseA_member_induceHU_irreducible`, and
`hcuZetaPair_induceHU_mem_sOf` in the (9.8.d) count assembly. -/
theorem caseA_member_seed_inertia_eq [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hθW : caseA_wComplement caseA ≤ θ.ker)
    (hθS0 : θ.comp caseA.S0.subtype ≠ 1) :
    ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHu caseA := by
  have htriv : ∀ w ∈ caseA_wComplement caseA,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) w
        = (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    intro w hw
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      MonoidHom.mem_ker.mp (hθW hw), Units.val_one]
  have hreg : ∃ x ∈ caseA.S0,
      (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    rw [Ne, MonoidHom.ext_iff, not_forall] at hθS0
    obtain ⟨x, hx⟩ := hθS0
    simp only [MonoidHom.comp_apply, Subgroup.subtype_apply, MonoidHom.one_apply] at hx
    refine ⟨x, x.2, ?_⟩
    simp only [linearIrreducibleCharacter_apply, map_one, Units.val_one, ne_eq, Units.val_eq_one]
    exact hx
  exact inertia_eq_hcuInHu caseA (caseA_wComplement_aInvariant caseA)
    (caseA_S0_sup_wComplement caseA) hreg htriv

/-- **Peterfalvi (9.8)**: character-count consequences in Clifford case (a).

Faithful to Peterfalvi (9.8.b,c,d) (count-statement audit, issue 2030):
* **(b)** `𝒮(H₀)` contains exactly `p-1` *reducible* characters; each has degree `qu` and lies
  in `𝒮(H₀C)`.
* **(c)** `𝒮(H₀C)` contains an *irreducible* character of degree `qu`.
* **(d)** `𝒮(H₀U')` contains at least `((p-1)/a)·(|U|/(a|U'|))` irreducible characters of
  degree `qa`.

All `𝒮(H₀·)` sets carry the `H₀`-join (`chief.H0 ⊔ ·`): Peterfalvi's `𝒮(H₀C)`/`𝒮(H₀U')` require
`H₀C`/`H₀U'` in the kernel, not `C`/`U'` alone.  Reducibility/irreducibility is
`IsIrreducibleCharacter`.

Relocated after the (9.8.c) `H₀C` character machinery so the (b)/(c) conjuncts can cite it.  (b) =
`reducible_count_sOf_H0` (count) + `caseA_reducible_induceHU_apply_one_eq_qu` (degree) +
`reducible_mem_sOf_H0C` (membership).  (c) is `caseA_exists_irreducible_sOf_H0C`.

**(d) status (degree substrate landed, count open).**  The (9.8.d) degree-`qa` construction is the
single-factor mirror of the degree-`qu` (b)/(c) machinery: the source character `θ₁·λ` (`θ₁` a
nontrivial character of the order-`p` factor `S₀ = H₁`, `λ ∈ Irr(C_U(S₀)/U')`) induces from the
inertia subgroup `H·C_U(S₀)`, of index `[HU : H·C_U(S₀)] = a` in `HU` — established here by
`index_hcuInHu_eq_caseA_a` (`= caseA.a`, via the second/first-isomorphism chain
`index_hcuInHu_eq_relindex_cuInHu` + `index_cuInHu_subgroupOf_uInHu_eq_a`, using the `C_U(S₀)`
realization `cuSub`/`cuInHu` and its normality `hcuInHu_normal`).  The carrier's `a` is now pinned
to
this genuine index `|Ū₁| = |U:C_U(S₀)|` (`CliffordCaseAData.a_eq_card_restrictAut_range`) — without
that pin the degree-`qa` claim referenced a free field and was not honestly provable.

**Inertia lift (fully landed).**  The *full* inertia equality `I_{HU}(θ₁₀) = H·C_U(S₀)` is now
proven for a source character `θ₁` supported on `S₀`.  Both directions:
* *hard* `I(θ₁₀) ⊓ U ≤ C_U(S₀)` — `inertia_inf_uInHu_le_cuInHu` (from `θ₁` faithful on the single
  summand `S₀`), whose algebraic heart is `chiefFactor_caseA_char_inertia_single`
  (`aInvariantRestrictAut S₀ = 1`) via `mulAut_eq_id_on_of_fixes_ne_one_on_prime`;
* *easy* `C_U(S₀) ≤ I(θ₁₀)` — `cuInHu_le_inertia_of_complement_triv`, whose algebraic heart is the
  new `mulAut_fixes_char_of_id_on_summand_triv_complement`: a `C_U(S₀)`-element acts trivially on
  `S₀` and preserves the `U`-invariant complement `W`, so the linear `θ₁` (trivial on `W`) is fixed.
The `S₀`-summand decomposition `H̄ = S₀ ⊕ W` is `chiefFactor_caseA_S0_complement` (operator Maschke,
`|U| ⟂ |H̄|`); the source character `θ₁ ∈ Irr(H̄/W)` (nontrivial on `S₀`, trivial on `W`) is
`exists_source_char_caseA`.  These assemble into `inertia_eq_hcuInHu` and the one-shot existence
`exists_source_char_inertia_eq_hcuInHu_caseA`: there is a `θ₁` (nontrivial on `S₀`) whose
inflation's
`HU`-inertia is exactly `H·C_U(S₀)`, of index `[HU:H·C_U(S₀)] = a` (`index_hcuInHu_eq_caseA_a`),
giving source degree `a` and `M`-induction degree `qa`.

**Pair-character substrate (landed).**  The `C`-factor of the (9.8.d) pair character `θ₁·λ` is now
built as `hcuLambdaHom` (`H·C_U(S₀) →* ℂˣ`, the `λ`-lift of `λ : C_U(S₀) →* ℂˣ` through the
`H`-quotient `(C_U(S₀)·H)/H ≅ C_U(S₀)`), with `hcuLambdaHom_eq_one_of_mem_hInHu` (kills `H`) and
`hcuLambdaHom_inclusion` (restricts to `λ`).  Its well-definedness rests on the new trivial
intersection `hInHu_inf_cuInHu_eq_bot` (`H ⊓ C_U(S₀) = ⊥`, from `H ⊓ U = ⊥`) — the single-factor
analog of `hInHu_inf_cInHu_eq_bot`.  These directly mirror the (9.9.c) `hcLambdaHom` channel
(rewired `cInHu → cuInHu`), and are honest reusable substrate for the pair hom.

**Source character + degree (fully landed).**  The pair hom `θ₁·λ` on `H·C_U(S₀)` is built: the
`θ₀`-extension `hcuThetaHom` (via `SemidirectProduct.lift`, the internal
`H·C_U(S₀) ≃* H ⋊ C_U(S₀)` from `hInHu_inf_cuInHu_eq_bot` + `sup = ⊤`, with the `C`-invariance
`cuInHu_le_inertia_of_complement_triv` discharging `lift`'s compatibility) times `hcuLambdaHom λ`,
packaged as `hcuPairHom`/`hcuPsiPair`.  Its `HU`-induction `ζ_{θ₁,λ}` is irreducible of degree `a`
(`hcuZetaPair_irreducible` via `inertia_eq_hcuInHu` +
`isIrreducibleCharacter_induce_of_inertia_eq`),
and `Ind_{HU}^M ζ` has degree `qa` (`hcuZetaPair_induceHU_apply_one`); the one-shot existence is
`caseA_exists_irreducible_source_degree_qa`.

**Group-theoretic prerequisites (landed).**  `U' ≤ C_U(S₀)` — `uprimeSub_le_cuSub`
(`U' = [U,U] ≤ C = C_U(H̄) ≤ C_U(S₀)`, via `uprimeSub_le_cSub` + `cSub_le_cuSub`), realized as
`uprimeSub_subgroupOf_le_cuInHu`.  `H₀U' ◁ M` — `chiefFactor_H0supUprime_subgroupOf_normal`
(`U W₁ ≤ N(H₀) ⊓ N(U')` and `H ≤ N(H₀) ⊓ N(U')`, the latter because `H` *centralizes* `U'`
via `typeP_H_le_normalizer_uprimeSub`), realized as `realizedH0supUprime_normal_huSub`.

**(iii) membership — LANDED.**  `Ind_{HU}^M ζ_{θ₁,λ} ∈ 𝒮(H₀U')` is now proven, for any `θ` and any
`λ` trivial on `U'`, as `hcuZetaPair_induceHU_mem_sOf` (via `hcuZetaPair_mem_xiOf` =
`hcuZetaPair_mem_xiSet` [`H ⊄ Ker`, `hcuPsiPair_apply_inclusion` + `liesOver_mem_characterKernel`] +
`hcuZetaPair_H0supUprime_subset_ker` [`H₀U' ⊆ Ker`]).  The kernel step is
`subsetCharacterKernel_induce_of_subgroupOf` (`[A.Normal]` = `realizedH0supUprime_normal_huSub`)
with
`hcuPairHom_eq_one_of_mem_realizedH0supUprime`: decompose a realized-`H₀U'` element as `h₀·u'`
(`realizedH0supUprime_eq_realizedH0_sup_uprimeInHu`) — the `θ`-extension `hcuThetaHom` kills `h₀`
(`hcuSeedHom_eq_one_of_mem_realizedH0`, since `H₀ = N.comap hInHuEquivH`) and the complement `u'`
(`hcuThetaHom_inclusion_cuInHu`); the `λ`-lift kills `h₀ ∈ H` (`hcuLambdaHom_eq_one_of_mem_hInHu`)
and restricts to `λ u' = 1` on `u' ∈ U'`.

**(iv) `Ind_{HU}^M ζ`-irreducibility — LANDED** (unconditional).  The `hIM`
(`I_M(ζ) ≠ M`) is now discharged: the (9.8.d) source `θ₁` is built *non-regular*
(`exists_source_char_hom_caseA_nonRegular` — trivial on a Clifford summand `Hpart j₁ ≤ W` where
`W = ⨆_{j≠j₀} Hpart j` is the summand-join complement `caseA_exists_summand_join_complement_S0`,
itself
from the support witness `caseA_exists_index_S0_not_le_biSup_compl`
`∃ j₀, ¬ S₀ ≤ ⨆_{j≠j₀} Hpart j`).
Since `ζ` lies over `θ₀` at `hInHu` (`hcuZetaPair_liesOver_hInHu`, lies-over descent
`liesOver_of_liesOver_liesOver_subgroupOf`), an `M`-fixed `ζ` would force `θ₁` *regular*
(`caseA_reducible_theta_regular`) — nontrivial on *every* summand — contradicting non-regularity at
`j₁`; hence `I_M(ζ)≠M` (`hcuZetaPair_inertia_ne_top`) and `Ind_{HU}^M ζ` is irreducible with no
hypothesis (`hcuZetaPair_induceHU_irreducible_of_nonRegular`,
`caseA_exists_irreducible_source_degree_qa_induceHU_irreducible`). This is cleaner than the
full-regular
`clifford_caseA_exists_char_inertia_hc_not_fixed` (no per-summand nontriviality needed): the single
summand `S₀ = H₁` supporting `θ₁ ∈ Irr(H̄/(H₂…H_q))` is moved off itself by the `W₁`-transitive
summand
permutation.

**(v) count — LANDED** (no `sorry`).  `𝒮(H₀U')` contains `≥ ((p-1)/a)·(|U|/(a|U'|))` irreducibles
of degree `qa`.  The assembly (in `caseA_character_counts`'s (d) branch):

* **family** `T := (Dθ ×ˢ Dλ).image ψ_{·,·} ⊆ Irr(H·C_U(S₀))`, where `Dθ = {θ | W ≤ Ker θ ∧
  θ|_{S₀} ≠ 1}` (`W = caseA_wComplement`) and `Dλ = {λ | U'-realized ≤ Ker λ}`.  `|T| = |Dθ|·|Dλ| =
  (p-1)·[C_U(S₀):U']` — injectivity `hcuPsiPair_injective_pair`,
  numerators `card_theta_triv_W_nontriv_S0`
  (`= p-1`) and `card_lambda_triv_uprime` (`= [C_U(S₀):U']`).
* **first induction (`/a`)** — the *hypothesis-light* orbit count `card_image_induce_ge_div`
  (`OrbitOnIrr`) gives `|image₁| ≥ |T|/[HU:H·C_U(S₀)] = |T|/a` from *only* the per-member inertia
  `= H·C_U(S₀)` (`hcuPsiPair_family_inertia_eq`, index `a` = `index_hcuInHu_eq_caseA_a`).  A lower
  bound suffices, so the family need **not** be conjugation-closed — this drops the Coq
  `Mtheta`-conjBy-descent *and* the intrinsic-`T` `def_Itheta` surjectivity route (the surjectivity
  lemma `exists_hcuPsiPair_eq_of_linear_realizedH0_ker` and reverse kernel-translations are landed
  substrate but unused by the final count).
* **second induction (γ, injective)** — `induceHU` is injective on `image₁` via
  `induceHU_inj_of_conj_mem_huSub` + `caseA_hcrit_of_member` (its `hS0notker` =
  `caseA_hcuZetaPair_realizedS0_not_subset_ker`; its `hkerW₂` =
  `hcuZetaPair_summandComplement_subset_ker`
  at `W = caseA_wComplement`; the (9.7.a) `horbit` is the reconstructed `caseA_wOrbit_horbit`).
* **target membership** — each `induceHU ζ` is in `𝒮(H₀U')` (`hcuZetaPair_induceHU_mem_sOf`),
  irreducible (`caseA_member_induceHU_irreducible`, the `W₁`-orbit non-regularity), of degree `qa`
  (`hcuZetaPair_induceHU_apply_one`).
* **assembly** — `ncard ≥ |induceHU '' image₁| = |image₁| ≥ |T|/a = (p-1)·[C_U(S₀):U']/a ≥
  ((p-1)/a)·[C_U(S₀):U']` (`Set.ncard_le_ncard` + `Set.ncard_coe_finset`
  + `Finset.card_image_of_injOn`;
  floor step `Nat.le_div_iff_mul_le` + `Nat.div_mul_le_self`), and `((p-1)/a)·(|U|/(a|U'|)) =
  ((p-1)/a)·[C_U(S₀):U']` by `card_U_div_a_mul_card_Uprime_eq_relIndex`.  Mirrors the Coq
  `typeP_nonGalois_characters` (9.8.d) `Mtheta`/`Xtheta`/`injXtheta` (`PFsection9.v` L1112-1254). -/
theorem caseA_character_counts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    {φ ∈ chars.SOf chief.H0 | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 ∧
      (∀ φ ∈ chars.SOf chief.H0, ¬ IsIrreducibleCharacter φ →
        φ 1 = ((data.q * chars.u : ℕ) : ℂ) ∧ φ ∈ chars.SOf (chief.H0 ⊔ chars.C)) ∧
      (∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.C), IsIrreducibleCharacter χ ∧
        χ 1 = ((data.q * chars.u : ℕ) : ℂ)) ∧
      ((chief.p - 1) / caseA.a) * (Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime)) ≤
        {χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard := by
  -- (b) count = §9↔§6 bijection `reducible_count_sOf_H0`; degree = caseA step-5 assembly;
  -- membership
  -- = case-agnostic cardinality argument `reducible_mem_sOf_H0C`.
  refine ⟨reducible_count_sOf_H0 hG chief, fun φ hφ hred =>
    ⟨caseA_reducible_induceHU_apply_one_eq_qu caseA hG φ hφ hred,
      reducible_mem_sOf_H0C hG chars φ hφ hred⟩, ?_, ?_⟩
  · -- (c) 9.8.c: an irreducible `𝒮(H₀C)`-member of degree `qu` (parity dichotomy on `Xθ`/`Xmu`).
    let : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
    let : Fintype ↥(hInHu data) := Fintype.ofFinite _
    let : Fintype ↥(huSub data) := Fintype.ofFinite _
    let : Fintype ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) := Fintype.ofFinite _
    let : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    let : Invertible
        (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    have : (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).Normal := hcInHu_realized_normal chief
    exact caseA_exists_irreducible_sOf_H0C caseA hG
  · -- (d) 9.8.d: `𝒮(H₀U')` has `≥ ((p-1)/a)·[C_U(S₀):U']` irreducibles of degree `qa`.
    classical
    have : (hInHu data ⊔ cuInHu caseA).Normal := hcuInHu_normal caseA
    let : Fintype ↥(huSub data) := Fintype.ofFinite _
    let : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
    let : Fintype ↥(hInHu data) := Fintype.ofFinite _
    let : Fintype ((↥data.H ⧸ chief.N) →* ℂˣ) := Fintype.ofFinite _
    let : Fintype (↥(cuInHu caseA) →* ℂˣ) := Fintype.ofFinite _
    let : Fintype ↥M := Fintype.ofFinite _
    let : Fintype ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) := Fintype.ofFinite _
    let : Fintype (IrreducibleCharacter ↥(huSub data)) := Fintype.ofFinite _
    let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    let : Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    let : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
      invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
    let : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
    have hWnorm : (caseA_wComplement caseA).Normal := Subgroup.normal_of_isMulCommutative _
    have ha_pos : 0 < caseA.a := by
      rw [← index_hcuInHu_eq_caseA_a caseA]
      exact Nat.pos_of_ne_zero fun h0 => by
        have hmc := (hInHu data ⊔ cuInHu caseA).index_mul_card
        rw [h0, zero_mul] at hmc
        exact (Nat.card_pos (α := ↥(huSub data))).ne' hmc.symm
    -- domain finsets `Dθ`, `Dlam` and the pair family `T ⊆ Irr(H·C_U(S₀))`.
    set Dθ := Finset.univ.filter (fun θ : (↥data.H ⧸ chief.N) →* ℂˣ =>
      caseA_wComplement caseA ≤ θ.ker ∧ θ.comp caseA.S0.subtype ≠ 1) with hDθdef
    set Dlam := Finset.univ.filter (fun lam : ↥(cuInHu caseA) →* ℂˣ =>
      (((uprimeSub data).subgroupOf M).subgroupOf (huSub data)).subgroupOf (cuInHu caseA)
        ≤ lam.ker) with hDlamdef
    have hmemDθ : ∀ θ ∈ Dθ, caseA_wComplement caseA ≤ θ.ker ∧ θ.comp caseA.S0.subtype ≠ 1 := by
      intro θ hθ; rw [hDθdef, Finset.mem_filter] at hθ; exact hθ.2
    have hmemDlam : ∀ lam ∈ Dlam,
        (((uprimeSub data).subgroupOf M).subgroupOf (huSub data)).subgroupOf (cuInHu caseA)
          ≤ lam.ker := by
      intro lam hlam; rw [hDlamdef, Finset.mem_filter] at hlam; exact hlam.2
    set pmap : {θ // θ ∈ Dθ} × (↥(cuInHu caseA) →* ℂˣ) →
        IrreducibleCharacter ↥(hInHu data ⊔ cuInHu caseA) :=
      fun p => hcuPsiPair caseA p.1.1
        (hcuSeedHom_hinv_of_wComplement_triv caseA p.1.1 (hmemDθ p.1.1 p.1.2).1) p.2 with hpmap
    set T := (Dθ.attach ×ˢ Dlam).image pmap with hTdef
    -- `|T| = |Dθ|·|Dlam| = (p-1)·[C_U(S₀):U']`.
    have hDθcard : Dθ.card = chief.p - 1 := by
      rw [hDθdef]
      exact card_theta_triv_W_nontriv_S0 caseA (caseA_S0_inf_wComplement caseA)
        (caseA_S0_sup_wComplement caseA) (caseA_S0_card caseA)
    have hDlamcard : Dlam.card = (uprimeSub data).relIndex (cuSub caseA) := by
      rw [hDlamdef, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact card_lambda_triv_uprime caseA
    have hinjmap : Set.InjOn pmap ↑(Dθ.attach ×ˢ Dlam) := by
      intro p _ q _ heq
      simp only [hpmap] at heq
      obtain ⟨hθeq, hlameq⟩ := hcuPsiPair_injective_pair caseA heq
      exact Prod.ext (Subtype.ext hθeq) hlameq
    have hTcard : T.card = (chief.p - 1) * (uprimeSub data).relIndex (cuSub caseA) := by
      rw [hTdef, Finset.card_image_of_injOn hinjmap, Finset.card_product, Finset.card_attach,
        hDθcard, hDlamcard]
    -- each member `ψ_{θ,λ}` has inertia `H·C_U(S₀)`.
    have hinertia : ∀ ψ ∈ T, IrreducibleCharacter.inertia (G := ↥(huSub data))
        (H := hInHu data ⊔ cuInHu caseA) ψ = hInHu data ⊔ cuInHu caseA := by
      intro ψ hψ
      rw [hTdef, Finset.mem_image] at hψ
      obtain ⟨p, _, rfl⟩ := hψ
      exact hcuPsiPair_family_inertia_eq caseA p.1.1 (hmemDθ p.1.1 p.1.2).1
        (hmemDθ p.1.1 p.1.2).2 p.2
    -- the ζ-image and the hypothesis-light orbit-count `≥` engine.
    set I1 := T.image (fun ψ => ClassFunction.induce (hInHu data ⊔ cuInHu caseA)
      ψ.toClassFunction) with hI1def
    have hengine : T.card / (hInHu data ⊔ cuInHu caseA).index ≤ I1.card :=
      OddOrder.RepresentationTheory.card_image_induce_ge_div T hinertia
    -- (γ) `induceHU` injective on `I1`.
    have hinjHU : Set.InjOn (induceHU data) ↑I1 := by
      intro ζ₁ hζ₁ ζ₂ hζ₂ heq
      rw [Finset.mem_coe, hI1def, Finset.mem_image] at hζ₁ hζ₂
      obtain ⟨ψ₁, hψ₁T, rfl⟩ := hζ₁
      obtain ⟨ψ₂, hψ₂T, rfl⟩ := hζ₂
      rw [hTdef, Finset.mem_image] at hψ₁T hψ₂T
      obtain ⟨p₁, _, rfl⟩ := hψ₁T
      obtain ⟨p₂, _, rfl⟩ := hψ₂T
      have hθ₀₁ := caseA_member_seed_inertia_eq caseA p₁.1.1 (hmemDθ p₁.1.1 p₁.1.2).1
        (hmemDθ p₁.1.1 p₁.1.2).2
      have hθ₀₂ := caseA_member_seed_inertia_eq caseA p₂.1.1 (hmemDθ p₂.1.1 p₂.1.2).1
        (hmemDθ p₂.1.1 p₂.1.2).2
      set χ₁ : IrreducibleCharacter ↥(huSub data) :=
        ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (pmap p₁).toClassFunction,
          hcuZetaPair_irreducible caseA p₁.1.1 _ p₁.2 hθ₀₁⟩ with hχ₁def
      set χ₂ : IrreducibleCharacter ↥(huSub data) :=
        ⟨ClassFunction.induce (hInHu data ⊔ cuInHu caseA) (pmap p₂).toClassFunction,
          hcuZetaPair_irreducible caseA p₂.1.1 _ p₂.2 hθ₀₂⟩ with hχ₂def
      have hcrit := caseA_hcrit_of_member data caseA (ζ₁ := χ₁) (ζ₂ := χ₂)
        (caseA_hcuZetaPair_realizedS0_not_subset_ker caseA p₁.1.1 _ p₁.2
          (hmemDθ p₁.1.1 p₁.1.2).2 hθ₀₁)
        (hcuZetaPair_summandComplement_subset_ker caseA p₂.1.1 _ p₂.2
          (caseA_wComplement_aInvariant caseA)
          (fun w hw => MonoidHom.mem_ker.mp ((hmemDθ p₂.1.1 p₂.1.2).1 hw)))
      exact congrArg IrreducibleCharacter.toClassFunction
        (induceHU_inj_of_conj_mem_huSub data hcrit heq)
    -- each `induceHU ζ` is in the target set (member ∈ 𝒮(H₀U'), irreducible, degree `qa`).
    have himgsub : (↑(I1.image (induceHU data)) : Set (ClassFunction ↥M ℂ)) ⊆
        {χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)} := by
      intro φ hφ
      rw [Finset.mem_coe, Finset.mem_image] at hφ
      obtain ⟨ζ, hζI1, rfl⟩ := hφ
      rw [hI1def, Finset.mem_image] at hζI1
      obtain ⟨ψ, hψT, rfl⟩ := hζI1
      rw [hTdef, Finset.mem_image] at hψT
      obtain ⟨p, hp, rfl⟩ := hψT
      have hθ₀ := caseA_member_seed_inertia_eq caseA p.1.1 (hmemDθ p.1.1 p.1.2).1
        (hmemDθ p.1.1 p.1.2).2
      have hθnt : p.1.1 ≠ 1 :=
        fun h => (hmemDθ p.1.1 p.1.2).2 (by rw [h]; exact MonoidHom.one_comp _)
      refine ⟨?_, ?_, ?_⟩
      · exact hcuZetaPair_induceHU_mem_sOf caseA p.1.1 hθnt _ p.2
          (fun c hc => MonoidHom.mem_ker.mp
            ((hmemDlam p.2 (Finset.mem_product.mp hp).2) (Subgroup.mem_subgroupOf.mpr hc))) hθ₀
      · exact caseA_member_induceHU_irreducible caseA p.1.1 _ p.2 (hmemDθ p.1.1 p.1.2).1
          (hmemDθ p.1.1 p.1.2).2 hθ₀
      · exact hcuZetaPair_induceHU_apply_one caseA p.1.1 _ p.2
    -- the target set is finite (`⊆ 𝒮 = induceHU '' 𝒳`).
    have htargetFin : {χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime) |
        IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.Finite := by
      refine Set.Finite.subset ((Set.toFinite (xiOf data (chief.H0 ⊔ chars.Uprime))).image
        (fun χ : IrreducibleCharacter ↥(huSub data) =>
          induceHU data (χ : ClassFunction ↥(huSub data) ℂ))) ?_
      intro φ hφ
      obtain ⟨hφS, -⟩ := hφ
      rw [Section11CharacterData.SOf_eq, mem_sOf] at hφS
      obtain ⟨χ, hχ, rfl⟩ := hφS
      exact ⟨χ, hχ, rfl⟩
    -- arithmetic: `((p-1)/a)·[C:U'] ≤ (p-1)·[C:U']/a = |T|/a ≤ |I1| = |induceHU '' I1| ≤ ncard`.
    have harith : Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime)
        = (uprimeSub data).relIndex (cuSub caseA) := card_U_div_a_mul_card_Uprime_eq_relIndex caseA
    calc ((chief.p - 1) / caseA.a)
            * (Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime))
        = ((chief.p - 1) / caseA.a) * ((uprimeSub data).relIndex (cuSub caseA)) := by rw [harith]
      _ ≤ ((chief.p - 1) * (uprimeSub data).relIndex (cuSub caseA)) / caseA.a := by
          rw [Nat.le_div_iff_mul_le ha_pos]
          calc ((chief.p - 1) / caseA.a * (uprimeSub data).relIndex (cuSub caseA)) * caseA.a
              = (chief.p - 1) / caseA.a * caseA.a
                  * (uprimeSub data).relIndex (cuSub caseA) := by ring
            _ ≤ (chief.p - 1) * (uprimeSub data).relIndex (cuSub caseA) :=
                Nat.mul_le_mul_right _ (Nat.div_mul_le_self _ _)
      _ = T.card / (hInHu data ⊔ cuInHu caseA).index := by
          rw [hTcard, index_hcuInHu_eq_caseA_a]
      _ ≤ I1.card := hengine
      _ = (I1.image (induceHU data)).card := (Finset.card_image_of_injOn hinjHU).symm
      _ ≤ {χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime) |
            IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard := by
          rw [← Set.ncard_coe_finset (I1.image (induceHU data))]
          exact Set.ncard_le_ncard himgsub htargetFin

/-- **Peterfalvi (9.9)**: character-count consequences in Clifford case (b).

Faithful to Peterfalvi (9.9.a,b,c) (count-statement audit, issue 2030):
* **(a)** every member of `𝒮(H₀C')` has degree `qu` (each `χ ∈ 𝒳(H₀C')` has `χ(1)=u`, so its
  induction `Ind_{HU}^M χ` has degree `[M:HU]·u = qu`).
* **(b)** `𝒮(H₀)` contains exactly `p-1` reducible characters; each has degree `qu` and lies in
  `𝒮(H₀C)`.
* **(c)** if `𝒮(H₀C')` contains *no irreducible character*, then `C = 1` and `u = (p^q-1)/(p-1)`.

`𝒮(H₀C')`/`𝒮(H₀C)` carry the `H₀`-join (`chief.H0 ⊔ chars.Cprime` / `chief.H0 ⊔ chars.C`).  The
former vacuous `u ∣ qu` (always true) and the false `(𝒮(H₀)).ncard = p-1` (`𝒮(H₀)` also has
irreducibles) are replaced by the genuine (9.9.a)/(9.9.b) statements; the (9.9.c) trigger is
"contains no irreducible" (not `ncard = 0`: in the exceptional case `𝒮(H₀C') = 𝒮(H₀)` is
nonempty).  The `C = ⊥` half of (c) is the pair-character argument
`caseB_no_irreducible_forces_C_bot`; the `u`-formula half is the `C = 1` Frobenius count. -/
theorem caseB_character_counts [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars) :
    (∀ φ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), φ 1 = ((data.q * chars.u : ℕ) : ℂ)) ∧
      {φ ∈ chars.SOf chief.H0 | ¬ IsIrreducibleCharacter φ}.ncard = chief.p - 1 ∧
      (∀ φ ∈ chars.SOf chief.H0, ¬ IsIrreducibleCharacter φ →
        φ 1 = ((data.q * chars.u : ℕ) : ℂ) ∧ φ ∈ chars.SOf (chief.H0 ⊔ chars.C)) ∧
      ((¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ) →
        chars.C = ⊥ ∧ chars.u = (chief.p ^ data.q - 1) / (chief.p - 1)) := by
  -- (9.9.a) is the proven `caseB_degree_qu`; (9.9.b) is the §9↔§6 bijection
  -- `reducible_count_sOf_H0`;
  -- (9.9.c): `C = ⊥` is the pair-character argument; the `u`-count remains.
  refine ⟨caseB_degree_qu hG chars caseB, ?_, ?_, ?_⟩
  · exact reducible_count_sOf_H0 hG chief
  · intro φ hφ hred
    have hmem := reducible_mem_sOf_H0C hG chars φ hφ hred
    exact ⟨forall_mem_sOf_H0C_apply_one_eq_qu hG chars caseB φ hmem, hmem⟩
  · intro hno
    exact ⟨caseB_no_irreducible_forces_C_bot hG chars caseB hno,
      caseB_no_irreducible_u_formula hG chars caseB hno⟩

/-- **A Frobenius-group structure is independent of the choice of complement**: conjugating the
complement preserves it (the kernel `N`, being normal, is fixed by conjugation).  Complements of a
normal Hall subgroup are all conjugate (Schur–Zassenhaus,
`Subgroup.IsComplement'.exists_conj_of_coprime`), so Frobenius-ness transports between any two of
them — the bridge from the type-`F` complement witness to the type-`P` complement `U`. -/
theorem _root_.OddOrder.Isaacs.Ch06.IsFrobeniusGroup.conj_complement {G' : Type*} [Group G']
    {N A : Subgroup G'} (h : OddOrder.Isaacs.Ch06.IsFrobeniusGroup G' N A) (n : G') :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup G' N (A.map (MulAut.conj n).toMonoidHom) := by
  have := h.isNormal
  refine ⟨h.isNormal, Subgroup.SchurZassenhausConj.isComplement'_conj h.isComplement n,
    h.ne_bot_kernel, ?_, ?_⟩
  · intro hbot
    exact h.ne_bot_complement ((Subgroup.map_eq_bot_iff_of_injective A
      (MulAut.conj n).injective).mp hbot)
  · intro a haA' hane m hmN hmne hconj
    obtain ⟨a₀, ha₀A, rfl⟩ := Subgroup.mem_map.mp haA'
    have ha₀ne : a₀ ≠ 1 := by
      rintro rfl; exact hane (by simp)
    have hm'N : n⁻¹ * m * n ∈ N := by
      simpa [mul_assoc] using h.isNormal.conj_mem m hmN n⁻¹
    have hm'ne : n⁻¹ * m * n ≠ 1 := by
      intro h1
      exact hmne (by
        have := congrArg (fun x => n * x * n⁻¹) h1
        simpa [mul_assoc] using this)
    refine h.conj_frobenius a₀ ha₀A ha₀ne _ hm'N hm'ne ?_
    have hc : (MulAut.conj n a₀) * m * (MulAut.conj n a₀)⁻¹ = m := hconj
    rw [MulAut.conj_apply] at hc
    -- `(n a₀ n⁻¹) m (n a₀ n⁻¹)⁻¹ = m  ⟹  a₀ (n⁻¹ m n) a₀⁻¹ = n⁻¹ m n`
    have := congrArg (fun x => n⁻¹ * x * n) hc
    simpa [mul_assoc] using this

/-- **Peterfalvi (9.10)**: in the exceptional case where `𝒮(H₀C')` contains no irreducible
character of degree `qu`, the quotient semidirect product is Frobenius; in type II the full `H U`
subgroup is Frobenius with kernel `H`, and `u = (p^q-1)/(p-1)`.

The trigger set is `𝒮(H₀C')` (`chief.H0 ⊔ chars.Cprime`) — the `H₀C'` join, not `C` alone
(count-statement audit, issue 2030); the missing character is required *irreducible* of degree `qu`
(matching the negation of the (9.8.c)/(9.9) existence).  The degree condition is redundant given
case (b) — every `𝒮(H₀C')`-member has degree `qu` (`caseB_degree_qu`) — so the trigger reduces
to the (9.9.c) one and the `u`-formula conjunct is `caseB_no_irreducible_u_formula`.

The first Frobenius conjunct is now the **genuine** `H̄ ⋊ Ū`-Frobenius content — every nontrivial
`Ū`-action `uActionHom g` acts fixed-point-freely on the chief factor `H̄ = H/H₀`
(`chiefFactor_caseB_action_fpf`, from `caseB.actsIrreducibly`), replacing the former opaque
`quotientSemidirectFrobenius : Prop` field (de-scaffold, issues 1012/2035).  The remaining type-II
`HU`-Frobenius clause (`[S,S]` Frobenius with kernel `S_F`, Peterfalvi (10.7)) is the genuine
character-theoretic Frobenius criterion, gated on `H₀ = 1` ((11.7) ← (10.8)); it is **proved
here** (`caseB_no_irreducible_forces_C_bot` → `U` cyclic → `S10.typeF_frobenius_of_card_eq_exponent`
→ Schur-Zassenhaus conjugacy), so all three conjuncts are discharged and the file is sorry-free. -/
theorem exceptional_case_frobenius_realization [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseB : CliffordCaseBData chars)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
        IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * chars.u : ℕ) : ℂ)) :
    (∀ g : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
        uActionHom data chief g ≠ 1 →
          MonoidHom.FixedPointFree (uActionHom data chief g)) ∧
      chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) ∧
      IsCyclic ↥data.typeP.U ∧
      (IsTypeII M →
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(data.H ⊔ data.U)
          (data.H.subgroupOf (data.H ⊔ data.U))
          (data.U.subgroupOf (data.H ⊔ data.U))) := by
  have hno' : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime), IsIrreducibleCharacter χ := by
    rintro ⟨χ, hmem, hirr⟩
    exact hno ⟨χ, hmem, hirr, caseB_degree_qu hG chars caseB χ hmem⟩
  -- `C = ⊥` in the exceptional case, hence `uActionHom` is injective and `U ≅ Ū` is cyclic
  -- (Singer).  The book states this cyclicity unconditionally in (9.10), so it is hoisted out
  -- of the type-II branch (which also consumes it).
  have hCbot : cSub data chief = ⊥ := caseB_no_irreducible_forces_C_bot hG chars caseB hno'
  have hker : (uActionHom data chief).ker = ⊥ := by
    have h1 : ((uActionHom data chief).ker.map
        (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype = ⊥ := hCbot
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _),
      Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)] at h1
  have hUcyc : IsCyclic ↥data.typeP.U := by
    have hUbar := caseB.Ubar_cyclic
    have hinj : Function.Injective (uActionHom data chief) :=
      (uActionHom data chief).ker_eq_bot_iff.mp hker
    have : IsCyclic ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
      isCyclic_of_surjective (MonoidHom.ofInjective hinj).symm.toMonoidHom
        (MonoidHom.ofInjective hinj).symm.surjective
    exact isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe
        (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).surjective
  refine ⟨fun g hg => chiefFactor_caseB_action_fpf chief caseB.actsIrreducibly g hg,
    caseB_no_irreducible_u_formula hG chars caseB hno', hUcyc, ?_⟩
  -- **Type-II `HU`-Frobenius** (Coq `typeP_reducible_core_cases`, right branch): the exceptional
  -- case forces `C = ⊥` (`caseB_no_irreducible_forces_C_bot`), so `U ≅ Ū` is cyclic (Singer);
  -- a cyclic complement collapses the type-F Frobenius `H ⊔ U₀` to the full `H ⊔ U`
  -- (`typeF_frobenius_of_card_eq_exponent`), transported to the type-`P` complement `U` by
  -- Schur–Zassenhaus conjugacy.
  intro hTypeII
  classical
  -- `C = ⊥`, hence `uActionHom` is injective and `U ≅ Ū` is cyclic.
  -- The type-II type-F structure of `M' = [M,M]`, with `tf.H = H` (both the Fitting kernel).
  obtain ⟨td⟩ := hTypeII
  obtain ⟨tf⟩ := td.derived_typeF
  have htfH : tf.H = data.typeP.H := by
    rw [tf.H_eq, td.derived_fitting_eq, td.typeP.H_eq, ← data.typeP.H_eq]
  -- Schur–Zassenhaus: the type-F complement `tf.U` and the type-`P` complement `U` of `H` in `M'`
  -- are conjugate.
  have hHnormal : ((data.typeP.H).subgroupOf (derivedInG M)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer data.typeP.H_le).mpr ?_
    have hn := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M
    rw [← data.typeP.H_eq] at hn
    exact (derivedInG_le_self M).trans hn
  have hNcard : Nat.card ↥((data.typeP.H).subgroupOf (derivedInG M))
      = Nat.card ↥data.typeP.H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.H_le).toEquiv
  have hNidx : ((data.typeP.H).subgroupOf (derivedInG M)).index = Nat.card ↥data.typeP.U := by
    rw [data.typeP.derived_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.U_le).toEquiv]
  have hCopHU : Nat.Coprime (Nat.card ↥data.typeP.H) (Nat.card ↥data.typeP.U) :=
    (typeP_coprime_H_uW1 data.typeP data.nontrivial.1).coprime_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left)
  have hHsolv : Group.IsSolvable ↥((data.typeP.H).subgroupOf (derivedInG M)) := by
    have : Group.IsNilpotent ↥data.typeP.H := by
      rw [data.typeP.H_eq]
      exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isNilpotent M
    have : Group.IsSolvable ↥data.typeP.H := IsNilpotent.to_isSolvable
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.subgroupOfEquivOfLe data.typeP.H_le).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe data.typeP.H_le).symm.surjective
  obtain ⟨nn, _hnnH, hnnconj⟩ := Subgroup.IsComplement'.exists_conj_of_coprime
    (by rw [hNcard, hNidx]; exact hCopHU) (Or.inl hHsolv)
    (htfH ▸ tf.complement) data.typeP.derived_complement
  -- `tf.U` is cyclic (conjugate to the cyclic `U`), so `|tf.U| = exp tf.U`.
  have htfUsubCyc : IsCyclic ↥((tf.U).subgroupOf (derivedInG M)) := by
    have e := Subgroup.equivMapOfInjective ((tf.U).subgroupOf (derivedInG M))
      (MulAut.conj nn).toMonoidHom (MulAut.conj nn).injective
    rw [hnnconj] at e
    have : IsCyclic ↥((data.typeP.U).subgroupOf (derivedInG M)) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe data.typeP.U_le).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe data.typeP.U_le).symm.surjective
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  have htfUcyc : IsCyclic ↥tf.U :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe tf.U_le).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe tf.U_le).surjective
  -- Collapse the type-F Frobenius to the full complement and transport to `U`.
  have hfrobM' := OddOrder.Peterfalvi.S10.typeF_frobenius_of_card_eq_exponent tf
    IsCyclic.exponent_eq_card.symm
  rw [htfH] at hfrobM'
  have hfrob2 := hfrobM'.conj_complement nn
  rw [hnnconj] at hfrob2
  -- Rewrite the ambient `M' = H ⊔ U`.
  have hM'eq : derivedInG M = data.H ⊔ data.U := by
    change derivedInG M = data.typeP.H ⊔ data.typeP.U
    rw [data.typeP.H_eq]
    exact data.typeP.derivedInG_eq_fitting_sup_U
  rw [← hM'eq]
  exact hfrob2

/-- **Peterfalvi (9.10)** (trigger form — the book's own statement).

Identical to `exceptional_case_frobenius_realization` except that the Clifford case-(b)
carrier is **derived** rather than assumed: the exceptional trigger `hno` alone selects
case (b) of the (9.7) dichotomy.

Indeed, in case (a) the count (9.8.c) (`caseA_character_counts`, third conjunct) produces an
irreducible member of `𝒮(H₀C)` of degree `q·u`; since `C′ ≤ C` (`Cprime_le_C`) and `𝒮` is
antitone (`sOf_antitone`), that member also lies in `𝒮(H₀C′)` — contradicting `hno`.  So the
dichotomy collapses to case (b) and `exceptional_case_frobenius_realization` applies.

This is what removes the last specialization from (9.10): the case dispatch used to be done
inline at the consumer (`S12_TypeIICrossIsometryPair`) rather than inside the theorem. -/
theorem exceptional_case_frobenius_realization_of_trigger [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (hno : ¬ ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
        IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * chars.u : ℕ) : ℂ)) :
    (∀ g : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)),
        uActionHom data chief g ≠ 1 →
          MonoidHom.FixedPointFree (uActionHom data chief g)) ∧
      chars.u = (chief.p ^ data.q - 1) / (chief.p - 1) ∧
      IsCyclic ↥data.typeP.U ∧
      (IsTypeII M →
        OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(data.H ⊔ data.U)
          (data.H.subgroupOf (data.H ⊔ data.U))
          (data.U.subgroupOf (data.H ⊔ data.U))) := by
  rcases clifford_dichotomy hG chars with hA | hB
  · -- Case (a) is refuted by the trigger itself.
    exfalso
    obtain ⟨caseA⟩ := hA
    obtain ⟨-, -, ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩, -⟩ :=
      caseA_character_counts hG chars caseA
    exact hno ⟨lam,
      sOf_antitone data
        (sup_le_sup_left (Section11CharacterData.Cprime_le_C chars) chief.H0) hlam_mem,
      hlam_irr, hlam_deg⟩
  · obtain ⟨caseB⟩ := hB
    exact exceptional_case_frobenius_realization hG chars caseB hno

/-- **Peterfalvi (9.8.d), existence form**: in case (9.7.a) the family `𝒮(H₀U′)` contains an
irreducible character of degree `q·a` — the character `λ` of the (11.9.c) non-Galois
contradiction (`ψ = μ_j − (u/a)λ`, issue 1024).  Positivity of the (9.8.d) count
(`caseA_character_counts`): `(p−1)/a ≥ 1` since `a ∣ p−1` (`a_dvd_p_sub_one`), and
`|U|/(a|U′|) = [C_U(S₀) : U′] ≥ 1` (`card_U_div_a_mul_card_Uprime_eq_relIndex`). -/
theorem caseA_exists_irreducible_qa [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) (caseA : CliffordCaseAData chars) :
    ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime),
      IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ) := by
  classical
  obtain ⟨-, -, -, hcount⟩ := caseA_character_counts hG chars caseA
  have hppos : 0 < chief.p - 1 := by
    have := chief.p_prime.two_le; omega
  have hf1 : 1 ≤ (chief.p - 1) / caseA.a :=
    (Nat.one_le_div_iff caseA.a_pos).mpr (Nat.le_of_dvd hppos caseA.a_dvd_p_sub_one)
  have hf2 : 1 ≤ Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime) := by
    change 1 ≤ Nat.card ↥data.U / (caseA.a * Nat.card ↥(uprimeSub data))
    rw [card_U_div_a_mul_card_Uprime_eq_relIndex caseA]
    have hne : (uprimeSub data).relIndex (cuSub caseA) ≠ 0 := by
      rw [Subgroup.relIndex]
      exact Subgroup.index_ne_zero_of_finite
    omega
  have hpos : {χ ∈ chars.SOf (chief.H0 ⊔ chars.Uprime) |
      IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard ≠ 0 := by
    have h1 : (1 : ℕ) ≤ ((chief.p - 1) / caseA.a)
        * (Nat.card ↥data.U / (caseA.a * Nat.card ↥chars.Uprime)) :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
    omega
  obtain ⟨χ, hχ⟩ := Set.nonempty_of_ncard_ne_zero hpos
  exact ⟨χ, hχ.1, hχ.2.1, hχ.2.2⟩

/-- **`a ∣ u`** (Peterfalvi (11.9.c) integrality input): the Clifford integer `a = [U : C_U(S₀)]`
divides `u = [U : C_U(H̄)]`, since `C_U(H̄) ≤ C_U(S₀)` (`cInHu_le_cuInHu`) — index
antitonicity through the two first-isomorphism identifications
(`index_cuInHu_subgroupOf_uInHu_eq_a`, `index_cInHu_subgroupOf_uInHu_eq_u`). -/
theorem caseA_a_dvd_u [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) :
    caseA.a ∣ chars.u := by
  rw [caseA.a_eq_card_restrictAut_range, ← index_cuInHu_subgroupOf_uInHu_eq_a caseA,
    ← index_cInHu_subgroupOf_uInHu_eq_u data chief chars]
  exact Subgroup.index_dvd_of_le (fun x hx =>
    Subgroup.mem_subgroupOf.mpr (cInHu_le_cuInHu caseA (Subgroup.mem_subgroupOf.mp hx)))

/-- **`𝒮(Y) = sOf data Y` is closed under complex conjugation** (parallel to
`inducedKernelFamily_closedUnderConjugate`): conjugating the source `χ` preserves membership in
`𝒳(Y)` — the kernel is conjugation-invariant (`characterKernel_conj`), so both `H ⊄ Ker χ`
(`xiSet`) and `Y ⊆ Ker χ` are preserved — and `induceHU` commutes with conjugation
(`induceHU_eq_induce` + `ClassFunction.induce_conj`).  The conjugate-closure input of the (11.8.6)
`𝒮(H₀C)` witness (`hwit`). -/
theorem sOf_closedUnderConjugate [Finite G] {M : Subgroup G}
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M) (Y : Subgroup G) :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate (OddOrder.Peterfalvi.S11.sOf data Y) := by
  classical
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(OddOrder.Peterfalvi.S11.huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro φ hφ
  obtain ⟨χ, hχ, rfl⟩ := hφ
  set χc : IrreducibleCharacter ↥(OddOrder.Peterfalvi.S11.huSub data) :=
    ⟨(χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ).conj, χ.isIrreducible.conj⟩
    with hχcdef
  have hk : OddOrder.Peterfalvi.S03.characterKernel
      (χc : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)
      = OddOrder.Peterfalvi.S03.characterKernel
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) :=
    OddOrder.Peterfalvi.S03.characterKernel_conj _
  refine ⟨χc, ⟨?_, ?_⟩, ?_⟩
  · -- `χc ∈ xiSet`: `H ⊄ Ker χc = Ker χ`
    have h1 := hχ.1
    simp only [OddOrder.Peterfalvi.S11.xiSet, Set.mem_ofPred_eq] at h1 ⊢
    rwa [hk]
  · -- `Y ⊆ Ker χc = Ker χ`
    rw [hk]; exact hχ.2
  · -- `(induceHU χ).conj = induceHU χc`
    rw [OddOrder.Peterfalvi.S11.induceHU_eq_induce data
        (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ),
      OddOrder.Peterfalvi.S11.induceHU_eq_induce data
        (χc : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)]
    exact ClassFunction.induce_conj (OddOrder.Peterfalvi.S11.huSub data)
      (χ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ)

/-- **The degree-`d` irreducible cut of `𝒮(Y)` is conjugate-closed** (the `hconjS` input of the
(9.11) column-pair adjunction): conjugation preserves `𝒮(Y)`-membership
(`sOf_closedUnderConjugate`), irreducibility, and the natural degree (`star_natCast`).

Stated over Hypothesis (9.2) alone.  It previously took the §11 `S13.Hypothesis` bundle, but the
proof only ever used its `s11Setup` field (and a `Finite G` already present as a binder), so the
§11 packaging was decoration — issue 1045. -/
theorem irrCut_conjClosed [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (Y : Subgroup G) (d : ℕ) {x : ClassFunction ↥M ℂ}
    (hx : x ∈ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))}) :
    x.conj ∈ {φ : ClassFunction ↥M ℂ | φ ∈ sOf data Y ∧
      IsIrreducibleCharacter φ ∧ ((φ : ↥M → ℂ) 1 = (d : ℂ))} := by
  obtain ⟨hmem, hirr, hdeg⟩ := hx
  refine ⟨sOf_closedUnderConjugate data Y hmem, hirr.conj, ?_⟩
  rw [ClassFunction.conj_apply, hdeg, star_natCast]

end OddOrder.Peterfalvi.S11


