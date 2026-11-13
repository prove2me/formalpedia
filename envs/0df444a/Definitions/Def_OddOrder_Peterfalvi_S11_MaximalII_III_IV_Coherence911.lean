-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:54:08.474818+00:00
-- url     : https://prove2.me/theorems/87574251-9c27-4bc6-9929-c457e7c9ca7f
-- title:
--   Peterfalvi (9.8.c)/(9.9.c): irreducible-character constructions
-- statement:
--   Formalizes the construction of irreducible characters of $HC$ and the associated homomorphisms in Peterfalvi (9.8.c) and (9.9.c), for the Clifford cases of maximal subgroups of types II, III and IV.
--
--   Main declarations: `hcQuotientEquivHbar` (Second isomorphism `HC/H₀C ≅ H̄`); `hcHom` (Inflation hom `HC → H̄`); `hcPsi` (The `HC`-linear character `ψ`); `hcLambdaHom` (The `λ`-lift `HC → ℂˣ`).
--
--   The bundle also proves 29 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/Coherence911.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/Coherence911.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- **realized `H₀C ◁ HU`** (in `huSub`): restricts `chiefFactor_H0supC_subgroupOf_normal`
(`(H₀C).subgroupOf M ◁ ↥M`) along `huSub ≤ ↥M`.  The `N ◁ G` hypothesis of the second isomorphism
`HC/H₀C ≅ H̄` in the (9.8.c) character construction. -/
theorem realizedH0supC_normal_huSub [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal :=
  (chiefFactor_H0supC_subgroupOf_normal chief).subgroupOf (huSub data)

/-- **`H₀C ∩ H = H₀` inside `hInHu`** (the `H ∩ N` of the second iso, realized in `hInHu`):
`(realized H₀C).subgroupOf hInHu = (realized H₀).subgroupOf hInHu`.  From
`hInHu_inf_realizedH0supC_eq_realizedH0` via `inf_subgroupOf_left`. This rewrites the
`N.subgroupOf H`
of `quotientInfEquivProdNormalQuotient` to `realized H₀`, the kernel of `hInHu ↠ H̄`. -/
theorem realizedH0supC_subgroupOf_hInHu_eq {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data)
      = ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data) := by
  rw [← Subgroup.inf_subgroupOf_left, hInHu_inf_realizedH0supC_eq_realizedH0]

/-- **realized `H₀` in `hInHu` = `N` pulled back along `hInHuEquivH`**: the realized `H₀`,
as a subgroup of `hInHu`, is `chief.N.comap hInHuEquivH`.  Via `hInHuEquivH_coe` + `chief.H0_eq`
(`H₀ = N.map H.subtype`): `x ∈ realized H₀ ⟺ ((x:M):G) ∈ H₀ ⟺ (hInHuEquivH x : G) ∈ H₀ ⟺
hInHuEquivH x ∈ N`.  Feeds `QuotientGroup.congr hInHuEquivH` for `hInHu/realizedH₀ ≅ ↥H ⧸ N =
H̄`. -/
theorem realizedH0_subgroupOf_hInHu_eq_comap {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data)
      = chief.N.comap (hInHuEquivH data).toMonoidHom := by
  ext x
  rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, chief.H0_eq, ← hInHuEquivH_coe,
    Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, hzeq⟩
    have hz_eq : z = hInHuEquivH data x := Subgroup.subtype_injective data.H hzeq
    rwa [hz_eq] at hz
  · intro h
    exact ⟨_, h, rfl⟩

/-- **realized `H₀` in `hInHu` maps to `N` under `hInHuEquivH`**: the map form of
`realizedH0_subgroupOf_hInHu_eq_comap`, via `map_comap_eq_self_of_surjective` (`hInHuEquivH`
surjective).  This is the `G'.map e = H'` hypothesis of `QuotientGroup.congr hInHuEquivH` for
`hInHu/realizedH₀ ≅ ↥H ⧸ N = H̄`. -/
theorem realizedH0_map_hInHuEquivH_eq_N {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data)).map
        (hInHuEquivH data).toMonoidHom = chief.N := by
  rw [realizedH0_subgroupOf_hInHu_eq_comap]
  exact Subgroup.map_comap_eq_self_of_surjective (hInHuEquivH data).surjective chief.N

/-- **Second isomorphism `HC/H₀C ≅ H̄`**: `(hInHu ⊔ H₀C)/H₀C ≃* ↥H ⧸ N`.  Composes
`quotientInfEquivProdNormalQuotient hInHu (realized H₀C)` (`HC/H₀C ≅ hInHu/(H₀C∩hInHu)`) with
`QuotientGroup.congr hInHuEquivH` (`hInHu/realizedH₀ ≅ ↥H ⧸ N`, using
`realizedH0supC_subgroupOf_hInHu_eq` + `realizedH0_map_hInHuEquivH_eq_N`).  The inflation
`θ̄ ∘ this`
gives the `HC`-linear character `ψ` of the (9.8.c) construction.  Type inferred to avoid the
`⊔`/`⧸` precedence trap. -/
noncomputable def hcQuotientEquivHbar [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :=
  letI hN := realizedH0supC_normal_huSub chief
  letI hN' : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data)).Normal := hN.subgroupOf (hInHu data)
  letI := chief.N_normal
  (QuotientGroup.quotientInfEquivProdNormalQuotient (hInHu data)
      (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).symm.trans
    (QuotientGroup.congr
      ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data)) chief.N (hInHuEquivH data)
      (by rw [realizedH0supC_subgroupOf_hInHu_eq]; exact realizedH0_map_hInHuEquivH_eq_N chief))

/-- **Inflation hom `HC → H̄`**: `↥(hInHu ⊔ H₀C) →* (↥H ⧸ N)`, the quotient map `mk'` by `H₀C`
followed by the second iso `hcQuotientEquivHbar`.  Composing a chief-factor character `θ̄` with this
gives the `HC`-linear character `ψ` (trivial on `H₀C`, inflation of `θ̄`) of the (9.8.c)
construction. -/
noncomputable def hcHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) →*
      (↥data.H ⧸ chief.N) :=
  letI hN := realizedH0supC_normal_huSub chief
  letI : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    hN.subgroupOf _
  (hcQuotientEquivHbar chief).toMonoidHom.comp
    (QuotientGroup.mk' ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub
        data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))))

/-- **The `HC`-linear character `ψ`** of the (9.8.c) construction: for a chief-factor character
`θ : H̄ →* ℂˣ` (the seed's regular character), `ψ = θ ∘ hcHom` is the inflation of `θ` to `HC`,
a linear (degree-one) irreducible character of `HC = hInHu ⊔ H₀C`, trivial on `H₀C`.  Its inertia in
`HU` is `HC` (`hInHu ◁ HC ◁ HU`, restriction to `θ₀`); `Ind_{HC}^{HU} ψ` is the degree-`u`
irreducible of `𝒳(H₀C)`. -/
noncomputable def hcPsi [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) :
    IrreducibleCharacter
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
  linearIrreducibleCharacter (θ.comp (hcHom chief))

/-- **`hcHom` is surjective**: `hcHom = (second iso) ∘ mk'(H₀C)`, a composite of the surjective
quotient map and the isomorphism `hcQuotientEquivHbar`.  Used to make `θ ↦ hcPsi θ` injective. -/
theorem hcHom_surjective [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Function.Surjective (hcHom chief) := by
  have := realizedH0supC_normal_huSub chief
  have : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    (realizedH0supC_normal_huSub chief).subgroupOf _
  intro y
  obtain ⟨x, rfl⟩ := (hcQuotientEquivHbar chief).surjective y
  obtain ⟨z, rfl⟩ := (QuotientGroup.mk'_surjective _) x
  exact ⟨z, rfl⟩

/-- **`θ ↦ hcPsi θ` is injective**: `hcPsi θ = linearIrreducibleCharacter (θ ∘ hcHom)`; distinct `θ`
give distinct `θ ∘ hcHom` (`hcHom` surjective, `MonoidHom.cancel_right`), hence distinct linear
characters (`linearIrreducibleCharacter_injective`).  So the regular seeds `θ` inject into the
`HC`-linear characters `hcPsi θ`, giving `|{hcPsi θ | θ regular}| = (p-1)^q` for the `oXtheta`
count. -/
theorem hcPsi_injective [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    Function.Injective (hcPsi chief) := by
  intro θ θ' h
  simp only [hcPsi] at h
  exact (MonoidHom.cancel_right (hcHom_surjective chief)).mp
    (linearIrreducibleCharacter_injective h)

/-- **`hcHom` kills `H₀C`**: `hcHom` sends the realized `H₀C` (inside `HC`) to `1`, since
`hcHom = iso ∘ mk'(H₀C)` and `mk'` kills `H₀C`.  Hence ψ = θ∘hcHom is trivial on `H₀C`, the kernel
condition `H₀C ⊆ Ker ζ` for `ζ ∈ 𝒳(H₀C)` in the (9.8.c) construction. -/
theorem hcHom_eq_one_of_mem_realizedH0supC [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    {x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))}
    (hx : x ∈ (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :
    hcHom chief x = 1 := by
  have hN := realizedH0supC_normal_huSub chief
  have : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).Normal :=
    hN.subgroupOf _
  simp only [hcHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply]
  rw [(QuotientGroup.eq_one_iff x).mpr hx, map_one]

/-- **`HC ◁ HU` in the realized `hInHu ⊔ H₀C` form**: `hInHu ⊔ (realized H₀C) ◁ huSub`, from
`hcInHu_normal` (`hInHu ⊔ cInHu ◁ HU`) and the identification `hInHu_sup_realizedH0supC`.  The
`H ◁ G` hypothesis of `isIrreducibleCharacter_induce_of_inertia_eq` for `Ind_{HC}^{HU} ψ`. -/
theorem hcInHu_realized_normal [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal := by
  rw [hInHu_sup_realizedH0supC]
  exact hcInHu_normal data chief

/-- **`hcHom ∘ inclusion = f` on `hInHu`**: `hcHom (incl h) = mk'_N (hInHuEquivH h)`, the seed
inflation.  The second iso sends the `hInHu`-class to the `HC`-class via inclusion
(`hfwd`: `quotientInf (mk' h) = mk' (incl h)`), then `congr_mk` applies `hInHuEquivH`.  Gives
`ψ|_hInHu = θ₀`, the input to the restriction-inertia `inertia(ψ) = HC`. -/
theorem hcHom_inclusion [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (h : ↥(hInHu data)) :
    hcHom chief (Subgroup.inclusion le_sup_left h)
      = QuotientGroup.mk' chief.N (hInHuEquivH data h) := by
  have hN := realizedH0supC_normal_huSub chief
  have hNsub := hN.subgroupOf
    (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
  have := chief.N_normal
  have hNh : ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data)).Normal := hN.subgroupOf (hInHu data)
  have hfwd : (QuotientGroup.quotientInfEquivProdNormalQuotient (hInHu data)
        (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
      (QuotientGroup.mk' _ h)
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left h) := by
    simp only [QuotientGroup.quotientInfEquivProdNormalQuotient,
      QuotientGroup.quotientInfEquivProdNormalizerQuotient, MulEquiv.trans_apply,
      QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.quotientKerEquivOfRightInverse, MulEquiv.coe_mk]
    rfl
  change (hcQuotientEquivHbar chief)
      (QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left h)) = _
  rw [← hfwd]
  change ((QuotientGroup.quotientInfEquivProdNormalQuotient (hInHu data)
        (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))).symm.trans
      (QuotientGroup.congr ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub
          data)).subgroupOf
        (hInHu data)) chief.N (hInHuEquivH data) _))
      ((QuotientGroup.quotientInfEquivProdNormalQuotient (hInHu data)
        (((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))
        (QuotientGroup.mk' _ h)) = _
  rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  exact QuotientGroup.congr_mk _ chief.N (hInHuEquivH data) _ h

/-- **`ψ|_hInHu = θ₀`** (pointwise): on the inclusion of `h ∈ hInHu`, the `HC`-linear character
`ψ = hcPsi θ` equals the seed's inflation `θ₀ = compHom hInHuEquivH (compHom mk'_N (linearIrr θ))`.
Both equal `(θ ((mk'_N) (hInHuEquivH h)) : ℂ)` via `hcHom_inclusion`.  This is the restriction
identity feeding the restriction-inertia `inertia(ψ) ⊆ inertia(θ₀) = HC`. -/
theorem hcPsi_apply_inclusion [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (h : ↥(hInHu data)) :
    (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      (Subgroup.inclusion le_sup_left h)
      = (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        h := by
  simp only [hcPsi, linearIrreducibleCharacter_apply, MonoidHom.comp_apply,
    ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom, hcHom_inclusion]

/-- **Restriction-inertia `inertia(ψ) ≤ inertia(θ₀)`**: an element `g` fixing the `HC`-character `ψ`
also fixes its restriction `θ₀ = ψ|_hInHu` (via `hcPsi_apply_inclusion`).  Pointwise `conjBy`
argument:
`conjBy g θ₀ (h) = θ₀⟨g h g⁻¹⟩ = ψ(incl⟨g h g⁻¹⟩) = ψ⟨g (incl h) g⁻¹⟩ = (conjBy g ψ)(incl h)
= ψ(incl h) = θ₀(h)`.  Combined with `subgroup_le_inertia` and the seed `inertia(θ₀) = HC`, gives
`inertia(ψ) = HC`. -/
theorem hcPsi_inertia_le [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ClassFunction.inertia (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      ≤ ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  have := hInHu_normal data
  intro g hg
  rw [ClassFunction.mem_inertia] at hg ⊢
  ext h
  have key : (ClassFunction.conjBy g (hcPsi chief θ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub
      data chief).subgroupOf M).subgroupOf (huSub data)) ℂ))
      (Subgroup.inclusion le_sup_left h)
      = (hcPsi chief θ : ClassFunction ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf
          M).subgroupOf (huSub data)) ℂ) (Subgroup.inclusion le_sup_left h) := by rw [hg]
  rw [ClassFunction.conjBy_apply] at key ⊢
  rw [← hcPsi_apply_inclusion, ← hcPsi_apply_inclusion, ← key]
  congr 1

/-- **`inertia(ψ) = HC`**: the inertia of the `HC`-linear character `ψ` in `HU` is exactly `HC`.
`le_antisymm` of `hcPsi_inertia_le` (`inertia(ψ) ≤ inertia(θ₀) = HC`, via the seed `hθ₀`) and
`subgroup_le_inertia` (`HC ≤ inertia(ψ)`).  This is the `inertia = H` hypothesis of
`isIrreducibleCharacter_induce_of_inertia_eq`, making `Ind_{HC}^{HU} ψ` irreducible of degree
`u`. -/
theorem hcPsi_inertia_eq_hc [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    ClassFunction.inertia (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) := by
  apply le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  refine le_trans (hcPsi_inertia_le chief θ) ?_
  rw [hθ₀]
  exact (hInHu_sup_realizedH0supC chief).ge

/-- **`ζ = Ind_{HC}^{HU}(ψ)` is irreducible** (degree `u`): direct from
`isIrreducibleCharacter_induce_of_inertia_eq` and `inertia(ψ) = HC` (`hcPsi_inertia_eq_hc`).  This
is
the degree-`u` irreducible character of `𝒳(H₀C)` over `θ₀` in the (9.8.c) construction. -/
theorem hcZeta_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    IsIrreducibleCharacter (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsi chief θ : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)) :=
  letI : Fintype
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    Fintype.ofFinite _
  OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq (hcPsi chief θ)
    (hcPsi_inertia_eq_hc chief θ hθ₀)

/-- **`[HU:HC] = u`**: the index of `HC = hInHu ⊔ H₀C` in `HU` is `u = |Ū|`.  Via the identification
`HC = hInHu ⊔ cInHu` and the existing `index_hcInHu_eq_relindex_cInHu` +
`index_cInHu_subgroupOf_uInHu_eq_u`
(`[HU:HC] = [U:C] = u`).  The degree `ζ(1) = [HU:HC]·ψ(1) = u·1` of the (9.8.c) construction. -/
theorem hc_index_eq_u [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief) :
    (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).index
      = chars.u := by
  rw [hInHu_sup_realizedH0supC]
  exact (index_hcInHu_eq_relindex_cInHu data chief).trans
    (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)

/-- **`HC = C·H` (realized)**: the `hInHu ⊔ (realized H₀C)` spelling of the inertia subgroup
equals `cInHu ⊔ hInHu`.  `hInHu_sup_realizedH0supC` plus `sup_comm`; the fixed spelling of the
second-isomorphism join in the `λ`-lift channel `hcLambdaHom`. -/
theorem hcRealized_eq_cInHu_sup_hInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)
      = cInHu data chief ⊔ hInHu data :=
  (hInHu_sup_realizedH0supC chief).trans (sup_comm _ _)

/-- `C ≤ HC` (realized): `cInHu` is contained in the `hInHu ⊔ (realized H₀C)` spelling of `HC`. -/
theorem cInHu_le_hcRealized {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) :
    cInHu data chief
      ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) :=
  le_trans le_sup_right (hInHu_sup_realizedH0supC chief).ge

/-- **The `λ`-lift `HC →* ℂˣ`** of a linear character `λ : C →* ℂˣ` (the second factor of the
(9.9.c) pair character): `HC → HC/H ≅ C/(C ⊓ H) = C —λ→ ℂˣ`.  Composite of the spelling bridge
`subgroupCongr`, the quotient map by `hInHu`, the reversed second isomorphism
`quotientInfEquivProdNormalQuotient cInHu hInHu`, and the lift of `λ` over the trivial
subgroup `H ⊓ C = ⊥` (`hInHu_inf_cInHu_eq_bot`).  Kills `hInHu`
(`hcLambdaHom_eq_one_of_mem_hInHu`) and restricts to `λ` on `cInHu` (`hcLambdaHom_inclusion`). -/
noncomputable def hcLambdaHom {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (lam : ↥(cInHu data chief) →* ℂˣ) :
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) →* ℂˣ :=
  letI : ((hInHu data).subgroupOf (cInHu data chief ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  (QuotientGroup.lift ((hInHu data).subgroupOf (cInHu data chief)) lam
      (fun x hx => by
        have hx1 : x = 1 := by
          have hmem : (x : ↥(huSub data)) ∈ hInHu data ⊓ cInHu data chief :=
            ⟨Subgroup.mem_subgroupOf.mp hx, x.2⟩
          rw [hInHu_inf_cInHu_eq_bot data chief, Subgroup.mem_bot] at hmem
          exact Subtype.ext hmem
        rw [hx1]
        exact lam.ker.one_mem)).comp
    ((QuotientGroup.quotientInfEquivProdNormalQuotient (cInHu data chief)
        (hInHu data)).symm.toMonoidHom.comp
      ((QuotientGroup.mk' ((hInHu data).subgroupOf (cInHu data chief ⊔ hInHu data))).comp
        (MulEquiv.subgroupCongr (hcRealized_eq_cInHu_sup_hInHu chief)).toMonoidHom))

/-- **`hcLambdaHom` kills `hInHu`**: the `λ`-lift is trivial on the `H`-part of `HC` (the
quotient map by `hInHu` kills it).  Hence the pair character restricts on `hInHu` to the plain
inflation `θ₀`, and the case-(b) inertia lift applies to the pair unchanged. -/
theorem hcLambdaHom_eq_one_of_mem_hInHu {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (lam : ↥(cInHu data chief) →* ℂˣ)
    {x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))}
    (hx : x ∈ (hInHu data).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :
    hcLambdaHom chief lam x = 1 := by
  let : ((hInHu data).subgroupOf (cInHu data chief ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  simp only [hcLambdaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply]
  have hmem : (MulEquiv.subgroupCongr (hcRealized_eq_cInHu_sup_hInHu chief)) x
      ∈ (hInHu data).subgroupOf (cInHu data chief ⊔ hInHu data) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx)
  rw [(QuotientGroup.eq_one_iff _).mpr hmem, map_one, map_one]

/-- **`hcLambdaHom` restricts to `λ` on `C`**: on the inclusion of `c ∈ cInHu` into `HC`, the
`λ`-lift returns `λ c`.  The second iso sends the `cInHu`-class to the `HC`-class via inclusion
(`hfwd`), so the reversed iso undoes the quotient map and the lift evaluates `λ`. -/
theorem hcLambdaHom_inclusion {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (lam : ↥(cInHu data chief) →* ℂˣ) (c : ↥(cInHu data chief)) :
    hcLambdaHom chief lam (Subgroup.inclusion (cInHu_le_hcRealized chief) c) = lam c := by
  let : ((hInHu data).subgroupOf (cInHu data chief ⊔ hInHu data)).Normal :=
    (hInHu_normal data).subgroupOf _
  have hfwd : (QuotientGroup.quotientInfEquivProdNormalQuotient (cInHu data chief)
        (hInHu data))
      (QuotientGroup.mk' _ c)
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left c) := by
    simp only [QuotientGroup.quotientInfEquivProdNormalQuotient,
      QuotientGroup.quotientInfEquivProdNormalizerQuotient, MulEquiv.trans_apply,
      QuotientGroup.quotientKerEquivOfSurjective,
      QuotientGroup.quotientKerEquivOfRightInverse, MulEquiv.coe_mk]
    rfl
  simp only [hcLambdaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have hcongr : (MulEquiv.subgroupCongr (hcRealized_eq_cInHu_sup_hInHu chief))
      (Subgroup.inclusion (cInHu_le_hcRealized chief) c)
      = Subgroup.inclusion le_sup_left c := by
    apply Subtype.ext
    rfl
  rw [hcongr, QuotientGroup.mk'_apply, show ((Subgroup.inclusion le_sup_left c :
      ↥(cInHu data chief ⊔ hInHu data)) : ↥(cInHu data chief ⊔ hInHu data)
        ⧸ (hInHu data).subgroupOf (cInHu data chief ⊔ hInHu data))
      = QuotientGroup.mk' _ (Subgroup.inclusion le_sup_left c) from rfl, ← hfwd,
    MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, QuotientGroup.lift_mk]

/-- **The (9.9.c) pair hom `θλ : HC →* ℂˣ`**: the product of the `θ`-inflation `θ ∘ hcHom`
(trivial on `H₀C`) and the `λ`-lift `hcLambdaHom λ` (trivial on `H`).  On `hInHu` it agrees
with `hcHom`'s inflation alone; on `cInHu` it is `λ` (the `θ`-factor dies on `C ≤ H₀C`). -/
noncomputable def hcPairHom [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ) :
    ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) →* ℂˣ :=
  (θ.comp (hcHom chief)) * (hcLambdaHom chief lam)

/-- **The `HC`-linear pair character `ψ_{θ,λ}`** of the (9.9.c) construction: the linear
(degree-one) irreducible character of `HC` with hom `hcPairHom θ λ`.  For `λ = 1` this is
`hcPsi θ`; for `λ ≠ 1` it does not kill `C`, the (9.9.c) lever. -/
noncomputable def hcPsiPair [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ) :
    IrreducibleCharacter
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
  linearIrreducibleCharacter (hcPairHom chief θ lam)

/-- **`ψ_{θ,λ}|_hInHu = θ₀`** (pointwise): on the inclusion of `h ∈ hInHu` the pair character
equals the seed's inflation `θ₀` — the `λ`-factor dies (`hcLambdaHom_eq_one_of_mem_hInHu`), and
the `θ`-factor is `hcPsi`'s restriction (`hcHom_inclusion`).  Same right-hand side as
`hcPsi_apply_inclusion`, so the restriction-inertia argument applies to the pair verbatim. -/
theorem hcPsiPair_apply_inclusion [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ) (h : ↥(hInHu data)) :
    (hcPsiPair chief θ lam : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      (Subgroup.inclusion le_sup_left h)
      = (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        h := by
  have hlam1 : hcLambdaHom chief lam (Subgroup.inclusion le_sup_left h) = 1 :=
    hcLambdaHom_eq_one_of_mem_hInHu chief lam (Subgroup.mem_subgroupOf.mpr h.2)
  simp only [hcPsiPair, hcPairHom, linearIrreducibleCharacter_apply, MonoidHom.mul_apply,
    MonoidHom.comp_apply, ClassFunction.compHom_apply,
    MulEquiv.coe_toMonoidHom, hcHom_inclusion, hlam1, mul_one]

/-- **Restriction-inertia `inertia(ψ_{θ,λ}) ≤ inertia(θ₀)`**: an element fixing the pair
character also fixes its `hInHu`-restriction `θ₀` (`hcPsiPair_apply_inclusion`).  Mirror of
`hcPsi_inertia_le` — the `λ`-factor is invisible on the restriction. -/
theorem hcPsiPair_inertia_le [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal] :
    ClassFunction.inertia (hcPsiPair chief θ lam : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      ≤ ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  have := hInHu_normal data
  intro g hg
  rw [ClassFunction.mem_inertia] at hg ⊢
  ext h
  have key : (ClassFunction.conjBy g (hcPsiPair chief θ lam : ClassFunction ↥(hInHu data ⊔
      ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ))
      (Subgroup.inclusion le_sup_left h)
      = (hcPsiPair chief θ lam : ClassFunction ↥(hInHu data ⊔
        ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
        (Subgroup.inclusion le_sup_left h) := by rw [hg]
  rw [ClassFunction.conjBy_apply] at key ⊢
  rw [← hcPsiPair_apply_inclusion, ← hcPsiPair_apply_inclusion, ← key]
  congr 1

/-- **`inertia(ψ_{θ,λ}) = HC`**: with the case-(b) seed `inertia(θ₀) = HC`
(`inertia_eq_hcInHu` for nontrivial `θ`), the pair character's `HU`-inertia is exactly `HC`.
Mirror of `hcPsi_inertia_eq_hc`. -/
theorem hcPsiPair_inertia_eq_hc [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    ClassFunction.inertia (hcPsiPair chief θ lam : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      = hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data) := by
  apply le_antisymm ?_ (ClassFunction.subgroup_le_inertia _)
  refine le_trans (hcPsiPair_inertia_le chief θ lam) ?_
  rw [hθ₀]
  exact (hInHu_sup_realizedH0supC chief).ge

/-- **`ζ_{θ,λ} = Ind_{HC}^{HU}(ψ_{θ,λ})` is irreducible** (degree `u`): direct from
`isIrreducibleCharacter_induce_of_inertia_eq` and `inertia(ψ_{θ,λ}) = HC`
(`hcPsiPair_inertia_eq_hc`).  The (9.9.c) irreducible source character over `θ₀`. -/
theorem hcZetaPair_irreducible [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    IsIrreducibleCharacter (ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsiPair chief θ lam : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)) :=
  letI : Fintype
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    Fintype.ofFinite _
  OddOrder.RepresentationTheory.isIrreducibleCharacter_induce_of_inertia_eq (hcPsiPair chief θ lam)
    (hcPsiPair_inertia_eq_hc chief θ lam hθ₀)

/-- **`H₀C' ⊆ Ker(θλ)`** (hom-level, pointwise): the pair hom kills the realized `H₀C'`.  The
`θ`-factor through `hcHom` kills all of `H₀C ⊇ H₀C'`; for the `λ`-factor, decompose
`x = h₀·c'` (`realizedH0supCprime_eq_realizedH0_sup_cprimeInHu`, `H₀ ◁ HU`) — the lift kills
`h₀ ∈ H₀ ≤ H` and `λ` kills `c' ∈ C'` by the hypothesis `hlam` (automatic for the linear `λ`
of the (9.9.c) construction, which factors through `C/C'`). -/
theorem hcPairHom_eq_one_of_mem_realizedH0supCprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    (hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    {x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))}
    (hx : x ∈ ((((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))) :
    hcPairHom chief θ lam x = 1 := by
  have hxHC : x ∈ ((((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) :=
    Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _
      (sup_le_sup_left (cprimeSub_le_C data chief) chief.H0))) hx
  have hθfac : θ.comp (hcHom chief) x = 1 := by
    rw [MonoidHom.comp_apply, hcHom_eq_one_of_mem_realizedH0supC chief hxHC, map_one]
  have hval : (x : ↥(huSub data))
      ∈ ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.mem_subgroupOf.mp hx
  rw [realizedH0supCprime_eq_realizedH0_sup_cprimeInHu] at hval
  have hH0n : ((chief.H0.subgroupOf M).subgroupOf (huSub data)).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (chief.H0_lt_H.le.trans (H_le_M data))).mpr
      chief.H0_normalized_by_M).subgroupOf (huSub data)
  obtain ⟨h₀, hh₀, c', hc', hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hval
  have hh₀H : h₀ ∈ hInHu data :=
    Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ chief.H0_lt_H.le) hh₀
  have hcC : c' ∈ cInHu data chief :=
    Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cprimeSub_le_C data chief)) hc'
  have hxfact : x = Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data))
      * Subgroup.inclusion (cInHu_le_hcRealized chief) (⟨c', hcC⟩ : ↥(cInHu data chief)) :=
    Subtype.ext hxeq.symm
  have hlamfac : hcLambdaHom chief lam x = 1 := by
    have h1 : hcLambdaHom chief lam
        (Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data))) = 1 :=
      hcLambdaHom_eq_one_of_mem_hInHu chief lam (Subgroup.mem_subgroupOf.mpr hh₀H)
    rw [hxfact, map_mul, h1, one_mul, hcLambdaHom_inclusion chief lam ⟨c', hcC⟩]
    exact hlam ⟨c', hcC⟩ hc'
  simp only [hcPairHom, MonoidHom.mul_apply, hθfac, hlamfac, mul_one]

/-- **`H₀C' ⊆ Ker ψ_{θ,λ}`** (`HC`-level, pointwise): every `x` in the realized `H₀C'` lies in
the character kernel of the pair character.  Mirror of
`hcPsi_mem_characterKernel_of_mem_realizedH0supC`, instance-free. -/
theorem hcPsiPair_mem_characterKernel_of_mem_realizedH0supCprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    (hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    {x : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))}
    (hx : x ∈ ((((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf
      (huSub data)).subgroupOf
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)))) :
    x ∈ OddOrder.Peterfalvi.S03.characterKernel (hcPsiPair chief θ lam : ClassFunction
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ) := by
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [hcPsiPair]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one,
    hcPairHom_eq_one_of_mem_realizedH0supCprime chief θ lam hlam hx, Units.val_one]

/-- **`H₀C' ⊆ Ker ψ_{θ,λ}`** as a `Set` inclusion (`HC`-level), instance-free.  Mirror of
`hcPsi_realizedH0supC_subgroupOf_subset_characterKernel`. -/
theorem hcPsiPair_realizedH0supCprime_subgroupOf_subset_characterKernel [Finite G]
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    (hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1) :
    ((((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :
        Set ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hcPsiPair chief θ lam) := by
  intro x hx
  exact hcPsiPair_mem_characterKernel_of_mem_realizedH0supCprime chief θ lam hlam
    (SetLike.mem_coe.mp hx)

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`H₀C' ⊆ Ker ζ_{θ,λ}`**: the realized `H₀C'` lies in the character kernel of
`ζ_{θ,λ} = Ind_{HC}^{HU}(ψ_{θ,λ})`.  Since the pair is `1` on `H₀C'` and `H₀C' ◁ HU`
(`realizedH0supCprime_normal_huSub`), the normal subgroup lands in the induced kernel
(`subsetCharacterKernel_induce_of_subgroupOf`).  Mirror of `hcZeta_H0supC_subset_ker`. -/
theorem hcZetaPair_H0supCprime_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (lam : ↥(cInHu data chief) →* ℂˣ)
    (hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card
        ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) : ℂ)] :
    ((((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsiPair chief θ lam)) := by
  have : Fintype
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    Fintype.ofFinite _
  have := realizedH0supCprime_normal_huSub chief
  exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((chief.H0 ⊔ cprimeSub data chief).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
    (le_trans (Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _
      (sup_le_sup_left (cprimeSub_le_C data chief) chief.H0))) le_sup_right)
    (hcPsiPair chief θ lam)
    (hcPsiPair_realizedH0supCprime_subgroupOf_subset_characterKernel chief θ lam hlam)

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`H ⊄ Ker ζ_{θ,λ}`** (`ζ_{θ,λ} ∈ 𝒳`): the irreducible `ζ_{θ,λ}` is nontrivial on
`H = hInHu`.  Mirror of `hcZeta_mem_xiSet` — the pair restricts on `hInHu` to the same
inflation `θ₀` (`hcPsiPair_apply_inclusion`), so `H ⊆ Ker` would force `θ = 1`. -/
theorem hcZetaPair_mem_xiSet [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1) (lam : ↥(cInHu data chief) →* ℂˣ)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    (⟨ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsiPair chief θ lam), hcZetaPair_irreducible chief θ lam hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiSet data := by
  have : Fintype
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    Fintype.ofFinite _
  classical
  set ζ : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.induce
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      (hcPsiPair chief θ lam), hcZetaPair_irreducible chief θ lam hθ₀⟩ with hζdef
  have hlo : OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver
      (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
      ζ (hcPsiPair chief θ lam) := by
    rw [← OddOrder.RepresentationTheory.IrreducibleCharacter.inner_induce_ne_zero_iff_liesOver]
    have hcoe : (ζ : ClassFunction ↥(huSub data) ℂ) = ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsiPair chief θ lam) := by rw [hζdef]
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
        hInHu data ≤ hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data)) h : ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
          (huSub data))) : ↥(huSub data)) ∈ hInHu data := by
    rw [Subgroup.coe_inclusion]; exact SetLike.coe_mem h
  have hψker := liesOver_mem_characterKernel hlo (hsub hgmem)
  have hψ1 : (hcPsiPair chief θ lam : ClassFunction
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) ℂ)
      1 = 1 := by
    simp [hcPsiPair]
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel, OddOrder.Peterfalvi.S03.characterDegree_def,
    hcPsiPair_apply_inclusion chief θ lam h, hψ1,
    ClassFunction.compHom_apply, ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom,
    linearIrreducibleCharacter_apply] at hψker
  have hqeq : (QuotientGroup.mk' chief.N) ((hInHuEquivH data) h) = q := hhq
  rw [hqeq] at hψker
  change θ q = (1 : ℂˣ)
  refine Units.ext ?_
  rw [Units.val_one]
  exact hψker

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`ζ_{θ,λ} ∈ 𝒳(H₀C')`**: combining `H ⊄ Ker` (`hcZetaPair_mem_xiSet`) and
`H₀C' ⊆ Ker` (`hcZetaPair_H0supCprime_subset_ker`).  This is the source character of the
(9.9.c) `𝒮(H₀C')`-member `Ind_{HU}^M ζ_{θ,λ}`.  Mirror of `hcZeta_mem_xiOf`. -/
theorem hcZetaPair_mem_xiOf [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ) (hθnt : θ ≠ 1) (lam : ↥(cInHu data chief) →* ℂˣ)
    (hlam : ∀ c : ↥(cInHu data chief),
      (c : ↥(huSub data)) ∈ ((cprimeSub data chief).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))]
    [Invertible (Nat.card ↥(huSub data) : ℂ)]
    [Invertible (Nat.card ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf
      (huSub data)) : ℂ)]
    [(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)).Normal]
    (hθ₀ : ClassFunction.inertia (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
        (ClassFunction.compHom (QuotientGroup.mk' chief.N)
          (linearIrreducibleCharacter θ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
        = hInHu data ⊔ cInHu data chief) :
    (⟨ClassFunction.induce
        (hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data))
        (hcPsiPair chief θ lam), hcZetaPair_irreducible chief θ lam hθ₀⟩ :
        IrreducibleCharacter ↥(huSub data)) ∈ xiOf data (chief.H0 ⊔ cprimeSub data chief) := by
  have : Fintype
      ↥(hInHu data ⊔ ((chief.H0 ⊔ cSub data chief).subgroupOf M).subgroupOf (huSub data)) :=
    Fintype.ofFinite _
  rw [mem_xiOf]
  exact ⟨hcZetaPair_mem_xiSet chief θ hθnt lam hθ₀,
    hcZetaPair_H0supCprime_subset_ker chief θ lam hlam⟩

/-- **`hcuSeedHom θ` kills `H₀`**: the seed hom `θ ∘ mk'(N) ∘ hInHuEquivH` is trivial on the
realized
`H₀` inside `hInHu`, since `hInHuEquivH` carries realized-`H₀` to `N`
(`realizedH0_subgroupOf_hInHu_eq_comap`) which `mk'(N)` kills.  Independent of `θ` (it is the
kernel condition `H₀ ⊆ Ker` for the `θ₀`-inflation). -/
theorem hcuSeedHom_eq_one_of_mem_realizedH0 [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} (chief : ChiefFactorData data) (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    {h : ↥(hInHu data)}
    (hh : h ∈ ((chief.H0.subgroupOf M).subgroupOf (huSub data)).subgroupOf (hInHu data)) :
    hcuSeedHom (chief := chief) θ h = 1 := by
  have hN : (hInHuEquivH data) h ∈ chief.N := by
    have := (realizedH0_subgroupOf_hInHu_eq_comap chief) ▸ hh
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at this
  rw [hcuSeedHom, MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hN, map_one]

set_option backward.isDefEq.respectTransparency false in
/-- **`hcuThetaHom` kills the complement `C_U(S₀)`**: on the inclusion of `c ∈ cuInHu` into
`H·C_U(S₀)`, the `θ₀`-extension returns `1` (its complement-part hom in the `SemidirectProduct.lift`
is `1`).  Via `SemidirectProduct.lift_inr` after `(mulEquivSubgroup).symm (inclusion c) = inr c`. -/
theorem hcuThetaHom_inclusion_cuInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (c : ↥(cuInHu caseA)) :
    hcuThetaHom caseA θ hinv (Subgroup.inclusion
        (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA) c) = 1 := by
  have := hInHu_normal data
  have : ((hInHu data).subgroupOf (hInHu data ⊔ cuInHu caseA)).Normal :=
    (hInHu_normal data).subgroupOf _
  have hsymm : (SemidirectProduct.mulEquivSubgroup
      (hInHu_isComplement'_cuInHu_in_hcuInHu caseA)).symm
      (Subgroup.inclusion (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA) c)
      = SemidirectProduct.inr
        (⟨Subgroup.inclusion (le_sup_right : cuInHu caseA ≤ hInHu data ⊔ cuInHu caseA) c,
          Subgroup.mem_subgroupOf.mpr c.2⟩ :
          ↥((cuInHu caseA).subgroupOf (hInHu data ⊔ cuInHu caseA))) := by
    rw [MulEquiv.symm_apply_eq]
    simp only [SemidirectProduct.mulEquivSubgroup, MulEquiv.ofBijective_apply,
      SemidirectProduct.monoidHomSubgroup_apply, SemidirectProduct.left_inr,
      SemidirectProduct.right_inr, OneMemClass.coe_one, one_mul]
  simp only [hcuThetaHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm,
    SemidirectProduct.lift_inr, MonoidHom.one_apply]

/-- **`realized H₀U' ≤ H·C_U(S₀)`**: the (9.8.d) kernel subgroup `H₀U'` realized inside `HU` lies in
the inertia subgroup `hInHu ⊔ cuInHu`.  `H₀ ≤ H ⟶ hInHu` and `U' ≤ C_U(S₀) ⟶ cuInHu`
(`uprimeSub_subgroupOf_le_cuInHu`). -/
theorem realizedH0supUprime_le_hcuInHu [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    ((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data)
      ≤ hInHu data ⊔ cuInHu caseA := by
  rw [realizedH0supUprime_eq_realizedH0_sup_uprimeInHu]
  refine sup_le (le_trans ?_ le_sup_left) (le_trans (uprimeSub_subgroupOf_le_cuInHu caseA)
    le_sup_right)
  exact Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ chief.H0_lt_H.le)

/-- **`hcuPairHom` kills `H₀U'`** (`HC`-level, pointwise): every `x` in the realized `H₀U'` lies in
the kernel of the pair hom `θ₁·λ`.  Decompose `x = h₀·u'` (`realizedH₀ ◁ H·C_U(S₀)`): the `θ`-part
`hcuThetaHom` restricts to `hcuSeedHom θ` on `h₀ ∈ H₀` (`= 1`,
`hcuSeedHom_eq_one_of_mem_realizedH0`)
and dies on `u' ∈ C_U(S₀)` (`hcuThetaHom_inclusion_cuInHu`); the `λ`-part `hcuLambdaHom` dies on
`h₀ ∈ H` (`hcuLambdaHom_eq_one_of_mem_hInHu`) and restricts to `λ u' = 1` on `u' ∈ U'` (`hlam`).
Single-factor mirror of `hcPairHom_eq_one_of_mem_realizedH0supCprime`. -/
theorem hcuPairHom_eq_one_of_mem_realizedH0supUprime [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    {x : ↥(hInHu data ⊔ cuInHu caseA)}
    (hx : x ∈ (((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data)).subgroupOf
      (hInHu data ⊔ cuInHu caseA)) :
    hcuPairHom caseA θ hinv lam x = 1 := by
  have := hInHu_normal data
  have hval : (x : ↥(huSub data))
      ∈ ((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data) :=
    Subgroup.mem_subgroupOf.mp hx
  rw [realizedH0supUprime_eq_realizedH0_sup_uprimeInHu] at hval
  have hH0n : ((chief.H0.subgroupOf M).subgroupOf (huSub data)).Normal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (chief.H0_lt_H.le.trans (H_le_M data))).mpr
      chief.H0_normalized_by_M).subgroupOf (huSub data)
  obtain ⟨h₀, hh₀, u', hu', hxeq⟩ := Subgroup.mem_sup_of_normal_left.mp hval
  have hh₀H : h₀ ∈ hInHu data :=
    Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ chief.H0_lt_H.le) hh₀
  have hu'C : u' ∈ cuInHu caseA := uprimeSub_subgroupOf_le_cuInHu caseA hu'
  have hxfact : x = Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data))
      * Subgroup.inclusion le_sup_right (⟨u', hu'C⟩ : ↥(cuInHu caseA)) :=
    Subtype.ext hxeq.symm
  -- `θ`-part: `1` on `h₀` (kills `H₀`) and `1` on `u'` (kills complement).
  have hθfac : hcuThetaHom caseA θ hinv x = 1 := by
    have h1 : hcuThetaHom caseA θ hinv
        (Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data)))
        = hcuSeedHom (chief := chief) θ ⟨h₀, hh₀H⟩ :=
      hcuThetaHom_inclusion_hInHu caseA θ hinv ⟨h₀, hh₀H⟩
    have h1' : hcuSeedHom (chief := chief) θ (⟨h₀, hh₀H⟩ : ↥(hInHu data)) = 1 :=
      hcuSeedHom_eq_one_of_mem_realizedH0 chief θ (Subgroup.mem_subgroupOf.mpr hh₀)
    have h2 : hcuThetaHom caseA θ hinv
        (Subgroup.inclusion le_sup_right (⟨u', hu'C⟩ : ↥(cuInHu caseA))) = 1 :=
      hcuThetaHom_inclusion_cuInHu caseA θ hinv ⟨u', hu'C⟩
    rw [hxfact, map_mul, h1, h1', one_mul, h2]
  -- `λ`-part: `1` on `h₀` (kills `H`) and `λ u' = 1` on `u' ∈ U'` (`hlam`).
  have hlamfac : hcuLambdaHom caseA lam x = 1 := by
    have h1 : hcuLambdaHom caseA lam
        (Subgroup.inclusion le_sup_left (⟨h₀, hh₀H⟩ : ↥(hInHu data))) = 1 :=
      hcuLambdaHom_eq_one_of_mem_hInHu caseA lam (Subgroup.mem_subgroupOf.mpr hh₀H)
    have h2 : hcuLambdaHom caseA lam
        (Subgroup.inclusion (cuInHu_le_hcuInHu caseA) (⟨u', hu'C⟩ : ↥(cuInHu caseA)))
        = lam ⟨u', hu'C⟩ := hcuLambdaHom_inclusion caseA lam ⟨u', hu'C⟩
    rw [hxfact, map_mul, h1, one_mul, h2]
    exact hlam ⟨u', hu'C⟩ hu'
  simp only [hcuPairHom, MonoidHom.mul_apply, hθfac, hlamfac, mul_one]

/-- **`H₀U' ⊆ Ker ψ_{θ₁,λ}` as a `Set` inclusion** (`HC`-level): the realized `H₀U'` is contained in
the character kernel of the pair character `ψ_{θ₁,λ}` (pointwise
`hcuPairHom_eq_one_of_mem_realizedH0supUprime`).  Mirror of
`hcPsiPair_realizedH0supCprime_subgroupOf_subset_characterKernel`. -/
theorem hcuPsiPair_realizedH0supUprime_subgroupOf_subset_characterKernel [Finite G]
    {M : Subgroup G} {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1) :
    ((((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data)).subgroupOf
        (hInHu data ⊔ cuInHu caseA) :
        Set ↥(hInHu data ⊔ cuInHu caseA)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (hcuPsiPair caseA θ hinv lam) := by
  intro x hx
  rw [OddOrder.Peterfalvi.S03.mem_characterKernel]
  simp only [hcuPsiPair]
  rw [linearIrreducibleCharacter_apply, OddOrder.Peterfalvi.S03.characterDegree_def,
    linearIrreducibleCharacter_apply_one,
    hcuPairHom_eq_one_of_mem_realizedH0supUprime caseA θ hinv lam hlam (SetLike.mem_coe.mp hx),
    Units.val_one]

set_option maxHeartbeats 1000000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **`H₀U' ⊆ Ker ζ_{θ₁,λ}`**: the realized `H₀U'` lies in the character kernel of
`ζ_{θ₁,λ} = Ind_{H·C_U(S₀)}^{HU}(ψ_{θ₁,λ})`.  Since the pair is `1` on `H₀U'` and `H₀U' ◁ HU`
(`realizedH0supUprime_normal_huSub`), the normal subgroup lands in the induced kernel
(`subsetCharacterKernel_induce_of_subgroupOf`).  Single-factor mirror of
`hcZetaPair_H0supCprime_subset_ker`. -/
theorem hcuZetaPair_H0supUprime_subset_ker [Finite G] {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (θ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hinv : ∀ c : ↥(cuInHu caseA), ∀ h : ↥(hInHu data),
      hcuSeedHom (chief := chief) θ
          ⟨(c : ↥(huSub data)) * (h : ↥(huSub data)) * (c : ↥(huSub data))⁻¹,
            (hInHu_normal data).conj_mem _ h.2 (c : ↥(huSub data))⟩
        = hcuSeedHom (chief := chief) θ h)
    (lam : ↥(cuInHu caseA) →* ℂˣ)
    (hlam : ∀ c : ↥(cuInHu caseA),
      (c : ↥(huSub data)) ∈ ((uprimeSub data).subgroupOf M).subgroupOf (huSub data) →
      lam c = 1)
    [Fintype ↥(huSub data)]
    [Finite ↥(hInHu data ⊔ cuInHu caseA)]
    [Invertible (Nat.card ↥(hInHu data ⊔ cuInHu caseA) : ℂ)] :
    ((((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data) :
        Set ↥(huSub data))) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (ClassFunction.induce
        (hInHu data ⊔ cuInHu caseA) (hcuPsiPair caseA θ hinv lam)) := by
  have : Fintype ↥(hInHu data ⊔ cuInHu caseA) := Fintype.ofFinite _
  have := realizedH0supUprime_normal_huSub chief
  exact OddOrder.Peterfalvi.S03.subsetCharacterKernel_induce_of_subgroupOf
    (A := ((chief.H0 ⊔ uprimeSub data).subgroupOf M).subgroupOf (huSub data))
    (H := hInHu data ⊔ cuInHu caseA)
    (realizedH0supUprime_le_hcuInHu caseA)
    (hcuPsiPair caseA θ hinv lam)
    (hcuPsiPair_realizedH0supUprime_subgroupOf_subset_characterKernel caseA θ hinv lam hlam)

end OddOrder.Peterfalvi.S11


