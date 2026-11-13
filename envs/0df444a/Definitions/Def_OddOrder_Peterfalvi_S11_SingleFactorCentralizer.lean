-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer
-- name    : OddOrder_Peterfalvi_S11_SingleFactorCentralizer
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:19:49.050203+00:00
-- url     : https://prove2.me/theorems/0f017478-9941-416f-9714-6b64ecff1924
-- title:
--   Peterfalvi (9.11.1): the single-factor centralizer
-- statement:
--   Formalizes the source-degree bound of Peterfalvi (9.11.1) and the case (a) divisibility facts based on the single-factor centralizer $C_U(S_0)$.
--
--   Main declarations: `xiOf_H0Cprime_source_apply_one_le_u` (Peterfalvi (9.11.1), the source-degree bound: every `χ ∈ 𝒳(H₀C′)` has `χ(1) ≤ u`); `caseA_source_degree_dvd_a_of_S0_witness` (Peterfalvi (9.11.1)/(9.8.a) case-(a) divisibility, `S₀`-witness form: `a ∣ χ(1)`); `exists_summand_witness_of_ne_one` (A nontrivial `H̄`-hom is nontrivial on some Clifford summand); `caseA_source_degree_dvd_a` (Peterfalvi (9.8.a)/(9.11.1) case-(a) divisibility: `a ∣ χ(1)` on `𝒳(H₀)`).
--
--   The bundle also proves 17 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_SingleFactorCentralizer.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_SingleFactorCentralizer.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CliffordData
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CuS0
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_CharacterCounts
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_Coherence911
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_SummandComplementKernel
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ThetaCountAssembly
import Definitions.Def_OddOrder_Peterfalvi_S07_Subcoherent
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceWeighted
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_NonInflatedDegreeSqInterval

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped Pointwise

variable {G : Type*} [Group G]

section DegreeBound

variable [Finite G] {M : Subgroup G}

open scoped Classical ComplexOrder in
/-- **Peterfalvi (9.11.1), the source-degree bound: every `χ ∈ 𝒳(H₀C′)` has `χ(1) ≤ u`.**

The degree of a source character with `H₀C′` in its kernel is at most `u = [U:C]`: `χ` lies over
a linear character `ψ` of `HC` (linear by the (9.9.a) commutator containment
`⁅HC,HC⁆ ≤ H₀C′ ⊆ Ker χ`), so `χ(1) ≤ (Ind_{HC}^{HU} ψ)(1) = [HU:HC] = u`.  This is the *upper*
half of the (9.9.a) degree computation, valid in **both** Clifford cases (case (b) upgrades it
to equality via the inertia argument, `caseB_degree_qu`); the (9.11.1) squeeze `lb0 ≤ lb1`
consumes it for the `𝒮₃`-member `χ` (member degree `q·χ(1) ≤ q·u`). -/
theorem xiOf_H0Cprime_source_apply_one_le_u {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} (chars : Section11CharacterData data chief)
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχ : χ ∈ xiOf data (chief.H0 ⊔ chars.Cprime)) :
    ((χ : ClassFunction ↥(huSub data) ℂ) : ↥(huSub data) → ℂ) 1 ≤ (chars.u : ℂ) := by
  classical
  have : Fintype ↥M := Fintype.ofFinite _
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data ⊔ cInHu data chief) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Invertible (Nat.card ↥(hInHu data ⊔ cInHu data chief) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype (IrreducibleCharacter ↥(huSub data)) :=
    Fintype.ofFinite _
  -- A constituent `ψ ∈ Irr(HC)` that `χ` lies over.
  obtain ⟨ψ, hψover⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.exists_liesOver
      (H := hInHu data ⊔ cInHu data chief) χ
  -- `ψ` is linear: `⁅HC,HC⁆ ⊆ Ker χ` (via `H₀C′ ⊆ Ker χ`), so `ψ` factors through the
  -- abelianization (the (9.9.a) obligation-3 block of `caseB_degree_qu`, verbatim).
  have hψdeg : (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ)
      (1 : ↥(hInHu data ⊔ cInHu data chief)) = 1 := by
    have : IsMulCommutative (↥(hInHu data ⊔ cInHu data chief) ⧸
        commutator ↥(hInHu data ⊔ cInHu data chief)) :=
      inferInstanceAs (IsMulCommutative (Abelianization ↥(hInHu data ⊔ cInHu data chief)))
    refine apply_one_eq_one_of_subset_characterKernel_of_isMulCommutative_quotient
      (N := commutator ↥(hInHu data ⊔ cInHu data chief)) ψ ?_
    intro g hg
    refine liesOver_mem_characterKernel hψover ?_
    refine hχ.2 ?_
    have hgmem : (g : ↥(huSub data))
        ∈ ⁅hInHu data ⊔ cInHu data chief, hInHu data ⊔ cInHu data chief⁆ := by
      rw [← derivedInG_eq_commutator]
      exact Subgroup.mem_map_of_mem _ hg
    exact commutator_hcInHu_le_realized data chief hgmem
  -- Constituent degree bound: `χ(1) ≤ (Ind_{HC}^{HU} ψ)(1)`.
  have hle := OddOrder.RepresentationTheory.apply_one_le_induce_apply_one_of_liesOver
    (I := hInHu data ⊔ cInHu data chief) χ ψ hψover
  -- `(Ind_{HC}^{HU} ψ)(1) = [HU:HC]·ψ(1) = [HU:HC] = u`.
  have hind : ClassFunction.induce (hInHu data ⊔ cInHu data chief)
      (ψ : ClassFunction ↥(hInHu data ⊔ cInHu data chief) ℂ) (1 : ↥(huSub data))
      = (chars.u : ℂ) := by
    rw [ClassFunction.induce_apply_one, hψdeg, mul_one]
    have hidx : (hInHu data ⊔ cInHu data chief).index = chars.u :=
      (index_hcInHu_eq_relindex_cInHu data chief).trans
        (index_cInHu_subgroupOf_uInHu_eq_u data chief chars)
    exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) hidx
  rw [hind] at hle
  exact hle

end DegreeBound

section CaseADivisibility

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- **The inertia of an `S₀`-nontrivial chief-factor character lies in `H·C_U(S₀)`**
(Peterfalvi (9.8.d)/(9.11.2) inertia containment, one-sided form).

The modular assembly over the landed hard direction `inertia_inf_uInHu_le_cuInHu`: decompose
`g ∈ I(θ₀)` as `g = h·u` (`H ⊔ U = ⊤` in `HU`, `H ◁ HU`); `h ∈ H ≤ I(θ₀)` always, so
`u = h⁻¹g ∈ I(θ₀) ⊓ U ≤ C_U(S₀)` by the single-factor stabilizer analysis.  This is the
containment half of the (9.8.d) inertia lift `I = H·C_U(S₀)` — sufficient for the (9.11.1)
divisibility, which only needs `[HU : H·C_U(S₀)] ∣ [HU : I(θ₀)]`. -/
theorem inertia_le_hcuInHu [Finite ↥(hInHu data)] (caseA : CliffordCaseAData chars)
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ caseA.S0,
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      ≤ hInHu data ⊔ cuInHu caseA := by
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  intro g hg
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
    (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cuInHu caseA hreg ⟨hu_in, hu⟩))

open scoped Classical in
/-- **Peterfalvi (9.11.1)/(9.8.a) case-(a) divisibility, `S₀`-witness form: `a ∣ χ(1)`.**

For `χ ∈ Irr(HU)` lying over the inflation of a linear `θ̄ : H̄ →* ℂˣ` that is **nontrivial on
the orbit generator `S₀`**, the Clifford integer `a = |U : C_U(S₀)|` divides the degree of `χ`:
the inertia `I(θ₀)` is contained in `H·C_U(S₀)` (`inertia_le_hcuInHu`), so
`a = [HU : H·C_U(S₀)]` (`index_hcuInHu_eq_caseA_a`) divides `[HU : I(θ₀)]`
(`Subgroup.index_dvd_of_le`), which divides `χ(1) = e·[HU:I(θ₀)]·θ₀(1)`
(`apply_one_eq_restrictionMultiplicity_mul_index_inertia`, `θ₀(1) = 1`).

This is Coq `a_dv_XH0` (`PFsection9.v:884-916`) with the summand pinned to `S₀`; the general
`𝒳(H₀)`-member reduces to this by `W₁`-transport (the summands are the `W₁`-orbit of `S₀`). -/
theorem caseA_source_degree_dvd_a_of_S0_witness
    [Fintype ↥(hInHu data)] [Invertible (Nat.card ↥(hInHu data) : ℂ)]
    (caseA : CliffordCaseAData chars)
    {χ : IrreducibleCharacter ↥(huSub data)}
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ}
    (hover : IrreducibleCharacter.LiesOver (hInHu data) χ
      (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))))
    (hS0 : ∃ x ∈ caseA.S0, θbar x ≠ 1)
    {d : ℕ} (hd : (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ)) :
    caseA.a ∣ d := by
  classical
  have : Fintype ↥M := Fintype.ofFinite _
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Fintype (IrreducibleCharacter ↥(hInHu data)) := Fintype.ofFinite _
  -- The realized constituent `θ₀ = linear(θ̄ ∘ mk'N ∘ equiv)` and its inflated `compHom` form.
  set θ₀ : IrreducibleCharacter ↥(hInHu data) :=
    linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
      (hInHuEquivH data).toMonoidHom)) with hθ₀def
  have hform : (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            ((linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
    rw [ClassFunction.compHom_linearIrreducibleCharacter,
      ClassFunction.compHom_linearIrreducibleCharacter, MonoidHom.comp_assoc]
  -- The regularity witness in irreducible-character form.
  have hreg : ∃ x ∈ caseA.S0,
      ((linearIrreducibleCharacter θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)) :
        ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ ((linearIrreducibleCharacter θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)) :
          ClassFunction (↥data.H ⧸ chief.N) ℂ) 1 := by
    obtain ⟨x, hx, hne⟩ := hS0
    refine ⟨x, hx, ?_⟩
    rw [linearIrreducibleCharacter_apply, linearIrreducibleCharacter_apply, map_one,
      Units.val_one]
    exact fun h => hne (Units.val_eq_one.mp h)
  -- Inertia containment `I(θ₀) ≤ H·C_U(S₀)`, hence `a ∣ [HU : I(θ₀)]`.
  have hcont : IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀
      ≤ hInHu data ⊔ cuInHu caseA := by
    change ClassFunction.inertia (θ₀ : ClassFunction ↥(hInHu data) ℂ)
      ≤ hInHu data ⊔ cuInHu caseA
    rw [hform]
    exact inertia_le_hcuInHu caseA hreg
  have hdvd_idx : caseA.a
      ∣ (IrreducibleCharacter.inertia (G := ↥(huSub data)) (H := hInHu data) θ₀).index := by
    rw [← index_hcuInHu_eq_caseA_a caseA]
    exact Subgroup.index_dvd_of_le hcont
  -- Clifford degree formula `χ(1) = e·[HU:I(θ₀)]·θ₀(1)` with `θ₀(1) = 1`.
  have key := OddOrder.RepresentationTheory.apply_one_eq_restrictionMultiplicity_mul_index_inertia
    (H := hInHu data) χ θ₀ hover
  obtain ⟨e, he⟩ :=
    OddOrder.RepresentationTheory.IrreducibleCharacter.restrictionMultiplicity_natCast
      (H := hInHu data) χ θ₀
  have hθ₀1 : (θ₀ : ClassFunction ↥(hInHu data) ℂ) (1 : ↥(hInHu data)) = 1 := by
    rw [hθ₀def, linearIrreducibleCharacter_apply, map_one, Units.val_one]
  rw [he, hθ₀1, hd, mul_one] at key
  -- `(d : ℂ) = e·[HU:I]`, so `d = e·[HU:I]` in `ℕ` and `a ∣ [HU:I] ∣ d`.
  have hdeq : d = e * (IrreducibleCharacter.inertia (G := ↥(huSub data))
      (H := hInHu data) θ₀).index := by
    exact_mod_cast key
  rw [hdeq]
  exact Dvd.dvd.mul_left hdvd_idx e

omit [Finite G] in
/-- **A nontrivial `H̄`-hom is nontrivial on some Clifford summand.**  The summands span
(`Hpart_iSup : ⨆ i, Hpart i = ⊤`), so a hom `θ̄` trivial on every `Hpart i` is trivial on all of
`H̄` (`Subgroup.iSup_induction`).  Selects the summand `w` of Coq `a_dv_XH0`'s
`/exists_inP[w W1w nt_t_w]` step. -/
theorem exists_summand_witness_of_ne_one (caseA : CliffordCaseAData chars)
    {θbar : (↥data.H ⧸ chief.N) →* ℂˣ} (hne : θbar ≠ 1) :
    ∃ w : Fin data.q, ∃ x ∈ caseA.Hpart w, θbar x ≠ 1 := by
  by_contra hall
  push Not at hall
  apply hne
  refine MonoidHom.ext fun y => ?_
  rw [MonoidHom.one_apply]
  have hy : y ∈ ⨆ i, caseA.Hpart i := caseA.Hpart_iSup ▸ Subgroup.mem_top y
  refine Subgroup.iSup_induction (C := fun z => θbar z = 1) caseA.Hpart hy
    (fun i z hz => hall i z hz) (map_one θbar) ?_
  intro a b ha hb
  rw [map_mul, ha, hb, mul_one]

open scoped Classical in
/-- **Peterfalvi (9.8.a)/(9.11.1) case-(a) divisibility: `a ∣ χ(1)` on `𝒳(H₀)`** (Coq
`a_dv_XH0`, `typeP_nonGalois_characters` part (a), `PFsection9.v:884-916`).

Every `χ ∈ 𝒳` with `H₀ ⊆ Ker χ` has degree divisible by the Clifford integer
`a = |U : C_U(S₀)|`.  Extraction (`exists_hom_constituent_of_mem_xiSet_H0`) yields a nontrivial
linear seed `θ̄` with `χ` lying over its inflation; `θ̄` is nontrivial on some summand
`Hpart w = φ(rep_w)•S₀` (`exists_summand_witness_of_ne_one`); conjugating `χ` by the
`M`-realization `m` of `rep_w` twists the seed to `θ̄∘φ(rep_w)` — nontrivial on `S₀` — while
preserving irreducibility and degree, so the `S₀`-witness form
(`caseA_source_degree_dvd_a_of_S0_witness`) applies to `χ^m` and `a ∣ χ^m(1) = χ(1)`.

This is the anchor-ratio divisibility of the (9.11.1) squeeze: every strict-branch adjoining
`χ − (χ(1)/qa)·χ₁` needs `a ∣ (source degree of χ)`. -/
theorem caseA_source_degree_dvd_a (caseA : CliffordCaseAData chars)
    {χ : IrreducibleCharacter ↥(huSub data)}
    (hχX : χ ∈ xiSet data)
    (hχH0 : ((chief.H0.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ))
    {d : ℕ} (hd : (χ : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ)) :
    caseA.a ∣ d := by
  classical
  have : Fintype ↥M := Fintype.ofFinite _
  have : Fintype ↥(huSub data) := Fintype.ofFinite _
  have : Fintype ↥(hInHu data) := Fintype.ofFinite _
  have : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have : Invertible (Nat.card ↥(hInHu data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  -- Extraction: a nontrivial linear seed `θ̄` with `χ` over its inflation.
  obtain ⟨θbar, hθbarne, hover⟩ := exists_hom_constituent_of_mem_xiSet_H0 hχX hχH0
  -- `θ̄` is nontrivial on some summand `Hpart w = φ(rep_w) • S₀`.
  obtain ⟨w, y, hyHw, hyne⟩ := exists_summand_witness_of_ne_one caseA hθbarne
  -- The twisted seed `θ̄ ∘ φ(rep_w)` is nontrivial on `S₀`.
  set φw := quotientMulAutHom chief.N_aInvariant (caseA.orbitRep w) with hφw
  set θbarw : (↥data.H ⧸ chief.N) →* ℂˣ := θbar.comp φw.toMonoidHom with hθbarw
  have hS0 : ∃ x ∈ caseA.S0, θbarw x ≠ 1 := by
    refine ⟨φw⁻¹ • y, ?_, ?_⟩
    · rw [caseA.Hpart_orbit w, ← hφw] at hyHw
      exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hyHw
    · rw [hθbarw, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
      change θbar (φw (φw⁻¹ • y)) ≠ 1
      simpa [MulAut.smul_def] using hyne
  -- The `M`-realization `m` of `rep_w` and the conjugated character `χ' = χ^m`.
  have hUW1M : data.typeP.U ⊔ data.typeP.W1 ≤ M := sup_le (U_le_M data) data.typeP.W1_le
  set m : ↥M := ⟨(caseA.orbitRep w : G), hUW1M (caseA.orbitRep w).2⟩ with hm
  have hmb : ((m : ↥M) : G) = ((caseA.orbitRep w : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have := huSub_normal data
  set χ' : IrreducibleCharacter ↥(huSub data) :=
    ⟨ClassFunction.conjBy (G := ↥M) (H := huSub data) m (χ : ClassFunction ↥(huSub data) ℂ),
      ClassFunction.IsIrreducibleCharacter.conjBy (H := huSub data) χ.isIrreducible m⟩
    with hχ'
  -- `χ'` lies over the inflation of the twisted seed.
  have hover' : IrreducibleCharacter.LiesOver (hInHu data) χ'
      (linearIrreducibleCharacter (θbarw.comp ((QuotientGroup.mk' chief.N).comp
        (hInHuEquivH data).toMonoidHom))) := by
    -- `Res χ' = compHom (hInHuConj m) (Res χ)` and the twisted target is the
    -- `compHom (hInHuConj m)`-image of the original target; inner products transport.
    have htarget : (linearIrreducibleCharacter (θbarw.comp ((QuotientGroup.mk' chief.N).comp
          (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)
        = ClassFunction.compHom (hInHuConj data m)
            (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
              (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ) := by
      rw [show (linearIrreducibleCharacter (θbar.comp ((QuotientGroup.mk' chief.N).comp
            (hInHuEquivH data).toMonoidHom)) : ClassFunction ↥(hInHu data) ℂ)
          = ClassFunction.compHom (hInHuEquivH data).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                ((linearIrreducibleCharacter θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) by
        rw [ClassFunction.compHom_linearIrreducibleCharacter,
          ClassFunction.compHom_linearIrreducibleCharacter, MonoidHom.comp_assoc]]
      rw [compHom_hInHuConj_hInHuEquivH data (caseA.orbitRep w) m hmb,
        compHom_typeP_conjAction_inflation,
        ClassFunction.compHom_linearIrreducibleCharacter,
        ClassFunction.compHom_linearIrreducibleCharacter,
        ClassFunction.compHom_linearIrreducibleCharacter, ← hφw, ← hθbarw]
      rfl
    change OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity _
      (χ' : ClassFunction ↥(huSub data) ℂ) _ ≠ 0
    rw [OddOrder.RepresentationTheory.ClassFunction.restrictionMultiplicity_def, htarget, hχ']
    change ClassFunction.inner (ClassFunction.restrict (hInHu data)
        (ClassFunction.conjBy (G := ↥M) (H := huSub data) m
          (χ : ClassFunction ↥(huSub data) ℂ)))
      (ClassFunction.compHom (hInHuConj data m) _) ≠ 0
    rw [hInHuConj_restrict_conjBy data m (χ : ClassFunction ↥(huSub data) ℂ),
      inner_compHom_of_bijective (hInHuConj data m) (hInHuConj_bijective data m)]
    exact hover
  -- `χ'(1) = χ(1) = d` (conjugation fixes the identity).
  have hd' : (χ' : ClassFunction ↥(huSub data) ℂ) (1 : ↥(huSub data)) = (d : ℂ) := by
    rw [hχ']
    change (ClassFunction.conjBy (G := ↥M) (H := huSub data) m
      (χ : ClassFunction ↥(huSub data) ℂ)) 1 = (d : ℂ)
    rw [ClassFunction.conjBy_apply, ← hd]
    exact congrArg _ (by simp)
  -- Conclude by the `S₀`-witness form applied to `χ'`.
  exact caseA_source_degree_dvd_a_of_S0_witness caseA hover' hS0 hd'

/-- **The Clifford integer `a` is odd** (Coq `odd_a`, `PFsection9.v:1536`): `a = [HU : H·C_U(S₀)]`
divides `|HU| ∣ |M| ∣ |G|`, and `|G|` is odd.  The parity input of the (9.11.1) `lb12` squeeze
step `2a ≤ p − 1` (`two_mul_le_of_dvd_of_odd`: `a ∣ p−1` odd + `p−1` even ⟹ `2a ∣ p−1`). -/
theorem caseA_a_odd (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) :
    Odd caseA.a := by
  have hdvd : caseA.a ∣ Nat.card G := by
    rw [← index_hcuInHu_eq_caseA_a caseA]
    exact ((hInHu data ⊔ cuInHu caseA).index_dvd_card).trans
      ((Subgroup.card_subgroup_dvd_card (huSub data)).trans
        (Subgroup.card_subgroup_dvd_card M))
  rcases Nat.even_or_odd caseA.a with heven | hodd
  · exfalso
    obtain ⟨k, hk⟩ := hG.odd
    have h2 : (2 : ℕ) ∣ Nat.card G := (even_iff_two_dvd.mp heven).trans hdvd
    omega
  · exact hodd

end CaseADivisibility

section SqueezeIdentifications

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- **`[U : C_U(S₀)] = a`** (ambient-`G` relative-index form of
`index_cuInHu_subgroupOf_uInHu_eq_a`): Lagrange `[U:C_U(S₀)]·|C_U(S₀)| = |U| = a·|C_U(S₀)|`
(`card_U_eq_a_mul_card_cuSub`), cancelling `|C_U(S₀)| > 0`. -/
theorem relIndex_cuSub_U_eq_a (caseA : CliffordCaseAData chars) :
    (cuSub caseA).relIndex data.U = caseA.a := by
  have h1 : (cuSub caseA).relIndex data.U * Nat.card ↥(cuSub caseA) = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cuSub caseA).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuSub_le_U caseA)).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (h1.trans (card_U_eq_a_mul_card_cuSub caseA))

/-- **`[U:U'] = a·[C_U(S₀):U']`** (the Coq `szS1'` denominator factorization): relative-index
multiplicativity along `U' ≤ C_U(S₀) ≤ U` with `[U:C_U(S₀)] = a`. -/
theorem relIndex_uprimeSub_U_eq (caseA : CliffordCaseAData chars) :
    (uprimeSub data).relIndex data.U
      = caseA.a * (uprimeSub data).relIndex (cuSub caseA) := by
  rw [← Subgroup.relIndex_mul_relIndex (uprimeSub data) (cuSub caseA) data.U
      (uprimeSub_le_cuSub caseA) (cuSub_le_U caseA),
    relIndex_cuSub_U_eq_a caseA, mul_comm]

/-- **`[U : C] = u`** (ambient-`G` relative-index form of `index_cInHu_subgroupOf_uInHu_eq_u`):
both sides multiply by `|C|` to `|U|` (Lagrange in `U` and in the `uInHu` realization). -/
theorem relIndex_cSub_U_eq_u (chars : Section11CharacterData data chief) :
    (cSub data chief).relIndex data.U = chars.u := by
  have h1 : (cSub data chief).relIndex data.U * Nat.card ↥(cSub data chief)
      = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cSub data chief).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cSub_le_U data chief)).toEquiv] at h
  have h2 : chars.u * Nat.card ↥(cSub data chief) = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cInHu data chief).subgroupOf (uInHu data))
    rwa [index_cInHu_subgroupOf_uInHu_eq_u data chief chars,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cInHu_le_uInHu data chief)).toEquiv,
      card_cInHu_eq data chief, card_uInHu_eq data] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

/-- **The `lb23` bound `u ≤ [U:U']`** — `u = [U:C]` and Lagrange monotonicity `[U:C] ≤ [U:U']`
along `U' ≤ C ≤ U` (`relIndex_le_relIndex_of_le`).  The `hule` input of the (9.11.1) squeeze. -/
theorem u_le_relIndex_uprimeSub_U (chars : Section11CharacterData data chief) :
    chars.u ≤ (uprimeSub data).relIndex data.U := by
  rw [← relIndex_cSub_U_eq_u chars]
  exact OddOrder.Peterfalvi.S07.relIndex_le_relIndex_of_le
    (uprimeSub_le_cSub data chief) (cSub_le_U data chief)

/-- **The exact (9.8.d) count `(p−1)·[U:U'] ≤ n₁·a²`** (Coq `lb_Sqa` with the `dv_lb`
exactness), `n₁` the number of degree-`qa` irreducibles in `𝒮(H₀U')`.  The landed count
(`caseA_character_counts` (d)) bounds `n₁` below by the iterated ℕ-division
`((p−1)/a)·(|U|/(a·|U'|))`; the divisibilities `a ∣ p−1` and `a·|U'| ∣ |U|` make both divisions
exact, and multiplying through by `a²` gives the multiplicative form consumed by the (9.11.1)
squeeze (`nineElevenOne_squeeze_arithmetic`'s `hcount`). -/
theorem caseA_character_count_exact (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseA : CliffordCaseAData chars) :
    (chief.p - 1) * ((uprimeSub data).relIndex data.U)
      ≤ {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a) := by
  have hcount := (caseA_character_counts hG chars caseA).2.2.2
  rw [show chars.Uprime = uprimeSub data from rfl,
    Section11CharacterData.SOf_eq,
    card_U_div_a_mul_card_Uprime_eq_relIndex caseA] at hcount
  rw [relIndex_uprimeSub_U_eq caseA, ← Nat.mul_div_cancel' caseA.a_dvd_p_sub_one]
  calc caseA.a * ((chief.p - 1) / caseA.a)
        * (caseA.a * (uprimeSub data).relIndex (cuSub caseA))
      = (chief.p - 1) / caseA.a * ((uprimeSub data).relIndex (cuSub caseA))
          * (caseA.a * caseA.a) := by ring
    _ ≤ {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a) := Nat.mul_le_mul_right _ hcount

end SqueezeIdentifications

section SqueezeArithmetic

/-- **Peterfalvi (9.11.1), the closed squeeze circle** (arithmetic core).

Inputs: the divisibility/parity facts making `2a ≤ p−1` (`two_mul_le_of_dvd_of_odd`), the degree
bound `χdeg ≤ u` (9.11.1 preamble), the index bound `u ≤ [U:U′]` (Lagrange), the (9.8.d) count
`(p−1)·[U:U′] ≤ n₁·a²` (exact form), the `sumnS` lower bound `n₁·(qa)² ≤ s₂` ((9.11.5)-(9.11.6):
uniform `Snorm` on `𝒮₁′` + subset monotonicity), and the pair-refuted upper bound
`s₂ ≤ 2q²a·χdeg` (the (5.6) contrapositive).  The chain
`(p−1)[U:U′]q² ≤ n₁(qa)² ≤ s₂ ≤ 2q²a·χdeg ≤ 2q²au ≤ (p−1)q²u ≤ (p−1)q²[U:U′]`
closes into a circle, so every inequality is an equality; cancellation extracts the (9.11.1)
conclusions `χdeg = u`, `2a = p−1`, `u = [U:U′]`, `n₁·a² = (p−1)·[U:U′]`, `s₂ = n₁(qa)²`. -/
theorem nineElevenOne_squeeze_arithmetic
    {p1 q a u iUU' χdeg n₁ : ℕ} {s₂ : ℝ}
    (hq : 0 < q) (ha : 0 < a) (hu : 0 < u) (hp1 : 0 < p1)
    (hadvd : a ∣ p1) (haodd : Odd a) (hpeven : Even p1)
    (hχu : χdeg ≤ u)
    (hule : u ≤ iUU')
    (hcount : p1 * iUU' ≤ n₁ * (a * a))
    (hs1' : (n₁ : ℝ) * ((q * a : ℕ) : ℝ) ^ 2 ≤ s₂)
    (hpair : s₂ ≤ 2 * (q : ℝ) ^ 2 * a * χdeg) :
    χdeg = u ∧ 2 * a = p1 ∧ u = iUU' ∧ n₁ * (a * a) = p1 * iUU' ∧
      s₂ = (n₁ : ℝ) * ((q * a : ℕ) : ℝ) ^ 2 := by
  -- `2a ≤ p−1` (Gauss: `a` odd divides the even `p1`).
  have h2a : 2 * a ≤ p1 :=
    OddOrder.Peterfalvi.S07.two_mul_le_of_dvd_of_odd hadvd haodd hpeven hp1
  -- The six nodes of the circle, as reals.
  set r₀ : ℝ := (p1 : ℝ) * iUU' * q ^ 2 with hr₀
  set r₁ : ℝ := (n₁ : ℝ) * ((q * a : ℕ) : ℝ) ^ 2 with hr₁
  set r₂ : ℝ := 2 * (q : ℝ) ^ 2 * a * χdeg with hr₂
  set r₃ : ℝ := 2 * (q : ℝ) ^ 2 * a * u with hr₃
  set r₄ : ℝ := (p1 : ℝ) * q ^ 2 * u with hr₄
  -- The circle: `r₀ ≤ r₁ ≤ s₂ ≤ r₂ ≤ r₃ ≤ r₄ ≤ r₀`.
  have h01 : r₀ ≤ r₁ := by
    have hc : ((p1 : ℝ) * iUU') ≤ (n₁ : ℝ) * (a * a) := by exact_mod_cast hcount
    calc r₀ = ((p1 : ℝ) * iUU') * (q : ℝ) ^ 2 := by rw [hr₀]; try ring
      _ ≤ ((n₁ : ℝ) * (a * a)) * (q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = r₁ := by rw [hr₁]; push_cast; try ring
  have h23 : r₂ ≤ r₃ := by
    have hχu' : (χdeg : ℝ) ≤ (u : ℝ) := by exact_mod_cast hχu
    rw [hr₂, hr₃]
    exact mul_le_mul_of_nonneg_left hχu' (by positivity)
  have h34 : r₃ ≤ r₄ := by
    have h2a' : ((2 * a : ℕ) : ℝ) ≤ (p1 : ℝ) := by exact_mod_cast h2a
    calc r₃ = ((2 * a : ℕ) : ℝ) * ((q : ℝ) ^ 2 * u) := by rw [hr₃]; push_cast; try ring
      _ ≤ (p1 : ℝ) * ((q : ℝ) ^ 2 * u) :=
          mul_le_mul_of_nonneg_right h2a' (by positivity)
      _ = r₄ := by rw [hr₄]; try ring
  have h40 : r₄ ≤ r₀ := by
    have hule' : (u : ℝ) ≤ (iUU' : ℝ) := by exact_mod_cast hule
    calc r₄ = ((p1 : ℝ) * (q : ℝ) ^ 2) * u := by rw [hr₄]; try ring
      _ ≤ ((p1 : ℝ) * (q : ℝ) ^ 2) * iUU' :=
          mul_le_mul_of_nonneg_left hule' (by positivity)
      _ = r₀ := by rw [hr₀]; try ring
  -- Close the circle: each adjacent pair is an equality.
  have e1s : r₁ = s₂ := le_antisymm hs1'
    (hpair.trans (h23.trans (h34.trans (h40.trans h01))))
  have es2 : s₂ = r₂ := le_antisymm hpair
    (h23.trans (h34.trans (h40.trans (h01.trans hs1'))))
  have e23 : r₂ = r₃ := le_antisymm h23
    (h34.trans (h40.trans (h01.trans (hs1'.trans hpair))))
  have e34 : r₃ = r₄ := le_antisymm h34
    (h40.trans (h01.trans (hs1'.trans (hpair.trans h23))))
  have e40 : r₄ = r₀ := le_antisymm h40
    (h01.trans (hs1'.trans (hpair.trans (h23.trans h34))))
  have e01 : r₀ = r₁ := le_antisymm h01
    (hs1'.trans (hpair.trans (h23.trans (h34.trans h40))))
  -- Cancellation constants.
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have huR : (0 : ℝ) < (u : ℝ) := by exact_mod_cast hu
  have hp1R : (0 : ℝ) < (p1 : ℝ) := by exact_mod_cast hp1
  -- (E1) `χdeg = u` from `r₂ = r₃`.
  have hE1 : χdeg = u := by
    have h : (χdeg : ℝ) = (u : ℝ) := by
      have h2q2a : (0 : ℝ) < 2 * (q : ℝ) ^ 2 * a := by positivity
      have := e23
      rw [hr₂, hr₃] at this
      exact mul_left_cancel₀ h2q2a.ne' this
    exact_mod_cast h
  -- (E2) `2a = p1` from `r₃ = r₄`.
  have hE2 : 2 * a = p1 := by
    have h : (2 * a : ℝ) = (p1 : ℝ) := by
      have hq2u : (0 : ℝ) < (q : ℝ) ^ 2 * u := by positivity
      have := e34
      rw [hr₃, hr₄] at this
      -- `2q²au = p1·q²u` ⟹ `2a = p1` (cancel `q²u`).
      have h' : (2 * (a : ℝ)) * ((q : ℝ) ^ 2 * u) = (p1 : ℝ) * ((q : ℝ) ^ 2 * u) := by
        linear_combination this
      exact mul_right_cancel₀ hq2u.ne' h'
    exact_mod_cast h
  -- (E3) `u = iUU'` from `r₄ = r₀`.
  have hE3 : u = iUU' := by
    have h : (u : ℝ) = (iUU' : ℝ) := by
      have hpq : (0 : ℝ) < (p1 : ℝ) * (q : ℝ) ^ 2 := by positivity
      have := e40
      rw [hr₄, hr₀] at this
      have h' : ((p1 : ℝ) * (q : ℝ) ^ 2) * (u : ℝ)
          = ((p1 : ℝ) * (q : ℝ) ^ 2) * (iUU' : ℝ) := by linear_combination this
      exact mul_left_cancel₀ hpq.ne' h'
    exact_mod_cast h
  -- (E4) `n₁·a² = p1·iUU'` from `r₀ = r₁`.
  have hE4 : n₁ * (a * a) = p1 * iUU' := by
    have h : ((n₁ * (a * a) : ℕ) : ℝ) = ((p1 * iUU' : ℕ) : ℝ) := by
      have hq2 : (0 : ℝ) < (q : ℝ) ^ 2 := by positivity
      have := e01
      rw [hr₀, hr₁] at this
      have h' : ((p1 : ℝ) * iUU') * (q : ℝ) ^ 2 = ((n₁ : ℝ) * (a * a)) * (q : ℝ) ^ 2 := by
        push_cast at this ⊢
        linear_combination this
      have := mul_right_cancel₀ hq2.ne' h'
      push_cast
      linear_combination this.symm
    exact_mod_cast h
  exact ⟨hE1, hE2, hE3, hE4, e1s.symm⟩

end SqueezeArithmetic

section Configuration

variable [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
  {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}

/-- **`Even (p − 1)`** for the chief-factor prime `p` of a minimal simple group of odd order.  `p`
divides `|H̄| = p^q ∣ |H| ∣ |G|` (odd), so `p` is odd (`≠ 2`) and `p − 1` is even.  The `lb12`
parity input `2a ∣ (p−1)`. -/
theorem chiefFactor_p_sub_one_even (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Even (chief.p - 1) := by
  have hq : 0 < data.q := data.nontrivial.2.1.pos
  have hpq : chief.p ^ data.q ∣ Nat.card ↥data.H :=
    ⟨Nat.card ↥chief.H0, chief.quotient_order⟩
  have hp_dvd : chief.p ∣ Nat.card G :=
    (dvd_pow_self chief.p hq.ne').trans (hpq.trans (Subgroup.card_subgroup_dvd_card data.H))
  have hp_ne2 : chief.p ≠ 2 := fun h =>
    (Nat.not_even_iff_odd.mpr hG.odd) (even_iff_two_dvd.mpr (h ▸ hp_dvd))
  obtain ⟨k, hk⟩ := chief.p_prime.odd_of_ne_two hp_ne2
  exact ⟨k, by omega⟩

/-- **Peterfalvi (9.11.1), the group-world equality configuration.**

The translation of `nineElevenOne_squeeze_arithmetic`'s numeric equalities into the group facts of
(9.11.1): given the squeeze inputs — the landed §9 identifications (`hχu`,
`u_le_relIndex_uprimeSub_U`, `caseA_character_count_exact`) plus the world bundle (`hs1'` uniform
sub-family value, `hpair` (5.6) contrapositive) — the squeeze circle closes to force

* `2·a = p − 1` (hence `a = (p−1)/2`);
* `C = U'` (from `[U:C] = [U:U']`, strict-index monotonicity off equality);
* the `𝒮₃`-member source degree `χdeg = u`;
* the count equality `n₁·a² = (p−1)·[U:U']` (`|𝒮₁| = (p−1)u/a²`).

Here `χdeg` is the abstract source degree of the chosen `𝒮₃`-member (`χ(1) ≤ u`) and `n₁` the number
of degree-`qa` irreducibles in `𝒮(H₀U')` (the landed count `caseA_character_counts` (d)); `s₂` is
the real `sumnS 𝒮₂`.  This is what the (9.11.2)–(9.11.8) refutation consumes. -/
theorem nineElevenOne_configuration (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (caseA : CliffordCaseAData chars) {χdeg : ℕ} {s₂ : ℝ}
    (hq : 0 < data.q) (hu : 0 < chars.u)
    (hp1 : 0 < chief.p - 1) (hχu : χdeg ≤ chars.u)
    (hs1' : ({χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard : ℝ)
        * ((data.q * caseA.a : ℕ) : ℝ) ^ 2 ≤ s₂)
    (hpair : s₂ ≤ 2 * (data.q : ℝ) ^ 2 * caseA.a * χdeg) :
    2 * caseA.a = chief.p - 1 ∧ chars.C = chars.Uprime ∧ χdeg = chars.u ∧
      {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard
        * (caseA.a * caseA.a) = (chief.p - 1) * ((uprimeSub data).relIndex data.U) := by
  obtain ⟨hE1, hE2, _hE3, hE4, _⟩ :=
    nineElevenOne_squeeze_arithmetic (p1 := chief.p - 1) (q := data.q) (a := caseA.a)
      (u := chars.u) (iUU' := (uprimeSub data).relIndex data.U) (χdeg := χdeg)
      (n₁ := {χ ∈ sOf data (chief.H0 ⊔ uprimeSub data) |
          IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * caseA.a : ℕ) : ℂ)}.ncard)
      (s₂ := s₂) hq caseA.a_pos hu hp1 caseA.a_dvd_p_sub_one (caseA_a_odd hG caseA)
      (chiefFactor_p_sub_one_even hG) hχu (u_le_relIndex_uprimeSub_U chars)
      (caseA_character_count_exact hG caseA) hs1' hpair
  -- `hE3 : u = [U:U']` translates to `C = U'` via strict index monotonicity off equality.
  refine ⟨hE2, ?_, hE1, hE4⟩
  -- `[U:C] = u = [U:U']`, and `U' ≤ C ≤ U`, so `C = U'`.
  have hCU' : (cSub data chief).relIndex data.U = (uprimeSub data).relIndex data.U := by
    rw [relIndex_cSub_U_eq_u chars]; exact _hE3
  by_contra hne
  have hne' : cSub data chief ≠ uprimeSub data := fun h => hne (by
    change chars.C = chars.Uprime
    simp only [Section11CharacterData.C, Section11CharacterData.Uprime]; exact h)
  exact absurd hCU' (ne_of_lt (OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
    (uprimeSub_le_cSub data chief) (cSub_le_U data chief) hne'))

end Configuration

/-- **A character supported on exactly two summands of an internal direct product.**  For the
internal direct product `Hbar = ∏ S k` of prime-order subgroups and two distinct indices `i ≠ j`,
there is a linear character `θ` nontrivial on `S i` and `S j` but *trivial on every other summand*
`S k`.  Combine the per-factor tuple `ψ` — nontrivial characters `A`, `B` at `i`, `j`
(`exists_ne_one_hom_of_prime_card`), the trivial character elsewhere (`Function.update` of the
constant `1`) — through `char_eq_on_factors_of_bijective`.  This is the (9.11.2) two-summand `θ`
whose inertia is `C_U(S i) ⊓ C_U(S j) = U₁ ∩ U₁ʷ` (regular on `S i`, `S j` for the `⊆` half; trivial
elsewhere for the `⊇` half). -/
theorem exists_two_summand_char {Hbar : Type*} [CommGroup Hbar] [Finite Hbar]
    {ι : Type*} [Finite ι] (S : ι → Subgroup Hbar)
    (hindep : iSupIndep S) (hspan : ⨆ i, S i = ⊤)
    (hp : ∀ i, (Nat.card ↥(S i)).Prime) {i j : ι} (hij : i ≠ j) :
    ∃ θ : Hbar →* ℂˣ, (∃ x ∈ S i, θ x ≠ 1) ∧ (∃ x ∈ S j, θ x ≠ 1) ∧
      ∀ k, k ≠ i → k ≠ j → ∀ x ∈ S k, θ x = 1 := by
  classical
  have : Fintype ι := Fintype.ofFinite _
  have hcomm : Pairwise fun a b : ι => ∀ x y : Hbar, x ∈ S a → y ∈ S b → Commute x y :=
    fun a b _ x y _ _ => mul_comm x y
  have hbij : Function.Bijective (Subgroup.noncommPiCoprod hcomm) :=
    ⟨Subgroup.injective_noncommPiCoprod_of_iSupIndep hindep, by
      rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]; exact hspan⟩
  obtain ⟨A, hAne⟩ := exists_ne_one_hom_of_prime_card (hp i)
  obtain ⟨B, hBne⟩ := exists_ne_one_hom_of_prime_card (hp j)
  set ψ : ∀ k, ↥(S k) →* ℂˣ := Function.update (Function.update (fun _ => 1) i A) j B with hψdef
  have hψj : ψ j = B := by rw [hψdef, Function.update_self]
  have hψi : ψ i = A := by rw [hψdef, Function.update_of_ne hij, Function.update_self]
  have hψk : ∀ k, k ≠ i → k ≠ j → ψ k = 1 := fun k hki hkj => by
    rw [hψdef, Function.update_of_ne hkj, Function.update_of_ne hki]
  obtain ⟨θ, hθ⟩ := char_eq_on_factors_of_bijective hcomm hbij ψ
  refine ⟨θ, ?_, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hAne
    rw [MonoidHom.one_apply] at hz
    exact ⟨↑z, z.2, by rw [hθ i z, hψi]; exact hz⟩
  · obtain ⟨z, hz⟩ := DFunLike.ne_iff.mp hBne
    rw [MonoidHom.one_apply] at hz
    exact ⟨↑z, z.2, by rw [hθ j z, hψj]; exact hz⟩
  · intro k hki hkj x hx
    have h := hθ k ⟨x, hx⟩
    rw [hψk k hki hkj] at h
    simpa using h

section NineElevenTwoInertia

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

variable [Finite G] {M : Subgroup G}

set_option backward.isDefEq.respectTransparency false in
/-- **Per-summand char-inertia (generic summand).**  For *any* order-`p` `U`-invariant summand `S`
of
the chief factor `H̄` and an irreducible `θ` nontrivial on `S`, a `U`-element `g` fixing `θ` acts
trivially on `S` (`aInvariantRestrictAut hSinv g = 1`, i.e. `g ∈ C_U(S)`).  This generalises the
a-owned `chiefFactor_caseA_char_inertia_single` from the distinguished generator `S₀ = caseA.S0` to
an
arbitrary summand — needed for the (9.11.2) two-summand inertia `I(θ) ⊓ U ⊆ C_U(S₀) ⊓ C_U(S₀ʷ)`,
obtained by applying this once to `S = S₀` and once to `S = S₀ʷ` (both order-`p`, `U`-invariant,
with
`θ` regular on each).  Same pure-algebra heart (`mulAut_eq_id_on_of_fixes_ne_one_on_prime`: `θ`
faithful on the prime-order `S`), lifted through `aInvariantRestrictAut_coe`. -/
theorem caseA_char_inertia_of_summand {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {S : Subgroup (↥data.H ⧸ chief.N)} (hSinv : IsAInvariant (uActionHom data chief) S)
    (hScard : Nat.card ↥S = chief.p)
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hreg : ∃ x ∈ S, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    aInvariantRestrictAut hSinv g = 1 := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) :=
    IsMulCommutative.of_comm chief.quotient_elementaryAbelian.comm
  have hid : ∀ x ∈ S, (uActionHom data chief) g x = x :=
    mulAut_eq_id_on_of_fixes_ne_one_on_prime ((uActionHom data chief) g) S
      (by rw [hScard]; exact chief.p_prime)
      (fun x hx => hSinv.smul_mem g hx) θ hreg hinv
  ext x
  rw [MulAut.one_apply, aInvariantRestrictAut_coe, hid x x.2]

/-- **(9.11.2) two-summand inertia containment `I(θ) ⊓ U ⊆ C_U(H_i) ⊓ C_U(H_j)`.**  For a character
`θ` regular on two Clifford summands `Hpart i`, `Hpart j`, a `U`-element `g` in the inertia (fixing
`θ`) acts trivially on *both* summands: `aInvariantRestrictAut (Hpart_aInvariant i) g = 1` and
`aInvariantRestrictAut (Hpart_aInvariant j) g = 1`, i.e. `g ∈ C_U(H_i) ∩ C_U(H_j)`.  Applying
`caseA_char_inertia_of_summand` once per summand (both order-`p` and `U`-invariant by
`Hpart_order`/`Hpart_aInvariant`).  This is the `⊆`-half of the (9.11.2) inertia identity
`I(θ) ⊓ U = U₁ ∩ U₁ʷ` (take `i = 0`, `j` = the `W₁`-translate index of `S₀ʷ`); the reverse `⊇` is
"fixing both summands ⟹ fixing `θ`", and the index of the intersection is then forced into
`{u, a}`. -/
theorem caseA_char_inertia_two_summands {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    {θ : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hregi : ∃ x ∈ caseA.Hpart i, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hinv : ∀ x, (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) ((uActionHom data chief) g x)
        = (θ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x) :
    aInvariantRestrictAut (caseA.Hpart_aInvariant i) g = 1 ∧
      aInvariantRestrictAut (caseA.Hpart_aInvariant j) g = 1 :=
  ⟨caseA_char_inertia_of_summand (caseA.Hpart_aInvariant i) (caseA.Hpart_order i) hregi g hinv,
    caseA_char_inertia_of_summand (caseA.Hpart_aInvariant j) (caseA.Hpart_order j) hregj g hinv⟩

/-- **(9.11.2) two-summand inertia containment `C_U(H_i) ⊓ C_U(H_j) ⊆ I(θ) ⊓ U`** (the reverse `⊇`).
For a linear character `χ` of `H̄` supported on the two summands `H_i`, `H_j` (trivial on every
other
summand `H_k`, `hsupp`), a `U`-element `g` centralizing both (`aInvariantRestrictAut … g = 1` on `i`
and `j`) fixes `χ`: `χ(g·x) = χ(x)` for all `x`.  Proof by the generators argument — `χ∘g` and `χ`
agree on each summand `H_k` (on `H_i`/`H_j` because `g` acts as the identity; on the others because
`χ` is trivial there and `g·H_k = H_k` by `U`-invariance), and the summands span `H̄`
(`Hpart_iSup`), so `χ∘g = χ` (`MonoidHom.eq_of_eqOn_top` on `MonoidHom.eqLocus`).

Together with `caseA_char_inertia_two_summands` (the `⊆` half) this identifies the inertia of a
two-summand-supported regular `θ`: `I(θ) ⊓ U = C_U(H_i) ⊓ C_U(H_j) = U₁ ∩ U₁ʷ`.  The (9.11.2)
degree computation then reads off `[U : U₁ ∩ U₁ʷ]` as the inertia index. -/
theorem caseA_centralizes_two_summands_fixes_char {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hgi : aInvariantRestrictAut (caseA.Hpart_aInvariant i) g = 1)
    (hgj : aInvariantRestrictAut (caseA.Hpart_aInvariant j) g = 1) :
    ∀ x, χ ((uActionHom data chief) g x) = χ x := by
  -- `g` acts as the identity on `H_i` and `H_j` (from `aInvariantRestrictAut … g = 1`).
  have hcent : ∀ k : Fin data.q, (k = i ∨ k = j) → ∀ x ∈ caseA.Hpart k,
      (uActionHom data chief) g x = x := by
    rintro k (rfl | rfl) x hx
    · have h := aInvariantRestrictAut_coe (caseA.Hpart_aInvariant k) g ⟨x, hx⟩
      rw [hgi] at h; simpa using h.symm
    · have h := aInvariantRestrictAut_coe (caseA.Hpart_aInvariant k) g ⟨x, hx⟩
      rw [hgj] at h; simpa using h.symm
  -- `χ ∘ (uActionHom g)` and `χ` agree on every summand, which span `H̄`.
  have hle : (⨆ k, caseA.Hpart k) ≤
      MonoidHom.eqLocus (χ.comp ((uActionHom data chief) g).toMonoidHom) χ := by
    rw [iSup_le_iff]
    intro k x hx
    change (χ.comp ((uActionHom data chief) g).toMonoidHom) x = χ x
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    by_cases hk : k = i ∨ k = j
    · rw [hcent k hk x hx]
    · push Not at hk
      rw [hsupp k hk.1 hk.2 _ ((caseA.Hpart_aInvariant k).smul_mem g hx),
        hsupp k hk.1 hk.2 x hx]
  rw [caseA.Hpart_iSup] at hle
  have heq : χ.comp ((uActionHom data chief) g).toMonoidHom = χ :=
    MonoidHom.eq_of_eqOn_top fun x _ => hle (Subgroup.mem_top x)
  intro x
  have := DFunLike.congr_fun heq x
  rwa [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at this

open scoped IsMulCommutative in
/-- **The (9.11.2) two-summand character exists on the case-(a) chief factor.**  Instantiates
`exists_two_summand_char` at the internal direct product `caseA.Hpart` of the `q` order-`p` Clifford
summands (`Hpart_iSupIndep` + `Hpart_iSup` + `Hpart_order`): for two distinct summand indices
`i ≠ j`
there is a linear character `θ` of `H̄` nontrivial on `H_i`, `H_j` and trivial on every other
summand.
Feeding this `θ` to `caseA_char_inertia_two_summands` (`⊆`) and
`caseA_centralizes_two_summands_fixes_char` (`⊇`) identifies its inertia as
`C_U(H_i) ⊓ C_U(H_j)`. -/
theorem exists_caseA_two_summand_char {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (hij : i ≠ j) :
    ∃ θ : (↥data.H ⧸ chief.N) →* ℂˣ, (∃ x ∈ caseA.Hpart i, θ x ≠ 1) ∧
      (∃ x ∈ caseA.Hpart j, θ x ≠ 1) ∧
      ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, θ x = 1 := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  exact exists_two_summand_char caseA.Hpart caseA.Hpart_iSupIndep caseA.Hpart_iSup
    (fun k => by rw [caseA.Hpart_order k]; exact chief.p_prime) hij

set_option backward.isDefEq.respectTransparency false in
/-- **`C ⊆ C_U(H_k)` (action level): centralizing all of `H̄` centralizes each summand.**  A
`U`-element `g` acting trivially on the whole chief factor (`uActionHom g = 1`, i.e. `g` realizing
an
element of `C = C_U(H̄)`) acts trivially on every Clifford summand `H_k`
(`aInvariantRestrictAut (Hpart_aInvariant k) g = 1`), because the restricted action is a restriction
of `uActionHom g = 1`.  This is the easy `⊆`-direction of the (9.11.2) final identity
`C = U₁ ∩ U₁ʷ`:
`C ⊆ C_U(H_i) ⊓ C_U(H_j)` (the reverse `⊇` is the deep degree argument). Realized to `G`-subgroups
it
gives `cSub ≤ C_U(H_i) ⊓ C_U(H_j)` (cf. the landed `cSub_le_cuSub` for the generator `S₀`). -/
theorem centralizes_all_imp_centralizes_summand {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (k : Fin data.q)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hg : (uActionHom data chief) g = 1) :
    aInvariantRestrictAut (caseA.Hpart_aInvariant k) g = 1 := by
  ext x
  rw [MulAut.one_apply, aInvariantRestrictAut_coe, hg, MulAut.one_apply]

/-- **Inflation-fixing ⟹ action-fixing (conclusion-agnostic).**  If a realized `U`-element `g` fixes
the *inflated* chief-factor character `θ₀ = θbar` inflated to `H` (the `compHom (mk' N)`-fixing
under
`typeP_conjAction`), then `g`'s `U`-action fixes `θbar` on `H̄`: `θbar(φ_U(g)·x) = θbar(x)` for all
`x`.  Strips the inflation (`compHom_typeP_conjAction_inflation`, then `mk' N` injective) exactly as
`caseB_char_inertia_inflation_of_core` does, but *without* committing to a downstream conclusion —
so
it composes with **any** char-inertia core (all-summand `uActionHom g = 1`, or the two-summand
centralizer).  This is the HU→Ū half of the (9.11.2) inertia bridge. -/
theorem inflation_fixing_imp_action_fixing {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    ∀ x, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)
        (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).φ.comp
          (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype) g x)
          = (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x := by
  rw [compHom_typeP_conjAction_inflation] at hfix
  have hfix2 := ClassFunction.compHom_injective_of_surjective
    (QuotientGroup.mk'_surjective chief.N) hfix
  intro x
  rw [show ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).φ.comp (typeP_quotientCoprimeAction data.typeP data.nontrivial.1
        chief.N_aInvariant).U.subtype) g
      = quotientMulAutHom chief.N_aInvariant
          ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
            chief.N_aInvariant).U.subtype g) from rfl]
  exact congrFun (congrArg (fun f : ClassFunction (↥data.H ⧸ chief.N) ℂ =>
    (f : (↥data.H ⧸ chief.N) → ℂ)) hfix2) x

/-- **(9.11.2) HU-inertia bridge (`⊆` half): fixing the inflated two-summand `θ₀` in `HU`
centralizes
both summands.**  For a chief-factor character `θbar` regular on the two Clifford summands `H_i`,
`H_j`, a realized `U`-element `g` in the `HU`-inertia of the inflation `θ₀` (`hfix`) centralizes
both
summands: `aInvariantRestrictAut … g = 1` on `i` and `j`.  Composes the inflation-stripping
`inflation_fixing_imp_action_fixing` (HU-fixing → Ū-fixing) with the Ū-level two-summand
char-inertia
`caseA_char_inertia_two_summands`.  This is the `HU`-side of `I(θ₀) ⊓ U ⊆ C_U(H_i) ⊓ C_U(H_j)`; with
the realized subgroups it feeds the index computation `[HU : I(θ₀)] = [U : U₁ ∩ U₁ʷ]`. -/
theorem caseA_hu_char_inertia_two_summands {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hregi : ∃ x ∈ caseA.Hpart i, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hfix : ClassFunction.compHom (typeP_conjAction data.typeP
              ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
                chief.N_aInvariant).U.subtype g)).toMonoidHom
              (ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))
            = ClassFunction.compHom (QuotientGroup.mk' chief.N)
                (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ)) :
    aInvariantRestrictAut (caseA.Hpart_aInvariant i) g = 1 ∧
      aInvariantRestrictAut (caseA.Hpart_aInvariant j) g = 1 :=
  caseA_char_inertia_two_summands caseA hregi hregj g (inflation_fixing_imp_action_fixing g hfix)

/-- **(9.11.2) HU-inertia bridge (`⊇` half, `compHom` form): centralizing both summands fixes the
inflated `θ₀`.**  The Ū-side `⊇` lemma `caseA_centralizes_two_summands_fixes_char` in the `compHom`
shape the `HU`-inertia consumer needs: for a `U`-element `g` centralizing both summands `H_i`, `H_j`
and a two-summand-supported linear `χ`, the pullback of `θbar = linearIrreducibleCharacter χ` along
`φ_U(g)` equals `θbar` as a class function (`compHom (uActionHom g) θbar = θbar`).  Combined with
`conjBy_compHom_hInHuEquivH` + `compHom_typeP_conjAction_inflation` (as in `cInHu_le_inertia`) this
gives `C_U(H_i) ⊓ C_U(H_j) ⊆ I(θ₀)` — the reverse containment completing `I(θ₀) ⊓ U = U₁ ∩ U₁ʷ`. -/
theorem caseA_centralizes_two_summands_compHom_eq {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1)
    (g : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (hgi : aInvariantRestrictAut (caseA.Hpart_aInvariant i) g = 1)
    (hgj : aInvariantRestrictAut (caseA.Hpart_aInvariant j) g = 1) :
    ClassFunction.compHom ((uActionHom data chief) g).toMonoidHom
        (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) := by
  ext y
  rw [ClassFunction.compHom_apply, MulEquiv.coe_toMonoidHom, linearIrreducibleCharacter_apply,
    linearIrreducibleCharacter_apply,
    caseA_centralizes_two_summands_fixes_char caseA χ hsupp g hgi hgj y]

end NineElevenTwoInertia

/-- **Peterfalvi (9.8.a), member-degree dictionary for `𝒮(H₀ ⊔ Y)`** (Coq `a_dv_XH0` in member
form): in Clifford case (a), every member `Ind_{HU}^M ξ` of a §9 family whose source kernel
contains `H₀` has degree `q·a·e` for some `e : ℕ` — the source degree `ξ(1)` is divisible by the
Clifford integer `a` (`caseA_source_degree_dvd_a`).  This is the per-member degree-ratio supply
of the (5.6) pair-bound assembly `nineElevenPairBound`: ratios are taken against the degree-`qa`
anchor, so each member's ratio is the natural `e = ξ(1)/a`. -/
theorem caseA_sOf_source_degree_ratio [Finite G] {M : Subgroup G}
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M}
    {chief : OddOrder.Peterfalvi.S11.ChiefFactorData data}
    {chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief}
    (caseA : OddOrder.Peterfalvi.S11.CliffordCaseAData chars)
    {Y : Subgroup G} {ψ : ClassFunction ↥M ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S11.sOf data (chief.H0 ⊔ Y)) :
    ∃ e : ℕ, (ψ : ↥M → ℂ) 1 = ((data.q * caseA.a * e : ℕ) : ℂ) := by
  classical
  obtain ⟨ξ, hξ, rfl⟩ := hψ
  obtain ⟨dξ, -, hdξ⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ξ
  have hker : ((chief.H0.subgroupOf M).subgroupOf (OddOrder.Peterfalvi.S11.huSub data) :
      Set ↥(OddOrder.Peterfalvi.S11.huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel
        (ξ : ClassFunction ↥(OddOrder.Peterfalvi.S11.huSub data) ℂ) :=
    subset_trans (SetLike.coe_subset_coe.mpr (Subgroup.subgroupOf_mono _
      (Subgroup.subgroupOf_mono _ le_sup_left))) hξ.2
  obtain ⟨e, he⟩ := OddOrder.Peterfalvi.S11.caseA_source_degree_dvd_a caseA hξ.1 hker hdξ
  refine ⟨e, ?_⟩
  rw [OddOrder.Peterfalvi.S11.induceHU_apply_one_eq_q_mul, hdξ, he]
  push_cast
  ring

end OddOrder.Peterfalvi.S11


