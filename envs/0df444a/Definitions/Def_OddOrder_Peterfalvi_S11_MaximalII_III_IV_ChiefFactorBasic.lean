-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_ChiefFactorBasic
-- name    : OddOrder_Peterfalvi_S11_MaximalII_III_IV_ChiefFactorBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:33:06.108471+00:00
-- url     : https://prove2.me/theorems/47d6714b-74f3-4138-9f4f-db92a1c226e2
-- title:
--   Peterfalvi §11: chief-factor core, opening layer
-- statement:
--   The opening layer of the chief-factor core in Peterfalvi, *Character Theory for the Odd Order Theorem*, §11, split from the parent file. It realizes $HU=H\sqcup U=M'$ inside $M$ (normal in $M$), and defines Peterfalvi (9.5)'s family $\mathcal{X}$ of irreducible characters of $HU$ and its subfamilies $\mathcal{X}(Y)$, together with induction from $HU$ to $M$.
--
--   Main declarations: `huSub` (`HU = H ⊔ U`, realised as a subgroup of `↥M`); `huSub_normal` (`HU ◁ M`: `HU = H ⊔ U = M' = [M,M]` is the derived subgroup realised inside `↥M`, hence normal); `hInHu` (`H`, realised as a subgroup of `HU = H ⊔ U` inside `↥M`); `xiSet`; and 17 more.
--
--   The bundle also proves 28 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_MaximalII_III_IV/ChiefFactorBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_MaximalII_III_IV_WielandtSetup

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

variable {M : Subgroup G}

/-- `HU = H ⊔ U`, realised as a subgroup of `↥M`. -/
def huSub (data : TypesIIIIIIVSetup M) : Subgroup ↥M :=
  (data.H ⊔ data.U).subgroupOf M

/-- `HU = H ⊔ U` is exactly the derived subgroup `M' = derivedInG M` realised inside `↥M`
(Peterfalvi (9.2): `M' = HU`).  This identifies the §9 induction carrier `huSub data` with the
`(derivedInG M).subgroupOf M` whose `mk'`-image is the `K` of the `M/H₀`-`Hypothesis`
(`chiefFactorQuotientHypothesis`), the bridge from the §9 family to the §6 reducible count
(issue 1012, B2 bijection). -/
theorem huSub_eq_derivedInG_subgroupOf (data : TypesIIIIIIVSetup M) :
    huSub data = (derivedInG M).subgroupOf M := by
  have h : data.H ⊔ data.U = derivedInG M := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]; rfl
  rw [huSub, h]

/-- **`HU ◁ M`**: `HU = H ⊔ U = M' = [M,M]` is the derived subgroup realised inside `↥M`, hence
normal.  This is the `H ⊴ G` hypothesis letting the §9 induction `induceHU = Ind_{HU}^M` use the
Clifford fibre/orbit machinery (`induce_eq_induce_iff_conj`: distinct `M`-conjugacy orbits ↔
distinct
inductions) for the `𝒳 ↔ 𝒮` count of Peterfalvi (9.5)/(9.9). -/
instance huSub_normal (data : TypesIIIIIIVSetup M) : (huSub data).Normal := by
  rw [huSub_eq_derivedInG_subgroupOf, show (derivedInG M).subgroupOf M = commutator ↥M by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]]
  infer_instance

/-- `H`, realised as a subgroup of `HU = H ⊔ U` inside `↥M`.  Used to state the kernel condition
`H ⊄ Ker χ` defining `𝒳`. -/
def hInHu (data : TypesIIIIIIVSetup M) : Subgroup ↥(huSub data) :=
  (data.H.subgroupOf M).subgroupOf (huSub data)

/-- **Peterfalvi (9.5)'s family `𝒳`**: the irreducible characters of `HU = H ⊔ U` (realised inside
`↥M`) that do not contain `H` in their kernel. -/
def xiSet (data : TypesIIIIIIVSetup M) : Set (IrreducibleCharacter ↥(huSub data)) :=
  { χ | ¬ ((hInHu data : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ)) }

/-- **Peterfalvi (9.5)'s family `𝒳(Y)`**: the members of `𝒳` containing `Y` in their kernel.  For
`Y ≤ HU`, `Y` is realised inside `HU` as `(Y.subgroupOf M).subgroupOf (huSub data)`. -/
def xiOf (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    Set (IrreducibleCharacter ↥(huSub data)) :=
  { χ ∈ xiSet data | ((Y.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) }

theorem xiOf_subset_xiSet (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    xiOf data Y ⊆ xiSet data :=
  fun _ h => h.1

theorem mem_xiOf {data : TypesIIIIIIVSetup M} {Y : Subgroup G}
    {χ : IrreducibleCharacter ↥(huSub data)} :
    χ ∈ xiOf data Y ↔ χ ∈ xiSet data ∧
      ((Y.subgroupOf M).subgroupOf (huSub data) : Set ↥(huSub data)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

/-- `𝒳(Y)` is antitone in `Y`: a larger kernel demand `Y ⊆ Ker χ` selects fewer characters. -/
theorem xiOf_antitone (data : TypesIIIIIIVSetup M) {Y Y' : Subgroup G} (hY : Y ≤ Y') :
    xiOf data Y' ⊆ xiOf data Y := fun _ hχ =>
  ⟨hχ.1, subset_trans (SetLike.coe_subset_coe.mpr
    (Subgroup.subgroupOf_mono (huSub data) (Subgroup.subgroupOf_mono M hY))) hχ.2⟩

/-- `Ind_{HU}^M χ`, the induction of a class function of `HU = H ⊔ U` to `↥M`.  The required
`Invertible (Nat.card ↥HU : ℂ)` is constructed from `[Finite G]` and baked in here so that `sSet`
and `sOf` share one canonical instance (avoiding the induce-instance desync). -/
noncomputable def induceHU [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) : ClassFunction ↥M ℂ :=
  letI : Fintype ↥M := Fintype.ofFinite _
  letI : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  ClassFunction.induce (huSub data) χ

/-- The induced degree: `(Ind_{HU}^M χ)(1) = [M : HU] · χ(1)` (Peterfalvi's `Ind` raises degrees by
the index `[M : HU]`). -/
theorem induceHU_apply_one [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ (1 : ↥M) = ((huSub data).index : ℂ) * χ (1 : ↥(huSub data)) := by
  let : Fintype ↥M := Fintype.ofFinite _
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ClassFunction.induce_apply_one (huSub data) χ

/-- **`[M : HU] = q = |W₁|`.**  `HU = H ⊔ U = M' = derivedInG M` (the type-`P` complementarity
`derived_complement`, `derivedInG_eq_fitting_sup_U`), and `W₁` complements `M'` in `M`
(`M_complement`), so `[M : HU] = [M : M'] = |W₁| = q`.  This pins the index that
`induceHU_apply_one` leaves abstract: every `𝒮`-member `Ind_{HU}^M χ` has degree `q · χ(1)`. -/
theorem huSub_index_eq_q [Finite G] (data : TypesIIIIIIVSetup M) :
    (huSub data).index = data.q := by
  have hsup : data.H ⊔ data.U = derivedInG M := by
    simp only [TypesIIIIIIVSetup.H, TypesIIIIIIVSetup.U]
    rw [data.typeP.derivedInG_eq_fitting_sup_U, data.typeP.H_eq]
  have hidx : ((derivedInG M).subgroupOf M).index = data.q := by
    simp only [TypesIIIIIIVSetup.q, TypesIIIIIIVSetup.W1]
    rw [data.typeP.M_complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeP.W1_le).toEquiv]
  change ((data.H ⊔ data.U).subgroupOf M).index = data.q
  rw [hsup]; exact hidx

/-- The induced degree, with the index resolved: `(Ind_{HU}^M χ)(1) = q · χ(1)` (`q = |W₁|`).  This
is the degree formula the §9 counts (9.8)/(9.9) use directly (`𝒮`-members of source degree `s` have
degree `q·s`, e.g. `qu`, `qa`). -/
theorem induceHU_apply_one_eq_q_mul [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : ClassFunction ↥(huSub data) ℂ) :
    induceHU data χ (1 : ↥M) = (data.q : ℂ) * χ (1 : ↥(huSub data)) := by
  rw [induceHU_apply_one, huSub_index_eq_q]

/-- **Peterfalvi (9.5)'s family `𝒮`**: `{Ind_{HU}^M χ | χ ∈ 𝒳}`. -/
noncomputable def sSet [Finite G] (data : TypesIIIIIIVSetup M) : Set (ClassFunction ↥M ℂ) :=
  { φ | ∃ χ ∈ xiSet data, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) }

/-- **Peterfalvi (9.5)'s family `𝒮(Y)`**: `{Ind_{HU}^M χ | χ ∈ 𝒳(Y)}`. -/
noncomputable def sOf [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    Set (ClassFunction ↥M ℂ) :=
  { φ | ∃ χ ∈ xiOf data Y, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) }

theorem mem_sOf [Finite G] {data : TypesIIIIIIVSetup M} {Y : Subgroup G}
    {φ : ClassFunction ↥M ℂ} :
    φ ∈ sOf data Y ↔ ∃ χ ∈ xiOf data Y, φ = induceHU data (χ : ClassFunction ↥(huSub data) ℂ) :=
  Iff.rfl

/-- `𝒮(Y) ⊆ 𝒮`: every character induced from `𝒳(Y)` is induced from `𝒳` (since `𝒳(Y) ⊆ 𝒳`). -/
theorem sOf_subset_sSet [Finite G] (data : TypesIIIIIIVSetup M) (Y : Subgroup G) :
    sOf data Y ⊆ sSet data := fun _ ⟨χ, hχ, hφ⟩ =>
  ⟨χ, xiOf_subset_xiSet data Y hχ, hφ⟩

open OddOrder.Peterfalvi.S11 in
/-- **`𝒮(⊥) = 𝒮`** (issue 1017; relocated from S15 to §11 for the (10.11) type-II consumer,
issue 1048): the `⊥`-kernel demand of `𝒮(Y)` is vacuous — only
the identity lies in `⊥`, and `1 ∈ Ker χ` always — so every `Ind_{HU}^M ξ ∈ 𝒮` already lies in
`𝒮(⊥)`.  Generic in `data` (the collapse core extracted from the linchpin `sSet_eq_sOf_H0Cprime`);
it identifies the degenerate `S`-instance kernel strata (`H₀ = C′ = U′ = ⊥`) with the full
family. -/
theorem sOf_bot_eq_sSet {M : Subgroup G} [Finite G] (data : TypesIIIIIIVSetup M) :
    sOf data (⊥ : Subgroup G) = sSet data := by
  apply Set.Subset.antisymm (sOf_subset_sSet _ _)
  rintro φ ⟨χ, hχ, rfl⟩
  refine ⟨χ, ?_, rfl⟩
  rw [mem_xiOf]
  refine ⟨hχ, ?_⟩
  intro x hx
  have hx1 : x = 1 := by
    have h2 := Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp (SetLike.mem_coe.mp hx))
    rw [Subgroup.mem_bot] at h2
    exact Subtype.ext (Subtype.ext h2)
  rw [hx1, OddOrder.Peterfalvi.S03.mem_characterKernel,
    OddOrder.Peterfalvi.S03.characterDegree_def]

/-- `𝒮(Y)` is antitone in `Y` (inherited from `xiOf_antitone`). -/
theorem sOf_antitone [Finite G] (data : TypesIIIIIIVSetup M) {Y Y' : Subgroup G} (hY : Y ≤ Y') :
    sOf data Y' ⊆ sOf data Y := fun _ ⟨χ, hχ, hφ⟩ =>
  ⟨χ, xiOf_antitone data hY hχ, hφ⟩

/-- Every `𝒮`-member is a genuine virtual character of `M`: `Ind_{HU}^M χ ∈ ℤ[Irr M]` for
`χ ∈ Irr(HU)` (`ClassFunction.induce_mem_ZIrr`).  This is the foundation on which the (9.8)/(9.9)
degree and inner-product counts treat `𝒮`-members as characters. -/
theorem induceHU_mem_ZIrr [Finite G] (data : TypesIIIIIIVSetup M)
    (χ : IrreducibleCharacter ↥(huSub data)) :
    induceHU data (χ : ClassFunction ↥(huSub data) ℂ) ∈ ZIrr ↥M := by
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥(huSub data) := Fintype.ofFinite _
  let : Invertible (Nat.card ↥M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let : Invertible (Nat.card ↥(huSub data) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact ClassFunction.induce_mem_ZIrr (huSub data) χ.mem_ZIrr

/-- `𝒮 ⊆ ℤ[Irr M]`: the whole induced family consists of virtual characters of `M`. -/
theorem sSet_subset_ZIrr [Finite G] (data : TypesIIIIIIVSetup M) :
    sSet data ⊆ (ZIrr ↥M : Set (ClassFunction ↥M ℂ)) := by
  rintro _ ⟨χ, -, rfl⟩
  exact induceHU_mem_ZIrr data χ

/-- The `U`-action on the chief factor `H̄ = ↥H ⧸ N` (Peterfalvi (9.5)), as the hom from `U`
(realised
inside `U ⊔ W₁`) to `Aut(H̄)`.  Its range has order `u` (`u_eq_card_quotient`); its kernel is
`C = C_U(H̄)`. -/
noncomputable def uActionHom (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :=
  (quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
    (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype

/-- **Peterfalvi's `C = C_U(H̄)`** (9.5): the kernel of the `U`-action on the chief factor `H̄`,
realised as a subgroup of `G` with `C ≤ U`.  By the first isomorphism theorem `|U : C| = u`
(`u_eq_card_quotient`'s range). -/
noncomputable def cSub (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) : Subgroup G :=
  ((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

theorem cSub_le_U (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cSub data chief ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

/-- **Peterfalvi's `U' = [U, U]`** (9.5), realised in `G` as `derivedInG U`. -/
def uprimeSub (data : TypesIIIIIIVSetup M) : Subgroup G := derivedInG data.U

theorem uprimeSub_le_U (data : TypesIIIIIIVSetup M) : uprimeSub data ≤ data.U :=
  Subgroup.map_subtype_le _

/-- **Peterfalvi's `C' = [C, C]`** (9.5), realised in `G` as `derivedInG C`. -/
noncomputable def cprimeSub (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) : Subgroup
    G :=
  derivedInG (cSub data chief)

theorem cprimeSub_le_C (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cprimeSub data chief ≤ cSub data chief :=
  Subgroup.map_subtype_le _

open Subgroup in
/-- **`C = C_U(H̄)` realised inside `↥U`**: `C.subgroupOf U` is the image of `ker (uActionHom)`
under the realization isomorphism `subgroupOfEquivOfLe : ↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`.

Extracted from `cSub_subgroupOf_U_normal` so that the (9.6) clause `U ≠ C`
(`chiefFactor_cSub_ne_U`) can read the kernel off the same identification. -/
theorem cSub_subgroupOf_U_eq_ker_map (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    (cSub data chief).subgroupOf data.U
      = (uActionHom data chief).ker.map
          (subgroupOfEquivOfLe
            (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toMonoidHom := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  ext x
  simp only [Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    simp only [cSub, Subgroup.mem_map] at hx
    obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
    refine ⟨y, hy, ?_⟩
    apply Subtype.ext
    rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
    rfl
  · rintro ⟨y, hy, rfl⟩
    simp only [cSub, Subgroup.mem_map]
    refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
    rfl

open Subgroup in
/-- **`C = C_U(H̄) ◁ U`** (Peterfalvi (9.5)): the kernel of the `U`-action on the chief factor is
normal in `U`.  `cSub` is the `G`-image of `(uActionHom).ker`, which corresponds (via the
realization iso `subgroupOfEquivOfLe : ↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`) to a kernel of a
homomorphism out of `↥U`; kernels are normal.  This is the `C ◁ U` input of the (9.9.a) carrier
normality `HC ◁ HU` (`sup_normal_of_normal_left_of_normal_subgroupOf`). -/
theorem cSub_subgroupOf_U_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    ((cSub data chief).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  rw [cSub_subgroupOf_U_eq_ker_map]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

/-- **`U W₁ ≤ N_G(C)`** (the `W₁`-half of the `H₀C ◁ M` normality, issue 1012): the `U W₁`-action on
the chief factor `H̄ = ↥H ⧸ N` is defined on *all* of `U ⊔ W₁` (`quotientMulAutHom`, built from
`typeP_conjAction : U ⊔ W₁ → MulAut ↥H`), so `C = C_U(H̄)` realises inside `L = ↥(U ⊔ W₁)` as the
intersection `U' ⊓ ker(quotientMulAutHom)` of two `L`-normal subgroups (`U' = U.subgroupOf L` normal
by the Frobenius structure `typeP_uW1_frobenius`, the action kernel normal as a kernel).  A normal
subgroup of `L` is normalized by all of `L = ↑(U ⊔ W₁)` once pushed forward along `L.subtype`
(`le_normalizer_map`, `normalizer_eq_top`).  Unlike the `H`-conjugation (which only gives
`[C, H] ≤ H₀`, i.e. `H ≤ N(H₀C)` not `H ≤ N(C)`), `W₁` normalizes `C` *exactly*. -/
theorem cSub_normalized_by_uW1 [Finite G] (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    data.typeP.U ⊔ data.typeP.W1 ≤ Subgroup.normalizer (cSub data chief : Set G) := by
  have hU : data.typeP.U ≠ ⊥ := data.nontrivial.1
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (typeP_uW1_frobenius data.typeP hU).isNormal
  have hKnorm : (quotientMulAutHom chief.N_aInvariant).ker.Normal := MonoidHom.normal_ker _
  have hInfNorm : ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊓ (quotientMulAutHom chief.N_aInvariant).ker).Normal :=
    Subgroup.normal_inf_normal _ _
  -- `C` realised in `L = ↥(U ⊔ W₁)` is `U' ⊓ ker(quotientMulAutHom)`.
  have hinner : (uActionHom data chief).ker.map
        (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype
      = (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
          ⊓ (quotientMulAutHom chief.N_aInvariant).ker := by
    rw [show (uActionHom data chief).ker
          = (quotientMulAutHom chief.N_aInvariant).ker.comap
              (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype from
        (MonoidHom.comap_ker _ _).symm,
      Subgroup.map_comap_eq, Subgroup.range_subtype]
  have hcSub : cSub data chief
      = ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
            ⊓ (quotientMulAutHom chief.N_aInvariant).ker).map
          (data.typeP.U ⊔ data.typeP.W1).subtype := by
    unfold cSub
    rw [hinner]
  rw [hcSub]
  have h1 := Subgroup.le_normalizer_map
    (H := (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
      ⊓ (quotientMulAutHom chief.N_aInvariant).ker)
    (data.typeP.U ⊔ data.typeP.W1).subtype
  rwa [Subgroup.normalizer_eq_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1

open scoped IsMulCommutative in
/-- **`C_U(H) ≤ C = C_U(H̄)`** (`U ∩ centralizer H ≤ cSub`): a `U`-element centralizing `H` (in `G`)
acts trivially on the chief factor quotient `H̄ = H/N`, hence lies in `ker(uActionHom)`, i.e. in
`C = cSub`.  Centralizing `H` pointwise makes conjugation trivial on every coset `hN`, so the
induced
automorphism of `H̄` is the identity.  This is the containment `[U,U] ≤ C(H) ⟹ U' ≤ C` behind
Peterfalvi (9.8.d)'s `U' ≤ C_U(S₀)` and the (9.9) `C' = [C,C]` normality inputs. -/
theorem mem_cSub_of_mem_U_of_centralizes [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) {x : G}
    (hxU : x ∈ data.typeP.U) (hxC : x ∈ Subgroup.centralizer (data.typeP.H : Set G)) :
    x ∈ cSub data chief := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  have hxUW1 : x ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hxU
  -- the `U`-action element with `G`-coordinate `x`
  set a : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    ⟨⟨x, hxUW1⟩, Subgroup.mem_subgroupOf.mpr hxU⟩ with ha_def
  -- `a ∈ ker(uActionHom)`: conjugation by `x ∈ C(H)` is trivial on `H`, hence on `H̄`.
  have hker : a ∈ (uActionHom data chief).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | _ h =>
      rw [uActionHom, MonoidHom.comp_apply,
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        MulAut.one_apply]
      -- conjugation by `x` fixes `h` since `x` centralizes `H`
      have hfix : (typeP_conjAction data.typeP
          ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a) h) = h := by
        apply Subtype.ext
        rw [typeP_conjAction_apply]
        have hcom : (h : G) * x = x * (h : G) :=
          (Subgroup.mem_centralizer_iff.mp hxC) (h : G) h.2
        change x * (h : G) * x⁻¹ = (h : G)
        rw [← hcom, mul_assoc, mul_inv_cancel, mul_one]
      rw [hfix]
  simp only [cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

/-- **`U' = [U,U] ≤ C = C_U(H̄)`** (`uprimeSub ≤ cSub`, Peterfalvi (9.5)/(8.5.b)): the derived
subgroup of `U` centralizes `H` (`typeP_commutator_U_centralizes_H`) and lies in `U`
(`uprimeSub_le_U`), so by `mem_cSub_of_mem_U_of_centralizes` it lies in `C`.  Peterfalvi cites this
as "(8.5.b): `U'` centralizes `H`". -/
theorem uprimeSub_le_cSub [Finite G] {M : Subgroup G}
    (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    uprimeSub data ≤ cSub data chief := by
  intro x hx
  refine mem_cSub_of_mem_U_of_centralizes data chief (uprimeSub_le_U data hx) ?_
  have hxUU : x ∈ ⁅data.U, data.U⁆ := by
    rw [uprimeSub, derivedInG, commutator_def, Subgroup.map_commutator] at hx
    simpa only [← data.U.subtype.range_eq_map, Subgroup.range_subtype] using hx
  exact typeP_commutator_U_centralizes_H data.typeP hxUU

/-- `H ⊴ HU`: the realization `hInHu data = (H.subgroupOf M).subgroupOf HU` of `H = M_F` inside
`HU` is normal (`M_F ◁ M`, descended along the inclusions). -/
instance hInHu_normal {M : Subgroup G} (data : TypesIIIIIIVSetup M) :
    (hInHu data).Normal := by
  have h1 : (data.H.subgroupOf M).Normal := by
    rw [show data.H = maxNilpotentNormalHall M from data.typeP.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal M
  exact h1.subgroupOf (huSub data)

theorem U_le_M (data : TypesIIIIIIVSetup M) : data.U ≤ M :=
  data.typeP.U_le.trans (Subgroup.map_subtype_le _)

theorem H_le_M (data : TypesIIIIIIVSetup M) : data.H ≤ M :=
  data.typeP.H_le.trans (Subgroup.map_subtype_le _)

/-- `U`, realized as a subgroup of `HU = H ⊔ U` inside `↥M`. -/
noncomputable def uInHu (data : TypesIIIIIIVSetup M) : Subgroup ↥(huSub data) :=
  (data.U.subgroupOf M).subgroupOf (huSub data)

/-- `C = C_U(H̄)`, realized as a subgroup of `HU` inside `↥M`. -/
noncomputable def cInHu (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Subgroup ↥(huSub data) :=
  ((cSub data chief).subgroupOf M).subgroupOf (huSub data)

theorem cInHu_le_uInHu (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    cInHu data chief ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _ (cSub_le_U data chief))

/-- **`H ⊓ C = ⊥` inside `HU`** (realized `hInHu ⊓ cInHu = ⊥`): `C ≤ U` and `H ⊓ U = ⊥`
(`typeP_H_inf_U`), so `H ⊓ C ≤ H ⊓ U = ⊥`.  A foundational input for the second-isomorphism
`HC/H₀C ≅ H̄` behind the (9.8.c) irreducible-character construction. -/
theorem hInHu_inf_cInHu_eq_bot {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) : hInHu data ⊓ cInHu data chief = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxU := cInHu_le_uInHu data chief hxC
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

open Subgroup in
set_option backward.isDefEq.respectTransparency false in
/-- **`C ◁ U` inside `HU`** (realized form): `cInHu ◁ uInHu`, transported from `cSub ◁ U`
(`cSub_subgroupOf_U_normal`) along the realization iso `↥uInHu ≃* ↥U`.  Comap of a normal subgroup
is normal. -/
theorem cInHu_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    ((cInHu data chief).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cInHu data chief).subgroupOf (uInHu data)
      = ((cSub data chief).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cInHu, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cSub_subgroupOf_U_normal data chief).comap f.toMonoidHom

open Subgroup in
/-- **`H ⊔ U = ⊤` inside `HU`** (realized form): `hInHu ⊔ uInHu = ⊤`, since `HU = H ⊔ U`.  Both
`H.subgroupOf M` and `U.subgroupOf M` lie below `huSub = (H ⊔ U).subgroupOf M`, and `subgroupOf`
distributes over `⊔` for subgroups below the ambient (`subgroupOf_sup`), so the realized join is
`((H ⊔ U).subgroupOf M).subgroupOf (huSub) = huSub.subgroupOf huSub = ⊤`. -/
theorem hInHu_sup_uInHu_eq_top (data : TypesIIIIIIVSetup M) :
    hInHu data ⊔ uInHu data = ⊤ := by
  have hHsub : data.H.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_left
  have hUsub : data.U.subgroupOf M ≤ huSub data := Subgroup.subgroupOf_mono M le_sup_right
  unfold hInHu uInHu
  rw [← subgroupOf_sup hHsub hUsub, ← subgroupOf_sup (H_le_M data) (U_le_M data)]
  exact Subgroup.subgroupOf_self _

/-- **Peterfalvi (9.9.a), the inertia subgroup is normal: `HC ◁ HU`.**  Realized as
`hInHu ⊔ cInHu ◁ huSub`, by the abstract `sup_normal_of_normal_left_of_normal_subgroupOf`:
`H ◁ HU` (`hInHu_normal`), `C ◁ U` (`cInHu_normal`), `H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`).  This
is
the normality `isIrreducibleCharacter_induce_of_inertia_eq` needs to make `Ind_{HC}^{HU} ψ`
irreducible in the (9.9.a) Clifford-degree argument. -/
theorem hcInHu_normal (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    (hInHu data ⊔ cInHu data chief).Normal :=
  haveI := hInHu_normal data
  haveI := cInHu_normal data chief
  sup_normal_of_normal_left_of_normal_subgroupOf (cInHu_le_uInHu data chief)
    (hInHu_sup_uInHu_eq_top data)

section

open scoped IsMulCommutative

/-- **`H ⊓ U ≤ C = C_U(H̄)`** (realized form `hInHu ⊓ uInHu ≤ cInHu`).  An element lying in both
`H` and `U` centralizes the chief factor `H̄ = H/H₀`: conjugation by an `H`-element descends to an
inner automorphism of the *abelian* `H̄`, hence is trivial, so the element lies in
`C = ker(U → Aut H̄)`.  This is the index input of (9.9.a)'s `[HU : HC] = u`. -/
theorem hInHu_inf_uInHu_le_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    hInHu data ⊓ uInHu data ≤ cInHu data chief := by
  have : IsMulCommutative (↥data.H ⧸ chief.N) := ⟨⟨chief.quotient_elementaryAbelian.1⟩⟩
  intro x hx
  obtain ⟨hxH, hxU⟩ := hx
  have hgH : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.H := by
    simp only [hInHu] at hxH; exact hxH
  have hgU : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hxU; exact hxU
  have hgUW1 : (((x : ↥(huSub data)) : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 :=
    Subgroup.mem_sup_left hgU
  -- the `U`-action element with the same `G`-coordinate
  set a : ↥(data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    ⟨⟨(((x : ↥(huSub data)) : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  -- `a ∈ ker(uActionHom)`: conjugation by an `H`-element is trivial on the abelian `H̄`.
  have hker : a ∈ (uActionHom data chief).ker := by
    rw [MonoidHom.mem_ker]
    ext q
    induction q using QuotientGroup.induction_on with
    | _ h =>
      rw [uActionHom, MonoidHom.comp_apply,
        OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        MulAut.one_apply]
      have hconj : (typeP_conjAction data.typeP
          ((data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype a) h)
          = (⟨_, hgH⟩ : ↥data.H) * h * (⟨_, hgH⟩ : ↥data.H)⁻¹ := by
        apply Subtype.ext
        rw [typeP_conjAction_apply]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      rw [hconj]
      simp only [← QuotientGroup.mk'_apply, map_mul, map_inv]
      rw [mul_comm (QuotientGroup.mk' chief.N ⟨_, hgH⟩) (QuotientGroup.mk' chief.N h),
        mul_assoc, mul_inv_cancel, mul_one]
  simp only [cInHu, Subgroup.mem_subgroupOf, cSub, Subgroup.mem_map]
  exact ⟨_, ⟨a, hker, rfl⟩, rfl⟩

end

/-- **`U ⊓ HC = C`** (realized: `uInHu ⊓ (hInHu ⊔ cInHu) = cInHu`).  The `U`-part of the inertia
subgroup `HC` is exactly `C`.  `⊇` is `C ≤ U` and `C ≤ HC`; `⊆` decomposes `x = h·c`
(`H ◁ HU`, `mem_sup_of_normal_left`) with `c ∈ C ≤ U`, so `h = x·c⁻¹ ∈ U`, whence
`h ∈ H ⊓ U ≤ C` (`hInHu_inf_uInHu_le_cInHu`) and `x = h·c ∈ C`.  This is the `[HU:HC] = [U:C]`
input of (9.9.a). -/
theorem uInHu_inf_hcInHu_eq_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    uInHu data ⊓ (hInHu data ⊔ cInHu data chief) = cInHu data chief := by
  have := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cInHu_le_uInHu data chief ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cInHu data chief :=
      hInHu_inf_uInHu_le_cInHu data chief (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩)
    exact (cInHu data chief).mul_mem hh_c ccmem
  · exact le_inf (cInHu_le_uInHu data chief) le_sup_right

/-- **(9.9.a) index step (A): `[HU:HC] = [U:C]` realized form
`HC.index = (cInHu.subgroupOf uInHu).index`.**
The second isomorphism theorem for `HC ◁ HU` with `uInHu ⊔ HC = ⊤`:
`HU ⧸ HC ≃ uInHu ⧸ (uInHu ⊓ HC)`,
and `uInHu ⊓ HC = cInHu` (`uInHu_inf_hcInHu_eq_cInHu`). -/
theorem index_hcInHu_eq_relindex_cInHu [Finite G] {M : Subgroup G} (data : TypesIIIIIIVSetup M)
    (chief : ChiefFactorData data) :
    (hInHu data ⊔ cInHu data chief).index
      = ((cInHu data chief).subgroupOf (uInHu data)).index := by
  have : (hInHu data ⊔ cInHu data chief).Normal := hcInHu_normal data chief
  have htop : uInHu data ⊔ (hInHu data ⊔ cInHu data chief) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cInHu data chief)).toEquiv
  -- The iso's source denominator `HC.subgroupOf uInHu = cInHu.subgroupOf uInHu` (by `U ⊓ HC = C`).
  have hsub : (hInHu data ⊔ cInHu data chief).subgroupOf (uInHu data)
      = (cInHu data chief).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data)) ∈ uInHu data ⊓ (hInHu data ⊔ cInHu data chief) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcInHu_eq_cInHu data chief] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  -- `he : Nat.card (↥uInHu ⧸ cInHu.subgroupOf uInHu)
  --       = Nat.card (↥(uInHu ⊔ HC) ⧸ HC.subgroupOf (uInHu ⊔ HC))`
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cInHu data chief).subgroupOf (uInHu data ⊔ (hInHu data ⊔ cInHu data chief)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cInHu data chief) ≤ uInHu data ⊔ (hInHu data ⊔ cInHu data chief))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  -- `hsplit : Nat.card ↥(uInHu ⊔ HC) = (cInHu.subgroupOf uInHu).index * Nat.card ↥HC`
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cInHu data chief))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  -- `hsplit : Nat.card ↥(huSub) = (cInHu.subgroupOf uInHu).index * Nat.card ↥HC`
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cInHu data chief)
  rw [hsplit, mul_comm (((cInHu data chief).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- `|uInHu| = |U|` (the realization `uInHu = (U.subgroupOf M).subgroupOf HU`). -/
theorem card_uInHu_eq (data : TypesIIIIIIVSetup M) :
    Nat.card ↥(uInHu data) = Nat.card ↥data.U := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  calc Nat.card ↥(uInHu data)
      = Nat.card ↥(data.U.subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUsubM).toEquiv
    _ = Nat.card ↥data.U := Nat.card_congr (Subgroup.subgroupOfEquivOfLe (U_le_M data)).toEquiv

/-- `|cInHu| = |C|` (the realization `cInHu = (cSub.subgroupOf M).subgroupOf HU`). -/
theorem card_cInHu_eq (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Nat.card ↥(cInHu data chief) = Nat.card ↥(cSub data chief) := by
  have hCsubM : (cSub data chief).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M
      ((cSub_le_U data chief).trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cSub data chief ≤ M := (cSub_le_U data chief).trans (U_le_M data)
  calc Nat.card ↥(cInHu data chief)
      = Nat.card ↥((cSub data chief).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cSub data chief) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

/-- `|C| = |ker(uActionHom)|`: `cSub` is the injective double-image of the kernel. -/
theorem card_cSub_eq_card_ker (data : TypesIIIIIIVSetup M) (chief : ChiefFactorData data) :
    Nat.card ↥(cSub data chief) = Nat.card ↥(uActionHom data chief).ker := by
  change Nat.card ↥(((uActionHom data chief).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype) = Nat.card ↥(uActionHom data chief).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

end OddOrder.Peterfalvi.S11


