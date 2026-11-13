-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenSetup
-- name    : OddOrder_Peterfalvi_S11_NineElevenSetup
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:22:28.84984+00:00
-- url     : https://prove2.me/theorems/746f4f41-b97a-4168-b891-343f05c627fa
-- title:
--   Peterfalvi (9.11): coherence, setup layer
-- statement:
--   The setup layer of the Peterfalvi (9.11) coherence argument, introducing the generic single-factor centralizer $C_U(H_j)$.
--
--   Main declarations: `cuSubOf` (The generic single-factor centralizer `C_U(H_j)`); `card_cuSubOf_eq_card_ker` (`|C_U(H_j)| = |ker(aInvariantRestrictAut H_j)|` (mirrors `card_cuSub_eq_card_ker`)); `cuInHuPair` (The realized two-summand centralizer `C_U(H_i) ∩ C_U(H_j)` inside `HU`); `cuInHuPair_le_uInHu` (`C_U(H_i) ∩ C_U(H_j) ≤ U` realized inside `HU` (mirrors `cuInHu_le_uInHu`)).
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenSetup.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenSetup.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_SingleFactorCentralizer

namespace OddOrder.Peterfalvi.S11

open OddOrder.RepresentationTheory

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped Pointwise

variable {G : Type*} [Group G]

section NineElevenTwoInertia

open OddOrder.Isaacs.Ch03 (IsAInvariant isAInvariant_iff_smul_mem)

variable [Finite G] {M : Subgroup G}

/-- **The generic single-factor centralizer `C_U(H_j)`** for an arbitrary Clifford summand
`H_j = caseA.Hpart j`, realized as a subgroup of `G` with `C_U(H_j) ≤ U`.  Mirror of `cuSub`
(which is `C_U(S₀)` for the distinguished generator): the kernel of the restricted `U`-action
`aInvariantRestrictAut (caseA.Hpart_aInvariant j)` on the order-`p` factor `H_j`, pushed into `G`
along `↥(U.subgroupOf (U ⊔ W₁)) ↪ ↥(U ⊔ W₁) ↪ G`.  By orbit symmetry `[U : C_U(H_j)] = a`
(`relIndex_cuSubOf_U_eq_a`), the same index as `C_U(S₀)`. -/
noncomputable def cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) : Subgroup G :=
  ((aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
    (data.typeP.U ⊔ data.typeP.W1).subtype

omit [Finite G] in
theorem cuSubOf_le_U {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) : cuSubOf caseA j ≤ data.U :=
  (Subgroup.map_mono (Subgroup.map_subtype_le _)).trans <| by
    rw [Subgroup.subgroupOf_map_subtype]; exact inf_le_left

omit [Finite G] in
/-- `|C_U(H_j)| = |ker(aInvariantRestrictAut H_j)|` (mirrors `card_cuSub_eq_card_ker`). -/
theorem card_cuSubOf_eq_card_ker {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    Nat.card ↥(cuSubOf caseA j)
      = Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker := by
  change Nat.card ↥(((aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker.map
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).map
        (data.typeP.U ⊔ data.typeP.W1).subtype)
      = Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]

/-- **`ker(uActionHom) ≤ ker(aInvariantRestrictAut H_j)`**: an element acting trivially on the
whole chief factor acts trivially on the summand `H_j` (mirrors
`ker_uActionHom_le_ker_aInvariantRestrictAut` for `S₀`, via
`centralizes_all_imp_centralizes_summand`). -/
theorem ker_uActionHom_le_ker_Hpart {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    (uActionHom data chief).ker ≤ (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg ⊢
  exact centralizes_all_imp_centralizes_summand caseA j g hg

/-- **`C = C_U(H̄) ≤ C_U(H_j)`** (`cSub ≤ cuSubOf`, mirrors `cSub_le_cuSub`). -/
theorem cSub_le_cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) : cSub data chief ≤ cuSubOf caseA j :=
  Subgroup.map_mono (Subgroup.map_mono (ker_uActionHom_le_ker_Hpart caseA j))

/-- **Orbit symmetry of the Clifford index `a`.**  For *any* summand `H_j = caseA.Hpart j` the
order of the `U`-action image on `H_j` equals `caseA.a` (`= |Ū₁|`, the image on the distinguished
generator `S₀`).  Since `H_j = φ(orbitRep j) • S₀` is the automorphic image of `S₀` under
`w = φ(orbitRep j)`, conjugation `σ = conjNormal w⁻¹` (well-defined on the acting group because
`U ◁ U W₁` is the Frobenius kernel, `W1_normalizes_U`) is an automorphism of the acting `U`-group
carrying `ker(restrict on S₀)` to `ker(restrict on H_j)`; equal kernels force equal ranges (first
isomorphism `|U| = |range|·|ker|` on both).  This is the crux behind `[U : C_U(H_j)] = a` for a
general summand (`relIndex_cuSubOf_U_eq_a`). -/
theorem caseA_a_eq_card_Hpart_restrictAut_range {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (j : Fin data.q) :
    caseA.a = Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).range := by
  classical
  set L := data.typeP.U ⊔ data.typeP.W1 with hL
  -- `U ◁ L` (Frobenius kernel), so conjugation by `L`-elements permutes the acting group `U`.
  have hAnorm : (data.typeP.U.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U)
  set wt : ↥L := caseA.orbitRep j with hwt
  set w : MulAut (↥data.H ⧸ chief.N) := quotientMulAutHom chief.N_aInvariant wt with hw
  set σ : MulAut ↥(data.typeP.U.subgroupOf L) := MulAut.conjNormal (wt⁻¹) with hσ
  have hHj : caseA.Hpart j = w • caseA.S0 := caseA.Hpart_orbit j
  -- Pointwise-fix characterisation of `restrict … = 1`.
  have hchar : ∀ (S : Subgroup (↥data.H ⧸ chief.N))
      (hS : IsAInvariant (uActionHom data chief) S)
      (a : ↥(data.typeP.U.subgroupOf L)),
      aInvariantRestrictAut hS a = 1 ↔ ∀ y ∈ S, (uActionHom data chief) a y = y := by
    intro S hS a
    constructor
    · intro h y hy
      have hcoe := aInvariantRestrictAut_coe hS a ⟨y, hy⟩
      rw [h] at hcoe
      simpa [MulAut.one_apply] using hcoe.symm
    · intro h
      ext z
      rw [MulAut.one_apply, aInvariantRestrictAut_coe]
      exact h _ z.2
  -- `σ`-conjugation of the action: `φ(σ a) x = w⁻¹ (φ a (w x))`.
  have hσφ : ∀ (a : ↥(data.typeP.U.subgroupOf L)) (x : ↥data.H ⧸ chief.N),
      (uActionHom data chief) (σ a) x = w⁻¹ ((uActionHom data chief) a (w x)) := by
    intro a x
    have hval : ((σ a : ↥(data.typeP.U.subgroupOf L)) : ↥L) = wt⁻¹ * (a : ↥L) * wt := by
      rw [hσ, MulAut.conjNormal_apply, inv_inv]
    have h1 : (uActionHom data chief) (σ a)
        = quotientMulAutHom chief.N_aInvariant
            ((σ a : ↥(data.typeP.U.subgroupOf L)) : ↥L) := rfl
    rw [h1, hval, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
    rfl
  -- Kernel correspondence `ker(H_j) = ker(S₀).comap σ`.
  have hker : (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
      = (aInvariantRestrictAut caseA.S0_aInvariant).ker.comap σ.toMonoidHom := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker, MulEquiv.coe_toMonoidHom,
      hchar (caseA.Hpart j) (caseA.Hpart_aInvariant j) a,
      hchar caseA.S0 caseA.S0_aInvariant (σ a)]
    constructor
    · intro h x hx
      rw [hσφ a x]
      have hxHj : w x ∈ caseA.Hpart j := by
        rw [hHj, ← MulAut.smul_def]
        exact Subgroup.smul_mem_pointwise_smul_iff.mpr hx
      rw [h (w x) hxHj, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    · intro h y hy
      rw [hHj] at hy
      have hx : w⁻¹ • y ∈ caseA.S0 := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hy
      have hfix := h (w⁻¹ • y) hx
      rw [hσφ a (w⁻¹ • y), MulAut.smul_def] at hfix
      have hww : w (w⁻¹ y) = y := by rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
      rw [hww] at hfix
      exact w⁻¹.injective hfix
  -- Equal kernel cardinalities (conjugation `σ` is a bijection).
  have hkercard : Nat.card ↥(aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
      = Nat.card ↥(aInvariantRestrictAut caseA.S0_aInvariant).ker := by
    rw [hker, Subgroup.comap_equiv_eq_map_symm']
    exact (Nat.card_congr (Subgroup.equivMapOfInjective _ σ.symm.toMonoidHom
      σ.symm.injective).toEquiv).symm
  -- Equal range cardinalities via the first isomorphism `|U| = |range|·|ker|`.
  have h0 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut caseA.S0_aInvariant).ker
  have hj := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (aInvariantRestrictAut caseA.S0_aInvariant)).toEquiv] at h0
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
    (aInvariantRestrictAut (caseA.Hpart_aInvariant j))).toEquiv] at hj
  rw [caseA.a_eq_card_restrictAut_range]
  have hcancel := h0.symm.trans hj
  rw [hkercard] at hcancel
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hcancel

/-- **`|U| = a · |C_U(H_j)|`** for an arbitrary summand (mirrors `card_U_eq_a_mul_card_cuSub`), via
orbit symmetry `a = |range(aInvariantRestrictAut H_j)|` (`caseA_a_eq_card_Hpart_restrictAut_range`)
and the first isomorphism theorem. -/
theorem card_U_eq_a_mul_card_cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    Nat.card ↥data.U = caseA.a * Nat.card ↥(cuSubOf caseA j) := by
  rw [caseA_a_eq_card_Hpart_restrictAut_range caseA j]
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (aInvariantRestrictAut (caseA.Hpart_aInvariant j))).toEquiv,
    ← card_cuSubOf_eq_card_ker caseA j,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv] at h
  exact h

/-- **`[U : C_U(H_j)] = a`** for an arbitrary Clifford summand `H_j` (mirrors
`relIndex_cuSub_U_eq_a` for `S₀`): Lagrange `[U:C_U(H_j)]·|C_U(H_j)| = |U| = a·|C_U(H_j)|`
(`card_U_eq_a_mul_card_cuSubOf`), cancelling `|C_U(H_j)| > 0`.  The orbit-symmetric per-summand
inertia index behind Peterfalvi (9.11.2). -/
theorem relIndex_cuSubOf_U_eq_a {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (j : Fin data.q) :
    (cuSubOf caseA j).relIndex data.U = caseA.a := by
  have h1 : (cuSubOf caseA j).relIndex data.U * Nat.card ↥(cuSubOf caseA j)
      = Nat.card ↥data.U := by
    have h := Subgroup.index_mul_card ((cuSubOf caseA j).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuSubOf_le_U caseA j)).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos
    (h1.trans (card_U_eq_a_mul_card_cuSubOf caseA j))

/-- **The realized two-summand centralizer `C_U(H_i) ∩ C_U(H_j)` inside `HU`**, as a subgroup of
`↥(huSub data)` (mirrors `cuInHu` for the single generator `S₀`, but with the *pair* intersection
`cuSubOf i ⊓ cuSubOf j` of the two single-factor centralizers). -/
noncomputable def cuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) : Subgroup ↥(huSub data) :=
  ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf M).subgroupOf (huSub data)

omit [Finite G] in
/-- `C_U(H_i) ∩ C_U(H_j) ≤ U` realized inside `HU` (mirrors `cuInHu_le_uInHu`). -/
theorem cuInHuPair_le_uInHu {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) : cuInHuPair caseA i j ≤ uInHu data :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _
    (inf_le_left.trans (cuSubOf_le_U caseA i)))

/-- **Realization bridge**: a `U`-element `a` whose realized `G`-image lies in `cuSubOf caseA k`
acts trivially on the summand `H_k` (`a ∈ ker(aInvariantRestrictAut (Hpart_aInvariant k))`).  The
reverse of the membership-building in `inertia_inf_uInHu_le_cuInHu`: `cuSubOf` is the double
`subtype`-image of the kernel, and the double `subtype` is injective, so the extracted kernel
witness equals `a`. -/
theorem mem_ker_of_realized_mem_cuSubOf {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) (k : Fin data.q)
    (a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U)
    (h : (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G)
        ∈ cuSubOf caseA k) :
    a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant k)).ker := by
  simp only [cuSubOf, Subgroup.mem_map] at h
  obtain ⟨w, ⟨b, hb_ker, hb_w⟩, hw⟩ := h
  have hba : b = a := by
    apply Subgroup.subtype_injective (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1))
    apply Subgroup.subtype_injective (data.typeP.U ⊔ data.typeP.W1)
    rw [hb_w]; exact hw
  rwa [hba] at hb_ker

/-- **(9.11.2) `⊆` half at the `HU`-inertia level: `I(θ₀) ⊓ U ≤ C_U(H_i) ∩ C_U(H_j)`.**  For the
inflation `θ₀` of a chief-factor character `θbar` regular on the two Clifford summands `H_i`, `H_j`,
a realized `U`-element `g` in the `HU`-inertia of `θ₀` lies in the realized two-summand centralizer
`cuInHuPair`.  Realizes `g` as an abstract `U`-element `a`, unwraps the `conjBy`-fixing to the
`compHom (typeP_conjAction)` form (`conjBy_compHom_hInHuEquivH` + the injective inflation iso),
feeds it to the two-summand char-inertia core `caseA_hu_char_inertia_two_summands` (giving
`aInvariantRestrictAut … a = 1` on both summands), and builds the intersection membership from the
two kernel witnesses.  Mirrors the single-factor `inertia_inf_uInHu_le_cuInHu`. -/
theorem inertia_inf_uInHu_le_cuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    {θbar : IrreducibleCharacter (↥data.H ⧸ chief.N)}
    (hregi : ∃ x ∈ caseA.Hpart i, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j, (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
      ≠ (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (θbar : ClassFunction (↥data.H ⧸ chief.N) ℂ))) ⊓ uInHu data
      ≤ cuInHuPair caseA i j := by
  rintro g ⟨hgin, hgu⟩
  have hgU : ((g : ↥M) : G) ∈ data.typeP.U := by
    simp only [uInHu] at hgu; exact hgu
  have hgUW1 : ((g : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨((g : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((g : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hfix := ClassFunction.mem_inertia.mp hgin
  rw [conjBy_compHom_hInHuEquivH data
    ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
    g hag] at hfix
  have hfix1 := ClassFunction.compHom_injective_of_surjective (hInHuEquivH data).surjective hfix
  obtain ⟨hi, hj⟩ := caseA_hu_char_inertia_two_summands caseA hregi hregj a hfix1
  have hkeri : a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant i)).ker :=
    MonoidHom.mem_ker.mpr hi
  have hkerj : a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker :=
    MonoidHom.mem_ker.mpr hj
  simp only [cuInHuPair, Subgroup.mem_subgroupOf, Subgroup.mem_inf, cuSubOf, Subgroup.mem_map]
  exact ⟨⟨_, ⟨a, hkeri, rfl⟩, rfl⟩, ⟨_, ⟨a, hkerj, rfl⟩, rfl⟩⟩

/-- **(9.11.2) `⊇` half at the `HU`-inertia level: `C_U(H_i) ∩ C_U(H_j) ≤ I(θ₀)`.**  For the
inflation `θ₀` of `θbar = linearIrreducibleCharacter χ` with `χ` a two-summand-supported
linear character (trivial off `i`, `j`, `hsupp`), the realized two-summand centralizer
`cuInHuPair` fixes `θ₀`.  A `cuInHuPair`-element `c` realizes an abstract `U`-element `a`
centralizing both summands (`aInvariantRestrictAut … a = 1` on `i` and `j`, via
`mem_ker_of_realized_mem_cuSubOf`), so `caseA_centralizes_two_summands_compHom_eq` gives
`compHom (uActionHom a) θbar = θbar`; inflating (`conjBy_compHom_hInHuEquivH` +
`compHom_typeP_conjAction_inflation`) then fixes `θ₀`.  Mirrors `cInHu_le_inertia`, replacing
`quotientMulAutHom w = 1` with the two-summand char-fixing. -/
theorem cuInHuPair_le_inertia {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1) :
    cuInHuPair caseA i j ≤ ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ))) := by
  intro c hc
  rw [ClassFunction.mem_inertia]
  have hcinf : ((c : ↥M) : G) ∈ cuSubOf caseA i ⊓ cuSubOf caseA j := by
    simpa only [cuInHuPair, Subgroup.mem_subgroupOf] using hc
  have hgU : ((c : ↥M) : G) ∈ data.typeP.U := cuSubOf_le_U caseA i hcinf.1
  have hgUW1 : ((c : ↥M) : G) ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_left hgU
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨((c : ↥M) : G), hgUW1⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha_def
  have hag : ((c : ↥M) : G)
      = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hgi : aInvariantRestrictAut (caseA.Hpart_aInvariant i) a = 1 :=
    MonoidHom.mem_ker.mp (mem_ker_of_realized_mem_cuSubOf caseA i a (hag ▸ hcinf.1))
  have hgj : aInvariantRestrictAut (caseA.Hpart_aInvariant j) a = 1 :=
    MonoidHom.mem_ker.mp (mem_ker_of_realized_mem_cuSubOf caseA j a (hag ▸ hcinf.2))
  have hchar : ClassFunction.compHom (quotientMulAutHom chief.N_aInvariant
        ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
          chief.N_aInvariant).U.subtype a)).toMonoidHom
        (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)
      = (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) :=
    caseA_centralizes_two_summands_compHom_eq caseA χ hsupp a hgi hgj
  rw [conjBy_compHom_hInHuEquivH data
      ((typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U.subtype a)
      c hag, compHom_typeP_conjAction_inflation, hchar]

/-- **(9.11.2) the `HU`-inertia identity `I(θ₀) = H·(C_U(H_i) ∩ C_U(H_j))`.**  Combining the two
containments (`inertia_inf_uInHu_le_cuInHuPair` for `⊆`, `cuInHuPair_le_inertia` for `⊇`) with
`H ≤ I(θ₀)` (`subgroup_le_inertia`) identifies the `HU`-inertia of the inflated two-summand
character `θ₀` as `hInHu ⊔ cuInHuPair`.  This is the realized `HU`-level lift of Peterfalvi
(9.11.2)'s inertia `I(θ₀) = H·(U₁ ∩ U₁ʷ)`; its index in `HU` is `[U : U₁ ∩ U₁ʷ]` (the
two-summand inertia index).  Mirrors `inertia_eq_hcInHu_of_inf_le` /
`inertia_eq_hcuInHu_of_easy_le`. -/
theorem caseA_inertia_eq_hcuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) {i j : Fin data.q}
    (χ : (↥data.H ⧸ chief.N) →* ℂˣ)
    (hsupp : ∀ k, k ≠ i → k ≠ j → ∀ x ∈ caseA.Hpart k, χ x = 1)
    (hregi : ∃ x ∈ caseA.Hpart i,
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1)
    (hregj : ∃ x ∈ caseA.Hpart j,
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) x
        ≠ (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ) 1) :
    ClassFunction.inertia (G := ↥(huSub data)) (H := hInHu data)
        (ClassFunction.compHom (hInHuEquivH data).toMonoidHom
          (ClassFunction.compHom (QuotientGroup.mk' chief.N)
            (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)))
      = hInHu data ⊔ cuInHuPair caseA i j := by
  set θ₀ := ClassFunction.compHom (hInHuEquivH data).toMonoidHom
    (ClassFunction.compHom (QuotientGroup.mk' chief.N)
      (linearIrreducibleCharacter χ : ClassFunction (↥data.H ⧸ chief.N) ℂ)) with hθ₀
  apply le_antisymm
  · intro g hg
    have hgtop : g ∈ hInHu data ⊔ uInHu data :=
      hInHu_sup_uInHu_eq_top data ▸ Subgroup.mem_top g
    rw [Subgroup.mem_sup_of_normal_left] at hgtop
    obtain ⟨h, hh, u, hu, rfl⟩ := hgtop
    have hh_in : h ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
      ClassFunction.subgroup_le_inertia θ₀ hh
    have hu_in : u ∈ ClassFunction.inertia (H := hInHu data) θ₀ := by
      have hmem : h⁻¹ * (h * u) ∈ ClassFunction.inertia (H := hInHu data) θ₀ :=
        mul_mem (inv_mem hh_in) hg
      rwa [inv_mul_cancel_left] at hmem
    exact mul_mem (Subgroup.mem_sup_left hh)
      (Subgroup.mem_sup_right (inertia_inf_uInHu_le_cuInHuPair caseA hregi hregj ⟨hu_in, hu⟩))
  · rw [sup_le_iff]
    exact ⟨ClassFunction.subgroup_le_inertia θ₀, cuInHuPair_le_inertia caseA χ hsupp⟩

omit [Finite G] in
open Subgroup in
/-- **`C_U(H_j) ◁ U`** for a general Clifford summand (mirrors `cuSub_subgroupOf_U_normal` for
`S₀`): the realization `cuSubOf j` is the `G`-image of the kernel `ker(aInvariantRestrictAut H_j)`,
so its `subgroupOf U` is normal (kernels are normal, transported by the realization iso
`↥(U.subgroupOf (U ⊔ W₁)) ≃* ↥U`). -/
theorem cuSubOf_subgroupOf_U_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars) (j : Fin data.q) :
    ((cuSubOf caseA j).subgroupOf data.U).Normal := by
  set e := subgroupOfEquivOfLe (le_sup_left : data.typeP.U ≤ data.typeP.U ⊔ data.typeP.W1) with he
  have heq : (cuSubOf caseA j).subgroupOf data.U
      = (aInvariantRestrictAut (caseA.Hpart_aInvariant j)).ker.map e.toMonoidHom := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      simp only [cuSubOf, Subgroup.mem_map] at hx
      obtain ⟨z, ⟨y, hy, hyz⟩, hzx⟩ := hx
      refine ⟨y, hy, ?_⟩
      apply Subtype.ext
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe, ← hzx, ← hyz]
      rfl
    · rintro ⟨y, hy, rfl⟩
      simp only [cuSubOf, Subgroup.mem_map]
      refine ⟨_, ⟨y, hy, rfl⟩, ?_⟩
      rw [MulEquiv.coe_toMonoidHom, he, subgroupOfEquivOfLe_apply_coe]
      rfl
  rw [heq]
  exact (MonoidHom.normal_ker _).map e.toMonoidHom e.surjective

omit [Finite G] in
/-- **`C_U(H_i) ∩ C_U(H_j) ◁ U`** (the two-summand centralizer is normal in `U`): the intersection
of the two single-factor normal centralizers (`cuSubOf_subgroupOf_U_normal`), via `subgroupOf`
distributing over `⊓` (`Subgroup.comap_inf`) and `⊓` of normals being normal. -/
theorem cuSubOf_pair_subgroupOf_U_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U).Normal := by
  have hi := cuSubOf_subgroupOf_U_normal caseA i
  have hj := cuSubOf_subgroupOf_U_normal caseA j
  have hEq : (cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U
      = (cuSubOf caseA i).subgroupOf data.U ⊓ (cuSubOf caseA j).subgroupOf data.U := by
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  rw [hEq]
  refine ⟨fun n hn g => Subgroup.mem_inf.mpr ⟨?_, ?_⟩⟩
  · exact hi.conj_mem n (Subgroup.mem_inf.mp hn).1 g
  · exact hj.conj_mem n (Subgroup.mem_inf.mp hn).2 g

omit [Finite G] in
/-- `|C_U(H_i) ∩ C_U(H_j)|` realized inside `HU` equals its `G`-cardinality (mirrors
`card_cuInHu_eq`): the double `subgroupOf` realization is an injective image. -/
theorem card_cuInHuPair_eq {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    Nat.card ↥(cuInHuPair caseA i j) = Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j) := by
  have hKleU : cuSubOf caseA i ⊓ cuSubOf caseA j ≤ data.U := inf_le_left.trans (cuSubOf_le_U caseA
      i)
  have hCsubM : (cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (hKleU.trans (le_sup_right : data.U ≤ data.H ⊔ data.U))
  have hCleM : cuSubOf caseA i ⊓ cuSubOf caseA j ≤ M := hKleU.trans (U_le_M data)
  calc Nat.card ↥(cuInHuPair caseA i j)
      = Nat.card ↥((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf M) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCsubM).toEquiv
    _ = Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCleM).toEquiv

omit [Finite G] in
open Subgroup in
set_option backward.isDefEq.respectTransparency false in
/-- **`C_U(H_i) ∩ C_U(H_j) ◁ U` realized inside `HU`** (mirrors `cuInHu_normal`):
`cuInHuPair ◁ uInHu`, transported from `(cuSubOf i ⊓ cuSubOf j) ◁ U` along `↥uInHu ≃* ↥U`. -/
theorem cuInHuPair_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    ((cuInHuPair caseA i j).subgroupOf (uInHu data)).Normal := by
  have hUsubM : data.U.subgroupOf M ≤ huSub data :=
    Subgroup.subgroupOf_mono M (le_sup_right : data.U ≤ data.H ⊔ data.U)
  set f : ↥(uInHu data) ≃* ↥data.U :=
    (subgroupOfEquivOfLe hUsubM).trans (subgroupOfEquivOfLe (U_le_M data)) with hf
  have hgval : ∀ x : ↥(uInHu data), ((f x : ↥data.U) : G) = (((x : ↥(huSub data)) : ↥M) : G) := by
    intro x
    have h1 : (f x : ↥data.U)
        = subgroupOfEquivOfLe (U_le_M data) (subgroupOfEquivOfLe hUsubM x) := by rw [hf]; rfl
    rw [h1, subgroupOfEquivOfLe_apply_coe, subgroupOfEquivOfLe_apply_coe]
  have hcomap : (cuInHuPair caseA i j).subgroupOf (uInHu data)
      = ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U).comap f.toMonoidHom := by
    ext x
    simp only [cuInHuPair, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom, hgval x]
  rw [hcomap]
  exact (cuSubOf_pair_subgroupOf_U_normal caseA i j).comap f.toMonoidHom

omit [Finite G] in
/-- **`H·(C_U(H_i) ∩ C_U(H_j)) ◁ HU`** (mirrors `hcuInHu_normal`): the (9.11.2) inertia subgroup is
normal.  From `H ◁ HU` (`hInHu_normal`), `C_U(H_i) ∩ C_U(H_j) ◁ U` (`cuInHuPair_normal`), and
`H ⊔ U = ⊤` (`hInHu_sup_uInHu_eq_top`) via `sup_normal_of_normal_left_of_normal_subgroupOf`. -/
theorem hcuInHuPair_normal {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) :
    (hInHu data ⊔ cuInHuPair caseA i j).Normal :=
  haveI := hInHu_normal data
  haveI := cuInHuPair_normal caseA i j
  OddOrder.GroupTheory.sup_normal_of_normal_left_of_normal_subgroupOf
    (cuInHuPair_le_uInHu caseA i j) (hInHu_sup_uInHu_eq_top data)

/-- **`C = C_U(H̄) ≤ C_U(H_i) ∩ C_U(H_j)`** realized (`cInHu ≤ cuInHuPair`): centralizing the whole
chief factor implies centralizing each summand (`cSub_le_cuSubOf`), realized through the double
`subgroupOf`. -/
theorem cInHu_le_cuInHuPair {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    {chars : Section11CharacterData data chief} (caseA : CliffordCaseAData chars)
    (i j : Fin data.q) : cInHu data chief ≤ cuInHuPair caseA i j :=
  Subgroup.subgroupOf_mono _ (Subgroup.subgroupOf_mono _
    (le_inf (cSub_le_cuSubOf caseA i) (cSub_le_cuSubOf caseA j)))

/-- **`U ⊓ H·(C_U(H_i) ∩ C_U(H_j)) = C_U(H_i) ∩ C_U(H_j)`** realized (mirrors
`uInHu_inf_hcuInHu_eq_cuInHu`), the second-iso input for `[HU : H·K] = [U : K]`.  The crux
`hInHu ⊓ uInHu ≤ cuInHuPair` factors through `H ⊓ U ≤ C` (`hInHu_inf_uInHu_le_cInHu`) and
`C ≤ K` (`cInHu_le_cuInHuPair`). -/
theorem uInHu_inf_hcuInHuPair_eq_cuInHuPair {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    uInHu data ⊓ (hInHu data ⊔ cuInHuPair caseA i j) = cuInHuPair caseA i j := by
  have := hInHu_normal data
  apply le_antisymm
  · rintro x ⟨hxU, hxHC⟩
    obtain ⟨hh, hhmem, cc, ccmem, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hxHC
    have hcc_u : cc ∈ uInHu data := cuInHuPair_le_uInHu caseA i j ccmem
    have hh_u : hh ∈ uInHu data := by
      have h1 : hh * cc * cc⁻¹ ∈ uInHu data :=
        (uInHu data).mul_mem hxU ((uInHu data).inv_mem hcc_u)
      rwa [mul_inv_cancel_right] at h1
    have hh_c : hh ∈ cuInHuPair caseA i j :=
      cInHu_le_cuInHuPair caseA i j
        (hInHu_inf_uInHu_le_cInHu data chief (Subgroup.mem_inf.mpr ⟨hhmem, hh_u⟩))
    exact (cuInHuPair caseA i j).mul_mem hh_c ccmem
  · exact le_inf (cuInHuPair_le_uInHu caseA i j) le_sup_right

/-- **Second-iso index step: `[HU : H·(C_U(H_i) ∩ C_U(H_j))] = [U : C_U(H_i) ∩ C_U(H_j)]`**
(realized `(hInHu ⊔ cuInHuPair).index = (cuInHuPair.subgroupOf uInHu).index`).  Mirrors
`index_hcuInHu_eq_relindex_cuInHu`: the second isomorphism theorem for `H·K ◁ HU` with
`uInHu ⊔ H·K = ⊤`, and `uInHu ⊓ H·K = K` (`uInHu_inf_hcuInHuPair_eq_cuInHuPair`). -/
theorem index_hcuInHuPair_eq_relindex_cuInHuPair {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    (hInHu data ⊔ cuInHuPair caseA i j).index
      = ((cuInHuPair caseA i j).subgroupOf (uInHu data)).index := by
  have : (hInHu data ⊔ cuInHuPair caseA i j).Normal := hcuInHuPair_normal caseA i j
  have htop : uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j) = ⊤ := by
    rw [← sup_assoc, sup_comm (uInHu data) (hInHu data), hInHu_sup_uInHu_eq_top, top_sup_eq]
  have he := Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalQuotient
    (uInHu data) (hInHu data ⊔ cuInHuPair caseA i j)).toEquiv
  have hsub : (hInHu data ⊔ cuInHuPair caseA i j).subgroupOf (uInHu data)
      = (cuInHuPair caseA i j).subgroupOf (uInHu data) := by
    ext x
    simp only [Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have hxin : (x : ↥(huSub data))
          ∈ uInHu data ⊓ (hInHu data ⊔ cuInHuPair caseA i j) :=
        Subgroup.mem_inf.mpr ⟨x.2, hx⟩
      rw [uInHu_inf_hcuInHuPair_eq_cuInHuPair caseA i j] at hxin
      exact hxin
    · intro hx; exact Subgroup.mem_sup_right hx
  rw [hsub] at he
  have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((hInHu data ⊔ cuInHuPair caseA i j).subgroupOf
      (uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j)))
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right :
        (hInHu data ⊔ cuInHuPair caseA i j)
          ≤ uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j))).toEquiv,
    ← he, ← Subgroup.index_eq_card] at hsplit
  have htopcard : Nat.card ↥(uInHu data ⊔ (hInHu data ⊔ cuInHuPair caseA i j))
      = Nat.card ↥(huSub data) := by
    rw [htop]; exact Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [htopcard] at hsplit
  have hmul := Subgroup.card_mul_index (hInHu data ⊔ cuInHuPair caseA i j)
  rw [hsplit, mul_comm (((cuInHuPair caseA i j).subgroupOf (uInHu data)).index)] at hmul
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos hmul

/-- **`[U : C_U(H_i) ∩ C_U(H_j)] = [uInHu : cuInHuPair]`** (realized index equals ambient-`G`
relative index).  Both sides multiply by `|C_U(H_i) ∩ C_U(H_j)|` to `|U|` (Lagrange in the `uInHu`
realization and in `U`), cancelling the positive common factor.  Mirrors the `relIndex_cSub_U_eq_u`
style. -/
theorem index_cuInHuPair_subgroupOf_uInHu_eq_relIndex {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) (i j : Fin data.q) :
    ((cuInHuPair caseA i j).subgroupOf (uInHu data)).index
      = (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U := by
  have hI : Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j)
      * ((cuInHuPair caseA i j).subgroupOf (uInHu data)).index = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cuInHuPair caseA i j).subgroupOf (uInHu data))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (cuInHuPair_le_uInHu caseA i j)).toEquiv,
      card_cuInHuPair_eq caseA i j, card_uInHu_eq data] at h
    exact h
  have hII : Nat.card ↥(cuSubOf caseA i ⊓ cuSubOf caseA j)
      * (cuSubOf caseA i ⊓ cuSubOf caseA j).relIndex data.U = Nat.card ↥data.U := by
    have h := Subgroup.card_mul_index ((cuSubOf caseA i ⊓ cuSubOf caseA j).subgroupOf data.U)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left.trans (cuSubOf_le_U caseA i))).toEquiv] at h
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (hI.trans hII.symm)

end NineElevenTwoInertia

/-- **`[U : K₁ ⊓ K₂] ≤ [U:K₁]·[U:K₂]`** (relative-index form of `Subgroup.index_inf_le`): the
relative index `H.relIndex U = (H.subgroupOf U).index`, and `subgroupOf = comap` distributes over
`⊓` (`Subgroup.comap_inf`), so the ambient `index_inf_le` in `↥U` applies.  The (9.11.2) injectivity
`Ū ↪ (U/U₁)×(U/U₁ʷ)` in relative-index form. -/
theorem relIndex_inf_le {G : Type*} [Group G] {K₁ K₂ U : Subgroup G} :
    (K₁ ⊓ K₂).relIndex U ≤ K₁.relIndex U * K₂.relIndex U := by
  simp only [Subgroup.relIndex, Subgroup.subgroupOf, Subgroup.comap_inf]
  exact Subgroup.index_inf_le

/-- **Peterfalvi (9.11.2), the bound `u ≤ a²`.**  Book (9.11.2): *"The canonical mapping from `Ū` to
`(U/U₁)×(U/U₁ʷ)` is injective, and so `u ≤ a²`."*  Given the inertia identity `C = U₁ ⊓ U₁ʷ` (the
*first* assertion of (9.11.2), the deep character-theoretic input: `U₁ = C_U(H₁)`, `U₁ʷ = C_U(H₂)`,
their intersection is `C = C_U(H̄)`) and the per-summand index `[U:U₁] = [U:U₁ʷ] = a`, the relative
index `u = [U:C]` is bounded by `[U:U₁]·[U:U₁ʷ] = a²` (`relIndex_inf_le`).  Consumed by the (9.11.5)
polynomial bound (`nineElevenFive_refutation`'s `hua2`). -/
theorem nineElevenTwo_u_le_a_sq [Finite G] {M : Subgroup G} {data : TypesIIIIIIVSetup M}
    {chief : ChiefFactorData data} {chars : Section11CharacterData data chief}
    (caseA : CliffordCaseAData chars) {K₁ K₂ : Subgroup G}
    (hK₁ : K₁.relIndex data.U = caseA.a) (hK₂ : K₂.relIndex data.U = caseA.a)
    (hCinf : chars.C = K₁ ⊓ K₂) : chars.u ≤ caseA.a * caseA.a := by
  have hu : (K₁ ⊓ K₂).relIndex data.U = chars.u := by
    rw [← hCinf]; exact relIndex_cSub_U_eq_u chars
  rw [← hu]
  calc (K₁ ⊓ K₂).relIndex data.U ≤ K₁.relIndex data.U * K₂.relIndex data.U := relIndex_inf_le
    _ = caseA.a * caseA.a := by rw [hK₁, hK₂]

end OddOrder.Peterfalvi.S11


