-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_HcBound
-- name    : OddOrder_Peterfalvi_S12_HcBound
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:57:02.438482+00:00
-- url     : https://prove2.me/theorems/1adb9c3a-32b7-42c8-b8b7-eae012341915
-- title:
--   Peterfalvi §12/§9: $H_C$ bound and the §9–§10 character-data bridge
-- statement:
--   Bridges the type III/IV hypothesis of §10 to the §9 character analysis, constructing the §9 character data and proving the congruence and index identification of Peterfalvi (11.8.1) and the unified degree of (9.8.b)/(9.9.b).
--
--   Main declarations: `Hypothesis.mkSection11CharacterData` (Construct the §9 `Section11CharacterData` from the §10 `Hypothesis`); `Hypothesis.toTypesIIIIIIVSetup` (Bridge to the §9 (repo S11) character analysis); `Hypothesis.mkSection11CharacterData_u_modEq_one` (Peterfalvi (11.8.1), the chief-factor image congruence `|Ū| ≡ 1 (mod q)`); `Hypothesis.u_eq_relIndex_C` (Peterfalvi (11.8.1), the index identification `u = |U : C|`).
--
--   The bundle also proves 1 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_HcBound.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_HcBound.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_CharacterParameters
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V_Core_DadeCalculations
import Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoGeneral
import Definitions.Def_OddOrder_GroupTheory_PiElementDecomposition

namespace OddOrder.Peterfalvi.S12

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Construct the §9 `Section11CharacterData` from the §10 `Hypothesis`** (the key unblocker for
the (11.8.1) §9 counts).  Given the §9 setup `data` (`toTypesIIIIIIVSetup`) and a chief factor
`chief` (`exists_chiefFactorData`), the §9 character datum's *character* fields are all derived from
`data`/`chief` (the families `𝒳 = xiSet`, `𝒮 = Ind_{HU}^M 𝒳`, `𝒮(Y)`); the only genuine fields are
`u = |Ū|` (pinned to the `U`-action image on the chief factor, `rfl`) and the degree-irrelevant
`tau`/`H0CprimeSupport`/`quotientSemidirectFrobenius` (used only by the (9.11) coherence, not by the
degree fact `caseB_degree_qu`).  So the §9 *degree* analysis — `clifford_dichotomy` (9.7) and the
`μ_j(1) = qu` of (9.8)/(9.9) — becomes available on the §10 `Hypothesis`.  (`tau := hyp.tau` records
the genuine Dade map for the coherence use; the support/`Prop` are placeholders for the count
use.) -/
noncomputable def Hypothesis.mkSection11CharacterData [Finite G] {M : Subgroup G} (hyp : Hypothesis
    M)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData data) :
    OddOrder.Peterfalvi.S11.Section11CharacterData data chief where
  u := Nat.card ↥(((quotientMulAutHom (N := chief.N) chief.N_aInvariant).comp
      (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
  u_eq_card_quotient := rfl
  H0CprimeSupport := ∅
  tau := hyp.tau
  quotientSemidirectFrobenius := True

/-- **Bridge to the §9 (repo S11) character analysis.**  A §10 type-III/IV `Hypothesis` yields the
§9 `TypesIIIIIIVSetup` on the same `M`, sharing the type-`P` structure `(H, U, W₁, W₂)`.  This is
the
`Hypothesis` → `Section11CharacterData` bridge the (11.8.1) §9 counts need: with it,
`exists_chiefFactorData` produces the chief factor `H̄ = H/H₀`, and `caseB_degree_qu` supplies
`μ_j(1) = qu` for the §10 character parameters.  The generic (9.11) shortcut formerly attached
to this bridge had an invalid support carrier and is withdrawn; the live honest coherence is
constructed in the S15 `Ind_S^G` / `A(S)` world.  `type_alt` restricts to III/IV (type V by
`no_typeV_maximal`); the `nontrivial` core (`U ≠ ⊥`, `|W₁|` prime, the `M_F`-TI condition) is the §8
structural input, threaded as `hnt` (obtainable from the type data via
`typePNontrivialCore_of_isTypeIIIorIV`). -/
def Hypothesis.toTypesIIIIIIVSetup [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP) :
    OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M where
  maximal := hyp.maximal
  typeP := hyp.typeP
  nontrivial := hnt
  type_alt := htype.elim (fun h => Or.inr (Or.inl h)) (fun h => Or.inr (Or.inr h))

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
/-- **Peterfalvi (11.8.1), the chief-factor image congruence `|Ū| ≡ 1 (mod q)`.**  The genuine `u`
field of the constructed §9 character datum, `u = |Ū| = |U/C_U(H̄)|` (the image of `U` in
`Aut(H̄)`, `mkSection11CharacterData.u`), satisfies `|Ū| ≡ 1 (mod w₁ = q)`.

This is the `U/C_U(H̄)`-quotient of the Frobenius congruence `|U| ≡ 1 (mod q)` (`card_U_modEq_one`):
`W₁` acts fixed-point-freely on `U` (`typeP_uW1_frobenius`) and this descends to the chief-factor
image `Ū` — a homomorphic image of `U` under the `U W₁`-equivariant action map `quotientMulAutHom` —
by the general Frobenius-group image congruence
`IsFrobeniusGroup.card_range_comp_subtype_modEq_one` (Isaacs Cor 6.2 + Lemma 6.1).  Together with
the
μ-grid degree `d = |Ū|` (from `caseB_degree_qu`, the μ-grid ↔ §9-family correspondence) this is the
§9 half of `charParam_d_modEq_one`. -/
theorem Hypothesis.mkSection11CharacterData_u_modEq_one [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData data) (hU : data.typeP.U ≠ ⊥) :
    (hyp.mkSection11CharacterData data chief).u ≡ 1 [MOD Nat.card ↥data.typeP.W1] := by
  have hgen := (OddOrder.Peterfalvi.S11.typeP_uW1_frobenius data.typeP
      hU).card_range_comp_subtype_modEq_one
    (quotientMulAutHom (N := chief.N) chief.N_aInvariant)
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv] at hgen

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom) in
open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the index identification `u = |U : C|`** (`C = U ⊓ C_G(H)`), under the
(11.7) collapse `H₀ = 1` (i.e. the chief-factor kernel `chief.N = ⊥`).

The genuine `u` field is `u = |Ū| = |range φ|`, where `φ : ↥(U.subgroupOf(U ⊔ W₁)) →* Aut(H̄)`
is the `U`-action on the chief factor `H̄ = ↥H ⧸ chief.N`.  By the first isomorphism theorem
`|range φ| = [dom : ker φ]`.  With `chief.N = ⊥` the quotient `H̄ = ↥H ⧸ ⊥` *is* `↥H`, so `φ` is the
conjugation action of `U ⊔ W₁` on `↥H` (`typeP_conjAction`); an element `v ∈ U` acts trivially iff
it centralizes `H`, i.e. `ker φ ≅ (C = U ⊓ C_G(H))` inside `U`.  Transporting the index along
`↥(U.subgroupOf(U ⊔ W₁)) ≃* ↥U` gives `[dom : ker φ] = C.relIndex U = |U : C|`.

This is the (11.7) `H₀ = 1` half of the (11.8.1) chain `|M'{}^{ab}| = |U : C| = u = d` feeding the
`|𝒮(HC)| = n` count (`card_SHCSet_filter_eq_charParam_n`); the `|M'{}^{ab}| = |U : C|` structural
half is `typePData_card_abelianization_derived_eq_relIndex_C` and `u = d` is `charParam_d_eq_u`. -/
theorem Hypothesis.u_eq_relIndex_C [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup M)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData data)
    (hN : chief.N = ⊥) :
    (hyp.mkSection11CharacterData data chief).u
      = (data.typeP.U ⊓ Subgroup.centralizer (data.typeP.H : Set G)).relIndex data.typeP.U := by
  classical
  set L := data.typeP.U ⊔ data.typeP.W1 with hL
  set C := data.typeP.U ⊓ Subgroup.centralizer (data.typeP.H : Set G) with hC
  -- The `U`-action map on `H̄`, restricted to `U` via the inclusion `↥U →* ↥L`.
  set φ := quotientMulAutHom (N := chief.N) chief.N_aInvariant with hφ
  set θ := φ.comp (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L)) with hθ
  -- (A) `u = |range φ_sub| = |range θ|`: the two restrictions of `φ` (to `U.subgroupOf L` and via
  -- the inclusion from `↥U`) have equal range, since both restriction domains sit as `U` in `L`.
  have hrange : ((φ.comp (data.typeP.U.subgroupOf L).subtype)).range = θ.range := by
    rw [hθ, MonoidHom.range_comp, MonoidHom.range_comp]
    congr 1
    -- `(U.subgroupOf L).subtype.range = (inclusion le_sup_left).range` (both are `U` inside `L`).
    rw [Subgroup.range_subtype, Subgroup.inclusion_range]
  have huθ : (hyp.mkSection11CharacterData data chief).u = Nat.card ↥θ.range := by
    change Nat.card ↥((φ.comp (data.typeP.U.subgroupOf L).subtype)).range = _
    rw [hrange]
  -- (B) `ker θ = C.subgroupOf U`: with `chief.N = ⊥`, `v ∈ U` acts trivially on `H̄ = ↥H` iff `↑v`
  -- centralizes `H`, i.e. `↑v ∈ C`.
  have hker : θ.ker = C.subgroupOf data.typeP.U := by
    ext v
    rw [MonoidHom.mem_ker, hθ, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, hC,
      Subgroup.mem_inf]
    constructor
    · intro hv
      refine ⟨v.property, Subgroup.mem_centralizer_iff.mpr (fun g hg => ?_)⟩
      -- `φ (incl v) = 1` ⇒ conjugation by `↑v` fixes every `⟨g, hg⟩ : ↥H`.
      have happ : φ (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L) v)
          ((⟨g, hg⟩ : ↥data.typeP.H) : ↥data.typeP.H ⧸ chief.N)
          = ((⟨g, hg⟩ : ↥data.typeP.H) : ↥data.typeP.H ⧸ chief.N) := by
        rw [hv]; rfl
      rw [hφ, OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply,
        QuotientGroup.eq, hN] at happ
      have hmem : (typeP_conjAction data.typeP
          (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L) v)
          ⟨g, hg⟩)⁻¹ * ⟨g, hg⟩ ∈ (⊥ : Subgroup ↥data.typeP.H) := happ
      rw [Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have hconj : (v : G) * g * (v : G)⁻¹ = g := by
        have := Subtype.ext_iff.mp hmem
        rwa [typeP_conjAction_apply, Subgroup.coe_inclusion] at this
      -- `↑v * g * ↑v⁻¹ = g` ⇒ `g * ↑v = ↑v * g`.
      exact (mul_inv_eq_iff_eq_mul.mp hconj).symm
    · rintro ⟨-, hvC⟩
      -- `↑v ∈ C_G(H)` ⇒ `φ (incl v) = 1` (conjugation by `↑v` fixes `↥H`, hence all of `H̄`).
      apply MulEquiv.ext
      intro y
      refine QuotientGroup.induction_on y (fun g => ?_)
      rw [hφ, OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom_apply]
      change ((typeP_conjAction data.typeP
        (Subgroup.inclusion (le_sup_left : data.typeP.U ≤ L) v) g : ↥data.typeP.H)
        : ↥data.typeP.H ⧸ chief.N) = _
      congr 1
      apply Subtype.ext
      rw [typeP_conjAction_apply, Subgroup.coe_inclusion]
      -- `↑v * ↑g * ↑v⁻¹ = ↑g` from `↑v ∈ C_G(H)`.
      have hgH : (g : G) ∈ (data.typeP.H : Set G) := g.property
      have hcomm : (g : G) * (v : G) = (v : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hvC (g : G) hgH
      rw [← hcomm, mul_inv_cancel_right]
  -- (C) `|range θ| = [dom : ker θ] = C.relIndex U`.
  rw [huθ, Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).symm.toEquiv, hker]
  rfl

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (9.8.b)/(9.9.b), unified degree**: in either Clifford case, every reducible member
of `𝒮(H₀)` has degree `qu`.  Case (a) is `caseA_reducible_induceHU_apply_one_eq_qu`; case (b)
combines the cardinality membership `reducible_mem_sOf_H0C` with the `𝒮(H₀C)` degree
`forall_mem_sOf_H0C_apply_one_eq_qu`.  This is the degree input the (11.8.1) `d = |Ū|`
identification consumes, dichotomy-free for the caller. -/
theorem reducible_mem_sOf_H0_apply_one_eq_qu [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
    (chars : Section11CharacterData data chief)
    (φ : ClassFunction ↥M ℂ) (hφ : φ ∈ sOf data chief.H0)
    (hred : ¬ IsIrreducibleCharacter φ) :
    φ (1 : ↥M) = ((data.q * chars.u : ℕ) : ℂ) := by
  rcases clifford_dichotomy hG chars with ⟨⟨caseA⟩⟩ | ⟨⟨caseB⟩⟩
  · exact caseA_reducible_induceHU_apply_one_eq_qu caseA hG φ hφ hred
  · refine forall_mem_sOf_H0C_apply_one_eq_qu hG chars caseB φ ?_
    rw [Section11CharacterData.SOf_eq]
    exact reducible_mem_sOf_H0C hG chars φ hφ hred

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S11 in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (11.8.1), the μ-columns are the reducible `𝒮(H₀)`-members** (Coq `PFsection11`
`memSred`): for `k ≠ 0`, the §10 column sum `μ_k = ∑_i μ_{ik}` lies in the §9 family `𝒮(H₀)` and is
reducible.

By counting: the reducible `𝒮(H₀)`-members number `p − 1` (`reducible_count_sOf_H0`, proven); each
one is a §6 column induction `Ind_{M'}^M χ_j` by the Clifford characterization
(`induce_not_isIrreducible_iff`), with the trivial column excluded by the `𝒳`-kernel condition
`H ⊄ Ker` (`chiRestrict_one_eq_trivial`) — hence lies among the `w₂ − 1 = p − 1` pairwise-distinct
column sums `μ_k`, `k ≠ 0` (`chief.typeIII_IV_p_eq_W2`).  Equal finite cardinalities force the two
sets equal (`Set.eq_of_subset_of_ncard_le`), so *every* `μ_k` (`k ≠ 0`) is a reducible
`𝒮(H₀)`-member.  This sharpens the `inducedFamily`-membership
(`muGrid_column_sum_mem_inducedFamily`) to the `𝒮(H₀)`-membership that the (9.8)/(9.9) degree
analysis (`reducible_mem_sOf_H0_apply_one_eq_qu`) consumes. -/
theorem Hypothesis.muGrid_column_sum_mem_sOf_H0_and_reducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt))
    (k : Fin hyp.w2) (hk : k ≠ 0) :
    (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
        ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 ∧
      ¬ IsIrreducibleCharacter (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) := by
  have := hyp.finiteG
  classical
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥h.K := Fintype.ofFinite _
  let : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  -- (4.5.a): the column sum at `j` is the induction of the column character `χ_j`
  have hFk : ∀ j : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = ClassFunction.induce h.K
          ((h.chiRestrict (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)))
            : ClassFunction ↥h.K ℂ) := by
    intro j
    rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq, ← Equiv.sum_comp (finCongr
        hcardW1.symm)
      (fun i' => ((h.columnFamily
        (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu i' : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- every column sum induces reducibly ((4.5.b))
  have hredF : ∀ j : Fin hyp.w2,
      ¬ IsIrreducibleCharacter (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) := by
    intro j
    rw [hFk j]
    exact h.induce_chiRestrict_not_isIrreducible _
  -- the column sums are pairwise distinct
  have hFinj : Function.Injective
      (fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j) := by
    intro j j' heq
    have heq' : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
        = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j' := heq
    rw [hFk j, hFk j'] at heq'
    have h1 := h.induce_injective_on_reducible
      (h.induce_chiRestrict_not_isIrreducible _) heq'
    have h2 := h.chiRestrict_injective h1
    have h3 := (finCardEquivCharacterGroup _).injective h2
    exact (finCongr hcardW2sub.symm).injective h3
  -- `|A| = p − 1 = w₂ − 1` (the §9 count and the (9.6) `p = |W₂|`)
  have hAcard : {φ ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 |
      ¬ IsIrreducibleCharacter φ}.ncard = hyp.w2 - 1 := by
    rw [reducible_count_sOf_H0 hG chief, ← chief.typeIII_IV_p_eq_W2 htype]
    rfl
  -- `|B| = w₂ − 1` (distinct column sums over `k ≠ 0`)
  have hBcard : (((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
      {j : Fin hyp.w2 | j ≠ 0}).ncard = hyp.w2 - 1 := by
    rw [Set.ncard_image_of_injective _ hFinj,
      show {j : Fin hyp.w2 | j ≠ 0} = (Set.univ \ {0} : Set (Fin hyp.w2)) by ext j; simp,
      Set.ncard_sdiff (Set.subset_univ _), Set.ncard_univ, Set.ncard_singleton]
    simp [Nat.card_eq_fintype_card]
  -- `A ⊆ B`: a reducible `𝒮(H₀)`-member is a nonzero column sum
  have hAB : {φ ∈ sOf (hyp.toTypesIIIIIIVSetup htype hnt) chief.H0 |
      ¬ IsIrreducibleCharacter φ}
      ⊆ ((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
        {j : Fin hyp.w2 | j ≠ 0} := by
    rintro φ ⟨hφS, hφred⟩
    obtain ⟨χ, hχxi, rfl⟩ := hφS
    have hKeq : huSub (hyp.toTypesIIIIIIVSetup htype hnt) = (derivedInG M).subgroupOf M :=
      huSub_eq_derivedInG_subgroupOf _
    -- transport the source along `HU = M' = K`
    have hχKirr : IsIrreducibleCharacter
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)) :=
      IsIrreducibleCharacter.compHom_of_surjective
        (MulEquiv.surjective _) χ.isIrreducible
    have hind : ClassFunction.induce ((derivedInG M).subgroupOf M)
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ))
        = induceHU (hyp.toTypesIIIIIIVSetup htype hnt)
            (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ) :=
      induce_compHom_subgroupCongr hKeq.symm _
    -- the reducible transported source is a §6 column `χ_j`
    obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff ⟨_, hχKirr⟩).mp (by
      change ¬ IsIrreducibleCharacter (ClassFunction.induce ((derivedInG M).subgroupOf M)
        (ClassFunction.compHom (MulEquiv.subgroupCongr hKeq.symm).toMonoidHom
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)))
      rw [hind]
      exact hφred)
    -- the trivial column is excluded by the `𝒳`-kernel condition `H ⊄ Ker χ`
    have hχ₂'ne : χ₂' ≠ 1 := by
      rintro rfl
      rw [h.chiRestrict_one_eq_trivial] at hχ₂'
      refine hχxi.1 ?_
      have hval : ∀ y : ↥((derivedInG M).subgroupOf M),
          (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)
            ((MulEquiv.subgroupCongr hKeq.symm) y) = 1 := by
        intro y
        have hcoe := congrArg
          (fun c : IrreducibleCharacter ↥h.K => (c : ClassFunction ↥h.K ℂ) y) hχ₂'
        simpa [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
          ClassFunction.compHom_apply] using hcoe.symm
      intro x _hx
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def]
      have hx1 := hval ((MulEquiv.subgroupCongr hKeq.symm).symm x)
      have hone := hval ((MulEquiv.subgroupCongr hKeq.symm).symm 1)
      rw [MulEquiv.apply_symm_apply] at hx1 hone
      rw [hx1, hone]
    -- identify the column index `k' ≠ 0` and conclude `φ = μ_{k'}`
    refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'), ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      intro h0
      apply hχ₂'ne
      have hs0 : (finCardEquivCharacterGroup
          ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))).symm χ₂' = 0 := by
        have := congrArg (finCongr hcardW2sub.symm) h0
        simpa using this
      calc χ₂' = finCardEquivCharacterGroup _
            ((finCardEquivCharacterGroup _).symm χ₂') := (Equiv.apply_symm_apply _ _).symm
        _ = finCardEquivCharacterGroup _ 0 := by rw [hs0]
        _ = 1 := finCardEquivCharacterGroup_zero _
    · change (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i
          (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂')))
        = induceHU (hyp.toTypesIIIIIIVSetup htype hnt)
            (χ : ClassFunction ↥(huSub (hyp.toTypesIIIIIIVSetup htype hnt)) ℂ)
      rw [hFk, show finCongr hcardW2sub.symm
          (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'))
          = (finCardEquivCharacterGroup _).symm χ₂' from by simp,
        Equiv.apply_symm_apply, hχ₂']
      exact hind
  -- equal counts force `A = B`; conclude for the given `k`
  have hBfin : (((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
      {j : Fin hyp.w2 | j ≠ 0}).Finite :=
    (Set.toFinite _).image _
  have hAeqB := Set.eq_of_subset_of_ncard_le hAB (le_of_eq (hBcard.trans hAcard.symm)) hBfin
  have hmemB : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k)
      ∈ ((fun j : Fin hyp.w2 => ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)) ''
        {j : Fin hyp.w2 | j ≠ 0} := ⟨k, hk, rfl⟩
  rw [← hAeqB] at hmemB
  exact ⟨hmemB.1, hmemB.2⟩

open scoped FiniteInduce in
open OddOrder.Peterfalvi.S11 in
/-- **(9.8) classification at the bridge family**: a *reducible* member of the general
kernel-filter family `inducedKernelFamily M'-trace B` (any `B`) is a nonzero μ-grid column sum.

Unlike the `𝒮(H₀)`-route, the trivial column is excluded directly by the family's `θ ≠ 1`
condition (`chiRestrict_one_eq_trivial`), so no `𝒳`-kernel condition is needed — this covers
the h56 break members (issue 2022, the U-side case being impossible for *reducible* members
precisely because the trivial column is the only `H`-trivial one among the `χ_j`). -/
theorem Hypothesis.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    {B : Subgroup ↥M} {ψ : ClassFunction ↥M ℂ}
    (hψ : ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) B)
    (hred : ¬ IsIrreducibleCharacter ψ) :
    ∃ k : Fin hyp.w2, k ≠ 0 ∧ ψ = ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, hθne, hθker, rfl⟩ := hψ
  let h := (hyp.toCertainTypeHypothesis hG hG.odd).toHypothesis
  have hNeZ1 : NeZero (Nat.card h.W1) := ⟨by have := h.one_lt_card_W1; omega⟩
  have hcyc : IsCyclic ↥(h.W1 ⊔ h.W2) := h.isCyclic_sup
  let : CommGroup ↥(h.W1 ⊔ h.W2) := IsCyclic.commGroup
  let : Fintype ↥M := Fintype.ofFinite _
  let : Fintype ↥h.K := Fintype.ofFinite _
  let : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  have hW1le : hyp.typeP.W1 ≤ M := hyp.typeP.W1_le
  have hW2le : hyp.typeP.W2 ≤ M := typePData_W2_le_self hyp.typeP
  have hcardW1 : Nat.card ↥h.W1 = hyp.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1le).toEquiv
  have hcardW2sub : Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2)) = hyp.w2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right)).toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW2le).toEquiv
  have hNeZ2 : NeZero (Nat.card ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) := ⟨Nat.card_pos.ne'⟩
  have hFk : ∀ j : Fin hyp.w2, (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i j)
      = ClassFunction.induce h.K
          ((h.chiRestrict (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j)))
            : ClassFunction ↥h.K ℂ) := by
    intro j
    rw [h.coe_chiRestrict, h.induce_restrict_certainType_eq,
      ← Equiv.sum_comp (finCongr hcardW1.symm)
      (fun i' => ((h.columnFamily
        (finCardEquivCharacterGroup _ (finCongr hcardW2sub.symm j))).mu i'
          : ClassFunction ↥M ℂ))]
    exact Finset.sum_congr rfl (fun i _ => by unfold Hypothesis.muGrid; rfl)
  -- the reducible source is a §6 column
  obtain ⟨χ₂', hχ₂'⟩ := (h.induce_not_isIrreducible_iff θ).mp hred
  have hχ₂'ne : χ₂' ≠ 1 := by
    rintro rfl
    rw [h.chiRestrict_one_eq_trivial] at hχ₂'
    exact hθne hχ₂'.symm
  refine ⟨finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'), ?_, ?_⟩
  · intro h0
    apply hχ₂'ne
    have hs0 : (finCardEquivCharacterGroup
        ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))).symm χ₂' = 0 := by
      have := congrArg (finCongr hcardW2sub.symm) h0
      simpa using this
    calc χ₂' = finCardEquivCharacterGroup _
          ((finCardEquivCharacterGroup _).symm χ₂') := (Equiv.apply_symm_apply _ _).symm
      _ = finCardEquivCharacterGroup _ 0 := by rw [hs0]
      _ = 1 := finCardEquivCharacterGroup_zero _
  · rw [hFk, show finCongr hcardW2sub.symm
        (finCongr hcardW2sub ((finCardEquivCharacterGroup _).symm χ₂'))
        = (finCardEquivCharacterGroup _).symm χ₂' from by simp,
      Equiv.apply_symm_apply, hχ₂']
    exact rfl

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the degree identification `d = u = |Ū|`** (Coq `Dd`).  The column sum
`μ_1 = ∑_i μ_{i1}` is a reducible member of the §9 family `𝒮(H₀)`
(`muGrid_column_sum_mem_sOf_H0_and_reducible`), so it has degree `q·u = q·|Ū|` by (9.8.b)/(9.9.b)
(`reducible_mem_sOf_H0_apply_one_eq_qu`, both Clifford cases); its degree is also `w₁·d` by the
(10.3) grid (`degree_independent`, via `hmu`).  Cancelling `q = w₁` gives `d = |Ū|`.  This is
the `d`-identification consumed by the residue `d ≡ 1 (mod q)` (`charParam_d_modEq_one`) and by
the `|S(HC)| = n = (d−1)/q` count. -/
theorem Hypothesis.charParam_d_eq_u [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hnt : TypePNontrivialCore M hyp.typeP)
    (chief : OddOrder.Peterfalvi.S11.ChiefFactorData (hyp.toTypesIIIIIIVSetup htype hnt)) :
    params.d = (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u := by
  have := hyp.finiteG
  classical
  -- the nonzero column `k = 1` (`w₂ ≥ 3`: `w₂` is an odd prime)
  have hw2odd : Odd hyp.w2 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W2)
  have hw2_3 : 3 ≤ hyp.w2 := by
    have h2 := params.w2_prime.two_le
    obtain ⟨m, hm⟩ := hw2odd
    omega
  set k : Fin hyp.w2 := ⟨1, by omega⟩ with hk_def
  have hk0 : k ≠ 0 := by
    intro h0
    have := congrArg Fin.val h0
    simp [hk_def] at this
  obtain ⟨hmem, hred⟩ :=
    hyp.muGrid_column_sum_mem_sOf_H0_and_reducible hG htype hnt chief k hk0
  -- degree `q·u` from the §9 counts (both Clifford cases)
  have hqu := reducible_mem_sOf_H0_apply_one_eq_qu hG
    (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief) _ hmem hred
  -- degree `w₁·d` from the (10.3) grid
  have hdeg : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
      = (hyp.w1 : ℂ) * (params.d : ℂ) := by
    have hcoe : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
        = ∑ i : Fin hyp.w1, (hyp.muGrid hG hG.odd i k) (1 : ↥M) := by
      rw [show ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k : ClassFunction ↥M ℂ) : ↥M → ℂ)
          = ∑ i : Fin hyp.w1, ((hyp.muGrid hG hG.odd i k : ClassFunction ↥M ℂ) : ↥M → ℂ) from
        AddSubmonoidClass.coe_finsetSum _ _]
      rw [Finset.sum_apply]
    have hterm : ∀ i : Fin hyp.w1, (hyp.muGrid hG hG.odd i k) (1 : ↥M) = (params.d : ℂ) := by
      intro i
      rw [← hmu]
      exact params.degree_independent i k hk0
    calc (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k) (1 : ↥M)
        = ∑ i : Fin hyp.w1, (hyp.muGrid hG hG.odd i k) (1 : ↥M) := hcoe
      _ = ∑ _i : Fin hyp.w1, (params.d : ℂ) := Finset.sum_congr rfl (fun i _ => hterm i)
      _ = (hyp.w1 : ℂ) * (params.d : ℂ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- cancel `q = w₁`
  have hq : (hyp.toTypesIIIIIIVSetup htype hnt).q = hyp.w1 := rfl
  have hqu' : (hyp.w1 : ℂ) * (params.d : ℂ)
      = (((hyp.toTypesIIIIIIVSetup htype hnt).q
          * (hyp.mkSection11CharacterData (hyp.toTypesIIIIIIVSetup htype hnt) chief).u : ℕ) : ℂ) :=
              by
    rw [← hdeg]; exact hqu
  rw [hq] at hqu'
  push_cast at hqu'
  have hw1ne : (hyp.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne _)
  exact_mod_cast mul_left_cancel₀ hw1ne hqu'

open OddOrder.Peterfalvi.S11 in
/-- **Peterfalvi (11.8.1), the residue `d ≡ 1 (mod q)`** (§9 count, named obligation).  `d = |Ū|`
(`charParam_d_eq_u`), and `|Ū| ≡ 1 (mod q)` is the chief-factor image of the Frobenius congruence
(`mkSection11CharacterData_u_modEq_one`). -/
theorem Hypothesis.charParam_d_modEq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd) :
    params.d ≡ 1 [MOD hyp.w1] := by
  have := hyp.finiteG
  classical
  have hnt : TypePNontrivialCore M hyp.typeP :=
    typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  obtain ⟨chief, -⟩ := exists_chiefFactorData hG (hyp.toTypesIIIIIIVSetup htype hnt)
  rw [hyp.charParam_d_eq_u hG htype params hmu hnt chief]
  exact hyp.mkSection11CharacterData_u_modEq_one (hyp.toTypesIIIIIIVSetup htype hnt) chief hnt.1

/-- **Peterfalvi (11.8.1), `δ = 1`**.  The (10.3) column sign `δ ∈ {±1}` equals `1`.  From the index
relation `n·w₁ = d − δ` (`n_formula`), `w₁ ∣ d − δ`; from the (11.8.1) residue `d ≡ 1 (mod w₁)`
(`charParam_d_modEq_one`), `w₁ ∣ 1 − d`; adding, `w₁ ∣ 1 − δ`.  With `δ = −1` this forces `w₁ ∣ 2`,
impossible for the odd `w₁ = |W₁| ≥ 3`.  Hence `δ = 1`.  (This is the pure arithmetic of (11.8.1);
the §9/Frobenius content is isolated in `charParam_d_modEq_one`.) -/
theorem Hypothesis.charParam_delta_eq_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hyp : Hypothesis M) (htype : IsTypeIII M ∨ IsTypeIV M)
    (params : CharacterParameters hyp) (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1) : params.delta = 1 := by
  have hw1odd : Odd hyp.w1 := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.W1)
  have hw1gt : 1 < hyp.w1 := (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.typeP.W1_nontrivial
  have hw1 : 3 ≤ hyp.w1 := by obtain ⟨k, hk⟩ := hw1odd; omega
  have hddelta : (hyp.w1 : ℤ) ∣ (params.d : ℤ) - params.delta :=
    ⟨params.n, by rw [mul_comm]; exact params.n_formula.symm⟩
  have hd1 : (hyp.w1 : ℤ) ∣ (1 : ℤ) - (params.d : ℤ) :=
    Nat.modEq_iff_dvd.mp (hyp.charParam_d_modEq_one hG htype params hmu)
  have hkey : (hyp.w1 : ℤ) ∣ (1 : ℤ) - params.delta := by
    have hcomb : (1 : ℤ) - params.delta = ((params.d : ℤ) - params.delta) + (1 - (params.d : ℤ)) :=
        by
      ring
    rw [hcomb]; exact dvd_add hddelta hd1
  rcases hδpm with h1 | hm1
  · exact h1
  · exfalso
    rw [hm1] at hkey
    have h2 : (hyp.w1 : ℤ) ∣ 2 := by simpa using hkey
    have hle := Int.le_of_dvd (by norm_num) h2
    have hw1Z : (3 : ℤ) ≤ (hyp.w1 : ℤ) := by exact_mod_cast hw1
    omega

end OddOrder.Peterfalvi.S12


