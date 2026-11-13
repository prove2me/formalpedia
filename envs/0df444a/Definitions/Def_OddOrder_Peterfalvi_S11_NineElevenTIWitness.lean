-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTIWitness
-- name    : OddOrder_Peterfalvi_S11_NineElevenTIWitness
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T12:37:15.84394+00:00
-- url     : https://prove2.me/theorems/113643e3-bae8-4f8d-a196-b9fa87c6c267
-- title:
--   Peterfalvi (9.11.2): the TI witness $U_1\cap U_1^w=C$
-- statement:
--   Formalizes the TI witness $U_1\cap U_1^w=C$ for $w\in W_1^\#$ in Peterfalvi (9.11.2) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §9, p. 56).
--
--   Main declarations: `mem_cuSubOf_of_forall_smul_eq` (Membership from summand-fixing); `exists_w1_rep_Hpart` (Every summand is a `W₁`-translate of the generator); `Hpart_injective` (The summands are pairwise distinct).
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S11_NineElevenTIWitness.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S11_NineElevenTIWitness.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenMackeyNorm

namespace OddOrder.Peterfalvi.S11

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs.Ch03 (IsAInvariant)

open OddOrder.Isaacs.Ch03.IsAInvariant (quotientMulAutHom)

open scoped Pointwise

variable {G : Type*} [Group G] {M : Subgroup G}

section ConjugationDictionary

variable [Finite G] {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

set_option backward.isDefEq.respectTransparency false in
/-- **Membership from summand-fixing**: a `U`-element `g` whose chief-factor action fixes the
Clifford summand `H_k` pointwise lies in the realized single-factor centralizer
`C_U(H_k) = cuSubOf caseA k`.  Builds the abstract kernel witness of `cuSubOf`'s
double-`map` definition (converse of `forall_smul_eq_of_mem_cuSubOf`). -/
theorem mem_cuSubOf_of_forall_smul_eq (caseA : CliffordCaseAData chars) (k : Fin data.q)
    {g : G} (hgU : g ∈ data.typeP.U)
    (hfix : ∀ y ∈ caseA.Hpart k,
      quotientMulAutHom chief.N_aInvariant
        (⟨g, Subgroup.mem_sup_left hgU⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) y = y) :
    g ∈ cuSubOf caseA k := by
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨g, Subgroup.mem_sup_left hgU⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha
  have hker : a ∈ (aInvariantRestrictAut (caseA.Hpart_aInvariant k)).ker := by
    change aInvariantRestrictAut (caseA.Hpart_aInvariant k) a = 1
    ext z
    rw [MulAut.one_apply, aInvariantRestrictAut_coe]
    exact hfix _ z.2
  exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_map.mpr ⟨a, hker, rfl⟩, rfl⟩

/-- **Summand-fixing from membership** (the converse dictionary): a member of the realized
`C_U(H_k)` acts trivially on `H_k` through the chief-factor action.  Extracts the abstract
kernel witness via `mem_ker_of_realized_mem_cuSubOf`. -/
theorem forall_smul_eq_of_mem_cuSubOf (caseA : CliffordCaseAData chars) (k : Fin data.q)
    {g : G} (hg : g ∈ cuSubOf caseA k) (hgU : g ∈ data.typeP.U) :
    ∀ y ∈ caseA.Hpart k,
      quotientMulAutHom chief.N_aInvariant
        (⟨g, Subgroup.mem_sup_left hgU⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) y = y := by
  set a : ↥(typeP_quotientCoprimeAction data.typeP data.nontrivial.1 chief.N_aInvariant).U :=
    ⟨⟨g, Subgroup.mem_sup_left hgU⟩, Subgroup.mem_subgroupOf.mpr hgU⟩ with ha
  have hag : g = (((typeP_quotientCoprimeAction data.typeP data.nontrivial.1
      chief.N_aInvariant).U.subtype a : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) := rfl
  have hker := mem_ker_of_realized_mem_cuSubOf caseA k a (hag ▸ hg)
  have hker1 : aInvariantRestrictAut (caseA.Hpart_aInvariant k) a = 1 := hker
  intro y hy
  have h := aInvariantRestrictAut_coe (caseA.Hpart_aInvariant k) a ⟨y, hy⟩
  rw [hker1] at h
  change (uActionHom data chief) a y = y
  simpa [MulAut.one_apply] using h.symm

/-- **The `W₁ ↔` summand conjugation dictionary, `≤` form**: if `H_j = φ(x) • H_i` for
`x ∈ U·W₁` then `C_U(H_i)^x ≤ C_U(H_j)`.  Conjugation equivariance
`φ(x·g·x⁻¹) = φ(x)·φ(g)·φ(x)⁻¹` through the membership dictionary; `x` normalizes `U`
(`U ⊴ U·W₁`). -/
theorem conj_smul_cuSubOf_le_of_Hpart_smul (caseA : CliffordCaseAData chars)
    {x : G} (hx : x ∈ data.typeP.U ⊔ data.typeP.W1) {i j : Fin data.q}
    (hHj : caseA.Hpart j = quotientMulAutHom chief.N_aInvariant
      (⟨x, hx⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) • caseA.Hpart i) :
    MulAut.conj x • cuSubOf caseA i ≤ cuSubOf caseA j := by
  intro g' hg'
  rw [Subgroup.mem_smul_pointwise_iff_exists] at hg'
  obtain ⟨g, hgK, rfl⟩ := hg'
  have hgU : g ∈ data.typeP.U := cuSubOf_le_U caseA i hgK
  have hxg : (MulAut.conj x) • g = x * g * x⁻¹ := rfl
  have hgU' : x * g * x⁻¹ ∈ data.typeP.U := by
    have hnorm : x ∈ Subgroup.normalizer data.typeP.U :=
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U) hx
    exact (Subgroup.mem_normalizer_iff.mp hnorm g).mp hgU
  rw [hxg]
  refine mem_cuSubOf_of_forall_smul_eq caseA j hgU' ?_
  intro y hy
  have hpack : (⟨x * g * x⁻¹, Subgroup.mem_sup_left hgU'⟩ :
      ↥(data.typeP.U ⊔ data.typeP.W1))
      = (⟨x, hx⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (⟨g, Subgroup.mem_sup_left hgU⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
          * (⟨x, hx⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))⁻¹ := rfl
  rw [hpack, map_mul, map_mul, map_inv, MulAut.mul_apply, MulAut.mul_apply]
  have hyin : (quotientMulAutHom chief.N_aInvariant
      (⟨x, hx⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)))⁻¹ y ∈ caseA.Hpart i := by
    rw [hHj] at hy
    have h := Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mp hy
    simpa [MulAut.smul_def] using h
  rw [forall_smul_eq_of_mem_cuSubOf caseA i hgK hgU _ hyin, ← MulAut.mul_apply,
    mul_inv_cancel, MulAut.one_apply]

/-- **The `W₁ ↔` summand conjugation dictionary**: if `H_j = φ(x) • H_i` for `x ∈ U·W₁` then
`C_U(H_i)^x = C_U(H_j)` — the realized form of the book's `U₁^w = C_U(H₁^w)` in (9.11.2).
Both inclusions are `conj_smul_cuSubOf_le_of_Hpart_smul` (the reverse at `x⁻¹`, along
`H_i = φ(x⁻¹) • H_j`). -/
theorem conj_smul_cuSubOf_of_Hpart_smul (caseA : CliffordCaseAData chars)
    {x : G} (hx : x ∈ data.typeP.U ⊔ data.typeP.W1) {i j : Fin data.q}
    (hHj : caseA.Hpart j = quotientMulAutHom chief.N_aInvariant
      (⟨x, hx⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) • caseA.Hpart i) :
    MulAut.conj x • cuSubOf caseA i = cuSubOf caseA j := by
  refine le_antisymm (conj_smul_cuSubOf_le_of_Hpart_smul caseA hx hHj) ?_
  have hxinv : x⁻¹ ∈ data.typeP.U ⊔ data.typeP.W1 := inv_mem hx
  have hHi : caseA.Hpart i = quotientMulAutHom chief.N_aInvariant
      (⟨x⁻¹, hxinv⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) • caseA.Hpart j := by
    have hpack : (⟨x⁻¹, hxinv⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))
        = (⟨x, hx⟩ : ↥(data.typeP.U ⊔ data.typeP.W1))⁻¹ := rfl
    rw [hpack, map_inv, hHj, inv_smul_smul]
  have hle := conj_smul_cuSubOf_le_of_Hpart_smul caseA hxinv hHi
  intro g' hg'
  have h1 : (MulAut.conj x⁻¹) • g' ∈ cuSubOf caseA i :=
    hle (Subgroup.smul_mem_pointwise_smul _ _ _ hg')
  refine (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mpr
    ⟨(MulAut.conj x⁻¹) • g', h1, ?_⟩
  rw [smul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]

omit [Finite G] in
/-- **Every summand is a `W₁`-translate of the generator**: `H_k = φ(w)•S₀` for some
`w ∈ U·W₁` with `(w : G) ∈ W₁`.  The `orbitRep` translate decomposes as `rep = u₀·w₀`
(`U ⊴ U·W₁`), i.e. `rep = w₀·(w₀⁻¹u₀w₀)` with `W₁`-part on the left, and the `U`-part is
absorbed by the `U`-invariance of `S₀` (`S0_aInvariant`). -/
theorem exists_w1_rep_Hpart (caseA : CliffordCaseAData chars) (k : Fin data.q) :
    ∃ w : ↥(data.typeP.U ⊔ data.typeP.W1), (w : G) ∈ data.typeP.W1 ∧
      caseA.Hpart k = quotientMulAutHom chief.N_aInvariant w • caseA.S0 := by
  have hUnorm : (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer data.typeP.W1_normalizes_U)
  have htop : data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
      ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hrep : caseA.orbitRep k ∈ data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)
      ⊔ data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨u₀, hu₀, w₀, hw₀, hmul⟩ := Subgroup.mem_sup_of_normal_left.mp hrep
  refine ⟨w₀, hw₀, ?_⟩
  have hrepeq : caseA.orbitRep k = w₀ * (w₀⁻¹ * u₀ * w₀) := by
    rw [← hmul]; group
  have hu₁U : w₀⁻¹ * u₀ * w₀
      ∈ data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1) := by
    have h := hUnorm.conj_mem u₀ hu₀ w₀⁻¹
    rwa [inv_inv] at h
  have hfix : quotientMulAutHom chief.N_aInvariant (w₀⁻¹ * u₀ * w₀) • caseA.S0
      = caseA.S0 :=
    caseA.S0_aInvariant ⟨w₀⁻¹ * u₀ * w₀, hu₁U⟩
  rw [caseA.Hpart_orbit k, hrepeq, map_mul, mul_smul, hfix]

omit [Finite G] in
/-- **The summands are pairwise distinct**: `k ↦ H_k` is injective — independent
(`Hpart_iSupIndep`) subgroups of order `p > 1` cannot coincide. -/
theorem Hpart_injective (caseA : CliffordCaseAData chars) :
    Function.Injective caseA.Hpart := by
  intro k k' hkk'
  by_contra hne
  have hdisj : Disjoint (caseA.Hpart k) (caseA.Hpart k') :=
    caseA.Hpart_iSupIndep.pairwiseDisjoint hne
  rw [hkk', disjoint_self] at hdisj
  have hcard := caseA.Hpart_order k'
  have hp := chief.p_prime.one_lt
  rw [hdisj, Subgroup.card_bot] at hcard
  omega

/-- **The summands form a full free `W₁`-orbit of `S₀`**: every `W₁`-element carries the
generator onto *some* summand.  The representative map `k ↦ w_k` of `exists_w1_rep_Hpart`
is injective (`Hpart_injective`), hence bijective onto the `q`-element realized `W₁`. -/
theorem forall_w1_exists_Hpart_smul (caseA : CliffordCaseAData chars) :
    ∀ v : ↥(data.typeP.U ⊔ data.typeP.W1), (v : G) ∈ data.typeP.W1 →
      ∃ k : Fin data.q,
        caseA.Hpart k = quotientMulAutHom chief.N_aInvariant v • caseA.S0 := by
  classical
  choose w hwW hwS0 using exists_w1_rep_Hpart caseA
  have hcardW : Nat.card
      ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) = data.q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (le_sup_right : data.typeP.W1 ≤ data.typeP.U ⊔ data.typeP.W1)).toEquiv]
    rfl
  set w' : Fin data.q → ↥(data.typeP.W1.subgroupOf (data.typeP.U ⊔ data.typeP.W1)) :=
    fun k => ⟨w k, Subgroup.mem_subgroupOf.mpr (hwW k)⟩ with hw'
  have hinj : Function.Injective w' := by
    intro k k' h
    have hww : w k = w k' := congrArg Subtype.val h
    exact Hpart_injective caseA (by rw [hwS0 k, hwS0 k', hww])
  have hbij : Function.Bijective w' := by
    rw [Nat.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcardW]
  intro v hv
  obtain ⟨k, hk⟩ := hbij.2 ⟨v, Subgroup.mem_subgroupOf.mpr hv⟩
  have hwkv : w k = v := congrArg Subtype.val hk
  exact ⟨k, by rw [hwS0 k, hwkv]⟩

/-- **`W₁` is generated by any nonidentity element** (prime order `q`): for `w ∈ W₁^#`,
every `v ∈ W₁` is an integer power of `w`. -/
theorem exists_zpow_of_mem_W1 {w : G} (hw : w ∈ data.typeP.W1) (hne : w ≠ 1) :
    ∀ v ∈ data.typeP.W1, ∃ n : ℤ, w ^ n = v := by
  have hqp : (data.q).Prime := data.nontrivial.2.1
  have hcard : Nat.card ↥data.typeP.W1 = data.q := rfl
  have hordeq : orderOf w = orderOf (⟨w, hw⟩ : ↥data.typeP.W1) :=
    orderOf_injective data.typeP.W1.subtype (Subgroup.subtype_injective _)
      (⟨w, hw⟩ : ↥data.typeP.W1)
  have hord : orderOf w ∣ data.q := by
    rw [hordeq, ← hcard]
    exact orderOf_dvd_natCard _
  have hordq : orderOf w = data.q := by
    rcases hqp.eq_one_or_self_of_dvd _ hord with h1 | h
    · exact absurd (orderOf_eq_one_iff.mp h1) hne
    · exact h
  have hzeq : Subgroup.zpowers w = data.typeP.W1 := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hw)
    rw [Nat.card_zpowers, hordq, hcard]
  intro v hv
  rw [← hzeq] at hv
  exact Subgroup.mem_zpowers_iff.mp hv

end ConjugationDictionary

section TIWitness

variable [Finite G] {data : TypesIIIIIIVSetup M} {chief : ChiefFactorData data}
  {chars : Section11CharacterData data chief}

/-- **Conjugation by a `W₁`-element permutes the single-factor centralizers**:
`C_U(H_i)^w = C_U(H_j)` for some `j` — the summand `φ(w)•H_i` is itself a summand
(`forall_w1_exists_Hpart_smul` at `w·w_i`), and the dictionary transports the
centralizer. -/
theorem exists_conj_smul_cuSubOf_eq (caseA : CliffordCaseAData chars)
    {w : G} (hw : w ∈ data.typeP.W1) (i : Fin data.q) :
    ∃ j : Fin data.q, MulAut.conj w • cuSubOf caseA i = cuSubOf caseA j := by
  have hwL : w ∈ data.typeP.U ⊔ data.typeP.W1 := Subgroup.mem_sup_right hw
  obtain ⟨wi, hwiW, hwiS0⟩ := exists_w1_rep_Hpart caseA i
  have hmemW : (((⟨w, hwL⟩ : ↥(data.typeP.U ⊔ data.typeP.W1)) * wi :
      ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.W1 :=
    mul_mem hw hwiW
  obtain ⟨j, hj⟩ := forall_w1_exists_Hpart_smul caseA _ hmemW
  refine ⟨j, conj_smul_cuSubOf_of_Hpart_smul caseA hwL ?_⟩
  rw [hj, map_mul, mul_smul, ← hwiS0]

/-- **Peterfalvi (9.11.2), the TI-witness discharged** (issue 9083 Phase E).

Book: *"If `w ∈ W₁^#`, then `U₁ ∩ U₁^w = C`."*  Under the (9.11.1) equality-configuration
degree dichotomy `hdeg` (every `𝒮(H₀C)`-member has degree `qu` or `qa` — the `𝒮₃`-side is
the landed squeeze output, the `𝒮₂`-side the `𝒮₂ = 𝒮₁` extraction), the witness
`U₁ = C_U(H_{i₀})` satisfies `C ≤ U₁ ≤ U`, `[U:U₁] = a`, and the TI-identity for every
`w ∈ W₁^#`:

* if **all** single-factor centralizers coincide, `C = ⋂ₖ C_U(H_k)` equals the common value
  (`mem_cSub_of_forall_mem_cuSubOf`), and `U₁ ∩ U₁^w = C ∩ C^w = C` — the book's `u = a`
  branch, *absorbed* rather than refuted (as in Phase B);
* otherwise `U₁^w = C_U(H_j) ≠ U₁`: else `⟨w⟩ = W₁` (prime order, `exists_zpow_of_mem_W1`)
  would fix `U₁`, and the free `W₁`-orbit structure of the summands
  (`exists_w1_rep_Hpart` + the conjugation dictionary) would force all centralizers equal.
  The Phase-B pair dichotomy `nineElevenTwo_relIndex_dichotomy` then pins
  `[U : U₁ ∩ U₁^w] ∈ {u, a}`; the `a`-branch collapses `U₁ = U₁^w` by strict index
  monotonicity (`relIndex_lt_relIndex_of_le_of_ne`), so the index is `u = [U:C]` and
  `U₁ ∩ U₁^w = C` by index equality. -/
theorem nineElevenTwoTIWitness_of_degree_dichotomy (caseA : CliffordCaseAData chars)
    (hdeg : ∀ φ ∈ sOf data (chief.H0 ⊔ cSub data chief),
      (φ : ↥M → ℂ) 1 = ((data.q * chars.u : ℕ) : ℂ) ∨
      (φ : ↥M → ℂ) 1 = ((data.q * caseA.a : ℕ) : ℂ)) :
    NineElevenTwoTIWitness caseA := by
  classical
  have hq0 : 0 < data.q := data.nontrivial.2.1.pos
  by_cases hall : ∀ k, cuSubOf caseA k = cuSubOf caseA ⟨0, hq0⟩
  · -- all single-factor centralizers coincide: `C = U₁`, the TI-identity is trivial
    have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ := by
      apply le_antisymm (cSub_le_cuSubOf caseA ⟨0, hq0⟩)
      intro g hg
      exact mem_cSub_of_forall_mem_cuSubOf caseA (fun k => (hall k).symm ▸ hg)
    refine ⟨cuSubOf caseA ⟨0, hq0⟩, cSub_le_cuSubOf caseA ⟨0, hq0⟩,
      cuSubOf_le_U caseA ⟨0, hq0⟩, relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, ?_⟩
    intro w hw _hne
    obtain ⟨j, hj⟩ := exists_conj_smul_cuSubOf_eq caseA hw ⟨0, hq0⟩
    rw [hj, hall j, inf_idem, ← hCeq]
  · -- some centralizer differs: the pair dichotomy resolves to index `u`
    push Not at hall
    obtain ⟨k₀, hk₀⟩ := hall
    refine ⟨cuSubOf caseA ⟨0, hq0⟩, cSub_le_cuSubOf caseA ⟨0, hq0⟩,
      cuSubOf_le_U caseA ⟨0, hq0⟩, relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, ?_⟩
    intro w hw hne
    obtain ⟨j, hj⟩ := exists_conj_smul_cuSubOf_eq caseA hw ⟨0, hq0⟩
    -- `C_U(H_j) ≠ U₁`: else `⟨w⟩ = W₁` fixes `U₁` and transitivity collapses all
    have hjne : cuSubOf caseA j ≠ cuSubOf caseA ⟨0, hq0⟩ := by
      intro hjeq
      apply hk₀
      have hwfix : MulAut.conj w • cuSubOf caseA ⟨0, hq0⟩ = cuSubOf caseA ⟨0, hq0⟩ := by
        rw [hj, hjeq]
      have hallfix : ∀ v ∈ data.typeP.W1,
          MulAut.conj v • cuSubOf caseA ⟨0, hq0⟩ = cuSubOf caseA ⟨0, hq0⟩ := by
        intro v hv
        obtain ⟨n, rfl⟩ := exists_zpow_of_mem_W1 hw hne v hv
        rw [map_zpow]
        have hstab : MulAut.conj w
            ∈ MulAction.stabilizer (MulAut G) (cuSubOf caseA ⟨0, hq0⟩) :=
          MulAction.mem_stabilizer_iff.mpr hwfix
        exact MulAction.mem_stabilizer_iff.mp (zpow_mem hstab n)
      obtain ⟨w0, hw0W, hw0⟩ := exists_w1_rep_Hpart caseA k₀
      obtain ⟨wi, hwiW, hwi⟩ := exists_w1_rep_Hpart caseA ⟨0, hq0⟩
      have hvW : ((w0 * wi⁻¹ : ↥(data.typeP.U ⊔ data.typeP.W1)) : G) ∈ data.typeP.W1 :=
        mul_mem hw0W (inv_mem hwiW)
      have hHk₀ : caseA.Hpart k₀ = quotientMulAutHom chief.N_aInvariant (w0 * wi⁻¹)
          • caseA.Hpart ⟨0, hq0⟩ := by
        rw [hw0, hwi, map_mul, mul_smul, map_inv, inv_smul_smul]
      have hdict := conj_smul_cuSubOf_of_Hpart_smul caseA (w0 * wi⁻¹).2 hHk₀
      rw [← hdict]
      exact hallfix _ hvW
    have hij : (⟨0, hq0⟩ : Fin data.q) ≠ j := fun h => hjne (by rw [h])
    rcases nineElevenTwo_relIndex_dichotomy caseA hij hdeg with hu | ha
    · -- index `u`: `C = U₁ ∩ U₁^w` by index equality
      have hCle : cSub data chief ≤ cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j :=
        le_inf (cSub_le_cuSubOf caseA ⟨0, hq0⟩) (cSub_le_cuSubOf caseA j)
      have hCeq : cSub data chief = cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne hCle
          (inf_le_left.trans (cuSubOf_le_U caseA ⟨0, hq0⟩)) (fun h => hne' h.symm)
        rw [hu, relIndex_cSub_U_eq_u chars] at hlt
        exact lt_irrefl _ hlt
      rw [hj, ← hCeq]
    · -- index `a`: would force `C_U(H_{i₀}) = C_U(H_j)`, contradicting `hjne`
      exfalso
      apply hjne
      have hi : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j = cuSubOf caseA ⟨0, hq0⟩ := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_left : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j
            ≤ cuSubOf caseA ⟨0, hq0⟩)
          (cuSubOf_le_U caseA ⟨0, hq0⟩) (fun h => hne' h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA ⟨0, hq0⟩, ha] at hlt
        exact lt_irrefl _ hlt
      have hjeq : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j = cuSubOf caseA j := by
        by_contra hne'
        have hlt := OddOrder.Peterfalvi.S07.relIndex_lt_relIndex_of_le_of_ne
          (inf_le_right : cuSubOf caseA ⟨0, hq0⟩ ⊓ cuSubOf caseA j ≤ cuSubOf caseA j)
          (cuSubOf_le_U caseA j) (fun h => hne' h.symm)
        rw [relIndex_cuSubOf_U_eq_a caseA j, ha] at hlt
        exact lt_irrefl _ hlt
      rw [← hjeq, hi]

end TIWitness

end OddOrder.Peterfalvi.S11


