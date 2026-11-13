-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:43:05.044844+00:00
-- url     : https://prove2.me/theorems/83a98d39-2de3-4626-8c3d-24d2aa41c42f
-- title:
--   BG §16: type classification and Theorem A bridges
-- statement:
--   Continues the type-V Singer file for Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §16 (Theorem A and Proposition 16.1) with the reverse type-classification bridges, the type II–IV criteria and the corresponding faithful-action results, including Corollary 15.5(c) / Theorem A(6) ($M'/M_F$ nilpotent).
--
--   Main declarations: `conjActionOfMemNormalizer` (Conjugation action of the cyclic group `⟨x⟩` on a subgroup `N` it normalizes); `derivedInG_quotient_maxNilpotentNormalHall_isNilpotent`.
--
--   The bundle also proves 32 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeBridges.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeBridges.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeVSinger

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Prop 16.1(d)/(f) reverse, `M_F = M_σ` from `U = ⊥`** (the `M_F = M_σ` conjunct of `hVP1`,
mmd L4478): a type-`P` datum with trivial complement `U = ⊥` has `M_F = M_σ`.  Sandwiching:
`M' = M_F ⊔ U = M_F` (`TypePData.derivedInG_eq_fitting_sup_U` with `U = ⊥`), while always
`M_F ≤ M_σ ≤ M'` (`maxNilpotentNormalHall_le_Msigma`, `Msigma_le_derived`); so `M_F = M_σ = M'`.
Axiom-clean (does *not* cite Theorem A(8), unlike the `M_F = M_σ` step of
`typeFData_of_kappa_eq_bot`).
This is the structural half of clause (d): the `IsTypeP1` half is the (deeper) `κ` refinement. -/
theorem mf_eq_msigma_of_typePData_U_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M) (hU : data.U = ⊥) :
    S15.MF M = OddOrder.BG.Ch3.S10.Msigma M := by
  -- `M' = M_F` since `M' = M_F ⊔ U` and `U = ⊥`.
  have hderiv : derivedInG M = S15.MF M := by
    rw [data.derivedInG_eq_fitting_sup_U, hU, sup_bot_eq]
  -- `M_F ≤ M_σ` always; `M_σ ≤ M' = M_F`; hence equal.
  refine le_antisymm (S15.maxNilpotentNormalHall_le_Msigma hG hM) ?_
  exact hderiv ▸ OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM

/-- **Type V vs a nontrivial complement** (general `U = ⊥` exclusivity core): a maximal subgroup
cannot be both type `V` (a `TypeVData`, so `U = ⊥` and `M' = M_F`) and carry a `TypePData` with
`U ≠ ⊥`.  Both data fix the *same* `H = maxNilpotentNormalHall M` and present `U` as a complement of
`H` in `M' = M_F ⊔ U`; the type-V witness forces `M' = M_F`, so the other `U ≤ H`, hence
(disjointness of the complement) `U = ⊥`.  Generalises the `not_isTypeII_of_isTypeV` argument and is
the common core of the `III/IV ≠ V` exclusivity used in the reverse bridges. -/
theorem not_isTypeV_of_typePData_U_ne_bot {M : Subgroup G}
    (hV : OddOrder.GroupTheory.IsTypeV M) (data : TypePData M) (hU : data.U ≠ ⊥) : False := by
  obtain ⟨dV⟩ := hV
  have hMV : derivedInG M = maxNilpotentNormalHall M := by
    rw [dV.typeP.derivedInG_eq_fitting_sup_U, dV.U_eq_bot, sup_bot_eq]
  have hUH : data.U ≤ data.H := by
    rw [data.H_eq]
    have hsup : maxNilpotentNormalHall M ⊔ data.U = maxNilpotentNormalHall M := by
      rw [← data.derivedInG_eq_fitting_sup_U, hMV]
    exact le_sup_right.trans (le_of_eq hsup)
  have hdisj : Disjoint (data.H.subgroupOf (derivedInG M))
      (data.U.subgroupOf (derivedInG M)) := data.derived_complement.disjoint
  have hUsub : data.U.subgroupOf (derivedInG M) = ⊥ := by
    rw [← inf_of_le_left (Subgroup.subgroupOf_mono (derivedInG M) hUH), inf_comm,
      disjoint_iff.mp hdisj]
  have hUbot : data.U = ⊥ :=
    (inf_of_le_left data.U_le).symm.trans
      (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hUsub))
  exact hU hUbot

/-- **Type V and Type II are mutually exclusive** (the `U = ⊥` vs `U ≠ ⊥` dichotomy): a type-II
maximal has a nontrivial complement `U ≠ ⊥` (`TypePNontrivialCore`), ruled out against a type-V
witness by `not_isTypeV_of_typePData_U_ne_bot`.  Supplies the `¬ M_P2` half of `hVP1`. -/
theorem not_isTypeII_of_isTypeV {M : Subgroup G} :
    OddOrder.GroupTheory.IsTypeV M → ¬ OddOrder.GroupTheory.IsTypeII M :=
  fun hV ⟨dII⟩ => not_isTypeV_of_typePData_U_ne_bot hV dII.typeP dII.common.1

/-- **Type III/IV and Type V are mutually exclusive** (the `U ≠ ⊥` vs `U = ⊥` dichotomy): types III
and IV carry a `TypePData` with nontrivial complement `U ≠ ⊥` (`TypePNontrivialCore`), ruled out
against a type-V witness by `not_isTypeV_of_typePData_U_ne_bot`.  Used in the `hIIIIVP1` reverse
bridge to force `M_F ≠ M_σ` (else the type would be V). -/
theorem not_isTypeV_of_isTypeIII_or_IV {M : Subgroup G}
    (h : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) :
    ¬ OddOrder.GroupTheory.IsTypeV M := by
  intro hV
  rcases h with hd | hd
  · exact not_isTypeV_of_typePData_U_ne_bot hV hd.some.typeP hd.some.common.1
  · exact not_isTypeV_of_typePData_U_ne_bot hV hd.some.typeP hd.some.common.1

/-- **Type-`P` complements are `M`-conjugate** (Schur–Zassenhaus): for any two `TypePData` on a
maximal subgroup `M`, the complements `U` are conjugate by an element of `M`.  Both `U_i` complement
the nilpotent normal Hall subgroup `H = M_F` in `M' = [M,M]` (the `derived_complement` field, with
`H` witness-independent via `H_eq`).  `H` is a Hall subgroup of `M`
(`maxNilpotentNormalHall_isHall`), hence Hall in `M'` (its `M'`-index divides its `M`-index), so
`|H|` and `[M' : H] = |U|` are coprime; Schur–Zassenhaus conjugacy of complements of a normal Hall
subgroup (`IsComplement'.exists_conj_of_coprime`, applied inside `↥M'`) gives `n ∈ H ≤ M` with
`n · U_1 · n⁻¹ = U_2`.  This is the engine behind the `II ≠ III/IV` exclusivity
(`not_isTypeII_of_isTypeIII_or_IV`): it transfers the normalizer condition `N_G(U) ≤ M` between
witnesses. -/
theorem typePData_exists_conj_U [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (d1 d2 : TypePData M) :
    ∃ n : G, n ∈ M ∧ MulAut.conj n • d1.U = d2.U := by
  have hH_le : maxNilpotentNormalHall M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  have hH_le_M : maxNilpotentNormalHall M ≤ M := maxNilpotentNormalHall_le M
  have hM'_le_M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hU1_le : d1.U ≤ derivedInG M := d1.U_le
  have hU2_le : d2.U ≤ derivedInG M := d2.U_le
  -- Solvability of `↥M'` (transport along the inclusion `↥M' ↪ ↥M`).
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hM'solv : Group.IsSolvable ↥(derivedInG M) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hM'_le_M)
  -- `H ◁ M'` (set-form normalizer, `M' ≤ M ≤ N_G(H)`).
  have hM'_le_NH : derivedInG M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    hM'_le_M.trans (maxNilpotentNormalHall_le_normalizer M)
  have hHn_normal : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hH_le).mpr hM'_le_NH
  -- Both `U_i` complement `H` in `M'` (`derived_complement`, rewritten via `H = M_F`).
  have hK1 : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).IsComplement'
      (d1.U.subgroupOf (derivedInG M)) := by rw [← d1.H_eq]; exact d1.derived_complement
  have hK2 : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).IsComplement'
      (d2.U.subgroupOf (derivedInG M)) := by rw [← d2.H_eq]; exact d2.derived_complement
  -- Coprimality `|H|` vs `[M' : H]`: `[M' : H] ∣ [M : H]` and `H` is Hall in `M`.
  have hdvd' : ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).index ∣
      ((maxNilpotentNormalHall M).subgroupOf M).index := by
    have hmul := Subgroup.relIndex_mul_relIndex (maxNilpotentNormalHall M) (derivedInG M) M
      hH_le hM'_le_M
    exact ⟨(derivedInG M).relIndex M, hmul.symm⟩
  have hcardEq : Nat.card ↥((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
      = Nat.card ↥((maxNilpotentNormalHall M).subgroupOf M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH_le_M).toEquiv]
  have hcop : Nat.Coprime
      (Nat.card ↥((maxNilpotentNormalHall M).subgroupOf (derivedInG M)))
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)).index := by
    rw [hcardEq]
    exact ((maxNilpotentNormalHall_isHall M).coprime_index).coprime_dvd_right hdvd'
  -- Schur–Zassenhaus inside `↥M'`: `n ∈ H` with `(U_1)ᶜᵒⁿʲ = U_2`.
  obtain ⟨n, hnH, hnconj⟩ :=
    Subgroup.IsComplement'.exists_conj_of_coprime hcop (Or.inl inferInstance) hK1 hK2
  -- Translate the conjugacy back to `G` (intertwine `M'.subtype` with `conj`).
  have hintertwine : (derivedInG M).subtype.comp (MulAut.conj n).toMonoidHom =
      (MulAut.conj (n : G)).toMonoidHom.comp (derivedInG M).subtype := by
    ext ⟨y, hy⟩; rfl
  have hsmul_map : ∀ K : Subgroup G,
      MulAut.conj (n : G) • K = K.map (MulAut.conj (n : G)).toMonoidHom := by
    intro K; rw [Subgroup.pointwise_smul_def]; rfl
  have hLHS : ((d1.U.subgroupOf (derivedInG M)).map (MulAut.conj n).toMonoidHom).map
      (derivedInG M).subtype = MulAut.conj (n : G) • d1.U := by
    rw [Subgroup.map_map, hintertwine, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hU1_le, hsmul_map]
  have hRHS : (d2.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype = d2.U :=
    Subgroup.map_subgroupOf_eq_of_le hU2_le
  refine ⟨(n : G), hM'_le_M n.2, ?_⟩
  calc MulAut.conj (n : G) • d1.U
      = ((d1.U.subgroupOf (derivedInG M)).map (MulAut.conj n).toMonoidHom).map
          (derivedInG M).subtype := hLHS.symm
    _ = (d2.U.subgroupOf (derivedInG M)).map (derivedInG M).subtype := by rw [hnconj]
    _ = d2.U := hRHS

/-- **Normalizer condition transfers between type-`P` complements** (mmd L4478 reverse): for two
`TypePData` on a maximal `M`, `N_G(U_1) ≤ M ⟺ N_G(U_2) ≤ M`.  The complements are `M`-conjugate
(`typePData_exists_conj_U`), and conjugation by `n ∈ M` fixes `M`
(`conj_smul_eq_self_of_mem_normalizer`) and intertwines normalizers (`normalizer_conj_smul`).  This
is the bridge that makes the type-II condition `¬ N_G(U) ≤ M` and the type-III/IV condition
`N_G(U) ≤ M` contradictory on the same `M`. -/
theorem typePData_normalizer_U_le_iff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (d1 d2 : TypePData M) :
    Subgroup.normalizer (d1.U : Set G) ≤ M ↔ Subgroup.normalizer (d2.U : Set G) ≤ M := by
  obtain ⟨n, hnM, hconj⟩ := typePData_exists_conj_U hG hM d1 d2
  have hnorm : Subgroup.normalizer (d2.U : Set G)
      = MulAut.conj n • Subgroup.normalizer (d1.U : Set G) := by
    rw [← hconj]; exact (normalizer_conj_smul n d1.U).symm
  have hMfix : MulAut.conj n • M = M :=
    conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hnM)
  rw [hnorm]
  constructor
  · intro h1
    calc MulAut.conj n • Subgroup.normalizer (d1.U : Set G)
        ≤ MulAut.conj n • M := Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr h1
      _ = M := hMfix
  · intro h2
    have h3 : MulAut.conj n • Subgroup.normalizer (d1.U : Set G) ≤ MulAut.conj n • M := by
      rw [hMfix]; exact h2
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mp h3

/-- **Type II and Type III/IV are mutually exclusive** (mmd L4478 reverse): the type-II condition
`¬ N_G(U) ≤ M` (`TypeIIData.normalizer_not_le`) and the type-III/IV condition `N_G(U) ≤ M`
(`TypeIIIData.normalizer_le`/`TypeIVData.normalizer_le`) cannot both hold on a maximal `M`, since
the
complements `U` are `M`-conjugate (`typePData_normalizer_U_le_iff`).  This is the exclusivity that
refines `IsTypeP` (`= IsTypeP1 ∨ IsTypeP2`) into the precise type for the reverse bridges
`hIIP2`/`hIIIIVP1`. -/
theorem not_isTypeII_of_isTypeIII_or_IV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (h : OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M) :
    ¬ OddOrder.GroupTheory.IsTypeII M := by
  rintro ⟨dII⟩
  rcases h with hd | hd
  · exact dII.normalizer_not_le
      ((typePData_normalizer_U_le_iff hG hM dII.typeP hd.some.typeP).mpr hd.some.normalizer_le)
  · exact dII.normalizer_not_le
      ((typePData_normalizer_U_le_iff hG hM dII.typeP hd.some.typeP).mpr hd.some.normalizer_le)

/-- **Prop 16.1 reverse, centralizer half of `π(W₁) ⊆ κ(M)`** (mmd L4478, `1 ⊂ C_H(W₁) ⊆
C_{M_σ}(W₁)`): for a type-`P` datum and a nonidentity `x ∈ W₁`, the `M_σ`-centralizer of `x` is
nontrivial.  Witness: `W₂ = M' ⊓ C(x)` (`centralizer_W1`) lies in both `M_σ` (`W₂ ≤ H = M_F ≤ M_σ`)
and `C(x)`, and `W₂ ≠ ⊥` (`W2_nontrivial`); so `W₂ ≤ M_σ ⊓ C(x)` is a nontrivial subgroup.

This is the `κ(M)`-membership ingredient that is **derivable from the bare `TypePData`** (it needs
no `W₁ = κ`-Hall identification).  The remaining `κ`-membership ingredients — `p ∉ σ(M)` and the
rank-one condition `r_p(M) = 1` putting `p ∈ τ₁(M) ∪ τ₃(M)` — are the carrier-gated half (the latter
genuinely needs `W₁` to be the Hall `κ(M)`-subgroup; cf. issue 8015 and
`typep-w1-kappa-carrier-not-derivable`). -/
theorem typePData_msigma_inf_centralizer_W1_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {x : G} (hx : x ∈ data.W1) (hxne : x ≠ 1) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
  -- `W₂ ≤ M_σ ⊓ C(x)`.
  have hW2le : data.W2 ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) := by
    refine le_inf ?_ ?_
    · -- `W₂ ≤ H = M_F ≤ M_σ`.
      calc data.W2 ≤ data.H := data.W2_le.trans inf_le_left
        _ = maxNilpotentNormalHall M := data.H_eq
        _ ≤ _ := S15.maxNilpotentNormalHall_le_Msigma hG hM
    · -- `W₂ = M' ⊓ C(x) ≤ C(x)`.
      rw [← data.centralizer_W1 x hx hxne]; exact inf_le_right
  -- A subgroup containing the nontrivial `W₂` is nontrivial.
  exact fun hbot => data.W2_nontrivial (le_bot_iff.mp (hW2le.trans hbot.le))

/-- **Prop 16.1 reverse, `σ`-complement half of `π(W₁) ⊆ κ(M)`** (mmd L4478, `W₁ ∩ M_σ = 1`): for a
type-`P` datum, every prime dividing `|W₁|` lies outside `σ(M)`.  If `p ∈ σ(M)`, an order-`p`
subgroup `L ≤ W₁` is a `σ(M)`-group, so it lands in the `σ`-Hall subgroup `M_σ`
(`sigma_subgroup_le_Msigma_of_isHall`, `Msigma_isHall`); but `W₁ ∩ M_σ ≤ W₁ ∩ M' = 1`
(`M_complement`), forcing `L = ⊥` and `|L| = p = 1`, a contradiction.

This is the second `κ`-membership ingredient **derivable from the bare `TypePData`** (with
`typePData_msigma_inf_centralizer_W1_ne_bot`).  Together they give `p ∉ σ(M)` and `M_σ ⊓ C(P) ≠ ⊥`;
the only carrier-gated ingredient left for `π(W₁) ⊆ κ(M)` is the rank-one condition `r_p(M) = 1`. -/
theorem typePData_W1_prime_not_mem_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M) {p : ℕ} (hp : p ∈ (Nat.card ↥data.W1).primeFactors) :
    p ∉ OddOrder.BG.Ch3.S10.sigma M := by
  intro hpσ
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
  -- An order-`p` element `g ∈ W₁` and the cyclic subgroup `L = ⟨g⟩` of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) p (Nat.dvd_of_mem_primeFactors
      hp)
  have hgord : orderOf ((g : G)) = p :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective g).trans hg
  set L : Subgroup G := Subgroup.zpowers (g : G) with hLdef
  have hLcard : Nat.card ↥L = p := by rw [hLdef, Nat.card_zpowers, hgord]
  have hLW1 : L ≤ data.W1 := Subgroup.zpowers_le.mpr g.2
  have hLM : L ≤ M := hLW1.trans data.W1_le
  -- `L` is a `σ(M)`-group (its only prime divisor is `p ∈ σ(M)`).
  have hLpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma M) L := by
    intro q hq
    rw [hLcard, (Fact.out : p.Prime).primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpσ
  -- So `L ≤ M_σ ≤ M'`, while `L ≤ W₁` and `W₁ ∩ M' = ⊥` (complement); hence `L = ⊥`.
  have hLMσ : L ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hM) hLM hLpi
  have hLsub_bot : L.subgroupOf M = ⊥ := by
    rw [eq_bot_iff, ← disjoint_iff.mp data.M_complement.disjoint]
    exact le_inf
      (Subgroup.comap_mono (hLMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)))
      (Subgroup.comap_mono hLW1)
  have hLbot : L = ⊥ :=
    (inf_eq_left.mpr hLM).symm.trans (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hLsub_bot))
  rw [hLbot, Subgroup.card_bot] at hLcard
  exact (Fact.out : p.Prime).ne_one hLcard.symm

/-- **Prop 16.1 reverse, `M_P` from `TypePData` modulo the rank-one input** (mmd L4478,
`π(W₁) ⊆ κ(M) ⟹ κ(M) ≠ ∅`): a type-`P` datum whose `W₁`-primes all have `M`-rank one has
`κ(M) ≠ ∅`, hence `M` is `S14.IsTypeP`.  This is the gated-endpoint assembly of the three `κ`-bridge
ingredients for a prime `p ∣ |W₁|`: `p ∉ σ(M)` (`typePData_W1_prime_not_mem_sigma`) and `r_p(M) = 1`
(the hypothesis `hrank`) put `p ∈ τ₁(M) ∪ τ₃(M)`, while `⟨g⟩` (`g ∈ W₁` of order `p`) is a rank-one
elementary abelian subgroup with `M_σ ⊓ C(⟨g⟩) ⊇ M_σ ⊓ C(g) ≠ ⊥`
(`typePData_msigma_inf_centralizer_W1_ne_bot`).  So `p ∈ κ(M)`.

The only residual hypothesis `hrank` is the carrier-gated half (the `W₁ = κ`-Hall fact forces
`r_p(M) = 1`; cf. issue 8015).  Supplies the `→ M_P` direction of the reverse classifications
`hIIP2`/`hIIIIVP1`/`hVP1` of `proposition_type_classification_of_inputs`. -/
theorem typePData_kappa_nonempty_of_rank1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (data : TypePData M)
    (hrank : ∀ p ∈ (Nat.card ↥data.W1).primeFactors, pRank ↥M p = 1) :
    (S14.kappa M).Nonempty := by
  classical
  -- A prime `p ∣ |W₁|` (`W₁ ≠ ⊥`).
  have hW1card : Nat.card ↥data.W1 ≠ 1 := fun h => data.W1_nontrivial (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hW1card
  have hp : p ∈ (Nat.card ↥data.W1).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  have : Fact p.Prime := ⟨hpp⟩
  -- An order-`p` element `g ∈ W₁` and the rank-one subgroup `P = ⟨g⟩`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) p hpdvd
  have hgord : orderOf ((g : G)) = p :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := fun hc => by
    rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by rw [Nat.card_zpowers, hgord]
  refine ⟨p, hpp, ?_, Subgroup.zpowers (g : G),
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩,
    (Subgroup.zpowers_le.mpr g.2).trans data.W1_le, ?_⟩
  · -- `p ∈ τ₁(M) ∪ τ₃(M)` from `p ∉ σ(M)` and `r_p(M) = 1`.
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := typePData_W1_prime_not_mem_sigma hG hM data hp
    have hr : pRank ↥M p = 1 := hrank p hp
    by_cases hM' : p ∈ (Nat.card ↥(derivedInG M)).primeFactors
    · exact Or.inr ((mem_tau3_iff M p).mpr ⟨hpσ, hM', hr⟩)
    · exact Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, hM', hr⟩)
  · -- `M_σ ⊓ C(⟨g⟩) ⊇ M_σ ⊓ C(g) ≠ ⊥`.
    have hCne : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ :=
      typePData_msigma_inf_centralizer_W1_ne_bot hG hM data g.2 hgne
    have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
        Subgroup.centralizer ((Subgroup.zpowers (g : G) : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
    exact fun hbot => hCne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))

/-- **Prop 16.1 reverse, cyclicity ingredient for `r_q(M) = 1`** (mmd L4478): for a type-`P`
datum and a prime `q ∤ |M'|`, every elementary abelian `q`-subgroup `A` of `↥M` is cyclic.

The abelianization `↥M ⧸ M'` is cyclic — the `M_complement` field makes the cyclic factor `W₁`
(`W1_cyclic`) a complement of `M' = [M,M]` in `M`, so `↥M ⧸ M' ≃* ↥W₁`
(`IsComplement'.QuotientMulEquiv`).  Since `q ∤ |M'|` and `A` is a `q`-group, `A ⊓ M' = ⊥`
(coprime orders), so the quotient map embeds `A` into the cyclic `↥M ⧸ M'`, forcing `A` cyclic.
This is the `q`-rank-one half of `π(W₁) ⊆ κ(M)` once `q ∤ |M'|` is in hand (Hall for type V, the
`centralizer_W1` fixed-point argument for types II–IV). -/
theorem typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived [Finite G]
    {M : Subgroup G} (data : TypePData M) {q : ℕ} (hq : q.Prime)
    (hndvd : ¬ q ∣ Nat.card ↥(derivedInG M))
    {A : Subgroup ↥M} (hA : A.IsElementaryAbelian q) : IsCyclic ↥A := by
  have : Fact q.Prime := ⟨hq⟩
  have : IsCyclic ↥data.W1 := data.W1_cyclic
  set N : Subgroup ↥M := (derivedInG M).subgroupOf M with hNdef
  -- `N = commutator ↥M`, hence normal.
  have hN_eq : N = commutator ↥M := by
    rw [hNdef, derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hNnorm : N.Normal := by rw [hN_eq]; infer_instance
  -- `↥M ⧸ N ≃* ↥(W₁.subgroupOf M)` is cyclic.
  have : IsCyclic ↥(data.W1.subgroupOf M) := by
    have e : ↥(data.W1.subgroupOf M) ≃* ↥data.W1 := Subgroup.subgroupOfEquivOfLe data.W1_le
    exact isCyclic_of_surjective e.symm e.symm.surjective
  have ecyc : (↥M ⧸ N) ≃* ↥(data.W1.subgroupOf M) := (data.M_complement.symm).QuotientMulEquiv
  have : IsCyclic (↥M ⧸ N) := isCyclic_of_surjective ecyc.symm ecyc.symm.surjective
  -- `A ⊓ N = ⊥`: `|A|` is a `q`-power and `q ∤ |N| = |M'|`.
  have hNcard : Nat.card ↥N = Nat.card ↥(derivedInG M) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA.isPGroup
  have hcop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥N) := by
    rw [hk, hNcard]
    exact Nat.Coprime.pow_left k ((hq.coprime_iff_not_dvd).mpr hndvd)
  have hAN : A ⊓ N = ⊥ := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  -- `A` injects into the cyclic `↥M ⧸ N`.
  set φ : ↥A →* (↥M ⧸ N) := (QuotientGroup.mk' N).comp A.subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at ha
    have hmem : (a : ↥M) ∈ A ⊓ N := ⟨a.2, ha⟩
    rw [hAN, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (Subtype.ext hmem)
  have : IsCyclic ↥φ.range := inferInstance
  exact isCyclic_of_surjective (MonoidHom.ofInjective hφinj).symm
    (MonoidHom.ofInjective hφinj).symm.surjective

/-- **Prop 16.1 reverse, `r_q(M) = 1` from `q ∤ |M'|`** (mmd L4478): for a type-`P` datum and a
prime `q ∣ |W₁|` with `q ∤ |M'|`, the `q`-rank of `M` is one.  Upper bound: every elementary
abelian `q`-subgroup is cyclic (`typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived`),
so `pRank ↥M q ≤ 1`.  Lower bound: `q ∣ |W₁| ∣ |M|` gives an order-`q` element, an elementary
abelian `q`-subgroup of order `q`, so `1 ≤ pRank ↥M q`.  This is the rank-one input that
`typePData_kappa_nonempty_of_rank1` needs to place the `W₁`-primes in `κ(M)`. -/
theorem typePData_pRank_eq_one_of_not_dvd_card_derived [Finite G]
    {M : Subgroup G} (data : TypePData M) {q : ℕ} (hq : q.Prime)
    (hqW1 : q ∣ Nat.card ↥data.W1)
    (hndvd : ¬ q ∣ Nat.card ↥(derivedInG M)) :
    pRank ↥M q = 1 := by
  have : Fact q.Prime := ⟨hq⟩
  refine le_antisymm ?_ ?_
  · exact pRank_le_one_of_forall_isElementaryAbelian_isCyclic (fun A hA =>
      typePData_isCyclic_isElementaryAbelian_of_not_dvd_card_derived data hq hndvd hA)
  · have hqM : q ∣ Nat.card ↥M := hqW1.trans (Subgroup.card_dvd_of_le data.W1_le)
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥M) q hqM
    have hcard : Nat.card ↥(Subgroup.zpowers g) = q := by rw [Nat.card_zpowers, hg]
    exact pow_le_card_of_le_pRank (Subgroup.zpowers g)
      (Subgroup.IsElementaryAbelian.of_card_prime hcard) (by rw [hcard, pow_one])

/-- **Prop 16.1 reverse, type V ⟹ type `P`** (mmd L4478, clause (d) `.mp`): a structurally
type-`V` maximal subgroup is type `P` (`κ(M) ≠ ∅`).  Type `V` has `U = ⊥`, so `M' = M_F` is the
nilpotent normal Hall subgroup `maxNilpotentNormalHall M`; Hall coprimality gives `q ∤ |M'|` for
every `q ∣ |W₁| = [M : M']`, whence `r_q(M) = 1`
(`typePData_pRank_eq_one_of_not_dvd_card_derived`).  Feeding this rank-one fact to
`typePData_kappa_nonempty_of_rank1` places `π(W₁) ⊆ κ(M)`, so `κ(M) ≠ ∅`.  This is the type-V
branch of the `hVP1` reverse bridge (the `IsTypeP` half) of Proposition 16.1. -/
theorem isTypeP_of_isTypeV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hV : OddOrder.GroupTheory.IsTypeV M) : S14.IsTypeP M := by
  obtain ⟨v⟩ := hV
  -- `M' = M_F` (`U = ⊥`).
  have hM'eq : derivedInG M = maxNilpotentNormalHall M := by
    rw [v.typeP.derivedInG_eq_fitting_sup_U, v.U_eq_bot, sup_bot_eq]
  have hHall := maxNilpotentNormalHall_isHall M
  refine typePData_kappa_nonempty_of_rank1 hG hM v.typeP (fun q hq => ?_)
  have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqW1 : q ∣ Nat.card ↥v.typeP.W1 := Nat.dvd_of_mem_primeFactors hq
  have hndvd : ¬ q ∣ Nat.card ↥(derivedInG M) := by
    rw [hM'eq]
    intro hdvd
    have hqMF : q ∈ (Nat.card ↥(maxNilpotentNormalHall M)).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hqp, hdvd, Nat.card_pos.ne'⟩
    have hidx : ((maxNilpotentNormalHall M).subgroupOf M).index = Nat.card ↥v.typeP.W1 := by
      rw [← hM'eq]; exact (v.typeP.card_W1_eq_derived_index).symm
    have hqIdx : q ∈ ((maxNilpotentNormalHall M).subgroupOf M).index.primeFactors := by
      rw [hidx]; exact Nat.mem_primeFactors.mpr ⟨hqp, hqW1, Nat.card_pos.ne'⟩
    exact (hHall.2 q hqIdx) hqMF
  exact typePData_pRank_eq_one_of_not_dvd_card_derived v.typeP hqp hqW1 hndvd

/-- Conjugation action of the cyclic group `⟨x⟩` on a subgroup `N` it normalizes. -/
def conjActionOfMemNormalizer {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) :
    ↥(Subgroup.zpowers x) →* MulAut ↥N :=
  N.normalizerMonoidHom.comp (Subgroup.inclusion (Subgroup.zpowers_le.mpr hx))

theorem conjActionOfMemNormalizer_apply {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (a : ↥(Subgroup.zpowers x)) (n : ↥N) :
    ((conjActionOfMemNormalizer hx a) n : G) = (a : G) * (n : G) * (a : G)⁻¹ := rfl

/-- Fixed points of the cyclic conjugation action on `N` are the elements of `N` centralizing `x`.
-/
theorem fixedPoints_conjActionOfMemNormalizer_eq {N : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (N : Set G)) :
    Subgroup.fixedPointsOfMulAut (conjActionOfMemNormalizer hx) =
      (N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf N := by
  ext n
  constructor
  · intro hn
    rw [Subgroup.mem_subgroupOf]
    refine ⟨n.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
    intro y hy
    rw [Set.mem_singleton_iff] at hy; subst hy
    have hfixG := congrArg Subtype.val
      (Subgroup.mem_fixedPointsOfMulAut.mp hn ⟨y, Subgroup.mem_zpowers y⟩)
    rw [conjActionOfMemNormalizer_apply] at hfixG
    calc y * (n : G) = (y * (n : G) * y⁻¹) * y := by group
      _ = (n : G) * y := by rw [hfixG]
  · intro hn
    rw [Subgroup.mem_fixedPointsOfMulAut]
    intro a
    apply Subtype.ext
    rw [conjActionOfMemNormalizer_apply]
    have hncent : (n : G) ∈ Subgroup.centralizer ({x} : Set G) :=
      (Subgroup.mem_subgroupOf.mp hn).2
    have hcomm : Commute (x : G) (n : G) :=
      Subgroup.mem_centralizer_iff.mp hncent x (Set.mem_singleton x)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    have hacomm : (a : G) * (n : G) = (n : G) * (a : G) := by
      rw [← hk]; exact (hcomm.zpow_left k)
    calc (a : G) * (n : G) * (a : G)⁻¹ = (n : G) * (a : G) * (a : G)⁻¹ := by rw [hacomm]
      _ = (n : G) := by group

/-- **`p`-element fixed-point count** (`[Finite G]`): if a `q`-element `x` normalizes `N` and
`q ∣ |N|`, then `q ∣ |C_N(x)|`.  The `q`-group `⟨x⟩` acts on `N` by conjugation, so
`|N| ≡ |C_N(x)| (mod q)` (`IsPGroup.card_modEq_card_fixedPoints`, the fixed points being
`N ⊓ C(x)`); since `q ∣ |N|`, also `q ∣ |C_N(x)|`.  Used to show `q ∤ |M'|` for the type-II–IV
reverse bridges: `C_{M'}(x) = W₂` has order coprime to `q = |W₁|`. -/
theorem prime_dvd_card_inf_centralizer_of_mem_normalizer [Finite G]
    {N : Subgroup G} {x : G} {q : ℕ} [Fact q.Prime]
    (hx : x ∈ Subgroup.normalizer (N : Set G))
    (hxq : IsPGroup q ↥(Subgroup.zpowers x))
    (hdvd : q ∣ Nat.card ↥N) :
    q ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  let : MulAction ↥(Subgroup.zpowers x) ↥N :=
    MulAction.compHom ↥N (conjActionOfMemNormalizer hx)
  have hmod := hxq.card_modEq_card_fixedPoints (α := ↥N)
  -- The fixed points of the conjugation action are `N ⊓ C(x)`.
  have hcard : Nat.card (MulAction.fixedPoints ↥(Subgroup.zpowers x) ↥N)
      = Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr (Equiv.trans (Equiv.subtypeEquivRight (fun n => ?_))
      (Subgroup.subgroupOfEquivOfLe (inf_le_left :
        N ⊓ Subgroup.centralizer ({x} : Set G) ≤ N)).toEquiv)
    rw [← fixedPoints_conjActionOfMemNormalizer_eq hx, Subgroup.mem_fixedPointsOfMulAut]
    exact Iff.rfl
  rw [hcard] at hmod
  exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hdvd))

/-- **`q ∤ |W₂|` for prime `|W₁| = q`** (type II–IV): `W₁` and `W₂` are subgroups of the cyclic
`W = W₁W₂` with `W₁ ⊓ W₂ = ⊥` (`W₂ ≤ M_F ≤ M'` and `W₁ ⊓ M' = ⊥` by `M_complement`).  If `q ∣ |W₂|`,
order-`q` elements `x ∈ W₁`, `y ∈ W₂` generate the *same* order-`q` subgroup of the cyclic `W`
(`cyclic_subgroup_eq_of_card_eq`), so `x ∈ ⟨y⟩ ≤ W₂`, forcing `x ∈ W₁ ⊓ W₂ = ⊥`, contra. -/
theorem typePData_not_dvd_card_W2_of_card_W1_prime [Finite G] {M : Subgroup G}
    (data : TypePData M) (hq : (Nat.card ↥data.W1).Prime) :
    ¬ (Nat.card ↥data.W1) ∣ Nat.card ↥data.W2 := by
  intro hdvd
  have : Fact (Nat.card ↥data.W1).Prime := ⟨hq⟩
  have : IsCyclic ↥data.W := data.W_cyclic
  have hW2leM' : data.W2 ≤ derivedInG M := le_trans data.W2_le (le_trans inf_le_left data.H_le)
  have hW1W2 : data.W1 ⊓ data.W2 = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have hmem : (⟨g, data.W1_le (Subgroup.mem_inf.mp hg).1⟩ : ↥M) ∈
        ((derivedInG M).subgroupOf M) ⊓ (data.W1.subgroupOf M) :=
      ⟨Subgroup.mem_subgroupOf.mpr (hW2leM' (Subgroup.mem_inf.mp hg).2),
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mp hg).1⟩
    rw [disjoint_iff.mp data.M_complement.disjoint, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hmem)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) (Nat.card ↥data.W1) dvd_rfl
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W2) (Nat.card ↥data.W1) hdvd
  have hxord : orderOf ((x : G)) = Nat.card ↥data.W1 :=
    (orderOf_injective data.W1.subtype data.W1.subtype_injective x).trans hx
  have hyord : orderOf ((y : G)) = Nat.card ↥data.W1 :=
    (orderOf_injective data.W2.subtype data.W2.subtype_injective y).trans hy
  have hxne : (x : G) ≠ 1 := fun hc => hq.ne_one (by rw [← hxord, hc, orderOf_one])
  have hW1leW : data.W1 ≤ data.W := le_sup_left.trans data.W_eq.ge
  have hW2leW : data.W2 ≤ data.W := le_sup_right.trans data.W_eq.ge
  have hxW : (x : G) ∈ data.W := hW1leW x.2
  have hyW : (y : G) ∈ data.W := hW2leW y.2
  have h1 : (Subgroup.zpowers (x : G)).subgroupOf data.W
      = (Subgroup.zpowers (y : G)).subgroupOf data.W := by
    refine OddOrder.GroupTheory.cyclic_subgroup_eq_of_card_eq ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hxW)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyW)).toEquiv,
      Nat.card_zpowers, Nat.card_zpowers, hxord, hyord]
  have hxin : (x : G) ∈ Subgroup.zpowers (y : G) := by
    have hm : (⟨(x : G), hxW⟩ : ↥data.W) ∈ (Subgroup.zpowers (x : G)).subgroupOf data.W :=
      Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers (x : G))
    rw [h1] at hm
    exact Subgroup.mem_subgroupOf.mp hm
  have hmem : (x : G) ∈ data.W1 ⊓ data.W2 := ⟨x.2, (Subgroup.zpowers_le.mpr y.2) hxin⟩
  rw [hW1W2, Subgroup.mem_bot] at hmem
  exact hxne hmem

/-- **Prop 16.1 reverse, type II–IV ⟹ type `P`** (mmd L4478): a type-`P` datum whose cyclic
factor `W₁` has *prime* order `q = |W₁|` (the `TypePNontrivialCore` of types II/III/IV) is BG type
`P`.  `q ∤ |M'|`: else the `q`-element `x ∈ W₁#` normalizing `M'` would give
`q ∣ |C_{M'}(x)| = |W₂|`
(`prime_dvd_card_inf_centralizer_of_mem_normalizer`, `centralizer_W1`), contradicting `q ∤ |W₂|`
(`typePData_not_dvd_card_W2_of_card_W1_prime`).  Then `r_q(M) = 1`
(`typePData_pRank_eq_one_of_not_dvd_card_derived`) and `κ(M) ≠ ∅`
(`typePData_kappa_nonempty_of_rank1`). -/
theorem isTypeP_of_typePData_of_card_W1_prime [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypePData M)
    (hqprime : (Nat.card ↥data.W1).Prime) : S14.IsTypeP M := by
  have : Fact (Nat.card ↥data.W1).Prime := ⟨hqprime⟩
  refine typePData_kappa_nonempty_of_rank1 hG hM data (fun p hp => ?_)
  have hpq : p = Nat.card ↥data.W1 := by
    rcases hqprime.eq_one_or_self_of_dvd p (Nat.dvd_of_mem_primeFactors hp) with h | h
    · exact absurd h (Nat.prime_of_mem_primeFactors hp).ne_one
    · exact h
  subst hpq
  have hndvd : ¬ Nat.card ↥data.W1 ∣ Nat.card ↥(derivedInG M) := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥data.W1) (Nat.card ↥data.W1) dvd_rfl
    have hxord : orderOf ((x : G)) = Nat.card ↥data.W1 :=
      (orderOf_injective data.W1.subtype data.W1.subtype_injective x).trans hx
    have hxne : (x : G) ≠ 1 := fun hc => hqprime.ne_one (by rw [← hxord, hc, orderOf_one])
    have hsubeq : (derivedInG M).subgroupOf M = commutator ↥M := by
      rw [derivedInG, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    have hle : derivedInG M ≤ M := Subgroup.map_subtype_le _
    have hnorm : ((derivedInG M).subgroupOf M).Normal := by rw [hsubeq]; infer_instance
    have hxnorm : (x : G) ∈ Subgroup.normalizer (derivedInG M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hnorm (data.W1_le x.2)
    have hxpg : IsPGroup (Nat.card ↥data.W1) ↥(Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxord, pow_one])
    have hdvdW2 : Nat.card ↥data.W1 ∣ Nat.card ↥data.W2 := by
      have hd := prime_dvd_card_inf_centralizer_of_mem_normalizer hxnorm hxpg hdvd
      rwa [data.centralizer_W1 (x : G) x.2 hxne] at hd
    exact typePData_not_dvd_card_W2_of_card_W1_prime data hqprime hdvdW2
  exact typePData_pRank_eq_one_of_not_dvd_card_derived data hqprime dvd_rfl hndvd

/-- **Prop 16.1 reverse, type II ⟹ type `P`** (clause (b) `.mp`, `IsTypeP` half): immediate from
`isTypeP_of_typePData_of_card_W1_prime` and the `TypePNontrivialCore` primality of `|W₁|`. -/
theorem isTypeP_of_isTypeII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hII : OddOrder.GroupTheory.IsTypeII M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hII
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, type III ⟹ type `P`** (clause (c) `.mp`, `IsTypeP` half). -/
theorem isTypeP_of_isTypeIII [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hIII : OddOrder.GroupTheory.IsTypeIII M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hIII
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, type IV ⟹ type `P`** (clause (c) `.mp`, `IsTypeP` half). -/
theorem isTypeP_of_isTypeIV [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hIV : OddOrder.GroupTheory.IsTypeIV M) : S14.IsTypeP M := by
  obtain ⟨d⟩ := hIV
  exact isTypeP_of_typePData_of_card_W1_prime hG hM d.typeP d.common.2.1

/-- **Prop 16.1 reverse, every non-type-I maximal subgroup is type `P`** (mmd L4478): the common
`IsTypeP` half of clauses (b)–(d) `.mp`.  Types II/III/IV reduce to the prime-`|W₁|` argument
(`isTypeP_of_typePData_of_card_W1_prime`); type V to the Hall argument (`isTypeP_of_isTypeV`).
This is exactly what `not_isTypeI_of_isTypeNonI` consumes (it discards the `P₁`/`P₂` refinement),
so it closes the FT-critical content of the reverse type bridges modulo `hIF` (type I ⟹ type F). -/
theorem isTypeP_of_isTypeNonI [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (h : OddOrder.GroupTheory.IsTypeNonI M) : S14.IsTypeP M := by
  rcases h with hII | hIII | hIV | hV
  · exact isTypeP_of_isTypeII hG hM hII
  · exact isTypeP_of_isTypeIII hG hM hIII
  · exact isTypeP_of_isTypeIV hG hM hIV
  · exact isTypeP_of_isTypeV hG hM hV

/-- **Theorem A(8), the `FittingIsTI`-free part** (mmd L4274): for `M_F ≠ M_σ`, the Hall
`(κ ∪ σ)ᶜ`-complement `U` is trivial and `|K| = p` is prime.  Both follow from
`mf_ne_msigma_typeP1_structure` (Theorem 15.2): `M_F ≠ M_σ ⟹ IsTypeP1 M`
(`isTypeP1_of_mf_ne_msigma`), whence `U.subgroupOf M = ⊥`
(`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`), while `|K| = p` prime is read off Theorem
15.2's structure conjunction directly.

This discharges two of the three conjuncts of Theorem A(8) in
`theoremA_maximal_structure_faithful`; the
remaining `FittingIsTI M` (`F(M)` a TI-subgroup of `G`) is the genuinely deep §15 content (Theorem A
proper, via the §9–§10 uniqueness/fusion machinery) and is *not* supplied here. -/
theorem theoremA8_complement_eq_bot_and_kappa_prime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    U.subgroupOf M = ⊥ ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  refine ⟨isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot
    (isTypeP1_of_mf_ne_msigma hG hM hne) hU, ?_⟩
  obtain ⟨_, _, _, p, _, hpp, _, hKp, -⟩ :=
    (mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar).2
  exact ⟨p, hpp, hKp⟩

/-- **BG Theorem A(8), in full** (mmd L4274): for `M_F ≠ M_σ`, the Hall `(κ ∪ σ)ᶜ`-complement `U`
is trivial, `F(M)` is a TI-subgroup of `G`, and `|K| = p` is prime.  Combines the
`FittingIsTI`-free part (`theoremA8_complement_eq_bot_and_kappa_prime`, via Theorem 15.2) with the
`FittingIsTI` clause (`S15.fitting_isTI_of_mf_ne_msigma`, the contrapositive of the `M_F = M_σ`
conclusion of Theorem 15.7(a)).  This is the full conjunction
`theoremA_maximal_structure_faithful` carries
for the `M_F ≠ M_σ` case.  Its one deep upstream citation is the §15 rank-theoretic core
`S15.piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` (Theorem 15.7(a)). -/
theorem theoremA8_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    U.subgroupOf M = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p := by
  obtain ⟨hUbot, hKp⟩ :=
    theoremA8_complement_eq_bot_and_kappa_prime hG hM hKM hK hKstar hU hne
  exact ⟨hUbot, S15.fitting_isTI_of_mf_ne_msigma hG hM hne, hKp⟩

/-- **Type-`P₁` (`M_F ≠ M_σ`) `TypePNontrivialCore`**
(the common type II--IV hypotheses of Peterfalvi
(8.6), for the type III/IV case): a `TypePData` of a type-`P₁` maximal subgroup with `M_F ≠ M_σ` and
nontrivial complement `U` satisfies `U ≠ ⊥`, `|W₁|` prime, and `M_F#` is a `TI`-subset.

The `|W₁|` primality is Theorem A(8) (`theoremA8_structure`: `M_F ≠ M_σ ⟹ |K| = p` prime, with
`|W₁| = |K| = [M:M']`); the `M_F#`-`TI` is the `FittingIsTI M` clause of A(8)
(`fitting_isTI_of_mf_ne_msigma`) read through
`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`.
Discharges the `hcommon` input of the type III/IV last mile `isTypeIII_or_IV_of_typePData`, so once
the type-`P₁` `TypePData` is constructed (`exists_typeP1_mf_complement` plus the deep
nilpotency/Fitting fields) and `N_G(U) ⊆ M` is supplied, the `hP1neIIIIV` bridge closes. -/
theorem typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (data : TypePData M) (hUne : data.U ≠ ⊥) :
    TypePNontrivialCore M data := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  refine ⟨hUne, ?_, ?_⟩
  · -- `|W₁| = [M:M'] = |K| = p` prime (Theorem A(8)).
    obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
    set K : Subgroup G := K'.map M.subtype with hKdef
    have hKM : K ≤ M := Subgroup.map_subtype_le K'
    have hKeq : K.subgroupOf M = K' :=
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
    have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
    -- The trivial `(κ ∪ σ)'`-Hall `U = ⊥` (type `P₁`: `π(M) ⊆ κ ∪ σ`).
    have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
        ((⊥ : Subgroup G).subgroupOf M) := by
      rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
      intro p hp
      simp only [Set.mem_compl_iff, not_not]
      by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
      · exact Set.mem_union_right _ hpσ
      · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hp, hpσ⟩)
    have : IsCyclic ↥K := (typeP_auxiliary_structure hG hM hKM bot_le hK rfl hU).2.1
    obtain ⟨_, _, p, hp, hKp⟩ := theoremA8_structure hG hM hKM hK rfl hU hne
    rw [data.card_W1_eq_derived_index, ← card_kappaHall_eq_derived_index hG hM hP1.1 hKM hK, hKp]
    exact hp
  · -- `M_F#` is `TI` (`FittingIsTI M` from `M_F ≠ M_σ`).
    exact maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM
      (S15.fitting_isTI_of_mf_ne_msigma hG hM hne)

/-- **Normalizer of a finite nilpotent subgroup is contained in the normalizer of each of its Sylow
subgroups** (the `char_norms (pcore_char p U)` step of Coq `BGsection16` `typePfacts`): for a finite
nilpotent `U ≤ G` and a Sylow `p`-subgroup `P` of `↥U`, the `G`-normalizer of `U` lies in the
`G`-normalizer of `P̄ = P.map U.subtype`.
Since `U` is nilpotent, `P` is normal — hence the *unique*
Sylow `p`-subgroup of `↥U` (`Sylow.unique_of_normal`) — so conjugation by any `g ∈ N_G(U)` (which
permutes `U`'s Sylow `p`-subgroups) fixes `P̄`.  Reusable. -/
theorem normalizer_le_normalizer_map_sylow_of_isNilpotent [Finite G] {U : Subgroup G}
    (hUnil : Group.IsNilpotent ↥U) {p : ℕ} [Fact p.Prime] (P : Sylow p ↥U) :
    Subgroup.normalizer (U : Set G) ≤
      Subgroup.normalizer (((P : Subgroup ↥U).map U.subtype : Subgroup G) : Set G) := by
  classical
  have := hUnil
  have hPnormal : (P : Subgroup ↥U).Normal := Ch01.Sylow.normal_of_isNilpotent P
  let : Unique (Sylow p ↥U) := P.unique_of_normal hPnormal
  set Pbar : Subgroup G := (P : Subgroup ↥U).map U.subtype with hPbardef
  have hPbar_le_U : Pbar ≤ U := Subgroup.map_subtype_le _
  -- `|P̄|` is the full `p`-part of `|U|`.
  have hcardPbar : Nat.card ↥Pbar = p ^ (Nat.card ↥U).factorization p := by
    rw [hPbardef, Subgroup.card_map_of_injective U.subtype_injective]
    exact P.card_eq_multiplicity
  intro g hg
  have hgU : MulAut.conj g • U = U := conj_smul_eq_self_of_mem_normalizer hg
  -- `conj g • P̄ ≤ U` (since `g` normalizes `U`).
  have hconj_le_U : MulAut.conj g • Pbar ≤ U := by
    rw [pointwise_mulAut_smul_eq_map]
    calc (Pbar.map (MulAut.conj g : G →* G))
        ≤ U.map (MulAut.conj g : G →* G) := Subgroup.map_mono hPbar_le_U
      _ = MulAut.conj g • U := (pointwise_mulAut_smul_eq_map _ _).symm
      _ = U := hgU
  -- `(conj g • P̄).subgroupOf U` is a Sylow `p` of `↥U`, hence `= P` by uniqueness.
  have hcardConj : Nat.card ↥((MulAut.conj g • Pbar).subgroupOf U)
      = p ^ (Nat.card ↥U).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hconj_le_U).toEquiv,
      pointwise_mulAut_smul_eq_map, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      hcardPbar]
  set Q : Sylow p ↥U := Sylow.ofCard ((MulAut.conj g • Pbar).subgroupOf U) hcardConj with hQdef
  have hQP : (Q : Subgroup ↥U) = (P : Subgroup ↥U) := by rw [Subsingleton.elim Q P]
  have h2 : (Q : Subgroup ↥U) = (MulAut.conj g • Pbar).subgroupOf U := Sylow.coe_ofCard _ _
  -- Transport back to `G`: `conj g • P̄ = P̄`, so `g ∈ N_G(P̄)`.
  have hfix : MulAut.conj g • Pbar = Pbar := by
    have h1 : ((MulAut.conj g • Pbar).subgroupOf U).map U.subtype = MulAut.conj g • Pbar :=
      Subgroup.map_subgroupOf_eq_of_le hconj_le_U
    rw [← h1, ← h2, hQP]
  exact mem_normalizer_of_conj_smul_eq_self hfix

/-- **A prime dividing the type-`P₁` `M_F`-complement is a `σ`-prime that `U` carries fully**
(the `sMp`/`sylP` steps of Coq `BGsection16` `typePfacts`): for a type-`P₁` maximal `M` and an
`M_F`-complement `U` in `M' = M_σ` (`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`), every prime `p ∣ |U|` lies in
`σ(M)` and the `p`-part of `|U|` equals the `p`-part of `|M|`.

`p ∈ σ(M)`: `p ∣ |U| ∣ |M_σ|` and `M_σ` is the `σ`-Hall (`Msigma_subgroupOf_isHall`).
`p`-parts agree: `|M| = |U| · [M:U]` and `p ∤ [M:U] = [M':U]·[M:M']`.  Here `[M':U] = |M_F|`
(`IsComplement'.index_eq_card`) and `p ∤ |M_F|` because `M_F` is a Hall subgroup of `M`
(`maxNilpotentNormalHall_isHall`) with `|U| ∣ [M:M_F]`, while `[M:M'] = [M:M_σ]` is a `σ'`-number
(`p ∈ σ`).  Hence a Sylow `p`-subgroup of `U` is a Sylow `p`-subgroup of `M`. -/
theorem typeP1_complement_mem_sigma_and_factorization [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥U).primeFactors) :
    p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
      (Nat.card ↥U).factorization p = (Nat.card ↥M).factorization p := by
  classical
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpU : p ∣ Nat.card ↥U := Nat.dvd_of_mem_primeFactors hp
  set M' := derivedInG M with hM'def
  have hM'σ : M' = OddOrder.BG.Ch3.S10.Msigma M := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have hUle' : U ≤ M' := hsup ▸ le_sup_right
  have hMFle' : maxNilpotentNormalHall M ≤ M' := hsup ▸ le_sup_left
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hUM : U ≤ M := hUle'.trans hM'M
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  -- (1) `p ∈ σ(M)`: `p ∣ |U| ∣ |M'| = |M_σ|`, and `π(M_σ) ⊆ σ`.
  have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv]
    exact Nat.mem_primeFactors.mpr
      ⟨hpp, hpU.trans (hM'σ ▸ Subgroup.card_dvd_of_le hUle'), Nat.card_pos.ne'⟩
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M := (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG
      hM).1 p hpMσ
  refine ⟨hpσ, ?_⟩
  -- (2) `p`-parts agree.  `[M:U] = [M':U]·[M:M']`.
  have hidx_split : (U.subgroupOf M').index * (M'.subgroupOf M).index = (U.subgroupOf M).index :=
    Subgroup.relIndex_mul_relIndex U M' M hUle' hM'M
  -- `p ∤ [M':U] = |M_F|`.
  have hp_not_UM' : ¬ p ∣ (U.subgroupOf M').index := by
    rw [hDcompl.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMFle').toEquiv]
    intro hdvd
    -- `|U| ∣ [M:M_F]` (since `[M':M_F] = |U|` and `[M:M_F] = [M':M_F]·[M:M']`).
    have hMF'idx : ((maxNilpotentNormalHall M).subgroupOf M').index = Nat.card ↥U := by
      rw [hDcompl.symm.index_eq_card,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle').toEquiv]
    have hsplit2 : ((maxNilpotentNormalHall M).subgroupOf M').index * (M'.subgroupOf M).index
        = ((maxNilpotentNormalHall M).subgroupOf M).index :=
      Subgroup.relIndex_mul_relIndex _ M' M hMFle' hM'M
    have hUdvd : Nat.card ↥U ∣ ((maxNilpotentNormalHall M).subgroupOf M).index :=
      ⟨(M'.subgroupOf M).index, by rw [← hsplit2, hMF'idx]⟩
    have hp_idxMF : p ∈ (((maxNilpotentNormalHall M).subgroupOf M).index).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hpp, hpU.trans hUdvd, Subgroup.index_ne_zero_of_finite⟩
    exact (maxNilpotentNormalHall_isHall M).2 p hp_idxMF
      (Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Nat.card_pos.ne'⟩)
  -- `p ∤ [M:M'] = [M:M_σ]` (`σ`-Hall, `p ∈ σ`).
  have hp_not_M'M : ¬ p ∣ (M'.subgroupOf M).index := by
    intro hdvd
    refine (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).2 p ?_ hpσ
    rw [hM'σ] at hdvd
    exact Nat.mem_primeFactors.mpr ⟨hpp, hdvd, Subgroup.index_ne_zero_of_finite⟩
  -- `p ∤ [M:U]`.
  have hp_not_UM : ¬ p ∣ (U.subgroupOf M).index := by
    rw [← hidx_split]
    intro h
    rcases (Nat.Prime.dvd_mul hpp).mp h with h1 | h2
    · exact hp_not_UM' h1
    · exact hp_not_M'M h2
  -- conclude.  `|M| = |U| · [M:U]`, `factorization p [M:U] = 0`.
  have hlag : Nat.card ↥U * (U.subgroupOf M).index = Nat.card ↥M := by
    have h := Subgroup.card_mul_index (U.subgroupOf M)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at h
  rw [← hlag, Nat.factorization_mul Nat.card_pos.ne' Subgroup.index_ne_zero_of_finite,
    Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hp_not_UM, add_zero]

/-- **Prop 16.1 forward bridge `hP1neIIIIV`** — a type-`P₁` maximal subgroup with `M_F ≠ M_σ` is
of type III or IV.

The type-`P` datum is fully constructed (`typePData_of_isTypeP1_mf_ne_msigma`, the type III/IV
carrier-constructibility milestone, BG Corollary 15.5): the nilpotent `M_F`-complement `U ≠ ⊥` with
`F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.  The complement is built transparently here (rather than via the
opaque constructor) so that `U ≠ ⊥` (`hcommon`) and the normalizer condition are statable for the
*specific* `U`.  `isTypeIII_or_IV_of_typePData` then splits on `IsMulCommutative ↥U` (III vs IV).

The **type III/IV last mile `N_G(U) ⊆ M`** (Peterfalvi (8.7) / Coq `BGsection15` `Fcore_structure`)
— the property that distinguishes type III/IV (`normalizer_le`) from type II
(`normalizer_not_le`) — is discharged in the proof below, without the BG uniqueness analysis of
the complement: pick a prime `p ∣ |U|` and the Sylow `p`-subgroup `P̄` of the *nilpotent* `U`, so
`N_G(U) ≤ N_G(P̄)` (uniqueness of Sylows in a nilpotent group,
`normalizer_le_normalizer_map_sylow_of_isNilpotent`); `p ∈ σ(M)` and `P̄` is a full Sylow
`p`-subgroup of `M` (`typeP1_complement_mem_sigma_and_factorization`), so
`N_G(P̄) ≤ M` (`Ch3.S10.normalizer_sylow_map_le_of_mem_sigma`). -/
theorem isTypeIII_or_IV_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    OddOrder.GroupTheory.IsTypeIII M ∨ OddOrder.GroupTheory.IsTypeIV M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  obtain ⟨U, hUle, hsup, hKnorm, hinf⟩ := exists_typeP1_mf_complement hG hM hP1 hKM hK
  have hUnilp : Group.IsNilpotent ↥U :=
    isNilpotent_complement_of_isTypeP1_mf_ne_msigma hG hM hP1 hne hsup hinf
  have hDcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hFiteq := fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma hG hM hP1 hsup hinf
  have hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    obtain ⟨_, -, -, -, hM''F, -, -, -, -, -, -, -⟩ := S15.fitting_decomposition hG hM
    rw [← hFiteq]; exact hM''F
  -- `U ≠ ⊥`: else `M_F = M' = M_σ`, contradicting `hne`.
  have hUne : U ≠ ⊥ := by
    rintro rfl
    refine hne ?_
    have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
      isTypeP1_derivedInG_eq_Msigma hG hM hP1
    have hMF' : maxNilpotentNormalHall M = derivedInG M := by rw [← hsup, sup_bot_eq]
    rw [hM'σ] at hMF'; exact hMF'
  set data : TypePData M :=
    typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK hUle hKnorm hUnilp hDcompl hSDfit hFiteq
    with hdata
  have hdataU : data.U = U := rfl
  have hcommon : TypePNontrivialCore M data :=
    typePData_nontrivialCore_of_isTypeP1_mf_ne_msigma hG hM hP1 hne data (hdataU ▸ hUne)
  refine isTypeIII_or_IV_of_typePData data hcommon ?_
  rw [hdataU]
  -- `N_G(U) ⊆ M` (Peterfalvi (8.7), Coq `typePfacts`): pick a prime `p ∣ |U|` and `P = Sylow_p(U)`.
  -- `N_G(U) ≤ N_G(P̄)` (`P̄` unique in the nilpotent `U`) and `P̄` is a `σ`-Sylow of `M`, so
  -- `N_G(P̄) ≤ M` (`normalizer_sylow_map_le_of_mem_sigma`).
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd
    (show Nat.card ↥U ≠ 1 from fun h => hUne (Subgroup.card_eq_one.mp h))
  have hpπU : p ∈ (Nat.card ↥U).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hpσ, hfact⟩ :=
    typeP1_complement_mem_sigma_and_factorization hG hM hP1 hsup hinf hpπU
  have hUM : U ≤ M := hUle.trans (Subgroup.map_subtype_le _)
  have P : Sylow p ↥U := default
  have hPbarM : ((P : Subgroup ↥U).map U.subtype) ≤ M :=
    (Subgroup.map_subtype_le _).trans hUM
  have hcardPbar : Nat.card ↥(((P : Subgroup ↥U).map U.subtype).subgroupOf M)
      = p ^ (Nat.card ↥M).factorization p := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPbarM).toEquiv,
      Subgroup.card_map_of_injective U.subtype_injective, P.card_eq_multiplicity, hfact]
  set Q : Sylow p ↥M := Sylow.ofCard (((P : Subgroup ↥U).map U.subtype).subgroupOf M) hcardPbar
    with hQdef
  refine le_trans (normalizer_le_normalizer_map_sylow_of_isNilpotent hUnilp P) ?_
  have hQmap : (Q : Subgroup ↥M).map M.subtype = (P : Subgroup ↥U).map U.subtype := by
    rw [hQdef, Sylow.coe_ofCard, Subgroup.map_subgroupOf_eq_of_le hPbarM]
  have hnorm := OddOrder.BG.Ch3.S10.normalizer_sylow_map_le_of_mem_sigma hpσ Q
  rwa [hQmap] at hnorm

/-- **BG Theorem A(7), first clause — `M'' ⊆ F(M)`** (mmd L4354), as a standalone `sorry`-free
lemma for *any* maximal `M`.  No longer `M_F ≠ M_σ`-gated: Theorem 15.2's closing (issue 8012)
supplies the type-`P₁` half, so a case split on `M_F = M_σ` discharges both branches.

* `M_F = M_σ` (`M_σ` nilpotent, `maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`): then
  `M'' ≤ M_σ` (`derivedDerived_le_Msigma`, always true via §12 `E'` abelian) and
  `M_σ ≤ M_F ≤ F(M)` (`Msigma_le_maxNilpotentNormalHall_of_nilpotent`,
  `maxNilpotentNormalHall_le_fittingInG`);
* `M_F ≠ M_σ` (type `P₁`): the `M'' ⊆ F(M)` conjunct of Theorem 15.2
  (`mf_ne_msigma_typeP1_structure`), where `F(M) = Q C_M(Q) ⊊ M_σ` and the containment is the
  genuinely-harder chief-factor analysis (not reducible to `M'' ≤ M_σ`, since `M_σ ⊄ F(M)` here).

The second clause of A(7) (`F(M) = C_M(M_F) M_F`, and `K ≠ 1 → F(M) ⊆ M'`) is left to the gated
`fittingInAmbient_eq_*`/`theoremC_paired_structure`; only `M'' ⊆ F(M)` enters the faithful monolith
`theoremA_maximal_structure_faithful`. -/
theorem derivedDerived_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    derivedInG (derivedInG M) ≤ S15.fittingInAmbient M := by
  by_cases hne : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
  · -- `M_σ` nilpotent: `M'' ≤ M_σ ≤ M_F ≤ F(M)`.
    have hnil : Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      (S15.maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp hne
    calc derivedInG (derivedInG M)
        ≤ OddOrder.BG.Ch3.S10.Msigma M := S15.derivedDerived_le_Msigma hG hM
      _ ≤ maxNilpotentNormalHall M :=
          S15.Msigma_le_maxNilpotentNormalHall_of_nilpotent hG hM hnil
      _ ≤ S15.fittingInAmbient M := S15.maxNilpotentNormalHall_le_fittingInG M
  · -- type `P₁`: cite the `M'' ⊆ F(M)` conjunct (16th) of Theorem 15.2.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hA7, _, _, _⟩ :=
      S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar
    exact hA7

/-- **BG Theorem A(6), proper containment `M' ⊊ M`** (mmd L4363, the `M' ⊂ M` end of the chain
`1 ⊂ M_F ⊆ M_σ ⊆ M' ⊂ M`): the derived subgroup of a maximal subgroup `M` of a minimal simple
group is proper.  `M` is nontrivial (`M_σ ≠ ⊥`, `M_σ ≤ M`) and solvable, so `M' = [M, M] ⊊ M`
(`Group.IsSolvable.commutator_lt_top_of_nontrivial`, transported into `G` along the injective
`M.subtype`). -/
theorem derivedInG_lt_of_maximal [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) : derivedInG M < M := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
      (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  rw [derivedInG]
  conv_rhs => rw [← Subgroup.range_subtype M, MonoidHom.range_eq_map]
  rw [Subgroup.map_lt_map_iff_of_injective M.subtype_injective]
  exact Group.IsSolvable.commutator_lt_top_of_nontrivial (G := ↥M)

/-- **BG Theorem A(6), nontriviality `1 ⊂ M_F`** (mmd L4363, the `1 ⊂ M_F` end of the chain): the
Fitting kernel `M_F` of a maximal subgroup `M` is nontrivial.  Book Theorem 15.2 proof by cases on
whether `M_σ` is nilpotent:

* `M_F = M_σ` (`M_σ` nilpotent): then `M_F = M_σ ≠ ⊥` (`Msigma_ne_bot`);
* `M_F ≠ M_σ` (type `P₁`): Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) supplies `K* ≤ M_F`, and
  `K* ≠ ⊥` (of prime order `q`), so `M_F ≠ ⊥`.

The hypothesis `hKstar_ne : K* ≠ ⊥` is BG Theorem A(5) (`theoremA_ungated_conjuncts`), always
available in the Theorem A setup. -/
theorem maxNilpotentNormalHall_ne_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKstar_ne : Kstar ≠ ⊥)
    (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    S15.MF M ≠ ⊥ := by
  by_cases hne : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
  · rw [hne]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
  · -- type `P₁`: `K* ≤ M_F` (conjunct 7 of Theorem 15.2), and `K* ≠ ⊥`.
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hKstarMF, _⟩ :=
      S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar
    intro hbot
    exact hKstar_ne (le_bot_iff.mp (hbot ▸ hKstarMF))

open scoped IsMulCommutative in
/-- **BG Corollary 15.5(c) / Theorem A(6), `M'/M_F` nilpotent** (mmd L4363, `M'/M_F is nilpotent`):
for every maximal subgroup `M` of a minimal simple group, the quotient of the derived subgroup `M'`
by the Fitting kernel `M_F` is nilpotent.  Book Corollary 15.5(c) proof by cases:

* `M_F = M_σ` (`M_σ` nilpotent, i.e. `M` type I / `M ∈ ℳ_𝓕`): `M'' ⊆ M_σ = M_F`
  (`derivedDerived_le_Msigma` = Corollary 12.10(b) / Lemma 15.1(a)), so `M'/M_F` is **abelian**,
  a fortiori nilpotent;
* `M_F ≠ M_σ` (type `P₁`): Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) gives `M_σ = M'`, a
  normal `q`-subgroup `Q ≤ M_F` with `M_σ = Q ⋊ D` and `D` nilpotent.  Then `M_σ/Q ≅ D` is
  nilpotent (complement iso), and since `Q ≤ M_F ≤ M_σ`, `M'/M_F = M_σ/M_F` is a quotient of the
  nilpotent `M_σ/Q` (Noether's third isomorphism), hence nilpotent.

This is the general (all-`M`) quotient form of the type-`F`/type-`P₁` complement-nilpotency lemmas
(`isNilpotent_complement_of_isTypeF`, `isNilpotent_complement_of_isTypeP1_mf_ne_msigma`), stated
directly on `M'/M_F` as printed in the book.  The `[Normal]` instance is BG background
(`M' ≤ M ≤ N(M_F)`); it is supplied at the call site. -/
theorem derivedInG_quotient_maxNilpotentNormalHall_isNilpotent [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    [((S15.MF M).subgroupOf (derivedInG M)).Normal] :
    Group.IsNilpotent (↥(derivedInG M) ⧸ (S15.MF M).subgroupOf (derivedInG M)) := by
  by_cases hne : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M
  · -- `M_F = M_σ`: `M'' ⊆ M_σ = M_F`, so `M'/M_F` is abelian.
    have hcomm : commutator ↥(derivedInG M) ≤ (S15.MF M).subgroupOf (derivedInG M) := by
      have h2 : derivedInG (derivedInG M) ≤ S15.MF M := by
        rw [hne]; exact S15.derivedDerived_le_Msigma hG hM
      intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact h2 (Subgroup.mem_map_of_mem _ hx)
    have : IsMulCommutative (↥(derivedInG M) ⧸ (S15.MF M).subgroupOf (derivedInG M)) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hcomm
    exact CommGroup.isNilpotent
  · -- type `P₁`: `M_σ = M'`, `Q ≤ M_F`, `M_σ = Q ⋊ D`, `D` nilpotent.  Work directly in `M'`.
    obtain ⟨_, Q, _, D, _, _, _, _, _, _, _, _, _, hQMF, hMnormQ, hcomplQD, hDnil, _, _, _,
      hMσderived, _, _, _, _⟩ := S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK hKstar
    -- push the `M_σ = M'` identification into the complement and containment facts.
    rw [hMσderived] at hcomplQD
    have hMFM' : S15.MF M ≤ derivedInG M :=
      hMσderived ▸ S15.maxNilpotentNormalHall_le_Msigma hG hM
    have hM'M : derivedInG M ≤ M := hMσderived ▸ OddOrder.BG.Ch3.S10.Msigma_le M
    have hQM' : Q ≤ derivedInG M := hQMF.trans hMFM'
    have hQnM' : (Q.subgroupOf (derivedInG M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM').mpr (hM'M.trans hMnormQ)
    -- `↥(D.subgroupOf M')` is nilpotent (embeds in the nilpotent `↥D` via `D ⊓ M'`).
    have hDnil' : Group.IsNilpotent ↥D := hDnil
    have hInfNil : Group.IsNilpotent ↥(D ⊓ derivedInG M) :=
      Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ derivedInG M ≤ D))
    have hDsubNil : Group.IsNilpotent ↥(D.subgroupOf (derivedInG M)) := by
      have econgr : ↥(D.subgroupOf (derivedInG M)) ≃*
          ↥((D ⊓ derivedInG M).subgroupOf (derivedInG M)) :=
        MulEquiv.subgroupCongr (Subgroup.inf_subgroupOf_right D (derivedInG M)).symm
      exact Group.nilpotent_of_mulEquiv (econgr.trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ derivedInG M ≤ derivedInG M))).symm
    -- `M'/Q ≅ ↥(D.subgroupOf M')` is nilpotent (complement iso, `Q` normal).
    have hNilM'Q : Group.IsNilpotent (↥(derivedInG M) ⧸ Q.subgroupOf (derivedInG M)) :=
      Group.nilpotent_of_mulEquiv (hcomplQD.symm.QuotientMulEquiv).symm
    -- `M'/M_F` is a quotient of the nilpotent `M'/Q` (Noether III, `Q ≤ M_F`), hence nilpotent.
    have hsub : Q.subgroupOf (derivedInG M) ≤ (S15.MF M).subgroupOf (derivedInG M) :=
      Subgroup.comap_mono hQMF
    exact Group.nilpotent_of_mulEquiv
      (QuotientGroup.quotientQuotientEquivQuotient (Q.subgroupOf (derivedInG M))
        ((S15.MF M).subgroupOf (derivedInG M)) hsub)

/-- **BG Theorem A — the faithful monolith** (mmd L4346-4355), all 16 conjuncts `sorry`-free.

This is the canonical faithful form of BG Theorem A.  It includes the explicit `hKM : K ≤ M` and
`hUM : U ≤ M` that the BG setup `M = K U M_σ` carries but the bare Hall
conditions on `K.subgroupOf M` / `U.subgroupOf M` do not force, so conjuncts A(3) (`M = K U M_σ`),
A(4) (`C_U(k) = 1`), and A(8) (`U = 1`) become provable.  Every conjunct is discharged by a
standalone lemma — none gated:

* A(1) `M_σ` is `σ(M)`-Hall, A(2) `K` cyclic, A(3)-normal `M ≤ N(U M_σ)`, A(4) `C_U(k) = 1`,
  A(5) `K* ≠ 1` and `C_M(k) = K K*`, A(6) `M_F ≤ M_σ ≤ M'` — all from `theoremA_ungated_conjuncts`;
* A(3)-decomposition `M = K U M_σ` — `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma`;
* A(6) the full book chain `1 ⊂ M_F ⊆ M_σ ⊆ M' ⊂ M` and `M'/M_F` nilpotent — the three clauses
  beyond `M_F ≤ M_σ ≤ M'` are `M_F ≠ ⊥` (`maxNilpotentNormalHall_ne_bot`), `M' ⊊ M`
  (`derivedInG_lt_of_maximal`), and the quotient nilpotency
  (`derivedInG_quotient_maxNilpotentNormalHall_isNilpotent`, Corollary 15.5(c)).  The last is stated
  as `∀ [((M_F).subgroupOf M').Normal], IsNilpotent (M' ⧸ M_F)`: the `[Normal]` is BG background
  (`M' ≤ M ≤ N(M_F)`) which a consumer discharges once and applies — this keeps the monolith's own
  signature instance-free so consumers of the *other* conjuncts are unaffected;
* A(7) `M'' ⊆ F(M)` — `derivedDerived_le_fittingInAmbient` (now ungated, issue 8012); plus the
  Corollary 15.5 Fitting decomposition `F(M) = C_M(M_F) M_F` and `K ≠ 1 ⟹ F(M) ⊆ M'` (the latter
  via `¬type-F`), both from `fitting_decomposition`;
* A(8) `M_F ≠ M_σ ⟹ U = 1 ∧ F(M)` TI `∧ |K|` prime — `theoremA8_structure` (`U.subgroupOf M = ⊥`
  upgraded to `U = ⊥` via `hUM`).

BG A(3)'s `U ⊴ UK` is *not* carried here: BG's `U` is a *specific* `K`-invariant complement, whereas
this monolith is parametrized over an *arbitrary* `(κ ∪ σ)'`-Hall `U` (its `M_σ`-conjugates are
equally valid Hall complements and are generally not `K`-invariant), so `K ≤ N(U)` — and hence
`U ⊴ UK` — cannot be asserted for every such `U`.  The `K`-invariant complement's existence is a
separate statement (`S14.exists_kappaHall_invariant_complement_to_MF` gives the `M_F`-complement
form `M' = M_F U`, `K ≤ N(U)`).

The former bare overstatement omitted `hKM`/`hUM` and was retired after all consumers migrated;
this theorem is the sole monolithic Theorem A API. -/
theorem theoremA_maximal_structure_faithful [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M)) :
    Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.Msigma M) ∧
      IsCyclic ↥K ∧
      M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M ∧
      M ≤ Subgroup.normalizer ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) ∧
      (∀ k ∈ K, k ≠ 1 → U ⊓ Subgroup.centralizer ({k} : Set G) = ⊥) ∧
      Kstar ≠ ⊥ ∧
      (K ≠ ⊥ → ∀ k ∈ K, k ≠ 1 → M ⊓ Subgroup.centralizer ({k} : Set G) = K ⊔ Kstar) ∧
      S15.MF M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
      OddOrder.BG.Ch3.S10.Msigma M ≤ derivedInG M ∧
      S15.MF M ≠ ⊥ ∧
      derivedInG M < M ∧
      (∀ [((S15.MF M).subgroupOf (derivedInG M)).Normal],
        Group.IsNilpotent (↥(derivedInG M) ⧸ (S15.MF M).subgroupOf (derivedInG M))) ∧
      derivedInG (derivedInG M) ≤ S15.fittingInAmbient M ∧
      S15.fittingInAmbient M = (Subgroup.centralizer (S15.MF M : Set G) ⊓ M) ⊔ S15.MF M ∧
      (K ≠ ⊥ → S15.fittingInAmbient M ≤ derivedInG M) ∧
      (S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M →
        U = ⊥ ∧ S15.FittingIsTI M ∧ ∃ p : ℕ, p.Prime ∧ Nat.card ↥K = p) := by
  obtain ⟨hA1, hA2, hA3n, hA4, hA5a, hA5b, hA6a, hA6b⟩ :=
    theoremA_ungated_conjuncts hG hM hKM hUM hK hKstar hU
  -- A(7) Fitting decomposition (Corollary 15.5): `F(M) = C_M(M_F) M_F` and `¬type-F → F(M) ⊆ M'`.
  obtain ⟨_, _, _, _, _, hFdecomp, _, _, _, _, hFleM'ofNotF, _⟩ := fitting_decomposition hG hM
  -- `K ≠ ⊥ ⟹ M` is type `P` (`κ(M) ≠ ∅`), hence not type `F`.
  have hPofne : K ≠ ⊥ → S14.IsTypeP M := fun hKne =>
    isTypeP_of_isHall_kappa_subgroupOf_ne_bot hK
      (fun h => hKne (by rw [← Subgroup.map_subgroupOf_eq_of_le hKM, h, Subgroup.map_bot]))
  refine ⟨hA1, hA2, typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM hKM hUM hK hU,
    hA3n, hA4, hA5a, hA5b, hA6a, hA6b,
    maxNilpotentNormalHall_ne_bot hG hM hA5a hKM hK hKstar,
    derivedInG_lt_of_maximal hG hM, ?_,
    derivedDerived_le_fittingInAmbient hG hM hKM hK hKstar, hFdecomp,
    fun hKne => hFleM'ofNotF (fun hF => S14.not_isTypeP_and_isTypeF ⟨hPofne hKne, hF⟩), ?_⟩
  · -- A(6) `M'/M_F` nilpotent (instance-parametrized: the `[Normal]` is BG background).
    intro _inst
    exact derivedInG_quotient_maxNilpotentNormalHall_isNilpotent hG hM hKM hK hKstar
  -- A(8): `theoremA8_structure` gives `U.subgroupOf M = ⊥`; lift to `U = ⊥` via `hUM`.
  intro hne
  obtain ⟨hUsub, hTI, hp⟩ := theoremA8_structure hG hM hKM hK hKstar hU hne
  refine ⟨?_, hTI, hp⟩
  have h := Subgroup.map_subgroupOf_eq_of_le hUM
  rw [hUsub, Subgroup.map_bot] at h
  exact h.symm

end OddOrder.BG.Ch4.S16


