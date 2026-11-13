-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeDataBridges
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeDataBridges
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:32:05.628229+00:00
-- url     : https://prove2.me/theorems/679c9efd-d9a6-49d4-88f9-067ca91dfa9d
-- title:
--   BG §16: Proposition 16.1 forward bridges, the shared type data
-- statement:
--   The construction of the shared `TypePData` and type-$F$ bridges from the §14/§15 structure of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, through `isTypeF_derivedInG_of_isTypeP2` and the conditional `isTypeII_of_isTypeP2_of_derived_typeF` (Proposition 16.1 forward bridges).
--
--   Main declarations: `sigCentFam` (The generating family `{U ⊓ C_G(x) : x ∈ M_σ#}` of `centralizerGeneratedBySigma M U`); `typePData_of_inputs`; `typePData_of_isTypeP_of_inputs` (Prop 16.1(b)--(d) forward bridge — `TypePData M` from BG-local `IsTypeP M` (gated-endpoint)); `typePData_of_isTypeP1_mf_eq_msigma`; and 1 more.
--
--   The bundle also proves 23 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeDataBridges.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TypeDataBridges.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TheoremsAE

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- The pointwise `MulAut`-action distributes over `sSup` of subgroups (it is `Subgroup.map`, a
left adjoint, so it preserves arbitrary joins). -/
private theorem mulAut_smul_sSup (a : MulAut G) (T : Set (Subgroup G)) :
    a • sSup T = ⨆ S ∈ T, a • S := by
  rw [Subgroup.pointwise_smul_def]
  exact (Subgroup.gc_map_comap _).l_sSup

/-- Conjugation by `u` carries `C_G(x)` to `C_G(u x u⁻¹)`. -/
private theorem conj_smul_centralizer_singleton (u x : G) :
    MulAut.conj u • Subgroup.centralizer ({x} : Set G)
      = Subgroup.centralizer ({u * x * u⁻¹} : Set G) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have hsmul : ((MulAut.conj u)⁻¹ • g : G) = u⁻¹ * g * u := by
    rw [← map_inv]; simp [MulAut.smul_def]
  rw [hsmul]
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    have h2 := congrArg (fun t => u * t * u⁻¹) h
    calc u * x * u⁻¹ * g = u * (x * (u⁻¹ * g * u)) * u⁻¹ := by group
      _ = u * (u⁻¹ * g * u * x) * u⁻¹ := h2
      _ = g * (u * x * u⁻¹) := by group
  · intro h
    have h2 := congrArg (fun t => u⁻¹ * t * u) h
    calc x * (u⁻¹ * g * u) = u⁻¹ * (u * x * u⁻¹ * g) * u := by group
      _ = u⁻¹ * (g * (u * x * u⁻¹)) * u := by rw [h]
      _ = u⁻¹ * g * u * x := by group

/-- The generating family `{U ⊓ C_G(x) : x ∈ M_σ#}` of `centralizerGeneratedBySigma M U`. -/
private abbrev sigCentFam (M U : Subgroup G) : Set (Subgroup G) :=
  {C | ∃ x ∈ S14.sigmaSharp M, C = U ⊓ Subgroup.centralizer ({x} : Set G)}

/-- `U`-conjugation fixes `⟨C_U(x) | x ∈ M_σ#⟩`: for `u ∈ U ≤ M` it permutes the generating set
`{U ⊓ C_G(x) : x ∈ M_σ#}`, since `M_σ ◁ M` makes `x ↦ u x u⁻¹` a bijection of `M_σ#` and
`u (U ⊓ C_G(x)) u⁻¹ = U ⊓ C_G(u x u⁻¹)`. -/
private theorem conj_smul_centralizerGeneratedBySigma {M U : Subgroup G} {u : G}
    (huM : u ∈ M) (huU : u ∈ U) :
    MulAut.conj u • S15.centralizerGeneratedBySigma M U
      = S15.centralizerGeneratedBySigma M U := by
  -- conjugation by an element of `M` preserves `M_σ#` (as `M_σ ◁ M`).
  have hsig : ∀ v : G, v ∈ M → ∀ x : G, x ∈ S14.sigmaSharp M → v * x * v⁻¹ ∈ S14.sigmaSharp M := by
    intro v hv x hx
    rw [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxMσ, hx1⟩ := hx
    refine ⟨?_, fun h => hx1 (mul_left_cancel ((mul_inv_eq_one.mp h).trans (mul_one v).symm))⟩
    have hvN : v ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
      le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hv
    exact (Subgroup.mem_normalizer_iff.mp hvN x).mp hxMσ
  -- conjugation by `v ∈ M ∩ U` maps each generator to a generator.
  have hgen : ∀ v : G, v ∈ M → v ∈ U →
      ∀ C ∈ sigCentFam M U, MulAut.conj v • C ∈ sigCentFam M U := by
    rintro v hvM hvU C ⟨x, hx, rfl⟩
    exact ⟨v * x * v⁻¹, hsig v hvM x hx, by
      rw [Subgroup.smul_inf, Subgroup.conj_smul_eq_self_of_mem hvU,
        conj_smul_centralizer_singleton]⟩
  rw [show S15.centralizerGeneratedBySigma M U = sSup (sigCentFam M U) from rfl, mulAut_smul_sSup]
  refine le_antisymm (iSup_le fun C => iSup_le fun hC => le_sSup (hgen u huM huU C hC)) ?_
  refine sSup_le fun C hC => ?_
  have hC' : (MulAut.conj u)⁻¹ • C ∈ sigCentFam M U := by
    rw [← map_inv MulAut.conj]
    exact hgen u⁻¹ (inv_mem huM) (inv_mem huU) C hC
  calc C = MulAut.conj u • ((MulAut.conj u)⁻¹ • C) := (smul_inv_smul _ _).symm
    _ ≤ ⨆ C' ∈ sigCentFam M U, MulAut.conj u • C' :=
      le_iSup₂ (f := fun C' (_ : C' ∈ sigCentFam M U) => MulAut.conj u • C')
        ((MulAut.conj u)⁻¹ • C) hC'

/-- **General helper (§14-independent, reusable).**  A nontrivial `M`-normal subgroup `H ⊴ M` of a
maximal subgroup `M` of a minimal simple group is self-normalizing in `G`: `N_G(H) = M`.  `H ⊴ M`
gives `M ≤ N_G(H)`; if the inclusion were proper, maximality forces `N_G(H) = G`, so `H ⊴ G`, and
simplicity gives `H ∈ {⊥, ⊤}` — both excluded (`H ≠ ⊥` by hypothesis, `H ≤ M ⊊ G` rules out `⊤`).
Generalizes `normalizer_Msigma_eq_self` (the `H = M_σ` instance) to any nontrivial `M`-normal `H`.
-/
theorem normalizer_eq_self_of_subgroupOf_normal_of_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M H : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hHle : H ≤ M)
    (hHnorm : (H.subgroupOf M).Normal) (hHne : H ≠ ⊥) :
    Subgroup.normalizer (H : Set G) = M := by
  have hle : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHle).mp hHnorm
  refine le_antisymm ?_ hle
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact le_of_eq heq.symm
  · have hnorm : H.Normal :=
      Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hM).2 _ hlt)
    rcases hG.simple.eq_bot_or_eq_top_of_normal _ hnorm with hbot | htop
    · exact absurd hbot hHne
    · exact absurd (top_le_iff.mp (htop ▸ hHle)) (mem_maximalSubgroups.mp hM).1

/-- **The Fitting subgroup of a maximal subgroup is self-normalizing**: `N_G(F(M)) = M` for a
maximal `M` of a minimal simple group of odd order.  `F(M)` is normal in `M`
(`fittingInG_subgroupOf_normal`) and nontrivial
    (`fitting_ne_bot_of_isSolvable_nontrivial`, as `M` is
a nontrivial — `M_σ ≠ ⊥` — solvable proper subgroup); apply the self-normalizing helper. -/
theorem normalizer_fittingInAmbient_eq_self [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    Subgroup.normalizer (S15.fittingInAmbient M : Set G) = M := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMne : M ≠ ⊥ := fun h =>
    OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM (le_bot_iff.mp (h ▸ OddOrder.BG.Ch3.S10.Msigma_le M))
  have : Nontrivial ↥M := (Subgroup.nontrivial_iff_ne_bot M).mpr hMne
  have hFne : S15.fittingInAmbient M ≠ ⊥ := by
    intro hbot
    refine OddOrder.Isaacs.Ch01.fitting_ne_bot_of_isSolvable_nontrivial ↥M ?_
    have hmap : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype
        = (⊥ : Subgroup ↥M).map M.subtype := by
      rw [Subgroup.map_bot]; exact hbot
    exact Subgroup.map_injective M.subtype_injective hmap
  exact normalizer_eq_self_of_subgroupOf_normal_of_ne_bot hG hM
    (OddOrder.BG.Ch2.S08.fittingInG_le M) (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M) hFne

/-- **Prop 16.1(a) `alternative` disjunct (i), TI case** (Peterfalvi (8.3)(a)): if the Fitting
subgroup `F(M)` of a maximal `M` is `TI` (`FittingIsTI M`), then its nilpotent normal Hall core
`M_F#` is a `TI`-subset with normalizer `N_G(M_F)`.  Since `M_F ≤ F(M)`, an overlap
`a, gag⁻¹ ∈ M_F#` is an overlap in `F(M)#`, so `FittingIsTI` forces `g ∈ N_G(F(M)) = M`
(`normalizer_fittingInAmbient_eq_self`);
and `M_F ⊴ M` gives `M ≤ N_G(M_F)`, whence `g ∈ N_G(M_F)`.  This supplies the first disjunct of the
`TypeIData.alternative` field in the `F(M)`-TI case of the `hFI` bridge of
`proposition_type_classification`
(the non-TI case is the deeper BG Theorem 15.7(e) trichotomy, `fitting_not_ti_cases`). -/
theorem maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hTI : S15.FittingIsTI M) :
    IsTISubset (sharpSubgroup (maxNilpotentNormalHall M))
      (Subgroup.normalizer (maxNilpotentNormalHall M : Set G)) := by
  -- `M_F ≤ F(M)`.
  have hMFleF : maxNilpotentNormalHall M ≤ S15.fittingInAmbient M :=
    S15.maxNilpotentNormalHall_le_fittingInG M
  -- `M ≤ N_G(M_F)` from `M_F ⊴ M`.
  have hMnorm : M ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (maxNilpotentNormalHall_le M)).mp
      (maxNilpotentNormalHall_subgroupOf_normal M)
  -- `N_G(F(M)) = M`.
  have hNF : Subgroup.normalizer (S15.fittingInAmbient M : Set G) = M :=
    normalizer_fittingInAmbient_eq_self hG hM
  intro g hg
  obtain ⟨a, haMem, hgaMem⟩ := hg
  rw [sharpSubgroup, Set.mem_sdiff] at haMem hgaMem
  -- Lift the overlap from `M_F#` to `F(M)#`.
  have ha' : a ∈ sharpSubgroup (S15.fittingInAmbient M) := by
    rw [sharpSubgroup, Set.mem_sdiff]; exact ⟨hMFleF haMem.1, haMem.2⟩
  have hga' : g * a * g⁻¹ ∈ sharpSubgroup (S15.fittingInAmbient M) := by
    rw [sharpSubgroup, Set.mem_sdiff]; exact ⟨hMFleF hgaMem.1, hgaMem.2⟩
  -- `FittingIsTI` ⟹ `g ∈ N_G(F(M)) = M ≤ N_G(M_F)`.
  exact hMnorm (hNF ▸ hTI g ⟨a, ha', hga'⟩)

/-- **Theorem A(8) `U = ⊥` core, from type `P₁`** (mmd L4274): for a type-`P₁` maximal subgroup,
the Hall `(κ(M) ∪ σ(M))ᶜ`-complement `U` is trivial.  Type `P₁` means `κ(M) = π(M) ∖ σ(M)`
(`IsTypeP1.2`), so `π(M) ⊆ κ(M) ∪ σ(M)` and the prime set `(κ(M) ∪ σ(M))ᶜ` meets `π(M)` only in
`∅`; a Hall `(κ ∪ σ)ᶜ`-subgroup of `M` therefore has order coprime to `|M|`, i.e. trivial.

This is the `U = ⊥` conjunct of the faithful Theorem A
(`theoremA_maximal_structure_faithful`), now **derivable from
`Thm 15.2 (mf_ne_msigma_typeP1_structure)`** via `isTypeP1_of_mf_ne_msigma`: `M_F ≠ M_σ ⟹ IsTypeP1 ⟹
U = ⊥`.  Together with `|K| = p` (also a Thm 15.2 output) this leaves only `FittingIsTI M` for the
full A(8).  Stated for the relative `U.subgroupOf M` (which is what the Hall hypothesis constrains);
when `U ≤ M` it gives `U = ⊥`. -/
theorem isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot [Finite G] {M U : Subgroup G}
    (hP1 : S14.IsTypeP1 M)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    U.subgroupOf M = ⊥ := by
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  -- `p ∈ (κ ∪ σ)ᶜ` (Hall) and `p ∈ π(M)` (`|U.subgroupOf M| ∣ |M|`).
  have hpcompl : p ∈ (S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    hU.1 p (Nat.mem_primeFactors.mpr ⟨hpp, hpdvd, Nat.card_pos.ne'⟩)
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpp,
      hpdvd.trans (Subgroup.card_subgroup_dvd_card (U.subgroupOf M)), Nat.card_pos.ne'⟩
  -- but `π(M) ⊆ κ(M) ∪ σ(M)` for type `P₁`.
  refine hpcompl ?_
  by_cases hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M
  · exact Set.mem_union_right _ hpσ
  · exact Set.mem_union_left _ (hP1.2 ▸ ⟨hpM, hpσ⟩)

/-- **For a type-`P₁` maximal subgroup, `M' = M_σ`** (Coq `BGsection16` `typePfacts`: for
`M ∈ ℳ_𝓟₁`, `Ms = M^(1)`; BG Theorem C(3) collapse with the trivial `(κ ∪ σ)'`-complement).
Since `κ(M) = π(M) ∖ σ(M)` for type `P₁`, the Hall `(κ ∪ σ)'`-subgroup `U` of `M` is trivial
(`isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot`), so Lemma 15.1(b)'s decomposition `M' = U M_σ`
(`typeP_auxiliary_structure` conjunct 5) collapses to `M' = M_σ`.

This is the structural fact underlying the type-`P₁` half of Proposition 16.1's forward bridges: the
`TypePData` complement `U` (`M' = M_F ⊔ U`) lives inside `M_σ = M'`, and (Coq `typePfacts`)
`U = ⊥ ⟺ M_F = M_σ` distinguishes type V (`U = ⊥`) from types III/IV (`U ≠ ⊥`). -/
theorem isTypeP1_derivedInG_eq_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) :
    derivedInG M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` and a Hall `(κ ∪ σ)'`-subgroup `U` of `M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K ≠ ⊥` (type `P` has nonempty `κ`).
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- `U = ⊥` (type `P₁`): the `(κ ∪ σ)'`-Hall is trivial.
  have hUbot : U = ⊥ := by
    have h0 : U.subgroupOf M = ⊥ := isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot hP1 hU
    rw [← Subgroup.card_eq_one] at h0 ⊢
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv] at h0
  -- Lemma 15.1(b): `M' = U ⊔ M_σ = ⊥ ⊔ M_σ = M_σ`.
  have haux := typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  rw [(haux.2.2.2.2.1 hKne).1, hUbot, bot_sup_eq]

/-- **Type-`P₁` `M_F`-internal complement** (the `M' = M_F ⋊ U` factorisation of Peterfalvi (8.4.b)
/ Coq `of_typeP`): for a type-`P₁` maximal subgroup `M` with Hall `κ(M)`-subgroup `K`, the Fitting
kernel `M_F` has a `K`-invariant complement `U` inside `M' = M_σ` (`M_F ⊔ U = M'`, `K ≤ N_G(U)`,
`M_F ⊓ U = ⊥`).

Construction: `M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`) is solvable, `M_F ◁ M` is a Hall subgroup
of `M'` (`maxNilpotentNormalHall_isHall`, transferred from `M` via index-divisibility), and `K` (a
`σ'`-group, `κ ⊆ σᶜ`) acts coprimely on the `σ`-group `M'`; the `K`-invariant Schur–Zassenhaus
complement (`exists_aInvariant_complement_within_normal`) supplies `U`.  This discharges the
`hUle`/`hKnorm`/`hDcompl`/`U ≠ ⊥` `TypePData` fields of the FT-critical `hP1neIIIIV` bridge; the
remaining `TypePData` fields (`U` nilpotent `= M'/M_F` nilpotent, the `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`
decomposition) and `N_G(U) ⊆ M` are the deeper Coq `Fcore_structure` content. -/
theorem exists_typeP1_mf_complement [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) :
    ∃ U : Subgroup G, U ≤ derivedInG M ∧
      maxNilpotentNormalHall M ⊔ U = derivedInG M ∧
      K ≤ Subgroup.normalizer (U : Set G) ∧
      maxNilpotentNormalHall M ⊓ U = ⊥ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set M' := derivedInG M with hM'def
  set N := maxNilpotentNormalHall M with hNdef
  have hM'_le_M : M' ≤ M := Subgroup.map_subtype_le _
  have hM'σ : M' = OddOrder.BG.Ch3.S10.Msigma M := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have : Group.IsSolvable ↥M' :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.inclusion hM'_le_M))
      (Subgroup.inclusion_injective hM'_le_M)
  -- `N = M_F ≤ M' = M_σ`.
  have hN_le : N ≤ M' := by rw [hM'σ]; exact maxNilpotentNormalHall_le_Msigma hG hM
  -- Normalizer facts (`M_F ◁ M`, `M' ◁ M`, `K ≤ M`).
  have hM'_norm_N : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'_le_M.trans (maxNilpotentNormalHall_le_normalizer M)
  have hK_norm_M' : K ≤ Subgroup.normalizer (M' : Set G) :=
    hKM.trans (OddOrder.BG.Ch3.S10.le_normalizer_derivedInG M)
  have hK_norm_N : K ≤ Subgroup.normalizer (N : Set G) :=
    hKM.trans (maxNilpotentNormalHall_le_normalizer M)
  -- `M_F` is a Hall subgroup of `M'` (transfer from `M`, since `[M':M_F] ∣ [M:M_F]`).
  have hN_hall : Ch03.IsHallSubgroup (Nat.card ↥N).primeFactors (N.subgroupOf M') := by
    obtain ⟨h1, h2⟩ := maxNilpotentNormalHall_isHall M
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩
    · rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_le).toEquiv] at hp
    · apply h2 p
      have hmul := Subgroup.relIndex_mul_relIndex N M' M hN_le hM'_le_M
      have hdvd : (N.subgroupOf M').index ∣ (N.subgroupOf M).index :=
        ⟨M'.relIndex M, hmul.symm⟩
      exact Nat.primeFactors_mono hdvd Subgroup.index_ne_zero_of_finite hp
  -- `K` (a `σ'`-group) acts coprimely on `M' = M_σ` (a `σ`-group).
  have hCop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥M') := by
    refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl (π := (OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      Nat.card_pos.ne' Nat.card_pos.ne' (fun p hp => ?_) (fun p hp => ?_)
    · -- `p ∈ π(K) ⊆ κ ⊆ σᶜ`.
      have hpκ : p ∈ S14.kappa M := by
        apply hK.1
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv]
      exact S14.kappa_subset_sigmaCompl hpκ
    · -- `p ∈ π(M') = π(M_σ) ⊆ σ`, so `p ∉ σᶜ`.
      simp only [Set.mem_compl_iff, not_not]
      have hpMσ : p ∈ (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)).toEquiv,
          ← hM'σ]
        exact hp
      exact (OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM).1 p hpMσ
  exact OddOrder.GroupTheory.exists_aInvariant_complement_within_normal
    hN_le hM'_norm_N hK_norm_M' hK_norm_N hN_hall hCop

/-- **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-complement is nilpotent** (`M'/M_F` nilpotent, the deferred half
of Corollary 15.5(c)): any complement `U` of `M_F` in `M' = M_σ` is nilpotent.

Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) supplies `Q ⋊ D = M_σ` with `Q ≤ M_F` and `D`
nilpotent; hence `M_σ = M_F · D`, so `M_σ/M_F` is the image of the nilpotent `D` under the
quotient map (`Group.nilpotent_of_surjective`), hence nilpotent.  The complement `U` (`U ⊓ M_F = ⊥`,
`U ⊔ M_F = M_σ`) is isomorphic to `M_σ/M_F` (the restricted quotient map is bijective), so `U` is
nilpotent.  Discharges the `hUnilp` field of the type-`P₁` `TypePData` for the `hP1neIIIIV` bridge.
-/
theorem isNilpotent_complement_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hne : S15.MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Group.IsNilpotent ↥U := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  have hM'σ : derivedInG M = Mσ := isTypeP1_derivedInG_eq_Msigma hG hM hP1
  rw [hM'σ] at hsup
  have hMFMσ : maxNilpotentNormalHall M ≤ Mσ := S15.maxNilpotentNormalHall_le_Msigma hG hM
  have hUMσ : U ≤ Mσ := hsup ▸ le_sup_right
  -- `M̄F = M_F.subgroupOf Mσ` is normal in `↥Mσ`.
  have hMFnormMσ : Mσ ≤ Subgroup.normalizer (maxNilpotentNormalHall M : Set G) :=
    (OddOrder.BG.Ch3.S10.Msigma_le M).trans (S15.maxNilpotentNormalHall_le_normalizer M)
  have hMFbarNorm : ((maxNilpotentNormalHall M).subgroupOf Mσ).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMFMσ).mpr hMFnormMσ
  -- Theorem 15.2: `Q ⋊ D = M_σ`, `Q ≤ M_F`, `D` nilpotent.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKeq]; exact hK'
  obtain ⟨_, Q, _, D, _, _, _, _, _, _, _, _, _, hQMF, _, hQDcompl, hDnil, _⟩ :=
    S15.mf_ne_msigma_typeP1_structure hG hM hne hKM hK rfl
  -- `M̄F ⊔ D̄ = ⊤` in `↥Mσ` (`Q̄ ⊔ D̄ = ⊤`, `Q̄ ≤ M̄F`).
  have hMFDbarTop : (maxNilpotentNormalHall M).subgroupOf Mσ ⊔ D.subgroupOf Mσ = ⊤ :=
    top_le_iff.mp (hQDcompl.sup_eq_top ▸ sup_le_sup_right (Subgroup.subgroupOf_mono Mσ hQMF) _)
  -- `D̄ = D.subgroupOf Mσ` is nilpotent (`≅ D ⊓ Mσ ≤ D`).
  have hDnilI : Group.IsNilpotent ↥D := hDnil
  have hDbarNil : Group.IsNilpotent ↥(D.subgroupOf Mσ) := by
    rw [← Subgroup.inf_subgroupOf_right]
    exact Group.nilpotent_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ Mσ ≤ D)).trans
        (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ⊓ Mσ ≤ Mσ)).symm)
  -- `M_σ/M_F` is nilpotent: the quotient map restricts to a surjection `D̄ ↠ M_σ/M_F`.
  have hquotNil : Group.IsNilpotent (↥Mσ ⧸ (maxNilpotentNormalHall M).subgroupOf Mσ) := by
    have hsurj : Function.Surjective
        (((QuotientGroup.mk' ((maxNilpotentNormalHall M).subgroupOf Mσ)).comp
          (D.subgroupOf Mσ).subtype)) := by
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      obtain ⟨m, hm, d, hd, hmd⟩ :=
        Subgroup.mem_sup_of_normal_left.mp (hMFDbarTop ▸ Subgroup.mem_top g)
      refine ⟨⟨d, hd⟩, ?_⟩
      change QuotientGroup.mk (d : ↥Mσ) = QuotientGroup.mk g
      rw [← hmd, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hm, one_mul]
    exact Group.nilpotent_of_surjective _ hsurj
  -- `U ≅ M_σ/M_F`: the restricted quotient map `Ū → M_σ/M_F` is bijective.
  have hŪsup : U.subgroupOf Mσ ⊔ (maxNilpotentNormalHall M).subgroupOf Mσ = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUMσ hMFMσ, sup_comm, hsup, Subgroup.subgroupOf_self]
  set g : ↥(U.subgroupOf Mσ) →* (↥Mσ ⧸ (maxNilpotentNormalHall M).subgroupOf Mσ) :=
    (QuotientGroup.mk' ((maxNilpotentNormalHall M).subgroupOf Mσ)).comp (U.subgroupOf Mσ).subtype
    with hgdef
  have hUbarInf : U.subgroupOf Mσ ⊓ (maxNilpotentNormalHall M).subgroupOf Mσ = ⊥ := by
    rw [eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hval : (a : G) ∈ maxNilpotentNormalHall M ⊓ U :=
      ⟨Subgroup.mem_subgroupOf.mp ha.2, Subgroup.mem_subgroupOf.mp ha.1⟩
    rw [hinf, Subgroup.mem_bot] at hval
    rw [Subgroup.mem_bot]
    exact Subtype.ext hval
  have hginj : Function.Injective g := by
    intro x y hxy
    have hdiv : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈ (maxNilpotentNormalHall M).subgroupOf Mσ :=
      (QuotientGroup.eq.mp hxy)
    have hxinv : (x : ↥Mσ)⁻¹ ∈ U.subgroupOf Mσ := inv_mem x.2
    have hUmem : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈ U.subgroupOf Mσ := mul_mem hxinv y.2
    have hmem : (x : ↥Mσ)⁻¹ * (y : ↥Mσ) ∈
        U.subgroupOf Mσ ⊓ (maxNilpotentNormalHall M).subgroupOf Mσ :=
      ⟨hUmem, hdiv⟩
    rw [hUbarInf, Subgroup.mem_bot, mul_eq_one_iff_inv_eq, inv_inv] at hmem
    exact Subtype.ext hmem
  have hgsurj : Function.Surjective g := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective y
    have hz : z ∈ U.subgroupOf Mσ ⊔ (maxNilpotentNormalHall M).subgroupOf Mσ := by
      rw [hŪsup]; exact Subgroup.mem_top z
    obtain ⟨u, hu, m, hm, hum⟩ := Subgroup.mem_sup_of_normal_right.mp hz
    refine ⟨⟨u, hu⟩, ?_⟩
    change QuotientGroup.mk (u : ↥Mσ) = QuotientGroup.mk z
    rw [← hum, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hm, mul_one]
  have : Group.IsNilpotent ↥(U.subgroupOf Mσ) :=
    Group.nilpotent_of_mulEquiv (MulEquiv.ofBijective g ⟨hginj, hgsurj⟩).symm
  exact Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hUMσ)

/-- **Type-`P₁` `M_F`-complement is a genuine complement in `M'`** (the `hDcompl` `TypePData`
field): any `U` with `M_F ⊔ U = M'` and `M_F ⊓ U = ⊥` gives
`IsComplement' (M_F.subgroupOf M') (U.subgroupOf M')`.

`M_F ◁ M ⊇ M'`, so `M_F.subgroupOf M'` is normal in `↥M'`; with `M_F ⊓ U = ⊥` (disjoint) and
`M_F ⊔ U = M'` (codisjoint, i.e. `⊤` in `↥M'`) the internal product is the whole of `↥M'`.  Card
route: `[M':M_F] = M_F.relIndex M' = M_F.relIndex U = |U|` (second isomorphism theorem
`relIndex_sup_right`, then `M_F ⊓ U = ⊥`), so `|M_F.subgroupOf M'|·|U.subgroupOf M'| = |M'|`, and
`isComplement'_of_card_mul_and_disjoint` concludes.  Purely from `hsup`/`hinf` (no type-`P₁`
hypothesis); discharges the deepest *non*-Fitting `U`-field gated by `exists_typeP1_mf_complement`.
-/
theorem isComplement'_mf_complement_of_sup_inf [Finite G] {M U : Subgroup G}
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    Subgroup.IsComplement' ((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
      (U.subgroupOf (derivedInG M)) := by
  classical
  set M' := derivedInG M with hM'def
  set N := maxNilpotentNormalHall M with hNdef
  have hNle : N ≤ M' := hsup ▸ le_sup_left
  have hUle : U ≤ M' := hsup ▸ le_sup_right
  -- `N.subgroupOf M'` is normal in `↥M'` (`M' ≤ M ≤ N_G(N)`).
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hNnormM' : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'M.trans (maxNilpotentNormalHall_le_normalizer M)
  have hN'norm : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr hNnormM'
  -- Disjointness and codisjointness in `↥M'`.
  have hdisj : Disjoint (N.subgroupOf M') (U.subgroupOf M') := by
    rw [disjoint_iff, eq_bot_iff]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    have hval : (a : G) ∈ N ⊓ U :=
      ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
    rw [hinf, Subgroup.mem_bot] at hval
    rw [Subgroup.mem_bot]; exact Subtype.ext hval
  have hsup' : N.subgroupOf M' ⊔ U.subgroupOf M' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNle hUle, hsup, Subgroup.subgroupOf_self]
  -- `[M':M_F] = |U.subgroupOf M'|` (second iso theorem, then disjointness).
  have hidx : (N.subgroupOf M').index = Nat.card ↥(U.subgroupOf M') := by
    have key : (N.subgroupOf M').relIndex (U.subgroupOf M') = Nat.card ↥(U.subgroupOf M') := by
      rw [Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr hdisj, Subgroup.index_bot]
    rw [← key, ← Subgroup.relIndex_sup_right, sup_comm, hsup', Subgroup.relIndex_top_right]
  have hcard : Nat.card ↥(N.subgroupOf M') * Nat.card ↥(U.subgroupOf M') = Nat.card ↥M' := by
    rw [← hidx, Subgroup.card_mul_index]
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdisj

/-- **Coprime inner-induced conjugation is trivial**: if `x` normalizes `N`, `orderOf x` is coprime
to `|N|`, and conjugation by `x` agrees on `N` with conjugation by some `n ∈ N` (so `x` induces an
*inner* automorphism of `N`), then `x` centralizes `N`.

The induced automorphism `φ(x) ∈ Aut(N)` (via `normalizerMonoidHom`) equals `φ(n)`, an inner
automorphism by `n ∈ N`, so `orderOf (φ x)` divides both `orderOf x` and `|N|` (as
`orderOf (φ n) ∣ orderOf n ∣ |N|`); coprimality forces `orderOf (φ x) = 1`, i.e. `φ x = 1`, i.e.
`x ∈ ker (normalizerMonoidHom N) = C_G(N)`.  This is the coprime-action core of the type-`P₁`
`M_F`-internal Fitting decomposition (`F(M) ⊓ U ⊆ C(M_F)`). -/
theorem mem_centralizer_of_inner_conj_of_coprime [Finite G] {N : Subgroup G} {x n : G}
    (hxN : x ∈ Subgroup.normalizer (N : Set G)) (hn : n ∈ N)
    (hcop : Nat.Coprime (orderOf x) (Nat.card ↥N))
    (hconj : ∀ y ∈ N, x * y * x⁻¹ = n * y * n⁻¹) :
    x ∈ Subgroup.centralizer (N : Set G) := by
  classical
  have hnN : n ∈ Subgroup.normalizer (N : Set G) := Subgroup.le_normalizer hn
  set φ := N.normalizerMonoidHom with hφ
  -- `φ ⟨x⟩ = φ ⟨n⟩`: conjugation by `x` and by `n` agree on `N`.
  have hφeq : φ ⟨x, hxN⟩ = φ ⟨n, hnN⟩ := by
    ext y
    exact hconj (y : G) y.2
  -- `orderOf (φ ⟨x⟩) ∣ orderOf x`.
  have hdvd_x : orderOf (φ ⟨x, hxN⟩) ∣ orderOf x := by
    have h1 := orderOf_map_dvd φ ⟨x, hxN⟩
    rwa [Subgroup.orderOf_mk] at h1
  -- `orderOf (φ ⟨x⟩) = orderOf (φ ⟨n⟩) ∣ orderOf n ∣ |N|`.
  have hdvd_N : orderOf (φ ⟨x, hxN⟩) ∣ Nat.card ↥N := by
    rw [hφeq]
    refine (orderOf_map_dvd φ ⟨n, hnN⟩).trans ?_
    rw [Subgroup.orderOf_mk]
    exact Subgroup.orderOf_dvd_natCard N hn
  -- Coprimality forces the induced automorphism to be trivial.
  have h1 : orderOf (φ ⟨x, hxN⟩) = 1 := Nat.eq_one_of_dvd_coprimes hcop hdvd_x hdvd_N
  have hker : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (N : Set G))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker, ← orderOf_eq_one_iff]; exact h1
  rw [hφ, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hker
  exact hker

/-- **Type-`P₁` (`M_F ≠ M_σ`) `M_F`-internal Fitting decomposition** (BG Corollary 15.5, the
`M' = M_σ` form): for a type-`P₁` maximal `M` with `M_F`-complement `U` in `M' = M_σ`
(`M_F ⊔ U = M'`, `M_F ⊓ U = ⊥`), the Fitting subgroup is `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.

`F(M)` is nilpotent with `M_F` a normal Hall subgroup (Hall in `M`, hence in `F(M)`) and
`F(M) ≤ M'` (`M` is not type `F`).  By the modular law `F(M) = M_F ⊔ (U ⊓ F(M))` (`M_F ≤ F(M)`,
`F(M) ≤ M' = M_F ⊔ U`).  The crux `U ⊓ F(M) ⊆ C(M_F)`: each `x ∈ U ⊓ F(M)` decomposes (Corollary
15.5, `F(M) = C_M(M_F) · M_F`) as `x = a · b` with `a ∈ C(M_F)`, `b ∈ M_F`, so conjugation by `x`
agrees on `M_F` with conjugation by `b` (inner); as `|U|` is coprime to `|M_F|` (`M_F` Hall),
`mem_centralizer_of_inner_conj_of_coprime` forces `x ∈ C(M_F)`.  Discharges the `hFiteq` (and hence
`hSDfit`, via `M'' ≤ F(M)`) residual of the type-`P₁` `TypePData` for the `hP1neIIIIV` bridge. -/
theorem fittingInAmbient_eq_mf_sup_inf_of_isTypeP1_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M)
    (hsup : maxNilpotentNormalHall M ⊔ U = derivedInG M)
    (hinf : maxNilpotentNormalHall M ⊓ U = ⊥) :
    (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set N := maxNilpotentNormalHall M with hNdef
  set M' := derivedInG M with hM'def
  set F := S15.fittingInAmbient M with hFdef
  have hnotF : ¬ S14.IsTypeF M := fun hF => (S14.isTypeF_iff_not_isTypeP.mp hF) hP1.1
  obtain ⟨_Y, -, -, -, _hM''F, hFcent, -, -, -, _hNM', hFle, -⟩ := S15.fitting_decomposition hG hM
  have hFleM' : F ≤ M' := hFle hnotF
  have hM'M : M' ≤ M := Subgroup.map_subtype_le _
  have hFM : F ≤ M := hFleM'.trans hM'M
  have hNF : N ≤ F := S15.maxNilpotentNormalHall_le_fittingInG M
  have hNM : N ≤ M := maxNilpotentNormalHall_le M
  have hUle : U ≤ M' := hsup ▸ le_sup_right
  -- `coprime |U| |N|`: `|U| ∣ [M:N]` (complement card), `N` Hall in `M`.
  have hcompl := isComplement'_mf_complement_of_sup_inf hsup hinf
  have hcard0 := (Subgroup.isComplement'_iff_card_mul_and_disjoint.mp hcompl).1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show N ≤ M' from hNF.trans hFleM')).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv] at hcard0
  -- `hcard0 : |N| * |U| = |M'|`.
  have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥N) := by
    have hHall := maxNilpotentNormalHall_isHall M
    have hci := hHall.coprime_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv] at hci
    -- `hci : coprime |N| (N.subgroupOf M).index`.
    have hMeq : Nat.card ↥N * (N.subgroupOf M).index = Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv]
      exact Subgroup.card_mul_index (N.subgroupOf M)
    have hM'dvdM : Nat.card ↥M' ∣ Nat.card ↥M := by
      rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM'M).toEquiv]
      exact Subgroup.card_subgroup_dvd_card (M'.subgroupOf M)
    have hUdvd : Nat.card ↥U ∣ (N.subgroupOf M).index := by
      have hdvd : Nat.card ↥N * Nat.card ↥U ∣ Nat.card ↥N * (N.subgroupOf M).index := by
        rw [hcard0, hMeq]; exact hM'dvdM
      exact (mul_dvd_mul_iff_left (Nat.card_pos (α := ↥N)).ne').mp hdvd
    exact (hci.coprime_dvd_right hUdvd).symm
  -- `F = N ⊔ (U ⊓ F)` (Dedekind modular law, via `M' = N ⋊ U` and `N ≤ F ≤ M'`).
  have hNnormM' : M' ≤ Subgroup.normalizer (N : Set G) :=
    hM'M.trans (maxNilpotentNormalHall_le_normalizer M)
  have hNnorm' : (N.subgroupOf M').Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hNF.trans hFleM')).mpr hNnormM'
  have hmod : F = N ⊔ (U ⊓ F) := by
    apply le_antisymm
    · intro f hf
      have hfM' : f ∈ M' := hFleM' hf
      have hmemsup : (⟨f, hfM'⟩ : ↥M') ∈ N.subgroupOf M' ⊔ U.subgroupOf M' := by
        rw [← Subgroup.subgroupOf_sup (hNF.trans hFleM') hUle, hsup, Subgroup.subgroupOf_self]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, u, hu, hnu⟩ := Subgroup.mem_sup_of_normal_left.mp hmemsup
      have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
      have huU : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
      have hfnu : f = (n : G) * (u : G) := by
        have h := congrArg Subtype.val hnu; simpa using h.symm
      have huF : (u : G) ∈ F := by
        rw [show (u : G) = (n : G)⁻¹ * f by rw [hfnu]; group]
        exact F.mul_mem (F.inv_mem (hNF hnN)) hf
      rw [hfnu]
      exact Subgroup.mul_mem_sup hnN (Subgroup.mem_inf.mpr ⟨huU, huF⟩)
    · exact sup_le hNF inf_le_right
  -- Crux: `U ⊓ F ≤ C(N)`.
  have hFUcent : U ⊓ F ≤ Subgroup.centralizer (N : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxU, hxF⟩ := hx
    have hxM : x ∈ M := hFM hxF
    have hNnorm : (N.subgroupOf M).Normal := maxNilpotentNormalHall_subgroupOf_normal M
    have hxFM : (⟨x, hxM⟩ : ↥M) ∈
        (Subgroup.centralizer (N : Set G) ⊓ M).subgroupOf M ⊔ N.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup inf_le_right hNM, Subgroup.mem_subgroupOf]
      change x ∈ Subgroup.centralizer (N : Set G) ⊓ M ⊔ N
      rw [← hFcent]; exact hxF
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hxFM
    have haC : (a : G) ∈ Subgroup.centralizer (N : Set G) :=
      (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).1
    have hbN : (b : G) ∈ N := Subgroup.mem_subgroupOf.mp hb
    have hxab : x = (a : G) * (b : G) := by
      have h := congrArg (Subtype.val) hab
      simpa using h.symm
    have hxnorm : x ∈ Subgroup.normalizer (N : Set G) := maxNilpotentNormalHall_le_normalizer M hxM
    have hcopx : Nat.Coprime (orderOf x) (Nat.card ↥N) :=
      Nat.Coprime.coprime_dvd_left (Subgroup.orderOf_dvd_natCard U hxU) hcop
    refine mem_centralizer_of_inner_conj_of_coprime hxnorm hbN hcopx ?_
    intro y hy
    have hbyb : (b : G) * y * (b : G)⁻¹ ∈ N := N.mul_mem (N.mul_mem hbN hy) (N.inv_mem hbN)
    have hcomm := (Subgroup.mem_centralizer_iff.mp haC) _ hbyb
    rw [hxab]
    calc (a : G) * (b : G) * y * ((a : G) * (b : G))⁻¹
        = (a : G) * ((b : G) * y * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (b : G) * y * (b : G)⁻¹ * (a : G) * (a : G)⁻¹ := by rw [← hcomm]
      _ = (b : G) * y * (b : G)⁻¹ := by group
  -- Assemble `F = N ⊔ (U ⊓ C(N))`.
  change F = N ⊔ (U ⊓ Subgroup.centralizer (N : Set G))
  apply le_antisymm
  · rw [hmod]
    exact sup_le_sup_left (le_inf inf_le_left hFUcent) N
  · refine sup_le hNF ?_
    have hle : U ⊓ Subgroup.centralizer (N : Set G) ≤ Subgroup.centralizer (N : Set G) ⊓ M :=
      le_inf inf_le_right (inf_le_left.trans (hUle.trans hM'M))
    exact hle.trans (le_sup_left.trans_eq hFcent.symm)

/-- **Prop 16.1(a) forward bridge, core** (mmd L4480): a type-`F` maximal `M` (`κ(M) = ∅`, so the
Hall `κ`-subgroup `K = ⊥`) carries the shared Peterfalvi type-`F` structure `TypeFData M`.

This is the `M ∈ ℳ_𝓕 ⟹ Type F` core feeding `proposition_type_classification`'s `hFI` (clause (a),
`mpr`).  The deep fields are read off existing §15 results: `U1_commutative` and `frobenius_HU0`
from `typeP_auxiliary_structure` (mmd 15.1(d)(e)); `H = M_F = M_σ` from Theorem A(8) (`U ≠ ⊥` rules
out the `M_F ≠ M_σ` branch); `M = U M_σ` from Theorem A(3) with `K = ⊥`; `centralizer_le_U1` is
`le_sSup` over `M_F# ⊆ M_σ#`; and `U1_normal` (`⟨C_U(x) | x ∈ M_σ#⟩ ◁ U`) is `U`-conjugation
invariance of the generating set `{U ⊓ C_G(x) : x ∈ M_σ#}` (`conj_smul_centralizerGeneratedBySigma`,
as `M_σ ◁ M`).  **Axiom-clean**: A(3) is `typeP_maximal_eq_kappaHall_sup_U_sup_Msigma` and the A(8)
`U = ⊥` exclusion routes through `isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot` (Thm 15.2), not
the retired bare overstatement; `typeP_auxiliary_structure` is itself clean. -/
theorem typeFData_of_kappa_eq_bot [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) (hKbot : K = ⊥)
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  -- Theorem A(3) decomposition `M = K U M_σ` (axiom-clean via the faithful `hKM`/`hUM` inputs).
  have hA3 : M = K ⊔ U ⊔ Mσ := typeP_maximal_eq_kappaHall_sup_U_sup_Msigma hG hM hKM hUM hK hU
  -- `M_F = M_σ`: `U ≠ ⊥` excludes the type-`P₁` `U = ⊥` (Theorem A(8), via Thm 15.2).
  have hMFMσ : S15.MF M = Mσ := by
    by_contra hne
    have hUsub : U.subgroupOf M = ⊥ :=
      isTypeP1_kappaSigma_compl_hall_subgroupOf_eq_bot (isTypeP1_of_mf_ne_msigma hG hM hne) hU
    have h := Subgroup.map_subgroupOf_eq_of_le hUM
    rw [hUsub, Subgroup.map_bot] at h
    exact hUne h.symm
  -- `M = U M_σ` (A3 with `K = ⊥`).
  have hMU : M = U ⊔ Mσ := by rw [hA3, hKbot, bot_sup_eq]
  -- `typeP_auxiliary_structure`: `U1` abelian (15.1(d)) + the Frobenius `U₀ M_σ` (15.1(e)).
  obtain ⟨_, _, _, _, _, _, hU1comm, hU0clause⟩ :=
    typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  obtain ⟨U0, hU0U, hexp, hfrob⟩ := hU0clause hUne
  refine ⟨{
    H := S15.MF M
    U := U
    U1 := S15.centralizerGeneratedBySigma M U
    U0 := U0
    H_eq := rfl
    H_nontrivial := by rw [hMFMσ]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    U_nontrivial := hUne
    H_le := S15.maxNilpotentNormalHall_le M
    U_le := hUM
    U1_le := by
      apply sSup_le
      rintro C ⟨x, _, rfl⟩
      exact inf_le_left
    U0_le := hU0U
    complement := ?_
    U1_normal := ?_
    U1_commutative := hU1comm
    centralizer_le_U1 := by
      intro x hx hx1
      apply le_sSup
      refine ⟨x, ?_, rfl⟩
      rw [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
        Set.mem_singleton_iff]
      exact ⟨S15.maxNilpotentNormalHall_le_Msigma hG hM hx, hx1⟩
    exponent_eq := hexp
    frobenius_HU0 := ?_ }⟩
  · -- `complement`: `M_F = M_σ` complements `U` in `M`.  `M_σ ◁ M`, `M_σ ⊓ U = ⊥` and `M_σ ⊔ U = M`
    -- come from the `K = ⊥` `SubgroupESetup` (`subgroupESetup_of_isHall_kappa_eq_bot`).
    obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
      subgroupESetup_of_isHall_kappa_eq_bot hG hM hKM hUM hK hKbot hU
    rw [hMFMσ]
    have hMσnorm : ((Mσ).subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr
        (le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M)
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxMσ hxU
      rw [Subgroup.mem_subgroupOf] at hxMσ hxU
      have hx : (x : G) ∈ Mσ ⊓ U := ⟨hxMσ, hxU⟩
      rw [hsetup.E_compl_inf, Subgroup.mem_bot] at hx
      exact Subtype.ext hx
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup (OddOrder.BG.Ch3.S10.Msigma_le M) hUM,
        hsetup.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]
  · -- `U1_normal`: `U`-conjugation fixes `⟨C_U(x) | x ∈ M_σ#⟩` (it permutes the generators).
    apply Subgroup.Normal.of_conjugate_fixed
    intro h
    rw [Subgroup.conj_smul_subgroupOf
      (by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left) h,
      conj_smul_centralizerGeneratedBySigma (hUM h.2) h.2]
  · -- `frobenius_HU0`: rewrite `M_F = M_σ`, `M_F ⊔ U₀ = U₀ ⊔ M_σ` into the Frobenius datum.
    rw [hMFMσ, sup_comm]
    exact hfrob

/-- **Prop 16.1(a) `TypeFData` construction wrapper**: a BG-local type-`F` maximal `M`
(`S14.IsTypeF M`, i.e. `κ(M) = ∅`) carries the shared Peterfalvi type-`F` structure
`GroupTheory.IsTypeF M`.  Specializes `typeFData_of_kappa_eq_bot` with `K = ⊥` (a `κ`-Hall since
`κ(M) = ∅`) and a `(κ ∪ σ)'`-Hall `U` from Hall's theorem; `U ≠ ⊥` because the `σ`-complement of a
maximal subgroup is nontrivial (`SubgroupESetup.E_ne_bot`: `E = U = ⊥` would force `M = M_σ ≤ M'`,
contradicting `M' ⊊ M`).  This is the type-`F`-structure half of the `hFI` bridge of
`proposition_type_classification`; the `alternative` trichotomy is added in `isTypeI_of_isTypeF`. -/
theorem isTypeF_groupTheory_of_isTypeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M) :
    OddOrder.GroupTheory.IsTypeF M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hκ : S14.kappa M = ∅ := hF
  -- `K = ⊥` is a `κ(M)`-Hall subgroup (`κ(M) = ∅`).
  have hKhall : Ch03.IsHallSubgroup (S14.kappa M) ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, Ch03.IsHallSubgroup.bot_iff]
    intro p _; rw [hκ]; exact Set.notMem_empty p
  -- A `(κ ∪ σ)'`-Hall subgroup `U` of `M` (Hall's theorem in the solvable `M`).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hUdef
  have hUM : U ≤ M := hUdef ▸ Subgroup.map_subtype_le U'
  have hUeq : U.subgroupOf M = U' :=
    hUdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hUeq ▸ hU'
  -- `U ≠ ⊥`: the `σ`-complement (`= U`, as `K = ⊥`) of the maximal subgroup is nontrivial.
  obtain ⟨E₁, E₂, E₃, hsetup⟩ :=
    subgroupESetup_of_isHall_kappa_eq_bot hG hM bot_le hUM hKhall rfl hU
  have hUne : U ≠ ⊥ := hsetup.E_ne_bot hG
  exact typeFData_of_kappa_eq_bot hG hM bot_le hUM hKhall rfl hU hUne

/-- **BG Theorem 15.7(e), conjunct A divisibility per prime** (Coq `regZq_dv_q1`): for a type-`F`
datum `td` and a `td.U0`-invariant order-`q` subgroup `Z` of the Frobenius kernel `td.H = M_F`, the
exponent of the complement `U` divides `q - 1`.

`td.U0` acts on `Z` by conjugation (`Subgroup.normalizerMonoidHom`, valid since `td.U0 ≤ N_G(Z)`);
the action is fixed-point-free because `td.H ⋊ td.U0` is a Frobenius group with kernel `td.H ⊇ Z`
(`td.frobenius_HU0.conj_frobenius`).  Hence `IsFrobeniusAction td.U0 Z`, giving
`|U0| ∣ |Z| - 1 = q - 1` (`card_dvd_sub_one_of_isFrobeniusAction`), and
`exp U = exp U0 ∣ |U0| ∣ q - 1` (`td.exponent_eq`, `Group.exponent_dvd_nat_card`).  This is the
divisibility engine of the exponent conjunct (c) of `isTypeI_of_isTypeF`; the per-prime witness `Z`
(order-`q` characteristic subgroup of `M_F`) is supplied separately. -/
theorem typeF_exponent_dvd_sub_one_of_invariant_card [Finite G] {M : Subgroup G}
    (td : OddOrder.GroupTheory.TypeFData M) {Z : Subgroup G} {q : ℕ}
    (hZH : Z ≤ td.H) (hZcard : Nat.card ↥Z = q)
    (hU0NZ : td.U0 ≤ Subgroup.normalizer (Z : Set G)) :
    Monoid.exponent ↥td.U ∣ q - 1 := by
  classical
  -- `G`-level fixed-point-freeness of the conjugation action of `U0` on the kernel `td.H`.
  have hfpf : ∀ u ∈ td.U0, u ≠ 1 → ∀ z ∈ td.H, z ≠ 1 → u * z * u⁻¹ ≠ z := by
    intro u hu hu1 z hz hz1 hconj
    have huK : u ∈ td.H ⊔ td.U0 := (le_sup_right : td.U0 ≤ td.H ⊔ td.U0) hu
    have hzK : z ∈ td.H ⊔ td.U0 := (le_sup_left : td.H ≤ td.H ⊔ td.U0) hz
    refine td.frobenius_HU0.conj_frobenius ⟨u, huK⟩ ((Subgroup.mem_subgroupOf).mpr hu)
      (fun h => hu1 (by simpa using Subtype.ext_iff.mp h)) ⟨z, hzK⟩
      ((Subgroup.mem_subgroupOf).mpr hz)
      (fun h => hz1 (by simpa using Subtype.ext_iff.mp h)) ?_
    exact Subtype.ext (by simpa using hconj)
  -- Conjugation action of `U0` on `Z` (`U0 ≤ N_G(Z)`).
  let : MulDistribMulAction ↥td.U0 ↥Z :=
    MulDistribMulAction.compHom ↥Z (Z.normalizerMonoidHom.comp (Subgroup.inclusion hU0NZ))
  have hFA : OddOrder.Isaacs.Ch06.IsFrobeniusAction ↥td.U0 ↥Z := by
    intro u hu z hz hfix
    have h1 : ((u • z : ↥Z) : G) = (u : G) * (z : G) * (u : G)⁻¹ := rfl
    refine hfpf (u : G) u.2 (fun h => hu (Subtype.ext h)) (z : G) (hZH z.2)
      (fun h => hz (Subtype.ext h)) ?_
    rw [← h1]; exact congrArg Subtype.val hfix
  have hdvd : Nat.card ↥td.U0 ∣ q - 1 :=
    hZcard ▸ OddOrder.BG.Ch4.S15.card_dvd_sub_one_of_isFrobeniusAction hFA
  rw [← td.exponent_eq]
  exact Group.exponent_dvd_nat_card.trans hdvd

/-- **Prop 16.1(a) forward bridge `hFI`** (Peterfalvi (8.3) / BG Theorem 15.7): a type-`F` maximal
`M` is of type I.  The shared type-`F` structure `TypeFData M` is `isTypeF_groupTheory_of_isTypeF`;
the `TypeIData.alternative` trichotomy splits on whether `F(M)` is `TI`:

* `FittingIsTI M`: disjunct (a), `M_F#` is a `TI`-subset
  (`maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI`).
* `¬FittingIsTI M`: disjuncts (b)/(c) (`M_F` abelian of rank 2, or the exponent–cyclic case)
  correspond to the BG Theorem 15.7(e) trichotomy (`nonTI_Fitting_structure`, Coq `BGsection15`).
  The abelian branch now **cites** `S15`'s BG (e1) rank half
  (`rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI`); the argument used to be inlined here.
  The non-abelian branch still derives its two conjuncts directly from the non-TI witness
  (`exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI` +
  `typeF_exponent_dvd_sub_one_of_invariant_card`
  for the exponent condition, `typeF_nonabelian_cyclic_opiCore_compl` for cyclic `O_{p'}`); for the
  type-`F` disjunct those two conjuncts are all that is needed (the type-`P₁` Singer case (e3) is
  excluded).  BG's full type-separated (e2)/(e3) refinement, with `p = |X|` pinned, is formalized
  downstream as `S16.fitting_not_ti_structure_e` (issue 3022, closed); the S15-layer
  `S15.fitting_not_ti_trichotomy` keeps only the conjuncts common to (e2)/(e3), being upstream of
  `WitnessPGroup`.

  ⚠ Historical note: until 2026-07-18 the `(e)` clause of the bundled `fitting_not_ti_cases` was
  **logically vacuous** — it read `abelian M_F ∨ (¬abelian M_F ∧ (type F ∨ type P₁))`, whose second
  disjunct is already delivered by that theorem's own conjunct (a), so it collapsed to excluded
  middle.  It has been dropped, and `S15.fitting_not_ti_trichotomy` now carries content on both
  sides. -/
theorem isTypeI_of_isTypeF [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (hF : S14.IsTypeF M) :
    OddOrder.GroupTheory.IsTypeI M := by
  obtain ⟨td⟩ := isTypeF_groupTheory_of_isTypeF hG hM hF
  refine ⟨{ typeF := td, alternative := ?_ }⟩
  by_cases hTI : S15.FittingIsTI M
  · -- `F(M)` TI ⟹ disjunct (a): `M_F#` is a `TI`-subset.
    refine Or.inl ?_
    rw [td.H_eq]
    exact maxNilpotentNormalHall_sharp_isTISubset_of_fittingIsTI hG hM hTI
  · -- `F(M)` not TI ⟹ BG Theorem 15.7(e) trichotomy.  For type `F` the type-`P₁` case (e3) is
    -- excluded, leaving disjunct (b) (`M_F` abelian of rank 2) or (c) (exponent / cyclic-`O_{p'}`).
    rw [td.H_eq]
    -- The non-TI witness: `g ∉ M`, prime `p ∈ σ(M)`, order-`p` `X₁ ≤ M_σ ⊓ M_σ^g`,
    -- `rank (M_F ⊓ C_G(X₁)) < 3`.
    obtain ⟨g, p, X₁, hgM, hp, _hpσ, hX₁card, hX₁Mσ, hX₁cMσ, _hCGnotM, hrank3, -⟩ :=
      exists_inf_conj_fitting_orderP_witness hG hM hTI
    have : Fact p.Prime := ⟨hp⟩
    have hMFeq : MF M = OddOrder.BG.Ch3.S10.Msigma M := mf_eq_msigma_of_not_fittingIsTI hG hM hTI
    -- `X₁ ≤ M_F` and `X₁ ≤ M_F^g` (using `M_F = M_σ`).
    have hX₁MF : X₁ ≤ MF M := le_trans hX₁Mσ (le_of_eq hMFeq.symm)
    have hX₁cMF : X₁ ≤ MulAut.conj g • MF M := by rw [hMFeq]; exact hX₁cMσ
    -- `p` is odd (`p ∣ |X₁| ∣ |G|`, `|G|` odd).
    have hpdvdG : p ∣ Nat.card G := hX₁card ▸ Subgroup.card_subgroup_dvd_card X₁
    have hpOdd : Odd p := by
      rcases hp.eq_two_or_odd' with rfl | h
      · exact absurd (even_iff_two_dvd.mpr hpdvdG) (Nat.not_even_iff_odd.mpr hG.odd)
      · exact h
    by_cases habel : IsMulCommutative ↥(MF M)
    · -- abelian `M_F` ⟹ disjunct (b): `rank M_F = 2`.  This is BG (e1)'s rank half, proved in
      -- `S15` as `rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI` (the argument used to be
      -- inlined here; it is shared with `S15.fitting_not_ti_trichotomy` now).
      refine Or.inr (Or.inl ⟨habel, ?_⟩)
      change rank ↥(MF M) = 2
      exact rank_mf_eq_two_of_isMulCommutative_of_not_fittingIsTI hG hM hTI habel
    · -- non-abelian `M_F` ⟹ disjunct (c): the exponent condition (conjunct A, via the Frobenius
      -- divisibility engine + per-prime order-`q` witnesses) and cyclic `O_{p'}(M_F)` (conjunct B).
      refine Or.inr (Or.inr ⟨fun q _hq hqπ => ?_, ?_⟩)
      · -- conjunct A: `exp U ∣ q - 1` for each `q ∈ π(M_F)`.
        obtain ⟨Z, hZMF, hZcard, hMNZ, -, -⟩ :=
          exists_orderQ_le_mf_normal_in_M_of_not_fittingIsTI hG hM hp hX₁card hX₁MF _hCGnotM
            hrank3 habel _hq hqπ
        exact typeF_exponent_dvd_sub_one_of_invariant_card td (by rw [td.H_eq]; exact hZMF)
          hZcard ((td.U0_le.trans td.U_le).trans hMNZ)
      · -- conjunct B: `∃ p ∈ π(M_F), IsCyclic O_{p'}(M_F)`.
        exact ⟨p, hp,
          (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF _hCGnotM habel).1,
          (typeF_nonabelian_cyclic_opiCore_compl hG hM hp hX₁card hX₁MF _hCGnotM habel).2⟩

/-- **Type-`P` `V`-normalizer characterization** (the `normalizer_V` field of `TypePData`,
Peterfalvi (8.4); BG records it as the self-normalizing exceptional set `M = N_G(V)`): if
`W = W₁ ⊔ W₂` is cyclic and the exceptional set `V = W ∖ (W₁ ∪ W₂)` is a `TI`-subset relative to
`W`, then every nonempty `X ⊆ V` has normalizer exactly `W`.

This is the genuine reduction underlying the deep-looking `normalizer_V` field: `N_G(X) ≤ W` is the
`TI` property (a conjugate of an element of `X ⊆ V` lands back in `V`, forcing the conjugator into
`W`); `W ≤ N_G(X)` is abelianness of the cyclic `W` (every `w ∈ W` centralizes `X ⊆ W`, so fixes it
setwise).  Both inputs (`W = K ⊔ K*` cyclic and the `zTilde K K*` `TI` property) are supplied by
Theorem 14.7 (`typeP_duality`), so this lemma discharges `normalizer_V` once §14 lands. -/
theorem normalizer_eq_sup_of_isTISubset_of_isCyclic {W1 W2 : Subgroup G}
    (hWcyc : IsCyclic ↥(W1 ⊔ W2))
    (hTI : IsTISubset ((↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (W1 ⊔ W2))
    {X : Set G} (hXne : X.Nonempty)
    (hXV : X ⊆ (↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) :
    Subgroup.normalizer X = W1 ⊔ W2 := by
  classical
  have : IsCyclic ↥(W1 ⊔ W2) := hWcyc
  let : CommGroup ↥(W1 ⊔ W2) := IsCyclic.commGroup
  -- elements of the cyclic `W = W₁ ⊔ W₂` commute in `G`.
  have hcomm : ∀ a b : G, a ∈ W1 ⊔ W2 → b ∈ W1 ⊔ W2 → a * b = b * a := fun a b ha hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥(W1 ⊔ W2)) ⟨b, hb⟩)
  apply le_antisymm
  · -- `N_G(X) ≤ W`: a conjugate of `a ∈ X ⊆ V` lands in `V`, so the `TI` property forces `g ∈ W`.
    intro g hg
    obtain ⟨a, haX⟩ := hXne
    have h1 : g⁻¹ * a * g ∈ X := (Subgroup.mem_set_normalizer_iff''.mp hg a).mp haX
    refine hTI g ⟨g⁻¹ * a * g, hXV h1, ?_⟩
    have he : g * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [he]; exact hXV haX
  · -- `W ≤ N_G(X)`: `w ∈ W` centralizes `X ⊆ W` (abelian), so it fixes `X` setwise.
    intro w hw
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    constructor
    · intro hhX
      have hfix : w * h * w⁻¹ = h := by rw [hcomm w h hw (hXV hhX).1]; group
      rw [hfix]; exact hhX
    · intro hconj
      have hhW : h ∈ W1 ⊔ W2 := by
        have hrw : h = w⁻¹ * (w * h * w⁻¹) * w := by group
        rw [hrw]
        exact mul_mem (mul_mem (inv_mem hw) (hXV hconj).1) hw
      have hfix : w * h * w⁻¹ = h := by rw [hcomm w h hw hhW]; group
      rwa [hfix] at hconj

/-- **Prop 16.1(b)--(d) forward bridge, shared core**: assemble the Peterfalvi type-`P` datum
`TypePData M` (mmd L4116/L4190, Peterfalvi (8.4)) from the BG-local structural facts.  This is the
single construction feeding *all three* of the `hP2II`/`hP1neIIIIV`/`hP1eqV` forward bridges of
`proposition_type_classification` (types II, III, IV, V all bundle a `TypePData`).

Following the gated-endpoint skeleton pattern (cf. `typeP_kstar_in_mf_of_inputs`), the deep
structural fields are taken as named hypotheses; their BG sources are:

* the derived-series complement `M = M' W₁`, `W = W₁ ⊔ W₂` cyclic, and the `zTilde` `TI` property
  (`hMcompl`/`hWcyc`/`hTI`) come from Theorem 14.7 (`typeP_duality`) with `W₁ = K`, `W₂ = K*`,
  `W = K ⊔ K*`;
* the **real Fitting** decomposition `F(M) = H ⊔ (U ⊓ C_M(H))` (Peterfalvi (8.5.a), issue 7008 — the
  LHS is `F(M)`, not `M_F`) and `M'' ≤ F(M)`, with `M_F` noncyclic (`hFiteq`/`hSDfit`/`hHncyc`) come
  from Theorem 15.2 (`mf_ne_msigma_typeP1_structure`) and Corollary 15.6;
* the `M'`-internal complement `M' = H U` with `U` nilpotent and **normalized by `W₁`** (Peterfalvi
  (8.4.b); `U ⊴ M'` would force `U = 1`, issue 7008) — `hDcompl`/`hUnilp`/`hW1norm` — comes from
  Lemma 15.1 / Theorem A.

The genuinely *derived* (not renamed) fields are `W_eq` (definitional), `W1_cyclic`/`W2_cyclic`
(subgroups of the cyclic `W`), and `normalizer_V` (the `TI` + cyclic reduction
`normalizer_eq_sup_of_isTISubset_of_isCyclic`).  Sorry-free in its own body. -/
def typePData_of_inputs {M H U W1 W2 : Subgroup G}
    (hHeq : H = maxNilpotentNormalHall M)
    (hHle : H ≤ derivedInG M)
    (hUle : U ≤ derivedInG M)
    (hW1le : W1 ≤ M)
    (hW2le : W2 ≤ H ⊓ secondDerivedInAmbient M)
    (hWcyc : IsCyclic ↥(W1 ⊔ W2))
    (hW1ne : W1 ≠ ⊥) (hW2ne : W2 ≠ ⊥)
    (hMcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (W1.subgroupOf M))
    (hW1norm : W1 ≤ Subgroup.normalizer (U : Set G))
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl :
      Subgroup.IsComplement' (H.subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hHncyc : ¬ IsCyclic ↥H)
    (hSDfit : secondDerivedInAmbient M ≤ H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hFiteq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      H ⊔ (U ⊓ Subgroup.centralizer (H : Set G)))
    (hCentW1 : ∀ x ∈ W1, x ≠ 1 →
      derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = W2)
    (hTI : IsTISubset ((↑(W1 ⊔ W2) : Set G) \ ((W1 : Set G) ∪ (W2 : Set G))) (W1 ⊔ W2)) :
    TypePData M := by
  haveI := hWcyc
  exact
    { H := H
      U := U
      W1 := W1
      W2 := W2
      W := W1 ⊔ W2
      H_eq := hHeq
      H_le := hHle
      U_le := hUle
      W1_le := hW1le
      W2_le := hW2le
      W_eq := rfl
      W_cyclic := hWcyc
      W1_nontrivial := hW1ne
      W2_nontrivial := hW2ne
      W1_cyclic := Subgroup.isCyclic_of_le (le_sup_left : W1 ≤ W1 ⊔ W2)
      W2_cyclic := Subgroup.isCyclic_of_le (le_sup_right : W2 ≤ W1 ⊔ W2)
      M_complement := hMcompl
      W1_normalizes_U := hW1norm
      U_nilpotent := hUnilp
      derived_complement := hDcompl
      H_noncyclic := hHncyc
      secondDerived_le_fitting := hSDfit
      fitting_eq := hFiteq
      centralizer_W1 := hCentW1
      normalizer_V := fun X hXne hXV =>
        normalizer_eq_sup_of_isTISubset_of_isCyclic hWcyc hTI hXne hXV }

/-- **The `W₂ = C_{M'}(W₁#)` centralizer law** (BG Theorem C / Peterfalvi (8.4), the `TypePData`
`centralizer_W1` field): for a type-`P` maximal subgroup with cyclic `κ`-Hall `K`, the
`M'`-centralizer
of every `k ∈ K#` is exactly `K* = C_{M_σ}(K)`.  Sharpens Theorem A(5) (`C_M(k) = K ⊔ K*`,
`typeP_centralizer_kappaElement_eq`) by intersecting with `M'`: since `K* ≤ M'` and `K ⊓ M' = ⊥`
(the `M = M' ⋊ K` complement has coprime orders, Theorem 14.7(h)), the modular law gives
`M' ⊓ (K ⊔ K*) = K*`.  Discharges the `hCentW1` residual of `typePData_of_isTypeP_of_inputs`. -/
theorem typeP_derivedInG_inf_centralizer_kappaElement_eq [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ x ∈ K, x ≠ 1 →
      derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = Kstar := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- Theorem 14.7(h): `M = M' ⋊ K` complement (coprime orders), `K ⊔ K*` cyclic ⟹ `K` cyclic.
  obtain ⟨_hMcompl, hcop, _, ⟨_, _, _, _, hWcyc, _, _, _⟩, _⟩ :=
    typeP_duality hG hM hP hKM hK hKstar
  have : IsCyclic ↥(K ⊔ Kstar) := hWcyc
  have : IsCyclic ↥K := Subgroup.isCyclic_of_le (le_sup_left : K ≤ K ⊔ Kstar)
  -- A Hall `(κ ∪ σ)ᶜ`-subgroup `U` of `M` (for the Theorem A(5) citation).
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K ⊓ M' = ⊥` (coprime `|K|`, `|M'|`).
  have hcop' : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(derivedInG M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((derivedInG M).subgroupOf M) = Nat.card ↥(derivedInG M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).toEquiv
    rw [e1, e2] at hcop; exact hcop.symm
  have hKinfM' : K ⊓ derivedInG M = ⊥ :=
    Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop'
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  -- `K* ≤ M_σ ≤ M'`.
  have hKstarM' : Kstar ≤ derivedInG M := by
    rw [hKstar]; exact inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)
  have hM'M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  -- `K ≤ N(K*)`: `K* ≤ C(K)` (from `K* = M_σ ⊓ C(K)`), so `K ≤ C(K*) ≤ N(K*)`.
  have hKsubCK : Kstar ≤ Subgroup.centralizer (K : Set G) := by rw [hKstar]; exact inf_le_right
  have hKN : K ≤ Subgroup.normalizer (Kstar : Set G) := by
    refine le_trans (fun k hk => ?_) (Subgroup.centralizer_le_normalizer (Kstar : Set G))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsCK := hKsubCK hs
    rw [Subgroup.mem_centralizer_iff] at hsCK
    exact (hsCK k hk).symm
  -- `M' ⊓ C(x) = M' ⊓ (M ⊓ C(x)) = M' ⊓ (K ⊔ K*)`, then Dedekind ⟹ `= K*`.
  intro x hx hx1
  have hA5 := typeP_centralizer_kappaElement_eq hG hM hP hKM hK hKstar hU x hx hx1
  have hredux : derivedInG M ⊓ Subgroup.centralizer ({x} : Set G) = derivedInG M ⊓ (K ⊔ Kstar) := by
    rw [← hA5, ← inf_assoc, inf_eq_left.mpr hM'M]
  rw [hredux]
  -- Dedekind (`eq_sup_inf_of_le_normalizer`): `H = K* ⊔ (H ⊓ K)`, with `H ⊓ K ≤ M' ⊓ K = ⊥`.
  have hKstarH : Kstar ≤ derivedInG M ⊓ (K ⊔ Kstar) := le_inf hKstarM' le_sup_right
  have hHle : derivedInG M ⊓ (K ⊔ Kstar) ≤ Kstar ⊔ K := by rw [sup_comm]; exact inf_le_right
  have hHinfK : (derivedInG M ⊓ (K ⊔ Kstar)) ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    calc (derivedInG M ⊓ (K ⊔ Kstar)) ⊓ K ≤ derivedInG M ⊓ K := inf_le_inf_right K inf_le_left
      _ = ⊥ := by rw [inf_comm]; exact hKinfM'
  rw [eq_sup_inf_of_le_normalizer hKN hKstarH hHle, hHinfK, sup_bot_eq]

/-- **Prop 16.1(b)--(d) forward bridge — `TypePData M` from BG-local `IsTypeP M`** (gated-endpoint).
Constructs the shared Peterfalvi type-`P` datum (`TypePData M`) for a type-`P` maximal subgroup with
a nontrivial `κ(M)`-Hall `K`, discharging *twelve* of the eighteen `typePData_of_inputs` fields from
the proven §14/§15 structure and gating only on the genuinely-deep **`M_F`-internal Fitting core**
(BG Corollary 15.5 / Lemma 15.1):

* discharged (`typeP_duality` = Theorem 14.7: `hMcompl`/`hWcyc`/`hTI`; `typeP_kstar_in_mf` =
  Corollary 15.6: `hW2ne`/`hW2le`/`hHncyc`; the `W₂ = C_{M'}(W₁#)` centralizer law `hCentW1`
  (`typeP_derivedInG_inf_centralizer_kappaElement_eq` = Theorem A(5) + Dedekind); plus
  `hHeq`/`hHle`/`hW1le`/`hW1ne`), with `W₁ = K`, `W₂ = K*`, `W = K ⊔ K*`, `H = M_F`;
* gated (named residuals): the `M_F`-internal complement `U` (`M' = M_F ⊔ U`, `U` nilpotent and
  normalized by `W₁` — `hUle`/`hKnorm`/`hUnilp`/`hDcompl`; issue 7008: `U ⊴ M'` is unfaithful) and
  the
  real Fitting decomposition `F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`hSDfit`/`hFiteq`).

This single construction feeds all three of `hP2II`/`hP1neIIIIV`/`hP1eqV` (types II/III/IV/V bundle
a
`TypePData`); the gated residuals are exactly the `M_F`-internal structure not present in
`typeP_auxiliary_structure`'s `M' = U M_σ` decomposition. -/
noncomputable def typePData_of_isTypeP_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M) (hKM : K ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hUle : U ≤ derivedInG M)
    (hKnorm : K ≤ Subgroup.normalizer (U : Set G))
    (hUnilp : Group.IsNilpotent ↥U)
    (hDcompl : Subgroup.IsComplement'
      ((maxNilpotentNormalHall M).subgroupOf (derivedInG M)) (U.subgroupOf (derivedInG M)))
    (hSDfit : secondDerivedInAmbient M ≤
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)))
    (hFiteq : (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype =
      maxNilpotentNormalHall M ⊔ (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G))) :
    TypePData M := by
  classical
  set Kstar : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
    with hKstar
  -- Theorem 14.7 (`typeP_duality`): the `M'`-complement (`.1`), `K ⊔ K*` cyclic and `zTilde` TI
  -- (extracted in `Prop`-valued `have` blocks — the `∃!` witness cannot be eliminated into the
  -- `def`'s `Type`).
  have hMcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M) :=
    (typeP_duality hG hM hP hKM hK hKstar).1
  have hWcyc : IsCyclic ↥(K ⊔ Kstar) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, h, _, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact h
  have hTI : IsTISubset (S14.zTilde K Kstar) (K ⊔ Kstar) := by
    obtain ⟨_, _, _, ⟨_, _, _, _, _, h, _, _⟩, _⟩ := typeP_duality hG hM hP hKM hK hKstar
    exact h
  -- Corollary 15.6 (`typeP_kstar_in_mf`): `K* ≠ ⊥`, `K* ≤ M_F`, `K* ≤ M''`, `M_F` noncyclic.
  have hk := typeP_kstar_in_mf hG hM hP hKM hK hKstar
  exact typePData_of_inputs (H := maxNilpotentNormalHall M) (U := U) (W1 := K) (W2 := Kstar)
    rfl (maxNilpotentNormalHall_le_derived hG hM) hUle hKM (le_inf hk.2.2.1 hk.2.2.2.1)
    hWcyc hKne hk.1 hMcompl hKnorm hUnilp hDcompl hk.2.2.2.2 hSDfit hFiteq
    (typeP_derivedInG_inf_centralizer_kappaElement_eq hG hM hP hKM hK hKstar) hTI

/-- **For a type-`P₁` maximal subgroup with `M_F = M_σ`, `F(M) = M_F`** (the type-V Fitting
collapse, Coq `BGsection16` `typePfacts` `U = 1` branch).  Corollary 15.5(d)
(`fitting_decomposition`) gives `F(M) ≤ M'` since `M` is type `P` (not type `F`); `M' = M_σ`
(`isTypeP1_derivedInG_eq_Msigma`) `= M_F` (hypothesis), and `M_F ≤ F(M)` always
(`maxNilpotentNormalHall_le_fittingInG`), so `F(M) = M_F`.  This discharges the deepest field
(`fitting_eq`) of the type-V `TypePData`, where `U = ⊥` makes `F(M) = M_F ⊔ (⊥ ⊓ C_M(M_F)) = M_F`.
-/
theorem fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hP1 : S14.IsTypeP1 M) (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    S15.fittingInAmbient M = S15.MF M := by
  have hnotF : ¬ S14.IsTypeF M := fun hF => (S14.isTypeF_iff_not_isTypeP.mp hF) hP1.1
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hFle, _⟩ := S15.fitting_decomposition hG hM
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    isTypeP1_derivedInG_eq_Msigma hG hM hP1
  refine le_antisymm ?_ (S15.maxNilpotentNormalHall_le_fittingInG M)
  exact (hFle hnotF).trans_eq (hM'σ.trans hmf.symm)

open scoped IsMulCommutative in
/-- **`TypePData M` for a type-`P₁` maximal subgroup with `M_F = M_σ`** — the type-V
carrier-constructibility milestone: such a maximal subgroup carries a Peterfalvi type-`P` datum with
*trivial* complement `U = ⊥`, `sorry`-free.

For type `P₁`, `M' = M_σ` (`isTypeP1_derivedInG_eq_Msigma`); with `M_F = M_σ` this gives
`M' = M_F`, so the `M_F`-internal complement collapses to `U = ⊥` (Coq `typePfacts`:
`M_F = M_σ ⟺ U = 1`).  Every `U`-field of `typePData_of_isTypeP_of_inputs` then trivializes:
`U ⊴ M'` and `K ≤ N_G(U)` are vacuous (`U = ⊥` normal), `hDcompl` is `IsComplement' ⊤ ⊥`
(`M_F.subgroupOf M' = ⊤` since `M' = M_F`), `hSDfit` is `M'' ≤ M' = M_F`, and `hFiteq` is the
type-V Fitting collapse `F(M) = M_F`
(`fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma`).  Feeds the `hP1eqV` bridge:
`isTypeV_of_typePData` reduces type V to the genuinely-deep Peterfalvi (8.8) `alternative`
trichotomy on `M_F`. -/
noncomputable def typePData_of_isTypeP1_mf_eq_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M)
    (hmf : S15.MF M = OddOrder.BG.Ch3.S10.Msigma M) :
    TypePData M := by
  classical
  haveI : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- A Hall `κ(M)`-subgroup `K` (the cyclic `W₁ = K`).  The goal `TypePData M` is `Type`-valued,
  -- so we extract via `Exists.choose` (not `obtain`, which cannot eliminate a `Prop` into `Type`).
  have hKex := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := hKex.choose.map M.subtype with hKdef
  have hKM : K ≤ M := Subgroup.map_subtype_le hKex.choose
  have hKeq : K.subgroupOf M = hKex.choose :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective hKex.choose
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by
    rw [hKeq]; exact hKex.choose_spec
  have hKne : K ≠ ⊥ := fun h =>
    card_kappaHall_ne_one hP1.1 hKM hK (by rw [h, Subgroup.card_bot])
  -- `M' = M_σ = M_F`, `F(M) = M_F`.
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    isTypeP1_derivedInG_eq_Msigma hG hM hP1
  have hM'MF : derivedInG M = maxNilpotentNormalHall M := hM'σ.trans hmf.symm
  -- Build with `U = ⊥`; every `U`-field trivializes.
  refine typePData_of_isTypeP_of_inputs hG hM hP1.1 hKM hKne hK (U := ⊥) bot_le ?_ ?_ ?_ ?_ ?_
  · -- `hKnorm`: `K ≤ N_G(⊥) = ⊤`.
    exact le_top.trans_eq (Subgroup.normalizer_eq_top (H := (⊥ : Subgroup G))).symm
  · -- `hUnilp`: `⊥` is nilpotent.
    infer_instance
  · -- `hDcompl`: `IsComplement' ⊤ ⊥` (`M_F.subgroupOf M' = ⊤` since `M' = M_F`).
    rw [Subgroup.bot_subgroupOf,
      Subgroup.subgroupOf_eq_top.mpr (le_of_eq hM'MF)]
    exact Subgroup.isComplement'_top_left.mpr rfl
  · -- `hSDfit`: `M'' ≤ M_F` (`M'' ≤ M' = M_F`).
    rw [bot_inf_eq, sup_bot_eq]
    exact (Subgroup.map_subtype_le _ : secondDerivedInAmbient M ≤ derivedInG M).trans_eq hM'MF
  · -- `hFiteq`: `F(M) = M_F` (type-V Fitting collapse).
    rw [bot_inf_eq, sup_bot_eq]
    exact fittingInAmbient_eq_maxNilpotentNormalHall_of_isTypeP1_mf_eq_msigma hG hM hP1 hmf

/-- **Prop 16.1 forward bridge, type III/IV last mile** (Peterfalvi (8.7)): a type-`P` datum whose
`U`-factor has its normalizer inside `M` is of type III or IV, according as `U` is abelian or not.
This is the clean part of the `hP1neIIIIV` bridge — no deep `alternative`/`derived_typeF` content,
only the decidable `IsMulCommutative ↥U` split distinguishing III (`U` abelian) from IV. -/
theorem isTypeIII_or_IV_of_typePData {M : Subgroup G} (data : TypePData M)
    (hcommon : TypePNontrivialCore M data)
    (hnorm : Subgroup.normalizer (data.U : Set G) ≤ M) :
    IsTypeIII M ∨ IsTypeIV M := by
  classical
  by_cases hU : IsMulCommutative ↥data.U
  · exact Or.inl ⟨{ typeP := data, common := hcommon, U_commutative := hU, normalizer_le := hnorm }⟩
  · exact Or.inr
      ⟨{ typeP := data, common := hcommon, U_not_commutative := hU, normalizer_le := hnorm }⟩

/-- **Prop 16.1 forward bridge, type II last mile** (Peterfalvi (8.6)): a type-`P` datum with `U`
abelian, `N_G(U) ⊄ M`, and the derived subgroup `M'` of type `F` (with `F(M') = H`) is of type II.
The `derived_typeF` field is the genuinely deep named residual (the type-`F` structure of `M'`). -/
theorem isTypeII_of_typePData {M : Subgroup G} (data : TypePData M)
    (hcommon : TypePNontrivialCore M data)
    (hUcomm : IsMulCommutative ↥data.U)
    (hnorm : ¬ Subgroup.normalizer (data.U : Set G) ≤ M)
    (hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M))
    (hderfit : maxNilpotentNormalHall (derivedInG M) = data.H) :
    IsTypeII M :=
  ⟨{ typeP := data, common := hcommon, U_commutative := hUcomm,
     normalizer_not_le := hnorm, derived_typeF := hderF, derived_fitting_eq := hderfit }⟩

open scoped IsMulCommutative in
/-- **Prop 16.1 forward bridge `hP2II`, reduced to the `M'`-type-`F` residual** — a type-`P₂`
maximal subgroup whose derived subgroup `M'` is of type `F` (with `F(M') = M_F`) is of type II.

This discharges *every* `isTypeII_of_typePData` input that is BG-local for the type-`P₂` case,
leaving exactly the genuinely-deep `M'`-type-`F` structure (`hderF`/`hderfit`, Peterfalvi (8.6)) as
hypotheses.  Notably **the whole `TypePNontrivialCore` (`hcommon`) is lane-local, not lane-b**:
`U ≠ ⊥` from the matched pair, `|W₁| = |K|` prime *and* the `M_σ`-`TI` condition both from
Proposition 14.2(g) (`typeP_structure`, proved) — `M_F = M_σ` for type `P₂`, so its `sharp`-`TI`
*is* the `σ#`-`TI`.  (Correcting the stale belief that `|W₁|` prime needs the lane-b (10.11)
`theorem88_caseB_prime_orders`; that is the *partner* primality, not the type-`P₂` `κ`-Hall's.)
`N_G(U) ⊄ M` is Corollary 14.12 (`typeP2_neighbor_is_typeF`) applied to a Sylow `r`-subgroup of the
matched `U`; the `TypePData` itself is `typePData_of_isTypeP2`.  The single remaining gate for the
`hP2II` bridge of `proposition_type_classification` is thus the type-`F` structure of `M'`. -/
theorem isTypeII_of_isTypeP2_of_derived_typeF [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hderF : OddOrder.GroupTheory.IsTypeF (derivedInG M))
    (hderfit : maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M) :
    OddOrder.GroupTheory.IsTypeII M := by
  classical
  have hex := typeP2_exists_matched_kappa_hall_pair hG hM hP2
  set K := hex.choose with hKdef
  set U := hex.choose_spec.choose with hUdef
  have hspec := hex.choose_spec.choose_spec
  have hKM : K ≤ M := hspec.1
  have hUM : U ≤ M := hspec.2.1
  have hUne : U ≠ ⊥ := hspec.2.2.1
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hspec.2.2.2.1
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M) :=
    hspec.2.2.2.2.1
  have hUcomm : IsMulCommutative ↥U := hspec.2.2.2.2.2.1
  have hKnorm : K ≤ Subgroup.normalizer (U : Set G) := hspec.2.2.2.2.2.2
  have hP : S14.IsTypeP M := hP2.1
  have hKne : K ≠ ⊥ := fun h => card_kappaHall_ne_one hP hKM hK (by rw [h, Subgroup.card_bot])
  have hM'eq := (typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU).1
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  have := hUcomm
  have hUnilp : Group.IsNilpotent ↥U := inferInstance
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  -- Proposition 14.2(g): `|K| = q` prime and `M_σ#` is `TI` (the `M_F#`-`TI` since `M_F = M_σ`).
  obtain ⟨_, q, hqp, hKq, hMσTI⟩ := (S14.typeP_structure hG hM hP hKM hK rfl hU).2.2.2.2.1 hP2
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥U) (⟨b, hb⟩ : ↥U))
  -- `N_G(U) ⊄ M`: Corollary 14.12 applied to a Sylow `r`-subgroup `R ≤ U` (`r ∈ π(U)`, `U ≠ ⊥`).
  have hnorm : ¬ Subgroup.normalizer (U : Set G) ≤ M := by
    obtain ⟨r, hrp, hrdvd⟩ := Nat.exists_prime_and_dvd
      (show Nat.card ↥U ≠ 1 from fun h => hUne (Subgroup.card_eq_one.mp h))
    have hrπU : r ∈ S14.piSet U := Nat.mem_primeFactors.mpr ⟨hrp, hrdvd, Nat.card_pos.ne'⟩
    obtain ⟨R', hR'⟩ := Ch03.hall_E_exists (G := ↥U) ({r} : Set ℕ)
    intro hNU
    obtain ⟨H, _, _, _, _, hHnorm⟩ := S14.typeP2_neighbor_is_typeF hG hM hP2 hKM hUM hK hU hUab
      hrπU (Subgroup.map_subtype_le R')
      (by rw [show (R'.map U.subtype).subgroupOf U = R' from
        Subgroup.comap_map_eq_self_of_injective U.subtype_injective R']; exact hR') hKnorm
    exact hHnorm (le_trans inf_le_right hNU)
  refine isTypeII_of_typePData
    (typePData_of_isTypeP_of_inputs hG hM hP hKM hKne hK hUle hKnorm hUnilp
      hdec.1 hdec.2.1 hdec.2.2)
    ⟨?_, ?_, ?_⟩ ?_ ?_ hderF ?_
  · change U ≠ ⊥; exact hUne
  · change (Nat.card ↥K).Prime; rw [hKq]; exact hqp
  · rw [hMFMσ]; exact hMσTI
  · change IsMulCommutative ↥U; exact hUcomm
  · change ¬ Subgroup.normalizer (U : Set G) ≤ M; exact hnorm
  · change maxNilpotentNormalHall (derivedInG M) = maxNilpotentNormalHall M; exact hderfit

/-- **Prop 16.1 / Peterfalvi (8.6.b II), the `M'`-type-`F` residual (`hderF`), unconditional** — the
derived subgroup `M' = M^{(1)}` of a type-`P₂` maximal `M` is itself of type `F`.

Structurally `M' = M_σ ⋊ U` is the type-`F`-shaped `M_σ ⋊ (complement)` inside `M` — exactly as the
type-`F` *maximal* of `typeFData_of_kappa_eq_bot` is `M = M_σ ⋊ U` — so the *same* data assemble:
the
`M_σ ⋊ U` complement (`typeP2_mf_internal_fitting_decomposition`), the abelian inertia `U₁` and the
Frobenius factor `M_σ ⋊ U₀` (Lemma 15.1(d)(e), `typeP_auxiliary_structure`), and the crucial
`F`-core
identity `(M')_F = M_σ = M_F`
(`maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2`).  This last
identity is the Coq `defM'F` step (`Fcore_max` + Hall transitivity): it needs **no** `τ₂(M) = ∅`
hypothesis (which is in fact false for some type-`P₂` `M`, cf. Corollary 15.9). -/
theorem isTypeF_derivedInG_of_isTypeP2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M)
    (hKM : K ≤ M) (hUM : U ≤ M) (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M)) [IsCyclic ↥K]
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    (hUne : U ≠ ⊥) :
    OddOrder.GroupTheory.IsTypeF (derivedInG M) := by
  classical
  have hMFMσ : maxNilpotentNormalHall M = OddOrder.BG.Ch3.S10.Msigma M :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr
      (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  have hMFM' : maxNilpotentNormalHall M = maxNilpotentNormalHall (derivedInG M) :=
    hMFMσ.trans (maxNilpotentNormalHall_derivedInG_eq_Msigma_of_isTypeP2 hG hM hP2 hKM hK).symm
  have hdec := typeP2_mf_internal_fitting_decomposition hG hM hP2 hKM hUM hKne hK hU
  obtain ⟨_, _, _, _, hconj5, _, hU1comm, hU0clause⟩ :=
    typeP_auxiliary_structure hG hM hKM hUM hK rfl hU
  obtain ⟨hM'eq, _, _, _⟩ := hconj5 hKne
  have hUle : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  obtain ⟨U0, hU0U, hexp, hfrob⟩ := hU0clause hUne
  refine ⟨{
    H := maxNilpotentNormalHall M
    U := U
    U1 := centralizerGeneratedBySigma M U
    U0 := U0
    H_eq := hMFM'
    H_nontrivial := by rw [hMFMσ]; exact OddOrder.BG.Ch3.S10.Msigma_ne_bot hG hM
    U_nontrivial := hUne
    H_le := maxNilpotentNormalHall_le_derived hG hM
    U_le := hUle
    U1_le := by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left
    U0_le := hU0U
    complement := hdec.1
    U1_normal := ?_
    U1_commutative := hU1comm
    centralizer_le_U1 := by
      intro x hx hx1
      apply le_sSup
      refine ⟨x, ?_, rfl⟩
      rw [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
      exact ⟨maxNilpotentNormalHall_le_Msigma hG hM hx, hx1⟩
    exponent_eq := hexp
    frobenius_HU0 := by rw [hMFMσ, sup_comm]; exact hfrob }⟩
  · -- `U1_normal`: `U`-conjugation permutes the generators `C_U(x)` of
    -- `centralizerGeneratedBySigma`.
    apply Subgroup.Normal.of_conjugate_fixed
    intro h
    rw [Subgroup.conj_smul_subgroupOf
      (by apply sSup_le; rintro C ⟨x, _, rfl⟩; exact inf_le_left) h,
      conj_smul_centralizerGeneratedBySigma (hUM h.2) h.2]

end OddOrder.BG.Ch4.S16


