-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S12_TypeIICrossIsometryPair
-- name    : OddOrder_Peterfalvi_S12_TypeIICrossIsometryPair
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:24:05.211043+00:00
-- url     : https://prove2.me/theorems/10e6d383-d98e-4556-8084-0c6d8482b61a
-- title:
--   Peterfalvi (10.7): the cross-isometry package at the canonical pair
-- statement:
--   Formalizes the cross-isometry package of Peterfalvi (10.7) at the canonical pair (Peterfalvi, *Character Theory for the Odd Order Theorem*, §10), including support facts for the induced family and the core-order coprimality for a nonconjugate pair.
--
--   Main declarations: `Hypothesis.mem_zSpan_inducedFamily_support_sharp_derived` (`ℤ[𝒮]`-combinations vanishing at `1` are supported in `(M′)^#`); `Hypothesis.supportInSubgroup_sharp_derived_subset_A0` (`(M′)^# ⊆ A₀(M)`); `typeP_core_order_coprime` (The core-order coprimality for a nonconjugate pair); `typeP_escaping_centralizer_not_le_typeII` (Peterfalvi (8.13.b/c4) at the canonical pair, escape-landing exclusion).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S12_TypeIICrossIsometryPair.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S12_TypeIICrossIsometryPair.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIGridTranspose
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S12_TypeIIFrobenius
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_FrobeniusGroupQuotient
import Definitions.Def_OddOrder_Peterfalvi_S12_CrossIsometrySetup

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open OddOrder.GroupTheory

variable {G : Type*} [Group G]

open scoped FiniteInduce in
/-- **`ℤ[𝒮]`-combinations vanishing at `1` are supported in `(M′)^#`** (the `zchar_on`/`defA1`
step of Coq `Frob_der1_type2`): every member of `inducedFamily M` is induced from the normal
`M′`, hence vanishes off `M′` (a ℤ-linear property, so every lattice element does); vanishing
at `1` then pins the support inside the sharp set.  This is the `M`-side support refinement
`supp ⊆ A₁(M) = (M′)^#` feeding the (8.18.b) disjointness (`A₀`-support alone would not do:
the pair's `A₀`-sets share the conjugates of `V`). -/
theorem Hypothesis.mem_zSpan_inducedFamily_support_sharp_derived [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) (inducedFamily M))
    (hφ1 : φ 1 = 0) :
    φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (sharpSubgroup (derivedInG M)) M := by
  have := hyp.finiteG
  classical
  have hKcomm : (derivedInG M).subgroupOf M = commutator ↥M := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  have hKnormal : ((derivedInG M).subgroupOf M).Normal := by rw [hKcomm]; infer_instance
  -- every lattice element vanishes off `M′` (span induction, the property is ℤ-linear)
  have hvanish : ∀ χ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) (inducedFamily M),
      ∀ w : ↥M, w ∉ (derivedInG M).subgroupOf M → χ w = 0 := by
    intro χ hχ
    induction hχ using Submodule.span_induction with
    | mem x hx =>
        intro w hw
        obtain ⟨θ, -, hxeq⟩ := hx
        rw [hxeq]
        exact ClassFunction.induce_eq_zero_of_not_mem_normal _ hw
    | zero => intro w _; rfl
    | add x y _ _ ihx ihy =>
        intro w hw
        rw [ClassFunction.add_apply, ihx w hw, ihy w hw, add_zero]
    | smul a x _ ih =>
        intro w hw
        rw [← Int.cast_smul_eq_zsmul ℂ a x, ClassFunction.smul_apply, ih w hw, mul_zero]
  intro z hz
  rw [ClassFunction.mem_support] at hz
  have hzK : z ∈ (derivedInG M).subgroupOf M := by
    by_contra hzK
    exact hz (hvanish φ hφ z hzK)
  have hz1 : z ≠ 1 := by rintro rfl; exact hz hφ1
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  exact ⟨Subgroup.mem_subgroupOf.mp hzK,
    fun h0 => hz1 (Subtype.ext (Set.mem_singleton_iff.mp h0))⟩

open scoped FiniteInduce in
/-- **`(M′)^# ⊆ A₀(M)`**: every nonidentity element of the derived subgroup centralizes
itself (a nonidentity element of `M`), so it lies in the `A(M)`-disjunct of `typePA0` —
the same witness as `inducedFamily_sub_support`'s tail.  Composes the sharp-support
refinement back into the `A₀`-supported lattice (`extends_on_supported`). -/
theorem Hypothesis.supportInSubgroup_sharp_derived_subset_A0 [Finite G] {M : Subgroup G}
    (hyp : Hypothesis M) :
    OddOrder.Peterfalvi.S04.supportInSubgroup (sharpSubgroup (derivedInG M)) M
      ⊆ hyp.A0 := by
  intro z hz
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hz
  obtain ⟨hzM', hz1⟩ := hz
  change (z : G) ∈ typePA0 M hyp.typeP
  unfold typePA0
  rw [Set.mem_union]
  left
  exact ⟨hzM', hz1, (z : G), ⟨z.2, hz1⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

open scoped Classical FiniteInduce Pointwise in
/-- **The core-order coprimality for a nonconjugate pair** (the `coxTs`-step of Coq
`FT_Dade_support_disjoint` `part_a2`): the order of an `(M′)^#`-point of the type-`P₁` `M` is
coprime to `|S_F| = |M_σ(S)|` of any maximal `S` not conjugate to `M`.

No (8.17.a) partition is needed: the type-`P₁` structure collapses the FTcore to the σ-Hall —
`M′ = M_σ(M)` (Coq `typePfacts`, `isTypeP1_derivedInG_eq_Msigma`) — so `|a|` is a `σ(M)`-number,
and `σ(M) ∩ σ(S) = ∅` for a nonconjugate pair (BG Theorem 13.9,
`sigma_disjoint_of_nonconjugate`); both `M_σ`'s are Hall, so a common prime divisor would lie in
the empty intersection.

⚠ Stated for an arbitrary nonconjugate maximal `S`, not for the canonical `Section16MaximalPairCore`
(issue 1044 着手順 5).  Neither `S`'s type nor its cyclic data enters: the old signature carried
`data`/`hSW1`/`hSW2`/`hKstar`/`ha0` and used none of them. -/
theorem typeP_core_order_coprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M S : Subgroup G}
    (hyp : Hypothesis M) (hSmax : S ∈ maximalSubgroups G)
    (hnc : ¬ ∃ g : G, MulAut.conj g • M = S)
    {a : G} (haM' : a ∈ sharpSubgroup (derivedInG M)) :
    Nat.Coprime (orderOf a) (Nat.card (OddOrder.BG.Ch3.S10.Msigma S)) := by
  classical
  -- the type-`P₁` `M` has `M′ = M_σ(M)` (BG `typePfacts`)
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.maximal
      (Or.inr hyp.type_alt)
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    refine ⟨hP, ?_⟩
    by_contra hne
    exact not_isTypeP2_of_isTypeIII_or_IV_or_V hG hyp.maximal hyp.type_alt ⟨hP, hne⟩
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma hG hyp.maximal hP1
  -- `σ`-disjointness of the nonconjugate pair (BG Theorem 13.9)
  have hdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M) (OddOrder.BG.Ch3.S10.sigma S) :=
    OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hyp.maximal hSmax hnc
  -- a common prime would lie in `σ(M) ∩ σ(S) = ∅`
  by_contra hne
  obtain ⟨q, hqp, hqdvd⟩ := Nat.exists_prime_and_dvd hne
  have hqa : q ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma M) :=
    (hqdvd.trans (Nat.gcd_dvd_left _ _)).trans
      (Subgroup.orderOf_dvd_natCard _ (hM'σ ▸ haM'.1))
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hyp.maximal).1 q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqa, Nat.card_pos.ne'⟩)
  have hqb : q ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma S) :=
    hqdvd.trans (Nat.gcd_dvd_right _ _)
  have hqσS : q ∈ OddOrder.BG.Ch3.S10.sigma S :=
    (OddOrder.BG.Ch3.S10.Msigma_isHall hG hSmax).1 q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqb, Nat.card_pos.ne'⟩)
  exact (Set.disjoint_left.mp hdisj hqσM) hqσS

set_option linter.unusedVariables false in
open scoped Classical FiniteInduce Pointwise in
/-- **Peterfalvi (8.13.b/c4) at the canonical pair, escape-landing exclusion**: an
`(M′)^#`-point of the type-`P₁` `M` whose centralizer **escapes `M`** cannot land in a
conjugate of any type-II maximal `S`.

Coq `FTsupport_facts` (b)+(c4) + the (10.7) consumer's `notFrobM`: the escaping `A₀`-point
has a *unique* supporting maximal `N[a]` (8.13.b), here `= S^g` by `C_G(a) ≤ S^g`; and
(8.13.c4) says a type-II supporter forces `M` to be a Frobenius group with kernel `M_F` —
impossible for the type-`P₁` `M`.

Proven from **BG Theorem D(4)** (`theoremD_msigma_conjugacy_and_centralizers`): the
type-`P₁` collapse `M′ = M_σ` puts `a ∈ M_σ(M)^#`, D(4) attaches to the escaping `a` a
supporting maximal `N₀` with the package clause `IsTypeP2 N₀ → IsTypeF M ∧ …`; the given
uniqueness pins `N₀ = S^g`, a conjugate of the type-II `S`, hence type `P₂` (Proposition
16.1(b), `proposition_type_classification`); the fired clause makes `M` type `F` = type I —
contradicting type III/IV/V (`not_isTypeI_of_isTypeNonI`).

⚠ Stated for an arbitrary type-II maximal `S`, not for the canonical `Section16MaximalPairCore`
(issue 1044 着手順 5): the old signature carried `mp`/`data`/`hSW1`/`hSW2`/`hKstar`/`ha0` and used
none of them beyond `S`'s type. -/
theorem typeP_escaping_centralizer_not_le_typeII [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M S : Subgroup G}
    (hyp : Hypothesis M) (hSII : IsTypeII S)
    {a : G} (haM' : a ∈ sharpSubgroup (derivedInG M))
    (hesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M)
    {g : G} (huniq : ∀ N ∈ maximalSubgroupsContaining
      (Subgroup.centralizer ({a} : Set G)), N = MulAut.conj g • S) :
    False := by
  classical
  -- the type-`P₁` collapse puts `a` in `M_σ(M)^#`
  have hP : OddOrder.BG.Ch4.S14.IsTypeP M :=
    OddOrder.BG.Ch4.S16.isTypeP_of_isTypeNonI hG hyp.maximal (Or.inr hyp.type_alt)
  have hP1 : OddOrder.BG.Ch4.S14.IsTypeP1 M := by
    refine ⟨hP, ?_⟩
    by_contra hne
    exact not_isTypeP2_of_isTypeIII_or_IV_or_V hG hyp.maximal hyp.type_alt ⟨hP, hne⟩
  have hM'σ : derivedInG M = OddOrder.BG.Ch3.S10.Msigma M :=
    OddOrder.BG.Ch4.S16.isTypeP1_derivedInG_eq_Msigma hG hyp.maximal hP1
  have haσ : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M := by
    change a ∈ sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma M)
    rw [← hM'σ]
    exact haM'
  -- BG Theorem D(4): the unique supporting maximal with the type-`F`/`P₂` package
  obtain ⟨-, -, -, hD4⟩ :=
    OddOrder.BG.Ch4.S16.theoremD_msigma_conjugacy_and_centralizers hG hyp.maximal
  obtain ⟨R, -, N₀, hQ, -⟩ := hD4 a haσ hesc
  obtain ⟨hN₀mem, -, -, -, -, -, hP2clause⟩ := hQ
  have hN₀eq : N₀ = MulAut.conj g • S := huniq N₀ hN₀mem
  have hN₀max : N₀ ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hN₀mem).1
  -- `N₀` is a conjugate of the type-II `S`, hence type `P₂` (Proposition 16.1(b))
  have hN₀II : IsTypeII N₀ := by
    rw [hN₀eq]
    exact isTypeII_pointwise_smul (MulAut.conj g) hSII
  obtain ⟨-, hIIiff, -⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hN₀max
  -- fire the (c4)-clause: `M` is type `F` = type I — contradicting type III/IV/V
  obtain ⟨hFM, -, -⟩ := hP2clause (hIIiff.mp hN₀II)
  obtain ⟨hIiffM, -, -⟩ :=
    OddOrder.BG.Ch4.S16.proposition_type_classification hG hyp.maximal
  exact OddOrder.BG.Ch4.S16.not_isTypeI_of_isTypeNonI hG hyp.maximal
    (Or.inr hyp.type_alt) (hIiffM.mpr hFM)

open scoped Classical FiniteInduce Pointwise in
/-- **Peterfalvi (8.18.b), bare base-point disjointness at the canonical pair — the
landing analysis** (Coq `part_a2` of `FT_Dade_support_disjoint`): no `(M′)^#`-point of the
type-`P₁` `M = mp.T` is conjugate to an `A(S)`-point of the type-II member `mp.S`.

Suppose `c·a·c⁻¹ = b ∈ A(S)`.  Then `b` is a `(κ(S) ∪ σ(S))′`-element of `S`: its `σ`-part
dies by the (8.17.a) core-order coprimality (`typeP_core_order_coprime`), its
`κ`-part because `b ∈ S′` and `S′` complements the cyclic `κ(S)`-Hall `W₁`
((8.4)/`typeP_derivedInG_isComplement_kappaHall`).  The `A(S)`-witness `u ∈ M_σ(S)^#`
commutes with `b`, so BG Lemma 15.1(c) (`uniqueMaximal_of_kappaSigmaCompl_element`, the
type-generic (8.12)) pins `ℳ(C_G(b)) = {S}`.  If `C_G(a) ≤ M`, then
`C_G(b) = C_G(a)^c ≤ M^c` forces `M^c = S` — contradicting the pair's nonconjugacy
(`mp.S_T_not_conj`).  Otherwise `a` escapes `M` while `C_G(a) ≤ S^{c⁻¹}` — killed by the
(8.13.c4) exclusion (`typeP_escaping_centralizer_not_le_typeII`). -/
theorem typeP_pair_base_bare_not_isConj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (_hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (_hSW1 : data.typeP.W1 = mp.K) (_hSW2 : data.typeP.W2 = mp.Kstar)
    {a : G} (haM' : a ∈ sharpSubgroup (derivedInG M)) (_ha0 : a ∈ typePA0 M hyp.typeP)
    {b : G} (hbS : b ∈ centralizerSupport
      (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S)) (derivedInG mp.S)) :
    ¬ IsConj a b := by
  classical
  intro hconj
  have : Group.IsSolvable ↥mp.S := hG.isSolvable_of_mem_maximalSubgroups mp.S_maximal
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  obtain ⟨hbM', hb1, u, huS, hbu⟩ := hbS
  have ha1 : a ≠ 1 := fun h0 => haM'.2 (Set.mem_singleton_iff.mpr h0)
  have hbne : b ≠ 1 := fun h0 => hb1 h0
  have hordeq : orderOf b = orderOf a := by
    rw [← hc]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective a
  -- `b` is a `(κ(S) ∪ σ(S))′`-element
  have hcopMσ := typeP_core_order_coprime hG hyp mp.S_maximal
    (by
      rintro ⟨g, hg⟩
      exact mp.S_T_not_conj ⟨g⁻¹, by
        rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hT]⟩)
    haM'
  have hSP : OddOrder.BG.Ch4.S14.IsTypeP mp.S :=
    OddOrder.BG.Ch4.S14.isTypeP_of_isTypeP2 mp.S_typeP2
  have hW1hall := typePData_W1_isHallSubgroup_kappa hG mp.S_maximal hSP data.typeP
  have : IsCyclic ↥data.typeP.W1 := data.typeP.W1_cyclic
  have hcompl := OddOrder.BG.Ch4.S14.typeP_derivedInG_isComplement_kappaHall hG
    mp.S_maximal hSP data.typeP.W1_le hW1hall
  have hcardS' : Nat.card ((derivedInG mp.S).subgroupOf mp.S) = Nat.card (derivedInG mp.S) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (OddOrder.Peterfalvi.S11.derivedInG_le_self mp.S)).toEquiv
  have hyπ : OddOrder.GroupTheory.IsPiElement
      ((OddOrder.BG.Ch4.S14.kappa mp.S ∪ OddOrder.BG.Ch3.S10.sigma mp.S)ᶜ) b := by
    intro q hq
    obtain ⟨hqp, hqdvd, -⟩ := Nat.mem_primeFactors.mp hq
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    constructor
    · -- `q ∉ κ(S)`: `q ∣ |b| ∣ |S′| = index(W₁)`, and the Hall `W₁` has `κ`-free index
      intro hqκ
      have hbord : orderOf b ∣ Nat.card (derivedInG mp.S) :=
        Subgroup.orderOf_dvd_natCard _ hbM'
      have hqidx : q ∣ ((data.typeP.W1).subgroupOf mp.S).index := by
        rw [hcompl.index_eq_card, hcardS']
        exact hqdvd.trans hbord
      exact hW1hall.2 q (Nat.mem_primeFactors.mpr
        ⟨hqp, hqidx, Subgroup.index_ne_zero_of_finite⟩) hqκ
    · -- `q ∉ σ(S)`: `σ`-primes divide `|M_σ(S)|`, coprime to `|a| = |b|` by (8.17.a)
      intro hqσ
      have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG mp.S_maximal
      have hqnidx : ¬ q ∣ (OddOrder.BG.Ch3.S10.Msigma mp.S).index := fun hdvd =>
        hHall.2 q (Nat.mem_primeFactors.mpr
          ⟨hqp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hqσ
      have hqG : q ∣ Nat.card G := hqdvd.trans (orderOf_dvd_natCard b)
      have hqMσ : q ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma mp.S) := by
        rcases (Nat.Prime.dvd_mul hqp).mp
          ((Subgroup.card_mul_index (OddOrder.BG.Ch3.S10.Msigma mp.S)) ▸ hqG) with h | h
        · exact h
        · exact absurd h hqnidx
      have hgcd : q ∣ Nat.gcd (orderOf a) (Nat.card (OddOrder.BG.Ch3.S10.Msigma mp.S)) :=
        Nat.dvd_gcd (hordeq ▸ hqdvd) hqMσ
      rw [Nat.Coprime.gcd_eq_one hcopMσ] at hgcd
      exact hqp.one_lt.ne' (Nat.dvd_one.mp hgcd)
  -- the `(κ∪σ)′`-Hall of `S` (Hall E in the solvable `S`)
  obtain ⟨U', hU'⟩ := OddOrder.Isaacs.Ch03.hall_E_exists (G := ↥mp.S)
    ((OddOrder.BG.Ch4.S14.kappa mp.S ∪ OddOrder.BG.Ch3.S10.sigma mp.S)ᶜ)
  have hUeq : (U'.map mp.S.subtype).subgroupOf mp.S = U' :=
    Subgroup.comap_map_eq_self_of_injective mp.S.subtype_injective U'
  have hUhall : OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa mp.S ∪ OddOrder.BG.Ch3.S10.sigma mp.S)ᶜ)
      ((U'.map mp.S.subtype).subgroupOf mp.S) := by
    rw [hUeq]
    exact hU'
  -- BG 15.1(c): `ℳ(C_G(b)) = {S}`
  have hbmem : b ∈ mp.S := OddOrder.Peterfalvi.S11.derivedInG_le_self mp.S hbM'
  have hCne : OddOrder.BG.Ch3.S10.Msigma mp.S ⊓
      Subgroup.centralizer ({b} : Set G) ≠ ⊥ := by
    intro hbot
    have humem : u ∈ OddOrder.BG.Ch3.S10.Msigma mp.S ⊓
        Subgroup.centralizer ({b} : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨huS.1, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact Subgroup.mem_centralizer_singleton_iff.mp hbu
    rw [hbot] at humem
    exact huS.2 (Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp humem))
  have hB := OddOrder.BG.Ch4.S16.uniqueMaximal_of_kappaSigmaCompl_element hG mp.S_maximal
    (Subgroup.map_subtype_le U') hUhall hbmem hbne hyπ hCne
  -- transport: `C_G(b) = C_G(a)^c`
  have hCconj : Subgroup.centralizer ({b} : Set G)
      = MulAut.conj c • Subgroup.centralizer ({a} : Set G) := by
    rw [← hc]
    exact (OddOrder.Peterfalvi.S10.conj_smul_centralizer_singleton' c a).symm
  by_cases hCa : Subgroup.centralizer ({a} : Set G) ≤ M
  · -- `C_G(b) ≤ M^c`, so `M^c = S` — contradicting the pair's nonconjugacy
    have hMc : MulAut.conj c • M ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({b} : Set G)) := by
      rw [mem_maximalSubgroupsContaining]
      refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul
        (mem_maximalSubgroups.mp (hT ▸ mp.T_maximal)), ?_⟩
      rw [hCconj]
      exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hCa
    rw [hB, Set.mem_singleton_iff] at hMc
    exact mp.S_T_not_conj ⟨c⁻¹, by
      rw [← hMc, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul, hT]⟩
  · -- `a` escapes `M` while `C_G(a) ≤ S^{c⁻¹}` — the (8.13.c4) exclusion
    have hSmem : mp.S ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({b} : Set G)) := by
      rw [hB]
      rfl
    have hCbS : Subgroup.centralizer ({b} : Set G) ≤ mp.S :=
      (mem_maximalSubgroupsContaining.mp hSmem).2
    have huniq : ∀ N ∈ maximalSubgroupsContaining
        (Subgroup.centralizer ({a} : Set G)), N = MulAut.conj c⁻¹ • mp.S := by
      intro N hN
      rw [mem_maximalSubgroupsContaining] at hN
      have hcN : MulAut.conj c • N ∈ maximalSubgroupsContaining
          (Subgroup.centralizer ({b} : Set G)) := by
        rw [mem_maximalSubgroupsContaining]
        refine ⟨OddOrder.BG.Ch3.S12.isCoatom_conj_smul (mem_maximalSubgroups.mp hN.1), ?_⟩
        rw [hCconj]
        exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hN.2
      rw [hB, Set.mem_singleton_iff] at hcN
      rw [← hcN, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    exact typeP_escaping_centralizer_not_le_typeII hG hyp (section16_S_isTypeII hG mp)
      haM' hCa huniq

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.18.b), base-point disjointness at the canonical pair** (the
support-geometry core of Coq `oST`): no `H(a)`-thickened `A₁(M)`-point of the type-`P₁`
`M = mp.T` is conjugate to an `A(S)`-point of the type-II member `mp.S`.

**The thickening reduces to the bare case by a power trick**: `h ∈ H(a)` commutes with `a`
((2.2) `H(a) ≤ C_G(a)`) with coprime order (`|H(a)| ⊥ |C_M(a)|` and `|a| ∣ |C_M(a)|`), so
CRT provides `k` with `(a·h)^k = a`; conjugating, `a` is conjugate to `b^k`, which is again
an `A(S)`-point (powers stay in `S′` and keep the centralizer witness).  The bare case is
`typeP_pair_base_bare_not_isConj`. -/
theorem typeP_pair_base_not_isConj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    {a : G} (haM' : a ∈ sharpSubgroup (derivedInG M)) (ha0 : a ∈ typePA0 M hyp.typeP)
    {h : G} (hh : h ∈ hyp.dadeData.dade.H ⟨a, ha0⟩)
    {b : G} (hbS : b ∈ centralizerSupport
      (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S)) (derivedInG mp.S)) :
    ¬ IsConj (a * h) b := by
  classical
  -- `a` and `h` commute with coprime orders ((2.2): `H(a) ≤ C_G(a)`, `|H(a)| ⊥ |C_M(a)|`),
  -- so `a` is a *power* of `a·h` (CRT), hence of `b` after conjugation — reducing to the
  -- bare case `a ~ b^k ∈ A(S)`.
  intro hconj
  have ha1 : a ≠ 1 := fun h0 => haM'.2 (Set.mem_singleton_iff.mpr h0)
  have hHle : hyp.dadeData.dade.H ⟨a, ha0⟩ ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [hyp.dadeData.dade.centralizer_eq_sup ⟨a, ha0⟩]
    exact le_sup_left
  have hcomm : Commute a h := (Subgroup.mem_centralizer_singleton_iff.mp (hHle hh)).symm
  -- coprime orders
  have hha : orderOf h ∣ Nat.card (hyp.dadeData.dade.H ⟨a, ha0⟩) :=
    Subgroup.orderOf_dvd_natCard _ hh
  have haa : orderOf a ∣ Nat.card
      (OddOrder.Peterfalvi.S04.centralizerIn M a) :=
    Subgroup.orderOf_dvd_natCard _
      (OddOrder.Peterfalvi.S04.mem_centralizerIn.mpr
        ⟨hyp.dadeData.dade.mem_L ha0, rfl⟩)
  have hcopHC := hyp.dadeData.dade.centralizer_coprime ⟨a, ha0⟩ ⟨a, ha0⟩
  have hcop : Nat.Coprime (orderOf a) (orderOf h) :=
    (hcopHC.coprime_dvd_left hha).symm.coprime_dvd_left haa
  -- CRT: `(a·h)^k = a` for `k ≡ 1 (mod |a|)`, `k ≡ 0 (mod |h|)`
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hcop 1 0
  have hpow : (a * h) ^ k = a := by
    rw [hcomm.mul_pow]
    have h1 : a ^ k = a ^ 1 := pow_eq_pow_iff_modEq.mpr hk1
    have h2 : h ^ k = h ^ 0 := pow_eq_pow_iff_modEq.mpr hk0
    rw [h1, h2, pow_one, pow_zero, mul_one]
  -- transport along the conjugacy: `b^k` is a conjugate of `a`
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hbk : b ^ k = c * a * c⁻¹ := by
    rw [← hc, conj_pow, hpow]
  -- `b^k` is again an `A(S)`-point (a power stays in `S′` and keeps the centralizer witness)
  obtain ⟨hbM', hb1, u, huS, hbu⟩ := hbS
  have hbkS : b ^ k ∈ centralizerSupport
      (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S)) (derivedInG mp.S) := by
    refine ⟨Subgroup.pow_mem _ hbM' k, ?_, u, huS,
      Subgroup.pow_mem (Subgroup.centralizer _) hbu k⟩
    intro h0
    apply ha1
    have h1 : c * a * c⁻¹ = 1 := by rw [← hbk, h0]
    have h2 : a = c⁻¹ * (c * a * c⁻¹) * c := by group
    rw [h2, h1]
    group
  -- the bare case kills `a ~ b^k`
  exact typeP_pair_base_bare_not_isConj hG hyp hT hKstar hSW1 hSW2 haM' ha0 hbkS
    (isConj_iff.mpr ⟨c, hbk.symm⟩)

open scoped Classical FiniteInduce in
/-- **Peterfalvi (8.18.b), cross-Dade orthogonality at the canonical pair** (Coq `oST` of
`Frob_der1_type2`, `PFsection10.v:577-590`): for `φ` a `(M′)^#`-supported class function of
the type-`P₁` `M = mp.T` and `ψ` an `A(S)`-supported class function of the type-II member
`mp.S`, the two Dade images are orthogonal, `⟨φ^{τ_M}, ψ^{τ_S}⟩ = 0`.

The image supports are the **restricted** thickenings
(`IsDadeMap.exists_base_of_map_apply_ne_zero`): a nonvanishing point of `φ^{τ_M}` is
conjugate to `a·h` with `a ∈ Supp(φ) ⊆ A₁(M) = (M′)^#` and `h ∈ H(a)`, and a nonvanishing
point of `ψ^{τ_S}` is conjugate to a bare `b ∈ Supp(ψ) ⊆ A(S)` (the (8.16) TI-route has
trivial signalizers).  A common point would make `a·h ~ b` — impossible by the (8.18.b)
base-point disjointness (`typeP_pair_base_not_isConj`), so the supports are disjoint and
the inner product vanishes (`inner_eq_zero_of_disjoint_support`). -/
theorem Hypothesis.cross_dade_inner_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {φ : ClassFunction ↥M ℂ} {ψ : ClassFunction ↥mp.S ℂ}
    (hφsupp : φ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (sharpSubgroup (derivedInG M)) M)
    (hψsupp : ψ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
        (derivedInG mp.S)) mp.S) :
    ClassFunction.inner (hyp.tau φ)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau ψ)
      = 0 := by
  classical
  have hφA0 : φ.support ⊆ hyp.A0 :=
    hφsupp.trans hyp.supportInSubgroup_sharp_derived_subset_A0
  have hψA0 : ψ.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
          (derivedInG mp.S)
        ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S :=
    hψsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  refine ClassFunction.inner_eq_zero_of_disjoint_support ?_
  rw [Set.disjoint_left]
  intro g hg1 hg2
  rw [ClassFunction.mem_support] at hg1 hg2
  -- `M`-side base point: `g ~ a·h`, `a ∈ Supp(φ) ⊆ (M′)^#`, `h ∈ H(a)`
  have hg1' : (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) φ) g ≠ 0 := hg1
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    hyp.dadeData.dade _ hφA0] at hg1'
  obtain ⟨a, h, hh, hconja, hvala⟩ :=
    OddOrder.Peterfalvi.S04.IsDadeMap.exists_base_of_map_apply_ne_zero
      (hyp.dadeData.dade.isDadeMap_dadeMap (k := ℂ)) _ hg1'
  have haM' : a.1 ∈ sharpSubgroup (derivedInG M) := by
    have := hφsupp (ClassFunction.mem_support.mpr hvala)
    rwa [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at this
  -- `S`-side base point: `g ~ b·k` with `k ∈ ⊥`, so `g ~ b`, `b ∈ Supp(ψ) ⊆ A(S)`
  rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support
    (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
    _ hψA0] at hg2
  obtain ⟨b, k, hk, hconjb, hvalb⟩ :=
    OddOrder.Peterfalvi.S04.IsDadeMap.exists_base_of_map_apply_ne_zero
      ((typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).dade0.isDadeMap_dadeMap (k := ℂ)) _ hg2
  have hbS : b.1 ∈ centralizerSupport
      (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S)) (derivedInG mp.S) := by
    have := hψsupp (ClassFunction.mem_support.mpr hvalb)
    rwa [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at this
  -- the TI-route has trivial signalizers: `k = 1`
  have hk1 : k = 1 := by
    have hbot : (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp)
        data.typeP).dade0.H b = ⊥ := rfl
    rw [hbot, Subgroup.mem_bot] at hk
    exact hk
  -- combine the conjugacies: `a·h ~ g ~ b`
  exact typeP_pair_base_not_isConj hG hyp hT hKstar hSW1 hSW2 haM' a.2 hh hbS
    (hconja.trans (by rw [hk1, mul_one] at hconjb; exact hconjb.symm))

open scoped Classical FiniteInduce in
/-- **The (10.7) cross-side orthogonality `⟨ζ^{τ₁}, λ^{τ₂}⟩ = 0`** (the `zeta_lam_ortho`
production; Coq `Frob_der1_type2`'s `orthonormal_vchar_diff_ortho` step): the `M`-side
coherent image of `ζ` is orthogonal to the `S`-side coherent image of `λ`.

The conjugate-pair difference trick: `{ζ^{τ₁}, ζ̄^{τ₁}}` and `{λ^{τ₂}, λ̄^{τ₂}}` are
orthonormal pairs of virtual characters (the coherence isometries on distinct
irreducibles), the differences are the Dade images `(ζ − ζ̄)^{τ_M}` and `(λ − λ̄)^{τ_S}`
(coherence agreement on the supported lattice) — orthogonal by the (8.18.b) support
disjointness (`cross_dade_inner_eq_zero_at_pair`) and both vanishing at `1`
(`dadeIntegralCharacterMap_apply_one_eq_zero`), so the cross-orthogonality primitive
`orthonormal_vchar_diff_ortho` applies. -/
theorem Hypothesis.tau1_zeta_inner_extension_lam_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (_hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (_hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
            (derivedInG mp.S)
          ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S)) :
    ClassFunction.inner (coh.tau1 params.zeta) (c.extension lam) = 0 := by
  classical
  subst hT
  -- `M`-side pieces: `ζ`, `ζ̄`, their coherent images
  have hζS : params.zeta ∈ inducedFamily mp.T := params.zeta_mem_S
  have hζirr := params.zeta_irreducible
  have hModd : Odd (Nat.card ↥mp.T) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card mp.T)
  have hζne : params.zeta.conj ≠ params.zeta := inducedFamily_hasNoRealCharacters hModd hζS
  have hζcS : params.zeta.conj ∈ inducedFamily mp.T :=
    inducedFamily_closedUnderConjugate mp.T hζS
  have haZ : coh.tau1 params.zeta ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr _ (Submodule.subset_span hζS)
  have hbZ : coh.tau1 params.zeta.conj ∈ ZIrr G :=
    coh.coherent.extension_mem_ZIrr _ (Submodule.subset_span hζcS)
  have ha1 := hyp.zeta_tau1_inner_self hG hG.odd coh hζS hζirr
  have hb1 := hyp.zeta_tau1_inner_self hG hG.odd coh hζcS hζirr.conj
  have hab : ClassFunction.inner (coh.tau1 params.zeta) (coh.tau1 params.zeta.conj) = 0 := by
    change ClassFunction.inner (coh.coherent.extension _) (coh.coherent.extension _) = 0
    rw [coh.coherent.extension_inner_eq _ _ (Submodule.subset_span hζS)
        (Submodule.subset_span hζcS),
      OddOrder.RepresentationTheory.irr_cf_inner hζirr hζirr.conj,
      if_neg (fun h => hζne h.symm)]
  -- `S`-side pieces: `λ`, `λ̄`, their coherent images (as in the (5.5) span lemma)
  have hSmodd : Odd (Nat.card ↥mp.S) :=
    hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card mp.S)
  have hlamIKF := typeII_sOf_subset_inducedKernelFamily data Y hlam_mem
  have hr : ¬ ClassFunction.IsReal lam :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters hSmodd
      (Y.subgroupOf mp.S) hlamIKF
  have hlamne : lam ≠ lam.conj := fun h => hr h.symm
  have hlam_zspan : lam ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hlamc_zspan : lam.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have hcZ : c.extension lam ∈ ZIrr G := c.extension_mem_ZIrr _ hlam_zspan
  have hdZ : c.extension lam.conj ∈ ZIrr G := c.extension_mem_ZIrr _ hlamc_zspan
  have hc1 : ClassFunction.inner (c.extension lam) (c.extension lam) = 1 := by
    rw [c.extension_inner_eq _ _ hlam_zspan hlam_zspan]
    exact hlam_irr.inner_self_eq_one
  have hd1 : ClassFunction.inner (c.extension lam.conj) (c.extension lam.conj) = 1 := by
    rw [c.extension_inner_eq _ _ hlamc_zspan hlamc_zspan]
    exact hlam_irr.conj.inner_self_eq_one
  have hcd : ClassFunction.inner (c.extension lam) (c.extension lam.conj) = 0 := by
    rw [c.extension_inner_eq _ _ hlam_zspan hlamc_zspan,
      OddOrder.RepresentationTheory.irr_cf_inner hlam_irr hlam_irr.conj,
      if_neg (fun h => hlamne h)]
  -- supports of the two differences
  have hsupp : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
        (derivedInG mp.S)) mp.S := by
    have hmem := typeII_T2_member_support hG mp.S_maximal (section16_S_isTypeII hG mp) data
      hlam_mem hlam_mem
    refine diff_support_subset_of_support_subset_union_one
      (hmem lam (by simp)) (hmem lam.conj (by simp)) ?_
    obtain ⟨n, -, hn⟩ := typeII_sOf_apply_one_eq_pos_natCast data hlam_mem
    rw [ClassFunction.conj_apply, hn, star_natCast]
  have hsuppA0 : (lam - lam.conj).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
          (derivedInG mp.S)
        ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S :=
    hsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  have hζ1conj : params.zeta.conj 1 = params.zeta 1 := by
    obtain ⟨nn, -, hn, -⟩ := hζirr.exists_natDegree_charValue_one_dvd_card
    simp only [ClassFunction.conj_apply, hn, star_natCast]
  have hφsupp : (params.zeta - params.zeta.conj).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
        (sharpSubgroup (derivedInG mp.T)) mp.T :=
    hyp.mem_zSpan_inducedFamily_support_sharp_derived
      (Submodule.sub_mem _ (Submodule.subset_span hζS) (Submodule.subset_span hζcS))
      (by rw [ClassFunction.sub_apply, hζ1conj, sub_self])
  -- the two difference identities: coherent images = Dade images
  have hMdiff : coh.tau1 params.zeta - coh.tau1 params.zeta.conj
      = hyp.tau (params.zeta - params.zeta.conj) :=
    (hyp.tau_zeta_sub_conj_eq_tau1 hG hG.odd coh hζS hζirr).symm
  have hSdiff : c.extension lam - c.extension lam.conj
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau
        (lam - lam.conj) := by
    rw [← c.extends_on_supported _
      ⟨Submodule.sub_mem _ hlam_zspan hlamc_zspan, hsuppA0⟩, map_sub]
  -- (8.18.b): the differences are orthogonal
  have hdiff : ClassFunction.inner
      (coh.tau1 params.zeta - coh.tau1 params.zeta.conj)
      (c.extension lam - c.extension lam.conj) = 0 := by
    rw [hMdiff, hSdiff]
    exact hyp.cross_dade_inner_eq_zero_at_pair hG rfl hKstar hSW1 hSW2 hφsupp hsupp
  -- both differences vanish at `1`
  have hab1 : (coh.tau1 params.zeta) 1 = (coh.tau1 params.zeta.conj) 1 := by
    have hz : (coh.tau1 params.zeta - coh.tau1 params.zeta.conj) (1 : G) = 0 := by
      rw [hMdiff]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        hyp.dadeData.dade (hyp.zeta_sub_conj_support hG hG.odd hζS hζirr)
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  have hcd1 : (c.extension lam) 1 = (c.extension lam.conj) 1 := by
    have hz : (c.extension lam - c.extension lam.conj) (1 : G) = 0 := by
      rw [hSdiff]
      exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_one_eq_zero
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0 hsuppA0
    rw [ClassFunction.sub_apply] at hz
    exact sub_eq_zero.mp hz
  exact orthonormal_vchar_diff_ortho haZ hbZ hcZ hdZ ha1 hb1 hc1 hd1 hab hcd hdiff hab1 hcd1

open scoped Classical FiniteInduce in
/-- **The (10.7) `cross_zero` production** (Coq `Frob_der1_type2`'s
`'[alpha^\tau, beta^{tau2}] = 0` step): for a nontrivial column `s`, the `τ₁`-image of
`α = μ_s − d·ζ` is orthogonal to `ν^{τ₂} − λ^{τ₂}`.

Both sides are Dade images of supported lattice elements: `μ_s = ∑_i μ_{is} ∈ 𝒮`
(`muGrid_column_sum_mem_inducedFamily`) and `ζ ∈ 𝒮` with `α(1) = w₁·d − d·w₁ = 0`
((10.3) degree independence and `ζ(1) = w₁`), so `α` is `(M′)^#`-supported
(`mem_zSpan_inducedFamily_support_sharp_derived`) and `τ₁α = α^{τ_M}`
(`extends_on_supported` through `(M′)^# ⊆ A₀`); `ν − λ` is `A(S)`-supported with
`τ₂(ν − λ) = (ν − λ)^{τ_S}`.  The (8.18.b) support disjointness
(`cross_dade_inner_eq_zero_at_pair`) kills the cross inner product. -/
theorem Hypothesis.tau1_muColumn_sub_zeta_inner_extension_diff_eq_zero_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : Hypothesis M) {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {params : CharacterParameters hyp} (coh : CoherentHypothesis hyp params)
    (hζ1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hμd : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hG.odd i j 1 = (params.d : ℂ))
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (_hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hdeg : lam 1 = nu 1)
    (c : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ))
      (OddOrder.Peterfalvi.S04.supportInSubgroup
        (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
            (derivedInG mp.S)
          ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S))
    (s : Fin hyp.w2) (hs : s ≠ 0) :
    ClassFunction.inner
      (coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
        - (params.d : ℂ) • params.zeta))
      (c.extension nu - c.extension lam) = 0 := by
  classical
  subst hT
  -- `M`-side: `α = μ_s − d·ζ` is a `1`-vanishing lattice element, `(M′)^#`-supported
  have hd01 : hyp.muGrid hG hG.odd 0 s 1 ≠ 1 := by
    rw [hμd 0 s hs]
    intro h
    have hd : params.d = 1 := by exact_mod_cast h
    have := params.d_gt_one
    omega
  have hμS : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s) ∈ inducedFamily mp.T :=
    hyp.muGrid_column_sum_mem_inducedFamily hG hG.odd s hd01
  have hdsmul : (params.d : ℂ) • params.zeta = (params.d : ℤ) • params.zeta := by
    rw [← Int.cast_smul_eq_zsmul ℂ (params.d : ℤ) params.zeta]
    norm_num
  have hαspan : (∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta
      ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.T) (inducedFamily mp.T) := by
    refine Submodule.sub_mem _ (Submodule.subset_span hμS) ?_
    rw [hdsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span params.zeta_mem_S)
  have hα1 : ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta) 1 = 0 := by
    rw [ClassFunction.sub_apply, ClassFunction.smul_apply, hζ1,
      ClassFunction.finset_sum_apply,
      Finset.sum_congr rfl (fun i _ => hμd i s hs),
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hαsharp := hyp.mem_zSpan_inducedFamily_support_sharp_derived hαspan hα1
  have hM : coh.tau1 ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
      - (params.d : ℂ) • params.zeta)
      = hyp.tau ((∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i s)
        - (params.d : ℂ) • params.zeta) :=
    coh.coherent.extends_on_supported _
      ⟨hαspan, hαsharp.trans hyp.supportInSubgroup_sharp_derived_subset_A0⟩
  -- `S`-side: `ν − λ` is `A(S)`-supported
  have hψsupp : (nu - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
        (derivedInG mp.S)) mp.S := by
    have hmem := typeII_T2_member_support hG mp.S_maximal (section16_S_isTypeII hG mp) data
      hlam_mem hnu_mem
    exact diff_support_subset_of_support_subset_union_one
      (hmem nu (by simp)) (hmem lam (by simp)) hdeg.symm
  have hψA0 : (nu - lam).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
      (centralizerSupport (sharpSubgroup (OddOrder.BG.Ch3.S10.Msigma mp.S))
          (derivedInG mp.S)
        ∪ conjClassSetIn mp.S (typePV mp.S data.typeP)) mp.S :=
    hψsupp.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono Set.subset_union_left)
  have hnu_zspan : nu ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  have hlam_zspan : lam ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥mp.S)
      ({lam, lam.conj, nu, nu.conj} : Set (ClassFunction ↥mp.S ℂ)) :=
    Submodule.subset_span (Set.mem_insert _ _)
  have hS : c.extension nu - c.extension lam
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).dade0
        (typeIIHypothesis46 hG mp.S_maximal (section16_S_isTypeII hG mp) data.typeP).tau
        (nu - lam) := by
    rw [← c.extends_on_supported _ ⟨Submodule.sub_mem _ hnu_zspan hlam_zspan, hψA0⟩, map_sub]
  rw [hM, hS]
  exact hyp.cross_dade_inner_eq_zero_at_pair hG rfl hKstar hSW1 hSW2 hαsharp hψsupp

set_option linter.unusedVariables false in
open scoped Classical FiniteInduce in
/-- **The (10.7) cross-isometry package at the canonical pair** (Coq `Frob_der1_type2`,
production step): for the `M`-seeded pair (`T = M`, `Kstar = hyp.typeP.W1`) and a
`(K, K*)`-reconciled §9 setup on the type-II member `mp.S`, the package exists with the
grid fields **honestly produced**: `tau2` is the (5.7) `T2`-coherent extension
(`typeII_T2_coherent`), and `nu_tau2_eq` is the (5.8) row pin
(`exists_nu_extension_eq_alignedRow_at_pair`).

The four support-geometry fields ((5.3.b) grid orthogonality and the (8.18.b)
cross-support vanishing) are the obligation-3 content, all discharged in this file
(see the module docstring). -/
theorem exists_typeIICrossIsometryData_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    (hζ1 : params.zeta 1 = (hyp.w1 : ℂ))
    (hμd : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hG.odd i j 1 = (params.d : ℂ))
    {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar)
    [NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1)]
    {Y : Subgroup G} {lam nu : ClassFunction ↥mp.S ℂ}
    (hlam_mem : lam ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hlam_irr : IsIrreducibleCharacter lam)
    (hnu_mem : nu ∈ OddOrder.Peterfalvi.S11.sOf data Y)
    (hnu_red : ¬ IsIrreducibleCharacter nu)
    (hdeg : lam 1 = nu 1) :
    Nonempty (TypeIICrossIsometryData hG coh lam nu) := by
  classical
  -- the (5.7) `T2`-coherence on `mp.S`
  obtain ⟨c⟩ := typeII_T2_coherent hG mp.S_maximal (section16_S_isTypeII hG mp) data
    hlam_mem hlam_irr hnu_mem hnu_red hdeg
  -- the (5.8) row pin (the assembled grid transpose)
  obtain ⟨r', delta', hpm, hrow⟩ := hyp.exists_nu_extension_eq_alignedRow_at_pair hG
    hT hKstar hSW1 hSW2 hlam_mem hlam_irr hnu_mem hnu_red hdeg c
  exact ⟨{ tau2 := c.extension
           r' := r'
           delta' := delta'
           delta'_pm := hpm
           nu_tau2_eq := hrow
           lam_ortho_grid := fun i j =>
             hyp.extension_lam_inner_alignedGrid_eq_zero_at_pair hG hT hKstar hSW1 hSW2
               hlam_mem hlam_irr hnu_mem hdeg c i j
           zeta_ortho_grid := fun i j =>
             hyp.tau1_zeta_inner_alignedGrid_eq_zero hG hG.odd coh params.zeta_mem_S
               params.zeta_irreducible i j
           zeta_lam_ortho :=
             hyp.tau1_zeta_inner_extension_lam_eq_zero_at_pair hG hT hKstar hSW1 hSW2
               coh hlam_mem hlam_irr hnu_mem hdeg c
           cross_zero := fun s hs =>
             hyp.tau1_muColumn_sub_zeta_inner_extension_diff_eq_zero_at_pair hG hT hKstar
               hSW1 hSW2 coh hζ1 hμd hlam_mem hlam_irr hnu_mem hdeg c s hs }⟩

open scoped Classical FiniteInduce in
/-- **Peterfalvi (10.7) at the canonical pair member** (Coq `Frob_der1_type2`, assembled):
under Hypothesis (10.4) for `M`, the `(K, K*)`-reconciled Types-II/III/IV setup on the
pair's type-II member `mp.S` has `[S,S] = S_F ⋊ U` Frobenius with kernel `S_F`.

The dichotomy assembly of the retired `typeII_HU_frobenius_of_coherent_aux`, with its sorried gate
replaced by the **honest pair-witness producer** (`exists_typeIICrossIsometryData_at_pair`,
axiom-clean): the §9 Clifford dichotomy's contradiction branches (Case A and the
non-exceptional Case B) produce an equal-degree irreducible/reducible pair in `𝒮(H₀)`,
whose (10.7) cross-isometry package is contradictory (`TypeIICrossIsometryData.elim`
against the (10.2)/(10.3) canonical parameters, `exists_charParameters_full`); the
exceptional Case B yields the Frobenius structure directly (Peterfalvi (9.10)). -/
theorem typeII_HU_frobenius_of_coherent_at_pair [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {mp : Section16MaximalPairCore G}
    (hT : mp.T = M) (hKstar : mp.Kstar = hyp.typeP.W1)
    {data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup mp.S}
    (hSW1 : data.typeP.W1 = mp.K) (hSW2 : data.typeP.W2 = mp.Kstar) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG mp.S)
      (data.typeP.H.subgroupOf (derivedInG mp.S))
      (data.typeP.U.subgroupOf (derivedInG mp.S)) := by
  have := hyp.finiteG
  classical
  have : NeZero (Nat.card (typeIIHypothesis46 hG mp.S_maximal
      (section16_S_isTypeII hG mp) data.typeP).W1) := ⟨Nat.card_pos.ne'⟩
  -- the (10.3) canonical parameters carrying the grid/`ζ` pins
  obtain ⟨params', hmu, hos, hzS, hz1, hzconj, hδpm, hδj⟩ := hyp.exists_charParameters_full hG
  let coh' : CoherentHypothesis hyp params' := ⟨coh.coherent⟩
  have hμd : ∀ (i : Fin hyp.w1) (j : Fin hyp.w2), j ≠ 0 →
      hyp.muGrid hG hG.odd i j 1 = (params'.d : ℂ) := fun i j hj => by
    rw [← hmu]
    exact params'.degree_independent i j hj
  obtain ⟨chief, -⟩ := OddOrder.Peterfalvi.S11.exists_chiefFactorData hG data
  -- §9 character data (only the genuine `u`/`u_eq` pair is consumed by the counts)
  let chars : OddOrder.Peterfalvi.S11.Section11CharacterData data chief :=
    { u := Nat.card ↥(((OddOrder.Isaacs.Ch03.IsAInvariant.quotientMulAutHom
          (N := chief.N) chief.N_aInvariant).comp
          (data.typeP.U.subgroupOf (data.typeP.U ⊔ data.typeP.W1)).subtype).range)
      u_eq_card_quotient := rfl
      H0CprimeSupport := ∅
      tau := 0
      quotientSemidirectFrobenius := True }
  -- the reducible `ν ∈ 𝒮(H₀)`: the (9.8.a)/(9.9.b) count `p − 1 ≥ 1`
  have hred_ne : {φ ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0 |
      ¬ IsIrreducibleCharacter φ}.Nonempty := by
    apply Set.nonempty_of_ncard_ne_zero
    rw [OddOrder.Peterfalvi.S11.reducible_count_sOf_H0 hG chief]
    have := chief.p_prime.two_le
    omega
  obtain ⟨nu, hnu_mem, hnu_red⟩ := hred_ne
  -- the left-branch refutation, now through the honest pair-witness producer
  have hleft : ∀ lam : ClassFunction ↥mp.S ℂ,
      lam ∈ OddOrder.Peterfalvi.S11.sOf data chief.H0 → IsIrreducibleCharacter lam →
      lam 1 = nu 1 → False := fun lam hlam_mem hlam_irr hdeg =>
    (exists_typeIICrossIsometryData_at_pair hG coh' hz1 hμd hT hKstar hSW1 hSW2
      hlam_mem hlam_irr hnu_mem hnu_red hdeg).elim fun pkg =>
      pkg.elim hG hmu hos hzS hz1 hzconj hδpm hδj
  -- Split on the exceptional condition first: in the exceptional case (9.10) now selects the
  -- Clifford branch itself (`..._of_trigger`), so no case carrier is needed here.
  by_cases hex : ∃ χ ∈ chars.SOf (chief.H0 ⊔ chars.Cprime),
      IsIrreducibleCharacter χ ∧ χ 1 = ((data.q * chars.u : ℕ) : ℂ)
  · -- non-exceptional: the degree-`q·u` irreducible exists — contradiction.  The reducible
    -- degree fact for `nu` is the one place the (9.7) dichotomy is still needed.
    exfalso
    rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG chars with hA | hB
    · obtain ⟨caseA⟩ := hA
      obtain ⟨-, hbred, ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩, -⟩ :=
        OddOrder.Peterfalvi.S11.caseA_character_counts hG chars caseA
      have hnu_deg := (hbred nu hnu_mem hnu_red).1
      exact hleft lam
        (OddOrder.Peterfalvi.S11.sOf_antitone data le_sup_left hlam_mem)
        hlam_irr (by rw [hlam_deg, hnu_deg])
    · obtain ⟨caseB⟩ := hB
      obtain ⟨lam, hlam_mem, hlam_irr, hlam_deg⟩ := hex
      obtain ⟨-, -, hbred, -⟩ :=
        OddOrder.Peterfalvi.S11.caseB_character_counts hG chars caseB
      have hnu_deg := (hbred nu hnu_mem hnu_red).1
      exact hleft lam
        (OddOrder.Peterfalvi.S11.sOf_antitone data le_sup_left hlam_mem)
        hlam_irr (by rw [hlam_deg, hnu_deg])
  · -- exceptional: (9.10) gives the `H ⊔ U` Frobenius on the `derivedInG mp.S` carrier
    have hfrobHU := (OddOrder.Peterfalvi.S11.exceptional_case_frobenius_realization_of_trigger
      hG chars hex).2.2.2 (section16_S_isTypeII hG mp)
    have hM'eq : derivedInG mp.S = data.typeP.H ⊔ data.typeP.U := by
      rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]
    rw [hM'eq]
    exact hfrobHU

open scoped Classical FiniteInduce Pointwise in
/-- **Peterfalvi (10.7)** (setup form, pair-witness route; Coq `Frob_der1_type2`): under
Hypothesis (10.4) for `M`, every Type-II maximal `S` with a Types-II/III/IV setup has
`[S,S] = S_F ⋊ U` Frobenius with kernel `S_F`, on the given datum's factors.

The honest replacement of `typeII_HU_frobenius_of_coherent_aux` (whose left branch cited
the sorried gate `exists_typeIICrossIsometryData`): the WLOG engine
`exists_reconciled_conj_typePData_S` transports the datum onto the canonical pair member
`mp.S` with `H`/`U` carried along as conjugates; the pair-member theorem
`typeII_HU_frobenius_of_coherent_at_pair` (fully proven) gives the Frobenius structure
there; and `IsFrobeniusGroup.mapEquiv` along the inverse conjugation returns it on the
original factors verbatim. -/
theorem typeII_HU_frobenius_of_coherent' [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    {hyp : Hypothesis M} {params : CharacterParameters hyp}
    (coh : CoherentHypothesis hyp params)
    {S : Subgroup G} (data : OddOrder.Peterfalvi.S11.TypesIIIIIIVSetup S)
    (hSII : IsTypeII S) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG S)
      (data.typeP.H.subgroupOf (derivedInG S))
      (data.typeP.U.subgroupOf (derivedInG S)) := by
  have := hyp.finiteG
  classical
  -- WLOG: transport the datum onto the canonical pair member, `H`/`U` tracked
  obtain ⟨mp, u, dataS, hT, hKstar, huS, hSW1, hSW2, hH, hU⟩ :=
    exists_reconciled_conj_typePData_S hG hyp data.maximal hSII data.typeP
  obtain ⟨dII⟩ := section16_S_isTypeII hG mp
  -- (10.7) at the pair member, on the reconciled setup
  have hfrob := typeII_HU_frobenius_of_coherent_at_pair hG coh hT hKstar
    (data := { maximal := mp.S_maximal
               typeP := dataS
               nontrivial := dII.common.transfer dataS
               type_alt := Or.inl (section16_S_isTypeII hG mp) }) hSW1 hSW2
  have hfrob2 : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG mp.S)
      ((MulAut.conj u • data.typeP.H).subgroupOf (derivedInG mp.S))
      ((MulAut.conj u • data.typeP.U).subgroupOf (derivedInG mp.S)) := by
    rw [← hH, ← hU]
    exact hfrob
  -- the two factors sit inside `[S,S]`
  have hM'eq : derivedInG S = data.typeP.H ⊔ data.typeP.U := by
    rw [data.typeP.derivedInG_eq_fitting_sup_U, ← data.typeP.H_eq]
  have hHle : data.typeP.H ≤ derivedInG S := by rw [hM'eq]; exact le_sup_left
  have hUle : data.typeP.U ≤ derivedInG S := by rw [hM'eq]; exact le_sup_right
  -- the conjugation isomorphism `[S,S] ≃* [mp.S, mp.S]`
  have hD : (derivedInG S).map (MulAut.conj u).toMonoidHom = derivedInG mp.S := by
    have h1 : MulAut.conj u • derivedInG S = derivedInG mp.S := by
      rw [derivedInG_pointwise_smul, huS]
    rw [← h1]
    rfl
  set e : ↥(derivedInG S) ≃* ↥(derivedInG mp.S) :=
    ((MulAut.conj u).subgroupMap (derivedInG S)).trans
      (MulEquiv.subgroupCongr hD) with he
  -- carrier bridge: `map e.symm ((u • X).subgroupOf [mp.S,mp.S]) = X.subgroupOf [S,S]`
  have hbridge : ∀ X : Subgroup G,
      ((MulAut.conj u • X).subgroupOf (derivedInG mp.S)).map e.symm.toMonoidHom
        = X.subgroupOf (derivedInG S) := by
    intro X
    have hcoe : ∀ z : ↥(derivedInG S), ((e z : ↥(derivedInG mp.S)) : G)
        = u * (z : G) * u⁻¹ := fun z => rfl
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨w, hw, rfl⟩
      change ((e.symm w : ↥(derivedInG S)) : G) ∈ X
      have hz : ((e.symm w : ↥(derivedInG S)) : G)
          = u⁻¹ * ((w : ↥(derivedInG mp.S)) : G) * u := by
        have := hcoe (e.symm w)
        rw [MulEquiv.apply_symm_apply] at this
        have h2 := congrArg (fun x => u⁻¹ * x * u) this
        simpa [mul_assoc] using h2.symm
      rw [hz]
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hw
      have hinv : (MulAut.conj u)⁻¹ • ((w : ↥(derivedInG mp.S)) : G)
          = u⁻¹ * ((w : ↥(derivedInG mp.S)) : G) * u := by
        rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv]
      rwa [hinv] at hw
    · intro hz
      refine ⟨e z, ?_, by simp⟩
      show ((e z : ↥(derivedInG mp.S)) : G) ∈ MulAut.conj u • X
      rw [hcoe z]
      have : u * (z : G) * u⁻¹ = (MulAut.conj u) • (z : G) := by
        rw [MulAut.smul_def, MulAut.conj_apply]
      rw [this]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hz
  -- transport back
  have hfrob' := hfrob2.mapEquiv e.symm
  rw [hbridge data.typeP.H, hbridge data.typeP.U] at hfrob'
  exact hfrob'

end OddOrder.Peterfalvi.S12


