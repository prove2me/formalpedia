-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_WitnessSylowBasic
-- name    : OddOrder_Peterfalvi_S14_MaximalI_WitnessSylowBasic
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:40:17.583686+00:00
-- url     : https://prove2.me/theorems/fe226072-3e73-4f69-9a1d-123c0c50c144
-- title:
--   Peterfalvi §14: witness Sylow cyclic, opening layer
-- statement:
--   The opening layer of the witness Sylow-cyclic development: the prime set $\pi$ of Peterfalvi (12.8), the minimal counterexample hypothesis, and the rank-two witness of (12.9).
--
--   Main declarations: `InPi` (Peterfalvi (12.8), the prime set `π`); `CounterexampleHypothesis` (Peterfalvi (12.8)); `RankTwoWitnessData` (The rank-two witness extracted in Peterfalvi (12.9), with all fields stated faithfully); `exists_ne_one_actionFixedBy_not_le_commutator` (Group-theoretic core of Peterfalvi (12.9)).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/WitnessSylowBasic.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/WitnessSylowBasic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_CentralizerContainment
import Definitions.Def_OddOrder_Peterfalvi_S13_NonGaloisExclusion

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Peterfalvi (12.8), the prime set `π`**: `q ∈ π` when some type-`I` maximal subgroup `M'`
has a **noncyclic Sylow `q`-subgroup in `M' / M'_F`**.  Encoded by a Sylow `q`-subgroup `P ≤ M'`
(`q`-group with `q ∤ [M' : P]`) that is noncyclic and satisfies `q ∣ [M' : M'_F]` — so `P` is not
contained in `M'_F` and its image in `M'/M'_F` is a noncyclic Sylow `q`-subgroup. -/
def InPi (q : ℕ) : Prop :=
  ∃ M' : Subgroup G, M' ∈ maximalSubgroups G ∧ IsTypeI M' ∧
    ∃ P : Subgroup G, P ≤ M' ∧ IsPGroup q ↥P ∧ ¬ q ∣ P.relIndex M' ∧
      ¬ IsCyclic ↥P ∧ q ∣ (maxNilpotentNormalHall M').relIndex M'

/-- **Peterfalvi (12.7), the `π = ∅` case** (the first sentence of the proof of (12.16)): if the
prime set `π` of (12.8) is empty, every type-I maximal `M` is a Frobenius group with kernel `M_F`.

`M_F = H` is a normal Hall subgroup (8.11), so its complement `U` has `|U| = [M : M_F]` coprime
to `|M_F|`; hence every Sylow `q`-subgroup `P` of `U` has full `q`-order in `M`.  Were `P`
noncyclic, its `M`-image `P.map U.subtype` would be a noncyclic Sylow `q`-subgroup of `M` with
`q ∣ [M : M_F]`, i.e. `q ∈ π` — contradicting `π = ∅`.  So `U` is a Z-group and the bridge
`typeI_frobenius_of_isZGroup_complement` applies.  Its only gap is the (8.11) Hall input. -/
theorem typeI_frobenius_of_pi_empty [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hpi : ∀ q : ℕ, q.Prime → ¬ InPi (G := G) q)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥M (data.typeF.H.subgroupOf M)
      (data.typeF.U.subgroupOf M) := by
  classical
  refine typeI_frobenius_of_isZGroup_complement data ?_
  set H := data.typeF.H with hHdef
  set U := data.typeF.U with hUdef
  have hUM : U ≤ M := data.typeF.U_le
  -- `[M : H] = |U|` (complement) and `|M| = |H| * |U|`.
  have hrel : H.relIndex M = Nat.card ↥U := by
    rw [Subgroup.relIndex, data.typeF.complement.symm.index_eq_card,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv]
  have hMcard : Nat.card ↥M = Nat.card ↥H * Nat.card ↥U := by
    rw [← (H.subgroupOf M).card_mul_index,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeF.H_le).toEquiv,
      ← Subgroup.relIndex, hrel]
  -- `H = M_F` is Hall in `G` (8.11), so `|H|` is coprime to `[M : H] = |U|`.
  have hHall := (OddOrder.Peterfalvi.S10.hall_maxNilpotentNormalHall_and_mainSubgroup hG hM
    (tau := PeterfalviType.I) ⟨data⟩).1
  rw [← data.typeF.H_eq] at hHall
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card ↥U) :=
    hHall.coprime_index.coprime_dvd_right
      (hrel ▸ Subgroup.relIndex_dvd_index_of_le data.typeF.H_le)
  -- Every Sylow `q`-subgroup `P` of `U` is cyclic.
  refine ⟨fun q hq P => ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  by_contra hnc
  -- `P ≠ ⊥`, so `q ∣ |U|`, and `|H|` has no `q`.
  have hPcard : Nat.card ↥(P : Subgroup ↥U) = q ^ (Nat.card ↥U).factorization q :=
    P.card_eq_multiplicity
  have hPne : (P : Subgroup ↥U) ≠ ⊥ := fun h => hnc (h ▸ inferInstance)
  have hfacU_pos : 0 < (Nat.card ↥U).factorization q := by
    rcases Nat.eq_zero_or_pos ((Nat.card ↥U).factorization q) with h0 | h
    · exact absurd (Subgroup.card_eq_one.mp (by rw [hPcard, h0, pow_zero])) hPne
    · exact h
  have hqU : q ∣ Nat.card ↥U := Nat.dvd_of_factorization_pos hfacU_pos.ne'
  have hHfac0 : (Nat.card ↥H).factorization q = 0 :=
    Nat.factorization_eq_zero_of_not_dvd
      (hq.coprime_iff_not_dvd.mp (hcop.coprime_dvd_right hqU).symm)
  have hMfac : (Nat.card ↥M).factorization q = (Nat.card ↥U).factorization q := by
    rw [hMcard, Nat.factorization_mul (Nat.card_pos (α := ↥H)).ne'
      (Nat.card_pos (α := ↥U)).ne', Finsupp.add_apply, hHfac0, zero_add]
  -- `Pm = P.map U.subtype`: a noncyclic `q`-subgroup of `M` of full `q`-order.
  set Pm := (P : Subgroup ↥U).map U.subtype with hPmdef
  have hPmM : Pm ≤ M := (Subgroup.map_subtype_le _).trans hUM
  have hPmcard : Nat.card ↥Pm = q ^ (Nat.card ↥M).factorization q := by
    rw [hPmdef, Subgroup.card_map_of_injective U.subtype_injective, hPcard, hMfac]
  have hPmsub : Nat.card ↥(Pm.subgroupOf M) = q ^ (Nat.card ↥M).factorization q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPmM).toEquiv, hPmcard]
  have hPmP : IsPGroup q ↥Pm := (IsPGroup.iff_card).mpr ⟨_, hPmcard⟩
  refine hpi q hq ⟨M, hM, ⟨data⟩, Pm, hPmM, hPmP, ?_, ?_, ?_⟩
  · -- `¬ q ∣ Pm.relIndex M`: `Pm` has the full `q`-part of `|M|`.
    rw [Subgroup.relIndex]
    intro hdvd
    have hsplit : (Nat.card ↥M).factorization q
        = (Nat.card ↥(Pm.subgroupOf M)).factorization q
          + ((Pm.subgroupOf M).index).factorization q := by
      conv_lhs => rw [← (Pm.subgroupOf M).card_mul_index]
      rw [Nat.factorization_mul (Nat.card_pos (α := ↥(Pm.subgroupOf M))).ne'
        Subgroup.index_ne_zero_of_finite, Finsupp.add_apply]
    rw [hPmsub, hq.factorization_pow, Finsupp.single_eq_same] at hsplit
    exact absurd (Nat.Prime.factorization_pos_of_dvd hq Subgroup.index_ne_zero_of_finite hdvd)
      (by omega)
  · -- `¬ IsCyclic ↥Pm`: `Pm ≃* P` and `P` is noncyclic.
    intro hc
    have := hc
    exact hnc (isCyclic_of_surjective
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype
          U.subtype_injective).symm.toMonoidHom
      (Subgroup.equivMapOfInjective (P : Subgroup ↥U) U.subtype
          U.subtype_injective).symm.surjective)
  · -- `q ∣ (maxNilpotentNormalHall M).relIndex M = [M : H] = |U|`.
    rw [← data.typeF.H_eq, hrel]; exact hqU

/-- **Peterfalvi (12.8)**: the minimal counterexample hypothesis for (12.7).

`M` is a type-`I` maximal subgroup whose Fitting kernel is `K = M_F` (`K' = [K, K]`), and `P₀`
is a Sylow `p`-subgroup of `M` that is noncyclic with `p ∣ [M : M_F]` (so the image of `P₀` in
`M/M_F` is a noncyclic Sylow `p`-subgroup, i.e. `p ∈ π`); `p` is the smallest element of `π`. -/
structure CounterexampleHypothesis where
  p : ℕ
  p_prime : p.Prime
  M : Subgroup G
  K : Subgroup G
  Kprime : Subgroup G
  P0 : Subgroup G
  M_maximal : M ∈ maximalSubgroups G
  M_typeI : IsTypeI M
  K_eq_MF : K = maxNilpotentNormalHall M
  Kprime_eq : Kprime = derivedInG K
  P0_le_M : P0 ≤ M
  /-- `P₀` is a `p`-group… -/
  P0_pGroup : IsPGroup p ↥P0
  /-- …and a Sylow `p`-subgroup of `M` (`p ∤ [M : P₀]`). -/
  P0_sylow : ¬ p ∣ P0.relIndex M
  /-- The Sylow `p`-subgroup of `M/M_F` is noncyclic (so `P₀` is noncyclic). -/
  P0_noncyclic : ¬ IsCyclic ↥P0
  /-- …and `p ∣ [M : M_F]` (so `P₀ ⊄ M_F`; together with the Hall property this gives `p ∤ |M_F|`).
  -/
  p_dvd_index : p ∣ K.relIndex M
  /-- `p` is the smallest prime in `π`. -/
  minimal_p : ∀ q : ℕ, q.Prime → InPi (G := G) q → p ≤ q

/-- **Peterfalvi (12.8), existence of the minimal counterexample.**  If the prime set `π` of
(12.8) is nonempty, its least element `p = Nat.find` yields a `CounterexampleHypothesis`: the
`InPi` witness for `p` supplies a type-`I` maximal `M'` with a noncyclic Sylow `p`-subgroup `P₀`
that has `p ∣ [M' : M'_F]`, and `Nat.find_min'` records that `p` is the smallest prime in `π`.

This is the well-ordering step that opens the minimal-counterexample analysis of (12.7); it is
`§8`-free and unconditional (its only input is `InPi` for some prime). -/
theorem exists_counterexampleHypothesis [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (h : ∃ q : ℕ, q.Prime ∧ InPi (G := G) q) :
    Nonempty (CounterexampleHypothesis (G := G)) := by
  classical
  obtain ⟨hp_prime, M', hM', hM'I, P, hPle, hPpg, hPsyl, hPnc, hqdvd⟩ := Nat.find_spec h
  exact ⟨{
    p := Nat.find h
    p_prime := hp_prime
    M := M'
    K := maxNilpotentNormalHall M'
    Kprime := derivedInG (maxNilpotentNormalHall M')
    P0 := P
    M_maximal := hM'
    M_typeI := hM'I
    K_eq_MF := rfl
    Kprime_eq := rfl
    P0_le_M := hPle
    P0_pGroup := hPpg
    P0_sylow := hPsyl
    P0_noncyclic := hPnc
    p_dvd_index := hqdvd
    minimal_p := fun q hq hqInPi => Nat.find_min' h ⟨hq, hqInPi⟩ }⟩

/-- The rank-two witness extracted in Peterfalvi (12.9), with all fields stated faithfully.

`L` is the second maximal subgroup with `P₀ ⊆ L_s` (`L_s = mainSubgroup L L_type`); `x` is the
order-`p` element of `Ω₁(P₀)^#` whose centralizer in `K = M_F` escapes `K'`, controls `N_G(⟨x⟩)`,
and escapes `L`. -/
structure RankTwoWitnessData (ctr : CounterexampleHypothesis (G := G)) where
  L : Subgroup G
  L_maximal : L ∈ maximalSubgroups G
  /-- Peterfalvi's type attached to `L` (so `L_s = mainSubgroup L L_type`). -/
  L_type : PeterfalviType
  L_hasType : HasPeterfalviType L_type L
  /-- `P₀ ⊆ L_s`. -/
  P0_le_Ls : ctr.P0 ≤ mainSubgroup L L_type
  x : G
  x_mem_P0 : x ∈ ctr.P0
  x_ne_one : x ≠ 1
  /-- `x ∈ Ω₁(P₀)^#`: `x` has order dividing `p`. -/
  x_mem_omega1 : x ^ ctr.p = 1
  /-- `C_K(x) ⊄ K'` (equivalently `C_{K/K'}(x) ≠ 1`). -/
  CKx_not_le_Kprime : ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime)
  /-- `N_G(⟨x⟩) ⊆ M`. -/
  normalizer_closure_x_le_M :
    Subgroup.normalizer ((Subgroup.closure ({x} : Set G) : Subgroup G) : Set G) ≤ ctr.M
  /-- `C_G(x) ⊄ L`. -/
  centralizer_x_not_le_L : ¬ (Subgroup.centralizer ({x} : Set G) ≤ L)

open OddOrder.Isaacs.Ch03.IsAInvariant
  (quotientMulAutHom quotientMulAutHom_apply_mk') in
/-- **Group-theoretic core of Peterfalvi (12.9)** (fully general, `§8`-independent).

If a **noncyclic abelian** group `A` acts **coprimely** on a finite group `K` whose
abelianization is nontrivial (`[K, K] ≠ K`), then some **nontrivial** `a ∈ A` has a fixed
subgroup `C_K(a)` that is *not* contained in the derived subgroup `[K, K]`.

This is the abstract content of the centralizer step of (12.9): there Peterfalvi takes
`A = Ω₁(P₀)` (elementary abelian of rank `2`, hence noncyclic) acting by conjugation on
`K = M_F`, with `[K, K] = K'`, and concludes `∃ x ∈ Ω₁(P₀)^#` with `C_K(x) ⊄ K'`
(equivalently `C_{K/K'}(x) ≠ 1`).

Proof.  `[K, K]` is characteristic, hence `A`-invariant, so `A` acts on the quotient
`K / [K, K]`.  By **BG Proposition 1.16(1)** (Isaacs 6.21,
`nontrivialActionFixedByClosure_eq_top_of_not_isCyclic'`) applied to that quotient action,
`K / [K, K] = ⟨ C_{K/[K,K]}(a) ∣ a ≠ 1 ⟩`.  Since `K / [K, K]` is nontrivial, some
`a ≠ 1` has `C_{K/[K,K]}(a) ≠ 1`; the witnessing coset lifts, by the coprime fixed-point
lifting (**Isaacs Cor 3.28**, `coprime_fixedPoints_quotient`), to an element of `C_K(a)`
outside `[K, K]`. -/
theorem exists_ne_one_actionFixedBy_not_le_commutator
    {A K : Type*} [Group A] [Finite A] [IsMulCommutative A] [Group K] [Finite K]
    (φ : A →* MulAut K) (hCop : Nat.Coprime (Nat.card A) (Nat.card K))
    (hSolv : Group.IsSolvable A ∨ Group.IsSolvable K) (hNC : ¬ IsCyclic A)
    (hK' : commutator K ≠ ⊤) :
    ∃ a : A, a ≠ 1 ∧ ¬ (Ch06.actionFixedBy φ a ≤ commutator K) := by
  classical
  -- `[K, K]` is characteristic, hence `A`-invariant; let `ψ` be the induced quotient action.
  have hN_inv : Ch03.IsAInvariant φ (commutator K) := Ch03.IsAInvariant.of_characteristic φ
  set ψ := quotientMulAutHom hN_inv with hψ
  -- Coprimality on the quotient: `|K / [K,K]|` divides `|K|`.
  have hCopQ : Nat.Coprime (Nat.card A) (Nat.card (K ⧸ commutator K)) :=
    hCop.coprime_dvd_right (commutator K).card_quotient_dvd_card
  -- BG 1.16(1) on the quotient action: the nontrivial fixed-point closure is everything.
  have htop : Ch06.nontrivialActionFixedByClosure ψ = ⊤ :=
    OddOrder.BG.Ch1.S01.nontrivialActionFixedByClosure_eq_top_of_not_isCyclic' ψ hCopQ hNC
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ a, a ≠ 1 → C_K(a) ≤ [K, K]`.  Show the quotient closure is `⊥`.
  have hquot_bot : Ch06.nontrivialActionFixedByClosure ψ ≤ ⊥ := by
    rw [Ch06.nontrivialActionFixedByClosure_le_iff]
    intro a ha q hq
    -- `q ∈ C_{K/K'}(a)`: `q` is fixed by every element of `⟨a⟩`.
    have hq_zp : q ∈ Ch06.actionFixedPoints ψ (Subgroup.zpowers a) := by
      rw [← Ch06.actionFixedBy_eq_actionFixedPoints_zpowers]; exact hq
    -- Lift `q = mk' g` and assemble the coset-fixed hypothesis on `⟨a⟩`.
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (commutator K) q
    have hg_fix : ∀ b : ↥(Subgroup.zpowers a), ∃ n ∈ commutator K, φ (b : A) g = g * n := by
      intro b
      have hb := (Ch06.mem_actionFixedPoints.mp hq_zp) b
      rw [hψ, quotientMulAutHom_apply_mk', QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq] at hb
      exact ⟨g⁻¹ * φ (b : A) g, by simpa using (commutator K).inv_mem hb, by group⟩
    -- Coprime fixed-point lifting (Isaacs Cor 3.28) on the cyclic group `⟨a⟩`.
    have hCop' : Nat.Coprime (Nat.card ↥(Subgroup.zpowers a)) (Nat.card K) :=
      hCop.coprime_dvd_left (Subgroup.card_subgroup_dvd_card _)
    have hSolv' : Group.IsSolvable ↥(Subgroup.zpowers a) ∨ Group.IsSolvable K := by
      rcases hSolv with hA | hK
      · have := hA; exact Or.inl inferInstance
      · exact Or.inr hK
    obtain ⟨c, hc_fix, n, hn, hcn⟩ :=
      Ch04.coprime_fixedPoints_quotient hCop' hSolv'
        (Ch03.IsAInvariant.of_characteristic (φ.comp (Subgroup.zpowers a).subtype)) hg_fix
    -- `c` is fixed by `a`, hence `c ∈ C_K(a) ≤ [K, K]` by `hcon`.
    have hca : φ a c = c := hc_fix ⟨a, Subgroup.mem_zpowers a⟩
    have hc_mem : c ∈ commutator K := hcon a ha (Ch06.mem_actionFixedBy.mpr hca)
    -- Then `g = c * n⁻¹ ∈ [K, K]`, so the coset `q = mk' g` is trivial.
    have hg_mem : g ∈ commutator K := by
      have : g = c * n⁻¹ := by rw [hcn]; group
      rw [this]; exact (commutator K).mul_mem hc_mem ((commutator K).inv_mem hn)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hg_mem
  -- `⊤ ≤ ⊥` forces `K / [K, K]` trivial, i.e. `[K, K] = ⊤`, contradicting `hK'`.
  have hbot : (⊤ : Subgroup (K ⧸ commutator K)) = ⊥ := le_bot_iff.mp (htop ▸ hquot_bot)
  apply hK'
  rw [Subgroup.eq_top_iff']
  intro k
  have hk1 : QuotientGroup.mk' (commutator K) k ∈ (⊥ : Subgroup (K ⧸ commutator K)) := by
    rw [← hbot]; exact Subgroup.mem_top _
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hk1
  exact hk1

/-- **Conjugation form of the (12.9) centralizer core** (ambient subgroups, directly the
form consumed by (12.9)).  If a **noncyclic abelian** subgroup `A ≤ G` normalizes a finite
subgroup `K` of **coprime** order whose abelianization is nontrivial (`⁅K, K⁆ ≠ K`), then
some `x ∈ A`, `x ≠ 1`, has `C_K(x) = C_G(x) ⊓ K` **not** contained in `⁅K, K⁆`.

Specialization of `exists_ne_one_actionFixedBy_not_le_commutator` to the conjugation action
`A → MulAut K` (`Subgroup.normalizerMonoidHom`): the abstract fixed subgroup `C_K(a)` becomes
`C_G(a) ⊓ K` and `commutator ↥K` maps to `⁅K, K⁆` under `K.subtype`. -/
theorem exists_mem_centralizer_inf_not_le_commutator
    {A K : Subgroup G} [Finite ↥A] [IsMulCommutative ↥A] [Finite ↥K]
    (hAK : A ≤ Subgroup.normalizer K) (hCop : Nat.Coprime (Nat.card ↥A) (Nat.card ↥K))
    (hSolv : Group.IsSolvable ↥A ∨ Group.IsSolvable ↥K) (hNC : ¬ IsCyclic ↥A) (hK' : ⁅K, K⁆ ≠ K) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 ∧ ¬ (Subgroup.centralizer {x} ⊓ K ≤ ⁅K, K⁆) := by
  classical
  -- The conjugation action `φ : A → MulAut K` and the `K.subtype`-image of `[↥K, ↥K]`.
  set φ : ↥A →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hAK)
    with hφ
  have htop_map : (⊤ : Subgroup ↥K).map K.subtype = K := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_top, true_and]
    constructor
    · rintro ⟨y, rfl⟩; exact y.2
    · intro hg; exact ⟨⟨g, hg⟩, rfl⟩
  have hmap : (commutator ↥K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, htop_map]
  -- `[↥K, ↥K] ≠ ⊤`: else its `K.subtype`-image would be `⁅K, K⁆ = K`.
  have hKtop : commutator ↥K ≠ ⊤ := by
    intro h; exact hK' (by rw [← hmap, h, htop_map])
  obtain ⟨a, ha_ne, hnle⟩ :=
    exists_ne_one_actionFixedBy_not_le_commutator φ hCop hSolv hNC hKtop
  -- Translate the abstract conclusion to ambient subgroups.
  obtain ⟨n, hn_fix, hn_out⟩ := SetLike.not_le_iff_exists.mp hnle
  refine ⟨(a : G), a.2, fun h => ha_ne (Subtype.ext h), SetLike.not_le_iff_exists.mpr
    ⟨(n : G), ?_, ?_⟩⟩
  · -- `n ∈ C_G(a) ⊓ K`: `a` conjugates `n` to itself, and `n ∈ K`.
    rw [Ch06.mem_actionFixedBy] at hn_fix
    have hval : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) :=
      congrArg (Subtype.val) hn_fix
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, n.2⟩
    rintro y rfl
    exact mul_inv_eq_iff_eq_mul.mp hval
  · -- `n ∉ ⁅K, K⁆`: else `n ∈ [↥K, ↥K]`, contradicting `hn_out`.
    rw [← hmap]
    intro hmem
    obtain ⟨m, hm, hmn⟩ := Subgroup.mem_map.mp hmem
    exact hn_out (by rw [show n = m from Subtype.ext hmn.symm]; exact hm)

/-- **Peterfalvi (12.9), the order-`p` centralizer witness** (the genuine, `§8`-free heart of
(12.9)).  Given the counterexample data with `P₀` abelian, coprime to `K = M_F`, normalizing `K`,
and `K` not perfect, there is an element `x ∈ Ω₁(P₀)^#` (order dividing `p`) with `C_K(x) ⊄ K'`.

Proof: apply the centralizer core `exists_mem_centralizer_inf_not_le_commutator` to the abelian
noncyclic `P₀` acting by conjugation on `K`, yielding `y ∈ P₀^#` with `C_K(y) ⊄ K'`; then pass to
the order-`p` power `x = y ^ (|y| / p)` — its centralizer contains `C_K(y)`, so still escapes
`K'`. -/
theorem exists_orderP_centralizer_witness [Finite G]
    (ctr : CounterexampleHypothesis (G := G))
    (habelian : IsMulCommutative ↥ctr.P0)
    (hcoprime : Nat.Coprime (Nat.card ↥ctr.P0) (Nat.card ↥ctr.K))
    (hP0_norm : ctr.P0 ≤ Subgroup.normalizer ctr.K)
    (hKperfect : ⁅ctr.K, ctr.K⁆ ≠ ctr.K) :
    ∃ x : G, x ∈ ctr.P0 ∧ x ≠ 1 ∧ x ^ ctr.p = 1 ∧
      ¬ (Subgroup.centralizer ({x} : Set G) ⊓ ctr.K ≤ ctr.Kprime) := by
  classical
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have := habelian
  have : Group.IsNilpotent ↥ctr.P0 := ctr.P0_pGroup.isNilpotent
  -- `K' = ⁅K, K⁆`.
  have hKprime : ctr.Kprime = ⁅ctr.K, ctr.K⁆ :=
    ctr.Kprime_eq.trans (Subgroup.map_subtype_commutator ctr.K)
  -- Centralizer core (A = P₀, abelian noncyclic, coprime, normalizing K, K not perfect).
  obtain ⟨y, hyP0, hy_ne, hy_cent⟩ :=
    exists_mem_centralizer_inf_not_le_commutator (A := ctr.P0) (K := ctr.K)
      hP0_norm hcoprime (Or.inl inferInstance) ctr.P0_noncyclic hKperfect
  -- `y` has `p`-power order `p ^ k` with `k ≥ 1`.
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp ctr.P0_pGroup) ⟨y, hyP0⟩
  have hoy : orderOf y = ctr.p ^ k :=
    (orderOf_injective ctr.P0.subtype ctr.P0.subtype_injective ⟨y, hyP0⟩).trans hk
  have hk_pos : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h
    · rw [h0, pow_zero, orderOf_eq_one_iff] at hoy; exact absurd hoy hy_ne
    · exact h
  have hp_dvd : ctr.p ∣ orderOf y := hoy ▸ dvd_pow_self ctr.p (by omega)
  have hord_pos : 0 < orderOf y := hoy ▸ pow_pos ctr.p_prime.pos k
  -- The order-`p` power `x = y ^ (|y| / p)`.
  set n := orderOf y / ctr.p with hn
  have hnp : n * ctr.p = orderOf y := Nat.div_mul_cancel hp_dvd
  have hn_pos : 0 < n := by
    rw [hn]; exact Nat.div_pos (Nat.le_of_dvd hord_pos hp_dvd) ctr.p_prime.pos
  have hn_lt : n < orderOf y := by
    rw [hn]; exact Nat.div_lt_self hord_pos ctr.p_prime.one_lt
  refine ⟨y ^ n, ctr.P0.pow_mem hyP0 n, ?_, ?_, ?_⟩
  · -- `y ^ n ≠ 1`: else `|y| ∣ n < |y|`, impossible.
    rw [Ne, ← orderOf_dvd_iff_pow_eq_one]
    exact Nat.not_dvd_of_pos_of_lt hn_pos hn_lt
  · -- `(y ^ n) ^ p = y ^ (n * p) = y ^ |y| = 1`.
    rw [← pow_mul, hnp, pow_orderOf_eq_one]
  · -- `C_K(y ^ n) ⊇ C_K(y) ⊄ K'`.
    rw [hKprime]
    intro hle
    apply hy_cent
    refine le_trans (inf_le_inf_right ctr.K ?_) hle
    intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    rintro z rfl
    exact Commute.pow_left (hg y rfl) n

/-- **Peterfalvi (12.9), the `(κ ∪ σ)ᶜ`-Hall complement obligation** — the precise BG §16
(Proposition 16.1) bridge behind `(8.12.a)`.  For the type-`I` minimal-counterexample `M`, the
Sylow `p`-subgroup `P₀` (with `p ∣ [M : M_F]`, hence `p ∤ |M_F|` as `M_F` is Hall) lies in a
`(κ(M) ∪ σ(M))ᶜ`-Hall subgroup `U ≤ M`.

*Why this is the gate (and not `(8.12.a)` itself).*  BG Theorem B(1)
(`theoremB_U_sylow_abelian_rank_le_two`, already **proved** in the repo) says every Sylow of such
a `U` is abelian of rank `≤ 2`; the only missing input is producing the complement `U`.  The
type-`I` complement of `M_F` is `π(M_F)ᶜ`-Hall (immediate from `M_F` being a normal Hall
subgroup), and Proposition 16.1's type-`I` classification (`κ(M) = ∅` and `M_F = M_σ`)
identifies `π(M_F)ᶜ` with `(κ ∪ σ)ᶜ`.

**Proof (issue 2016).**  Write `M = ctr.M`, `p = ctr.p`.  Proposition 16.1 (clause (a)) gives
`κ(M) = ∅` for the type-`I` `M`, and (clause (f)) gives `M_F = M_σ`.  Since `M_F` is `π(M_F)`-Hall
in `M` (`maxNilpotentNormalHall_isHall`) and `p ∣ [M : M_F]`, we have `p ∤ |M_F| = |M_σ|`.  As
`M_σ` is `σ(M)`-Hall in `G` (`S10.isHall_Msigma_Malpha`), `p ∤ |M_σ|` forces `p ∉ σ(M)` (else
`p` would divide the `σ`-part `|M_σ|` of `|G|`).  With `κ(M) = ∅` this gives `p ∈ (κ ∪ σ)ᶜ`, so
the `p`-group `P₀` is a `(κ ∪ σ)ᶜ`-subgroup of the solvable `M` and Hall's theorem D
(`Ch03.hall_D`) places it in a `(κ ∪ σ)ᶜ`-Hall subgroup `U` of `M`.  The only `§16`-gated inputs
are the cited Proposition 16.1 type-`I` clauses (lane-f frontier, issue 8015). -/
theorem exists_sigmaKappaCompl_hall_ge_P0 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ∃ U : Subgroup G, ctr.P0 ≤ U ∧ U ≤ ctr.M ∧
      Ch03.IsHallSubgroup
        ((OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ)
        (U.subgroupOf ctr.M) := by
  classical
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hMsolv : Group.IsSolvable ↥ctr.M := hG.isSolvable_of_mem_maximalSubgroups ctr.M_maximal
  -- κ(M) = ∅ (Type I ⟹ Type F, Prop 16.1 clause (a)).
  have hκ : OddOrder.BG.Ch4.S14.kappa ctr.M = ∅ :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).1.mp ctr.M_typeI
  -- M_F = M_σ (Prop 16.1 clause (f)).
  have hMFσ : maxNilpotentNormalHall ctr.M = OddOrder.BG.Ch3.S10.Msigma ctr.M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
      (Or.inl ctr.M_typeI)
  -- `p ∤ |M_F|`: `M_F` is `π(M_F)`-Hall in `M` and `p ∣ [M : M_F]`.
  have hpidx : ctr.p ∣ ((maxNilpotentNormalHall ctr.M).subgroupOf ctr.M).index := by
    have h := ctr.p_dvd_index
    rwa [ctr.K_eq_MF, Subgroup.relIndex] at h
  have hMFhall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M
  have hp_not_dvd_MF : ¬ ctr.p ∣ Nat.card ↥(maxNilpotentNormalHall ctr.M) := fun hdvd =>
    hMFhall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpidx, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hdvd, Nat.card_pos.ne'⟩)
  have hp_not_dvd_Mσ : ¬ ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) :=
    hMFσ ▸ hp_not_dvd_MF
  -- `p ∣ |G|` (`p ∣ [M : M_F] ∣ |M| ∣ |G|`).
  have hp_dvd_G : ctr.p ∣ Nat.card G :=
    (hpidx.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  -- `p ∉ σ(M)`: `M_σ` is `σ(M)`-Hall in `G`, and `p ∤ |M_σ|` with `p ∣ |G| = |M_σ|·[G:M_σ]`.
  have hσHall := (OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha hG ctr.M_maximal).1
  have hp_not_sigma : ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := by
    intro hpσ
    refine hp_not_dvd_Mσ ?_
    have hpmul : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M)
        * (OddOrder.BG.Ch3.S10.Msigma ctr.M).index := by
      rw [Subgroup.card_mul_index]; exact hp_dvd_G
    rcases (Nat.Prime.dvd_mul ctr.p_prime).mp hpmul with h | h
    · exact h
    · exact absurd hpσ (hσHall.index_no_pi ctr.p
        (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, h, Subgroup.index_ne_zero_of_finite⟩))
  -- `p ∈ (κ ∪ σ)ᶜ`.
  have hp_compl : ctr.p ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M
      ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    simp only [Set.mem_compl_iff, Set.mem_union, not_or]
    exact ⟨hκ ▸ Set.notMem_empty ctr.p, hp_not_sigma⟩
  -- Every prime divisor of `|P₀|` (a `p`-power) is `p ∈ (κ ∪ σ)ᶜ`; place `P₀` via Hall D.
  have hcond : ∀ q ∈ (Nat.card ↥(ctr.P0.subgroupOf ctr.M)).primeFactors,
      q ∈ (OddOrder.BG.Ch4.S14.kappa ctr.M ∪ OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    intro q hq
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp ctr.P0_pGroup)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe ctr.P0_le_M).toEquiv, hn] at hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [(Nat.prime_dvd_prime_iff_eq hqp ctr.p_prime).mp (hqp.dvd_of_dvd_pow hqdvd)]
    exact hp_compl
  obtain ⟨V, hVhall, hPV⟩ := Ch03.hall_D (G := ↥ctr.M) hcond
  refine ⟨V.map ctr.M.subtype, ?_, Subgroup.map_subtype_le V, ?_⟩
  · rw [show ctr.P0 = (ctr.P0.subgroupOf ctr.M).map ctr.M.subtype from
      (Subgroup.map_subgroupOf_eq_of_le ctr.P0_le_M).symm]
    exact Subgroup.map_mono hPV
  · have hUeq : (V.map ctr.M.subtype).subgroupOf ctr.M = V :=
      Subgroup.comap_map_eq_self_of_injective ctr.M.subtype_injective V
    rw [hUeq]; exact hVhall

/-- **Peterfalvi (12.9), the rank-two structure for `P₀`** = `(8.12.a)`.

Every Sylow subgroup of the type-`I` complement `U` (`M = M_F ⋊ U`) is abelian of rank `≤ 2`
(BG **Theorem B(1)**, `theoremB_U_sylow_abelian_rank_le_two`, **proved**); applied to the Sylow
`p`-subgroup `P₀ ≤ U` and combined with `P₀` noncyclic (Hypothesis `(12.8)`, `ctr.P0_noncyclic`,
giving `2 ≤ rank P₀` via `two_le_rank_of_noncyclic_pSubgroup`), this forces `P₀` abelian of rank
exactly `2`.

The substantive content (Theorem B(1) + the rank lower bound) is therefore **wired and
load-bearing**; the only remaining gap is the `(κ ∪ σ)ᶜ`-Hall complement obligation
`exists_sigmaKappaCompl_hall_ge_P0` (the BG §16 / Proposition 16.1 bridge, lane-f).

(The other structural inputs `P₀` coprime to `K`, `P₀ ≤ N_G(K)`, `⁅K, K⁆ ≠ K` are discharged in
`exists_rankTwoWitness` from `(8.11)` [`M_F` Hall] and `M_F ◁ M` nilpotent + nontrivial.) -/
theorem counterexample_P0_K_structure [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    IsMulCommutative ↥ctr.P0 ∧ rank ↥ctr.P0 = 2 := by
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  obtain ⟨U, hP0U, hUM, hU⟩ := exists_sigmaKappaCompl_hall_ge_P0 hG ctr
  obtain ⟨hrank_le, habelian⟩ :=
    OddOrder.BG.Ch4.S16.theoremB_U_sylow_abelian_rank_le_two hG ctr.M_maximal hUM hU
      ctr.p ctr.p_prime ctr.P0 hP0U ctr.P0_pGroup
  exact ⟨habelian, le_antisymm hrank_le
    (OddOrder.BG.Ch2.S09.two_le_rank_of_noncyclic_pSubgroup hG ctr.P0_pGroup ctr.P0_noncyclic)⟩

/-- **Counterexample fact: `K = M_F = M_σ`.**  For the type-`I` minimal counterexample `M`, its
Fitting kernel `K = M_F` equals the `σ`-core `M_σ` (Proposition 16.1 clause (f), via
`proposition_type_classification`). -/
theorem MF_eq_Msigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ctr.K = OddOrder.BG.Ch3.S10.Msigma ctr.M := by
  rw [ctr.K_eq_MF]
  exact (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
    (Or.inl ctr.M_typeI)

/-- **Counterexample fact: `p ∉ σ(M)`.**  The minimal prime `p` of Hypothesis (12.8) does not lie
in `σ(M)`: `M_σ` is `σ(M)`-Hall in `G` and `p ∤ |M_σ| = |M_F|` (as `M_F` is Hall in `M` and
`p ∣ [M : M_F]`), while `p ∣ |G| = |M_σ| · [G : M_σ]`, so `p` divides `[G : M_σ]`, forcing
`p ∉ σ(M)`. -/
theorem p_not_mem_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := by
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  have hMFσ : maxNilpotentNormalHall ctr.M = OddOrder.BG.Ch3.S10.Msigma ctr.M :=
    (OddOrder.BG.Ch4.S16.proposition_type_classification hG ctr.M_maximal).2.2.2.2.2.mpr
      (Or.inl ctr.M_typeI)
  have hpidx : ctr.p ∣ ((maxNilpotentNormalHall ctr.M).subgroupOf ctr.M).index := by
    have h := ctr.p_dvd_index
    rwa [ctr.K_eq_MF, Subgroup.relIndex] at h
  have hMFhall := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_isHall ctr.M
  have hp_not_dvd_MF : ¬ ctr.p ∣ Nat.card ↥(maxNilpotentNormalHall ctr.M) := fun hdvd =>
    hMFhall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hpidx, Subgroup.index_ne_zero_of_finite⟩)
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, hdvd, Nat.card_pos.ne'⟩)
  have hp_not_dvd_Mσ : ¬ ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M) :=
    hMFσ ▸ hp_not_dvd_MF
  have hp_dvd_G : ctr.p ∣ Nat.card G :=
    (hpidx.trans (Subgroup.index_dvd_card _)).trans (Subgroup.card_subgroup_dvd_card ctr.M)
  have hσHall := (OddOrder.BG.Ch3.S10.isHall_Msigma_Malpha hG ctr.M_maximal).1
  intro hpσ
  refine hp_not_dvd_Mσ ?_
  have hpmul : ctr.p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma ctr.M)
      * (OddOrder.BG.Ch3.S10.Msigma ctr.M).index := by
    rw [Subgroup.card_mul_index]; exact hp_dvd_G
  rcases (Nat.Prime.dvd_mul ctr.p_prime).mp hpmul with h | h
  · exact h
  · exact absurd hpσ (hσHall.index_no_pi ctr.p
      (Nat.mem_primeFactors.mpr ⟨ctr.p_prime, h, Subgroup.index_ne_zero_of_finite⟩))

/-- **Peterfalvi (12.11), step (8.1.c): `P₀` does not centralize `K = M_F`.**  If `P₀ ≤ C_G(K)`,
then (as `K = M_σ`) `P₀ ≤ C_G(M_σ)`, so `C_G(M_σ) ⊓ P₀ = P₀` has `rank ≤ 1` by BG Proposition
10.11(b) (`rank_centralizer_Msigma_inf_le_one`, applicable since `P₀` is a `p`-group with
`p ∉ σ(M)`, hence a `σ(M)ᶜ`-subgroup of `M`).  But `P₀` is noncyclic (Hypothesis (12.8)), so
`2 ≤ rank P₀` — a contradiction.  This is the honest content of the "(8.1.c) ⟹ `P₀` does not
centralize `K`" step of Peterfalvi (12.11). -/
theorem P0_not_le_centralizer_K [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (ctr : CounterexampleHypothesis (G := G)) :
    ¬ ctr.P0 ≤ Subgroup.centralizer (ctr.K : Set G) := by
  have : Fact ctr.p.Prime := ⟨ctr.p_prime⟩
  intro hP0C
  -- `P₀` is a `σ(M)ᶜ`-subgroup (a `p`-group with `p ∉ σ(M)`).
  have hpσ : ctr.p ∉ OddOrder.BG.Ch3.S10.sigma ctr.M := p_not_mem_sigma hG ctr
  have hP0pi : ctr.P0.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma ctr.M)ᶜ := by
    intro q hq
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp ctr.P0_pGroup
    rw [hn] at hq
    obtain ⟨hqp, hqdvd, _⟩ := Nat.mem_primeFactors.mp hq
    rw [(Nat.prime_dvd_prime_iff_eq hqp ctr.p_prime).mp (hqp.dvd_of_dvd_pow hqdvd)]
    exact hpσ
  -- `rank (C_G(M_σ) ⊓ P₀) ≤ 1` (BG Prop 10.11(b)).
  have hrank := OddOrder.BG.Ch3.S10.rank_centralizer_Msigma_inf_le_one hG ctr.M_maximal
    ctr.P0_le_M hP0pi
  -- `P₀ ≤ C_G(M_σ)` (from `hP0C` and `K = M_σ`), so `C_G(M_σ) ⊓ P₀ = P₀`.
  have hP0Cσ : ctr.P0 ≤ Subgroup.centralizer (OddOrder.BG.Ch3.S10.Msigma ctr.M : Set G) := by
    rwa [MF_eq_Msigma hG ctr] at hP0C
  rw [inf_eq_right.mpr hP0Cσ] at hrank
  have h2 := OddOrder.BG.Ch2.S09.two_le_rank_of_noncyclic_pSubgroup hG ctr.P0_pGroup
    ctr.P0_noncyclic
  omega

end OddOrder.Peterfalvi.S14


