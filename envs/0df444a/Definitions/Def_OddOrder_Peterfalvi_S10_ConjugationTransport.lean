-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S10_ConjugationTransport
-- name    : OddOrder_Peterfalvi_S10_ConjugationTransport
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T11:10:24.184758+00:00
-- url     : https://prove2.me/theorems/fd83933e-ab45-403a-9f98-b538bd132339
-- title:
--   Peterfalvi §10: minimal simple groups, the conjugation-transport layer
-- statement:
--   The conjugation-transport layer of the minimal-simple-groups development of Peterfalvi, *Character Theory for the Odd Order Theorem*, §10, split from the parent file. It consists of lemmas only, including `typeIA_subset_sharp`, `typeIA_conj_mem` and `typeF_complement_isHall_kappa_sigma_compl`.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S10_ConjugationTransport.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S10_ConjugationTransport.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S10_StructureSetup

namespace OddOrder.Peterfalvi.S10

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- Elements of `A(M)` are nonidentity: `A(M) ⊆ G^#`. -/
theorem typeIA_subset_sharp (M : Subgroup G) (data : TypeIData M) :
    typeIA M data ⊆ OddOrder.Peterfalvi.S04.sharp (Set.univ : Set G) := by
  rintro y ⟨-, hy1, -⟩
  exact OddOrder.Peterfalvi.S04.mem_sharp.mpr ⟨Set.mem_univ y, hy1⟩

/-- `A(M) ⊆ M`. -/
theorem typeIA_subset (M : Subgroup G) (data : TypeIData M) :
    typeIA M data ⊆ (M : Set G) :=
  fun _ hy => hy.1

/-- Conjugation preserves nonidentity: `m·a·m⁻¹ ≠ 1` for `a ≠ 1`. -/
theorem conj_ne_one {m a : G} (ha : a ≠ 1) : m * a * m⁻¹ ≠ 1 := fun h =>
  ha (by
    have h2 : a = m⁻¹ * (m * a * m⁻¹) * m := by group
    rw [h] at h2
    simpa using h2)

/-- `A(M)` is `M`-conjugation invariant: `m·A(M)·m⁻¹ = A(M)` pointwise.  The centralizer witness
`x ∈ H^#` transports along the `M`-normality of `H = M_F` (`maxNilpotentNormalHall_le_normalizer`).
-/
theorem typeIA_conj_mem (M : Subgroup G) (data : TypeIData M) {m : G} (hm : m ∈ M) {a : G}
    (ha : a ∈ typeIA M data) : m * a * m⁻¹ ∈ typeIA M data := by
  obtain ⟨haM, ha1, x, hx, hax⟩ := ha
  obtain ⟨hxH, hx1⟩ := (Set.mem_sdiff x).mp hx
  have hmxH : m * x * m⁻¹ ∈ maxNilpotentNormalHall M := by
    have hnorm := OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_le_normalizer M hm
    rw [Subgroup.mem_normalizer_iff] at hnorm
    exact (hnorm x).mp (data.typeF.H_eq ▸ (SetLike.mem_coe.mp hxH))
  refine ⟨mul_mem (mul_mem hm haM) (inv_mem hm), conj_ne_one ha1, m * x * m⁻¹, ?_, ?_⟩
  · exact (Set.mem_sdiff _).mpr ⟨data.typeF.H_eq ▸ (SetLike.mem_coe.mpr hmxH),
      conj_ne_one (fun h => hx1 (Set.mem_singleton_iff.mpr h))⟩
  · rw [Subgroup.mem_centralizer_singleton_iff] at hax ⊢
    calc m * a * m⁻¹ * (m * x * m⁻¹) = m * (a * x) * m⁻¹ := by group
      _ = m * (x * a) * m⁻¹ := by rw [hax]
      _ = m * x * m⁻¹ * (m * a * m⁻¹) := by group

/-- `A(M)` is nonempty (any `x ∈ H^#` lies in `C_M(x)^#`). -/
theorem typeIA_nonempty (M : Subgroup G) (data : TypeIData M) :
    (typeIA M data).Nonempty := by
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp data.typeF.H_nontrivial
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  exact ⟨a.1, data.typeF.H_le a.2, ha1',
    a.1, (Set.mem_sdiff _).mpr ⟨SetLike.mem_coe.mpr a.2, fun h => ha1' (Set.mem_singleton_iff.mp
        h)⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

/-- **The type-`F` complement `U` is a `(κ ∪ σ)′`-Hall subgroup of `M`.**  For type I,
`κ(M) = ∅` (Proposition 16.1) and `H = M_F = M_σ` is the `σ`-Hall of `G`, so the complement
`U` of `H` in `M` has `σ′`-order (`|U| = |M : H|` divides `|G : M_σ|`) and `σ`-index
(`|M : U| = |H|`).  Supplies the `hU` input of BG Theorem II
(`theoremII_tame_embedding`) from the shared type-I data. -/
theorem typeF_complement_isHall_kappa_sigma_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    OddOrder.Isaacs.Ch03.IsHallSubgroup
      ((OddOrder.BG.Ch4.S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (data.typeF.U.subgroupOf M) := by
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hHMσ : data.typeF.H = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [data.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hM (Or.inl ⟨data⟩)
  have hcompl := data.typeF.complement
  have hHall := OddOrder.BG.Ch3.S10.Msigma_isHall hG hM
  constructor
  · -- primes of `|U|` avoid `κ ∪ σ = σ`: `|U| = |M : H|` divides `|G : M_σ|`, a `σ′`-number.
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_union, hκ, Set.mem_empty_iff_false, false_or]
    intro hpσ
    have hidx : (data.typeF.H.subgroupOf M).index
        = Nat.card (data.typeF.U.subgroupOf M) := hcompl.symm.index_eq_card
    have hrel : (data.typeF.H.subgroupOf M).index * M.index = data.typeF.H.index :=
      Subgroup.relIndex_mul_index data.typeF.H_le
    have hdvd : p ∣ (OddOrder.BG.Ch3.S10.Msigma M).index := by
      rw [← hHMσ, ← hrel]
      exact Dvd.dvd.mul_right (hidx ▸ (Nat.mem_primeFactors.mp hp).2.1) _
    have hidx_ne : (OddOrder.BG.Ch3.S10.Msigma M).index ≠ 0 :=
      Subgroup.index_ne_zero_of_finite
    exact hHall.2 p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, hdvd, hidx_ne⟩) hpσ
  · -- primes of `|M : U| = |H| = |M_σ|` lie in `σ ⊆ κ ∪ σ`.
    intro p hp
    simp only [Set.mem_compl_iff, Set.mem_union, not_not, hκ, Set.mem_empty_iff_false, false_or]
    have hidxU : (data.typeF.U.subgroupOf M).index
        = Nat.card (data.typeF.H.subgroupOf M) := hcompl.index_eq_card
    have hcardH : Nat.card (data.typeF.H.subgroupOf M) = Nat.card data.typeF.H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe data.typeF.H_le).toEquiv
    have hpH : p ∣ Nat.card (OddOrder.BG.Ch3.S10.Msigma M) := by
      rw [← hHMσ, ← hcardH, ← hidxU]
      exact (Nat.mem_primeFactors.mp hp).2.1
    exact hHall.1 p (Nat.mem_primeFactors.mpr
      ⟨(Nat.mem_primeFactors.mp hp).1, hpH, Nat.card_pos.ne'⟩)

/-- **The type-I support `A(M)` lies in BG's Theorem E set `A(M) = ASet M U`.**  A point
`y ∈ A(M)` is a nonidentity element of `M` centralizing some `x ∈ H^# = M_σ^#`, so
`M_σ ⊓ C_G(y) ≠ ⊥` (`y ∈ \widehat{M_σ}`), and `y ∈ M = U ⊔ M_σ` by the type-`F` complement
decomposition.  The support-set bridge feeding BG Theorem II into the (8.13) pins. -/
theorem typeIA_subset_ASet [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M) :
    typeIA M data ⊆ OddOrder.BG.Ch4.S16.ASet M data.typeF.U := by
  have hHMσ : data.typeF.H = OddOrder.BG.Ch3.S10.Msigma M := by
    rw [data.typeF.H_eq]
    exact OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hM (Or.inl ⟨data⟩)
  rintro y ⟨hyM, _hy1, x, hxH, hyC⟩
  obtain ⟨hxHmem, hx1⟩ := (Set.mem_sdiff _).mp hxH
  refine ⟨⟨hyM, ?_⟩, ?_⟩
  · -- `x ∈ M_σ ⊓ C_G(y)` is a nonidentity witness.
    intro hbot
    have hxC : x ∈ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact (Subgroup.mem_centralizer_iff.mp hyC x (Set.mem_singleton x)).symm
    have hxmem : x ∈ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({y} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hHMσ ▸ SetLike.mem_coe.mp hxHmem, hxC⟩
    rw [hbot] at hxmem
    exact hx1 (Set.mem_singleton_iff.mpr (Subgroup.mem_bot.mp hxmem))
  · -- `y ∈ U ⊔ M_σ`: decompose `y = h · u` along the type-`F` complement.
    obtain ⟨⟨h, u⟩, hhu, -⟩ := Subgroup.IsComplement.existsUnique
      data.typeF.complement (⟨y, hyM⟩ : ↥M)
    have hyval : ((h : ↥M) : G) * ((u : ↥M) : G) = y := by
      simpa using congrArg (fun z : ↥M => (z : G)) hhu
    have hh : ((h : ↥M) : G) ∈ OddOrder.BG.Ch3.S10.Msigma M :=
      hHMσ ▸ Subgroup.mem_subgroupOf.mp h.2
    have hu : ((u : ↥M) : G) ∈ data.typeF.U := Subgroup.mem_subgroupOf.mp u.2
    rw [SetLike.mem_coe, ← hyval]
    exact mul_mem (Subgroup.mem_sup_right hh) (Subgroup.mem_sup_left hu)

/-- **Peterfalvi (8.13.a) for the type-I support**: two `G`-conjugate elements of `A(M)` are
already `M`-conjugate.  BG §16 Theorem II conjunct 1 (`theoremII_tame_embedding`, whose
`X = ASet M U` branch receives `A(M)` via `typeIA_subset_ASet`); the `κ`-Hall input is `K = ⊥`
(`κ(M) = ∅` for type I) and the `(κ ∪ σ)′`-Hall input is the type-`F` complement
(`typeF_complement_isHall_kappa_sigma_compl`). -/
theorem typeIA_isConj_conj_in_M [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a b : G} (ha : a ∈ typeIA M data) (hb : b ∈ typeIA M data) (hab : IsConj a b) :
    ∃ m : G, m ∈ M ∧ m * a * m⁻¹ = b := by
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro p _
    rw [hκ]
    exact Set.notMem_empty p
  have hII := OddOrder.BG.Ch4.S16.theoremII_tame_embedding hG hM bot_le data.typeF.U_le hK
    (typeF_complement_isHall_kappa_sigma_compl hG hM data) (Or.inl rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hab
  obtain ⟨m, hmM, hmb⟩ := hII.1 a (typeIA_subset_ASet hG hM data ha)
    b (typeIA_subset_ASet hG hM data hb) ⟨g, hg.symm⟩
  exact ⟨m, hmM, hmb.symm⟩

/-- `MulAut` smul is `map` along the automorphism (local copy of the S09/S11 helper). -/
theorem mulAut_smul_eq_map' (φ : MulAut G) (H : Subgroup G) :
    φ • H = H.map (φ : G →* G) := by
  rw [Subgroup.pointwise_smul_def]
  rfl

/-- `τ₂` is conjugation-equivariant (from `σ`-equivariance and the `pRank` invariance under
the conjugation isomorphism). -/
private theorem tau2_conj_smul' [Finite G] (g : G) (M : Subgroup G) :
    OddOrder.BG.Ch3.S12.tau2 (MulAut.conj g • M) = OddOrder.BG.Ch3.S12.tau2 M := by
  have e : ↥M ≃* ↥(MulAut.conj g • M) :=
    (Subgroup.equivMapOfInjective M (MulAut.conj g : G →* G)
      (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (mulAut_smul_eq_map' (MulAut.conj g) M).symm)
  ext p
  simp only [OddOrder.BG.Ch3.S12.tau2, Set.mem_ofPred_eq,
    OddOrder.BG.Ch4.S14.sigma_conj_smul_eq]
  rw [OddOrder.BG.Ch3.S13.pRank_eq_of_mulEquiv (p := p) e.symm]

/-- **Peterfalvi (8.13.c2) coprimality core at a `σ`-sharp point** — the `σ`-decomposition-generic
form (`non_disjoint_signalizer_frobenius`, BG Lemma 14.13(a), takes any maximal `S`; the type-I
`escaping_sigma_disjoint_centralizer` only specialises it by deriving `z ∈ M_σ^#` from `κ(S) = ∅`
and `w ∈ M_σ` from the type-`F` Frobenius absorption — both are hypotheses here).

For an escaping `z ∈ M_σ^#` and any `w ∈ M_σ^#`, no prime `p ∈ σ(N[z])` divides `|C_S(w)|`:
a common `p ∈ σ(N[z]) ∩ π(S)` makes `S` Frobenius with kernel `S_σ` and `τ₂(S) = ∅`; `w ∈ S_σ`
absorbs a Cauchy `p`-element of `C_S(w)` into `S_σ`, so `p ∈ σ(S)`, forcing `N[z]` conjugate to `S`
(`sigma_disjoint_of_nonconjugate`) and transporting `τ₂(N[z]) ∋ π(⟨z⟩) ≠ ∅` onto `τ₂(S) = ∅`. -/
theorem escaping_sigmaSharp_disjoint_centralizer_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hS : S ∈ maximalSubgroups G)
    {z : G} (hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S)
    (hzesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ S)
    {w : G} (hwS : w ∈ S) (hw1 : w ≠ 1)
    (hwit : ∃ x ∈ OddOrder.BG.Ch3.S10.Msigma S, x ≠ 1 ∧ Commute w x)
    {p : ℕ} (hpp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z))
    (hpC : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) : False := by
  classical
  have hz1 : z ≠ 1 := hσz.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard := by
    by_contra h
    exact hzesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hS hσz.1 hz1
      (not_lt.mp h))
  -- `p ∈ π(S)` (it divides `|C_S(w)| ∣ |S|`), so Lemma 14.13(a) fires.
  have hpS : p ∈ OddOrder.BG.Ch4.S14.piSet S := by
    refine Nat.mem_primeFactors.mpr ⟨hpp, hpC.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨-, htau2S, U, -, hfrobU⟩ :=
    OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius hG hS hσz hgt ⟨p, hpσ, hpS⟩
  -- Frobenius kernel absorption: commuting with a nontrivial `S_σ`-element lands in `S_σ`.
  have hker : ∀ {u v : G}, u ∈ S → v ∈ OddOrder.BG.Ch3.S10.Msigma S → v ≠ 1 →
      Commute u v → u ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    intro u v huS hvMσ hv1 hcomm
    have hvS : v ∈ S := OddOrder.BG.Ch3.S10.Msigma_le S hvMσ
    have hcent := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le hfrobU
      (⟨v, hvS⟩ : ↥S) (Subgroup.mem_subgroupOf.mpr hvMσ)
      (fun h1 => hv1 (congrArg Subtype.val h1))
    have humem : (⟨u, huS⟩ : ↥S) ∈
        Subgroup.centralizer ({(⟨v, hvS⟩ : ↥S)} : Set ↥S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.eq
    exact Subgroup.mem_subgroupOf.mp (hcent humem)
  obtain ⟨xw, hxwMσ, hxw1, hxwc⟩ := hwit
  have hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma S := hker hwS hxwMσ hxw1 hxwc
  -- a Cauchy `p`-element of `C_S(w)` lies in `S_σ` (absorption), so `p ∈ σ(S)`.
  have : Fact p.Prime := ⟨hpp⟩
  obtain ⟨c, hc_ord⟩ := exists_prime_orderOf_dvd_card' p hpC
  have hcS : (c : G) ∈ S := (Subgroup.mem_inf.mp c.2).1
  have hcC : Commute (c : G) w := by
    have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
    exact this
  have hcMσ : (c : G) ∈ OddOrder.BG.Ch3.S10.Msigma S :=
    hker hcS hwMσ hw1 hcC
  have hpσS : p ∈ OddOrder.BG.Ch3.S10.sigma S := by
    refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup S p (Nat.mem_primeFactors.mpr
      ⟨hpp, ?_, Nat.card_pos.ne'⟩)
    have hcord : orderOf ((⟨(c : G), hcMσ⟩ :
        ↥(OddOrder.BG.Ch3.S10.Msigma S))) = p := by
      rw [← hc_ord]
      exact (orderOf_injective (OddOrder.BG.Ch3.S10.Msigma S).subtype
        (OddOrder.BG.Ch3.S10.Msigma S).subtype_injective
        (⟨(c : G), hcMσ⟩ : ↥(OddOrder.BG.Ch3.S10.Msigma S))).symm.trans
        (orderOf_injective (OddOrder.Peterfalvi.S04.centralizerIn S w).subtype
          (OddOrder.Peterfalvi.S04.centralizerIn S w).subtype_injective c)
    rw [← hcord]
    exact orderOf_dvd_natCard _
  -- `σ(N[z]) ∩ σ(S) ≠ ∅` forces `N[z] ~ S`, transporting `τ₂`.
  have hN₀max : OddOrder.BG.Ch4.S16.FT_signalizerBase z ∈ maximalSubgroups G := by
    obtain ⟨N₀, hN₀⟩ :=
      OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG hS hσz hzesc
    have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard ∧
        (maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G))).Nonempty :=
      ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase z = hbr.2.choose :=
      dif_pos hbr
    rw [hb]
    exact (mem_maximalSubgroupsContaining.mp hbr.2.choose_spec).1
  have hconj : ∃ g : G, MulAut.conj g • OddOrder.BG.Ch4.S16.FT_signalizerBase z = S := by
    by_contra hnc2
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hN₀max hS hnc2) hpσ hpσS
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨Nstr, ⟨hNstr_max, hNstr_C, -, -, hNstr_tau2, -, -⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG hS hσz hgt
  have hNstr_eq : Nstr = OddOrder.BG.Ch4.S16.FT_signalizerBase z := by
    obtain ⟨N₀, hN₀⟩ :=
      OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG hS hσz hzesc
    have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G)),
        L = N₀ := by
      intro L hL
      rw [hN₀, Set.mem_singleton_iff] at hL
      exact hL
    have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard ∧
        (maximalSubgroupsContaining (Subgroup.centralizer ({z} : Set G))).Nonempty :=
      ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase z = hbr.2.choose := dif_pos hbr
    rw [hb, huniq _ hbr.2.choose_spec,
      huniq Nstr (mem_maximalSubgroupsContaining.mpr ⟨hNstr_max, hNstr_C⟩)]
  -- a prime of `orderOf z` lies in `τ₂(N[z]) = τ₂(S) = ∅`, but `z ≠ 1` — contradiction.
  set p₀ : ℕ := (orderOf z).minFac with hp₀
  have hp₀p : p₀.Prime := Nat.minFac_prime (fun h => hz1 (orderOf_eq_one_iff.mp h))
  have hp₀tau2 : p₀ ∈ OddOrder.BG.Ch3.S12.tau2 Nstr := by
    refine hNstr_tau2 p₀ ?_
    refine Nat.mem_primeFactors.mpr ⟨hp₀p, ?_, Nat.card_pos.ne'⟩
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    exact Nat.minFac_dvd _
  rw [hNstr_eq, show OddOrder.BG.Ch4.S16.FT_signalizerBase z = MulAut.conj g⁻¹ • S from by
      rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul],
    tau2_conj_smul'] at hp₀tau2
  exact htau2S p₀ hp₀p hp₀tau2

/-- **The `w ∈ M_σ^#` form of `escaping_sigmaSharp_disjoint_centralizer_of_witness`**: a point of
`M_σ^#` is its own centralizing witness. -/
theorem escaping_sigmaSharp_disjoint_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hS : S ∈ maximalSubgroups G)
    {z : G} (hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S)
    (hzesc : ¬ Subgroup.centralizer ({z} : Set G) ≤ S)
    {w : G} (hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma S) (hw1 : w ≠ 1)
    {p : ℕ} (hpp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z))
    (hpC : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) : False :=
  escaping_sigmaSharp_disjoint_centralizer_of_witness hG hS hσz hzesc
    (OddOrder.BG.Ch3.S10.Msigma_le S hwMσ) hw1 ⟨w, hwMσ, hw1, Commute.refl w⟩ hpp hpσ hpC

/-- **The (8.13.c2) coprimality core**: for an escaping point `z` of the type-I support `A(S)`,
no prime of `σ(N[z])` (`N[z] = FT_signalizerBase z` the supporting maximal) divides `|C_S(w)|`
for any `w ∈ A(S)`.

BG Theorem II conjunct (c): a common prime `p ∈ σ(N[z]) ∩ π(C_S(w)) ⊆ σ(N[z]) ∩ π(S)` fires
Lemma 14.13(a) (`non_disjoint_signalizer_frobenius`), making `S` a Frobenius group with kernel
`S_σ` and `τ₂(S) = ∅`.  The Frobenius kernel absorbs centralizers
(`IsFrobeniusGroup.centralizer_kernel_le`): the `A(S)`-point `w` centralizes a nontrivial
element of `S_F = S_σ`, so `w ∈ S_σ`, and a Cauchy `p`-element of `C_S(w)` then also lies in
`S_σ`, giving `p ∈ σ(S)`.  Now `σ(N[z]) ∩ σ(S) ≠ ∅` forces `N[z]` conjugate to `S` (Theorem
13.9, `sigma_disjoint_of_nonconjugate`), transporting `τ₂(N[z]) ∋ π(⟨z⟩) ≠ ∅`
(`signalizer_structure_of_mem_sigmaSharp`) onto `τ₂(S) = ∅` — contradiction. -/
theorem escaping_sigma_disjoint_centralizer [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {S : Subgroup G}
    (hS : S ∈ maximalSubgroups G) (dS : TypeIData S)
    {z : G} (hz : z ∈ OddOrder.GroupTheory.escapingCentralizerSet S (typeIA S dS))
    {w : G} (hw : w ∈ typeIA S dS) {p : ℕ} (hpp : p.Prime)
    (hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase z))
    (hpC : p ∣ Nat.card (OddOrder.Peterfalvi.S04.centralizerIn S w)) : False := by
  classical
  obtain ⟨hzA, hzesc⟩ := hz
  have hz1 : z ≠ 1 := hzA.2.1
  -- `z` is σ-sharp with more than one σ-maximal.
  have hκ : OddOrder.BG.Ch4.S14.kappa S = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hS).mp ⟨dS⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa S)
      ((⊥ : Subgroup G).subgroupOf S) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro q _
    rw [hκ]
    exact Set.notMem_empty q
  have hσz : z ∈ OddOrder.BG.Ch4.S14.sigmaSharp S :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hS bot_le dS.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hS dS) (Or.inl rfl)
      (typeIA_subset_ASet hG hS dS hzA) hz1 hzesc
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement z).ncard := by
    by_contra h
    exact hzesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hS hσz.1 hz1
      (not_lt.mp h))
  -- `p ∈ π(S)` (it divides `|C_S(w)| ∣ |S|`), so Lemma 14.13(a) fires.
  have hpS : p ∈ OddOrder.BG.Ch4.S14.piSet S := by
    refine Nat.mem_primeFactors.mpr ⟨hpp, hpC.trans ?_, Nat.card_pos.ne'⟩
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨-, -, U, -, hfrobU⟩ :=
    OddOrder.BG.Ch4.S16.non_disjoint_signalizer_frobenius hG hS hσz hgt ⟨p, hpσ, hpS⟩
  -- Frobenius kernel absorption: commuting with a nontrivial `S_σ`-element lands in `S_σ`.
  have hker : ∀ {u v : G}, u ∈ S → v ∈ OddOrder.BG.Ch3.S10.Msigma S → v ≠ 1 →
      Commute u v → u ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    intro u v huS hvMσ hv1 hcomm
    have hvS : v ∈ S := OddOrder.BG.Ch3.S10.Msigma_le S hvMσ
    have hcent := OddOrder.Isaacs.Ch06.IsFrobeniusGroup.centralizer_kernel_le hfrobU
      (⟨v, hvS⟩ : ↥S) (Subgroup.mem_subgroupOf.mpr hvMσ)
      (fun h1 => hv1 (congrArg Subtype.val h1))
    have humem : (⟨u, huS⟩ : ↥S) ∈
        Subgroup.centralizer ({(⟨v, hvS⟩ : ↥S)} : Set ↥S) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext hcomm.eq
    exact Subgroup.mem_subgroupOf.mp (hcent humem)
  -- `w ∈ S_σ`: it centralizes a nontrivial element of `S_F = S_σ` (type-`F` absorption).
  have hMFMσ : maxNilpotentNormalHall S = OddOrder.BG.Ch3.S10.Msigma S :=
    OddOrder.Peterfalvi.S10Interface.maxNilpotentNormalHall_eq_Msigma_of_typeI_or_II
      hG hS (Or.inl ⟨dS⟩)
  obtain ⟨hwS, hw1, h, hh, hwC⟩ := hw
  obtain ⟨hhH, hh1⟩ := (Set.mem_sdiff _).mp hh
  have hh1' : h ≠ 1 := fun he => hh1 (Set.mem_singleton_iff.mpr he)
  have hhMσ : h ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    rw [← hMFMσ, ← dS.typeF.H_eq]
    exact SetLike.mem_coe.mp hhH
  have hwMσ : w ∈ OddOrder.BG.Ch3.S10.Msigma S := by
    refine hker hwS hhMσ hh1' ?_
    exact Subgroup.mem_centralizer_singleton_iff.mp hwC
  -- the remaining `σ`-generic contradiction is the shared coprimality core.
  exact escaping_sigmaSharp_disjoint_centralizer hG hS hσz hzesc hwMσ hw1 hpp hpσ hpC

/-- **Peterfalvi (8.13.c1) at a `σ`-sharp escaping point** — the `σ`-decomposition-generic core of
`escaping_typeIA_signalizer_structure`, shared by every Peterfalvi type.  For `a ∈ M_σ^#` with
`C_G(a) ⊄ M`, the signalizer `R(a) = FT_signalizer a` gives `C_G(a) = R(a) ⋊ C_M(a)`:
- join `C_G(a) = R(a) ⊔ C_M(a)`, disjointness `R(a) ⊓ C_M(a) = ⊥`, and normality of `R(a)` in
`C_G(a)`.

The escaping hypothesis forces `1 < |𝓜_σ(a)|` (`centralizer_le_of_maximalSigma_le_one`), so the
supporting maximal is pinned (`N[a] = FT_signalizerBase a`, singleton uniqueness) and Theorem D(3)'s
complement structure at `M ∈ 𝓜_σ(a)` (`signalizer_structure_of_mem_sigmaSharp` →
`signalizer_centralizer_isComplement`) supplies the split, with normality from
`FT_signalizer_normal_in_centralizer`.  The type-specific (8.13.c2) coprimality conjunct is *not*
included here — it is proved per type (`escaping_sigma_disjoint_centralizer` for type I). -/
theorem escaping_sigmaSharp_signalizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {a : G}
    (hσa : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M)
    (haesc : ¬ Subgroup.centralizer ({a} : Set G) ≤ M) :
    Subgroup.centralizer ({a} : Set G)
        = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
      Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
        (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
      (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
        c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) := by
  classical
  have ha1 : a ≠ 1 := hσa.2
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    exact haesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσa.1 ha1
      (not_lt.mp h))
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσa haesc
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)),
      L = N₀ := by
    intro L hL
    rw [hN₀, Set.mem_singleton_iff] at hL
    exact hL
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase a = N₀ := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase a = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  obtain ⟨Nstr, ⟨hNstr_max, hNstr_C, -, -, -, -, hNstr_all⟩, -⟩ :=
    OddOrder.BG.Ch4.S16.signalizer_structure_of_mem_sigmaSharp hG hM hσa hgt
  have hNstr_eq : Nstr = N₀ :=
    huniq Nstr (mem_maximalSubgroupsContaining.mpr ⟨hNstr_max, hNstr_C⟩)
  have hM𝓜 : M ∈ OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a := ⟨hM, hσa.1⟩
  obtain ⟨-, -, hMcompl, -⟩ := hNstr_all M hM𝓜
  have hCN₀ : Subgroup.centralizer ({a} : Set G) ≤ N₀ := hNstr_eq ▸ hNstr_C
  have haM : a ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hσa.1
  have hcompl := OddOrder.BG.Ch4.S16.signalizer_centralizer_isComplement
    (hNstr_eq ▸ hMcompl) hCN₀ haM
  have hRdef : OddOrder.BG.Ch4.S16.FT_signalizer a
      = OddOrder.BG.Ch3.S10.Msigma N₀ ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [OddOrder.BG.Ch4.S16.FT_signalizer, hbase]
  have hRle : OddOrder.BG.Ch4.S16.FT_signalizer a ≤ Subgroup.centralizer ({a} : Set G) :=
    OddOrder.BG.Ch4.S16.FT_signalizer_le_centralizer a
  have hCMle : OddOrder.Peterfalvi.S04.centralizerIn M a ≤
      Subgroup.centralizer ({a} : Set G) := inf_le_right
  refine ⟨?_, ?_, ?_⟩
  · refine le_antisymm ?_ (sup_le hRle hCMle)
    intro c hc
    obtain ⟨⟨u, v⟩, huv, -⟩ := Subgroup.IsComplement.existsUnique hcompl
      (⟨c, hc⟩ : ↥(Subgroup.centralizer ({a} : Set G)))
    have hcval : ((u : ↥(Subgroup.centralizer ({a} : Set G))) : G) *
        ((v : ↥(Subgroup.centralizer ({a} : Set G))) : G) = c := by
      simpa using congrArg (fun z : ↥(Subgroup.centralizer ({a} : Set G)) => (z : G)) huv
    have hu : ((u : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈
        OddOrder.Peterfalvi.S04.centralizerIn M a := by
      have hu' := Subgroup.mem_subgroupOf.mp u.2
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hu').1,
        SetLike.coe_mem (u : ↥(Subgroup.centralizer ({a} : Set G)))⟩
    have hv : ((v : ↥(Subgroup.centralizer ({a} : Set G))) : G) ∈
        OddOrder.BG.Ch4.S16.FT_signalizer a := by
      have hv' := Subgroup.mem_subgroupOf.mp v.2
      rw [hRdef]
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hv').1,
        SetLike.coe_mem (v : ↥(Subgroup.centralizer ({a} : Set G)))⟩
    rw [← hcval]
    exact mul_mem (Subgroup.mem_sup_right hu) (Subgroup.mem_sup_left hv)
  · rw [disjoint_iff, eq_bot_iff]
    intro y hy
    obtain ⟨hyR, hyC⟩ := Subgroup.mem_inf.mp hy
    have hyc : y ∈ Subgroup.centralizer ({a} : Set G) := hRle hyR
    have hymem : (⟨y, hyc⟩ : ↥(Subgroup.centralizer ({a} : Set G))) ∈
        ((M ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf
          (Subgroup.centralizer ({a} : Set G))) ⊓
        ((OddOrder.BG.Ch3.S10.Msigma N₀ ⊓
          Subgroup.centralizer ({a} : Set G)).subgroupOf
          (Subgroup.centralizer ({a} : Set G))) := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mpr hyC,
        Subgroup.mem_subgroupOf.mpr ?_⟩
      exact hRdef ▸ hyR
    have hybot := hcompl.disjoint.le_bot hymem
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp hybot))
  · intro c hc y hy
    have hnorm := OddOrder.BG.Ch4.S16.FT_signalizer_normal_in_centralizer hbr hc
    exact (Subgroup.mem_normalizer_iff.mp hnorm y).mp hy

/-- **Peterfalvi (8.13.c1/c2) at an escaping point of the type-I support** (BG §16 Theorem II +
Theorem D(3)/(4); Coq `FTsupport_facts` part c).  For escaping `a ∈ A(M)` (`C_G(a) ⊄ M`), with
`R(a) = FT_signalizer a` the supporting-maximal signalizer:
- (8.13.c1) `C_G(a) = R(a) ⋊ C_M(a)` — join, disjointness, and normality of `R(a)`;
- (8.13.c2) `|R(a)|` is coprime to `|C_M(b)|` for every `b ∈ A(M)`.

Assembly: the escaping point is `σ`-sharp with more than one `σ`-maximal (the (8.13.b)
machinery), so the supporting maximal is the pinned `N[a] = FT_signalizerBase a` and Theorem
D(3) supplies the complement structure — `signalizer_centralizer_isComplement` fed by the
`N`-complement of `signalizer_structure_of_mem_sigmaSharp` at `M ∈ 𝓜_σ(a)` — while the
normality is `FT_signalizer_normal_in_centralizer`.  (c2): a prime of `|R(a)|` divides
`|(N[a])_σ|`, so it lies in `σ(N[a])` and the coprimality core
`escaping_sigma_disjoint_centralizer` (BG Lemma 14.13(a) route) applies. -/
theorem escaping_typeIA_signalizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (data : TypeIData M)
    {a : G} (ha : a ∈ OddOrder.GroupTheory.escapingCentralizerSet M (typeIA M data)) :
    Subgroup.centralizer ({a} : Set G)
        = OddOrder.BG.Ch4.S16.FT_signalizer a ⊔ OddOrder.Peterfalvi.S04.centralizerIn M a ∧
      Disjoint (OddOrder.BG.Ch4.S16.FT_signalizer a)
        (OddOrder.Peterfalvi.S04.centralizerIn M a) ∧
      (∀ c ∈ Subgroup.centralizer ({a} : Set G), ∀ y ∈ OddOrder.BG.Ch4.S16.FT_signalizer a,
        c * y * c⁻¹ ∈ OddOrder.BG.Ch4.S16.FT_signalizer a) ∧
      (∀ b ∈ typeIA M data,
        Nat.Coprime (Nat.card (OddOrder.BG.Ch4.S16.FT_signalizer a))
          (Nat.card (OddOrder.Peterfalvi.S04.centralizerIn M b))) := by
  classical
  obtain ⟨haA, haesc⟩ := ha
  have ha1 : a ≠ 1 := haA.2.1
  -- `a` is σ-sharp with more than one σ-maximal (the (8.13.b) machinery).
  have hκ : OddOrder.BG.Ch4.S14.kappa M = ∅ :=
    (OddOrder.Peterfalvi.S10Interface.isTypeI_iff_isTypeF hG hM).mp ⟨data⟩
  have hK : OddOrder.Isaacs.Ch03.IsHallSubgroup (OddOrder.BG.Ch4.S14.kappa M)
      ((⊥ : Subgroup G).subgroupOf M) := by
    rw [Subgroup.bot_subgroupOf, OddOrder.Isaacs.Ch03.IsHallSubgroup.bot_iff]
    intro q _
    rw [hκ]
    exact Set.notMem_empty q
  have hσa : a ∈ OddOrder.BG.Ch4.S14.sigmaSharp M :=
    OddOrder.BG.Ch4.S16.mem_sigmaSharp_of_mem_aSet_of_escape hG hM bot_le data.typeF.U_le hK
      (typeF_complement_isHall_kappa_sigma_compl hG hM data) (Or.inl rfl)
      (typeIA_subset_ASet hG hM data haA) ha1 haesc
  have hgt : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard := by
    by_contra h
    exact haesc (OddOrder.BG.Ch4.S16.centralizer_le_of_maximalSigma_le_one hG hM hσa.1 ha1
      (not_lt.mp h))
  -- singleton uniqueness pins the supporting maximal, identifying the base of `R(a)`.
  obtain ⟨N₀, hN₀⟩ :=
    OddOrder.BG.Ch4.S16.maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
      hG hM hσa haesc
  have huniq : ∀ L ∈ maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G)),
      L = N₀ := by
    intro L hL
    rw [hN₀, Set.mem_singleton_iff] at hL
    exact hL
  have hbr : 1 < (OddOrder.BG.Ch4.S14.maximalSigmaSubgroupsOfElement a).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({a} : Set G))).Nonempty :=
    ⟨hgt, ⟨N₀, by rw [hN₀]; rfl⟩⟩
  have hbase : OddOrder.BG.Ch4.S16.FT_signalizerBase a = N₀ := by
    have hb : OddOrder.BG.Ch4.S16.FT_signalizerBase a = hbr.2.choose := dif_pos hbr
    rw [hb]
    exact huniq _ hbr.2.choose_spec
  -- unfold `R(a) = (N₀)_σ ⊓ C_G(a)` for the coprimality step.
  have hRdef : OddOrder.BG.Ch4.S16.FT_signalizer a
      = OddOrder.BG.Ch3.S10.Msigma N₀ ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [OddOrder.BG.Ch4.S16.FT_signalizer, hbase]
  -- (8.13.c1) join/disjoint/normal is the `σ`-decomposition-generic complement structure.
  obtain ⟨hjoin, hdisj, hnormc⟩ :=
    escaping_sigmaSharp_signalizer_structure hG hM hσa haesc
  refine ⟨hjoin, hdisj, hnormc, ?_⟩
  · -- (c2): primes of `|R(a)|` lie in `σ(N[a])`; apply the coprimality core.
    intro b hb
    by_contra hnc
    obtain ⟨p, hpp, hpR, hpC⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
    have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma (OddOrder.BG.Ch4.S16.FT_signalizerBase a) := by
      rw [hbase]
      refine OddOrder.BG.Ch3.S10.Msigma_isPiGroup N₀ p (Nat.mem_primeFactors.mpr
        ⟨hpp, ?_, Nat.card_pos.ne'⟩)
      refine hpR.trans (Subgroup.card_dvd_of_le ?_)
      rw [hRdef]
      exact inf_le_left
    exact escaping_sigma_disjoint_centralizer hG hM data ⟨haA, haesc⟩ hb hpp hpσ hpC

end OddOrder.Peterfalvi.S10


