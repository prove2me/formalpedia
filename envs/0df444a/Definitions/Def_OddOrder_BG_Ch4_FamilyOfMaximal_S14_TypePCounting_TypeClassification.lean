-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypeClassification
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_TypeClassification
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:04:48.488303+00:00
-- url     : https://prove2.me/theorems/3e38783a-79be-49a5-99be-51a96be30156
-- title:
--   BG §14: notation and the type classification layer
-- statement:
--   The split-extension derived-subgroup helper, the §14 notation of Bender–Glauberman, *Local Analysis for the Odd Order Theorem* ($\kappa(M)$, type-$\mathcal{P}$ families, $\sigma$-length) and the basic type-classification relations.
--
--   Main declarations: `piSet` (The set of prime divisors of a finite subgroup, used as BG's `pi(M)`); `sigmaComplementPrimes` (BG `pi(M) - sigma(M)`, as a set of natural primes); `kappa`; `IsTypeP` (BG `M_P`: maximal subgroups with nonempty `kappa(M)`); and 5 more.
--
--   The bundle also proves 19 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/TypeClassification.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/TypeClassification.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeAction
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S13_PrimeActionTransition
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem125
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1211
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Lemma1217
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S14_Prop142Support
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03c_Thm37
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_S03g_Thm310
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupTypeConj
import Definitions.Def_OddOrder_GroupTheory_PiElementDecomposition

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped commutatorElement in
/-- **Derived subgroup of a split extension**: if `N ⊴ H` has a complement `E`
(`H = N ⋊ E`) and `N ≤ H'`, then `H' = N ⊔ ⁅E, E⁆`.

`N ⊔ ⁅E,E⁆ ≤ H'` is immediate (`N ≤ H'` by hypothesis, `⁅E,E⁆ ≤ ⁅⊤,⊤⁆ = H'`).  For
`H' ≤ N ⊔ ⁅E,E⁆`, every commutator `⁅n₁e₁, n₂e₂⁆` is congruent mod `N` to `⁅e₁,e₂⁆ ∈ ⁅E,E⁆`
(pushing through `H ↠ H/N` kills the `N`-factors), and `N ⊴ H` makes `N · ⁅E,E⁆` a subgroup. -/
theorem commutator_eq_sup_commutator_of_isComplement' {H : Type*} [Group H]
    {N E : Subgroup H} [N.Normal] (hcompl : N.IsComplement' E)
    (hNle : N ≤ commutator H) :
    commutator H = N ⊔ ⁅E, E⁆ := by
  have hsup : N ⊔ E = ⊤ := hcompl.sup_eq_top
  refine le_antisymm ?_ (sup_le hNle ?_)
  · -- `H' = ⁅⊤,⊤⁆ ≤ N ⊔ ⁅E,E⁆`.
    rw [commutator_def, ← hsup, Subgroup.commutator_le]
    intro a ha b hb
    -- Decompose `a = n₁ e₁`, `b = n₂ e₂` using `N ⊴ H`.
    obtain ⟨n₁, hn₁, e₁, he₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp ha
    obtain ⟨n₂, hn₂, e₂, he₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hb
    -- `⁅n₁e₁, n₂e₂⁆ ≡ ⁅e₁,e₂⁆  (mod N)`, via `H ↠ H/N`.
    have hmod : ⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹ ∈ N := by
      have hf₁ : (QuotientGroup.mk' N) n₁ = 1 := (QuotientGroup.eq_one_iff n₁).mpr hn₁
      have hf₂ : (QuotientGroup.mk' N) n₂ = 1 := (QuotientGroup.eq_one_iff n₂).mpr hn₂
      have key : (QuotientGroup.mk' N) (⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹) = 1 := by
        simp only [map_mul, map_inv, map_commutatorElement, hf₁, hf₂, one_mul, mul_inv_cancel]
      exact (QuotientGroup.eq_one_iff _).mp (by rwa [QuotientGroup.mk'_apply] at key)
    -- `⁅n₁e₁, n₂e₂⁆ = (⁅n₁e₁,n₂e₂⁆ ⁅e₁,e₂⁆⁻¹) · ⁅e₁,e₂⁆ ∈ N · ⁅E,E⁆ ⊆ N ⊔ ⁅E,E⁆`.
    have heq : ⁅n₁ * e₁, n₂ * e₂⁆ = (⁅n₁ * e₁, n₂ * e₂⁆ * ⁅e₁, e₂⁆⁻¹) * ⁅e₁, e₂⁆ := by
      group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmod)
      (Subgroup.mem_sup_right (Subgroup.commutator_mem_commutator he₁ he₂))
  · -- `⁅E,E⁆ ≤ ⁅⊤,⊤⁆ = H'`.
    rw [commutator_def]
    exact Subgroup.commutator_mono le_top le_top

/-- The set of prime divisors of a finite subgroup, used as BG's `pi(M)`. -/
def piSet (M : Subgroup G) : Set ℕ :=
  {p | p ∈ (Nat.card ↥M).primeFactors}

/-- BG `pi(M) - sigma(M)`, as a set of natural primes. -/
def sigmaComplementPrimes (M : Subgroup G) : Set ℕ :=
  piSet M \ OddOrder.BG.Ch3.S10.sigma M

/-- **BG `kappa(M)`** (mmd L3760): primes in `tau_1(M) ∪ tau_3(M)` for which
some rank-one elementary abelian `p`-subgroup has nontrivial centralizer in
`M_sigma`. -/
def kappa (M : Subgroup G) : Set ℕ :=
  {p | p.Prime ∧ p ∈ tau1 M ∪ tau3 M ∧
    ∃ P : Subgroup G, P ∈ elemAbelianOfRank G p 1 ∧ P ≤ M ∧
      OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥}

/-- **BG `M_P`**: maximal subgroups with nonempty `kappa(M)`. -/
def IsTypeP (M : Subgroup G) : Prop :=
  (kappa M).Nonempty

/-- **BG `M_P1`**: type-P maximal subgroups with maximal `kappa(M)`. -/
def IsTypeP1 (M : Subgroup G) : Prop :=
  IsTypeP M ∧ kappa M = sigmaComplementPrimes M

/-- **BG `M_P2`**: type-P maximal subgroups whose `kappa(M)` is a proper subset. -/
def IsTypeP2 (M : Subgroup G) : Prop :=
  IsTypeP M ∧ kappa M ≠ sigmaComplementPrimes M

/-- **BG `M_F` family**: the Frobenius-type maximal subgroups, i.e. `kappa(M)=empty`. -/
def IsTypeF (M : Subgroup G) : Prop :=
  kappa M = ∅

theorem isTypeP_of_isTypeP1 {M : Subgroup G} (h : IsTypeP1 M) : IsTypeP M := h.1

theorem isTypeP_of_isTypeP2 {M : Subgroup G} (h : IsTypeP2 M) : IsTypeP M := h.1

/-- The type-`P` maximal subgroups split as the (disjoint) union of `M_P1` and `M_P2`. -/
theorem isTypeP_iff_isTypeP1_or_isTypeP2 {M : Subgroup G} :
    IsTypeP M ↔ IsTypeP1 M ∨ IsTypeP2 M := by
  constructor
  · intro hP
    by_cases h : kappa M = sigmaComplementPrimes M
    · exact Or.inl ⟨hP, h⟩
    · exact Or.inr ⟨hP, h⟩
  · rintro (h | h) <;> exact h.1

/-- `M_P1` and `M_P2` are disjoint: `kappa(M)` cannot both equal and differ from `π(M)∖σ(M)`. -/
theorem not_isTypeP1_and_isTypeP2 {M : Subgroup G} : ¬ (IsTypeP1 M ∧ IsTypeP2 M) := by
  rintro ⟨⟨_, h1⟩, _, h2⟩
  exact h2 h1

/-- `M_F` (Frobenius type) is exactly the complement of `M_P` (type `P`). -/
theorem isTypeF_iff_not_isTypeP {M : Subgroup G} : IsTypeF M ↔ ¬ IsTypeP M := by
  simp only [IsTypeF, IsTypeP, Set.not_nonempty_iff_eq_empty]

/-- A maximal subgroup is not simultaneously type `P` and Frobenius type. -/
theorem not_isTypeP_and_isTypeF {M : Subgroup G} : ¬ (IsTypeP M ∧ IsTypeF M) := by
  rintro ⟨hP, hF⟩
  exact (isTypeF_iff_not_isTypeP.mp hF) hP

/-- `κ(M) ⊆ τ₁(M) ∪ τ₃(M)`, directly from the definition of `κ`.  Used in Proposition 14.2:
a Hall `κ(M)`-subgroup is a `σ(M)'`-subgroup (since `τ₁, τ₃ ⊆ σ(M)'`), so the §12 `E`-setup
may be chosen to contain it. -/
theorem kappa_subset_tau1_union_tau3 {M : Subgroup G} : kappa M ⊆ tau1 M ∪ tau3 M :=
  fun _ hp => hp.2.1

/-- Every prime in `κ(M)` is prime (recorded explicitly in the definition). -/
theorem prime_of_mem_kappa {M : Subgroup G} {p : ℕ} (hp : p ∈ kappa M) : p.Prime := hp.1

/-- `κ(M) ⊆ σ(M)'`: a Hall `κ(M)`-subgroup is a `σ(M)'`-subgroup (since `τ₁, τ₃ ⊆ σ(M)'`).
This lets Proposition 14.2 feed a Hall `κ(M)`-subgroup `K` to `exists_subgroupESetup_with_le`
to obtain an `E`-setup with `K ≤ E`. -/
theorem kappa_subset_sigmaCompl {M : Subgroup G} : kappa M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := by
  intro p hp
  rcases kappa_subset_tau1_union_tau3 hp with h | h
  · exact ((mem_tau1_iff M p).mp h).1
  · exact ((mem_tau3_iff M p).mp h).1

/-- `κ(M) ⊆ π(M) ∖ σ(M)` (`sigmaComplementPrimes M`): a `κ`-prime divides `|M|` (it carries a
rank-one elementary abelian witness `P ≤ M` of order `p`) and lies outside `σ(M)`
(`kappa_subset_sigmaCompl`). -/
theorem kappa_subset_sigmaComplementPrimes [Finite G] {M : Subgroup G} :
    kappa M ⊆ sigmaComplementPrimes M := by
  intro p hpκ
  have hpsig : p ∈ (OddOrder.BG.Ch3.S10.sigma M)ᶜ := kappa_subset_sigmaCompl hpκ
  obtain ⟨hpp, _, P, hPelem, hPM, _⟩ := hpκ
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  exact ⟨Nat.mem_primeFactors.mpr ⟨hpp, hPcard ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩,
    hpsig⟩

/-- In a §12 `E`-setup, if the `σ(M)'`-complement `E` is a `κ(M)`-group (every prime divisor of
`|E|` lies in `κ(M)`), then `M` is type-`P₁`: `κ(M) = π(M) ∖ σ(M)`.  `E` is a `σ(M)'`-Hall, so it
carries every `σ(M)'`-prime of `M`; combined with `κ(M) ⊆ π(M) ∖ σ(M)` this forces equality.
Used to exclude the degenerate cases (`κ(M) ∩ τ₃(M) ≠ ∅`, or `E₂E₃ = 1`) when building the
matched `κ`-complement of a type-`P₂` maximal subgroup. -/
theorem kappa_eq_sigmaComplementPrimes_of_isPiGroup_card_E [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (hEκ : ∀ p ∈ (Nat.card ↥E).primeFactors, p ∈ kappa M) :
    kappa M = sigmaComplementPrimes M := by
  refine le_antisymm kappa_subset_sigmaComplementPrimes (fun p hp => ?_)
  obtain ⟨hpπ, hpσ⟩ := hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hpπ
  have hpM : p ∣ Nat.card ↥M := Nat.dvd_of_mem_primeFactors hpπ
  -- `p ∤ |M_σ|` (`M_σ` is a `σ(M)`-group and `p ∉ σ(M)`).
  have hpMσ : ¬ p ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hd =>
    hpσ (OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p
      (Nat.mem_primeFactors.mpr ⟨hpp, hd, Nat.card_pos.ne'⟩))
  -- `p ∣ |E|` from `|M_σ| · |E| = |M|`.
  have hcardM := h.card_Msigma_mul_card_E
  have hpE : p ∣ Nat.card ↥E :=
    (hpp.dvd_mul.mp (hcardM ▸ hpM)).resolve_left hpMσ
  exact hEκ p (Nat.mem_primeFactors.mpr ⟨hpp, hpE, Nat.card_pos.ne'⟩)

/-- **`M`-conjugacy invariance of the `κ`-witness condition**: for `m ∈ M`, since `M_σ ◁ M`,
conjugation by `m` carries `M_σ ⊓ C_G(P)` to `M_σ ⊓ C_G(P^m)`, so `C_{M_σ}(P) ≠ 1` implies
`C_{M_σ}(P^m) ≠ 1`.  Used in Proposition 14.2 to transport the `κ(M)`-witness across
`M`-conjugacy (the `∃ → ∀` upgrade of BG L3807 and the WLOG `K = E₁`). -/
theorem Msigma_inf_centralizer_conj_ne_bot {M P : Subgroup G} {m : G} (hmM : m ∈ M)
    (h : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj m • P : Subgroup G) : Set G) ≠ ⊥ := by
  have hmN : m ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma M) :=
    le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M hmM
  obtain ⟨⟨x, hxmem⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  rw [Subgroup.mem_inf] at hxmem
  obtain ⟨hxMσ, hxC⟩ := hxmem
  rw [Subgroup.ne_bot_iff_exists_ne_one]
  refine ⟨⟨m * x * m⁻¹, Subgroup.mem_inf.mpr
    ⟨(Subgroup.mem_normalizer_iff.mp hmN x).mp hxMσ, ?_⟩⟩, ?_⟩
  · -- `m x m⁻¹` centralizes `P^m`: write `y ∈ P^m` as `y = m (m⁻¹ y m) m⁻¹` with `m⁻¹ y m ∈ P`,
    -- which `x` centralizes.
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy
    have hyval : (MulAut.conj m)⁻¹ • y = m⁻¹ * y * m := by
      rw [inv_smul_eq_iff]
      change y = MulAut.conj m (m⁻¹ * y * m)
      rw [MulAut.conj_apply]; group
    rw [hyval] at hy
    have hcomm : (m⁻¹ * y * m) * x = x * (m⁻¹ * y * m) :=
      (Subgroup.mem_centralizer_iff.mp hxC) _ hy
    calc y * (m * x * m⁻¹)
        = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by group
      _ = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by rw [hcomm]
      _ = (m * x * m⁻¹) * y := by group
  · -- `m x m⁻¹ ≠ 1` since `x ≠ 1`.
    intro hc
    apply hx1
    have hxe : m * x * m⁻¹ = 1 := by simpa using congrArg Subtype.val hc
    refine Subtype.ext ?_
    have hconj : m * x * m⁻¹ = m * 1 * m⁻¹ := by rw [hxe]; group
    exact mul_left_cancel (mul_right_cancel hconj)

open OddOrder.BG.Ch3.S13 in
/-- In a §12 `E`-setup, a prime `p ∈ κ(M) ∩ τ₃(M)` forces `E₃ ≠ 1` and makes `E₃` act
non-regularly on `M_σ`: the `κ`-witness `P ∈ ℰ_p¹(M)` (with `C_{M_σ}(P) ≠ 1`) is `M`-conjugate
into the Hall `τ₃`-piece `E₃` (`exists_conj_smul_le_hallPiece`), and `M_σ`-centralizer
nontriviality transports along the conjugacy (`Msigma_inf_centralizer_conj_ne_bot`).  This is
the entry to BG Proposition 14.2's `κ ∩ τ₃ ≠ ∅` case (which then invokes Corollary 13.11). -/
theorem E3_not_regular_of_mem_kappa_tau3 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) (hpκ : p ∈ kappa M) (hpτ3 : p ∈ tau3 M) :
    E₃ ≠ ⊥ ∧ ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₃ := by
  obtain ⟨_, _, P, hPelem, hPM, hPC⟩ := hpκ
  have : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  have hPpi : Ch03.Subgroup.IsPiGroup (tau3 M) (P.subgroupOf M) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard,
      hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ3
  have hπσ : tau3 M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    fun q hq => ((mem_tau3_iff M q).mp hq).1
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG h h.E₃_le h.E₃_hall hπσ hPM hPpi
  have hPwC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≠ ⊥ :=
    Msigma_inf_centralizer_conj_ne_bot hwM hPC
  have hPwne : (MulAut.conj w • P : Subgroup G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one (conj_smul_mem_elemAbelianOfRank w hPelem)
  obtain ⟨⟨z, hzPw⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPwne
  have hz1' : z ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hzE3 : z ∈ E₃ := hwle hzPw
  refine ⟨fun hE3bot => hz1' (Subgroup.mem_bot.mp (hE3bot ▸ hzE3)), ?_⟩
  intro hreg
  have hzfix := hreg z hzE3 hz1'
  rw [fixedByElement] at hzfix
  apply hPwC
  rw [eq_bot_iff, ← hzfix]
  refine inf_le_inf_left _ ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact ha z hzPw

/-- **BG Proposition 14.2's `κ(M) ⊆ τ₁(M)` case entry** (mirror of
`E3_not_regular_of_mem_kappa_tau3`):
a prime `p ∈ κ(M) ∩ τ₁(M)` forces `E₁ ≠ 1` and makes `E₁` act non-regularly on `M_σ` (the
`κ`-witness `P ∈ ℰ_p¹(M)` is `M`-conjugate into the Hall `τ₁`-piece `E₁`, transporting
`C_{M_σ}` nontriviality).  Feeds `κ(M) = τ₁(M)` and the `K^* ≠ 1` conjunct of case `τ₁`. -/
theorem E1_not_regular_of_mem_kappa_tau1 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} (hp : p.Prime) (hpκ : p ∈ kappa M) (hpτ1 : p ∈ tau1 M) :
    E₁ ≠ ⊥ ∧ ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₁ := by
  obtain ⟨_, _, P, hPelem, hPM, hPC⟩ := hpκ
  have : Fact p.Prime := ⟨hp⟩
  have hPcard : Nat.card ↥P = p := by rw [(mem_elemAbelianOfRank.mp hPelem).2, pow_one]
  have hPpi : Ch03.Subgroup.IsPiGroup (tau1 M) (P.subgroupOf M) := by
    intro q hq
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPM).toEquiv, hPcard,
      hp.primeFactors, Finset.mem_singleton] at hq
    exact hq ▸ hpτ1
  have hπσ : tau1 M ⊆ (OddOrder.BG.Ch3.S10.sigma M)ᶜ :=
    fun q hq => ((mem_tau1_iff M q).mp hq).1
  obtain ⟨w, hwM, hwle⟩ :=
    exists_conj_smul_le_hallPiece hG h h.E₁_le h.E₁_hall hπσ hPM hPpi
  have hPwC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer ((MulAut.conj w • P : Subgroup G) : Set G) ≠ ⊥ :=
    Msigma_inf_centralizer_conj_ne_bot hwM hPC
  have hPwne : (MulAut.conj w • P : Subgroup G) ≠ ⊥ :=
    ne_bot_of_mem_elemAbelianOfRank_one (conj_smul_mem_elemAbelianOfRank w hPelem)
  obtain ⟨⟨z, hzPw⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPwne
  have hz1' : z ≠ 1 := fun hc => hz1 (Subtype.ext hc)
  have hzE1 : z ∈ E₁ := hwle hzPw
  refine ⟨fun hE1bot => hz1' (Subgroup.mem_bot.mp (hE1bot ▸ hzE1)), ?_⟩
  intro hreg
  have hzfix := hreg z hzE1 hz1'
  rw [fixedByElement] at hzfix
  apply hPwC
  rw [eq_bot_iff, ← hzfix]
  refine inf_le_inf_left _ ?_
  intro a ha
  rw [Subgroup.mem_centralizer_iff] at ha ⊢
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  rw [hg]
  exact ha z hzPw

/-- **Global `M_σ`-fixed point from prime action + a single non-regular point** (BG
Proposition 14.2, `κ(M) ∩ τ₃(M) ≠ ∅` case): if `E` acts in a prime manner on `M_σ` and some
`E₃ ≤ E` does not act regularly (a witness `x ∈ E₃#` has `C_{M_σ}(x) ≠ 1`), then prime action
collapses `C_{M_σ}(x) = C_{M_σ}(E)` for every `x ∈ E#`, so `C_{M_σ}(E) ≠ 1`.

Once `K = E` this is the conjunct `K^* = C_{M_σ}(K) ≠ 1`.  It also drives the `κ(M) ⊇ π(E)`
step of `K = E`: for each prime `p ∣ |E|`, a rank-one `P ≤ E` of order `p` has, by prime
action, `C_{M_σ}(P) = C_{M_σ}(E) ≠ 1`, so `p ∈ κ(M)`. -/
theorem Msigma_inf_centralizer_E_ne_bot_of_actsPrime_nonregular {M E E₃ : Subgroup G}
    (hEprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E) (hE3le : E₃ ≤ E)
    (hreg : ¬ ActsRegularlyOn (OddOrder.BG.Ch3.S10.Msigma M) E₃) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
  -- A non-regular witness `x ∈ E₃#` with `C_{M_σ}(x) ≠ 1`.
  have hxex : ∃ x ∈ E₃, x ≠ 1 ∧
      fixedByElement (OddOrder.BG.Ch3.S10.Msigma M) x ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    exact hreg fun x hx hx1 => hcon x hx hx1
  obtain ⟨x, hxE3, hx1, hxfix⟩ := hxex
  -- Prime action collapses the `x`-fixed points to the `E`-fixed points.
  have heq := hEprime x (hE3le hxE3) hx1
  rw [← fixedBy_def, ← heq]
  exact hxfix

/-- **Every prime dividing `|E|` lies in `τ₁(M) ∪ τ₃(M)`** in BG Proposition 14.2's
`κ(M) ∩ τ₃(M) ≠ ∅` case (the effective content of `E₂ = ⊥`): a prime `p ∣ |E|` is a
`σ(M)'`-prime with `r_p(M) ≤ 2`.  If `r_p(M) = 2` then `p ∈ τ₂(M)`, and Corollary 12.6
(`elemAb_normal_in_E_of_tau2`, projection on `E₃`) forces `C_{M_σ}(x) = 1` for the `E₃`-witness
`x`, contradicting `hxC`.  Hence `r_p(M) = 1`, so `p ∈ τ₁(M) ∪ τ₃(M)`.

Together with prime action (`C_{M_σ}(P) = C_{M_σ}(E) ≠ 1` for rank-one `P ≤ E`) this gives
`π(E) ⊆ κ(M)`, the key to `K = E` in the `κ ∩ τ₃` case. -/
theorem mem_tau1_union_tau3_of_mem_primeFactors_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∈ tau1 M ∪ tau3 M := by
  obtain ⟨hpp, hpdvdE, -⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨hpp⟩
  have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M := h.not_mem_sigma_of_mem_primeFactors hG hp
  have hr2 : pRank ↥M p ≤ 2 := h.pRank_M_le_two hG hp
  -- `p ∣ |M|`, so `r_p(M) ≥ 1`.
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr
      ⟨hpp, hpdvdE.trans (Subgroup.card_dvd_of_le h.E_le), Nat.card_pos.ne'⟩
  have hr1 : 1 ≤ pRank ↥M p := one_le_pRank_of_mem_primeFactors hpM
  by_cases hr : pRank ↥M p = 2
  · -- `r_p(M) = 2 ⟹ p ∈ τ₂`, which makes `E₃` regular and kills the witness.
    exfalso
    have hpτ2 : p ∈ tau2 M := (mem_tau2_iff M p).mpr ⟨hpσ, hr⟩
    obtain ⟨A, hA, hAE⟩ := exists_elemAb_rank_two_le_E_of_tau2 hG h hpτ2
    exact hxC ((elemAb_normal_in_E_of_tau2 hG h hpτ2 hA hAE).2.2.2.1 x hxE3 hxne)
  · -- `r_p(M) = 1`: `p ∈ τ₃` if `p ∣ |M'|`, else `p ∈ τ₁`.
    have hr1' : pRank ↥M p = 1 := by omega
    by_cases hd : p ∈ tau3 M
    · exact Or.inr hd
    · refine Or.inl ((mem_tau1_iff M p).mpr ⟨hpσ, ?_, hr1'⟩)
      intro hderiv
      exact hd ((mem_tau3_iff M p).mpr ⟨hpσ, hderiv, hr1'⟩)

/-- **`π(E) ⊆ κ(M)`** in BG Proposition 14.2's `κ(M) ∩ τ₃(M) ≠ ∅` case: every prime `p ∣ |E|`
lies in `κ(M)`.  By `mem_tau1_union_tau3_of_mem_primeFactors_card_E`, `p ∈ τ₁(M) ∪ τ₃(M)`; and a
rank-one `P = ⟨g⟩ ≤ E` of order `p` (Cauchy) has `C_{M_σ}(P) = C_{M_σ}(g) = C_{M_σ}(E) ≠ 1` by
prime action (using the `E₃`-witness `x`), so `P` certifies `p ∈ κ(M)`.

This is the `K = E` step: with `π(E) ⊆ κ(M)` and the complement index `[M:E] = |M_σ|` coprime to
`κ(M)`, `E` is a Hall `κ(M)`-subgroup of `M`, hence equals the Hall `κ(M)`-subgroup `K ≤ E`. -/
theorem mem_kappa_of_mem_primeFactors_card_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hEprime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E)
    {x : G} (hxE3 : x ∈ E₃) (hxne : x ≠ 1)
    (hxC : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E).primeFactors) : p ∈ kappa M := by
  obtain ⟨hpp, hpdvdE, -⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨hpp⟩
  have hτ13 : p ∈ tau1 M ∪ tau3 M :=
    mem_tau1_union_tau3_of_mem_primeFactors_card_E hG h hxE3 hxne hxC hp
  -- `C_{M_σ}(E) ≠ 1` from the witness `x` and prime action.
  have hCE : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G) ≠ ⊥ := by
    have heqx := hEprime x (h.E₃_le hxE3) hxne
    rw [← fixedBy_def, ← heqx]; exact hxC
  -- A rank-one `P = ⟨g⟩ ≤ E` of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvdE
  have hgE : (g : G) ∈ E := g.2
  have hgord : orderOf (g : G) = p :=
    (orderOf_injective E.subtype E.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by
    rw [Nat.card_zpowers]; exact hgord
  have hPelem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPM : Subgroup.zpowers (g : G) ≤ M := Subgroup.zpowers_le.mpr (h.E_le hgE)
  -- `C_{M_σ}(⟨g⟩) = C_{M_σ}(g) = C_{M_σ}(E) ≠ 1`.
  have heqg := hEprime (g : G) hgE hgne
  have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
  have hPC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) ≠ ⊥ := by
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ := by
      rw [← fixedByElement_def, heqg, fixedBy_def]; exact hCE
    exact fun hbot => hne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))
  exact ⟨hpp, hτ13, Subgroup.zpowers (g : G), hPelem, hPM, hPC⟩

/-- **`π(E₁) ⊆ κ(M)`** in BG Proposition 14.2's `κ(M) ⊆ τ₁(M)` case: every prime `p ∣ |E₁|` lies
in `κ(M)`.  `p ∈ τ₁(M)` (as `E₁` is Hall `τ₁(M)` of `E`), and a rank-one `P = ⟨g⟩ ≤ E₁` of order
`p` has `C_{M_σ}(P) = C_{M_σ}(E₁) ≠ 1` by prime action (`hE1prime`) plus `C_{M_σ}(E₁) ≠ 1`
(`hCE1`, from `E1_not_regular`).  So `E₁` is a `κ(M)`-subgroup; with `[M:E₁]` coprime to `κ(M)`
this makes `E₁` a Hall `κ(M)`-subgroup, conjugate to `K` (the entry to WLOG `K = E₁`). -/
theorem mem_kappa_of_mem_primeFactors_card_E1 [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃)
    (hE1prime : ActsPrimeOn (OddOrder.BG.Ch3.S10.Msigma M) E₁)
    (hCE1 : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) ≠ ⊥)
    {p : ℕ} (hp : p ∈ (Nat.card ↥E₁).primeFactors) : p ∈ kappa M := by
  obtain ⟨hpp, hpdvdE1, -⟩ := Nat.mem_primeFactors.mp hp
  have : Fact p.Prime := ⟨hpp⟩
  have hpτ1 : p ∈ tau1 M := h.E₁_hall.1 p (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv]; exact hp)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpdvdE1
  have hgE1 : (g : G) ∈ E₁ := g.2
  have hgord : orderOf (g : G) = p :=
    (orderOf_injective E₁.subtype E₁.subtype_injective g).trans hg
  have hgne : (g : G) ≠ 1 := by
    intro hc; rw [hc, orderOf_one] at hgord; exact hpp.ne_one hgord.symm
  have hPcard : Nat.card ↥(Subgroup.zpowers (g : G)) = p := by
    rw [Nat.card_zpowers]; exact hgord
  have hPelem : Subgroup.zpowers (g : G) ∈ elemAbelianOfRank G p 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hPcard, by rw [hPcard, pow_one]⟩
  have hPM : Subgroup.zpowers (g : G) ≤ M :=
    Subgroup.zpowers_le.mpr ((h.E₁_le.trans h.E_le) hgE1)
  have heqg := hE1prime (g : G) hgE1 hgne
  have hCle : Subgroup.centralizer ({(g : G)} : Set G) ≤
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact Commute.zpow_left (hy (g : G) (Set.mem_singleton _)) n
  have hPC : OddOrder.BG.Ch3.S10.Msigma M ⊓
      Subgroup.centralizer (↑(Subgroup.zpowers (g : G)) : Set G) ≠ ⊥ := by
    have hne : OddOrder.BG.Ch3.S10.Msigma M ⊓
        Subgroup.centralizer ({(g : G)} : Set G) ≠ ⊥ := by
      rw [← fixedByElement_def, heqg, fixedBy_def]; exact hCE1
    exact fun hbot => hne (le_bot_iff.mp ((inf_le_inf_left _ hCle).trans hbot.le))
  exact ⟨hpp, Or.inl hpτ1, Subgroup.zpowers (g : G), hPelem, hPM, hPC⟩

/-- **BG Proposition 14.2(c)** for the `κ(M) ∩ τ₃(M) ≠ ∅` case: if `X ∈ ℰ_q¹(G)` lies in
`K^* = C_{M_σ}(E)` (i.e. `X ≤ M_σ ⊓ C(E)`), then `𝓜(C_G(X)) = {M}`.  Here `q ∣ |M_σ|` forces
`q ∈ σ(M)`, and `X ≤ M_σ ⊓ C(E₁)` (since `E₁ ≤ E`), so Lemma 13.6
(`maximalContaining_eq_singleton_of_E1`) applies with `P = E₁` and a Sylow `q`-subgroup of `M_σ`.
With `K = E` this is the `𝓜(C_G(X)) = {M}` half of (c); it drives conjunct (d)
(`K^* ∩ M^g = 1` for `g ∉ M`). -/
theorem maximalContaining_centralizer_of_le_Msigma_centralizer_E [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    {X : Subgroup G} {q : ℕ} [Fact q.Prime] (hX : X ∈ elemAbelianOfRank G q 1)
    (hXK : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M := hXK.trans inf_le_left
  have hXcard : Nat.card ↥X = q := by rw [(mem_elemAbelianOfRank.mp hX).2, pow_one]
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  have hXC : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G) :=
    le_inf hXMσ ((hXK.trans inf_le_right).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr h.E₁_le)))
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T →
      S = T := fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  exact (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hX hXC hSMσ hSq hSmax).1

/-- **BG Proposition 14.2(c)**, `C(E₁)` form (for case `κ ⊆ τ₁`, where
`K^* = C_{M_σ}(K) = C_{M_σ}(E₁)`
after the WLOG `K = E₁`): if `X ∈ ℰ_q¹(G)` lies in `M_σ ⊓ C(E₁)`, then `𝓜(C_G(X)) = {M}`.  Same as
`maximalContaining_centralizer_of_le_Msigma_centralizer_E` but takes `X ≤ M_σ ⊓ C(E₁)` directly
(Lemma 13.6 with `P = E₁`). -/
theorem maximalContaining_centralizer_of_le_Msigma_centralizer_E1 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) (hE1ne : E₁ ≠ ⊥)
    {X : Subgroup G} {q : ℕ} [Fact q.Prime] (hX : X ∈ elemAbelianOfRank G q 1)
    (hXC : X ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (E₁ : Set G)) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M := hXC.trans inf_le_left
  have hXcard : Nat.card ↥X = q := by rw [(mem_elemAbelianOfRank.mp hX).2, pow_one]
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨Fact.out, hXcard ▸ Subgroup.card_dvd_of_le hXMσ, Nat.card_pos.ne'⟩)
  obtain ⟨S, hSMσ, hSq, _, hScard⟩ := exists_einvariant_sylow_Msigma hG h q
  have hSmax : ∀ T : Subgroup G, T ≤ OddOrder.BG.Ch3.S10.Msigma M → IsPGroup q ↥T → S ≤ T →
      S = T := fun T hTM hTq hST => eq_of_le_of_isPGroup_card_eq_factorization hScard hTM hTq hST
  exact (maximalContaining_eq_singleton_of_E1 hG h hqσ (le_refl E₁) hE1ne hX hXC hSMσ hSq hSmax).1

end OddOrder.BG.Ch4.S14


