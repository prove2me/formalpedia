-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:06:44.255761+00:00
-- url     : https://prove2.me/theorems/befe93ae-de0c-4e26-a315-08b1066a04df
-- title:
--   BG §15: Theorem 15.2 step 5, Corollary 15.5 (continuation)
-- statement:
--   A continuation of the Theorem 15.2 / Corollary 15.5 part of §15 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*: step 5 ($D$ centralizes $Q$ for narrow $Q$) and conjunct 3 ($M''\subseteq F(M)$) as gated-endpoint skeletons.
--
--   Main declarations: `D_centralizes_Q_of_narrow`; `derivedDerived_le_fittingInAmbient_of_inputs`.
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/Corollary155.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/Corollary155.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Assembly

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **`D ⋊ K` is a Frobenius group from the prime-manner action** (BG Theorem 15.2, mmd L4196-4200,
BG Theorem 3.10(b)(c) input): for the `q'`-Hall complement `D` of `Q` in `M_σ` and the `κ`-Hall
complement `K`, the group `D ⊔ K` is Frobenius with kernel `D` and complement `K`.

The Frobenius (fixed-point-free) condition is exactly the prime-manner action: a `k ∈ K#` fixing
`n ∈ D#` would centralize it, so `n ∈ C_{M_σ}(k) = K* ⊆ Q` (`hprime`, `hKstarQ`; `D ≤ M_σ`), while
`n ∈ D` and `D ∩ Q = 1` (`hDQ`), forcing `n = 1`.  The remaining structure is bookkeeping:
`D ◁ D⊔K` (`K ≤ N_G(D)`, `hKnormD`), `D, K` complements (`D ∩ K = 1`, `hDK`), both nontrivial.

Discharges the `hfrob` hypothesis of `chiefFactor_card_and_commutator_of_inputs`. -/
theorem isFrobeniusGroup_DK_of_primeManner
    {M K D Kstar Q : Subgroup G}
    (hprime : ∀ x ∈ K, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = Kstar)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hKstarQ : Kstar ≤ Q) (hDQ : Disjoint D Q)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G)) (hDK : Disjoint D K)
    (hDne : D ≠ ⊥) (hKne : K ≠ ⊥) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(D ⊔ K)
      (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K)) := by
  have hDL : D ≤ D ⊔ K := le_sup_left
  have hKL : K ≤ D ⊔ K := le_sup_right
  -- `D ◁ D⊔K` from `D ≤ N(D)` and `K ≤ N(D)`.
  have hDnormD : (D : Subgroup G) ≤ Subgroup.normalizer (D : Set G) := Subgroup.le_normalizer
  have hDLnormal : (D.subgroupOf (D ⊔ K)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hDL).mpr (sup_le hDnormD hKnormD)
  refine
    { isNormal := hDLnormal
      isComplement := ?_
      ne_bot_kernel := ?_
      ne_bot_complement := ?_
      conj_frobenius := ?_ }
  · -- `D` and `K` are complements in `D ⊔ K`.
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    · rw [Subgroup.disjoint_def]
      intro x hxD hxK
      rw [Subgroup.mem_subgroupOf] at hxD hxK
      exact Subtype.ext (Subgroup.disjoint_def.mp hDK hxD hxK)
    · have hsup : D.subgroupOf (D ⊔ K) ⊔ K.subgroupOf (D ⊔ K) = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hDL hKL, Subgroup.subgroupOf_self]
      have := Subgroup.normal_mul (D.subgroupOf (D ⊔ K)) (K.subgroupOf (D ⊔ K))
      rw [hsup, Subgroup.coe_top] at this
      exact this.symm
  · -- kernel nontrivial.
    intro hbot
    exact hDne (by
      have := Subgroup.map_mono (f := (D ⊔ K).subtype) (le_of_eq hbot)
      rwa [Subgroup.map_subgroupOf_eq_of_le hDL, Subgroup.map_bot, le_bot_iff] at this)
  · -- complement nontrivial.
    intro hbot
    exact hKne (by
      have := Subgroup.map_mono (f := (D ⊔ K).subtype) (le_of_eq hbot)
      rwa [Subgroup.map_subgroupOf_eq_of_le hKL, Subgroup.map_bot, le_bot_iff] at this)
  · -- Frobenius condition = fixed-point-free = prime manner.
    rintro a ha ha1 n hn hn1 hfix
    rw [Subgroup.mem_subgroupOf] at ha hn
    have haK : (a : G) ∈ K := ha
    have ha1G : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hnG : (n : G) ≠ 1 := fun h => hn1 (Subtype.ext h)
    have hfixG : (a : G) * (n : G) * (a : G)⁻¹ = (n : G) := Subtype.ext_iff.mp hfix
    -- `n ∈ C_G(a)`: `a n a⁻¹ = n` ⟹ `a n = n a`.
    have han : (a : G) * (n : G) = (n : G) * (a : G) := by
      rw [mul_inv_eq_iff_eq_mul] at hfixG; exact hfixG
    have hnCent : (n : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro g hg
      rw [Set.mem_singleton_iff] at hg; subst hg
      exact han
    -- `n ∈ C_{M_σ}(a) = K* ⊆ Q`, while `n ∈ D` and `D ∩ Q = 1`.
    have hnMσ : (n : G) ∈ OddOrder.BG.Ch3.S10.Msigma M := hDMσ hn
    have hnKstar : (n : G) ∈ Kstar := by
      rw [← hprime (a : G) haK ha1G]; exact Subgroup.mem_inf.mpr ⟨hnCent, hnMσ⟩
    have hnQ : (n : G) ∈ Q := hKstarQ hnKstar
    exact hnG (Subgroup.disjoint_def.mp hDQ hn hnQ)

/-- **BG Theorem 15.2 step 3-4, the chief-factor engine wiring** (mmd L4194-4196): given the
type-`P₁` data with `Q = O_q(M)`, the `K`-invariant complement `D` of `Q` in `M_σ`, and the
*output of `chiefFactor_Q0_normal_minimal_of_inputs`* (the normal `Q₀ = C_Q(D) ⊴ M`, `¬ K* ≤ Q₀`,
`Q₀ < Q`, and the lattice-minimality), it runs Theorem 3.10 on the Frobenius group `KD` and yields
the chief-factor index `[Q : Q₀] = q^{|K|}` with `|K|` prime, the commutator constraint
`D' ⊆ C_D(Q̄)`, and the elementary abelian section `Q̄ = Q/Q₀`.

Chains the chief-factor producers: `isElementaryAbelian_chiefFactor_of_minimalNormal`
(`hEA`/`hNT`), `card_centralizer_quotient_eq_of_kstar` (`hCfix`/`hCcard`),
`isFrobeniusGroup_DK_of_primeManner` (`hfrob`), `mem_centralizer_of_centralizes_quotient`
(`hFPF`), `actsPrimeManner_quotient_of_inputs` (`hcond3`), and the Theorem 3.10 engine
`chiefFactor_card_and_commutator_of_inputs`.  The coprimality `gcd(|D ⊔ K|, |Q|) = 1` uses
`|D ⊔ K| = |K|·|D|` (the Frobenius semidirect structure). -/
theorem chiefFactor_engine_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar Q D Q0 : Subgroup G} {q : ℕ} [Fact q.Prime]
    [(Q0.subgroupOf Q).Normal]
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    (hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hKstarQ : Kstar ≤ Q) (hKne : K ≠ ⊥)
    (hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)))
    (hDq' : q ∉ (Nat.card ↥D).primeFactors)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hQDdisj : Disjoint Q D) (hDne : D ≠ ⊥)
    (hQ0def : Q0 = Q ⊓ Subgroup.centralizer (D : Set G))
    (hMNQ0 : M ≤ Subgroup.normalizer (Q0 : Set G)) (hKstarNotQ0 : ¬ Kstar ≤ Q0)
    (hQ0ltQ : Q0 < Q)
    (hmin : ∀ H : Subgroup G, Q0 < H → H ≤ Q → (H.subgroupOf M).Normal → Q ≤ H) :
    (Nat.card ↥K).Prime ∧
      (Q0.subgroupOf Q).index = q ^ Nat.card ↥K ∧
      (∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q0) ∧
      OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q) := by
  classical
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hDM : D ≤ M := hDMσ.trans hMσM
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hQpg : IsPGroup q ↥Q := by rw [hQ]; exact isPGroup_opiCoreInG_singleton M
  have hQ0Q : Q0 ≤ Q := hQ0ltQ.le
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := hKM.trans hMnormQ
  have hDNQ : D ≤ Subgroup.normalizer (Q : Set G) := hDM.trans hMnormQ
  have hQQ0 : Q ≤ Subgroup.normalizer (Q0 : Set G) := hQM.trans hMNQ0
  have hKQ0 : K ≤ Subgroup.normalizer (Q0 : Set G) := hKM.trans hMNQ0
  have hDNQ0 : D ≤ Subgroup.normalizer (Q0 : Set G) := hDM.trans hMNQ0
  have hKstarN : Kstar ≤ Subgroup.normalizer (Q0 : Set G) := hKstarQ.trans hQQ0
  have hSolvQ : Group.IsSolvable ↥Q :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQM)
  have hsolvDK : Group.IsSolvable ↥(D ⊔ K) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (sup_le hDM hKM))
  have hKstarP : (Nat.card ↥Kstar).Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have hKstarEqQ : Nat.card ↥Kstar = q := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    have hdvd : Nat.card ↥Kstar ∣ Nat.card ↥Q := Subgroup.card_dvd_of_le hKstarQ
    rw [hn] at hdvd
    exact (Nat.prime_dvd_prime_iff_eq hKstarP Fact.out).mp (hKstarP.dvd_of_dvd_pow hdvd)
  have hqD : ¬ q ∣ Nat.card ↥D := fun hdvd =>
    hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, Nat.card_pos.ne'⟩)
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr hqD).symm
  have hcopKQ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥Q) :=
    hcop.coprime_dvd_right (Subgroup.card_dvd_of_le hQMσ)
  have hDKdisj : Disjoint D K := hKMσdisj.symm.mono_left hDMσ
  have hcopDKQ : Nat.Coprime (Nat.card ↥(D ⊔ K)) (Nat.card ↥Q) := by
    have hcardsup : Nat.card ↥(D ⊔ K) = Nat.card ↥K * Nat.card ↥D := by
      rw [sup_comm]
      exact card_sup_eq_mul_of_le_normalizer_of_disjoint hKnormD (disjoint_iff.mp hDKdisj.symm)
    rw [hcardsup]; exact Nat.coprime_mul_iff_left.mpr ⟨hcopKQ, hcopDQ⟩
  have hprime := actsPrimeManner_of_typeP hG hM hP1.1 hKM hK hKstar
  obtain ⟨hEA, hNT⟩ :=
    isElementaryAbelian_chiefFactor_of_minimalNormal hQ0ltQ hQM hQpg hMnormQ hMNQ0 hmin
  obtain ⟨C, hQ0C, hCQ, hCfix, hCcard⟩ :=
    card_centralizer_quotient_eq_of_kstar hKstar hQMσ hKstarQ hKstarEqQ hQ0Q hKstarNotQ0 hKQ hQQ0
      hKQ0 hKstarN hcopKQ (Or.inr hSolvQ)
  have hfrob := isFrobeniusGroup_DK_of_primeManner (M := M) hprime hDMσ hKstarQ hQDdisj.symm hKnormD
    hDKdisj hDne hKne
  have hFPF : ∀ x ∈ Q, (∀ d ∈ D, ⁅d, x⁆ ∈ Q0) → x ∈ Q0 :=
    fun x hxQ hfix => mem_centralizer_of_centralizes_quotient hQ0def hDNQ hQQ0 hDNQ0 hcopDQ
      (Or.inr hSolvQ) hxQ hfix
  have hcond3 := actsPrimeManner_quotient_of_inputs hKstar hprime hQMσ hKstarQ hQ0Q hKQ hQQ0 hKQ0
    hcopKQ (Or.inr hSolvQ)
  obtain ⟨hKprime, hindex, hDcomm⟩ :=
    chiefFactor_card_and_commutator_of_inputs hQ0Q hQ0C hCQ hDne hEA hNT hDNQ hKQ hDNQ0 hKQ0 hQQ0
      hsolvDK hfrob hcopDKQ hFPF hcond3 hCfix hCcard
  exact ⟨hKprime, hindex, hDcomm, hEA⟩

/-- **Theorem 15.2(g) reverse inclusion, reduced to `C_M(Q) ⊆ M_σ`** (mmd L4196-4198): if the
centralizer `C_M(Q)` of the normal `q`-subgroup `Q` lies in `M_σ` (the genuinely BG-specific input,
from `σ`-uniqueness — it does *not* follow from local structure, cf. the ChatGPT-verified counter-
example `M = (C₇⋊C₃)×(C₃₁⋊C₅)`), then `C_M(Q) ⊆ F(M)`.  `C_M(Q)` is nilpotent
(`isNilpotent_of_centralizes_normal_of_quotient_isNilpotent`: it centralizes `Q ◁ M_σ` and
`M_σ/Q` is nilpotent) and normal in `M` (`M ≤ N_G(Q) ≤ N_G(C_G(Q))`), so a nilpotent normal
subgroup of `M` lands in `F(M)` (`nilpotent_normal_le_fitting`).  Discharges the `hcent` input of
`fittingInAmbient_eq_sup_centralizer_inf_of_inputs`. -/
theorem centralizer_inf_le_fittingInAmbient_of_le_Msigma [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} (_hM : M ∈ maximalSubgroups G)
    (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal]
    [Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))]
    (hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    Subgroup.centralizer (Q : Set G) ⊓ M ≤ fittingInAmbient M := by
  have : Group.IsSolvable ↥M := _hG.isSolvable_of_mem_maximalSubgroups _hM
  -- `C_M(Q)` is nilpotent (central extension over the nilpotent `M_σ/Q`).
  have : Group.IsNilpotent ↥(Subgroup.centralizer (Q : Set G) ⊓ M) :=
    isNilpotent_of_centralizes_normal_of_quotient_isNilpotent hCle inf_le_left
  -- `C_M(Q) ◁ M` (`M` normalizes `Q`, hence `C_G(Q)`, hence `C_G(Q) ⊓ M`).
  have hMnormC : M ≤ Subgroup.normalizer
      ((Subgroup.centralizer (Q : Set G) ⊓ M : Subgroup G) : Set G) :=
    le_normalizer_inf (hMnormQ.trans (normalizer_le_normalizer_centralizer Q))
      Subgroup.le_normalizer
  have : ((Subgroup.centralizer (Q : Set G) ⊓ M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hMnormC
  have : Group.IsNilpotent ↥((Subgroup.centralizer (Q : Set G) ⊓ M).subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe (inf_le_right :
      Subgroup.centralizer (Q : Set G) ⊓ M ≤ M)).symm
  -- Nilpotent normal subgroup of `M` lands in `F(M)`.
  calc Subgroup.centralizer (Q : Set G) ⊓ M
      = ((Subgroup.centralizer (Q : Set G) ⊓ M).subgroupOf M).map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    _ = fittingInAmbient M := rfl

/-- **BG Theorem 15.2(g), assembled from the single `σ`-gap `C_M(Q) ⊆ M_σ`** (mmd L4196-4198):
chains the equality skeleton (`fittingInAmbient_eq_sup_centralizer_inf_of_inputs`) with the reduced
reverse inclusion (`centralizer_inf_le_fittingInAmbient_of_le_Msigma`).  For `Q = O_q(M)` with
`M_σ/Q` nilpotent, the conjunct `F(M) = Q ⊔ (C_G(Q) ⊓ M)` follows from `C_M(Q) ⊆ M_σ` alone.  This
is the wrapper-facing form: the only outstanding input is the BG-specific `C_M(Q) ⊆ M_σ` (a
`σ`-uniqueness fact to be supplied from the global analysis / forward input). -/
theorem fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M)
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal]
    [Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))]
    (hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) :=
  fittingInAmbient_eq_sup_centralizer_inf_of_inputs hQ
    (centralizer_inf_le_fittingInAmbient_of_le_Msigma hG hM hMnormQ hCle)

/-- **`D = ⁅D, K⁆` from the Frobenius (fixed-point-free) action** (BG Theorem 15.2, mmd L4202,
BG Lemma 6.3(a) flavour but via the coprime decomposition): if `D ⊔ K` is a Frobenius group with
kernel `D` and complement `K` (so `K` acts fixed-point-freely on `D`), `K ≤ N_G(D)`, and the orders
of `K` and `D` are coprime with `D`/`K` one-sided solvable, then `⁅D, K⁆ = D`.

`Proposition 1.6(d)` (`subgroup_coprime_decomposition`) gives `D = C_D(K) ⊔ ⁅D, K⁆`; the Frobenius
condition forces `C_D(K) = C_G(K) ⊓ D = ⊥` (a nontrivial `d ∈ D` centralizing a nontrivial `k ∈ K`
would be fixed by conjugation, contradicting `conj_frobenius`), so the decomposition collapses to
`D = ⁅D, K⁆`. -/
theorem commutator_eq_self_of_frobenius_DK [Finite G] {D K : Subgroup G}
    (hKne : K ≠ ⊥)
    (hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D))
    (hSolv : Group.IsSolvable ↥K ∨ Group.IsSolvable ↥D) :
    ⁅D, K⁆ = D := by
  -- `C_G(K) ⊓ D = ⊥`: a nontrivial common element contradicts the Frobenius condition.
  have hCDK : (Subgroup.centralizer (K : Set G) ⊓ D : Subgroup G) = ⊥ := by
    rw [eq_bot_iff]
    intro d hd
    rw [Subgroup.mem_inf] at hd
    obtain ⟨hdcent, hdD⟩ := hd
    by_contra hdne
    rw [Subgroup.mem_bot] at hdne
    -- Pick a nontrivial `k ∈ K`.
    have : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).mpr hKne
    obtain ⟨k, hkK, hkne⟩ := (Subgroup.nontrivial_iff_exists_ne_one K).mp inferInstance
    -- `k` and `d` commute (from `d ∈ C_G(K)`), so `k * d * k⁻¹ = d`, contradicting Frobenius.
    have hcomm : k * d = d * k := (Subgroup.mem_centralizer_iff.mp hdcent) k hkK
    have hfix : k * d * k⁻¹ = d := by rw [hcomm]; group
    exact hFrobFPF k hkK hkne d hdD hdne hfix
  -- Proposition 1.6(d): `D = (C_G(K) ⊓ D) ⊔ ⁅D, K⁆`.
  have hdecomp := OddOrder.BG.Ch3.S13.subgroup_coprime_decomposition hKnormD hcop hSolv
  rw [hCDK, bot_sup_eq] at hdecomp
  exact hdecomp.symm

set_option synthInstance.maxHeartbeats 80000 in
-- raised heartbeat budget for the heavy elaboration below
/-- **Theorem 15.2 step 5 — `D` centralizes `Q` for narrow `Q`** (mmd L4202, BG Theorem 5.5(a)):
if `Q` is a narrow `q`-group (`q` odd), `D ⊔ K` is a Frobenius group with kernel `D` and complement
`K` acting in a prime manner, `D ⊔ K ≤ N_G(Q)`, `D` is a `q'`-group (`q ∤ |D|`), and the orders of
`K`, `D` are coprime, then `D ⊆ C_G(Q)`.

`N := N_G(Q)` is proper (`Q ≠ 1, G` in the simple `G`), hence solvable; the conjugation action
`ψ : N → MulAut Q` has kernel `C_G(Q) ⊓ N`.  Theorem 5.5(a) (`solvableAut_of_narrow`, applied to the
faithful action of `N/ker`) gives that `(N/ker)'` is a `q`-group.  By the Frobenius condition
`⁅D, K⁆ = D` (`commutator_eq_self_of_frobenius_DK`), so `D ⊆ ⁅N, N⁆ = N'`; the image of `D` in
`N/ker` therefore lies in `(N/ker)'` (a `q`-group) yet is a `q'`-group (`q ∤ |D|`), hence trivial.
Trivial image means `D ⊆ ker ψ = C_G(Q) ⊓ N`, i.e. `D ⊆ C_G(Q)`. -/
theorem D_centralizes_Q_of_narrow [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {Q D K : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hq_odd : Odd q) (hQpg : IsPGroup q ↥Q) (hQnarrow : OddOrder.GroupTheory.IsNarrow q ↥Q)
    (hQne : Q ≠ ⊥)
    (hKne : K ≠ ⊥)
    (hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D))
    (hKsolv : Group.IsSolvable ↥K)
    (hDKN : D ⊔ K ≤ Subgroup.normalizer (Q : Set G))
    (hqD : ¬ q ∣ Nat.card ↥D) :
    D ≤ Subgroup.centralizer (Q : Set G) := by
  classical
  have hp_prime : q.Prime := Fact.out
  -- `N := N_G(Q)` is a proper (hence solvable) subgroup of the simple `G`.
  set N : Subgroup G := Subgroup.normalizer (Q : Set G) with hN_def
  have hNlt : N < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hQnorm : Q.Normal := by rw [← Subgroup.normalizer_eq_top_iff]; exact htop
    rcases hG.simple.eq_bot_or_eq_top_of_normal Q hQnorm with h | h
    · exact hQne h
    · have hGpg : IsPGroup q G := (h ▸ hQpg : IsPGroup q ↥(⊤ : Subgroup G)).of_surjective
        (Subgroup.topEquiv : (⊤ : Subgroup G) ≃* G).toMonoidHom Subgroup.topEquiv.surjective
      have : Group.IsNilpotent G := hGpg.isNilpotent
      exact hG.notSolvable inferInstance
  have hNsolv : Group.IsSolvable ↥N := hG.isSolvable_of_lt_top N hNlt
  -- The conjugation action `ψ : N → Aut Q` with kernel `C_G(Q) ∩ N`.
  set ψ : ↥N →* MulAut ↥Q := Q.normalizerMonoidHom with hψ_def
  have hψker : ψ.ker = (Subgroup.centralizer (Q : Set G)).subgroupOf N :=
    Q.normalizerMonoidHom_ker
  -- `A := N / ker ψ` acts faithfully, is solvable and odd.
  have hA_odd : Odd (Nat.card (↥N ⧸ ψ.ker)) := by
    refine hG.odd.of_dvd_nat (dvd_trans ?_ (Subgroup.card_subgroup_dvd_card N))
    simpa [Subgroup.index] using Subgroup.index_dvd_card ψ.ker
  -- Theorem 5.5(a): `(N / ker)'` is a `q`-group.
  obtain ⟨hcomm, -, -, -⟩ := Ch1.S05.solvableAut_of_narrow hq_odd hQpg hQnarrow
    (QuotientGroup.kerLift ψ) (QuotientGroup.kerLift_injective ψ) hA_odd
  have hA' : IsPGroup q (_root_.commutator (↥N ⧸ ψ.ker)) := by
    have hle : _root_.commutator (↥N ⧸ ψ.ker) ≤ Ch01.opCore q (↥N ⧸ ψ.ker) := by
      rw [_root_.commutator, Subgroup.commutator_le]
      intro x _ y _
      have h1 : QuotientGroup.mk' (Ch01.opCore q (↥N ⧸ ψ.ker)) ⁅x, y⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm _ _
      exact (QuotientGroup.eq_one_iff _).mp h1
    exact (Ch01.opCore_isPGroup q _).to_le hle
  -- `D ⊔ K ≤ N`, so `D ≤ N`; and `D = ⁅D, K⁆ ≤ N'`.
  have hDN : (D : Subgroup G) ≤ N := le_sup_left.trans hDKN
  have hDcommDK : ⁅D, K⁆ = D :=
    commutator_eq_self_of_frobenius_DK hKne hFrobFPF hKnormD hcop (Or.inl hKsolv)
  have hDcomm : (D : Subgroup G).subgroupOf N ≤ _root_.commutator ↥N := by
    have hDder : (D : Subgroup G) ≤ derivedInG N := by
      rw [← hDcommDK]
      calc ⁅D, K⁆ ≤ ⁅N, N⁆ := Subgroup.commutator_mono hDN (le_sup_right.trans hDKN)
        _ = derivedInG N := (Subgroup.map_subtype_commutator N).symm
    have key : ((_root_.commutator ↥N).map N.subtype).comap N.subtype = _root_.commutator ↥N :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective (_root_.commutator ↥N)
    calc (D : Subgroup G).subgroupOf N
        ≤ (derivedInG N).comap N.subtype := Subgroup.comap_mono hDder
      _ = _root_.commutator ↥N := key
  -- The image of `D` in `A` is `≤ (N/ker)'` (a `q`-group) and is a `q'`-group: hence trivial.
  set DA : Subgroup (↥N ⧸ ψ.ker) :=
    ((D : Subgroup G).subgroupOf N).map (QuotientGroup.mk' ψ.ker) with hDA_def
  have hDA_q : IsPGroup q ↥DA := by
    refine hA'.to_le ?_
    calc DA ≤ (_root_.commutator ↥N).map (QuotientGroup.mk' ψ.ker) := Subgroup.map_mono hDcomm
      _ ≤ _root_.commutator (↥N ⧸ ψ.ker) := by
          rw [_root_.commutator, _root_.commutator, Subgroup.map_commutator]
          exact Subgroup.commutator_mono le_top le_top
  -- `q ∤ |DA|`: `|DA|` divides `|D|` (surjective images), and `q ∤ |D|`.
  have hDA_card_dvd : Nat.card ↥DA ∣ Nat.card ↥D := by
    have h1 : Nat.card ↥DA ∣ Nat.card ↥((D : Subgroup G).subgroupOf N) :=
      Subgroup.card_map_dvd (H := (D : Subgroup G).subgroupOf N) (QuotientGroup.mk' ψ.ker)
    have h2 : Nat.card ↥((D : Subgroup G).subgroupOf N) = Nat.card ↥D :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDN).toEquiv
    rw [h2] at h1; exact h1
  have hqDA : ¬ q ∣ Nat.card ↥DA := fun h => hqD (h.trans hDA_card_dvd)
  -- A `q`-group with `q ∤ |DA|` is trivial.
  have hDA_bot : DA = ⊥ := by
    obtain ⟨k, hk⟩ := hDA_q.exists_card_eq
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · rw [hk0, pow_zero] at hk; exact Subgroup.card_eq_one.mp hk
    · exact absurd (hk ▸ dvd_pow_self q hkpos.ne') hqDA
  -- Trivial image means `D ≤ ker ψ = C_G(Q) ∩ N`, hence `D ≤ C_G(Q)`.
  have hDker : (D : Subgroup G).subgroupOf N ≤ ψ.ker := by
    rw [hDA_def, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hDA_bot
    exact hDA_bot
  rw [hψker] at hDker
  intro x hx
  have hxN : x ∈ N := hDN hx
  have : (⟨x, hxN⟩ : ↥N) ∈ (Subgroup.centralizer (Q : Set G)).subgroupOf N :=
    hDker (by rw [Subgroup.mem_subgroupOf]; exact hx)
  rw [Subgroup.mem_subgroupOf] at this
  exact this

/-- **Theorem 15.2 step 5 — `D` centralizes `Q` from `q ∉ β(M)`** (mmd L4202): the `hDcent` input of
`mem_beta_of_inputs`, with the narrowness of `Q` discharged from `q ∉ β(M)`.

When `Q = O_q(M)` is (the image in `G` of) a Sylow `q`-subgroup `P` of `M` — which holds in the
type-P1 setting, since `M_σ/Q` is a `q'`-group, so the normal Sylow `q` of `M_σ` is a Sylow `q` of
`M` — narrowness of `↥Q ≅ ↥P` follows from `q ∉ β(M)` (`isNarrow_sylow_of_not_mem_beta`, BG Lemma
10.8 setup).  Chaining with `D_centralizes_Q_of_narrow` (the Theorem 5.5(a) gate) gives
`q ∉ β(M) → D ⊆ C_G(Q)`, exactly the `hDcent` hypothesis of `mem_beta_of_inputs`. -/
theorem D_centralizes_Q_of_not_mem_beta [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M Q D K : Subgroup G} {q : ℕ} [Fact q.Prime] (hM : M ∈ maximalSubgroups G)
    (hq_odd : Odd q) (hQpg : IsPGroup q ↥Q) (hQne : Q ≠ ⊥)
    (hqπ : q ∈ (Nat.card ↥M).primeFactors)
    (P : Sylow q ↥M) (hQP : Q = (P : Subgroup ↥M).map M.subtype)
    (hKne : K ≠ ⊥)
    (hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n)
    (hKnormD : K ≤ Subgroup.normalizer (D : Set G))
    (hcop : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D))
    (hKsolv : Group.IsSolvable ↥K)
    (hDKN : D ⊔ K ≤ Subgroup.normalizer (Q : Set G))
    (hqD : ¬ q ∣ Nat.card ↥D) :
    q ∉ OddOrder.BG.Ch3.S10.beta M → D ≤ Subgroup.centralizer (Q : Set G) := by
  intro hqβ
  -- Narrowness of the Sylow `P`, transferred along `↥Q ≅ ↥P`.
  have hPnarrow : OddOrder.GroupTheory.IsNarrow q ↥(P : Subgroup ↥M) :=
    OddOrder.BG.Ch3.S10.isNarrow_sylow_of_not_mem_beta hG hM hqπ hqβ P
  have eQP : ↥Q ≃* ↥(P : Subgroup ↥M) :=
    (MulEquiv.subgroupCongr hQP).trans
      (Subgroup.equivMapOfInjective _ M.subtype M.subtype_injective).symm
  have hQnarrow : OddOrder.GroupTheory.IsNarrow q ↥Q :=
    OddOrder.GroupTheory.IsNarrow.of_mulEquiv eQP.symm hPnarrow
  exact D_centralizes_Q_of_narrow hG hq_odd hQpg hQnarrow hQne hKne hFrobFPF hKnormD hcop hKsolv
    hDKN hqD

/-- **Theorem 15.2 step 5 — `q ∈ β(M)`, gated-endpoint skeleton** (mmd L4202): "if `q ∉ β(M)`,
then Theorem 5.5(a) shows `(DK)' = D` centralizes `Q`, a contradiction".  The contradiction is
clean: `D` centralizing `Q` means `Q ≤ C_G(D)`, i.e. `C_Q(D) = Q`, against the established
`C_Q(D) = Q₀ ⊊ Q` (`M_σ` non-nilpotent).  Reduces `q ∈ β(M)` to the single Theorem-5.5 input
`hDcent` (`q ∉ β(M) → D ⊆ C_G(Q)`) and the proper-centralizer fact `hQ0` (`¬ Q ⊆ C_G(D)`). -/
theorem mem_beta_of_inputs {M Q D : Subgroup G} {q : ℕ}
    (hQ0 : ¬ Q ≤ Subgroup.centralizer (D : Set G))
    (hDcent : q ∉ OddOrder.BG.Ch3.S10.beta M → D ≤ Subgroup.centralizer (Q : Set G)) :
    q ∈ OddOrder.BG.Ch3.S10.beta M := by
  by_contra hq
  have hDQ := hDcent hq
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer] at hDQ
  exact hQ0 (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (by rwa [Subgroup.commutator_comm] at hDQ))

/-- **Theorem 15.2(f) — `M_F` non-cyclic, gated-endpoint skeleton** (mmd L4202): `M_F` is
non-cyclic because it contains the non-cyclic section `Q̄ = Q/Q₀` (the elementary abelian chief
factor of order `q^p`, `p ≥ 2`).  If `M_F` were cyclic, then so would be its subgroup `Q`
(`Subgroup.isCyclic_of_le`) and the quotient `Q/Q₀` (`isCyclic_of_surjective`), against `hQbar`.
Reduces `¬ IsCyclic M_F` to `Q ⊆ M_F` (Theorem 15.2(c)) and `¬ IsCyclic (Q/Q₀)` (from `|Q̄| = q^p`,
`p ≥ 2`). -/
theorem not_isCyclic_MF_of_inputs {M Q Q0 : Subgroup G} [(Q0.subgroupOf Q).Normal]
    (hQMF : Q ≤ MF M) (hQbar : ¬ IsCyclic (↥Q ⧸ Q0.subgroupOf Q)) :
    ¬ IsCyclic ↥(MF M) := by
  intro hcyc
  have := hcyc
  have : IsCyclic ↥Q := Subgroup.isCyclic_of_le hQMF
  exact hQbar (isCyclic_of_surjective (QuotientGroup.mk' (Q0.subgroupOf Q))
    (QuotientGroup.mk'_surjective _))

/-- A finite elementary-abelian `q`-group of order exceeding `q` is not cyclic (`§14`-independent,
reusable; generalises `not_isCyclic_of_card_prime_sq` to any order `> q`).  A cyclic group has
`Monoid.exponent = Nat.card`, while elementary-abelianness forces the exponent to divide `q`, so
`Nat.card ∣ q`. -/
theorem not_isCyclic_of_lt_card {q : ℕ} (hq : q.Prime) {Mod : Type*} [Group Mod] [Finite Mod]
    (h : OddOrder.GroupTheory.IsElementaryAbelian q Mod) (hlt : q < Nat.card Mod) :
    ¬ IsCyclic Mod := by
  intro hcyc
  have hExp_eq : Monoid.exponent Mod = Nat.card Mod := IsCyclic.exponent_eq_card
  have hExp_dvd : Monoid.exponent Mod ∣ q := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]; exact h.pow_eq_one
  rw [hExp_eq] at hExp_dvd
  exact (Nat.not_dvd_of_pos_of_lt hq.pos hlt) hExp_dvd

/-- **Theorem 15.2(f) conjunct `¬ IsCyclic M_F`, gated-endpoint skeleton** (mmd L4202): assembles
`not_isCyclic_MF_of_inputs` with the engine output `[Q : Q₀] = q^n` (`n = |K| ≥ 2`, since `|K|` is
the prime `p`).  The chief factor `Q̄ = Q/Q₀` (elementary abelian of order `q^n > q`) is non-cyclic
(`not_isCyclic_of_lt_card`), and `Q ⊆ M_F` (`hQMF`, Theorem 15.2(c)) lifts this to `M_F`. -/
theorem not_isCyclic_MF_of_chiefFactor_inputs [Finite G] {M Q Q0 : Subgroup G}
    [(Q0.subgroupOf Q).Normal] {q n : ℕ} (hq : q.Prime) (hn : 2 ≤ n)
    (hEA : OddOrder.GroupTheory.IsElementaryAbelian q (↥Q ⧸ Q0.subgroupOf Q))
    (hindex : (Q0.subgroupOf Q).index = q ^ n) (hQMF : Q ≤ MF M) :
    ¬ IsCyclic ↥(MF M) := by
  refine not_isCyclic_MF_of_inputs hQMF (not_isCyclic_of_lt_card hq hEA ?_)
  rw [← Subgroup.index_eq_card, hindex]
  calc q = q ^ 1 := (pow_one q).symm
    _ < q ^ n := pow_lt_pow_right₀ hq.one_lt (by omega)

/-- **Theorem 15.2(g) `F(M) ⊆ M_σ`** (mmd L4198), from the same `σ`-gap as the `(g)` equality:
`F(M) = Q ⊔ (C_G(Q) ⊓ M)` (`fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma`), with
`Q = O_q(M) ⊆ M_σ` (`opiCoreInG_singleton_le_Msigma_of_mem_sigma`, `q ∈ σ(M)`) and
`C_M(Q) ⊆ M_σ` (the forward input `hCle`).  So `F(M) ⊆ M_σ`. -/
theorem fittingInAmbient_le_Msigma_of_le_Msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M Q : Subgroup G} {q : ℕ} [Fact q.Prime]
    (hM : M ∈ maximalSubgroups G) (hMnormQ : M ≤ Subgroup.normalizer (Q : Set G))
    (hQ : Q = opiCoreInG ({q} : Set ℕ) M) (hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M)
    [(Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal]
    [Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))]
    (hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M) :
    fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M := by
  rw [fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma hG hM hMnormQ hQ hCle]
  refine sup_le ?_ hCle
  rw [hQ]
  exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ

open scoped commutatorElement in
/-- **Theorem 15.2 conjunct 3 — `M'' ⊆ F(M)`, gated-endpoint skeleton** (mmd L4198-4201): the
chain `M'' = M_σ' ⊆ Q D' ⊆ C_{M_σ}(Q̄) = F(M)`.

After identifying `M'' = M_σ'` (conjunct 2, `h2 : M_σ = M'`), the proof reduces `M_σ' ⊆ F(M)` to
three structural ingredients:
* `hsigmaprime : M_σ' ⊆ Q ⊔ ⁅D, D⁆` — the derived subgroup of the semidirect `M_σ = Q ⋊ D`
  (`Q ◁ M_σ`, complement `D`) lands in `Q · D'` (the `M_σ = QD` structure consequence);
* `hQab` / `hDcomm` — both `Q` and `D' = ⁅D, D⁆` *centralize the chief factor* `Q̄ = Q/Q₀`:
  `Q̄` is (elementary) abelian (`⁅Q, Q⁆ ⊆ Q₀`, `hQab`) and `D' ⊆ C_D(Q̄)` is the engine output
  `chiefFactor_card_and_commutator_of_inputs` (`∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q₀`, mmd 15.2(g));
* `hsecFit : C_{M_σ}(Q̄) ⊆ F(M)` — the *section-centralizer* containment, the genuinely BG-specific
  forward input.  This is the mmd's "Proposition 1.5(d) yields `F(M) = Q C_M(Q) = C_{M_σ}(Q̄)`"
  (`D` nilpotent while `M_σ` is not), which bundles the `σ`-uniqueness gap `C_M(Q) ⊆ M_σ` (cf.
  `fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma`) with the Prop 1.5(d) section identity.
  Note `D'` only centralizes the *section* `Q̄`, not `Q` itself, so the full-centralizer helper
  `centralizer_inf_le_fittingInAmbient_of_le_Msigma` is too weak here; the section form is needed.

Both `Q` and `D'` therefore lie in `C_{M_σ}(Q̄)` (they centralize `Q̄` and sit inside `M_σ`), whence
in `F(M)` by `hsecFit`, so `M_σ' ⊆ Q ⊔ D' ⊆ F(M)`.  Once the step-4 core supplies `hsigmaprime`
(QD structure) and `hsecFit` (Prop 1.5(d) + `σ`-gap), conjunct 3 becomes unconditional. -/
theorem derivedDerived_le_fittingInAmbient_of_inputs [Finite G] {M Q Q0 D : Subgroup G}
    (h2 : OddOrder.BG.Ch3.S10.Msigma M = derivedInG M)
    (hsigmaprime : derivedInG (OddOrder.BG.Ch3.S10.Msigma M) ≤ Q ⊔ ⁅D, D⁆)
    (hQsig : Q ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hDsig : D ≤ OddOrder.BG.Ch3.S10.Msigma M)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0)
    (hDcomm : ∀ g ∈ ⁅D, D⁆, ∀ x ∈ Q, ⁅g, x⁆ ∈ Q0)
    (hsecFit : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) → x ∈ fittingInAmbient M) :
    derivedInG (derivedInG M) ≤ fittingInAmbient M := by
  -- `M'' = M_σ'` (conjunct 2): rewrite the inner `derivedInG M` to `M_σ`.
  rw [← h2]
  -- `M_σ' ⊆ Q ⊔ D'`; show each of `Q`, `D'` lands in `F(M)` via the section-Fitting input.
  refine hsigmaprime.trans (sup_le ?_ ?_)
  · -- `Q ⊆ F(M)`: each `x ∈ Q` lies in `M_σ` and centralizes `Q̄` (`Q̄` abelian).
    intro x hx
    exact hsecFit x (hQsig hx) (fun y hy => hQab x hx y hy)
  · -- `D' ⊆ F(M)`: each `g ∈ ⁅D, D⁆` lies in `M_σ` and centralizes `Q̄` (engine output).
    have hDDsig : ⁅D, D⁆ ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem (hDsig ha) (hDsig hb)) (inv_mem (hDsig ha)))
        (inv_mem (hDsig hb))
    intro g hg
    exact hsecFit g (hDDsig hg) (fun x hx => hDcomm g hg x hx)

/-- **BG Corollary 15.5, "Lemma 1"**: `O_{σ(M)}(F(M)) = F(M_σ)` (`§14`-independent).
`≤`: `O_σ(F(M)) ≤ O_σ(M) = M_σ` (`opiCoreInG_fittingInG_le_opiCoreInG`); it is nilpotent (subgroup
of `F(M)`) and normal in `M` (characteristic in `F(M) ◁ M`), hence normal in `M_σ`, so a nilpotent
normal subgroup of `M_σ` lands in `F(M_σ)`.  `≥`: `F(M_σ)` is characteristic in `M_σ ◁ M` hence
normal in `M`, nilpotent, so `F(M_σ) ≤ F(M)` (`fittingInG_le_fittingInG_of_le_normalizer`); it is a
`σ`-group (`≤ M_σ`) and normal in `F(M)`, so `F(M_σ) ≤ O_σ(F(M))`. -/
theorem opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma [Finite G]
    {M : Subgroup G} :
    opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) =
      fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := by
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  -- `M` normalizes both `M_σ` and `O_σ(F(M))`.
  have hM_norm_Mσ : M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M
  have hMσ_le_M : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  refine le_antisymm ?_ ?_
  · -- `O_σ(F(M)) ≤ F(M_σ)`.
    set N : Subgroup G := opiCoreInG σ (fittingInAmbient M) with hN
    -- `N ≤ M_σ`.
    have hN_Mσ : N ≤ OddOrder.BG.Ch3.S10.Msigma M := by
      have := OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_le_opiCoreInG σ M
      rwa [show opiCoreInG σ M = OddOrder.BG.Ch3.S10.Msigma M from rfl] at this
    -- `N ◁ M` (characteristic in `F(M)`), hence `N ◁ M_σ`.
    have hM_norm_N : M ≤ Subgroup.normalizer (N : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        ((OddOrder.GroupTheory.opiCoreInG_le σ (fittingInAmbient M)).trans
          (OddOrder.BG.Ch2.S08.fittingInG_le M))).mp
        (OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σ M)
    have hNnorm_Mσ : (N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN_Mσ).mpr (hMσ_le_M.trans hM_norm_N)
    -- `N` is nilpotent (subgroup of the nilpotent `F(M)`).
    have : Group.IsNilpotent ↥N := by
      have : Group.IsNilpotent ↥(fittingInAmbient M) :=
        OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
      exact Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.GroupTheory.opiCoreInG_le σ (fittingInAmbient M)))
    -- Nilpotent normal subgroup of `M_σ` lands in `F(M_σ)`.
    have : Group.IsNilpotent ↥(N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
      Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hN_Mσ).symm
    have := hNnorm_Mσ
    calc N = (N.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).map
              (OddOrder.BG.Ch3.S10.Msigma M).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hN_Mσ).symm
      _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥(OddOrder.BG.Ch3.S10.Msigma M)).map
              (OddOrder.BG.Ch3.S10.Msigma M).subtype :=
          Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
      _ = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := rfl
  · -- `F(M_σ) ≤ O_σ(F(M))`.
    -- `F(M_σ) ≤ F(M)` (`F(M_σ)` characteristic in `M_σ ◁ M`, nilpotent).
    have hFMσ_le_FM : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ fittingInAmbient M :=
      OddOrder.BG.Ch2.S08.fittingInG_le_fittingInG_of_le_normalizer hMσ_le_M hM_norm_Mσ
    -- `F(M_σ) ≤ M_σ`, a `σ`-group.
    have hFMσ_le_Mσ : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤
        OddOrder.BG.Ch3.S10.Msigma M := OddOrder.BG.Ch2.S08.fittingInG_le _
    have hFMσ_pi : Subgroup.IsPiSubgroup σ (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) :=
      fun r hr => OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hFMσ_le_Mσ) Nat.card_pos.ne' hr)
    -- `F(M_σ) ◁ F(M)` (since `M` normalizes `F(M_σ)` and `F(M) ≤ M`).
    have hM_norm_FMσ : M ≤ Subgroup.normalizer
        ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) : Subgroup G) : Set G) := fun x hx =>
      OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem_normalizer (hM_norm_Mσ hx)
    have hFMσ_norm_FM : ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)).subgroupOf
        (fittingInAmbient M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hFMσ_le_FM).mpr
        ((OddOrder.BG.Ch2.S08.fittingInG_le M).trans hM_norm_FMσ)
    exact OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hFMσ_le_FM
      hFMσ_norm_FM hFMσ_pi

/-- Lattice absorption used in BG Corollary 15.5 (Case I): if `C = A ⊔ X` with `A ≤ B`, then
`C ⊔ B = X ⊔ B`.  Pure lattice fact (kept generic to avoid `whnf` on the underlying `Subgroup`
`set`-locals in the main proof). -/
theorem sup_eq_sup_of_eq_sup_of_le {α : Type*} [Lattice α] {C A X B : α}
    (hC : C = A ⊔ X) (hA : A ≤ B) : C ⊔ B = X ⊔ B := by
  subst hC
  rw [sup_right_comm, sup_eq_right.mpr hA, sup_comm]

/-- **Nilpotent normal subgroup lands in the ambient Fitting subgroup** (`§14`-independent,
reusable): if `N ≤ M`, `N.subgroupOf M ⊴ M`, and `N` is nilpotent, then `N ≤ F(M)`
(`fittingInAmbient M`).  The relative `N.subgroupOf M` is a nilpotent normal subgroup of `↥M`,
so it lies in `fitting ↥M` (`nilpotent_normal_le_fitting`); mapping back gives the claim. -/
theorem le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent [Finite G] {M N : Subgroup G}
    (hNM : N ≤ M) (hNnorm : (N.subgroupOf M).Normal) [Group.IsNilpotent ↥N] :
    N ≤ fittingInAmbient M := by
  have := hNnorm
  have : Group.IsNilpotent ↥(N.subgroupOf M) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNM).symm
  calc N = (N.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hNM).symm
    _ ≤ (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype :=
        Subgroup.map_mono OddOrder.Isaacs.Ch01.nilpotent_normal_le_fitting
    _ = fittingInAmbient M := rfl

/-- **BG Theorem 15.2** (mmd L4112): if `M_F` is strictly smaller than `M_sigma`,
then `M` is type `P1` and has the normal `q`-subgroup / minimal chief factor
structure described in the text. -/
theorem mf_ne_msigma_typeP1_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    S14.IsTypeP1 M ∧
      ∃ Q Q0 D : Subgroup G, ∃ p q : ℕ,
        p.Prime ∧ q.Prime ∧ Nat.card ↥K = p ∧ Nat.card ↥Kstar = q ∧
        q ∈ S14.piSet (MF M) ∧ q ∈ OddOrder.BG.Ch3.S10.beta M ∧
        Kstar ≤ MF M ∧
        Q ≤ MF M ∧ M ≤ Subgroup.normalizer (Q : Set G) ∧
        Subgroup.IsComplement' (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M))
          (D.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) ∧
        Group.IsNilpotent ↥D ∧
        Q0 = Q ⊓ Subgroup.centralizer (D : Set G) ∧
        M ≤ Subgroup.normalizer (Q0 : Set G) ∧
        -- mmd 15.2(f): the chief factor `Q̄ = Q/Q0` is elementary abelian of order `q^p`
        -- (faithfulness fix, Lane G 2026-06-16: the previous scaffold wrote
        -- `Nat.card ↥(Q.subgroupOf (Q ⊔ Q0))`, which is `|Q|` since `Q0 = Q ⊓ C(D) ⊆ Q` forces
        -- `Q ⊔ Q0 = Q`; the intended `|Q̄| = |Q : Q0|` is `(Q0.subgroupOf Q).index`).
        (Q0.subgroupOf Q).index = q ^ p ∧
        OddOrder.BG.Ch3.S10.Msigma M = derivedInG M ∧
        derivedInG (derivedInG M) ≤ fittingInAmbient M ∧
        -- mmd 15.2(g) "F(M) ⊂ M_σ": the Fitting subgroup is contained in the σ-core.
        fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
        -- mmd 15.2(g) "F(M) = Q C_M(Q)": the Fitting subgroup is the product of the normal
        -- `q`-subgroup `Q` and its `M`-centralizer (`Q` self-centralizing up to `C_M(Q)`).
        fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) ∧
        -- mmd 15.2(f): `M_F ⊇ Q̄`, an elementary abelian section of order `q^p` (rank `p ≥ 3`),
        -- so `M_F` is non-cyclic.  Breaks the 15.5↔15.6 circularity (Corollary 15.6's proof needs
        -- this without citing Corollary 15.5).
        ¬ IsCyclic ↥(MF M) := by
  classical
  -- **Setup.**  `p = |K|`, `q = |K*|`; `M` is type `P₁`, `q` prime, `M_σ = M'`.
  set q : ℕ := Nat.card ↥Kstar with hqdef
  have hP1 : S14.IsTypeP1 M := isTypeP1_of_mf_ne_msigma hG hM hne
  have hP : S14.IsTypeP M := hP1.1
  have hq_prime : q.Prime := kstar_card_prime_of_inputs hG hM hP1 hKM hK hKstar
  have : Fact q.Prime := ⟨hq_prime⟩
  have hMσderived : OddOrder.BG.Ch3.S10.Msigma M = derivedInG M :=
    typeP1_msigma_eq_derivedInG hG hM hP1 hKM hK hKstar
  obtain ⟨hcomplDer, _, _⟩ := S14.typeP_duality hG hM hP hKM hK hKstar
  have hcomplMσ : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M) := by rw [hMσderived]; exact hcomplDer
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hMσnotnil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hnil =>
    hne ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hnil)
  have hKstarMσ : Kstar ≤ OddOrder.BG.Ch3.S10.Msigma M := by rw [hKstar]; exact inf_le_left
  have hqMσ : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [hqdef]; exact Subgroup.card_dvd_of_le hKstarMσ
  have hqσ : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hq_prime, hqMσ, Nat.card_pos.ne'⟩)
  set Q : Subgroup G := opiCoreInG ({q} : Set ℕ) M with hQdef
  have hQMσ : Q ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    rw [hQdef]; exact OddOrder.BG.Ch3.S10.opiCoreInG_singleton_le_Msigma_of_mem_sigma hqσ
  have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef]; exact OddOrder.GroupTheory.le_normalizer_opiCoreInG _ M
  have hQM : Q ≤ M := hQMσ.trans hMσM
  have hcop_sub : Nat.Coprime (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)) := by
    have h := coprime_card_derived_kappaHall_of_isComplement' hK hcomplDer
    rwa [hMσderived]
  have hcond2 := actsPrimeManner_subgroupOf_of_typeP hG hM hP hKM hK hKstar
  have hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
      ⊓ Subgroup.centralizer (K : Set G))).Prime := by rw [← hKstar]; exact hq_prime
  have hKstarQ : Kstar ≤ Q := by
    have h := kstar_le_opiCore_of_inputs hG hM hKM hcomplMσ hcop_sub.symm hcond2 hne hqG
    rw [← hKstar, ← hqdef, ← hQdef] at h; exact h
  have hcopKMσ : Nat.Coprime (Nat.card ↥K) (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M)) := by
    have e1 : Nat.card ↥(K.subgroupOf M) = Nat.card ↥K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
    have e2 : Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv
    rw [e1, e2] at hcop_sub; exact hcop_sub.symm
  have hKMσdisj : Disjoint K (OddOrder.BG.Ch3.S10.Msigma M) := by
    rw [disjoint_iff]
    exact Subgroup.card_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcopKMσ
      (Subgroup.card_dvd_of_le inf_le_left) (Subgroup.card_dvd_of_le inf_le_right))
  have hKne : K ≠ ⊥ := by
    intro hK0
    apply hMσnotnil
    have hKstareq : Kstar = OddOrder.BG.Ch3.S10.Msigma M := by
      rw [hKstar, hK0]
      have hc : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
        rw [Subgroup.coe_bot]; ext g; simp [Subgroup.mem_centralizer_iff]
      rw [hc, inf_top_eq]
    have hcardMσ : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = q ^ 1 := by
      rw [pow_one, hqdef, hKstareq]
    exact (IsPGroup.of_card hcardMσ).isNilpotent
  have hQpg : IsPGroup q ↥Q := by rw [hQdef]; exact isPGroup_opiCoreInG_singleton M
  have hQneMσ : Q ≠ OddOrder.BG.Ch3.S10.Msigma M := by
    intro hQeq; exact hMσnotnil (hQeq ▸ hQpg.isNilpotent)
  -- **The `K`-invariant complement `D` of `Q` in `M_σ`.**
  obtain ⟨D, hDMσ, hKnormD, hQDdisj, hcomplD, hDnil, hDne, hDq'⟩ :=
    exists_kInvariant_qComplement hG hM hP hKM hK hKstar hQdef hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcopKMσ
  -- **The chief factor `Q₀ = C_Q(D) ⊴ M` and the Theorem 3.10 engine outputs.**
  obtain ⟨hMNQ0, hKstarNotQ0, hQ0ltQ, hmin⟩ :=
    chiefFactor_Q0_normal_minimal_of_inputs hG hM hP1 hKM hK hKstar hQdef hQMσ hMnormQ hKstarQ
      hQneMσ hKne hKMσdisj hcopKMσ hMσnotnil hDq' hDMσ hKnormD hQDdisj hcomplD hDnil hDne
  set Q0 : Subgroup G := Q ⊓ Subgroup.centralizer (D : Set G) with hQ0def
  have hQ0Q : Q0 ≤ Q := hQ0ltQ.le
  have hQ0nQ : (Q0.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0Q).mpr (hQM.trans hMNQ0)
  obtain ⟨hKprime, hindex, hDcomm, hEA⟩ :=
    chiefFactor_engine_of_inputs hG hM hP1 hKM hK hKstar hQdef hQMσ hMnormQ hKstarQ hKne hKMσdisj
      hcopKMσ hDq' hDMσ hKnormD hQDdisj hDne hQ0def hMNQ0 hKstarNotQ0 hQ0ltQ hmin
  -- **Fitting subgroup (Theorem 15.2(g)).**
  have hQnMσ : (Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQMσ).mpr (hMσM.trans hMnormQ)
  have hNilMσQ : Group.IsNilpotent (↥(OddOrder.BG.Ch3.S10.Msigma M) ⧸
      Q.subgroupOf (OddOrder.BG.Ch3.S10.Msigma M)) :=
    msigma_quotient_isNilpotent_of_inputs hG hM hP hKM hK hKstar hQMσ hMnormQ hKstarQ hQneMσ hKne
      hKMσdisj hcopKMσ
  have hprime := actsPrimeManner_of_typeP hG hM hP hKM hK hKstar
  have hQgtq : q < Nat.card ↥Q := by
    have h1 : (Q0.subgroupOf Q).index ≤ Nat.card ↥Q :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have h2 : q < q ^ Nat.card ↥K := by
      calc q = q ^ 1 := (pow_one q).symm
        _ < q ^ Nat.card ↥K := Nat.pow_lt_pow_right hq_prime.one_lt hKprime.two_le
    rw [hindex] at h1; exact lt_of_lt_of_le h2 h1
  have hKstarneQ : Kstar ≠ Q := by
    intro h
    have hqeq : q = Nat.card ↥Q := by rw [hqdef, h]
    rw [hqeq] at hQgtq; exact lt_irrefl _ hQgtq
  have hCle : Subgroup.centralizer (Q : Set G) ⊓ M ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    centralizer_le_Msigma_of_primeManner hG hM hP1 hKM hK hprime hQMσ hMnormQ hKstarQ hKstarneQ
  have cC17 : fittingInAmbient M ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    fittingInAmbient_le_Msigma_of_le_Msigma hG hM hMnormQ hQdef hqσ hCle
  have cC18 : fittingInAmbient M = Q ⊔ (Subgroup.centralizer (Q : Set G) ⊓ M) :=
    fittingInAmbient_eq_sup_centralizer_inf_of_le_Msigma hG hM hMnormQ hQdef hCle
  have hcopDQ : Nat.Coprime (Nat.card ↥D) (Nat.card ↥Q) := by
    obtain ⟨n, hn⟩ := hQpg.exists_card_eq
    rw [hn]
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp
    · rw [Nat.coprime_pow_right_iff h0]
      exact ((Fact.out : q.Prime).coprime_iff_not_dvd.mpr (fun hd =>
        hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩))).symm
  have hQab : ∀ x ∈ Q, ∀ y ∈ Q, ⁅x, y⁆ ∈ Q0 := by
    intro x hxQ y hyQ
    have hcomm := hEA.comm (QuotientGroup.mk (⟨x, hxQ⟩ : ↥Q))
      (QuotientGroup.mk (⟨y, hyQ⟩ : ↥Q))
    have h1 : QuotientGroup.mk (⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆) =
        (1 : ↥Q ⧸ Q0.subgroupOf Q) := by
      rw [← QuotientGroup.mk'_apply, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
    have h2 : ((⁅(⟨x, hxQ⟩ : ↥Q), (⟨y, hyQ⟩ : ↥Q)⁆ : ↥Q) : G) = ⁅x, y⁆ := by
      push_cast [commutatorElement_def]; rfl
    rwa [h2] at h1
  -- `M_σ' ⊆ Q ⊔ ⁅D, D⁆`: the derived subgroup of the semidirect `M_σ = Q ⋊ D` (`Q` normal,
  -- `D` complement).  `derivedInG_le_sup_of_normal` (S13) is exactly this normal-target argument:
  -- modulo the normal `Q` the quotient `M_σ/Q` is the image of `D`, so its derived subgroup is the
  -- image of `D' = ⁅D, D⁆`, and pulling back gives `M_σ' ⊆ Q ⊔ ⁅D, D⁆`.  (The `M_σ = QD`
  -- decomposition `Q ⊔ D = M_σ` is read off the complement `hcomplD.sup_eq_top`.)
  have hsigmaprime : derivedInG (OddOrder.BG.Ch3.S10.Msigma M) ≤ Q ⊔ ⁅D, D⁆ := by
    have hsup : Q ⊔ D = OddOrder.BG.Ch3.S10.Msigma M := by
      have h := congrArg (Subgroup.map (OddOrder.BG.Ch3.S10.Msigma M).subtype) hcomplD.sup_eq_top
      rwa [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hQMσ, inf_eq_left.mpr hDMσ, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at h
    have hle := OddOrder.BG.Ch3.S13.derivedInG_le_sup_of_normal hQMσ hDMσ hsup hQnMσ
    rwa [show derivedInG D = ⁅D, D⁆ from Subgroup.map_subtype_commutator D] at hle
  have hsecFit : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, (∀ y ∈ Q, ⁅x, y⁆ ∈ Q0) →
      x ∈ fittingInAmbient M :=
    centralizer_msigma_quotient_le_fittingInAmbient hG hM hQMσ hDMσ hQ0def hQ0Q hcomplD hMnormQ
      hMNQ0 hQpg hDnil hcopDQ hQab
  have cC16 : derivedInG (derivedInG M) ≤ fittingInAmbient M :=
    derivedDerived_le_fittingInAmbient_of_inputs hMσderived hsigmaprime hQMσ hDMσ hQab hDcomm
      hsecFit
  -- **`q ∈ β(M)` (conjunct 6).**
  have hQne : Q ≠ ⊥ := by
    intro h0
    have hKstar0 : Kstar = ⊥ := le_bot_iff.mp (h0 ▸ hKstarQ)
    have : q = 1 := by rw [hqdef, hKstar0, Subgroup.card_bot]
    exact hq_prime.ne_one this
  have hQ0notC : ¬ Q ≤ Subgroup.centralizer (D : Set G) := by
    intro hle
    exact (ne_of_lt hQ0ltQ) (le_antisymm hQ0Q (le_inf le_rfl hle))
  have hqπ : q ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq_prime, hqMσ.trans (Subgroup.card_dvd_of_le hMσM), Nat.card_pos.ne'⟩
  have hq_odd : Odd q := hG.odd.of_dvd_nat ((Nat.mem_primeFactors.mp hqπ).2.1.trans
    (Subgroup.card_subgroup_dvd_card M))
  have hcopKD : Nat.Coprime (Nat.card ↥K) (Nat.card ↥D) :=
    hcopKMσ.coprime_dvd_right (Subgroup.card_dvd_of_le hDMσ)
  have hDKN : D ⊔ K ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le (hDMσ.trans (hMσM.trans hMnormQ)) (hKM.trans hMnormQ)
  have hqD : ¬ q ∣ Nat.card ↥D := fun hd =>
    hDq' (Nat.mem_primeFactors.mpr ⟨Fact.out, hd, Nat.card_pos.ne'⟩)
  have hKsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKM)
  have hqK : ¬ q ∣ Nat.card ↥K := fun hd =>
    hq_prime.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hcopKMσ hd hqMσ)
  -- Sylow witness `P : Sylow q ↥M` with `Q = P.map M.subtype`.
  have hidx_M : ¬ q ∣ (Q.subgroupOf M).index := by
    have hMcard : Nat.card ↥M = Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) * Nat.card ↥K := by
      have h := hcomplMσ.card_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσM).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv] at h
      exact h.symm
    have hMσcard : Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) = Nat.card ↥Q * Nat.card ↥D := by
      have h := hcomplD.card_mul_card
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQMσ).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDMσ).toEquiv] at h
      exact h.symm
    have hidxeq : (Q.subgroupOf M).index = Nat.card ↥D * Nat.card ↥K := by
      have hmul := Subgroup.card_mul_index (Q.subgroupOf M)
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv, hMcard, hMσcard] at hmul
      refine Nat.eq_of_mul_eq_mul_left Nat.card_pos (?_ : Nat.card ↥Q * _ = Nat.card ↥Q * _)
      rw [hmul]; ring
    rw [hidxeq]
    exact fun hdvd => ((Nat.Prime.dvd_mul hq_prime).mp hdvd).elim hqD hqK
  obtain ⟨P, hQP⟩ := exists_sylow_eq_opiCore hQdef hQM hMnormQ hQpg hidx_M
  -- the `G`-level fixed-point-free condition, lifted from the `↥(D ⊔ K)`-Frobenius group.
  have hfrob := isFrobeniusGroup_DK_of_primeManner (M := M) hprime hDMσ hKstarQ hQDdisj.symm hKnormD
    (hKMσdisj.symm.mono_left hDMσ) hDne hKne
  have hFrobFPF : ∀ a ∈ K, a ≠ 1 → ∀ n ∈ D, n ≠ 1 → a * n * a⁻¹ ≠ n := by
    intro a haK ha1 n hnD hn1 heq
    have haDK : a ∈ D ⊔ K := (le_sup_right : K ≤ D ⊔ K) haK
    have hnDK : n ∈ D ⊔ K := (le_sup_left : D ≤ D ⊔ K) hnD
    refine hfrob.conj_frobenius ⟨a, haDK⟩ (Subgroup.mem_subgroupOf.mpr haK)
      (fun h => ha1 (congrArg Subtype.val h)) ⟨n, hnDK⟩ (Subgroup.mem_subgroupOf.mpr hnD)
      (fun h => hn1 (congrArg Subtype.val h)) (Subtype.ext ?_)
    change (a : G) * (n : G) * (a : G)⁻¹ = (n : G)
    exact heq
  have cC6 : q ∈ OddOrder.BG.Ch3.S10.beta M :=
    mem_beta_of_inputs hQ0notC (D_centralizes_Q_of_not_mem_beta hG hM hq_odd hQpg hQne hqπ P hQP
      hKne hFrobFPF hKnormD hcopKD hKsolv hDKN hqD)
  -- **`Q, K* ⊆ M_F` and `q ∈ π(M_F)` (conjuncts 5,7,8).**
  have hQhall : OddOrder.Isaacs.Ch03.IsHallSubgroup (Nat.card ↥Q).primeFactors
      (Q.subgroupOf M) := by
    have hpf : ((Nat.card ↥Q).primeFactors : Set ℕ) = ({q} : Set ℕ) := by
      obtain ⟨n, hn⟩ := hQpg.exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl; rw [pow_zero] at hn; rw [hn] at hQgtq
        have := hq_prime.two_le; omega
      rw [hn, Nat.primeFactors_prime_pow hn0 hq_prime, Finset.coe_singleton]
    rw [hpf]
    exact isHallSubgroup_subgroupOf_of_pgroup_of_not_dvd_index hQM hQpg hidx_M
  have hQnilM : Group.IsNilpotent ↥(Q.subgroupOf M) :=
    (hQpg.comap_subtype).isNilpotent
  have cC8 : Q ≤ MF M := le_maxNilpotentNormalHall hQM
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ) hQnilM hQhall
  have cC7 : Kstar ≤ MF M := hKstarQ.trans cC8
  have cC5 : q ∈ S14.piSet (MF M) := by
    rw [S14.piSet, Set.mem_ofPred_eq]
    refine Nat.mem_primeFactors.mpr ⟨hq_prime, ?_, Nat.card_pos.ne'⟩
    rw [hqdef]; exact Subgroup.card_dvd_of_le cC7
  -- **`¬ IsCyclic M_F` (conjunct 19).**
  have cC19 : ¬ IsCyclic ↥(MF M) :=
    not_isCyclic_MF_of_chiefFactor_inputs hq_prime hKprime.two_le hEA hindex cC8
  -- **Assemble.**
  exact ⟨hP1, Q, Q0, D, Nat.card ↥K, q, hKprime, hq_prime, rfl, hqdef.symm, cC5, cC6, cC7, cC8,
    hMnormQ, hcomplD, hDnil, hQ0def, hMNQ0, hindex, hMσderived, cC16, cC17, cC18, cC19⟩

/-- **BG Corollary 15.5** (mmd L4225): the decomposition `F(M) = F(M_σ) × Y` with
`Y = O_{σ(M)'}(F(M))` a cyclic `τ₂(M)`-subgroup, together with `F(M) = C_M(M_F)·M_F`,
`M'' ⊆ F(M)`, `M_F ⊆ M'`, and `K ≠ 1 → F(M) ⊆ M'`.  Direct products are encoded by the
commuting/trivial-intersection package.

Faithfulness fix (Lane G): the previous scaffold parametrized an arbitrary `H ≤ M_F` (mmd
fixes `H = M_F`) and used `M_F(M_σ)` where the textbook has the Fitting subgroup `F(M_σ)`
(`fittingInAmbient (Msigma M)`); the dropped conjuncts (a)/(b)/(d) are restored.  The `M'/M_F`
nilpotent clause of (c) is still deferred (quotient API).

`M_F` cyclic ⟹ `F(M)` cyclic exposure (Lane G 2026-06-15): the final conjunct records the
derived consequence that Corollary 15.6's proof cites ("if `M_F` is cyclic, then `F(M)` is
cyclic by Corollary 15.5").  It follows from (a)/(b): when `M_σ` is nilpotent, `F(M_σ) = M_σ =
M_F` (`fittingInAmbient_eq_self_of_isNilpotent`), so `F(M) = M_F × Y` is a product of coprime
cyclic factors (`isCyclic_prod_iff`); otherwise `M_F` is non-cyclic (Theorem 15.2) and the
implication is vacuous.  This supplies the `hFcyc` hypothesis of `typeP_kstar_in_mf_of_inputs`. -/
theorem fitting_decomposition [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ∃ Y : Subgroup G,
      -- (a) `Y = O_{σ(M)'}(F(M))` is a cyclic `τ₂(M)`-subgroup of `F(M)`.
      IsCyclic ↥Y ∧ (↑(Nat.card ↥Y).primeFactors ⊆ tau2 M) ∧ Y ≤ fittingInAmbient M ∧
      -- (b) `M'' ⊆ F(M) = C_M(M_F)·M_F = F(M_σ) × Y`.
      derivedInG (derivedInG M) ≤ fittingInAmbient M ∧
      fittingInAmbient M = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M ∧
      fittingInAmbient M = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ⊔ Y ∧
      fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ⊓ Y = ⊥ ∧
      ⁅fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M), Y⁆ = ⊥ ∧
      -- (c) `M_F ⊆ M'`.  ⚠ The book's second half of (c), "`M'/M_F` is nilpotent", is **proved**
      -- as `S16.derivedInG_quotient_maxNilpotentNormalHall_isNilpotent`; it cannot be bundled
      -- here because that proof lives downstream (`S16_MainResults/TypeBridges.lean` imports
      -- §15), so putting it in this statement would be an import cycle.  (The old comment said
      -- it was "deferred — quotient API"; stale, corrected in the issue 0177 §15 audit.)
      MF M ≤ derivedInG M ∧
      -- (d) if `K ≠ 1` (i.e. `M` is not of type `F`), then `F(M) ⊆ M'`.
      (¬ S14.IsTypeF M → fittingInAmbient M ≤ derivedInG M) ∧
      -- The derived consequence Corollary 15.6's proof cites ("`F(M)` is cyclic by Cor 15.5"):
      -- via the `F(M) = F(M_σ) × Y` decomposition (both factors cyclic, coprime orders when
      -- `M_σ` is nilpotent so `F(M_σ) = M_σ = M_F`; otherwise `M_F` is non-cyclic, vacuous).
      (IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M)) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσ
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσ
  set F := fittingInAmbient M with hF
  set FMσ := fittingInAmbient Mσ with hFMσ
  -- `Y := O_{σ'}(F(M))`, the `σ'`-Hall part of the Fitting subgroup.
  set Y : Subgroup G := opiCoreInG σᶜ F with hY
  have hFnil : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  -- ## Case-independent facts.
  -- Lemma 1: `O_σ(F(M)) = F(M_σ)`.
  have hL1 : opiCoreInG σ F = FMσ :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  -- Nilpotent Hall splitting `O_σ(F) ⊔ Y = F`.
  have hsplit : opiCoreInG σ F ⊔ Y = F := opiCoreInG_sup_compl_eq_of_isNilpotent σ
  -- Conjunct 3: `Y ≤ F`.
  have h3 : Y ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  -- Conjunct 6: `F = F(M_σ) ⊔ Y`.
  have h6 : F = FMσ ⊔ Y := by rw [← hL1, hsplit]
  -- Conjunct 7: `F(M_σ) ⊓ Y = ⊥`.
  have h7 : FMσ ⊓ Y = ⊥ := by
    rw [← hL1, hY]
    exact OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  -- Conjunct 8: `⁅F(M_σ), Y⁆ = ⊥`.
  have h8 : ⁅FMσ, Y⁆ = ⊥ := by
    rw [← hL1, hY]; exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot σ F
  -- Conjunct 9: `M_F ≤ M'`.
  have h9 : MF M ≤ derivedInG M := maxNilpotentNormalHall_le_derived hG hM
  -- `Y` is a `σ'`-group, `M_σ` is a `σ`-group, so they are coprime.
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F
  -- `M ≤ N_G(M_σ)` and `M ≤ N_G(Y)` (the latter since `Y` is characteristic in `F(M) ◁ M`).
  have hM_norm_Mσ : M ≤ Subgroup.normalizer (Mσ : Set G) :=
    OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M
  have hMσ_le_M : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hM_norm_Y : M ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
        (h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M))).mp
      (by rw [hY]; exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M)
  -- ## Lemma 15.1 inputs (a `κ`-Hall `K` and a `(κ∪σ)ᶜ`-Hall `U`), via Hall's theorem in `↥M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hK
  have hKof : K.subgroupOf M = K' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hKHall : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := by rw [hKof]; exact hK'
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M) ((S14.kappa M ∪ σ)ᶜ)
  set U : Subgroup G := U'.map M.subtype with hU
  have hUof : U.subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hUHall : Ch03.IsHallSubgroup ((S14.kappa M ∪ σ)ᶜ) (U.subgroupOf M) := by
    rw [hUof]; exact hU'
  -- Lemma 15.1 conclusion (with `Kstar := M_σ ⊓ C_M(K)`).
  obtain ⟨_, _, _, hMddσ, hKguard, _, _, _⟩ :=
    typeP_auxiliary_structure hG hM (hK ▸ Subgroup.map_subtype_le K')
      (hU ▸ Subgroup.map_subtype_le U') hKHall rfl hUHall
  -- Conjunct 4 / 10 helper: `M'' ≤ M_σ` (Lemma 15.1, unconditional).
  have hMdd_Mσ : derivedInG (derivedInG M) ≤ Mσ := hMddσ
  -- ## Case split on whether `M_σ` is nilpotent (`M_F = M_σ`).
  by_cases hcase : MF M = Mσ
  · -- ### Case I: `M_σ` nilpotent, `M_F = M_σ`, `F(M_σ) = M_σ`.
    have hMσnil : Group.IsNilpotent ↥Mσ :=
      (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mp hcase
    have hFMσ_eq : FMσ = Mσ := fittingInAmbient_eq_self_of_isNilpotent
    -- `M_σ ≤ F(M)` (nilpotent normal subgroup of `M`).
    have hMσ_le_F : Mσ ≤ F := by rw [← hFMσ_eq]; rw [h6]; exact le_sup_left
    -- `[M_σ, Y] = ⊥`, so `Y` centralizes `M_σ`; together with `Y ≤ M`, `Y ≤ C_G(M_σ) ⊓ M`.
    have hMσY : ⁅Mσ, Y⁆ = ⊥ := by rw [← hFMσ_eq]; exact h8
    have hY_cent : Y ≤ Subgroup.centralizer (Mσ : Set G) := by
      rw [Subgroup.commutator_comm] at hMσY
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMσY
    have hY_le_M : Y ≤ M := h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
    -- Corollary 15.3(a) at `H := M_σ`: `C_M(M_σ) = (C_G(M_σ) ⊓ M_σ) ⊔ X`, `X` cyclic `τ₂`.
    -- Sorry-free via `mf_centralizer_msigma_decomp` (Prop 14.2(b1)(e) + Schur–Zassenhaus +
    -- Lemma 15.1(c)); this de-axiomatises the A(8) `FittingIsTI` chain (issue 8016).
    obtain ⟨X, hXcyc, hXτ₂, hCeq⟩ := mf_centralizer_msigma_decomp hG hM
    -- `C := C_G(M_σ) ⊓ M`, `A := C_G(M_σ) ⊓ M_σ`.
    set C : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ M with hCdef
    set A : Subgroup G := Subgroup.centralizer (Mσ : Set G) ⊓ Mσ with hAdef
    have hY_C : Y ≤ C := le_inf hY_cent hY_le_M
    have hA_C : A ≤ C := inf_le_inf_left _ hMσ_le_M
    have hX_C : X ≤ C := le_sup_right.trans hCeq.ge
    -- `A ⊴ C` (so we can form the cyclic quotient `C/A`).
    have hC_norm_A : C ≤ Subgroup.normalizer (A : Set G) := by
      have h1 : C ≤ Subgroup.normalizer (Subgroup.centralizer (Mσ : Set G)) :=
        inf_le_left.trans Subgroup.le_normalizer
      have h2 : C ≤ Subgroup.normalizer (Mσ : Set G) := inf_le_right.trans hM_norm_Mσ
      exact (le_inf h1 h2).trans Subgroup.inf_normalizer_le_normalizer_inf
    have hA_normal : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer_inf).mpr
        (by rw [inf_eq_left.mpr hA_C]; exact hC_norm_A)
    -- `A ≤ M_σ` is a `σ`-group; `Y` is a `σ'`-group; hence `|A|` and `|Y|` are coprime.
    have hA_pi : ∀ r ∈ (Nat.card ↥A).primeFactors, r ∈ σ := fun r hr =>
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le (inf_le_right : A ≤ Mσ))
          Nat.card_pos.ne' hr)
    have hY_pi' : ∀ r ∈ (Nat.card ↥Y).primeFactors, r ∉ σ := fun r hr =>
      (Set.mem_compl_iff _ _).mp (hYpi r hr)
    -- `Y ⊓ A = ⊥` (coprime orders).
    have hY_inf_A : Y ⊓ A = ⊥ :=
      (Subgroup.disjoint_of_coprime_natCard
        ((Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
          hA_pi hY_pi').symm)).eq_bot
    -- Embed `Y` into the cyclic quotient `C/A` (`C/A` is a quotient image of the cyclic `X`).
    have haxtop : A.subgroupOf C ⊔ X.subgroupOf C = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hA_C hX_C, show A ⊔ X = C from hCeq.symm,
        Subgroup.subgroupOf_self]
    have hYc_inf_a : Y.subgroupOf C ⊓ A.subgroupOf C = ⊥ := by
      rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, hY_inf_A,
        MonoidHom.comap_bot]
      exact C.ker_subtype
    have hinj : Function.Injective
        ((QuotientGroup.mk' (A.subgroupOf C)).comp (Y.subgroupOf C).subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hy
      have hmem : (Y.subgroupOf C).subtype y ∈ Y.subgroupOf C ⊓ A.subgroupOf C := ⟨y.2, hy⟩
      rw [hYc_inf_a, Subgroup.mem_bot] at hmem
      rw [Subgroup.mem_bot]; exact Subtype.ext hmem
    have hxcyc : IsCyclic ↥(X.subgroupOf C) := by
      have : IsCyclic ↥X := hXcyc
      exact isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hX_C).symm.surjective
    have hquot_cyc : IsCyclic (↥C ⧸ A.subgroupOf C) := by
      have hsurj : Function.Surjective
          ((QuotientGroup.mk' (A.subgroupOf C)).comp (X.subgroupOf C).subtype) := by
        rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
        have h1 : (A.subgroupOf C ⊔ X.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) =
            ⊤ := by
          rw [haxtop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
        have hkerbot : (A.subgroupOf C).map (QuotientGroup.mk' (A.subgroupOf C)) = ⊥ := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
        rw [Subgroup.map_sup, hkerbot, bot_sup_eq] at h1
        rw [h1]
      exact isCyclic_of_surjective _ hsurj
    -- Conjunct 1: `Y` is cyclic (`Y ≅ Y.subgroupOf C ↪ C/A` cyclic).
    have hYcyc' : IsCyclic ↥(Y.subgroupOf C) :=
      isCyclic_of_surjective _ (MonoidHom.ofInjective hinj).symm.surjective
    have hYcyc : IsCyclic ↥Y :=
      isCyclic_of_surjective _ (Subgroup.subgroupOfEquivOfLe hY_C).surjective
    -- Conjunct 2: `π(Y) ⊆ τ₂` (`q ∣ |Y| ∣ [C:A] ∣ |X|`, `π(X) ⊆ τ₂`).
    have hYτ₂ : (↑(Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tau2 M := by
      intro q hq
      have hqp : q.Prime := Nat.prime_of_mem_primeFactors hq
      have hcardYc : Nat.card ↥(Y.subgroupOf C) = Nat.card ↥Y :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_C).toEquiv
      have hdvd1 : Nat.card ↥Y ∣ (A.subgroupOf C).index := by
        rw [← hcardYc, Subgroup.index_eq_card]
        exact Subgroup.card_dvd_of_injective _ hinj
      have hdvd2 : (A.subgroupOf C).index ∣ Nat.card ↥X := by
        have hidx : (A.subgroupOf C).index = (A.subgroupOf C).relIndex (X.subgroupOf C) := by
          rw [← Subgroup.relIndex_top_right, ← haxtop, Subgroup.relIndex_sup_left]
        have hcardx : Nat.card ↥(X.subgroupOf C) = Nat.card ↥X :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX_C).toEquiv
        rw [hidx, ← hcardx]
        exact Subgroup.relIndex_dvd_card (A.subgroupOf C) (X.subgroupOf C)
      have hqX : q ∈ (Nat.card ↥X).primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp,
          ((Nat.dvd_of_mem_primeFactors hq).trans hdvd1).trans hdvd2, Nat.card_pos.ne'⟩
      exact hXτ₂ hqX
    -- Conjunct 4: `M'' ⊆ F(M)` (`M'' ≤ M_σ ≤ F(M)`, `M_σ` nilpotent).
    have h4 : derivedInG (derivedInG M) ≤ F := hMdd_Mσ.trans hMσ_le_F
    -- Conjunct 5: `F(M) = (C_G(M_F) ⊓ M) ⊔ M_F = (C_G(M_σ) ⊓ M) ⊔ M_σ`.
    have h5 : F = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := by
      rw [hcase]
      -- `M ≤ N_G(C_G(M_σ))`: normalizing `M_σ` normalizes its centralizer.
      have hM_norm_CMσ : M ≤ Subgroup.normalizer (Subgroup.centralizer (Mσ : Set G)) :=
        hM_norm_Mσ.trans (normalizer_le_normalizer_centralizer Mσ)
      -- `C := C_G(M_σ) ⊓ M ⊴ M`.
      have hC_norm : M ≤ Subgroup.normalizer (C : Set G) :=
        (le_inf hM_norm_CMσ Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
      have hC_normal : (C.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hC_norm
      refine le_antisymm ?_ ?_
      · -- `F ⊆ (C_G(M_σ) ⊓ M) ⊔ M_σ`: `F = M_σ ⊔ Y`, `M_σ ≤ M_σ`, `Y ≤ C`.
        rw [h6, hFMσ_eq]
        exact sup_le (le_sup_right) (hY_C.trans le_sup_left)
      · -- `(C_G(M_σ) ⊓ M) ⊔ M_σ ⊆ F`: `M_σ ≤ F`, and `C ⊔ M_σ` is nilpotent normal (`= X ⊔ M_σ`).
        refine sup_le ?_ hMσ_le_F
        -- `C ⊔ M_σ ⊴ M` and is nilpotent, hence `⊆ F(M)`.
        have hCMσ_le_M : C ⊔ Mσ ≤ M := sup_le inf_le_right hMσ_le_M
        have hCMσ_norm : ((C ⊔ Mσ).subgroupOf M).Normal := by
          rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCMσ_le_M]
          exact le_trans (le_inf hC_norm hM_norm_Mσ)
            (Subgroup.normalizer_inf_normalizer_le_normalizer_sup C Mσ)
        -- `C ⊔ M_σ = X ⊔ M_σ` (since `C = A ⊔ X` and `A ≤ M_σ`).
        have hA_le_Mσ : A ≤ Mσ := inf_le_right
        have hCMσ_eq : C ⊔ Mσ = X ⊔ Mσ := sup_eq_sup_of_eq_sup_of_le hCeq hA_le_Mσ
        -- `X ⊔ M_σ` nilpotent: `X` cyclic, `M_σ` nilpotent, `[X, M_σ] = ⊥` (`X ≤ C_G(M_σ)`).
        have hXcent : ⁅X, Mσ⁆ = ⊥ := by
          have hXle : X ≤ Subgroup.centralizer (Mσ : Set G) := hX_C.trans inf_le_left
          exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hXle
        have hXcyc' : IsCyclic ↥X := hXcyc
        let : CommGroup ↥X := IsCyclic.commGroup
        have : Group.IsNilpotent ↥X := CommGroup.isNilpotent
        have hCMσ_nil : Group.IsNilpotent ↥(C ⊔ Mσ) := by
          rw [hCMσ_eq]; exact isNilpotent_sup_of_commutator_eq_bot hXcent
        have := hCMσ_norm
        have hCMσ_le_F : C ⊔ Mσ ≤ F :=
          le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent hCMσ_le_M hCMσ_norm
        exact le_sup_left.trans hCMσ_le_F
    -- Conjunct 10: `¬ TypeF → F(M) ⊆ M'`.  `M = K M'`, `M/M' ≅ K` (`κ`-group), `π(Y) ⊆ τ₂`,
    -- and `κ ∩ τ₂ = ∅`, so `Y ≤ M'`; with `M_σ ≤ M'` this gives `F ⊆ M'`.
    have h10 : ¬ S14.IsTypeF M → F ≤ derivedInG M := by
      intro hnotF
      have hP : S14.IsTypeP M := by
        rw [S14.isTypeF_iff_not_isTypeP] at hnotF; exact not_not.mp hnotF
      -- `K ≠ ⊥`: some `κ`-prime divides `|M|`, but a trivial `κ`-Hall would push it to the index.
      have hKne : K ≠ ⊥ := by
        obtain ⟨p, hpκ⟩ := hP
        obtain ⟨hpprime, -, P, hPmem, hPM, -⟩ := id hpκ
        have : Fact p.Prime := ⟨hpprime⟩
        -- `p ∣ |M|` (a rank-one elementary abelian `p`-subgroup `P ≤ M`).
        have hpcardP : Nat.card ↥P = p := by
          have := (OddOrder.GroupTheory.mem_elemAbelianOfRank.mp hPmem).2
          rwa [pow_one] at this
        have hpM : p ∈ (Nat.card ↥M).primeFactors :=
          Nat.mem_primeFactors.mpr ⟨hpprime,
            hpcardP ▸ Subgroup.card_dvd_of_le hPM, Nat.card_pos.ne'⟩
        intro hKbot
        -- `K = ⊥` ⟹ `(K.subgroupOf M).index = |↥M|`, so `p` divides the index of the `κ`-Hall.
        have hidx : (K.subgroupOf M).index = Nat.card ↥M := by
          rw [hKbot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
        have hpidx : p ∈ (K.subgroupOf M).index.primeFactors := by rw [hidx]; exact hpM
        exact hKHall.2 p hpidx hpκ
      obtain ⟨hMderiv, _, hcompl, _⟩ := hKguard hKne
      -- `Y ≤ M'`: image of the normal `τ₂`-subgroup `Y` in the abelian `M/M'` (order `|K|`, a
      -- `κ`-number) is trivial because `τ₂ ∩ κ = ∅`.
      have hY_le_deriv : Y ≤ derivedInG M := by
        have hYM : Y ≤ M := h3.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
        set Hsub : Subgroup ↥M := Y.subgroupOf M with hHsub
        set D : Subgroup ↥M := (derivedInG M).subgroupOf M with hDdef
        have hDcomm : D = commutator ↥M :=
          Subgroup.comap_map_eq_self_of_injective M.subtype_injective (commutator ↥M)
        have hDnorm : D.Normal := by rw [hDcomm]; infer_instance
        -- `[M : M'] = |K|` (complement), a `κ`-number.
        have hDindex : D.index = Nat.card ↥(K.subgroupOf M) := hcompl.symm.index_eq_card
        -- `Coprime |Y| [M:M']` (`π(Y) ⊆ τ₂`, `π(K) ⊆ κ`, `τ₂ ∩ κ = ∅`).
        have hKpi : ∀ r ∈ (Nat.card ↥(K.subgroupOf M)).primeFactors, r ∈ S14.kappa M :=
          fun r hr => hKHall.1 r hr
        have hcop : Nat.Coprime (Nat.card ↥Hsub) D.index := by
          rw [hDindex]
          refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne'
            Nat.card_pos.ne' (π := tau2 M) (fun r hr => ?_) (fun r hr => ?_)
          · -- `π(Y) ⊆ τ₂`.
            have : r ∈ (Nat.card ↥Y).primeFactors := by
              rwa [hHsub, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYM).toEquiv] at hr
            exact hYτ₂ this
          · -- `κ ∩ τ₂ = ∅`: a `κ`-prime has rank one, a `τ₂`-prime has rank two.
            intro hrτ₂
            have hrκ : r ∈ S14.kappa M := hKpi r hr
            have hr1 : pRank ↥M r = 1 := by
              rcases S14.kappa_subset_tau1_union_tau3 hrκ with h | h
              · exact ((mem_tau1_iff M r).mp h).2.2
              · exact ((mem_tau3_iff M r).mp h).2.2
            have hr2 : pRank ↥M r = 2 := ((mem_tau2_iff M r).mp hrτ₂).2
            rw [hr1] at hr2; exact absurd hr2 (by norm_num)
        -- `Y.subgroupOf M ≤ commutator ↥M`: image in the abelianization is trivial.
        have hHnorm : Hsub.Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).mpr hM_norm_Y
        have hcard_img_dvd_Y : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) ∣ Nat.card ↥Hsub :=
          Subgroup.card_map_dvd Hsub (QuotientGroup.mk' D)
        have hcard_img_dvd_idx : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) ∣ D.index := by
          rw [Subgroup.index_eq_card]
          exact Subgroup.card_subgroup_dvd_card _
        have hcard_img_one : Nat.card ↥(Hsub.map (QuotientGroup.mk' D)) = 1 :=
          Nat.eq_one_of_dvd_coprimes hcop hcard_img_dvd_Y hcard_img_dvd_idx
        have himg_bot : Hsub.map (QuotientGroup.mk' D) = ⊥ :=
          Subgroup.card_eq_one.mp hcard_img_one
        have hHsub_le_D : Hsub ≤ D := by
          rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at himg_bot
          exact himg_bot
        -- Transport back to `G`: `Y ≤ M'`.
        calc Y = Hsub.map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hYM).symm
          _ ≤ D.map M.subtype := Subgroup.map_mono hHsub_le_D
          _ = derivedInG M := Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le _)
      rw [h6, hFMσ_eq]
      exact sup_le ((OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)) hY_le_deriv
    -- Conjunct 11: `M_F` cyclic → `F(M)` cyclic (`F = M_F × Y`, both cyclic coprime).
    have h11 : IsCyclic ↥(MF M) → IsCyclic ↥F := by
      intro hMFcyc
      have := hMFcyc
      have := hYcyc
      -- `F = M_F ⊔ Y` with `M_F ⊓ Y = ⊥`, `[M_F, Y] = ⊥`, coprime orders.
      have hMFY_inf : MF M ⊓ Y = ⊥ := by rw [hcase, ← hFMσ_eq]; exact h7
      have hMFY_comm : ⁅(MF M : Subgroup G), Y⁆ = ⊥ := by rw [hcase, ← hFMσ_eq]; exact h8
      have hFeq : F = MF M ⊔ Y := by rw [h6, hFMσ_eq, hcase]
      have hcop : Nat.Coprime (Nat.card ↥(MF M)) (Nat.card ↥Y) := by
        refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl Nat.card_pos.ne' Nat.card_pos.ne'
          (π := σ) (fun r hr => ?_) hY_pi'
        rw [hcase] at hr
        exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r hr
      -- Cyclic product (orderOf approach, mirroring `S06.isCyclic_sup`).
      obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := ↥(MF M))
      obtain ⟨b, hb⟩ := IsCyclic.exists_generator (α := ↥Y)
      have hMF_le : MF M ≤ MF M ⊔ Y := le_sup_left
      have hY_le : Y ≤ MF M ⊔ Y := le_sup_right
      have hoa : orderOf (Subgroup.inclusion hMF_le a) = Nat.card ↥(MF M) := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective _) a,
          orderOf_eq_card_of_forall_mem_zpowers ha]
      have hob : orderOf (Subgroup.inclusion hY_le b) = Nat.card ↥Y := by
        rw [orderOf_injective _ (Subgroup.inclusion_injective _) b,
          orderOf_eq_card_of_forall_mem_zpowers hb]
      have hMFnorm_Y : MF M ≤ Subgroup.normalizer (Y : Set G) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMFY_comm).trans
          (OddOrder.Isaacs.Ch07.centralizer_le_normalizer Y)
      have hcardsup : Nat.card ↥(MF M ⊔ Y) = Nat.card ↥(MF M) * Nat.card ↥Y := by
        have hprod := Subgroup.card_HK_mul_card_inf_eq_card_mul_card (MF M) Y
        rw [hMFY_inf, Subgroup.card_bot, mul_one] at hprod
        rwa [show ((MF M : Set G) * (Y : Set G)) = ((MF M ⊔ Y : Subgroup G) : Set G) from
          (Subgroup.coe_mul_of_left_le_normalizer_right (MF M) Y hMFnorm_Y).symm] at hprod
      have hcomm : Commute (Subgroup.inclusion hMF_le a) (Subgroup.inclusion hY_le b) := by
        have hab : ((a : G)) * (b : G) = (b : G) * (a : G) :=
          (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hMFY_comm a.2) (b : G) b.2).symm
        exact Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inclusion]; exact hab)
      rw [hFeq]
      refine isCyclic_of_orderOf_eq_card
        (Subgroup.inclusion hMF_le a * Subgroup.inclusion hY_le b) ?_
      rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [hoa, hob]; exact hcop),
        hoa, hob, hcardsup]
    exact ⟨Y, hYcyc, hYτ₂, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  · -- ### Case II: `M_σ` not nilpotent, `M_F ≠ M_σ`, so `M` is type `P1` and `F(M) ⊆ M_σ`.
    obtain ⟨_hP1, Q, _Q0, _D, _p, _q, _, _, _, _, _, _, _, hQsubMF, _, _, _, _, _, _, hMσderiv,
        _, hFsubMσ, hFQ, hMFnc⟩ :=
      mf_ne_msigma_typeP1_structure hG hM hcase (Subgroup.map_subtype_le K') hKHall rfl
    -- In Case II: `F(M) ⊆ M_σ`, so `Y = O_{σ'}(F(M)) = ⊥` and `F(M) = F(M_σ)`.
    -- `Y = ⊥`: `F(M) ⊆ M_σ` is a `σ`-group, so its `σ'`-Hall core is trivial.
    have hYbot : Y = ⊥ := by
      rw [hY]
      refine OddOrder.GroupTheory.opiCoreInG_compl_eq_bot_of_isPiSubgroup ?_
      intro r hr
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup M r
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hFsubMσ) Nat.card_pos.ne' hr)
    -- `F(M) = F(M_σ)`: `F(M) ◁ M` nilpotent `⊆ M_σ ⟹ ◁ M_σ ⟹ ⊆ F(M_σ)`; `F(M_σ) ⊆ F(M)` (Lemma 1).
    have hFMσ_eq : F = FMσ := by
      refine le_antisymm ?_ ?_
      · -- `F ⊆ M_σ`, `F ◁ M_σ` (since `F ◁ M`), `F` nilpotent ⟹ `F ⊆ F(M_σ)`.
        have hF_norm_Mσ : (F.subgroupOf Mσ).Normal :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hFsubMσ).mpr
            (hMσ_le_M.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
              (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
              (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)))
        exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent hFsubMσ hF_norm_Mσ
      · -- `F(M_σ) ⊆ O_σ(F(M)) ⊆ F(M)`.
        rw [← hL1]; exact OddOrder.GroupTheory.opiCoreInG_le σ F
    -- Now assemble.  With `Y = ⊥`, conjuncts (a) and the `× Y` split collapse.
    have hYcyc : IsCyclic ↥Y := by rw [hYbot]; infer_instance
    have hYτ₂ : (↑(Nat.card ↥Y).primeFactors : Set ℕ) ⊆ tau2 M := by
      rw [hYbot, Subgroup.card_bot]; simp
    -- Conjunct 4: `M'' ⊆ F(M)`.
    have h4 : derivedInG (derivedInG M) ≤ F := by
      have hMdd_F : derivedInG (derivedInG M) ≤ fittingInAmbient M := ‹_›
      exact hMdd_F
    -- Conjunct 5 (Case II, `M_F ≠ M_σ`): `F(M) = (C_G(M_F) ⊓ M) ⊔ M_F` (mmd 15.2(g)
    -- "(b) `F(M) = C_M(H)H`" with `H = M_F`).
    have h5 : F = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := by
      have hMF_le_F : MF M ≤ F := maxNilpotentNormalHall_le_fittingInG M
      have hQ_le_MF : Q ≤ MF M := hQsubMF
      -- `C_M(M_F) ⊆ C_M(Q) ⊆ Q ⊔ C_M(Q) = F(M)` (Theorem 15.2(g) equality `hFQ`).
      have hCMF_le_F : Subgroup.centralizer (MF M : Set G) ⊓ M ≤ F := by
        have hsub : Subgroup.centralizer (MF M : Set G) ⊓ M ≤
            Subgroup.centralizer (Q : Set G) ⊓ M := by
          refine inf_le_inf_right _ ?_
          intro x hx
          rw [Subgroup.mem_centralizer_iff] at hx ⊢
          exact fun g hg => hx g (hQ_le_MF hg)
        rw [hF, hFQ]; exact hsub.trans le_sup_right
      refine le_antisymm ?_ (sup_le hCMF_le_F hMF_le_F)
      -- `⊆` (mmd 15.2(g)): the `σ'`-free, type-`P1` structural step `F(M) ⊆ C_M(M_F)·M_F`.
      -- Strategy (general, §14-independent): `M_F` is the full Hall `π(M_F)`-part of `F(M)`, so the
      -- nilpotent `F(M)` splits as `F(M) = M_F × O_{π(M_F)'}(F(M))`, and the second factor
      -- centralizes `M_F` (distinct Hall components of a nilpotent group commute).
      set π : Set ℕ := ↑(Nat.card ↥(MF M)).primeFactors with hπ
      -- `F ≤ M` and `M ≤ N_G(F)` (`F` is normal in `M`).
      have hF_le_M : F ≤ M := OddOrder.BG.Ch2.S08.fittingInG_le M
      have hM_norm_F : M ≤ Subgroup.normalizer (F : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
          (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)
      -- `M_F ≤ O_π(F)`: `M_F ≤ F`, `(M_F).subgroupOf F ⊴ F` (as `F ≤ M ≤ N_G(M_F)`), `M_F` a
      -- `π`-group.
      have hMF_norm_F : (((MF M).subgroupOf F)).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hMF_le_F).mpr
          (hF_le_M.trans (maxNilpotentNormalHall_le_normalizer M))
      have hMF_pi : Subgroup.IsPiSubgroup π (MF M) := fun p hp => by
        rw [hπ]; exact Finset.mem_coe.mpr hp
      have hMF_le_Oπ : MF M ≤ OddOrder.GroupTheory.opiCoreInG π F :=
        OddOrder.GroupTheory.le_opiCoreInG_of_normal_of_isPiSubgroup hMF_le_F hMF_norm_F hMF_pi
      -- `O_π(F) ≤ M_F`: `O_π(F)` is a normal `π`-subgroup of `↥M`, and `M_F` is `π`-Hall in `↥M`.
      have hOπ_le_F : OddOrder.GroupTheory.opiCoreInG π F ≤ F :=
        OddOrder.GroupTheory.opiCoreInG_le π F
      have hOπ_le_M : OddOrder.GroupTheory.opiCoreInG π F ≤ M := hOπ_le_F.trans hF_le_M
      have hObar_norm : ((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOπ_le_M).mpr
          (OddOrder.GroupTheory.le_normalizer_opiCoreInG_of_le_normalizer π hM_norm_F)
      have hObar_pi :
          Ch03.Subgroup.IsPiGroup π ((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M) := by
        intro p hp
        have hcardO : Nat.card ↥((OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M) =
            Nat.card ↥(OddOrder.GroupTheory.opiCoreInG π F) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOπ_le_M).toEquiv
        exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG π F p (by rwa [hcardO] at hp)
      have hObar_le_Hbar :
          (OddOrder.GroupTheory.opiCoreInG π F).subgroupOf M ≤ (MF M).subgroupOf M :=
        Ch03.Subgroup.IsPiGroup.normal_le_hall hObar_pi (maxNilpotentNormalHall_isHall M)
      have hMF_le_M : MF M ≤ M := maxNilpotentNormalHall_le M
      have hOπ_le_MF : OddOrder.GroupTheory.opiCoreInG π F ≤ MF M := by
        have := Subgroup.map_mono (f := M.subtype) hObar_le_Hbar
        rwa [Subgroup.map_subgroupOf_eq_of_le hOπ_le_M,
          Subgroup.map_subgroupOf_eq_of_le hMF_le_M] at this
      have hOπ_eq_MF : OddOrder.GroupTheory.opiCoreInG π F = MF M :=
        le_antisymm hOπ_le_MF hMF_le_Oπ
      -- `F = O_π(F) ⊔ O_{π'}(F) = M_F ⊔ O_{π'}(F)`.
      have hsplit : OddOrder.GroupTheory.opiCoreInG π F ⊔
          OddOrder.GroupTheory.opiCoreInG πᶜ F = F :=
        opiCoreInG_sup_compl_eq_of_isNilpotent π
      -- `O_{π'}(F)` centralizes `M_F = O_π(F)`, and lies in `M`, so `≤ C_G(M_F) ⊓ M`.
      have hcomm : ⁅OddOrder.GroupTheory.opiCoreInG π F,
          OddOrder.GroupTheory.opiCoreInG πᶜ F⁆ = ⊥ :=
        OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot π F
      have hOπ'_cent : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤
          Subgroup.centralizer (MF M : Set G) := by
        have hcomm' : ⁅OddOrder.GroupTheory.opiCoreInG πᶜ F,
            OddOrder.GroupTheory.opiCoreInG π F⁆ = ⊥ := by
          rw [Subgroup.commutator_comm]; exact hcomm
        rw [← hOπ_eq_MF]
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm'
      have hOπ'_le_M : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤ M :=
        (OddOrder.GroupTheory.opiCoreInG_le πᶜ F).trans hF_le_M
      have hOπ'_le : OddOrder.GroupTheory.opiCoreInG πᶜ F ≤
          Subgroup.centralizer (MF M : Set G) ⊓ M := le_inf hOπ'_cent hOπ'_le_M
      -- Assemble: `F = M_F ⊔ O_{π'}(F) ≤ (C_G(M_F) ⊓ M) ⊔ M_F`.
      calc F = OddOrder.GroupTheory.opiCoreInG π F ⊔
                OddOrder.GroupTheory.opiCoreInG πᶜ F := hsplit.symm
        _ = MF M ⊔ OddOrder.GroupTheory.opiCoreInG πᶜ F := by rw [hOπ_eq_MF]
        _ ≤ MF M ⊔ (Subgroup.centralizer (MF M : Set G) ⊓ M) := sup_le_sup_left hOπ'_le _
        _ = (Subgroup.centralizer (MF M : Set G) ⊓ M) ⊔ MF M := sup_comm _ _
    -- Conjunct 10: `¬ TypeF → F(M) ⊆ M'`.  `F(M) ⊆ M_σ = M'` (Theorem 15.2).
    have h10 : ¬ S14.IsTypeF M → F ≤ derivedInG M := fun _ => hFsubMσ.trans hMσderiv.le
    -- Conjunct 11: `M_F` cyclic → `F(M)` cyclic.  Vacuous: `M_F` is non-cyclic (Theorem 15.2).
    have h11 : IsCyclic ↥(MF M) → IsCyclic ↥F := fun h => absurd h hMFnc
    exact ⟨Y, hYcyc, hYτ₂, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩

/-- **§14-independent assembly of BG Corollary 15.6** from its §14/§15 inputs taken as
hypotheses.  This packages the *logic* of Corollary 15.6 (mmd L4232) with no citation of the §14
scaffold at all — it was written while §14 was still a `sorry`-stated skeleton.  §14 has since
landed, and `typeP_kstar_in_mf` discharges each hypothesis by a single citation and applies this
skeleton.  Hypothesis provenance (mmd L4434 dependency table):

* `hKne` (`K* ≠ 1`) ← Proposition 14.2(c) (`typeP_structure`, conjunct `Kstar ≠ ⊥`);
* `hcyc` (`K K*` cyclic) ← Theorem 14.7(d) (`typeP_duality`, conjunct `IsCyclic (K ⊔ Kstar)`);
* `hKsubMF` (`K* ⊆ M_F`) ← Theorem 15.2(b)(c) (case-split on `M_F = M_σ`);
* `hcompl`/`hcop` (`M = K M'`, `K ∩ M' = 1`, coprime) ← Theorem 14.7(h) / Lemma 15.1's `K ≠ 1`
  clause;
* `hFcyc` (`M_F` cyclic ⟹ `F(M)` cyclic) ← Corollary 15.5 (the consequence its proof of 15.6
  cites).

The two nontrivial steps are unconditional: `K* ⊆ M''`
(`Msigma_inf_centralizer_le_derivedDerived_of_isComplement'`) and the `M_F`-not-cyclic
contradiction (`fittingInAmbient_cyclic_imp_derivedDerived_eq_bot`, giving `M'' = 1`, against
`K* ⊆ M''` and `K* ≠ 1`). -/
theorem typeP_kstar_in_mf_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G))
    (hKne : Kstar ≠ ⊥) (hcyc : IsCyclic ↥(K ⊔ Kstar)) (hKsubMF : Kstar ≤ MF M)
    (hcompl : Subgroup.IsComplement' ((derivedInG M).subgroupOf M) (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥((derivedInG M).subgroupOf M))
      (Nat.card ↥(K.subgroupOf M)))
    (hFcyc : IsCyclic ↥(MF M) → IsCyclic ↥(fittingInAmbient M)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have := hcyc
  -- `K* ⊆ M''`:  the §14-independent conjunct-4 engine.
  have hKsubdd : Kstar ≤ derivedInG (derivedInG M) := by
    rw [hKstar]
    exact Msigma_inf_centralizer_le_derivedDerived_of_isComplement' hG hM hcompl hcop
  refine ⟨hKne, Subgroup.isCyclic_of_le (le_sup_right : Kstar ≤ K ⊔ Kstar), hKsubMF,
    hKsubdd, ?_⟩
  -- `M_F` not cyclic:  else `F(M)` cyclic ⟹ `M'' = 1`, but `K* ⊆ M''` and `K* ≠ 1`.
  intro hcycMF
  have hMdd : derivedInG (derivedInG M) = ⊥ :=
    fittingInAmbient_cyclic_imp_derivedDerived_eq_bot (hFcyc hcycMF)
  exact hKne (le_bot_iff.mp (hMdd ▸ hKsubdd))

/-- **BG Corollary 15.6** (mmd L4174): for a type-P maximal subgroup, `Kstar` is
nontrivial cyclic and lies in `M_F`, while `M_F` itself is not cyclic. -/
theorem typeP_kstar_in_mf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K Kstar : Subgroup G} (hM : M ∈ maximalSubgroups G) (hP : S14.IsTypeP M)
    (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    Kstar ≠ ⊥ ∧ IsCyclic ↥Kstar ∧ Kstar ≤ MF M ∧
      Kstar ≤ derivedInG (derivedInG M) ∧ ¬ IsCyclic ↥(MF M) := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- A Hall `(κ ∪ σ)ᶜ`-subgroup `U` of `M` exists by solvability (Hall's theorem); this is the
  -- `U`-factor of the type-`P` decomposition `M = K U M_σ` needed to invoke Proposition 14.2.
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥M)
    ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
  have hUeq : (U'.map M.subtype).subgroupOf M = U' :=
    Subgroup.comap_map_eq_self_of_injective M.subtype_injective U'
  have hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      ((U'.map M.subtype).subgroupOf M) := by rw [hUeq]; exact hU'
  -- `K* ≠ 1`:  Proposition 14.2(c) (`typeP_structure`).
  have hKne : Kstar ≠ ⊥ := (typeP_structure hG hM hP hKM hK hKstar hU).2.1
  -- `K K*` cyclic and the `M = K M'` complement / coprime data:  Theorem 14.7(d),(h).
  obtain ⟨hcompl, hcop, _Mstar, ⟨_, _, _, _, hcyc, _, _, _⟩, _⟩ :=
    typeP_duality hG hM hP hKM hK hKstar
  -- `K* ⊆ M_F`:  Theorem 15.2 when `M_F ≠ M_σ`, else `K* ⊆ M_σ = M_F` directly.
  have hKsubMF : Kstar ≤ MF M := by
    by_cases hMF : MF M = OddOrder.BG.Ch3.S10.Msigma M
    · rw [hKstar, hMF]; exact inf_le_left
    · obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, hk, _⟩ :=
        mf_ne_msigma_typeP1_structure hG hM hMF hKM hK hKstar
      exact hk
  -- `M_F` cyclic ⟹ `F(M)` cyclic:  Corollary 15.5 (`fitting_decomposition`, last conjunct).
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hFcyc⟩ := fitting_decomposition hG hM
  exact typeP_kstar_in_mf_of_inputs hG hM hKstar hKne hcyc hKsubMF hcompl hcop hFcyc

end OddOrder.BG.Ch4.S15


