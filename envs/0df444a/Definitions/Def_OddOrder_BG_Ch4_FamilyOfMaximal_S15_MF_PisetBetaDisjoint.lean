-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_PisetBetaDisjoint
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_PisetBetaDisjoint
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:08:20.450991+00:00
-- url     : https://prove2.me/theorems/03d0b4bd-c038-4c58-a7ba-e8ef7dce284f
-- title:
--   BG §15: $\pi$-set and $\beta$ disjointness (TI-failure part)
-- statement:
--   A part of the TI-failure development of §15 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the TI-failure file. It consists of lemmas only: if $\pi(M_F)$ and $\beta$ are disjoint then $M_F=M_\sigma$, the $O_\pi$-core of the $\sigma$-complement in $F(M)$ is cyclic with prime factors in $\tau_2$, and $\tau_3=\emptyset$ forces $E_3=1$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 27 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/PisetBetaDisjoint.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/PisetBetaDisjoint.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **BG Theorem 15.2(b), contrapositive form** (mmd L4185): if no prime divides `M_F` and lies
in `β(M)`, then `M_F = M_σ`.  Theorem 15.2 shows that whenever `M_F ≠ M_σ`, the prime `q = |K*|`
satisfies `q ∈ π(M_F) ∩ β(M)`; the contrapositive gives the claim.  A Hall `κ(M)`-subgroup `K`
needed to invoke 15.2 exists by solvability of `M` (Hall's theorem).

This is the `M_F = M_σ` endgame of Theorem 15.7(a): once the rank-theoretic core
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` establishes `π(M_F) ∩ β(M) = ∅`, this lemma
delivers `M_F = M_σ` (equivalently, `M_σ` nilpotent). -/
theorem mf_eq_msigma_of_piSet_inf_beta_disjoint [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hdisj : ∀ q : ℕ, q ∈ S14.piSet (MF M) → q ∉ OddOrder.BG.Ch3.S10.beta M) :
    MF M = OddOrder.BG.Ch3.S10.Msigma M := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  by_contra hne
  -- A Hall `κ(M)`-subgroup `K` of `M` exists by Hall's theorem in the solvable group `↥M`.
  obtain ⟨K', hK'⟩ := Ch03.hall_E_exists (G := ↥M) (S14.kappa M)
  set K : Subgroup G := K'.map M.subtype with hKdef
  have hKM : K ≤ M := hKdef ▸ Subgroup.map_subtype_le K'
  have hKeq : K.subgroupOf M = K' :=
    hKdef ▸ Subgroup.comap_map_eq_self_of_injective M.subtype_injective K'
  have hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M) := hKeq ▸ hK'
  -- Theorem 15.2(b): for `M_F ≠ M_σ`, the prime `q = |K*|` lies in `π(M_F) ∩ β(M)`.
  obtain ⟨_, _, _, _, _, _, _, _, _, hqπ, hqβ, _⟩ :=
    (mf_ne_msigma_typeP1_structure hG hM hne hKM hK rfl).2
  exact hdisj _ hqπ hqβ

/-- **BG Corollary 15.5(a)**: `O_{σ(M)'}(F(M))` is cyclic.  Extracted from `fitting_decomposition`,
whose cyclic witness `Y` (a `τ₂(M) ⊆ σ(M)ᶜ`-group, normal in the nilpotent `F(M)` and complementing
`O_{σ(M)}(F(M)) = F(M_σ)`) equals `O_{σ(M)'}(F(M))` by modularity. -/
theorem opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    IsCyclic ↥(opiCoreInG (OddOrder.BG.Ch3.S10.sigma M)ᶜ (fittingInAmbient M)) := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  set F := fittingInAmbient M with hFdef
  obtain ⟨Y, hYcyc, hYtau2, hYleF, _, _, hF_eq, _hFmσ_Y_bot, hcomm, _, _, _⟩ :=
    fitting_decomposition hG hM
  -- `O_σ(F) = F(M_σ)`, so `F = O_σ(F) ⊔ Y`.
  have hOσ : opiCoreInG σ F = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  have hF_eq2 : F = opiCoreInG σ F ⊔ Y := by rw [hOσ]; exact hF_eq
  -- `Y ⊴ F`: normalized by `Y` and by `F(M_σ)` (which centralizes it), and `F = F(M_σ) ⊔ Y`.
  have hYnorm : (Y.subgroupOf F).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hYleF).mpr ?_
    rw [hF_eq]
    refine sup_le ?_ Subgroup.le_normalizer
    have h1 : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  -- `Y` is a `σᶜ`-group (`π(Y) ⊆ τ₂(M) ⊆ σᶜ`).
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := fun r hr => tau2_subset_sigma_compl M (hYtau2 hr)
  have hYle : Y ≤ opiCoreInG σᶜ F := le_opiCoreInG_of_normal_of_isPiSubgroup hYleF hYnorm hYpi
  have hinf : opiCoreInG σ F ⊓ opiCoreInG σᶜ F = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  -- `O_σ(F) = F(M_σ)` centralizes `Y`, so it normalizes `Y`.
  have hEnorm : opiCoreInG σ F ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hOσ]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  -- `O_{σᶜ}(F) = Y` by the normality-aware Dedekind law, hence cyclic.
  have hDF : opiCoreInG σᶜ F ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  have hDY : opiCoreInG σᶜ F = Y := by
    have hkey := Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot
      (W := Y) (A := opiCoreInG σ F) (L := opiCoreInG σᶜ F) hYle hinf hEnorm
    rw [← hkey, sup_comm, ← hF_eq2, inf_eq_right.mpr hDF]
  rw [hDY]; exact hYcyc

/-- **BG Corollary 15.5(a), `τ₂`-membership form**: the `σ'`-part `O_{σ(M)'}(F(M))` of the Fitting
subgroup is a `τ₂(M)`-group.  Companion to `opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic`,
extracted from `fitting_decomposition`'s cyclic witness `Y` (which equals `O_{σ'}(F(M))` by the
modular argument). -/
theorem opiCoreInG_sigmaCompl_fittingInAmbient_primeFactors_subset_tau2 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) :
    ↑(Nat.card ↥(opiCoreInG (OddOrder.BG.Ch3.S10.sigma M)ᶜ (fittingInAmbient M))).primeFactors ⊆
      tau2 M := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  set F := fittingInAmbient M with hFdef
  obtain ⟨Y, _hYcyc, hYtau2, hYleF, _, _, hF_eq, _, hcomm, _, _, _⟩ := fitting_decomposition hG hM
  have hOσ : opiCoreInG σ F = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
    opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
  have hF_eq2 : F = opiCoreInG σ F ⊔ Y := by rw [hOσ]; exact hF_eq
  have hYnorm : (Y.subgroupOf F).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hYleF).mpr ?_
    rw [hF_eq]
    refine sup_le ?_ Subgroup.le_normalizer
    have h1 : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ Subgroup.centralizer (Y : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact h1.trans (Subgroup.centralizer_le_normalizer _)
  have hYpi : Subgroup.IsPiSubgroup σᶜ Y := fun r hr => tau2_subset_sigma_compl M (hYtau2 hr)
  have hYle : Y ≤ opiCoreInG σᶜ F := le_opiCoreInG_of_normal_of_isPiSubgroup hYleF hYnorm hYpi
  have hinf : opiCoreInG σ F ⊓ opiCoreInG σᶜ F = ⊥ :=
    OddOrder.GroupTheory.inf_eq_bot_of_isPiSubgroup_of_isPiSubgroup_compl
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σ F)
      (OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F)
  have hEnorm : opiCoreInG σ F ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hOσ]
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hDF : opiCoreInG σᶜ F ≤ F := OddOrder.GroupTheory.opiCoreInG_le σᶜ F
  have hDY : opiCoreInG σᶜ F = Y := by
    have hkey := Subgroup.inf_sup_eq_of_le_normalizer_of_inf_eq_bot
      (W := Y) (A := opiCoreInG σ F) (L := opiCoreInG σᶜ F) hYle hinf hEnorm
    rw [← hkey, sup_comm, ← hF_eq2, inf_eq_right.mpr hDF]
  rw [hDY]; exact hYtau2

/-- **BG Theorem 15.7(d), the `τ₃(M) = ∅` prime-set core**: if `M' ≤ F(M)` then `τ₃(M) = ∅`.

`F(M) = F(M_σ) × O_{σ'}(F(M))` (`fitting_decomposition`, an internal direct product) with `F(M_σ)`
a `σ(M)`-group (`= O_σ(F(M))`) and `O_{σ'}(F(M))` a `τ₂(M)`-group, so every prime of `M' ≤ F(M)` is
in `σ(M) ∪ τ₂(M)`.  A `τ₃(M)`-prime is `∉ σ(M)` (hence `∈ τ₂(M)`, `r_p = 2`) yet lies in `π(M')`
with `r_p = 1` — contradiction.

This is the `defE`/`E3_1` prime-set half of Corollary 15.9's cyclic Frobenius complement (Coq
`nonTI_Fitting_structure` part (d)): once `τ₃(M) = ∅` the `τ₃`-Hall `E₃` of any `σ(M)'`-complement
is
trivial (`E3_eq_bot_of_tau3_eq_empty`), so `E = E₁E₂` and — with `τ₂(M) = ∅` (Theorem 15.8) —
`E = E₁`
is cyclic.  The remaining upstream gate is the `¬FittingIsTI`-specific `M' ≤ F(M)` (`M'` nilpotency;
issue 2037). -/
theorem tau3_eq_empty_of_derivedInG_le_fittingInAmbient [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hM'F : derivedInG M ≤ fittingInAmbient M) : tau3 M = ∅ := by
  classical
  obtain ⟨Y, -, hYtau2, -, -, -, hF6, hF7, hF8, -, -, -⟩ := fitting_decomposition hG hM
  set Fσ : Subgroup G := fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) with hFσdef
  -- `F(M) = F(M_σ) × Y` ⟹ `|F(M)| = |F(M_σ)| · |Y|`.
  have hFσnormY : Fσ ≤ Subgroup.normalizer (Y : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hF8).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcard : Nat.card ↥(fittingInAmbient M) = Nat.card ↥Fσ * Nat.card ↥Y := by
    rw [hF6]; exact card_sup_eq_mul_of_le_normalizer_of_disjoint hFσnormY hF7
  -- `π(F(M_σ)) ⊆ σ(M)` (`F(M_σ) = O_σ(F(M))`, a `σ`-core).
  have hFσσ : ∀ p ∈ (Nat.card ↥Fσ).primeFactors, p ∈ OddOrder.BG.Ch3.S10.sigma M := by
    intro p hp
    rw [hFσdef, ← opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma] at hp
    exact OddOrder.GroupTheory.isPiSubgroup_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M)
      (fittingInAmbient M) p hp
  -- No `τ₃`-prime survives.
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  rw [mem_tau3_iff]
  rintro ⟨hpσ, hpM', hp1⟩
  have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpM'
  have hpF : p ∈ (Nat.card ↥(fittingInAmbient M)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpprime,
      (Nat.dvd_of_mem_primeFactors hpM').trans (Subgroup.card_dvd_of_le hM'F), Nat.card_pos.ne'⟩
  rw [hcard, Nat.primeFactors_mul Nat.card_pos.ne' Nat.card_pos.ne', Finset.mem_union] at hpF
  rcases hpF with h | h
  · exact hpσ (hFσσ p h)
  · have hp2 : pRank ↥M p = 2 := ((mem_tau2_iff M p).mp (hYtau2 (Finset.mem_coe.mpr h))).2
    omega

/-- **`E₃ = ⊥` from `τ₃(M) = ∅`**: the `τ₃(M)`-Hall factor `E₃` of any `σ(M)'`-complement `E`-setup
is trivial when `M` has no `τ₃`-primes.  A `{τ₃}`-Hall subgroup of the empty prime set has order
coprime to every prime, hence order `1`.  Companion to
`tau3_eq_empty_of_derivedInG_le_fittingInAmbient` (BG Theorem 15.7(d), `E3_1`). -/
theorem E3_eq_bot_of_tau3_eq_empty [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃) (htau3 : tau3 M = ∅) :
    E₃ = ⊥ := by
  classical
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpsub : p ∈ (Nat.card ↥(E₃.subgroupOf E)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₃_le).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
  have hmem : p ∈ tau3 M := hsetup.E₃_hall.1 p hpsub
  rw [htau3] at hmem
  exact hmem

/-- **`E₂ = ⊥` from `τ₂(M) = ∅`**: the `τ₂(M)`-Hall factor `E₂` of any
`σ(M)'`-complement `E`-setup is
trivial when `M` has no `τ₂`-*primes* (Theorem 15.8's `τ₂(M) = ∅` for the Corollary 15.9 escape, in
the `∀ p, p.Prime → p ∉ τ₂(M)` form output by `tau2_transfer_constraint`).  `τ₂`-analogue of
`E3_eq_bot_of_tau3_eq_empty`. -/
theorem E2_eq_bot_of_tau2_eq_empty [Finite G] {M E E₁ E₂ E₃ : Subgroup G}
    (hsetup : OddOrder.BG.Ch3.S12.SubgroupESetup M E E₁ E₂ E₃)
    (htau2 : ∀ p : ℕ, p.Prime → p ∉ tau2 M) :
    E₂ = ⊥ := by
  classical
  rw [← Subgroup.card_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
  have hpsub : p ∈ (Nat.card ↥(E₂.subgroupOf E)).primeFactors := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hsetup.E₂_le).toEquiv]
    exact Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
  exact htau2 p hp (hsetup.E₂_hall.1 p hpsub)

/-- **Type-`P₂` `M_F`-internal Fitting decomposition** (BG Corollary 15.5; the `M' = M_F × U`
form feeding Proposition 16.1's forward bridges).  For a type-`P₂` maximal subgroup `M` with
`κ`-Hall `K` and `(κ ∪ σ)'`-Hall `U`, the derived subgroup `M'` is the internal direct product of
the Fitting kernel `M_F` and `U` (the complement `hDcompl`), the Fitting subgroup is
`F(M) = M_F ⊔ (U ⊓ C_M(M_F))` (`hFiteq`), and `M'' ≤ F(M)` (`hSDfit`).

This discharges the three genuinely-deep `M_F`-internal residuals (`hDcompl`/`hSDfit`/`hFiteq`)
of `typePData_of_isTypeP_of_inputs`, the shared linchpin of the `hP2II`/`hP1neIIIIV`/`hP1eqV`
forward bridges of `proposition_type_classification`.

Proof: `M_F = M_σ` (`M_σ` nilpotent for type `P₂`) and `M' = U ⊔ M_σ` with `U ⊓ M_σ = ⊥`
(Lemma 15.1(b)) give the complement.  The Fitting identity routes through `Y := O_{σ'}(F(M))`,
the `τ₂`-part of `F(M)` (Corollary 15.5(a)): `Y` is a `(κ ∪ σ)'`-group normal in `M`
(`π(Y) ⊆ τ₂`, and `τ₂ ∩ κ = ∅` by rank), hence `Y ≤ U`, and `Y` centralizes `M_σ = M_F`, so
`F(M) = M_F ⊔ Y ≤ M_F ⊔ (U ⊓ C_M(M_F)) ≤ F(M)`. -/
theorem typeP2_mf_internal_fitting_decomposition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP2 : S14.IsTypeP2 M) (hKM : K ≤ M) (hUM : U ≤ M)
    (hKne : K ≠ ⊥)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M)) :
    Subgroup.IsComplement' ((maxNilpotentNormalHall M).subgroupOf (derivedInG M))
        (U.subgroupOf (derivedInG M)) ∧
      secondDerivedInAmbient M ≤ maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) ∧
      (OddOrder.Isaacs.Ch01.fitting ↥M).map M.subtype = maxNilpotentNormalHall M ⊔
        (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
  classical
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  set Mσ := OddOrder.BG.Ch3.S10.Msigma M with hMσdef
  set F := fittingInAmbient M with hFdef
  have hFnil : Group.IsNilpotent ↥F := OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M
  -- `M_F = M_σ`: `M_σ` is nilpotent for type `P₂`.
  have hMσnil : Group.IsNilpotent ↥Mσ := S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2
  have hMFMσ : maxNilpotentNormalHall M = Mσ :=
    (maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hMσnil
  -- Lemma 15.1(b): `M' = U ⊔ M_σ`.
  obtain ⟨hM'eq, _hUab⟩ := typeP_hall_derived_eq_and_abelian hG hM hKM hUM hKne hK hU
  have hMσ_le_M' : Mσ ≤ derivedInG M := OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM
  have hM'_le_M : derivedInG M ≤ M := Subgroup.map_subtype_le _
  have hMσ_le_M : Mσ ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  have hU_le_M' : U ≤ derivedInG M := by rw [hM'eq]; exact le_sup_left
  -- `U ⊓ M_σ = ⊥` (coprime Hall orders).
  have hUMσ_bot : U ⊓ Mσ = ⊥ := by
    have hMσHall : Ch03.IsHallSubgroup σ (Mσ.subgroupOf M) :=
      OddOrder.BG.Ch3.S10.Msigma_subgroupOf_isHall hG hM
    have hcop : Nat.Coprime (Nat.card ↥U) (Nat.card ↥Mσ) := by
      refine Ch03.Nat.coprime_of_isPiGroup_of_isPiGroup_compl
        (π := (S14.kappa M ∪ σ)ᶜ) Nat.card_pos.ne' Nat.card_pos.ne' ?_ ?_
      · intro p hp
        exact hU.1 p (by rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUM).toEquiv])
      · intro p hp hpcompl
        have hpMσ : p ∈ (Nat.card ↥(Mσ.subgroupOf M)).primeFactors := by
          rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMσ_le_M).toEquiv]
        exact hpcompl (Or.inr (hMσHall.1 p hpMσ))
    exact (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  -- `Y := O_{σ'}(F(M))`, the `τ₂`-part of `F(M)`.
  set Y := opiCoreInG σᶜ F with hYdef
  have hY_le_M : Y ≤ M :=
    (OddOrder.GroupTheory.opiCoreInG_le σᶜ F).trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hOσMσ : opiCoreInG σ F = Mσ := by
    rw [opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma, ← hMσdef,
      fittingInAmbient_eq_self_of_isNilpotent]
  -- `Y` centralizes `M_σ`.
  have hY_le_cent : Y ≤ Subgroup.centralizer (Mσ : Set G) := by
    have hcomm : ⁅opiCoreInG σ F, Y⁆ = ⊥ := by
      rw [hYdef]; exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot σ F
    rw [hOσMσ, Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  -- `Y ≤ U`: `Y` is a `(κ∪σ)'`-group normal in `M`, and `U` is the `(κ∪σ)'`-Hall.
  have hY_le_U : Y ≤ U := by
    have hY_pi : Ch03.Subgroup.IsPiGroup ((S14.kappa M ∪ σ)ᶜ) (Y.subgroupOf M) := by
      intro p hp
      have hpY : p ∈ (Nat.card ↥Y).primeFactors := by
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY_le_M).toEquiv] at hp
      have hpσ : p ∈ σᶜ := OddOrder.GroupTheory.isPiSubgroup_opiCoreInG σᶜ F p hpY
      have hpτ2 : p ∈ tau2 M :=
        opiCoreInG_sigmaCompl_fittingInAmbient_primeFactors_subset_tau2 hG hM hpY
      rw [Set.mem_compl_iff, Set.mem_union]
      rintro (hpκ | hpσ')
      · have hr1 : pRank ↥M p = 1 := by
          rcases S14.kappa_subset_tau1_union_tau3 hpκ with h | h
          · exact ((mem_tau1_iff M p).mp h).2.2
          · exact ((mem_tau3_iff M p).mp h).2.2
        have hr2 : pRank ↥M p = 2 := ((mem_tau2_iff M p).mp hpτ2).2
        rw [hr1] at hr2; exact absurd hr2 (by norm_num)
      · exact hpσ hpσ'
    have hYnorm_M : (Y.subgroupOf M).Normal := by
      rw [hYdef]; exact OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M
    have hsub_le : Y.subgroupOf M ≤ U.subgroupOf M :=
      Ch03.Subgroup.IsPiGroup.normal_le_hall hY_pi hU
    have hmap := Subgroup.map_mono (f := M.subtype) hsub_le
    rwa [Subgroup.map_subgroupOf_eq_of_le hY_le_M, Subgroup.map_subgroupOf_eq_of_le hUM] at hmap
  -- `F(M) = M_F ⊔ Y`.
  have hF_split : F = maxNilpotentNormalHall M ⊔ Y := by
    have hsplit : opiCoreInG σ F ⊔ Y = F := by
      rw [hYdef]; exact opiCoreInG_sup_compl_eq_of_isNilpotent σ
    rw [← hsplit, hOσMσ, hMFMσ]
  -- `M_F ≤ F(M)`.
  have hMF_le_F : maxNilpotentNormalHall M ≤ F := by
    have : Group.IsNilpotent ↥(maxNilpotentNormalHall M) := maxNilpotentNormalHall_isNilpotent M
    exact le_fittingInAmbient_of_subgroupOf_normal_of_isNilpotent
      (maxNilpotentNormalHall_le M) (maxNilpotentNormalHall_subgroupOf_normal M)
  -- `F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.
  have hFiteq : F = maxNilpotentNormalHall M ⊔
      (U ⊓ Subgroup.centralizer (maxNilpotentNormalHall M : Set G)) := by
    apply le_antisymm
    · rw [hF_split]
      refine sup_le_sup_left (le_inf hY_le_U ?_) _
      rw [hMFMσ]; exact hY_le_cent
    · refine sup_le hMF_le_F ?_
      have hFcent : F = (Subgroup.centralizer (maxNilpotentNormalHall M : Set G) ⊓ M) ⊔
          maxNilpotentNormalHall M := by
        obtain ⟨-, -, -, -, -, h, -, -, -, -, -, -⟩ := fitting_decomposition hG hM
        exact h
      rw [hFcent]
      exact (le_inf inf_le_right (inf_le_left.trans hUM)).trans le_sup_left
  refine ⟨?_, ?_, hFiteq⟩
  · -- `hDcompl`: `M_F = M_σ` complements `U` in `M'`.
    rw [hMFMσ]
    have hMσnorm' : ((Mσ).subgroupOf (derivedInG M)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hMσ_le_M').mpr
        (hM'_le_M.trans (OddOrder.GroupTheory.le_normalizer_opiCoreInG σ M))
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      intro x hxMσ hxU
      rw [Subgroup.mem_subgroupOf] at hxMσ hxU
      have hx : (x : G) ∈ U ⊓ Mσ := ⟨hxU, hxMσ⟩
      rw [hUMσ_bot, Subgroup.mem_bot] at hx
      exact Subtype.ext hx
    · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hMσ_le_M' hU_le_M',
        sup_comm, ← hM'eq, Subgroup.subgroupOf_self, Subgroup.coe_top]
  · -- `hSDfit`: `M'' ≤ F(M) = M_F ⊔ (U ⊓ C_M(M_F))`.
    have hM''F : secondDerivedInAmbient M ≤ F := by
      obtain ⟨-, -, -, -, h, -, -, -, -, -, -, -⟩ := fitting_decomposition hG hM
      exact h
    exact hM''F.trans (le_of_eq hFiteq)

/-- In a finite cyclic group, a subgroup is determined by its cardinality (every subgroup is the
kernel of `x ↦ x ^ |A|`, which depends only on `|A|`). -/
theorem eq_of_card_eq_of_isCyclic {C : Type*} [Group C] [Finite C] [IsCyclic C]
    {H K : Subgroup C} (h : Nat.card ↥H = Nat.card ↥K) : H = K := by
  let : CommGroup C := IsCyclic.commGroup
  have key : ∀ A : Subgroup C, A = (powMonoidHom (Nat.card ↥A) : C →* C).ker := by
    intro A
    have hcard : Nat.card ↥((powMonoidHom (Nat.card ↥A) : C →* C).ker) = Nat.card ↥A := by
      rw [IsCyclic.card_powMonoidHom_ker, Nat.gcd_eq_right (Subgroup.card_subgroup_dvd_card A)]
    refine Subgroup.eq_of_le_of_card_ge (fun a ha => ?_) (le_of_eq hcard)
    rw [MonoidHom.mem_ker, powMonoidHom_apply]
    have h1 : (⟨a, ha⟩ : ↥A) ^ Nat.card ↥A = 1 := pow_card_eq_one'
    simpa only [SubmonoidClass.coe_pow, OneMemClass.coe_one] using congrArg Subtype.val h1
  rw [key H, key K, h]

/-- Two subgroups of `G` of equal finite order, both contained in a cyclic subgroup `C`, are
equal. -/
theorem eq_of_le_isCyclic_of_card_eq [Finite G] {C H K : Subgroup G} [IsCyclic ↥C]
    (hHC : H ≤ C) (hKC : K ≤ C) (h : Nat.card ↥H = Nat.card ↥K) : H = K := by
  have hcardH : Nat.card ↥(H.subgroupOf C) = Nat.card ↥H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv
  have hcardK : Nat.card ↥(K.subgroupOf C) = Nat.card ↥K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKC).toEquiv
  have hsub : H.subgroupOf C = K.subgroupOf C :=
    eq_of_card_eq_of_isCyclic (by rw [hcardH, hcardK, h])
  rw [← Subgroup.map_subgroupOf_eq_of_le hHC, ← Subgroup.map_subgroupOf_eq_of_le hKC, hsub]

/-- If `K` normalizes a cyclic subgroup `C` and `X ≤ C` is finite, then `K` normalizes `X`:
subgroups of a cyclic group are determined by their order, so the order-preserving `C`-conjugation
by elements of `K` fixes `X`. -/
theorem le_normalizer_of_le_isCyclic_normalized [Finite G] {C X K : Subgroup G} [IsCyclic ↥C]
    (hXC : X ≤ C) (hKC : K ≤ Subgroup.normalizer (C : Set G)) :
    K ≤ Subgroup.normalizer (X : Set G) := by
  intro m hm
  -- `m` conjugates `C` to itself.
  have hmC : MulAut.conj m • C = C := by
    ext x
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show ((MulAut.conj m)⁻¹ • x : G) = m⁻¹ * x * m by
        simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
    exact ((Subgroup.mem_normalizer_iff''.mp (hKC hm)) x).symm
  -- `conj m • X ≤ C` and has the same order, so equals `X`.
  have hconjle : MulAut.conj m • X ≤ C :=
    hmC ▸ (Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hXC)
  have hcard : Nat.card ↥(MulAut.conj m • X) = Nat.card ↥X :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj m) X).toEquiv).symm
  have hXeq : MulAut.conj m • X = X := eq_of_le_isCyclic_of_card_eq hconjle hXC hcard
  rw [Subgroup.mem_normalizer_iff'']
  intro h
  have hiff : h ∈ MulAut.conj m • X ↔ m⁻¹ * h * m ∈ X := by
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      show ((MulAut.conj m)⁻¹ • h : G) = m⁻¹ * h * m by
        simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
  rwa [hXeq] at hiff

/-- **Setup for BG Theorem 15.7(a)**: `¬FittingIsTI M` produces an element `g ∉ M` and a nontrivial
intersection `F(M) ⊓ F(M)^g`.  Unfolding `¬IsTISubset (F(M)^#) (N_G(F(M)))`:
there is `g ∉ N_G(F(M))`
and `a ∈ F(M)^#` with `gag⁻¹ ∈ F(M)^#`; then `gag⁻¹ ∈ F(M) ⊓ (conj g • F(M))` is nontrivial, and
`g ∉ M` because `F(M) ⊴ M` forces `M ≤ N_G(F(M))`. -/
theorem exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI {M : Subgroup G}
    (hnotTI : ¬ FittingIsTI M) :
    ∃ g : G, g ∉ M ∧
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) ≠ ⊥ := by
  rw [FittingIsTI] at hnotTI
  simp only [OddOrder.GroupTheory.IsTISubset] at hnotTI
  push Not at hnotTI
  obtain ⟨g, ⟨a, haA, hgaA⟩, hgN⟩ := hnotTI
  simp only [fittingSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff] at haA hgaA
  obtain ⟨haF, _ha1⟩ := haA
  obtain ⟨hgaF, hga1⟩ := hgaA
  -- `g ∉ M`: `F(M) ⊴ M` ⟹ `M ≤ N_G(F(M))`, but `g ∉ N_G(F(M))`.
  have hMN : M ≤ Subgroup.normalizer ((fittingInAmbient M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch2.S08.fittingInG_le M)).mp
      (OddOrder.BG.Ch2.S08.fittingInG_subgroupOf_normal M)
  refine ⟨g, fun h => hgN (hMN h), ?_⟩
  -- `gag⁻¹` is a nontrivial element of `F(M) ⊓ conj g • F(M)`.
  intro hbot
  have hmem : g * a * g⁻¹ ∈
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) := by
    refine Subgroup.mem_inf.mpr ⟨hgaF, ?_⟩
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using haF
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hga1 hmem

/-- **Step 3 of BG Theorem 15.7(a)**: a prime `p` dividing the TI-failure intersection
`F(M) ⊓ F(M)^g` (with `g ∉ M`) lies in `σ(M)`.

If not, `O_{σ(M)'}(F(M))` is cyclic (`opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic`), so any
order-`p` subgroup `X₁ ≤ F(M) ⊓ F(M)^g` (it is a `p`-subgroup of `F(M)`, hence
`≤ O_p(F(M)) ≤ O_{σ'}(F(M))`) is the unique one, hence normalized by both `M` and `M^g` (each
normalizes the relevant cyclic `O_{σ'}` and `X₁ = (X₁)` is order-preserved).  Then
`normalizer_eq_of_normal_of_mem_maximal` gives `N_G(X₁) = M`, but also
`M = N_G(g⁻¹·X₁·g) = g⁻¹·M·g`,
forcing `g ∈ M` — contradiction. -/
theorem mem_sigma_of_prime_dvd_card_inf_conj_fitting [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {g : G} (hgM : g ∉ M) {p : ℕ} (hp : p.Prime)
    (hpdvd : p ∣ Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M)) :
    p ∈ OddOrder.BG.Ch3.S10.sigma M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hpσ
  set F := fittingInAmbient M with hFdef
  set σ := OddOrder.BG.Ch3.S10.sigma M with hσdef
  have hFleM : F ≤ M := OddOrder.BG.Ch2.S08.fittingInG_le M
  -- `O_{σᶜ}(F)` is cyclic and normalized by `M`.
  have hcyc : IsCyclic ↥(opiCoreInG σᶜ F) := opiCoreInG_sigmaCompl_fittingInAmbient_isCyclic hG hM
  have hMNOσc : M ≤ Subgroup.normalizer ((opiCoreInG σᶜ F : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      ((OddOrder.GroupTheory.opiCoreInG_le σᶜ F).trans hFleM)).mp
      (OddOrder.BG.Ch2.S08.opiCoreInG_fittingInG_subgroupOf_normal σᶜ M)
  have hpσc : ({p} : Set ℕ) ⊆ σᶜ := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; rw [hq]; exact hpσ
  -- Generic helper: a `p`-subgroup of `F` is normalized by `M` (via `X₁ ≤ O_{σᶜ}(F)` cyclic).
  have hpnorm : ∀ Z : Subgroup G, Z ≤ F → IsPGroup p ↥Z →
      M ≤ Subgroup.normalizer (Z : Set G) := by
    intro Z hZF hZp
    have hZOp : Z ≤ opiCoreInG ({p} : Set ℕ) F :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M) hZF hZp
    have hZOσc : Z ≤ opiCoreInG σᶜ F :=
      hZOp.trans (Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono hpσc _))
    exact le_normalizer_of_le_isCyclic_normalized hZOσc hMNOσc
  -- An order-`p` subgroup `X₁` of `X = F ⊓ F^g`.
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(F ⊓ MulAut.conj g • F)) p hpdvd
  set X₁ : Subgroup G := (Subgroup.zpowers x).map (F ⊓ MulAut.conj g • F).subtype with hX₁def
  have hX₁leX : X₁ ≤ F ⊓ MulAut.conj g • F := hX₁def ▸ Subgroup.map_subtype_le _
  have hX₁card : Nat.card ↥X₁ = p := by
    rw [hX₁def, Subgroup.card_map_of_injective (F ⊓ MulAut.conj g • F).subtype_injective,
      Nat.card_zpowers, hxord]
  have hX₁ne : X₁ ≠ ⊥ := by
    intro h; rw [h, Subgroup.card_bot] at hX₁card; exact hp.one_lt.ne' hX₁card.symm
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁F : X₁ ≤ F := hX₁leX.trans inf_le_left
  have hX₁cF : X₁ ≤ MulAut.conj g • F := hX₁leX.trans inf_le_right
  -- `X₁ ⊴ M`, so `N_G(X₁) = M`.
  have hMNX₁ : M ≤ Subgroup.normalizer (X₁ : Set G) := hpnorm X₁ hX₁F hX₁pg
  have hNX₁ : Subgroup.normalizer (X₁ : Set G) = M :=
    OddOrder.BG.Ch2.S08.normalizer_eq_of_normal_of_mem_maximal hG hM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (hX₁F.trans hFleM)).mpr hMNX₁)
      hX₁ne (hX₁F.trans hFleM)
  -- `g⁻¹·X₁·g ≤ F` is also a `p`-group, so `M ≤ N(g⁻¹·X₁·g) = g⁻¹·N(X₁)·g = g⁻¹·M·g`.
  set X₁' : Subgroup G := MulAut.conj g⁻¹ • X₁ with hX₁'def
  have hX₁'card : Nat.card ↥X₁' = p := by
    rw [hX₁'def, ← Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) X₁).toEquiv, hX₁card]
  have hX₁'F : X₁' ≤ F := by
    have hle : X₁' ≤ MulAut.conj g⁻¹ • (MulAut.conj g • F) :=
      hX₁'def ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cF
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
  have hX₁'pg : IsPGroup p ↥X₁' := IsPGroup.of_card (n := 1) (by rw [hX₁'card, pow_one])
  have hMNX₁' : M ≤ Subgroup.normalizer (X₁' : Set G) := hpnorm X₁' hX₁'F hX₁'pg
  -- `N(X₁') = g⁻¹ • N(X₁) = g⁻¹ • M`.
  have hNX₁'eq : Subgroup.normalizer (X₁' : Set G) = MulAut.conj g⁻¹ • M := by
    rw [hX₁'def, ← hNX₁]
    exact (Subgroup.map_normalizer_eq_of_bijective X₁ (MulAut.conj g⁻¹).bijective).symm
  -- So `M ≤ g⁻¹ • M`, equal cards ⟹ `M = g⁻¹ • M`, i.e. `g ∈ N(M) = M`.
  rw [hNX₁'eq] at hMNX₁'
  have hcardM : Nat.card ↥(MulAut.conj g⁻¹ • M) = Nat.card ↥M :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) M).toEquiv).symm
  have hMeq : MulAut.conj g⁻¹ • M = M :=
    (Subgroup.eq_of_le_of_card_ge hMNX₁' (le_of_eq hcardM)).symm
  -- `g⁻¹·M·g = M ⟹ g⁻¹ ∈ N_G(M) ≤ M ⟹ g ∈ M`, contradicting `g ∉ M`.
  have hg_inv_N : g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    have hiff : h ∈ MulAut.conj g⁻¹ • M ↔ g * h * g⁻¹ ∈ M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        show ((MulAut.conj g⁻¹)⁻¹ • h : G) = g * h * g⁻¹ by
          simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
    rw [hMeq] at hiff
    rw [inv_inv]; exact hiff
  have hg_inv_M : g⁻¹ ∈ M :=
    OddOrder.BG.Ch3.S10.maximal_normalizer_le_self hG hM hg_inv_N
  exact hgM (by simpa using inv_mem hg_inv_M)

/-- **Rank-3 lower bound on `M_F` for `β`-primes** (the `≥ 3` side of BG Theorem 15.7(a)'s rank
dichotomy): if a prime `r` divides `M_F` and lies in `β(M)`, then `r_r(M_F) ≥ 3`.

`M_F` is a Hall subgroup of `M` (`maxNilpotentNormalHall_isHall`), so `r ∈ π(M_F)` gives
`r ∤ [M : M_F]` and hence `r_r(M_F) = r_r(M)` (`pRank_eq_of_le_of_not_dvd_index`); and
`r ∈ β(M) ⊆ α(M)` gives `r_r(M) ≥ 3` by the definition of `α(M)`.  Consumed by the rank core
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI` as the contradiction target against the `< 3`
bound coming from `C_{M_F}(X₁)`. -/
theorem three_le_pRank_mf_of_mem_beta [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (_hM : M ∈ maximalSubgroups G)
    {r : ℕ} (hrπ : r ∈ S14.piSet (MF M)) (hrβ : r ∈ OddOrder.BG.Ch3.S10.beta M) :
    3 ≤ pRank ↥(MF M) r := by
  have hrmem : r ∈ (Nat.card ↥(MF M)).primeFactors := hrπ
  have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrmem
  have : Fact r.Prime := ⟨hrp⟩
  -- `M_F` is `π(M_F)`-Hall in `M`; `r ∈ π(M_F)` ⟹ `r ∤ [M : M_F]`.
  have hHall := maxNilpotentNormalHall_isHall (G := G) M
  have hidx : ¬ r ∣ ((MF M).subgroupOf M).index := fun hdvd =>
    hHall.2 r (Nat.mem_primeFactors.mpr ⟨hrp, hdvd, Subgroup.index_ne_zero_of_finite⟩) hrmem
  -- `r_r(M_F) = r_r(M)`; and `r ∈ β(M) ⊆ α(M)` ⟹ `r_r(M) ≥ 3`.
  rw [OddOrder.GroupTheory.pRank_eq_of_le_of_not_dvd_index (maxNilpotentNormalHall_le M) hidx]
  exact (OddOrder.BG.Ch3.S10.beta_subset_alpha M hrβ).2

/-- A subgroup contained in two **distinct** maximal subgroups of a minimal simple odd group has
rank `< 3`.  Contrapositive of `isUniquelyMaximal_of_three_le_rank_of_lt_top`: rank `≥ 3` would
force unique maximality, contradicting membership in two distinct coatoms. -/
theorem rank_lt_three_of_le_two_maximals [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {C M N : Subgroup G} (hM : M ∈ maximalSubgroups G) (hN : N ∈ maximalSubgroups G)
    (hMN : M ≠ N) (hCM : C ≤ M) (hCN : C ≤ N) : rank ↥C < 3 := by
  by_contra h
  have hCt : C < ⊤ := lt_of_le_of_lt hCM (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM).lt_top
  exact hMN ((OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_three_le_rank_of_lt_top hG hCt
    (not_lt.mp h)).eq_of_isCoatom_of_le (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM) hCM
    (OddOrder.GroupTheory.mem_maximalSubgroups.mp hN) hCN)

/-- **Order-`p` non-TI witness extraction** (shared infrastructure of BG Theorem 15.7(a)/(e)):
from `¬FittingIsTI M` produce an element `g ∉ M`, a prime `p ∈ σ(M)`, and an order-`p` subgroup `X₁`
of `M_σ` that is also contained in the conjugate `M_σ^g`, with `C_G(X₁) ⊄ M` and
`rank (M_F ⊓ C_G(X₁)) < 3`.  This bundles the common prefix (steps 1, 3, 5–7) of
`piSet_mf_inf_beta_disjoint_of_not_fittingIsTI`, so that both the rank-core (`M_F = M_σ`,
Theorem 15.7(a)) and the type-`F` trichotomy (Theorem 15.7(e), `isTypeI_of_isTypeF`) can consume the
same witness `X₁`.  The two conjugate-membership facts `X₁ ≤ M_σ` and `X₁ ≤ M_σ^g` drive the
`O_p(M_σ)`-noncyclicity argument (Coq `not_cycMp`), and `rank (M_F ⊓ C_G(X₁)) < 3` is the
`E1X_facts` rank bound.

Stated **for a fixed `g`**, exactly as BG and Coq do (`nonTI_Fitting_structure` takes
`g \notin M -> X :!=: 1 ->` as hypotheses): BG's argument works for *any* `g ∉ M` with
`X = F(M) ∩ F(M)^g ≠ 1`, and the `p = |X|` step of Theorem 15.7(e) needs `p` tied to that same `X`,
which an `∃ g` statement cannot express.  The `∃ g` form is `exists_inf_conj_fitting_orderP_witness`
below, which just supplies a `g` from `¬FittingIsTI`. -/
theorem exists_orderP_witness_of_inf_conj_fitting_ne_bot [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {g : G} (hgM : g ∉ M)
    (hXne : (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) ≠ ⊥) :
    ∃ (p : ℕ) (X₁ : Subgroup G),
      p.Prime ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
        Nat.card ↥X₁ = p ∧
        X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
        X₁ ≤ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M ∧
        ¬ Subgroup.centralizer (X₁ : Set G) ≤ M ∧
        rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3 ∧
        -- `X₁` sits inside the TI-failure intersection `X = F(M) ∩ F(M)ᵍ` itself.  True by
        -- construction (`X₁` is generated by an order-`p` element of `X`), but it was not exposed
        -- until 2026-07-19; BG's `p = |X|` step needs `X₁` and `X` related in the statement.
        X₁ ≤ (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) := by
  classical
  have hXcard : Nat.card ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M) ≠ 1 :=
    fun h => hXne (Subgroup.card_eq_one.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hXcard
  have : Fact p.Prime := ⟨hp⟩
  have hpσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
    mem_sigma_of_prime_dvd_card_inf_conj_fitting hG hM hgM hp hpdvd
  -- An order-`p` subgroup `X₁ ≤ X`.
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M)) p hpdvd
  set X₁ : Subgroup G :=
    (Subgroup.zpowers x).map (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M).subtype
    with hX₁def
  have hX₁leX : X₁ ≤ fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M :=
    hX₁def ▸ Subgroup.map_subtype_le _
  have hX₁card : Nat.card ↥X₁ = p := by
    rw [hX₁def, Subgroup.card_map_of_injective
      (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M).subtype_injective,
      Nat.card_zpowers, hxord]
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hX₁F : X₁ ≤ fittingInAmbient M := hX₁leX.trans inf_le_left
  have hX₁cF : X₁ ≤ MulAut.conj g • fittingInAmbient M := hX₁leX.trans inf_le_right
  have hX₁M : X₁ ≤ M := hX₁F.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hpσ_sub : ({p} : Set ℕ) ⊆ OddOrder.BG.Ch3.S10.sigma M := by
    intro q hq; rw [Set.mem_singleton_iff] at hq; rw [hq]; exact hpσ
  -- Generic helper: a `p`-subgroup of `F(M)` lies in `M_σ`
  -- (`O_p(F(M)) ≤ O_σ(F(M)) = F(M_σ) ≤ M_σ`).
  have hMσ_of : ∀ Z : Subgroup G, Z ≤ fittingInAmbient M → IsPGroup p ↥Z →
      Z ≤ OddOrder.BG.Ch3.S10.Msigma M := by
    intro Z hZF hZp
    have h1 : Z ≤ opiCoreInG ({p} : Set ℕ) (fittingInAmbient M) :=
      OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        (OddOrder.BG.Ch2.S08.fittingInG_isNilpotent M) hZF hZp
    have h2 : opiCoreInG ({p} : Set ℕ) (fittingInAmbient M)
        ≤ opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M) :=
      Subgroup.map_mono (OddOrder.Isaacs.Ch03.oPiCore_mono hpσ_sub _)
    have h3' : opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) (fittingInAmbient M)
        = fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) :=
      opiCoreInG_sigma_fittingInAmbient_eq_fittingInAmbient_Msigma
    exact (h1.trans h2).trans (h3' ▸ OddOrder.BG.Ch2.S08.fittingInG_le _)
  have hX₁Mσ : X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M := hMσ_of X₁ hX₁F hX₁pg
  -- `X₁ ≤ M_σ^g`: pull `X₁` back by `g⁻¹` into `F(M)`, apply `hMσ_of`, push forward by `g`.
  have hY₁ : MulAut.conj g⁻¹ • X₁ ≤ fittingInAmbient M := by
    have hle : MulAut.conj g⁻¹ • X₁ ≤ MulAut.conj g⁻¹ • (MulAut.conj g • fittingInAmbient M) :=
      Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cF
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
  have hY₁pg : IsPGroup p ↥(MulAut.conj g⁻¹ • X₁) := by
    have hcard : Nat.card ↥(MulAut.conj g⁻¹ • X₁) = p := by
      rw [← Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) X₁).toEquiv, hX₁card]
    exact IsPGroup.of_card (n := 1) (by rw [hcard, pow_one])
  have hX₁cMσ : X₁ ≤ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M := by
    have hY₁Mσ : MulAut.conj g⁻¹ • X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M := hMσ_of _ hY₁ hY₁pg
    have hpush := (Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj g)).mpr hY₁Mσ
    rwa [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul] at hpush
  -- Step 6: `C_G(X₁) ⊄ M` (Theorem 10.1(e)).
  have hconj_g_inv : MulAut.conj g⁻¹ • X₁ ≤ M := hY₁.trans (OddOrder.BG.Ch2.S08.fittingInG_le M)
  have hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
    intro hCG
    have he := (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM hpσ hX₁ne hX₁pg).2.2.2.2
    exact hgM (by simpa using inv_mem (he hX₁M hCG g⁻¹ hconj_g_inv))
  -- Step 7: `rank (M_F ⊓ C_G(X₁)) < 3` (`C_{M_F}(X₁)` lies in `M` and in a coatom `N ≠ M`).
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne
  have hCGlt : Subgroup.centralizer (X₁ : Set G) < ⊤ :=
    lt_of_le_of_lt
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x₀.2))
      (OddOrder.BG.Ch2.S09.centralizer_singleton_lt_top hG
        (fun h => hx₀ne (Subtype.ext h)))
  obtain ⟨N, hNco, hCGN⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.centralizer (X₁ : Set G))).resolve_left hCGlt.ne
  have hNmax : N ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hNco
  have hNneM : M ≠ N := fun h => hCGnotM (h ▸ hCGN)
  have hrank3 : rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3 :=
    rank_lt_three_of_le_two_maximals hG hM hNmax hNneM
      (inf_le_left.trans (maxNilpotentNormalHall_le M)) (inf_le_right.trans hCGN)
  exact ⟨p, X₁, hp, hpσ, hX₁card, hX₁Mσ, hX₁cMσ, hCGnotM, hrank3, hX₁leX⟩

/-- **BG Theorem 15.7(e) non-TI witness, `∃ g` form** — the packaging most consumers want.  From
`¬FittingIsTI M` alone, `exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI` produces some
`g ∉ M` with `X = F(M) ∩ F(M)^g ≠ 1`, and `exists_orderP_witness_of_inf_conj_fitting_ne_bot`
supplies the witness for it.

Prefer the fixed-`g` version when the conclusion has to mention `X` itself — notably BG's
`p = |X|` step, where the existential over `g` would decouple `p` from the intersection it is
supposed to measure. -/
theorem exists_inf_conj_fitting_orderP_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hnotTI : ¬ FittingIsTI M) :
    ∃ (g : G) (p : ℕ) (X₁ : Subgroup G),
      g ∉ M ∧ p.Prime ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M ∧
        Nat.card ↥X₁ = p ∧
        X₁ ≤ OddOrder.BG.Ch3.S10.Msigma M ∧
        X₁ ≤ MulAut.conj g • OddOrder.BG.Ch3.S10.Msigma M ∧
        ¬ Subgroup.centralizer (X₁ : Set G) ≤ M ∧
        rank ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) < 3 ∧
        X₁ ≤ (fittingInAmbient M ⊓ MulAut.conj g • fittingInAmbient M : Subgroup G) := by
  obtain ⟨g, hgM, hXne⟩ := exists_notMem_inf_conj_fitting_ne_bot_of_not_fittingIsTI hnotTI
  obtain ⟨p, X₁, h⟩ := exists_orderP_witness_of_inf_conj_fitting_ne_bot hG hM hgM hXne
  exact ⟨g, p, X₁, hgM, h⟩

/-- **`O_p(M_F)` is noncyclic at a non-TI witness prime**
(Coq `nonTI_Fitting_structure`, `not_cycMp`):
if `M_F` contains an order-`p` subgroup `X₁` that is also contained in the conjugate `M_F^g` for
some
`g ∉ M`, then `O_p(M_F)` is not cyclic.  Were it cyclic, `X₁` would be its unique
order-`p` subgroup,
hence characteristic in `O_p(M_F) ⊴ M`, giving `N_G(X₁) = M`; applied to `g⁻¹·X₁·g ≤ O_p(M_F)` it
gives
`N_G(g⁻¹·X₁·g) = g⁻¹·M·g`, so `M = g⁻¹·M·g`, forcing `g ∈ M` — contradiction.  Both `X₁` and its
`g⁻¹`-conjugate land in the *same* cyclic `O_p(M_F)`, so no cyclic-conjugate transfer is needed.

This supplies the rank `≥ 2` lower bound of the abelian branch of Theorem 15.7(e)
(`isTypeI_of_isTypeF`): an abelian noncyclic `p`-group has `p`-rank `≥ 2`. -/
theorem not_isCyclic_opiCore_mf_of_orderP_le_conj [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {g : G} {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime) (hgM : g ∉ M)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hX₁cMF : X₁ ≤ MulAut.conj g • MF M) :
    ¬ IsCyclic ↥(opiCoreInG ({p} : Set ℕ) (MF M)) := by
  classical
  intro hcyc
  have : Fact p.Prime := ⟨hp⟩
  set C : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hCdef
  have : IsCyclic ↥C := hcyc
  -- `M ≤ N(C)` since `C = O_p(M_F)` is characteristic in `M_F ⊴ M`.
  have hMNC : M ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_opiCoreInG_of_le_normalizer _ (maxNilpotentNormalHall_le_normalizer M)
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  have hX₁C : X₁ ≤ C :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  have hX₁M : X₁ ≤ M := hX₁MF.trans (maxNilpotentNormalHall_le M)
  -- `M ≤ N(X₁)`, hence `N(X₁) = M`.
  have hMNX₁ : M ≤ Subgroup.normalizer (X₁ : Set G) :=
    le_normalizer_of_le_isCyclic_normalized hX₁C hMNC
  have hNX₁ : Subgroup.normalizer (X₁ : Set G) = M :=
    OddOrder.BG.Ch2.S08.normalizer_eq_of_normal_of_mem_maximal hG hM
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hX₁M).mpr hMNX₁) hX₁ne hX₁M
  -- `X₁' := g⁻¹·X₁·g ≤ O_p(M_F)` too (it lies in `M_F` and is a `p`-group), so `M ≤ N(X₁')`.
  set X₁' : Subgroup G := MulAut.conj g⁻¹ • X₁ with hX₁'def
  have hX₁'card : Nat.card ↥X₁' = p := by
    rw [hX₁'def, ← Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) X₁).toEquiv, hX₁card]
  have hX₁'pg : IsPGroup p ↥X₁' := IsPGroup.of_card (n := 1) (by rw [hX₁'card, pow_one])
  have hX₁'MF : X₁' ≤ MF M := by
    have hle : X₁' ≤ MulAut.conj g⁻¹ • (MulAut.conj g • MF M) :=
      hX₁'def ▸ Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hX₁cMF
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at hle
  have hX₁'C : X₁' ≤ C :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁'MF hX₁'pg
  have hMNX₁' : M ≤ Subgroup.normalizer (X₁' : Set G) :=
    le_normalizer_of_le_isCyclic_normalized hX₁'C hMNC
  -- `N(X₁') = g⁻¹ • N(X₁) = g⁻¹ • M`.
  have hNX₁'eq : Subgroup.normalizer (X₁' : Set G) = MulAut.conj g⁻¹ • M := by
    rw [hX₁'def, ← hNX₁]
    exact (Subgroup.map_normalizer_eq_of_bijective X₁ (MulAut.conj g⁻¹).bijective).symm
  rw [hNX₁'eq] at hMNX₁'
  have hcardM : Nat.card ↥(MulAut.conj g⁻¹ • M) = Nat.card ↥M :=
    (Nat.card_congr (Subgroup.equivSMul (MulAut.conj g⁻¹) M).toEquiv).symm
  have hMeq : MulAut.conj g⁻¹ • M = M :=
    (Subgroup.eq_of_le_of_card_ge hMNX₁' (le_of_eq hcardM)).symm
  -- `g⁻¹·M·g = M ⟹ g⁻¹ ∈ N_G(M) ≤ M ⟹ g ∈ M`, contradicting `g ∉ M`.
  have hg_inv_N : g⁻¹ ∈ Subgroup.normalizer (M : Set G) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    have hiff : h ∈ MulAut.conj g⁻¹ • M ↔ g * h * g⁻¹ ∈ M := by
      rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
        show ((MulAut.conj g⁻¹)⁻¹ • h : G) = g * h * g⁻¹ by
          simp [MulAut.smul_def, ← map_inv, MulAut.conj_apply]]
    rw [hMeq] at hiff
    rw [inv_inv]; exact hiff
  have hg_inv_M : g⁻¹ ∈ M :=
    OddOrder.BG.Ch3.S10.maximal_normalizer_le_self hG hM hg_inv_N
  exact hgM (by simpa using inv_mem hg_inv_M)

/-- **An abelian noncyclic `p`-group (`p` odd) has `p`-rank `≥ 2`** (additive analogue of mathcomp's
`abelian_rank1_cyclic`): a finite commutative `p`-group `R` with `p` odd that is not cyclic has
`2 ≤ pRank R p`.  Noncyclicity gives `p < |Ω₁(R)|` (contrapositive of
`isCyclic_of_card_omega1_le_prime`); `Ω₁(R)` is elementary abelian
(`isElementaryAbelian_omega_one_of_comm`) and a `p`-group, so `p² ≤ |Ω₁(R)|` and hence
`2 ≤ log_p|Ω₁(R)| ≤ pRank R p` (`le_pRank`).  Supplies the rank `≥ 2` lower bound of the abelian
branch of BG Theorem 15.7(e) (`isTypeI_of_isTypeF`). -/
theorem two_le_pRank_of_comm_isPGroup_not_isCyclic {R : Type*} [Group R] [Finite R]
    {p : ℕ} [Fact p.Prime] (hp_odd : Odd p) (hcomm : ∀ x y : R, x * y = y * x)
    (hR : IsPGroup p R) (hnc : ¬ IsCyclic R) : 2 ≤ pRank R p := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  -- `Ω₁(R)` is elementary abelian and a `p`-group.
  have hΩea : (Omega R p 1).IsElementaryAbelian p :=
    OddOrder.BG.Ch1_Preliminary.isElementaryAbelian_omega_one_of_comm hcomm
  have hΩpg : IsPGroup p ↥(Omega R p 1) := fun g =>
    (hR g.val).imp fun k hk =>
      Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hk)
  -- Noncyclicity ⟹ `p < |Ω₁(R)|`.
  have hlt : p < Nat.card ↥(Omega R p 1) := by
    by_contra hle
    exact hnc (OddOrder.BG.Ch1.S04.isCyclic_of_card_omega1_le_prime hR hp_odd (not_lt.mp hle))
  -- `|Ω₁(R)| = p^k` with `k ≥ 2`.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩpg
  have hk2 : 2 ≤ k := by
    by_contra h
    push Not at h
    interval_cases k
    · simp only [pow_zero] at hk; rw [hk] at hlt; omega
    · simp only [pow_one] at hk; rw [hk] at hlt; omega
  have hcard : p ^ 2 ≤ Nat.card ↥(Omega R p 1) := by
    rw [hk]; exact Nat.pow_le_pow_right (le_of_lt hp1) hk2
  -- `2 ≤ log_p|Ω₁(R)| ≤ pRank R p`.
  exact le_trans (Nat.le_log_of_pow_le hp1 hcard) (le_pRank (Omega R p 1) hΩea)

/-- **`C_{M_F}(X₁)` is not uniquely maximal** (Coq `nonTI_Fitting_structure`, `E1X_facts` clause
`C1 ∉ 'U`): if the centralizer `C_G(X₁)` of a nontrivial subgroup `X₁` is not contained in `M`, then
`C_{M_F}(X₁) = M_F ⊓ C_G(X₁)` is not uniquely maximal.

Were it uniquely maximal, then since `C_{M_F}(X₁) ≤ C_G(X₁) < ⊤`, the overgroup `C_G(X₁)` would also
be uniquely maximal (`IsUniquelyMaximal.of_le_of_lt_top`); and the unique maximal subgroup over
`C_{M_F}(X₁)` is `M` (a coatom containing it), so `C_G(X₁) ≤ M`, contradicting the hypothesis.
This is the `E1X_facts` input feeding the non-abelian branch of Theorem 15.7(e)
(`abelian C_{M_F}(X₁)` and `cyclic O_{p'}(M_F)`). -/
theorem not_isUniquelyMaximal_mf_inf_centralizer_of_not_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X₁ : Subgroup G} (hX₁ne : X₁ ≠ ⊥)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M) :
    ¬ OddOrder.GroupTheory.IsUniquelyMaximal (MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := by
  intro huniq
  -- `C₁ ≤ M`, `C₁ ≤ C_G(X₁)`, and `C_G(X₁) < ⊤`.
  have hC1M : MF M ⊓ Subgroup.centralizer (X₁ : Set G) ≤ M :=
    inf_le_left.trans (maxNilpotentNormalHall_le M)
  have hC1C : MF M ⊓ Subgroup.centralizer (X₁ : Set G) ≤ Subgroup.centralizer (X₁ : Set G) :=
    inf_le_right
  obtain ⟨x₀, hx₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁ne
  have hCGlt : Subgroup.centralizer (X₁ : Set G) < ⊤ :=
    lt_of_le_of_lt (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x₀.2))
      (OddOrder.BG.Ch2.S09.centralizer_singleton_lt_top hG (fun h => hx₀ne (Subtype.ext h)))
  -- `C_G(X₁)` is uniquely maximal, with the same unique maximal subgroup `M` as `C₁`.
  have huniqC : OddOrder.GroupTheory.IsUniquelyMaximal (Subgroup.centralizer (X₁ : Set G)) :=
    huniq.of_le_of_lt_top hC1C hCGlt
  have hMco : IsCoatom M := OddOrder.GroupTheory.mem_maximalSubgroups.mp hM
  have heq : M = huniqC.uniqueMaximalSubgroup :=
    huniq.eq_of_isCoatom_of_le hMco hC1M huniqC.uniqueMaximalSubgroup_isCoatom
      (hC1C.trans huniqC.le_uniqueMaximalSubgroup)
  exact hCGnotM (heq ▸ huniqC.le_uniqueMaximalSubgroup)

/-- **A finite nilpotent group with all Sylow subgroups abelian is abelian.**  A finite nilpotent
group is the internal direct product of its (normal) Sylow subgroups
(`Sylow.directProductOfNormal`); if each factor is commutative the product is, and commutativity
transports back across the isomorphism.  Used to prove `abelian C_{M_F}(X₁)` in the `E1X_facts`
input to BG Theorem 15.7(e): each Sylow of the nilpotent `C_{M_F}(X₁)` is abelian (a non-abelian
one would be uniquely maximal by `nonabelian_pgroup_isUniquelyMaximal`, contradicting
`not_isUniquelyMaximal_mf_inf_centralizer_of_not_le`). -/
theorem isMulCommutative_of_isNilpotent_of_sylow_comm {N : Type*} [Group N] [Finite N]
    [Group.IsNilpotent N]
    (h : ∀ (p : ℕ) [Fact p.Prime] (P : Sylow p N), IsMulCommutative ↥(P : Subgroup N)) :
    IsMulCommutative N := by
  classical
  have : Fintype N := Fintype.ofFinite N
  have hnorm : ∀ {p : ℕ} [Fact p.Prime] (P : Sylow p N), (↑P : Subgroup N).Normal :=
    fun P => OddOrder.Isaacs.Ch01.Sylow.normal_of_isNilpotent P
  let e := Sylow.directProductOfNormal (G := N) hnorm
  -- The direct-product domain is commutative: each component `↥P` is.
  have hDcomm : ∀ a b : (∀ p : (Nat.card N).primeFactors, ∀ P : Sylow p N, ↥(P : Subgroup N)),
      a * b = b * a := by
    intro a b
    funext p P
    have : Fact (p : ℕ).Prime := Fact.mk (Nat.prime_of_mem_primeFactors p.2)
    exact (isMulCommutative_iff.mp (h p P)) (a p P) (b p P)
  -- Transport commutativity across `e : (Π Sylows) ≃* N`.
  refine isMulCommutative_iff.mpr fun x y => ?_
  have hxy := congrArg e (hDcomm (e.symm x) (e.symm y))
  rwa [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply] at hxy

/-- **`C_{M_F}(X₁)` is abelian** (Coq `nonTI_Fitting_structure`, `E1X_facts` clause `abelian C1`):
if `C_G(X₁) ⊄ M` (with `X₁ ≠ 1`), the nilpotent subgroup `C_{M_F}(X₁) = M_F ⊓ C_G(X₁)` is abelian.

Every Sylow `P` of the nilpotent `C_{M_F}(X₁)` is abelian: a non-abelian one would be uniquely
maximal (`nonabelian_pgroup_isUniquelyMaximal`), and as `P ≤ C_{M_F}(X₁) < ⊤` this would force
`C_{M_F}(X₁)` itself to be uniquely maximal (`IsUniquelyMaximal.of_le_of_lt_top`), contradicting
`not_isUniquelyMaximal_mf_inf_centralizer_of_not_le`. Then
`isMulCommutative_of_isNilpotent_of_sylow_comm`
gives abelianness.  This is the second `E1X_facts` input (with noncyclicity) to the non-abelian
branch of BG Theorem 15.7(e). -/
theorem isMulCommutative_mf_inf_centralizer_of_not_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {X₁ : Subgroup G} (hX₁ne : X₁ ≠ ⊥)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M) :
    IsMulCommutative ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) := by
  classical
  set C1 : Subgroup G := MF M ⊓ Subgroup.centralizer (X₁ : Set G) with hC1def
  have hC1MF : C1 ≤ MF M := inf_le_left
  -- `C1` is nilpotent (a subgroup of the nilpotent `M_F`).
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  have : Group.IsNilpotent ↥(C1.subgroupOf (MF M)) := Subgroup.isNilpotent (C1.subgroupOf (MF M))
  have hC1nil : Group.IsNilpotent ↥C1 :=
    Group.nilpotent_of_surjective (Subgroup.subgroupOfEquivOfLe hC1MF).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hC1MF).surjective
  -- `C1 < ⊤` and `C1` is not uniquely maximal.
  have hC1notU : ¬ OddOrder.GroupTheory.IsUniquelyMaximal C1 :=
    not_isUniquelyMaximal_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hC1lt : C1 < ⊤ := lt_of_le_of_lt (hC1MF.trans (maxNilpotentNormalHall_le M))
    (OddOrder.GroupTheory.mem_maximalSubgroups.mp hM).lt_top
  -- Each Sylow of `C1` is abelian (else `C1` is uniquely maximal).
  apply isMulCommutative_of_isNilpotent_of_sylow_comm
  intro r _ P
  by_contra hnab
  set P' : Subgroup G := (P : Subgroup ↥C1).map C1.subtype with hP'def
  have hP'le : P' ≤ C1 := hP'def ▸ Subgroup.map_subtype_le _
  have hequiv : ↥(P : Subgroup ↥C1) ≃* ↥P' :=
    Subgroup.equivMapOfInjective _ C1.subtype C1.subtype_injective
  have hP'p : IsPGroup r ↥P' := P.isPGroup'.of_equiv hequiv
  have hP'nab : ¬ IsMulCommutative ↥P' := fun hcomm => hnab <|
    isMulCommutative_iff.mpr fun a b => hequiv.injective <| by
      rw [map_mul, map_mul]; exact (isMulCommutative_iff.mp hcomm) (hequiv a) (hequiv b)
  exact hC1notU ((nonabelian_pgroup_isUniquelyMaximal hG hP'p hP'nab).of_le_of_lt_top hP'le hC1lt)

/-- **Frobenius complement order divides `|kernel| - 1`** (mathcomp `regular_norm_dvd_pred`, in the
`IsFrobeniusAction` form): if a finite group `A` acts on a finite group `N` by automorphisms with no
nonidentity element of `A` fixing a nonidentity element of `N` (`IsFrobeniusAction A N`), then
`|A| ∣ |N| - 1`.  Immediate from `IsFrobeniusAction.card_modEq_one` (`|N| ≡ 1 [MOD |A|]`).

This is the divisibility crux of the exponent condition (conjunct A) of BG Theorem 15.7(e2):
applied to `N = Z_q = Ω₁(Z(O_q(M_σ)))` (order `q`) with `A = U₀` the Frobenius complement acting
fixed-point-freely on the kernel `M_σ`, it gives `|U₀| ∣ q - 1`, hence
`exp(U) = exp(U₀) ∣ q - 1`. -/
theorem card_dvd_sub_one_of_isFrobeniusAction {A N : Type*} [Group A] [Finite A] [Group N]
    [Finite N] [MulDistribMulAction A N] (h : OddOrder.Isaacs.Ch06.IsFrobeniusAction A N) :
    Nat.card A ∣ Nat.card N - 1 := by
  have : Fintype A := Fintype.ofFinite A
  have : Fintype N := Fintype.ofFinite N
  have hmod : Nat.card N ≡ 1 [MOD Nat.card A] := by
    simpa only [Nat.card_eq_fintype_card] using h.card_modEq_one
  exact (Nat.modEq_iff_dvd' Nat.card_pos).mp hmod.symm

/-- **The join of two commuting commutative subgroups is commutative.**  Writing `A ⊔ B` as the
closure of `↑A ∪ ↑B`, generators commute: two from `A` (abelian), two from `B` (abelian), or one of
each (they centralize each other, `A ≤ C_G(B)`).  Used for `not_cPP` in BG Theorem 15.7(e): were
`O_p(M_F)` abelian, then `M_F = O_p(M_F) ⊔ O_{p'}(M_F)` would be abelian (the `p'`-core is abelian
and centralizes the `p`-core), contradicting non-abelianness of `M_F`. -/
theorem isMulCommutative_sup_of_le_centralizer {A B : Subgroup G}
    (hA : IsMulCommutative ↥A) (hB : IsMulCommutative ↥B)
    (hAB : A ≤ Subgroup.centralizer (B : Set G)) :
    IsMulCommutative ↥(A ⊔ B) := by
  rw [Subgroup.sup_eq_closure]
  refine Subgroup.isMulCommutative_closure fun x hx y hy => ?_
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · simpa using congrArg Subtype.val (isMulCommutative_iff.mp hA ⟨x, hx⟩ ⟨y, hy⟩)
  · exact (Subgroup.mem_centralizer_iff.mp (hAB hx) y hy).symm
  · exact Subgroup.mem_centralizer_iff.mp (hAB hy) x hx
  · simpa using congrArg Subtype.val (isMulCommutative_iff.mp hB ⟨x, hx⟩ ⟨y, hy⟩)

/-- **A finite commutative group of odd order and rank `≤ 1` is cyclic** (additive converse of
mathcomp's `abelian_rank1_cyclic`).  Each Sylow `q`-subgroup is an abelian `q`-group whose `pRank`
is at most `rank N ≤ 1`, hence cyclic (contrapositive of
`two_le_pRank_of_comm_isPGroup_not_isCyclic`, using that `q`, a divisor of the odd `|N|`, is odd);
so `N` is a `Z`-group, and a finite commutative (hence nilpotent) `Z`-group is cyclic
(`IsZGroup.exponent_eq_card` + `IsCyclic.of_exponent_eq_card`).  This is the rank-1 ⇒ cyclic step of
the `cyclic O_{p'}(M_F)` conjunct of BG Theorem 15.7(e). -/
theorem isCyclic_of_isMulCommutative_of_rank_le_one {N : Type*} [Group N] [Finite N]
    (hcomm : ∀ x y : N, x * y = y * x) (hodd : Odd (Nat.card N)) (hrank : rank N ≤ 1) :
    IsCyclic N := by
  classical
  have hmc : IsMulCommutative N := isMulCommutative_iff.mpr hcomm
  have hZ : _root_.IsZGroup N := by
    refine ⟨fun q hq P => ?_⟩
    have : Fact q.Prime := ⟨hq⟩
    by_contra hPnc
    rcases subsingleton_or_nontrivial ↥(P : Subgroup N) with _ | hnt
    · exact hPnc inferInstance
    · have hPcomm : ∀ x y : ↥(P : Subgroup N), x * y = y * x := fun x y =>
        Subtype.ext (hcomm (x : N) (y : N))
      have hqdvd : q ∣ Nat.card N := by
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp P.isPGroup'
        have h1 : 1 < Nat.card ↥(P : Subgroup N) := Finite.one_lt_card_iff_nontrivial.mpr hnt
        have hn0 : n ≠ 0 := by rintro rfl; rw [pow_zero] at hn; omega
        have hqP : q ∣ Nat.card ↥(P : Subgroup N) := by rw [hn]; exact dvd_pow_self q hn0
        exact hqP.trans (Subgroup.card_subgroup_dvd_card _)
      have hqodd : Odd q := by
        rcases hq.eq_two_or_odd' with rfl | h
        · exact absurd (even_iff_two_dvd.mpr hqdvd) (Nat.not_even_iff_odd.mpr hodd)
        · exact h
      have h2 : 2 ≤ pRank ↥(P : Subgroup N) q :=
        two_le_pRank_of_comm_isPGroup_not_isCyclic hqodd hPcomm P.isPGroup' hPnc
      have hle : pRank ↥(P : Subgroup N) q ≤ rank N :=
        le_trans (pRank_mono_of_le (P : Subgroup N)) (pRank_le_rank q)
      omega
  exact IsCyclic.of_exponent_eq_card (_root_.IsZGroup.exponent_eq_card N)

/-- **Shared "`O_p(M_F)` is non-abelian" step** for BG Theorem 15.7(e) (Coq `not_cPP`).  From the
non-TI witness data (`X₁ ≤ M_F` of order `p`, `C_G(X₁) ⊄ M`) with a non-abelian Fitting subgroup
`M_F`, the `p`-core `P = O_p(M_F)` is non-abelian: the `p'`-core `R = O_{p'}(M_F)` centralizes `P`
(cores of a nilpotent group commute) and lies in the abelian `C₁ = C_{M_F}(X₁)`, so `R` is abelian;
were `P` abelian too, `M_F = P ⊔ R` would be a join of two commuting commutative subgroups, hence
abelian.  Used by both conjunct B (`typeF_nonabelian_cyclic_opiCore_compl`) and the per-prime
witness `q = p` case. -/
theorem opiCore_singleton_not_isMulCommutative_of_witness [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    ¬ IsMulCommutative ↥(opiCoreInG ({p} : Set ℕ) (MF M)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hX₁ne : X₁ ≠ ⊥ :=
    fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  set R : Subgroup G := opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) with hRdef
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  have hcomm : ⁅R, P⁆ = ⊥ := by
    rw [hRdef, hPdef, Subgroup.commutator_comm]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot ({p} : Set ℕ) (MF M)
  have hRcP : R ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hRMF : R ≤ MF M := opiCoreInG_le _ _
  have hCPCX : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (X₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₁P)
  have hRC1 : R ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) := le_inf hRMF (hRcP.trans hCPCX)
  have hC1ab : IsMulCommutative ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) :=
    isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hRab : ∀ x y : ↥R, x * y = y * x := fun x y =>
    Subtype.ext (by
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(x : G), hRC1 x.2⟩ ⟨(y : G), hRC1 y.2⟩))
  have hPRsup : P ⊔ R = MF M := opiCoreInG_sup_compl_eq_of_isNilpotent ({p} : Set ℕ)
  intro hPab
  refine hnab (hPRsup ▸ isMulCommutative_sup_of_le_centralizer hPab ?_ ?_)
  · exact isMulCommutative_iff.mpr hRab
  · rw [Subgroup.commutator_comm] at hcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm

/-- **BG Theorem 15.7(e), conjunct B — `cyclic O_{p'}(M_F)`** (Coq `nonTI_Fitting_structure`,
`cycHp'`): for the non-TI witness prime `p` (`X₁ ≤ M_F` of order `p`, `C_G(X₁) ⊄ M`) and a
non-abelian Fitting subgroup `M_F`, the `p'`-core `O_{p'}(M_F)` is cyclic.

`C₁ = C_{M_F}(X₁)` is abelian (`isMulCommutative_mf_inf_centralizer_of_not_le`) and not uniquely
maximal (`not_isUniquelyMaximal_mf_inf_centralizer_of_not_le`).  The `p'`-core `R = O_{p'}(M_F)`
centralizes the `p`-core `P = O_p(M_F) ⊇ X₁` (`opiCoreInG_commutator_compl_eq_bot`), so `R ≤ C₁`,
hence `R` is abelian.  `P` is non-abelian (else `M_F = P ⊔ R` would be abelian,
`isMulCommutative_sup_of_le_centralizer`), so `P ∈ 𝒰` (`nonabelian_pgroup_isUniquelyMaximal`).
Were `rank R ≥ 2`, then `D = M_F ⊓ C_G(P) ⊇ R` would have `rank ≥ 2` and lie in `C_G(P)`, so
`D ∈ 𝒰` (BG Corollary 9.2) and hence `C₁ ⊇ D` would be uniquely maximal — contradiction.  Thus
`rank R ≤ 1`, and the odd abelian `R` is cyclic (`isCyclic_of_isMulCommutative_of_rank_le_one`). -/
theorem typeF_nonabelian_cyclic_opiCore_compl [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {p : ℕ} {X₁ : Subgroup G} (hp : p.Prime)
    (hX₁card : Nat.card ↥X₁ = p) (hX₁MF : X₁ ≤ MF M)
    (hCGnotM : ¬ Subgroup.centralizer (X₁ : Set G) ≤ M)
    (hnab : ¬ IsMulCommutative ↥(MF M)) :
    p ∈ (Nat.card ↥(MF M)).primeFactors ∧
      IsCyclic ↥(opiCoreInG (({p} : Set ℕ)ᶜ) (MF M)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hX₁ne : X₁ ≠ ⊥ := fun h => hp.one_lt.ne' (by rw [← hX₁card, h, Subgroup.card_bot])
  have hX₁pg : IsPGroup p ↥X₁ := IsPGroup.of_card (n := 1) (by rw [hX₁card, pow_one])
  have hMFnil : Group.IsNilpotent ↥(MF M) := maxNilpotentNormalHall_isNilpotent M
  -- `p ∈ π(M_F)`: `p = |X₁| ∣ |M_F|`.
  have hpπ : p ∈ (Nat.card ↥(MF M)).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hX₁card ▸ Subgroup.card_dvd_of_le hX₁MF, Nat.card_pos.ne'⟩
  set P : Subgroup G := opiCoreInG ({p} : Set ℕ) (MF M) with hPdef
  set R : Subgroup G := opiCoreInG (({p} : Set ℕ)ᶜ) (MF M) with hRdef
  -- `X₁ ≤ P = O_p(M_F)`.
  have hX₁P : X₁ ≤ P :=
    OddOrder.BG.Ch2.S08.le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent hMFnil hX₁MF hX₁pg
  -- `R = O_{p'}(M_F) ≤ C_G(P)` (the `p`- and `p'`-cores of the nilpotent `M_F` commute).
  have hcomm : ⁅R, P⁆ = ⊥ := by
    rw [hRdef, hPdef, Subgroup.commutator_comm]
    exact OddOrder.BG.Ch2.S08.opiCoreInG_commutator_compl_eq_bot ({p} : Set ℕ) (MF M)
  have hRcP : R ≤ Subgroup.centralizer (P : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hRMF : R ≤ MF M := opiCoreInG_le _ _
  have hCPCX : Subgroup.centralizer (P : Set G) ≤ Subgroup.centralizer (X₁ : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hX₁P)
  have hRC1 : R ≤ MF M ⊓ Subgroup.centralizer (X₁ : Set G) := le_inf hRMF (hRcP.trans hCPCX)
  -- `C₁` abelian ⟹ `R` abelian.
  have hC1ab : IsMulCommutative ↥(MF M ⊓ Subgroup.centralizer (X₁ : Set G)) :=
    isMulCommutative_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hRab : ∀ x y : ↥R, x * y = y * x := fun x y =>
    Subtype.ext (by
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hC1ab ⟨(x : G), hRC1 x.2⟩ ⟨(y : G), hRC1 y.2⟩))
  -- `P` non-abelian (`not_cPP`): else `M_F = P ⊔ R` is abelian.
  have hPRsup : P ⊔ R = MF M := opiCoreInG_sup_compl_eq_of_isNilpotent ({p} : Set ℕ)
  have hPnab : ¬ IsMulCommutative ↥P := by
    intro hPab
    refine hnab (hPRsup ▸ isMulCommutative_sup_of_le_centralizer hPab ?_ ?_)
    · exact isMulCommutative_iff.mpr hRab
    · rw [Subgroup.commutator_comm] at hcomm
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hPpg : IsPGroup p ↥P := isPGroup_opiCoreInG_singleton (MF M)
  have hPU : OddOrder.GroupTheory.IsUniquelyMaximal P :=
    nonabelian_pgroup_isUniquelyMaximal hG hPpg hPnab
  -- `rank R ≤ 1`: else `C₁ ∈ 𝒰` via `D = M_F ⊓ C_G(P)`, contradicting `nonuniqC1`.
  have hC1notU : ¬ OddOrder.GroupTheory.IsUniquelyMaximal
      (MF M ⊓ Subgroup.centralizer (X₁ : Set G)) :=
    not_isUniquelyMaximal_mf_inf_centralizer_of_not_le hG hM hX₁ne hCGnotM
  have hrankR : rank ↥R ≤ 1 := by
    by_contra hr
    have h2R : 2 ≤ rank ↥R := by omega
    have hRD : R ≤ MF M ⊓ Subgroup.centralizer (P : Set G) := le_inf hRMF hRcP
    have h2D : 2 ≤ rank ↥(MF M ⊓ Subgroup.centralizer (P : Set G)) :=
      le_trans h2R (rank_le_of_injective (Subgroup.inclusion_injective hRD))
    have hDU : OddOrder.GroupTheory.IsUniquelyMaximal (MF M ⊓ Subgroup.centralizer (P : Set G)) :=
      OddOrder.BG.Ch2.S09.isUniquelyMaximal_of_le_centralizer_of_two_le_rank hG hPU inf_le_right h2D
    have hDC1 : MF M ⊓ Subgroup.centralizer (P : Set G) ≤
        MF M ⊓ Subgroup.centralizer (X₁ : Set G) := le_inf inf_le_left (inf_le_right.trans hCPCX)
    have hC1lt : MF M ⊓ Subgroup.centralizer (X₁ : Set G) < ⊤ :=
      lt_of_le_of_lt (inf_le_left.trans (maxNilpotentNormalHall_le M))
        (mem_maximalSubgroups.mp hM).lt_top
    exact hC1notU (hDU.of_le_of_lt_top hDC1 hC1lt)
  -- `R` is odd, abelian, of rank `≤ 1`, hence cyclic.
  have hRodd : Odd (Nat.card ↥R) := by
    rcases Nat.even_or_odd (Nat.card ↥R) with he | ho
    · exact absurd
        (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp he).trans (Subgroup.card_subgroup_dvd_card R)))
        (Nat.not_even_iff_odd.mpr hG.odd)
    · exact ho
  exact ⟨hpπ, isCyclic_of_isMulCommutative_of_rank_le_one hRab hRodd hrankR⟩

/-- **BG Theorem D(2) — `M_σ ∩ M^g` is cyclic** (mmd L4317, BG Lemma 12.17 third clause, Coq
`sigma_compl_embedding` cyclic part): for `g ∉ M`, the intersection `M_σ ∩ M^g` is cyclic.

`M_σ ∩ M^g` is abelian (its derived subgroup lies in `(M_σ ∩ M^g) ⊓ M_σ' = 1`, the TI part
`S12.Msigma_inf_conj_inf_derived_eq_bot`), of odd order, and of rank `≤ 1`: any noncyclic elementary
abelian `A ≤ M_σ ∩ M^g` would, by `norm_noncyclic_sigma` (Corollary 12.4), satisfy `C_G(A) ≤ N_G(A)
≤ M`, contradicting the σ-uniqueness core `S12.centralizer_not_le_of_isPGroup_le_Msigma_inf_conj`.
A finite commutative odd group of rank `≤ 1` is cyclic
(`isCyclic_of_isMulCommutative_of_rank_le_one`).  Supplies the `hD2` input of Theorem D.

*Placement*: this is §12 content (Lemma 12.17 third clause) and was originally stated next to
Theorem D in `S16_MainResults`; it lives here because its last step needs the §15 helper
`isCyclic_of_isMulCommutative_of_rank_le_one`, and because Theorem 15.7(b)
(`inf_conj_fitting_isCyclic`) consumes it upstream of §16. -/
theorem Msigma_inf_conj_isCyclic [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {g : G} (hg : g ∉ M) :
    IsCyclic ↥(OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • M) := by
  classical
  set K : Subgroup G := OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • M with hKdef
  have hKMσ : K ≤ OddOrder.BG.Ch3.S10.Msigma M := hKdef ▸ inf_le_left
  -- **abelian**: `K' ≤ K ⊓ M_σ' = 1` (the TI part of Lemma 12.17).
  have hTI : K ⊓ derivedInG (OddOrder.BG.Ch3.S10.Msigma M) = ⊥ := by
    rw [hKdef]; exact OddOrder.BG.Ch3.S12.Msigma_inf_conj_inf_derived_eq_bot hG hM hg
  have hder_bot : derivedInG K = ⊥ := by
    rw [eq_bot_iff, ← hTI]
    exact le_inf (Subgroup.map_subtype_le _)
      (OddOrder.BG.Ch3.S12.derivedInG_le_derivedInG hKMσ)
  have hcommK : commutator ↥K = ⊥ := by
    have h := hder_bot
    rwa [derivedInG, Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective] at h
  have habelian : ∀ x y : ↥K, x * y = y * x := by
    have hle : (⊤ : Subgroup ↥K) ≤ Subgroup.centralizer ((⊤ : Subgroup ↥K) : Set ↥K) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommK
    intro x y
    exact Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top y)) x (Subgroup.mem_top x)
  -- **odd order**.
  have hodd : Odd (Nat.card ↥K) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card K)
  -- **rank ≤ 1**: a noncyclic elementary abelian `A ≤ K` contradicts the σ-uniqueness core.
  have hrank : rank ↥K ≤ 1 := by
    by_contra hcon
    obtain ⟨p, hp, A, hAea, hAle, hAnc⟩ :=
      exists_isElementaryAbelian_not_isCyclic_le_of_two_le_rank K (by omega)
    have : Fact p.Prime := ⟨hp⟩
    have hAmeet : A ≤ OddOrder.BG.Ch3.S10.Msigma M ⊓ MulAut.conj g • M := hKdef ▸ hAle
    have hAMσ : A ≤ OddOrder.BG.Ch3.S10.Msigma M := hAmeet.trans inf_le_left
    have hAM : A ≤ M := hAMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
    have hAp : IsPGroup p ↥A := hAea.isPGroup
    have hAne : A ≠ ⊥ := by rintro rfl; exact hAnc isCyclic_of_subsingleton
    have hpdvdA : p ∣ Nat.card ↥A := by
      obtain ⟨n, hn⟩ := hAp.exists_card_eq
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · exact absurd (Subgroup.card_eq_one.mp (by rw [hn, h0, pow_zero])) hAne
      · exact hn ▸ dvd_pow_self p hpos.ne'
    have hApσ : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
        ⟨hp, hpdvdA.trans (Subgroup.card_dvd_of_le hAMσ), Nat.card_pos.ne'⟩)
    have hNA : Subgroup.normalizer (A : Set G) ≤ M :=
      OddOrder.BG.Ch3.S12.norm_noncyclic_sigma hG hM hApσ hAp hAM hAnc
    have hCA : Subgroup.centralizer (A : Set G) ≤ M :=
      (Subgroup.centralizer_le_normalizer _).trans hNA
    exact OddOrder.BG.Ch3.S12.centralizer_not_le_of_isPGroup_le_Msigma_inf_conj
      hG hM hg hApσ hAp hAne hAmeet hCA
  exact isCyclic_of_isMulCommutative_of_rank_le_one habelian hodd hrank

end OddOrder.BG.Ch4.S15


