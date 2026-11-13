-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TypeP1Forcing
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TypeP1Forcing
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:55:01.581033+00:00
-- url     : https://prove2.me/theorems/3107f2a6-4a52-4907-a4f8-a1b05fd773ab
-- title:
--   BG §15: Theorem 15.2, the type-$\mathcal{P}_1$ forcing layer
-- statement:
--   The §14-gated conditional helpers for Theorem 15.2 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §15, through `isTypeP1_of_mf_ne_msigma` and `kstar_card_prime_of_inputs`: $M_F\ne M_\sigma$ forces type $\mathcal{P}_1$.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/TypeP1Forcing.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S15_MF/TypeP1Forcing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151

namespace OddOrder.BG.Ch4.S15

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open scoped Pointwise

open scoped IsMulCommutative

open scoped commutatorElement

variable {G : Type*} [Group G]

/-- **Theorem 15.2, step 2 entry** (mmd L4192, "By Lemma 6.3(a), `M_σ = [M_σ, K]`"): in a
type-`P1` factorization `M = K M_σ` (so `M_σ` is a complement of `K` in `M`), the σ-core is its
own commutator with `K`: `⁅M_σ, K⁆ = M_σ` (inside `M`).

This is the §14-independent algebraic core of step 2.  The only §14 input is the complement
`M = K M_σ` (type-`P1`, from Lemma 14.1 / Theorem 14.7(h)), taken here as `hcompl`; combined with
`M_σ ⊆ M'` (Theorem A, `Msigma_le_derived`) and solvability of `M`, Lemma 6.3(a)
(`commutator_eq_self_of_isComplement'_le_commutator`) gives the identity.  It feeds the
contrapositive of Theorem 3.8 in the next step: `⁅M_σ, K⁆ = M_σ ⊄ F(M_σ)` since `M_σ` is
non-nilpotent (`M_F ⊊ M_σ`). -/
theorem msigma_eq_commutator_kappa_of_isComplement' [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M)) :
    ⁅(OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M, K.subgroupOf M⁆
      = (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hM_le_NMσ :
      M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMσ_norm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr hM_le_NMσ
  have hMσ_le : (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M ≤ commutator ↥M := by
    calc (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
        ≤ (derivedInG M).subgroupOf M :=
          Subgroup.comap_mono (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hM)
      _ = commutator ↥M := by
          rw [derivedInG, Subgroup.subgroupOf,
            Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  exact OddOrder.BG.Ch1.S06.commutator_eq_self_of_isComplement'_le_commutator hcompl hMσ_le

/-- **Theorem 15.2, step 2 core** (mmd L4192, "by Theorem 3.8, `K* ∩ F(M) ≠ 1`"): the
contrapositive of BG **Theorem 3.8** (`S03h.thm38`) applied to the coprime action of `K` on the
non-nilpotent `M_σ`.  In the type-`P1` factorization `M = K M_σ` (complement `hcompl`), with `K`'s
prime-manner action on `M_σ` (`hcond2`, Proposition 14.2(a)), `M_σ` of odd order coprime to `K`
(`hoddM`, `hcop`), and `M_σ` non-nilpotent (`M_F ≠ M_σ`), the `K`-centralizer meets the Fitting
subgroup of `M_σ` nontrivially: `C_{F(M_σ)}(K) ≠ 1`.

Proof: were `C_{F(M_σ)}(K) = 1`, Theorem 3.8 (hypotheses (1) `hcop`, (2) `hcond2`, (3) the
assumed triviality) would give `⁅M_σ, K⁆ ⊆ F(M_σ)`.  But `⁅M_σ, K⁆ = M_σ`
(`msigma_eq_commutator_kappa_of_isComplement'`), so `F(M_σ) = M_σ`, forcing `M_σ` nilpotent
(`isNilpotent_of_fittingInAmbient_eq_self`) — contradicting `M_F ≠ M_σ`
(`maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent`).  This is the brick that consumes the
freshly-formalized BG Theorem 3.8 (issue 8011); it unblocks `K* ⊆ Q = O_q(M)` (step 2 tail). -/
theorem centralizer_kappa_inf_fittingInAmbient_ne_bot_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥(K.subgroupOf M))
      (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)))
    (hcond2 : ∀ x ∈ (K.subgroupOf M : Set ↥M), x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥M) ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
        = Subgroup.centralizer (K.subgroupOf M : Set ↥M)
            ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    Subgroup.centralizer (K.subgroupOf M : Set ↥M)
        ⊓ fittingInAmbient ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) ≠ ⊥ := by
  classical
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  -- `M` has odd order (divisor of `|G|`).
  have hoddM : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  -- `M_σ` non-nilpotent (else `M_F = M_σ`), transported to the `subgroupOf` realization.
  have hMσ_not_nil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hnil =>
    hne ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hnil)
  have hMσ'_not_nil :
      ¬ Group.IsNilpotent ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) := by
    intro hnil
    have := hnil
    exact hMσ_not_nil
      (Group.nilpotent_of_mulEquiv
        (Subgroup.subgroupOfEquivOfLe (OddOrder.BG.Ch3.S10.Msigma_le M)))
  -- normality of `M_σ.subgroupOf M`.
  have hM_le_NMσ :
      M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hMσ_norm : ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (OddOrder.BG.Ch3.S10.Msigma_le M)).mpr hM_le_NMσ
  -- Contrapositive of Theorem 3.8: assume `C_{F(M_σ)}(K) = 1`.
  by_contra hbot
  have hle := OddOrder.BG.Ch1.S03h.thm38 (G := ↥M)
    (K := (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) (R := K.subgroupOf M)
    hoddM hcompl hcop hcond2 hbot
  rw [msigma_eq_commutator_kappa_of_isComplement' hG hM hcompl] at hle
  -- `⁅M_σ, K⁆ = M_σ ⊆ F(M_σ)` gives `F(M_σ) = M_σ`, hence `M_σ` nilpotent — contradiction.
  have heq : fittingInAmbient ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      = (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M :=
    le_antisymm (OddOrder.BG.Ch2.S08.fittingInG_le _) hle
  exact hMσ'_not_nil (isNilpotent_of_fittingInAmbient_eq_self heq)

/-- **Theorem 15.2, step 2 tail (part 1)** (mmd L4192, "Thus `K*` lies in `Q = O_q(M)`"): the
order-`q` subgroup `K* = C_{M_σ}(K)` is contained in the Fitting subgroup of `M_σ`.

Combines step 2 core (`C_{F(M_σ)}(K) ≠ 1`, i.e. `K* ⊓ F(M_σ) ≠ 1`) with `|K*| = q` prime (`hq`,
the §14 input Theorem 14.7(f)): a prime-order subgroup meeting `F(M_σ)` nontrivially is contained
in it (`le_of_inf_ne_bot_of_card_prime`).  Since `K*` is a `q`-group, this lands `K* ⊆ O_q(F(M_σ))
⊆ O_q(M) = Q` (the `Q`-containment is the remaining part-2 bookkeeping).

Here `K*` is the `↥M`-realization `C_{↥M}(K) ⊓ M_σ`; the wrapper supplies `hq` from the `§14`
value `q = |K*|` (prime) and the `subgroupOf` cardinality identity. -/
theorem kstar_le_fittingInAmbient_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥(K.subgroupOf M))
      (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)))
    (hcond2 : ∀ x ∈ (K.subgroupOf M : Set ↥M), x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥M) ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
        = Subgroup.centralizer (K.subgroupOf M : Set ↥M)
            ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hq : (Nat.card ↥(Subgroup.centralizer (K.subgroupOf M : Set ↥M)
            ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).Prime) :
    Subgroup.centralizer (K.subgroupOf M : Set ↥M)
        ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
      ≤ fittingInAmbient ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) := by
  have hcore :=
    centralizer_kappa_inf_fittingInAmbient_ne_bot_of_inputs hG hM hcompl hcop hcond2 hne
  have : Fact (Nat.card ↥(Subgroup.centralizer (K.subgroupOf M : Set ↥M)
      ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).Prime := ⟨hq⟩
  -- `K* ⊓ F(M_σ) = C(K) ⊓ F(M_σ) ≠ ⊥` (since `F(M_σ) ≤ M_σ`).
  have hInf_ne : (Subgroup.centralizer (K.subgroupOf M : Set ↥M)
        ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
        ⊓ fittingInAmbient ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M) ≠ ⊥ := by
    rw [inf_assoc, inf_of_le_right (OddOrder.BG.Ch2.S08.fittingInG_le _)]
    exact hcore
  exact OddOrder.BG.Ch1.S05.le_of_inf_ne_bot_of_card_prime rfl hInf_ne

/-- **Theorem 15.2, step 2 tail (part 2)** (mmd L4192, "Thus `K*` lies in `Q = O_q(M)`"): given
`K* ⊆ F(M_σ)` (part 1) and that `K*` is a `q`-group (`hKstar_q`, from `|K*| = q` prime), the
`q`-core chain lands `K* ⊆ O_q(M) = Q`.

`K* ⊆ O_q(F(M_σ))` (a `q`-subgroup of the nilpotent `F(M_σ)`, `piGroup_le_opiCoreInG_of_nilpotent`);
`O_q(F(M_σ))` is normal in `M` (the characteristic chain `O_q(F(M_σ)) ⊴ F(M_σ) ⊴ M_σ`, lifted by
`M ≤ N_G(M_σ) ⟹ M ≤ N_G(F(M_σ)) ⟹ M ≤ N_G(O_q(F(M_σ)))`), hence a normal `q`-subgroup of `M`, so
`⊆ O_q(M)` (`le_opiCoreInG_of_normal_of_isPiSubgroup`).  The §14 input is `q = |K*|` prime (used
only to know `K*` is a `q`-group, via `hKstar_q`). -/
theorem kstar_le_opiCore_of_le_fittingInAmbient [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (_hM : M ∈ maximalSubgroups G)
    {q : ℕ}
    (hKstar_q : ∀ r ∈ (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
        ⊓ Subgroup.centralizer (K : Set G))).primeFactors, r ∈ ({q} : Set ℕ))
    (hKstar_le_F : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
        ≤ fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
        ≤ opiCoreInG ({q} : Set ℕ) M := by
  have : Group.IsNilpotent ↥(fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) :=
    OddOrder.BG.Ch2.S08.fittingInG_isNilpotent _
  -- step A: `K* ⊆ O_q(F(M_σ))` — a `q`-subgroup of the nilpotent `F(M_σ)`.
  have hA : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      ≤ opiCoreInG ({q} : Set ℕ) (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) :=
    piGroup_le_opiCoreInG_of_nilpotent hKstar_q hKstar_le_F
  -- characteristic chain: `M ≤ N(M_σ) → N(F(M_σ)) → N(O_q(F(M_σ)))`.
  have hM_le_NMσ :
      M ≤ Subgroup.normalizer ((OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G) := by
    rw [OddOrder.BG.Ch3.S10.Msigma]
    exact le_normalizer_opiCoreInG (OddOrder.BG.Ch3.S10.sigma M) M
  have hM_le_NF : M ≤ Subgroup.normalizer
      ((fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) : Subgroup G) : Set G) :=
    fun x hx => OddOrder.BG.Ch2.S08.mem_normalizer_fittingInG_of_mem_normalizer (hM_le_NMσ hx)
  have hM_le_NOq : M ≤ Subgroup.normalizer
      ((opiCoreInG ({q} : Set ℕ) (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M))
        : Subgroup G) : Set G) :=
    le_normalizer_opiCoreInG_of_le_normalizer ({q} : Set ℕ) hM_le_NF
  -- `O_q(F(M_σ)) ≤ M`, normal in `M`, a `{q}`-subgroup ⟹ `⊆ O_q(M)`.
  have hOq_le_M : opiCoreInG ({q} : Set ℕ) (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)) ≤ M :=
    (opiCoreInG_le _ _).trans
      ((OddOrder.BG.Ch2.S08.fittingInG_le _).trans (OddOrder.BG.Ch3.S10.Msigma_le M))
  have hB : opiCoreInG ({q} : Set ℕ) (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M))
      ≤ opiCoreInG ({q} : Set ℕ) M :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hOq_le_M
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hOq_le_M).mpr hM_le_NOq)
      (isPiSubgroup_opiCoreInG _ _)
  exact hA.trans hB

/-- **Theorem 15.2, step 2 tail — `G`-form bridge of part 1**: the `↥M`-realized
`kstar_le_fittingInAmbient_of_inputs` lifted to a statement about the ambient subgroups
`K* = M_σ ⊓ C_G(K)` and `F(M_σ)` of `G`.

Translates the `↥M` conclusion `C_{↥M}(K) ⊓ M_σ ≤ F(M_σ)` to `M_σ ⊓ C_G(K) ≤ F(M_σ)` (`G`-form)
via `centralizer_subgroupOf` (the `C_{↥M}(K) = C_G(K) ↾ M` identity) and
`fitting_subgroupOf_map_subtype_eq` (`F(M_σ ↾ M) = F(M_σ) ↾ M`), then reflects `subgroupOf`-`≤`
back to `G`.  This is the bridge that lets the `↥M`-native step-2 helpers (which need the ambient
to be `M` for Lemma 6.3(a) / Theorem 3.8) feed the `G`-native `q`-core chain
(`kstar_le_opiCore_of_le_fittingInAmbient`).  Needs `K ≤ M` (`hKM`, the Hall containment). -/
theorem kstar_le_fittingInAmbient_G_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M)
    (hcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥(K.subgroupOf M))
      (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)))
    (hcond2 : ∀ x ∈ (K.subgroupOf M : Set ↥M), x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥M) ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
        = Subgroup.centralizer (K.subgroupOf M : Set ↥M)
            ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
        ⊓ Subgroup.centralizer (K : Set G))).Prime) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      ≤ fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) := by
  have hKstar_le_M : OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G) ≤ M :=
    inf_le_left.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  have hF_le_M : fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M) ≤ M :=
    (OddOrder.BG.Ch2.S08.fittingInG_le _).trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  -- bridge (a): `C_{↥M}(K) ⊓ M_σ = (M_σ ⊓ C_G(K)) ↾ M`.
  have hbridge_a : Subgroup.centralizer (K.subgroupOf M : Set ↥M)
        ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
      = (OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)).subgroupOf M := by
    have himg : M.subtype '' (K.subgroupOf M : Set ↥M) = (K : Set G) := by
      rw [← Subgroup.coe_map, Subgroup.map_subgroupOf_eq_of_le hKM]
    rw [OddOrder.BG.Ch1.S03h.centralizer_subgroupOf (K.subgroupOf M : Set ↥M), himg, inf_comm]
    simp only [Subgroup.subgroupOf, Subgroup.comap_inf]
  -- translate `hqG` to the `↥M` prime hypothesis of part 1.
  have hq : (Nat.card ↥(Subgroup.centralizer (K.subgroupOf M : Set ↥M)
      ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)).Prime := by
    rw [hbridge_a, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKstar_le_M).toEquiv]
    exact hqG
  -- bridge (b): `F(M_σ ↾ M) = F(M_σ) ↾ M`.
  have hbridge_b : fittingInAmbient ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      = (fittingInAmbient (OddOrder.BG.Ch3.S10.Msigma M)).subgroupOf M :=
    OddOrder.BG.Ch1.S03h.fitting_subgroupOf_map_subtype_eq (OddOrder.BG.Ch3.S10.Msigma_le M)
  -- part 1 (`↥M`), then bridge both sides to `G` and reflect.
  have h := kstar_le_fittingInAmbient_of_inputs hG hM hcompl hcop hcond2 hne hq
  rw [hbridge_a, hbridge_b] at h
  have h2 := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hKstar_le_M,
    Subgroup.map_subgroupOf_eq_of_le hF_le_M] at h2

/-- **Theorem 15.2, step 2 tail — `K* ⊆ Q = O_q(M)`** (mmd L4192): the composition of the `G`-form
part 1 (`K* ⊆ F(M_σ)`) and part 2 (the `q`-core chain), giving the full "`K*` lies in `Q`"
conclusion from the base `§14` inputs.  Here `q = |K*|` (prime by `hqG`, the §14 Theorem 14.7(f)
input), so `Q = O_q(M)` is the normal Sylow `q`-subgroup of the theorem. -/
theorem kstar_le_opiCore_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M)
    (hcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
      (K.subgroupOf M))
    (hcop : Nat.Coprime (Nat.card ↥(K.subgroupOf M))
      (Nat.card ↥((OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)))
    (hcond2 : ∀ x ∈ (K.subgroupOf M : Set ↥M), x ≠ 1 →
      Subgroup.centralizer ({x} : Set ↥M) ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M
        = Subgroup.centralizer (K.subgroupOf M : Set ↥M)
            ⊓ (OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M)
    (hqG : (Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
        ⊓ Subgroup.centralizer (K : Set G))).Prime) :
    OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)
      ≤ opiCoreInG ({Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M
          ⊓ Subgroup.centralizer (K : Set G))} : Set ℕ) M := by
  have h1 := kstar_le_fittingInAmbient_G_of_inputs hG hM hKM hcompl hcop hcond2 hne hqG
  refine kstar_le_opiCore_of_le_fittingInAmbient hG hM (fun r hr => ?_) h1
  rw [hqG.primeFactors, Finset.mem_singleton] at hr
  exact Set.mem_singleton_iff.mpr hr

/-- **Theorem 15.2, step 2 tail — complement `D` is nilpotent** (mmd L4192, "`M_σ/Q` is nilpotent",
giving conjunct (d)): a `K`-invariant complement `D` of `Q` in `M_σ` is nilpotent.

Rather than the quotient `M_σ/Q`, we work with the isomorphic complement `D ≤ M_σ` (`D ∩ Q = 1`,
`hDQ`).  A prime-order `K₁ ≤ K` (`hK₁prime`) normalizes `D` (`hK₁norm`, `K`-invariance) and acts
on it fixed-point-freely: if `r ∈ K₁#` fixes `n ∈ D` (`r n r⁻¹ = n`), then `n ∈ C_{M_σ}(r) ⊆ Q`
(`hCentleQ`, the §14 prime-manner action of Proposition 14.2(a) together with `K* ⊆ Q` from the
`q`-core chain) while `n ∈ D`, so `n ∈ D ∩ Q = 1`.  Theorem 3.7 (`frobeniusKernelIsNilpotent`,
fixed-point-free prime-order action) then gives `D` nilpotent.  `hCentleQ` is the sole §14 input. -/
theorem complement_isNilpotent_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {K Q D K₁ : Subgroup G} (hDM : D ≤ M) (hK₁M : K₁ ≤ M)
    (hDMσ : D ≤ OddOrder.BG.Ch3.S10.Msigma M) (hDQ : Disjoint D Q) (hK₁K : K₁ ≤ K)
    (hK₁norm : K₁ ≤ Subgroup.normalizer (D : Set G)) (hDK₁disj : Disjoint D K₁)
    (hDne : D ≠ ⊥) (hK₁ne : K₁ ≠ ⊥) (hK₁prime : ∃ p : ℕ, p.Prime ∧ Nat.card ↥K₁ = p)
    (hCentleQ : ∀ r ∈ (K : Set G), r ≠ 1 →
      Subgroup.centralizer ({r} : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M ≤ Q) :
    Group.IsNilpotent ↥D := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have : Group.IsSolvable ↥(D ⊔ K₁) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective (sup_le hDM hK₁M))
  refine OddOrder.BG.Ch1.S03c.isNilpotent_of_normalizing_primeOrder_fixedPointFree
    hK₁norm hDK₁disj hDne hK₁ne hK₁prime ?_
  intro r hrK₁ hr1 n hnD hn1 hfix
  have hrK : r ∈ K := hK₁K hrK₁
  have hnMσ : n ∈ OddOrder.BG.Ch3.S10.Msigma M := hDMσ hnD
  -- `r n r⁻¹ = n` means `r n = n r`, i.e. `n ∈ C_G(r)`.
  have hrn : r * n = n * r := by rw [mul_inv_eq_iff_eq_mul] at hfix; exact hfix
  have hnCent : n ∈ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro g hg
    rw [Set.mem_singleton_iff] at hg; subst hg
    exact hrn
  -- so `n ∈ C_{M_σ}(r) ⊆ Q`, while `n ∈ D` and `D ∩ Q = 1`.
  have hnQ : n ∈ Q := hCentleQ r hrK hr1 (Subgroup.mem_inf.mpr ⟨hnCent, hnMσ⟩)
  exact hn1 (Subgroup.disjoint_def.mp hDQ hnD hnQ)

/-- **BG Theorem 15.2, step 1 derivation (a)** (mmd L4190, "By Lemma 14.1, this implies (a)"):
if `M_F ≠ M_σ` (i.e. `M_σ` is *not* nilpotent), then `M` is of type `P₁`.

Two halves, both via BG Lemma 14.1 (`msigma_structure_of_notMem_sigma_kappa`):

* `¬ IsTypeP2 M`: were `M` type-`P₂`, `msigma_isNilpotent_of_isTypeP2` would make `M_σ` nilpotent.
* `IsTypeP M`: the `σ`-complement `E` of `M` is nontrivial (`SubgroupESetup.E_ne_bot`), so some
  prime `p ∣ |E|` lies in `π(M) ∖ σ(M)`.  Building a maximal-rank elementary abelian `A ≤ M` (as in
  `msigma_isNilpotent_of_isTypeP2`), if `p ∉ κ(M)` then Lemma 14.1 forces `M_σ` nilpotent — a
  contradiction; hence `p ∈ κ(M)`, so `κ(M) ≠ ∅`, i.e. `M` is type-`P`.

`IsTypeP M ∧ ¬ IsTypeP2 M` gives `κ(M) = π(M) ∖ σ(M)` (the only failure mode for a type-`P`
member is `κ(M) ⊊ π(M) ∖ σ(M)`, which is type-`P₂`), i.e. `IsTypeP1 M`. -/
theorem isTypeP1_of_mf_ne_msigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hne : MF M ≠ OddOrder.BG.Ch3.S10.Msigma M) :
    S14.IsTypeP1 M := by
  classical
  -- `M_σ` is not nilpotent (else `M_F = M_σ`).
  have hMσ_not_nil : ¬ Group.IsNilpotent ↥(OddOrder.BG.Ch3.S10.Msigma M) := fun hnil =>
    hne ((maxNilpotentNormalHall_eq_Msigma_iff_isNilpotent hG hM).mpr hnil)
  -- `¬ IsTypeP2 M` (else `M_σ` nilpotent, BG `msigma_isNilpotent_of_isTypeP2`).
  have hnotP2 : ¬ S14.IsTypeP2 M := fun hP2 =>
    hMσ_not_nil (S14.msigma_isNilpotent_of_isTypeP2 hG hM hP2)
  -- `IsTypeP M`: a prime `p ∣ |E|` lands in `κ(M)` (else Lemma 14.1 makes `M_σ` nilpotent).
  have hP : S14.IsTypeP M := by
    obtain ⟨E, E₁, E₂, E₃, hsetup⟩ := OddOrder.BG.Ch3.S12.exists_subgroupESetup hG hM
    have hEne : E ≠ ⊥ := hsetup.E_ne_bot hG
    have hEcard : Nat.card ↥E ≠ 1 := fun hc => hEne (Subgroup.card_eq_one.mp hc)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hEcard
    have : Fact p.Prime := ⟨hp⟩
    have hpE : p ∈ (Nat.card ↥E).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvd, Nat.card_pos.ne'⟩
    have hpσ : p ∉ OddOrder.BG.Ch3.S10.sigma M :=
      hsetup.not_mem_sigma_of_mem_primeFactors hG hpE
    -- `p ∈ π(M)`: `p ∣ |E|` and `E ≤ M`.
    have hpdvdM : p ∣ Nat.card ↥M := hpdvd.trans (Subgroup.card_dvd_of_le hsetup.E_le)
    have hpM : p ∈ (Nat.card ↥M).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpdvdM, Nat.card_pos.ne'⟩
    have hpπ : p ∈ S14.piSet M := hpM
    -- A maximal-rank elementary abelian `p`-subgroup `A = B.map M.subtype ≤ M`.
    obtain ⟨B, hBea, hBlog⟩ :=
      exists_isElementaryAbelian_log_card_ge_of_pos_le_pRank (G := ↥M) (p := p)
        (n := pRank ↥M p) (OddOrder.BG.Ch3.S12.one_le_pRank_of_mem_primeFactors hpM) (le_refl _)
    obtain ⟨j, hj⟩ := hBea.isPGroup.exists_card_eq
    have hjeq : j = pRank ↥M p := by
      have hsq := le_antisymm (le_pRank B hBea) hBlog
      rwa [hj, Nat.log_pow hp.one_lt] at hsq
    have hAmem : B.map M.subtype ∈ elemAbelianOfRank G p (pRank ↥M p) := by
      refine ⟨Subgroup.IsElementaryAbelian.map M.subtype_injective hBea, ?_⟩
      rw [Subgroup.card_map_of_injective M.subtype_injective, hj, hjeq]
    -- If `p ∉ κ(M)`, Lemma 14.1 makes `M_σ` nilpotent — contradiction.  So `p ∈ κ(M)`.
    by_contra hPfalse
    rw [S14.IsTypeP, Set.not_nonempty_iff_eq_empty] at hPfalse
    have hpκ : p ∉ S14.kappa M := (Set.eq_empty_iff_forall_notMem.mp hPfalse) p
    exact hMσ_not_nil
      (S14.msigma_structure_of_notMem_sigma_kappa hG hM hpπ hpσ hpκ hAmem
        (Subgroup.map_subtype_le _)).2.2
  -- `IsTypeP M ∧ ¬ IsTypeP2 M` ⟹ `κ(M) = π(M) ∖ σ(M)`, i.e. `IsTypeP1 M`.
  refine ⟨hP, ?_⟩
  by_contra hkne
  exact hnotP2 ⟨hP, hkne⟩

/-- **BG Theorem 15.2, step 1 derivation (b)** (mmd L4190, "Theorem 14.7(f) implies that
`q = |K*|` is a prime"): for a type-`P₁` maximal subgroup `M`, the order of
`Kstar = C_{M_σ}(K)` is prime.

Route (BG Theorem 14.7(f) via the `Z`-family duality):
* `typeP_duality` provides the unique non-conjugate partner `M*` with `Kstar ≤ M*`, `Kstar` a Hall
  `κ(M*)`-subgroup of `M*`, the symmetric relation `K = M*_σ ⊓ C_G(Kstar)`, and the disjunction
  `IsTypeP2 M ∨ IsTypeP2 M*`.
* Since `M` is type-`P₁`, it is not type-`P₂` (`not_isTypeP1_and_isTypeP2`); hence `M*` is
  type-`P₂`.
* `typeP_structure` applied to `M*` (with `Kstar` in the `K`-role) has the `IsTypeP2 M* →`
  conjunct `∃ q, q.Prime ∧ Nat.card ↥Kstar = q`, giving `|Kstar|` prime.

The Hall `(κ(M*) ∪ σ(M*))'`-subgroup `U*` of `M*` needed by `typeP_structure` is built by Hall's
theorem in the solvable `M*` (`Ch03.hall_E_exists`), as in `typeP_kstar_in_mf`. -/
theorem kstar_card_prime_of_inputs [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K Kstar : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hP1 : S14.IsTypeP1 M) (hKM : K ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hKstar : Kstar = OddOrder.BG.Ch3.S10.Msigma M ⊓ Subgroup.centralizer (K : Set G)) :
    (Nat.card ↥Kstar).Prime := by
  classical
  -- The unique non-conjugate partner `M*` and its symmetric `Z`-family data.
  obtain ⟨_hcompl, _hcop, Mstar, ⟨hMstarMax, hMstarP, _hMstarNC,
      ⟨hKstarLe, hKstarHall, hKeqMstar⟩, _hZcyc, _hTI, hP2disj, _hpart⟩, _huniq⟩ :=
    S14.typeP_duality hG hM hP1.1 hKM hK hKstar
  -- `M` type-`P₁` ⟹ `¬ IsTypeP2 M` ⟹ `M*` is type-`P₂`.
  have hMstar2 : S14.IsTypeP2 Mstar :=
    hP2disj.resolve_left (fun hM2 => S14.not_isTypeP1_and_isTypeP2 ⟨hP1, hM2⟩)
  -- A Hall `(κ(M*) ∪ σ(M*))'`-subgroup `U*` of `M*` (Hall's theorem in the solvable `M*`).
  have : Group.IsSolvable ↥Mstar := hG.isSolvable_of_mem_maximalSubgroups hMstarMax
  obtain ⟨U', hU'⟩ := Ch03.hall_E_exists (G := ↥Mstar)
    ((S14.kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
  have hUeq : (U'.map Mstar.subtype).subgroupOf Mstar = U' :=
    Subgroup.comap_map_eq_self_of_injective Mstar.subtype_injective U'
  have hUstar : Ch03.IsHallSubgroup ((S14.kappa Mstar ∪ OddOrder.BG.Ch3.S10.sigma Mstar)ᶜ)
      ((U'.map Mstar.subtype).subgroupOf Mstar) := by rw [hUeq]; exact hU'
  -- `typeP_structure` on `M*` (with `Kstar` in the `K`-role, `K` in the `Kstar`-role):
  -- the `IsTypeP2 M* →` conjunct yields `σ(M*) = β(M*) ∧ ∃ q, q.Prime ∧ Nat.card ↥Kstar = q ∧ …`.
  obtain ⟨_hσβ, q, hq, hKstarq, _hTI⟩ :=
    (S14.typeP_structure hG hMstarMax hMstarP hKstarLe hKstarHall hKeqMstar hUstar).2.2.2.2.1
      hMstar2
  rw [hKstarq]; exact hq

end OddOrder.BG.Ch4.S15


