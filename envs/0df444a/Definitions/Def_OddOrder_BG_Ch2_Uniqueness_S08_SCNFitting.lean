-- Prove2me | Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_SCNFitting
-- name    : OddOrder_BG_Ch2_Uniqueness_S08_SCNFitting
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:23:19.846196+00:00
-- url     : https://prove2.me/theorems/cd5fc73f-dfb2-4217-8293-c8d8ec3ae8df
-- title:
--   BG §8: SCN and the Fitting subgroup of a maximal subgroup
-- statement:
--   Part of the Bender–Glauberman §8 development relating $\mathrm{SCN}$ subgroups to the Fitting subgroup of a maximal subgroup. The bundle consists of lemmas only.
--
--   The bundle also proves 36 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch2_Uniqueness/S08_SCNFitting.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch2_Uniqueness/S08_SCNFitting.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch2_Uniqueness_S08_PiCoreCentralizers

namespace OddOrder.BG.Ch2.S08

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- BG (8.7) with (8.2): after `π(F(H)) = π(F(M))`, the `p`-complement core of
`H` lies in the original maximal subgroup `M`. -/
theorem opiCoreInG_singleton_compl_le_maximal_of_cFittingInG_le_of_primes_eq
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : Group.IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hPrimes : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) :
    opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M := by
  let Ap : Subgroup G := opiCoreInG ({p} : Set ℕ) (cFittingInG M A0)
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  change N ≤ M
  have hN_cent_Ap : N ≤ Subgroup.centralizer (Ap : Set G) := by
    have hAp_cent_N : Ap ≤ Subgroup.centralizer (N : Set G) := by
      dsimp [Ap, N]
      exact opiCoreInG_singleton_cFittingInG_le_centralizer_opiCoreInG_singleton_compl
        hG hM hA0 hHsolv hAH hPrimes
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hAp_cent_N hy) x hx).symm
  have hCentAp_le_M : Subgroup.centralizer (Ap : Set G) ≤ M := by
    have hOp_ne : centerFittingOpCoreInG p M ≠ ⊥ :=
      centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hp
    have hOp_le_Ap : centerFittingOpCoreInG p M ≤ Ap := by
      dsimp [Ap]
      exact centerFittingOpCoreInG_le_opiCoreInG_cFittingInG_singleton hA0
    exact centralizer_le_maximal_of_centerFittingOpCoreInG_le hG hM hOp_ne hOp_le_Ap
  exact hN_cent_Ap.trans hCentAp_le_M

/-- BG (8.7): in the non-`p`-group case, each q-core of `F(H)` lies in the
original maximal subgroup `M` whenever `H` contains `C_F(M)(A0)`. -/
theorem opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hHsolv : Group.IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors) :
    opiCoreInG ({q} : Set ℕ) (fittingInG H) ≤ M := by
  exact
    opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_compl_le_opiCoreInG_compl
      hG hM hp hA0 hFnp hq
      (opiCoreInG_cFittingInG_singleton_compl_le_opiCoreInG_singleton_compl
        hG hM hA0 hHsolv hAH hq)

/-- BG (8.5) applied to the commutator form (8.4): if `q ∈ π(F(M))`, every
`A = C_F(M)(A0)`-invariant `π(A)`-complement subgroup lies in `O_{q'}(X)`. -/
theorem hInvariant_le_opiCoreInG_singleton_compl_of_mem_primeFactors_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : Group.IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hq : q ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ≤ opiCoreInG ({q} : Set ℕ)ᶜ X := by
  obtain ⟨r, hr, hrq⟩ :=
    exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup
      (H := ↥(fittingInG M)) hp hFnp q
  have : Fact r.Prime := ⟨(Nat.mem_primeFactors.mp hr).1⟩
  let Br : Subgroup G := centerFittingOpCoreInG r M
  have hY_comm : Y ≤ ⁅Br, Y⁆ := by
    dsimp [Br]
    exact hInvariant_le_commutator_centerFittingOpCoreInG_of_not_pGroup
      hG hM hA0 hFnp hr hY
  have hBr_core : Br ≤ opiCoreInG ({q} : Set ℕ)ᶜ X := by
    dsimp [Br]
    exact centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA0 hXsolv hAX hq hr (fun hqr => hrq hqr.symm)
  have hY_X : Y ≤ X := hY.1
  have hY_norm_core : Y ≤ Subgroup.normalizer (opiCoreInG ({q} : Set ℕ)ᶜ X : Set G) :=
    hY_X.trans (le_normalizer_opiCoreInG ({q} : Set ℕ)ᶜ X)
  have hcomm_core : ⁅Br, Y⁆ ≤ opiCoreInG ({q} : Set ℕ)ᶜ X :=
    (Subgroup.commutator_mono hBr_core le_rfl).trans
      (OddOrder.Isaacs.Ch04.commutator_le_of_le_normalizer hY_norm_core)
  exact hY_comm.trans hcomm_core

/-- If `Y ≤ X` and `Y` lies in `O_{q'}(X)` for every `q ∈ π`, then `Y` lies in
`O_{π'}(X)`. This packages the BG (8.5) intersection step
`⋂_{q∈π} O_{q'}(X) = O_{π'}(X)` in the direction needed for Hypothesis 7.1. -/
theorem le_opiCoreInG_compl_of_forall_le_opiCoreInG_singleton_compl
    [Finite G] {π : Set ℕ} {X Y : Subgroup G} (hYX : Y ≤ X)
    (hYq : ∀ q, q ∈ π → Y ≤ opiCoreInG ({q} : Set ℕ)ᶜ X) :
    Y ≤ opiCoreInG πᶜ X := by
  let K : Subgroup G :=
    X ⊓ ⨅ q : {q : ℕ // q ∈ π}, opiCoreInG ({q.1} : Set ℕ)ᶜ X
  have hYK : Y ≤ K := by
    refine le_inf hYX ?_
    refine le_iInf ?_
    intro q
    exact hYq q.1 q.2
  have hKX : K ≤ X := inf_le_left
  have hKnorm : (K.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKX]
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hnormX := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hx) y
    constructor
    · intro hy
      simp only [K, Subgroup.mem_inf, Subgroup.mem_iInf] at hy ⊢
      refine ⟨hnormX.mp hy.1, ?_⟩
      intro q
      have hnormCore :=
        Subgroup.mem_normalizer_iff.mp
          (le_normalizer_opiCoreInG ({q.1} : Set ℕ)ᶜ X hx) y
      exact hnormCore.mp (hy.2 q)
    · intro hy
      simp only [K, Subgroup.mem_inf, Subgroup.mem_iInf] at hy ⊢
      refine ⟨hnormX.mpr hy.1, ?_⟩
      intro q
      have hnormCore :=
        Subgroup.mem_normalizer_iff.mp
          (le_normalizer_opiCoreInG ({q.1} : Set ℕ)ᶜ X hx) y
      exact hnormCore.mpr (hy.2 q)
  have hKpi : Subgroup.IsPiSubgroup πᶜ K := by
    intro s hs hsπ
    have hK_le_core_s : K ≤ opiCoreInG ({s} : Set ℕ)ᶜ X := by
      dsimp [K]
      exact inf_le_right.trans
        (iInf_le (fun q : {q : ℕ // q ∈ π} =>
          opiCoreInG ({q.1} : Set ℕ)ᶜ X) ⟨s, hsπ⟩)
    have hs_core : s ∈ ({s} : Set ℕ)ᶜ :=
      isPiSubgroup_opiCoreInG ({s} : Set ℕ)ᶜ X s
        (Nat.primeFactors_mono (Subgroup.card_dvd_of_le hK_le_core_s)
          Nat.card_pos.ne' hs)
    exact hs_core (by simp)
  exact hYK.trans (le_opiCoreInG_of_normal_of_isPiSubgroup hKX hKnorm hKpi)

/-- BG (8.5), support-detection form: if the `σ`-complement core of a solvable
subgroup `X` containing `C_F(M)(A0)` is trivial and `σ ⊆ π(F(M))`, then every prime
of `F(M)` lies in `σ`. -/
theorem primesOf_fittingInG_subset_of_opiCoreInG_compl_eq_bot
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 X : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : Group.IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    {σ : Set ℕ}
    (hσπ : σ ⊆ OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
    (hOσ : opiCoreInG σᶜ X = ⊥) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG M) ⊆ σ := by
  intro r hrπ
  by_contra hrσ
  have hrF : r ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hrπ
  have : Fact r.Prime := ⟨(Nat.mem_primeFactors.mp hrF).1⟩
  have hBrX : centerFittingOpCoreInG r M ≤ X :=
    (centerFittingOpCoreInG_le_cFittingInG (q := r) hA0).trans hAX
  have hBr_core : centerFittingOpCoreInG r M ≤ opiCoreInG σᶜ X := by
    refine le_opiCoreInG_compl_of_forall_le_opiCoreInG_singleton_compl hBrX ?_
    intro q hqσ
    have hqπ : q ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := hσπ hqσ
    have hqF : q ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
      simpa [OddOrder.BG.Ch2.S07.primesOf] using hqπ
    have : Fact q.Prime := ⟨(Nat.mem_primeFactors.mp hqF).1⟩
    have hqr : q ≠ r := by
      intro hqr
      exact hrσ (by simpa [hqr] using hqσ)
    exact centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA0 hXsolv hAX hqF hrF hqr
  have hBr_bot : centerFittingOpCoreInG r M = ⊥ :=
    le_bot_iff.mp (by
      rw [← hOσ]
      exact hBr_core)
  exact (centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hrF) hBr_bot

/-- BG (8.5), generated-condition form: in the non-p-group case, every member of
`ℋ_X(C_F(M)(A0); π(C_F(M)(A0))^c)` lies in `O_{π(C_F(M)(A0))^c}(X)`. -/
theorem hInvariant_le_opiCoreInG_primesOf_cFittingInG_compl_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 X Y : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hXsolv : Group.IsSolvable ↥X)
    (hAX : cFittingInG M A0 ≤ X)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hY : Y ∈ hInvariant X (cFittingInG M A0)
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Y ≤ opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ X := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  refine le_opiCoreInG_compl_of_forall_le_opiCoreInG_singleton_compl hY.1 ?_
  intro q hqA
  have hqF_primes : q ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    simpa [hPrimes] using hqA
  have hqF : q ∈ (Nat.card ↥(fittingInG M)).primeFactors := by
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hqF_primes
  have : Fact q.Prime := ⟨(Nat.mem_primeFactors.mp hqF).1⟩
  exact hInvariant_le_opiCoreInG_singleton_compl_of_mem_primeFactors_not_pGroup
    hG hM hA0 hXsolv hAX hp hFnp hqF hY

/-- BG (8.5) verifies Hypothesis 7.1 for `A = C_F(M)(A0)` in the non-p-group case. -/
theorem hypothesis71_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0) := by
  refine ⟨?_, ?_, ?_⟩
  · exact cFitting_ne_bot_of_isMaxElemAbelianIn hp hA0
  · exact lt_of_le_of_lt (inf_le_right.trans (fittingInG_le M))
      (mem_maximalSubgroups.mp hM).lt_top
  · intro X hAX hXlt
    refine OddOrder.BG.Ch2.S07.generated_eq_of_forall_le_opiCoreInG hAX ?_
    intro Y hY
    exact hInvariant_le_opiCoreInG_primesOf_cFittingInG_compl_of_not_pGroup
      hG hM hA0 (hG.isSolvable_of_lt_top X hXlt) hAX hp hFnp hY

/-- Theorem 7.2 specialized to `A = C_F(M)(A0)`: once Hypothesis 7.1 is verified,
`K = O_{π(A)^c}(C_G(A))` acts transitively on `ℋ_G*(A;q)`. -/
theorem transitive_cFittingInG_of_hypothesis71 [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    OddOrder.BG.Ch2.S07.ConjTransitiveOn
      (OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0))
      (hInvariantStar ⊤ (cFittingInG M A0) {q}) :=
  OddOrder.BG.Ch2.S07.transitive_of_three_le_rank_center hG hA hq (by
    dsimp [cFittingInG]
    exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA0 hm)

/-- The subgroup `C_F(M)(A0)` is subnormal inside `F(M)`, because `F(M)` is nilpotent. -/
theorem cFittingInG_subgroupOf_fittingInG_isSubnormal [Finite G] {M A0 : Subgroup G} :
    ((cFittingInG M A0).subgroupOf (fittingInG M)).IsSubnormal := by
  have : Group.IsNilpotent ↥(fittingInG M) := fittingInG_isNilpotent M
  exact OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite _

/-- Theorem 7.4 specialized to the propagation step in BG (8.6), with
`A = C_F(M)(A0)` and `P = F(M)`. -/
theorem transitivity_propagates_to_fittingInG_of_cFittingInG [Finite G]
    (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime] {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ) :
    Subgroup.centralizer (fittingInG M : Set G) ⊓
        OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0) =
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
        (Subgroup.centralizer (fittingInG M : Set G)) ∧
    OddOrder.BG.Ch2.S07.ConjTransitiveOn
      (opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
        (Subgroup.centralizer (fittingInG M : Set G)))
      (hInvariantStar ⊤ (fittingInG M) {q}) ∧
    hInvariantStar ⊤ (fittingInG M) {q} ⊆
      hInvariantStar ⊤ (cFittingInG M A0) {q} ∧
    (∀ Q ∈ hInvariantStar ⊤ (fittingInG M) {q},
      fittingInG M ⊓ derivedInG (Subgroup.normalizer (fittingInG M)) ≤
        derivedInG (Subgroup.normalizer Q) ∧
      ∀ n : G, n ∈ Subgroup.normalizer (fittingInG M) →
        ∃ c ∈ opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
            (Subgroup.centralizer (fittingInG M : Set G)),
          ∃ m ∈ Subgroup.normalizer (fittingInG M) ⊓ Subgroup.normalizer Q, n = c * m) := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hPproper : fittingInG M < ⊤ :=
    lt_of_le_of_lt (fittingInG_le M) (mem_maximalSubgroups.mp hM).lt_top
  have hPpi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0)) (fittingInG M) := by
    rw [hPrimes]
    intro r hr
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hr
  have hAP : cFittingInG M A0 ≤ fittingInG M := by
    dsimp [cFittingInG]
    exact inf_le_right
  exact OddOrder.BG.Ch2.S07.transitivity_propagates hG hA hq (fittingInG M)
    hPproper hPpi hAP cFittingInG_subgroupOf_fittingInG_isSubnormal
    (transitive_cFittingInG_of_hypothesis71 hG hA0 hm hA hq)

/-- The relative centralizer C_F(M)(A0) is proper whenever M is maximal. -/
theorem cFitting_lt_top_of_mem_maximal {M A0 : Subgroup G}
    (hM : M ∈ maximalSubgroups G) :
    Subgroup.centralizer (A0 : Set G) ⊓ fittingInG M < ⊤ :=
  lt_of_le_of_lt (inf_le_right.trans (fittingInG_le M))
    (mem_maximalSubgroups.mp hM).lt_top

/-- BG (8.6) packaged for A = C_{F(M)}(A0): once Hypothesis 7.1 and the
centralizer pi-subgroup condition are known, H_G*(A;q) is a singleton. -/
theorem hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_centralizer_isPiSubgroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact q.Prime]
    {M A0 : Subgroup G} (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hCpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))
      (Subgroup.centralizer (cFittingInG M A0 : Set G)))
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q}) :
    Q₁ = Q₂ :=
  OddOrder.BG.Ch2.S07.hInvariantStar_eq_of_three_le_rank_center_of_centralizer_isPiSubgroup
    hG hA hq (by
      dsimp [cFittingInG]
      exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA0 hm) hCpi hQ₁ hQ₂

/-- BG (8.6) for `A = C_F(M)(A0)` in the non-`p`-group case: once Hypothesis 7.1
is verified for `A`, the star family `ℋ_G*(A;q)` is a singleton for every
`q` in the complement of `π(A)`. -/
theorem hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    {Q₁ Q₂ : Subgroup G} (hQ₁ : Q₁ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q})
    (hQ₂ : Q₂ ∈ hInvariantStar ⊤ (cFittingInG M A0) {q}) :
    Q₁ = Q₂ :=
  hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_centralizer_isPiSubgroup
    hG hA0 hm hA hq
    (centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA0 hFnp) hQ₁ hQ₂

/-- BG (8.6), normalizer bridge: in the non-p-group case, the propagation
 decomposition forces every element normalizing F(M) to normalize each member of
 `H_G*(F(M);q)`. -/
theorem normalizer_fittingInG_le_normalizer_of_hInvariantStar_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    Subgroup.normalizer (fittingInG M : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  have hprop := transitivity_propagates_to_fittingInG_of_cFittingInG
    hG hM hA0 hm hA hq
  have hKbot :
      OddOrder.BG.Ch2.S07.kSubgroup (cFittingInG M A0) = ⊥ :=
    kSubgroup_cFittingInG_eq_bot_of_not_pGroup hG hM hA0 hFnp
  have hopi_bot :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ
        (Subgroup.centralizer (fittingInG M : Set G)) = ⊥ := by
    have hfirst := hprop.1
    rw [hKbot, inf_bot_eq] at hfirst
    exact hfirst.symm
  intro n hn
  obtain ⟨c, hc, m, hmN, hn_eq⟩ := (hprop.2.2.2 Q hQ).2 n hn
  have hc_one : c = 1 := by
    have hc_bot : c ∈ (⊥ : Subgroup G) := by
      rwa [hopi_bot] at hc
    exact Subgroup.mem_bot.mp hc_bot
  have hmQ : m ∈ Subgroup.normalizer (Q : Set G) := hmN.2
  rw [hn_eq, hc_one, one_mul]
  exact hmQ

/-- BG (8.6), maximal-subgroup form of the normalizer bridge: in the non-p-group
 case, M normalizes every member of `H_G*(F(M);q)`. -/
theorem maximal_le_normalizer_of_hInvariantStar_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    M ≤ Subgroup.normalizer (Q : Set G) := by
  intro x hxM
  exact normalizer_fittingInG_le_normalizer_of_hInvariantStar_of_not_pGroup
    hG hM hA0 hm hFnp hA hq hQ (mem_normalizer_fittingInG_of_mem hxM)

/-- BG (8.6): a nontrivial member of `H_G*(F(M);q)` lies in the maximal subgroup
`M` once `M` is known to normalize it. -/
theorem hInvariantStar_le_maximal_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) (hQne : Q ≠ ⊥) :
    Q ≤ M :=
  le_maximal_of_le_normalizer_of_ne_bot_isPiSubgroup_singleton hG hM
    (maximal_le_normalizer_of_hInvariantStar_fittingInG_of_not_pGroup
      hG hM hA0 hm hFnp hA hq hQ)
    hQne (hInvariantStar_isPiSubgroup hQ)

/-- BG (8.6): a nontrivial member of `H_G*(F(M);q)` is absorbed by `F(M)`. -/
theorem hInvariantStar_le_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) (hQne : Q ≠ ⊥) :
    Q ≤ fittingInG M := by
  have hQM : Q ≤ M :=
    hInvariantStar_le_maximal_of_not_pGroup hG hM hA0 hm hFnp hA hq hQ hQne
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    maximal_le_normalizer_of_hInvariantStar_fittingInG_of_not_pGroup
      hG hM hA0 hm hFnp hA hq hQ
  have hQnorm : (Q.subgroupOf M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hMQ
  exact le_fittingInG_of_normal_isPiSubgroup_singleton hQM hQnorm
    (hInvariantStar_isPiSubgroup hQ)

/-- BG (8.6) endpoint for `F(M)`: every member of `H_G*(F(M);q)` is trivial for
`q` outside `π(C_F(M)(A0))` in the non-p-group case. -/
theorem hInvariantStar_eq_bot_of_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (fittingInG M) {q}) :
    Q = ⊥ := by
  by_cases hQbot : Q = ⊥
  · exact hQbot
  have hQleF : Q ≤ fittingInG M :=
    hInvariantStar_le_fittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hQ hQbot
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hFpi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0)) (fittingInG M) := by
    rw [hPrimes]
    intro r hr
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hr
  have hQpi_compl : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ Q := by
    intro r hr
    have hrq : r = q := Set.mem_singleton_iff.mp ((hInvariantStar_isPiSubgroup hQ) r hr)
    rw [hrq]
    exact hq
  exact eq_bot_of_le_of_isPiSubgroup_of_isPiSubgroup_compl hQleF hFpi hQpi_compl

/-- BG (8.6) endpoint for `A = C_F(M)(A0)`: every member of `H_G*(A;q)` is
trivial for `q` outside `π(A)` in the non-p-group case. -/
theorem hInvariantStar_eq_bot_of_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariantStar ⊤ (cFittingInG M A0) {q}) :
    Q = ⊥ := by
  have hBotInvF : (⊥ : Subgroup G) ∈ hInvariant ⊤ (fittingInG M) {q} := by
    rw [mem_hInvariant]
    refine ⟨bot_le, ?_, ?_⟩
    · intro x _
      rw [Subgroup.mem_normalizer_iff]
      intro y
      simp
    · intro r hr
      rw [Subgroup.card_bot] at hr
      simp at hr
  obtain ⟨R, hRstar, _hBotR⟩ := exists_le_hInvariantStar hBotInvF
  have hRbot : R = ⊥ :=
    hInvariantStar_eq_bot_of_fittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hRstar
  have hprop := transitivity_propagates_to_fittingInG_of_cFittingInG
    hG hM hA0 hm hA hq
  have hRstarA : R ∈ hInvariantStar ⊤ (cFittingInG M A0) {q} := hprop.2.2.1 hRstar
  have hQR : Q = R :=
    hInvariantStar_eq_of_cFittingInG_of_hypothesis71_of_not_pGroup
      hG hM hA0 hm hFnp hA hq hQ hRstarA
  exact hQR.trans hRbot

/-- BG (8.6), non-star form: every `A`-invariant q-subgroup is trivial for
`A = C_F(M)(A0)` and `q` outside `π(A)` in the non-p-group case. -/
theorem hInvariant_eq_bot_of_cFittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 Q : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hQ : Q ∈ hInvariant ⊤ (cFittingInG M A0) {q}) :
    Q = ⊥ := by
  obtain ⟨R, hRstar, hQR⟩ := exists_le_hInvariantStar hQ
  have hRbot : R = ⊥ :=
    hInvariantStar_eq_bot_of_cFittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hRstar
  exact le_bot_iff.mp (by simpa [hRbot] using hQR)

/-- BG (8.6), q-core form: if `A = C_F(M)(A0)` lies in `H`, then the ambient
q-core of `H` is trivial for `q` outside `π(A)` in the non-p-group case. -/
theorem opiCoreInG_singleton_eq_bot_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hq : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ)
    (hAH : cFittingInG M A0 ≤ H) :
    opiCoreInG ({q} : Set ℕ) H = ⊥ := by
  have hQ : opiCoreInG ({q} : Set ℕ) H ∈ hInvariant ⊤ (cFittingInG M A0) {q} := by
    rw [mem_hInvariant]
    exact ⟨le_top,
      hAH.trans (le_normalizer_opiCoreInG ({q} : Set ℕ) H),
      isPiSubgroup_opiCoreInG ({q} : Set ℕ) H⟩
  exact hInvariant_eq_bot_of_cFittingInG_of_not_pGroup hG hM hA0 hm hFnp hA hq hQ

/-- If q divides `|F(H)|`, then the ambient q-core `O_q(H)` is nontrivial. -/
theorem opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG [Finite G]
    {q : ℕ} [Fact q.Prime] {H : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG H)).primeFactors) :
    opiCoreInG ({q} : Set ℕ) H ≠ ⊥ := by
  have hZne : centerFittingOpCoreInG q H ≠ ⊥ :=
    centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq
  have hZpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q H) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG H)
  have hZleO : centerFittingOpCoreInG q H ≤ opiCoreInG ({q} : Set ℕ) H :=
    le_opiCoreInG_of_normal_of_isPiSubgroup (centerFittingOpCoreInG_le q H)
      (centerFittingOpCoreInG_subgroupOf_normal q H) hZpi
  intro hObot
  apply hZne
  exact le_bot_iff.mp (by
    rw [← hObot]
    exact hZleO)

/-- If q divides `|F(H)|`, then the ambient q-core of `F(H)` is nontrivial. -/
theorem opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors [Finite G]
    {q : ℕ} [Fact q.Prime] {H : Subgroup G}
    (hq : q ∈ (Nat.card ↥(fittingInG H)).primeFactors) :
    opiCoreInG ({q} : Set ℕ) (fittingInG H) ≠ ⊥ := by
  have hZne : centerFittingOpCoreInG q H ≠ ⊥ :=
    centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hq
  have hZleF : centerFittingOpCoreInG q H ≤ fittingInG H :=
    (centerFittingOpCoreInG_le_centerFittingInG q H).trans
      (centerFittingInG_le_fittingInG H)
  have hZnormF : ((centerFittingOpCoreInG q H).subgroupOf (fittingInG H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZleF]
    have hH_norm_Z : H ≤ Subgroup.normalizer (centerFittingOpCoreInG q H : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centerFittingOpCoreInG_le q H)).mp
        (centerFittingOpCoreInG_subgroupOf_normal q H)
    exact (fittingInG_le H).trans hH_norm_Z
  have hZpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (centerFittingOpCoreInG q H) := by
    dsimp [centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({q} : Set ℕ) (centerFittingInG H)
  have hZleO : centerFittingOpCoreInG q H ≤
      opiCoreInG ({q} : Set ℕ) (fittingInG H) :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hZleF hZnormF hZpi
  intro hObot
  apply hZne
  exact le_bot_iff.mp (by
    rw [← hObot]
    exact hZleO)

/-- BG (8.8), Prop 1.4 bridge: once `D_p = O_p(F(H))` is inside `M`,
`D_p` centralizes the `p`-complement core of `M`. -/
theorem opiCoreInG_fittingInG_singleton_le_centralizer_opiCoreInG_singleton_compl_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : Group.IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hDpM : opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤ M) :
    opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤
      Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ M : Set G) := by
  let Dp : Subgroup G := opiCoreInG ({p} : Set ℕ) (fittingInG H)
  let N : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ M
  change Dp ≤ Subgroup.centralizer (N : Set G)
  have hOFM_le_OA : opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0) :=
    opiCoreInG_singleton_compl_fittingInG_le_opiCoreInG_singleton_compl_cFittingInG
      hA0
  have hOA_le_OH : opiCoreInG ({p} : Set ℕ)ᶜ (cFittingInG M A0) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ H :=
    opiCoreInG_cFittingInG_singleton_compl_le_opiCoreInG_singleton_compl
      hG hM hA0 hHsolv hAH hp
  have hOFM_le_OH : opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) ≤
      opiCoreInG ({p} : Set ℕ)ᶜ H :=
    hOFM_le_OA.trans hOA_le_OH
  have hDp_cent_OFM : Dp ≤
      Subgroup.centralizer (opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) : Set G) := by
    dsimp [Dp]
    exact opiCoreInG_fittingInG_le_centralizer_of_le_opiCoreInG_compl
      ({p} : Set ℕ) hOFM_le_OH
  have hN_M : N ≤ M := by
    dsimp [N]
    exact opiCoreInG_le ({p} : Set ℕ)ᶜ M
  have hDp_norm_N : Dp ≤ Subgroup.normalizer (N : Set G) := by
    dsimp [N]
    exact hDpM.trans (le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M)
  have hDp_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) Dp := by
    dsimp [Dp]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (fittingInG H)
  have hN_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ N := by
    dsimp [N]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ M
  have hCop : Nat.Coprime (Nat.card ↥Dp) (Nat.card ↥N) :=
    coprime_card_of_isPiSubgroup_of_isPiSubgroup_compl hDp_pi hN_pi
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hNsolv : Group.IsSolvable ↥N :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hN_M)
      (Subgroup.inclusion_injective hN_M)
  have hFN_le_OFM : fittingInG N ≤ opiCoreInG ({p} : Set ℕ)ᶜ (fittingInG M) := by
    dsimp [N]
    exact fittingInG_opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_fittingInG M
  have hDp_cent_FN : Dp ≤ Subgroup.centralizer (fittingInG N : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hDp_cent_OFM hd) y (hFN_le_OFM hy)
  exact le_centralizer_of_coprime_normalizes_of_le_centralizer_fittingInG
    hDp_norm_N hCop hDp_cent_FN

/-- BG (8.8): the `p`-complement core of `M` lies in `H` once `D_p` lies in
`M` and the Prop 1.4 centralizer bridge is available. -/
theorem opiCoreInG_singleton_compl_maximal_le_of_fittingInG_singleton_le_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hpM : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hpH : p ∈ (Nat.card ↥(fittingInG H)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : Group.IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hDpM : opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤ M) :
    opiCoreInG ({p} : Set ℕ)ᶜ M ≤ H := by
  let Dp : Subgroup G := opiCoreInG ({p} : Set ℕ) (fittingInG H)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ M
  change K ≤ H
  have hDp_H : Dp ≤ H := by
    dsimp [Dp]
    exact (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans (fittingInG_le H)
  have hDp_norm_H : (Dp.subgroupOf H).Normal := by
    dsimp [Dp]
    exact opiCoreInG_fittingInG_subgroupOf_normal ({p} : Set ℕ) H
  have hDp_ne : Dp ≠ ⊥ := by
    dsimp [Dp]
    exact opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors hpH
  have hNormalizer_Dp_eq_H : Subgroup.normalizer (Dp : Set G) = H :=
    normalizer_eq_of_normal_of_mem_maximal hG hH hDp_norm_H hDp_ne hDp_H
  have hDp_cent_K : Dp ≤ Subgroup.centralizer (K : Set G) := by
    dsimp [Dp, K]
    exact opiCoreInG_fittingInG_singleton_le_centralizer_opiCoreInG_singleton_compl_maximal
      hG hM hpM hA0 hHsolv hAH hDpM
  have hK_cent_Dp : K ≤ Subgroup.centralizer (Dp : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    exact (Subgroup.mem_centralizer_iff.mp (hDp_cent_K hd) x hx).symm
  exact hK_cent_Dp.trans (by
    simpa [hNormalizer_Dp_eq_H] using Subgroup.centralizer_le_normalizer (Dp : Set G))

/-- BG (8.8), reverse inclusion: once `O_{p'}(M)` lies in `H`, it is absorbed by
`O_{p'}(H)`. -/
theorem opiCoreInG_singleton_compl_maximal_le_opiCoreInG_singleton_compl_of_le_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hHsolv : Group.IsSolvable ↥H)
    (hAH : cFittingInG M A0 ≤ H)
    (hOMH : opiCoreInG ({p} : Set ℕ)ᶜ M ≤ H) :
    opiCoreInG ({p} : Set ℕ)ᶜ M ≤ opiCoreInG ({p} : Set ℕ)ᶜ H := by
  let R : Subgroup G := centerFittingOpCoreInG p M
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ M
  let NH : Subgroup G := Subgroup.normalizer (R : Set G) ⊓ H
  let CH : Subgroup G := Subgroup.centralizer (R : Set G) ⊓ H
  change K ≤ opiCoreInG ({p} : Set ℕ)ᶜ H
  have hR_H : R ≤ H := by
    dsimp [R]
    exact (centerFittingOpCoreInG_le_cFittingInG (q := p) hA0).trans hAH
  have hR_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) R := by
    dsimp [R, centerFittingOpCoreInG]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (centerFittingInG M)
  have hR_ne : R ≠ ⊥ := by
    dsimp [R]
    exact centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hp
  have hNormalizer_R_eq_M : Subgroup.normalizer (R : Set G) = M := by
    dsimp [R]
    exact normalizer_centerFittingOpCoreInG_eq_of_ne_bot hG hM hR_ne
  have hK_NH : K ≤ NH := by
    intro x hx
    refine ⟨?_, hOMH hx⟩
    have hxM : x ∈ M := by
      dsimp [K] at hx
      exact opiCoreInG_le ({p} : Set ℕ)ᶜ M hx
    simpa [hNormalizer_R_eq_M] using hxM
  have hK_norm_NH : (K.subgroupOf NH).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK_NH]
    intro x hx
    have hxM : x ∈ M := by
      have hxN : x ∈ Subgroup.normalizer (R : Set G) := hx.1
      simpa [hNormalizer_R_eq_M] using hxN
    dsimp [K]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M hxM
  have hK_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ M
  have hK_le_ONH : K ≤ opiCoreInG ({p} : Set ℕ)ᶜ NH :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hK_NH hK_norm_NH hK_pi
  have hONH_le_OCH : opiCoreInG ({p} : Set ℕ)ᶜ NH ≤ opiCoreInG ({p} : Set ℕ)ᶜ CH := by
    dsimp [NH, CH]
    exact opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf hR_H hR_pi
  have hR_p : IsPGroup p ↥R :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton hR_pi
  have hOCH_le_OH : opiCoreInG ({p} : Set ℕ)ᶜ CH ≤ opiCoreInG ({p} : Set ℕ)ᶜ H := by
    dsimp [CH]
    exact OddOrder.BG.Ch2.S07.opiCoreInG_centralizer_inf_le_opiCoreInG
      hHsolv hR_H hR_p
  exact hK_le_ONH.trans (hONH_le_OCH.trans hOCH_le_OH)

/-- BG (8.8), first inclusion: if `D = F(H)` is already contained in `M`, then
`O_{p'}(H)` is contained in `O_{p'}(M)`. -/
theorem opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_of_fittingInG_le_maximal
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M H : Subgroup G} (hM : M ∈ maximalSubgroups G) (hH : H ∈ maximalSubgroups G)
    (hpH : p ∈ (Nat.card ↥(fittingInG H)).primeFactors)
    (hFH_le_M : fittingInG H ≤ M)
    (hOpComplH_le_M : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M) :
    opiCoreInG ({p} : Set ℕ)ᶜ H ≤ opiCoreInG ({p} : Set ℕ)ᶜ M := by
  let Dp : Subgroup G := opiCoreInG ({p} : Set ℕ) (fittingInG H)
  let K : Subgroup G := opiCoreInG ({p} : Set ℕ)ᶜ H
  let NM : Subgroup G := Subgroup.normalizer (Dp : Set G) ⊓ M
  let CM : Subgroup G := Subgroup.centralizer (Dp : Set G) ⊓ M
  change K ≤ opiCoreInG ({p} : Set ℕ)ᶜ M
  have hDp_H : Dp ≤ H := by
    dsimp [Dp]
    exact (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans (fittingInG_le H)
  have hDp_norm_H : (Dp.subgroupOf H).Normal := by
    dsimp [Dp]
    exact opiCoreInG_fittingInG_subgroupOf_normal ({p} : Set ℕ) H
  have hDp_ne : Dp ≠ ⊥ := by
    dsimp [Dp]
    exact opiCoreInG_singleton_fittingInG_ne_bot_of_mem_primeFactors hpH
  have hNormalizer_Dp_eq_H : Subgroup.normalizer (Dp : Set G) = H :=
    normalizer_eq_of_normal_of_mem_maximal hG hH hDp_norm_H hDp_ne hDp_H
  have hK_le_NM : K ≤ NM := by
    intro x hx
    refine ⟨?_, hOpComplH_le_M hx⟩
    have hxH : x ∈ H := by
      dsimp [K] at hx
      exact opiCoreInG_le ({p} : Set ℕ)ᶜ H hx
    simpa [hNormalizer_Dp_eq_H] using hxH
  have hK_norm_NM : (K.subgroupOf NM).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK_le_NM]
    intro x hx
    have hxH : x ∈ H := by
      have hxN : x ∈ Subgroup.normalizer (Dp : Set G) := hx.1
      simpa [hNormalizer_Dp_eq_H] using hxN
    dsimp [K]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H hxH
  have hK_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ)ᶜ K := by
    dsimp [K]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hK_le_ONM : K ≤ opiCoreInG ({p} : Set ℕ)ᶜ NM :=
    le_opiCoreInG_of_normal_of_isPiSubgroup hK_le_NM hK_norm_NM hK_pi
  have hDp_M : Dp ≤ M := by
    dsimp [Dp]
    exact (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans hFH_le_M
  have hDp_pi : Subgroup.IsPiSubgroup ({p} : Set ℕ) Dp := by
    dsimp [Dp]
    exact isPiSubgroup_opiCoreInG ({p} : Set ℕ) (fittingInG H)
  have hONM_le_OCM : opiCoreInG ({p} : Set ℕ)ᶜ NM ≤ opiCoreInG ({p} : Set ℕ)ᶜ CM := by
    dsimp [NM, CM]
    exact opiCoreInG_singleton_compl_normalizer_inf_le_centralizer_inf hDp_M hDp_pi
  have hMsolv : Group.IsSolvable ↥M := hG.isSolvable_of_mem_maximalSubgroups hM
  have hDp_p : IsPGroup p ↥Dp := by
    dsimp [Dp]
    exact isPGroup_opiCoreInG_singleton (fittingInG H)
  have hOCM_le_OM : opiCoreInG ({p} : Set ℕ)ᶜ CM ≤ opiCoreInG ({p} : Set ℕ)ᶜ M := by
    dsimp [CM]
    exact OddOrder.BG.Ch2.S07.opiCoreInG_centralizer_inf_le_opiCoreInG
      hMsolv hDp_M hDp_p
  exact hK_le_ONM.trans (hONM_le_OCM.trans hOCM_le_OM)

/-- BG (8.6), Fitting-prime support form: if `A = C_F(M)(A0)` lies in `H`, then
`π(F(H)) ⊆ π(A)` in the non-p-group case. -/
theorem primesOf_fittingInG_subset_primesOf_cFittingInG_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hAH : cFittingInG M A0 ≤ H) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG H) ⊆
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) := by
  intro q hqF
  have hqF_mem : q ∈ (Nat.card ↥(fittingInG H)).primeFactors := by
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hqF
  have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqF_mem⟩
  by_contra hqA
  have hqcomp : q ∈ (OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0))ᶜ := hqA
  have hObot : opiCoreInG ({q} : Set ℕ) H = ⊥ :=
    opiCoreInG_singleton_eq_bot_of_cFittingInG_le_of_not_pGroup
      hG hM hA0 hm hFnp hA hqcomp hAH
  exact opiCoreInG_singleton_ne_bot_of_mem_primeFactors_fittingInG hqF_mem hObot

/-- BG (8.6), pi-subgroup form: if `A = C_F(M)(A0)` lies in `H`, then `F(H)`
is a `π(F(M))`-subgroup in the non-p-group case. -/
theorem fittingInG_isPiSubgroup_primesOf_fittingInG_of_cFittingInG_le_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hA : OddOrder.BG.Ch2.S07.Hypothesis71 (cFittingInG M A0))
    (hAH : cFittingInG M A0 ≤ H) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (fittingInG H) := by
  have hA0F : A0 ≤ fittingInG M := isMaxElemAbelianIn_le hA0
  have hPrimes :
      OddOrder.BG.Ch2.S07.primesOf (cFittingInG M A0) =
        OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [cFittingInG]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  rw [← hPrimes]
  exact primesOf_fittingInG_subset_primesOf_cFittingInG_of_cFittingInG_le_of_not_pGroup
    hG hM hA0 hm hFnp hA hAH

/-- BG (8.6), pi-subgroup form with Hypothesis 7.1 supplied by BG (8.5). -/
theorem fittingInG_isPiSubgroup_primesOf_fittingInG_of_not_pGroup
    [Finite G] (hG : IsMinimalSimpleOdd G) {p : ℕ} [Fact p.Prime]
    {M A0 H : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hA0 : isMaxElemAbelianIn p A0 (fittingInG M))
    (hm : 3 ≤ rank ↥A0)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M))
    (hAH : cFittingInG M A0 ≤ H) :
    Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))
      (fittingInG H) :=
  fittingInG_isPiSubgroup_primesOf_fittingInG_of_cFittingInG_le_of_not_pGroup
    hG hM hA0 hm hFnp
    (hypothesis71_cFittingInG_of_not_pGroup hG hM hp hA0 hFnp) hAH

/-- **BG Theorem 8.1(a)** (mmd L2319-2321): `M ∈ ℳ`, `p ∈ π(F(M))`, `A₀ ∈ ℰ_p^*(F(M))`,
`m(A₀) ≥ 3`。`F(M)` が `p`-群でなければ `C_{F(M)}(A₀) ∈ 𝒰`。 -/
theorem cFitting_isUniquelyMaximal_of_not_pGroup [Finite G] (hG : IsMinimalSimpleOdd G)
    {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    {A₀ : Subgroup G} (hA₀ : isMaxElemAbelianIn p A₀ (fittingInG M))
    (hm : 3 ≤ rank ↥A₀)
    (hFnp : ¬ IsPGroup p ↥(fittingInG M)) :
    IsUniquelyMaximal (Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M) := by
  let A : Subgroup G := Subgroup.centralizer (A₀ : Set G) ⊓ fittingInG M
  change IsUniquelyMaximal A
  have hA0F : A₀ ≤ fittingInG M := isMaxElemAbelianIn_le hA₀
  have hA_le_M : A ≤ M := by
    dsimp [A]
    exact inf_le_right.trans (fittingInG_le M)
  have hA_proper : A < ⊤ := by
    dsimp [A]
    exact cFitting_lt_top_of_mem_maximal hM
  have hA_ne : A ≠ ⊥ := by
    dsimp [A]
    exact cFitting_ne_bot_of_isMaxElemAbelianIn hp hA₀
  have hPrimesA :
      OddOrder.BG.Ch2.S07.primesOf A = OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    dsimp [A]
    exact primesOf_cFitting_eq_primesOf_fittingInG hA0F
  have hCentralizer_le_M : Subgroup.centralizer (A : Set G) ≤ M := by
    dsimp [A]
    exact centralizer_cFitting_le_maximal_of_not_isPGroup hG hM hA0F hFnp
  have hCpi : Subgroup.IsPiSubgroup (OddOrder.BG.Ch2.S07.primesOf A)
      (Subgroup.centralizer (A : Set G)) := by
    dsimp [A]
    exact centralizer_cFitting_isPiSubgroup_of_not_pGroup hG hM hA₀ hFnp
  have hCenterRank : 3 ≤ rank ↥(Subgroup.center ↥A) := by
    dsimp [A]
    exact three_le_rank_center_cFitting_of_isMaxElemAbelianIn hA₀ hm
  refine IsUniquelyMaximal.of_unique_maximal hA_proper hM hA_le_M ?_
  intro H hH hAH
  have hHco : IsCoatom H := hH
  have hH_mem : H ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hH
  have hAH_cFitting : cFittingInG M A₀ ≤ H := by
    dsimp [A] at hAH
    exact hAH
  have hFittingH_pi : Subgroup.IsPiSubgroup
      (OddOrder.BG.Ch2.S07.primesOf (fittingInG M)) (fittingInG H) :=
    fittingInG_isPiSubgroup_primesOf_fittingInG_of_not_pGroup
      hG hM hp hA₀ hm hFnp hAH_cFitting
  have hSigma_subset_pi : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) ⊆
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
    intro q hq
    exact hFittingH_pi q (by simpa [OddOrder.BG.Ch2.S07.primesOf] using hq)
  have hH_solvable : Group.IsSolvable ↥H := hG.isSolvable_of_lt_top H hHco.lt_top
  have hO_sigma_compl_bot :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG H))ᶜ H = ⊥ :=
    opiCoreInG_primesOf_fittingInG_compl_eq_bot
  have hO_pi_compl_le_sigma :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ H ≤
        opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG H))ᶜ H := by
    rw [opiCoreInG, opiCoreInG]
    refine Subgroup.map_mono (Ch03.oPiCore_mono ?_ ↥H)
    intro q hq_not_pi hq_sigma
    exact hq_not_pi (hSigma_subset_pi hq_sigma)
  have hO_pi_compl_bot :
      opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ H = ⊥ := by
    exact le_bot_iff.mp (by rw [← hO_sigma_compl_bot]; exact hO_pi_compl_le_sigma)
  have hPi_subset_sigma : OddOrder.BG.Ch2.S07.primesOf (fittingInG M) ⊆
      OddOrder.BG.Ch2.S07.primesOf (fittingInG H) :=
    primesOf_fittingInG_subset_of_opiCoreInG_compl_eq_bot
      hG hM hA₀ hH_solvable hAH_cFitting hSigma_subset_pi hO_sigma_compl_bot
  have hSigma_eq_pi : OddOrder.BG.Ch2.S07.primesOf (fittingInG H) =
      OddOrder.BG.Ch2.S07.primesOf (fittingInG M) :=
    Set.Subset.antisymm hSigma_subset_pi hPi_subset_sigma
  have hFittingH_le_M : fittingInG H ≤ M := by
    have hFH_nilp : Group.IsNilpotent ↥(fittingInG H) := fittingInG_isNilpotent H
    refine le_of_sylow_le_of_nilpotent hFH_nilp ?_
    intro r
    have : Fact (r : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors r.2⟩
    let S : Subgroup G := ((default : Sylow (r : ℕ) ↥(fittingInG H)) :
      Subgroup ↥(fittingInG H)).map (fittingInG H).subtype
    have hS_le_core : S ≤ opiCoreInG ({(r : ℕ)} : Set ℕ) (fittingInG H) := by
      dsimp [S]
      exact le_opiCoreInG_singleton_of_isPGroup_of_le_nilpotent
        hFH_nilp (Subgroup.map_subtype_le _)
        ((default : Sylow (r : ℕ) ↥(fittingInG H)).isPGroup'.map
          (fittingInG H).subtype)
    have hrFH : (r : ℕ) ∈ (Nat.card ↥(fittingInG H)).primeFactors := r.2
    have hrFM_primes : (r : ℕ) ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG M) := by
      rw [← hSigma_eq_pi]
      exact hrFH
    have hrFM : (r : ℕ) ∈ (Nat.card ↥(fittingInG M)).primeFactors := hrFM_primes
    exact hS_le_core.trans
      (opiCoreInG_fittingInG_singleton_le_maximal_of_cFittingInG_le_of_not_pGroup
        hG hM hp hA₀ hFnp hH_solvable hAH_cFitting hrFM)
  have hOpComplH_le_M : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ M :=
    opiCoreInG_singleton_compl_le_maximal_of_cFittingInG_le_of_primes_eq
      hG hM hp hA₀ hH_solvable hAH_cFitting hSigma_eq_pi
  have hpFittingH : p ∈ (Nat.card ↥(fittingInG H)).primeFactors := by
    have hpFH_primes : p ∈ OddOrder.BG.Ch2.S07.primesOf (fittingInG H) := by
      rw [hSigma_eq_pi]
      exact hp
    simpa [OddOrder.BG.Ch2.S07.primesOf] using hpFH_primes
  have hOpComplH_le_OpComplM : opiCoreInG ({p} : Set ℕ)ᶜ H ≤
      opiCoreInG ({p} : Set ℕ)ᶜ M :=
    opiCoreInG_singleton_compl_le_opiCoreInG_singleton_compl_of_fittingInG_le_maximal
      hG hM hH_mem hpFittingH hFittingH_le_M hOpComplH_le_M
  have hDpH_le_M : opiCoreInG ({p} : Set ℕ) (fittingInG H) ≤ M :=
    (opiCoreInG_le ({p} : Set ℕ) (fittingInG H)).trans hFittingH_le_M
  have hOpComplM_le_H : opiCoreInG ({p} : Set ℕ)ᶜ M ≤ H :=
    opiCoreInG_singleton_compl_maximal_le_of_fittingInG_singleton_le_maximal
      hG hM hH_mem hp hpFittingH hA₀ hH_solvable hAH_cFitting hDpH_le_M
  have hOpComplM_le_OpComplH : opiCoreInG ({p} : Set ℕ)ᶜ M ≤
      opiCoreInG ({p} : Set ℕ)ᶜ H :=
    opiCoreInG_singleton_compl_maximal_le_opiCoreInG_singleton_compl_of_le_maximal
      hG hM hp hA₀ hH_solvable hAH_cFitting hOpComplM_le_H
  have hOpCompl_eq : opiCoreInG ({p} : Set ℕ)ᶜ H =
      opiCoreInG ({p} : Set ℕ)ᶜ M :=
    le_antisymm hOpComplH_le_OpComplM hOpComplM_le_OpComplH
  obtain ⟨r, hrFM, hrp⟩ :=
    exists_primeFactor_ne_of_mem_primeFactor_not_isPGroup
      (H := ↥(fittingInG M)) hp hFnp p
  have hRprime : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hrFM⟩
  have hBr_ne : centerFittingOpCoreInG r M ≠ ⊥ :=
    centerFittingOpCoreInG_ne_bot_of_mem_primeFactors_fittingInG hrFM
  have hBr_le_OpComplM : centerFittingOpCoreInG r M ≤
      opiCoreInG ({p} : Set ℕ)ᶜ M :=
    centerFittingOpCoreInG_le_opiCoreInG_singleton_compl_of_ne
      hG hM hA₀ (hG.isSolvable_of_mem_maximalSubgroups hM) (by
        dsimp [cFittingInG]
        exact inf_le_right.trans (fittingInG_le M)) hp hrFM (fun hpr => hrp hpr.symm)
  have hOpComplM_ne : opiCoreInG ({p} : Set ℕ)ᶜ M ≠ ⊥ := by
    intro hbot
    exact hBr_ne (le_bot_iff.mp (by
      rw [← hbot]
      exact hBr_le_OpComplM))
  have hOpComplH_ne : opiCoreInG ({p} : Set ℕ)ᶜ H ≠ ⊥ := by
    rw [hOpCompl_eq]
    exact hOpComplM_ne
  have hOpComplH_H : opiCoreInG ({p} : Set ℕ)ᶜ H ≤ H :=
    opiCoreInG_le ({p} : Set ℕ)ᶜ H
  have hOpComplH_norm_H : ((opiCoreInG ({p} : Set ℕ)ᶜ H).subgroupOf H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOpComplH_H]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ H
  have hNormalizer_OpComplH_eq_H :
      Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ H : Set G) = H :=
    normalizer_eq_of_normal_of_mem_maximal hG hH_mem hOpComplH_norm_H
      hOpComplH_ne hOpComplH_H
  have hOpComplM_M : opiCoreInG ({p} : Set ℕ)ᶜ M ≤ M :=
    opiCoreInG_le ({p} : Set ℕ)ᶜ M
  have hOpComplM_norm_M : ((opiCoreInG ({p} : Set ℕ)ᶜ M).subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hOpComplM_M]
    exact le_normalizer_opiCoreInG ({p} : Set ℕ)ᶜ M
  have hNormalizer_OpComplM_eq_M :
      Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ M : Set G) = M :=
    normalizer_eq_of_normal_of_mem_maximal hG hM hOpComplM_norm_M
      hOpComplM_ne hOpComplM_M
  calc
    H = Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ H : Set G) :=
      hNormalizer_OpComplH_eq_H.symm
    _ = Subgroup.normalizer (opiCoreInG ({p} : Set ℕ)ᶜ M : Set G) := by
      rw [hOpCompl_eq]
    _ = M := hNormalizer_OpComplM_eq_M

/-- If `F(M)` is a nontrivial `p`-group, then its prime support is exactly `{p}`. -/
theorem primesOf_fittingInG_eq_singleton_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    OddOrder.BG.Ch2.S07.primesOf (fittingInG M) = ({p} : Set ℕ) := by
  have hF_ne_bot : fittingInG M ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card ↥(fittingInG M) = 1 := Subgroup.card_eq_one.mpr hbot
    rw [hcard, Nat.primeFactors_one] at hp
    exact Finset.notMem_empty p hp
  obtain ⟨n, hn⟩ := hFp.exists_card_eq
  have hn0 : n ≠ 0 := by
    intro hn_zero
    apply hF_ne_bot
    rw [Subgroup.eq_bot_iff_card, hn, hn_zero, pow_zero]
  ext q
  simp only [OddOrder.BG.Ch2.S07.primesOf, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  rw [hn, Nat.primeFactors_prime_pow hn0 (Fact.out : p.Prime), Finset.mem_singleton]

/-- BG 8.1(b), first p-group bridge: if `F(M)` is a `p`-group, then
`O_{p'}(M)=1`. This is the formal version of
`F(O_{p'}(M)) ≤ O_{p'}(F(M)) = 1`. -/
theorem opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} [Group.IsSolvable ↥M]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    opiCoreInG ({p} : Set ℕ)ᶜ M = ⊥ := by
  have hπ : OddOrder.BG.Ch2.S07.primesOf (fittingInG M) = ({p} : Set ℕ) :=
    primesOf_fittingInG_eq_singleton_of_isPGroup hp hFp
  have hcore : opiCoreInG (OddOrder.BG.Ch2.S07.primesOf (fittingInG M))ᶜ M = ⊥ :=
    opiCoreInG_primesOf_fittingInG_compl_eq_bot
  simpa [hπ] using hcore

/-- BG 8.1(b), second p-group bridge: if `F(M)` is a `p`-group, then
`F(M)=O_p(M)` in the ambient group. -/
theorem fittingInG_eq_opiCoreInG_singleton_of_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G}
    (hFp : IsPGroup p ↥(fittingInG M)) :
    fittingInG M = opiCoreInG ({p} : Set ℕ) M := by
  apply le_antisymm
  · have hFpi : Subgroup.IsPiSubgroup ({p} : Set ℕ) (fittingInG M) :=
      OddOrder.GroupTheory.isPiSubgroup_singleton_of_isPGroup hFp
    exact le_opiCoreInG_of_normal_of_isPiSubgroup (fittingInG_le M)
      (fittingInG_subgroupOf_normal M) hFpi
  · exact opiCoreInG_singleton_le_fittingInG M

/-- If the `p'`-core is trivial, the `O_{p',p}` layer collapses to the `p`-core. -/
theorem oPiPrimePiCore_singleton_eq_oPiCore_singleton_of_compl_bot
    {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (h : Ch03.oPiCore (({p} : Set ℕ)ᶜ) X = ⊥) :
    Ch03.oPiPrimePiCore ({p} : Set ℕ) X = Ch03.oPiCore ({p} : Set ℕ) X := by
  have key : ∀ (N : Subgroup X) [N.Normal], N = ⊥ →
      Subgroup.comap (QuotientGroup.mk' N) (Ch03.oPiCore ({p} : Set ℕ) (X ⧸ N))
        = Ch03.oPiCore ({p} : Set ℕ) X := by
    intro N _ hN
    subst hN
    rw [show (QuotientGroup.mk' (⊥ : Subgroup X))
        = (QuotientGroup.quotientBot (G := X)).symm.toMonoidHom from rfl]
    rw [Subgroup.comap_equiv_eq_map_symm']
    simp only [MulEquiv.symm_symm]
    exact Ch03.oPiCore.map_eq_of_mulEquiv ({p} : Set ℕ) (QuotientGroup.quotientBot (G := X))
  -- `oPiPrimePiCore {p} X` unfolds definitionally to the `comap` at `{q | q ∉ {p}} = {p}ᶜ`.
  exact key _ h

/-- BG 8.1(b), third p-group bridge: when `F(M)` is a `p`-group, `O_{p',p}(M)`,
viewed in `G`, lies in `F(M)`. -/
theorem oPiPrimePiCore_singleton_map_le_fittingInG_of_fittingInG_isPGroup [Finite G]
    {p : ℕ} [Fact p.Prime] {M : Subgroup G} [Group.IsSolvable ↥M]
    (hp : p ∈ (Nat.card ↥(fittingInG M)).primeFactors)
    (hFp : IsPGroup p ↥(fittingInG M)) :
    (Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M).map M.subtype ≤ fittingInG M := by
  have hmap_bot : (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M).map M.subtype = ⊥ := by
    simpa [opiCoreInG] using
      (opiCoreInG_singleton_compl_eq_bot_of_fittingInG_isPGroup (M := M) hp hFp)
  have hbot : Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (Ch03.oPiCore (({p} : Set ℕ)ᶜ) ↥M) M.subtype_injective).mp hmap_bot
  have hcollapse :
      Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M = Ch03.oPiCore ({p} : Set ℕ) ↥M :=
    oPiPrimePiCore_singleton_eq_oPiCore_singleton_of_compl_bot hbot
  calc
    (Ch03.oPiPrimePiCore ({p} : Set ℕ) ↥M).map M.subtype
        = (Ch03.oPiCore ({p} : Set ℕ) ↥M).map M.subtype := by rw [hcollapse]
    _ = opiCoreInG ({p} : Set ℕ) M := rfl
    _ ≤ fittingInG M := opiCoreInG_singleton_le_fittingInG M

end OddOrder.BG.Ch2.S08


