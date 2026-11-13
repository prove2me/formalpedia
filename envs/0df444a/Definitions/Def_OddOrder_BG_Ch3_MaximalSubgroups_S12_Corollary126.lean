-- Prove2me | Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary126
-- name    : OddOrder_BG_Ch3_MaximalSubgroups_S12_Corollary126
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:29:40.692013+00:00
-- url     : https://prove2.me/theorems/07c9fc80-a844-42e3-a3ff-713fde0309a4
-- title:
--   BG §12: Corollary 12.6, $A\trianglelefteq E$ and centralizer control
-- statement:
--   Formalizes Corollary 12.6 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §12, a corollary of Theorem 12.5: for $p\in\tau_2(M)$ and $A\in\mathcal{E}_p^2(E)$ it shows that $A$ is normal in $E$ and controls centralizers. Parts are proved standalone, e.g. the Dedekind equality $(M_\sigma\sqcup A)\sqcap E=A$, and are assembled in `elemAb_normal_in_E_of_tau2`.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 8 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary126.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch3_MaximalSubgroups/S12_Corollary126.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch3_MaximalSubgroups_S12_Theorem125

namespace OddOrder.BG.Ch3.S12

open OddOrder.GroupTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Dedekind identity for the §12 setup**: `(M_σ ⊔ A) ⊓ E = A` for `A ≤ E`
(decompose in `↥M` along the normal `M_σ` and use `M_σ ⊓ E = 1`). -/
theorem sup_Msigma_inf_E_eq_of_le [Finite G]
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {A : Subgroup G} (hAE : A ≤ E) :
    (S10.Msigma M ⊔ A) ⊓ E = A := by
  refine le_antisymm ?_ (le_inf le_sup_right hAE)
  rintro x ⟨hxsup, hxE⟩
  have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
  have hAM : A ≤ M := hAE.trans h.E_le
  have hxM : x ∈ M := h.E_le hxE
  have : ((S10.Msigma M).subgroupOf M).Normal := by
    rw [S10.Msigma_subgroupOf]; infer_instance
  have hsub : (⟨x, hxM⟩ : ↥M) ∈ (S10.Msigma M).subgroupOf M ⊔ A.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup hMσM hAM]
    exact Subgroup.mem_subgroupOf.mpr hxsup
  have hsub' : (⟨x, hxM⟩ : ↥M) ∈
      ((S10.Msigma M).subgroupOf M : Set ↥M) * (A.subgroupOf M : Set ↥M) := by
    rw [← Subgroup.normal_mul]
    exact hsub
  obtain ⟨s, hs, a, ha, hsa⟩ := hsub'
  have hseq : (s : ↥M) = ⟨x, hxM⟩ * a⁻¹ := by rw [← hsa]; group
  have hsE : (s : G) ∈ E := by
    have hcoe : (s : G) = x * ((a : ↥M) : G)⁻¹ := by rw [hseq]; rfl
    rw [hcoe]
    exact E.mul_mem hxE (E.inv_mem (hAE (Subgroup.mem_subgroupOf.mp ha)))
  have hsbot : (s : G) ∈ S10.Msigma M ⊓ E := ⟨Subgroup.mem_subgroupOf.mp hs, hsE⟩
  rw [h.E_compl_inf, Subgroup.mem_bot] at hsbot
  have hxa : (⟨x, hxM⟩ : ↥M) = a := by
    rw [← hsa, show s = 1 from Subtype.ext hsbot]
    exact one_mul a
  have hxa' : x = ((a : ↥M) : G) := congrArg Subtype.val hxa
  rw [hxa']
  exact Subgroup.mem_subgroupOf.mp ha

/-- **BG Corollary 12.6(a), first part** (mmd L3192): `E ≤ N_G(A)` — from
`M_σ A ⊴ M` (Theorem 12.5(c)) and the Dedekind identity. -/
theorem E_le_normalizer_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    E ≤ Subgroup.normalizer (A : Set G) := by
  have hAM : A ≤ M := hAE.trans h.E_le
  have h125c := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.1
  have hinf := sup_Msigma_inf_E_eq_of_le h hAE
  have key : ∀ y ∈ E, ∀ g ∈ A, y * g * y⁻¹ ∈ A := by
    intro y hy g hg
    rw [← hinf]
    refine ⟨?_, E.mul_mem (E.mul_mem hy (hAE hg)) (E.inv_mem hy)⟩
    exact (Subgroup.mem_normalizer_iff.mp (h125c (h.E_le hy)) g).mp
      (Subgroup.mem_sup_right hg)
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx => key e he x hx
  · intro hx
    have h1 := key e⁻¹ (E.inv_mem he) _ hx
    simpa [mul_assoc] using h1

/-- **BG Corollary 12.6(a), second part** (mmd L3192-3194): every line
`X ∈ ℰ_p¹(E)` lies in `A` (i.e. `ℰ_p¹(E) = ℰ¹(A)`): `X ⊔ A` is a `p`-subgroup of `M`,
hence lies in a Sylow `p`-subgroup `P ⊇ A`, and `Ω₁(P) = A` (`omega1_eq_of_tau2`)
absorbs the exponent-`p` subgroup `X`. -/
theorem line_le_of_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXE : X ≤ E) :
    X ≤ A := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- `X ⊔ A` is a `p`-group: `A.subgroupOf E` is normal in `↥E` by part 1.
  have : (A.subgroupOf E).Normal := by
    constructor
    intro a ha g
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp
      (E_le_normalizer_of_tau2 hG h hp hA hAE g.2) (a : G)).mp ha
  have hsup_pg : IsPGroup p ↥(X.subgroupOf E ⊔ A.subgroupOf E : Subgroup ↥E) :=
    IsPGroup.to_sup_of_normal_right hX.1.isPGroup.comap_subtype
      hA.1.isPGroup.comap_subtype
  have hXA_pg : IsPGroup p ↥(X ⊔ A : Subgroup G) := by
    have hmap : (X.subgroupOf E ⊔ A.subgroupOf E).map E.subtype = X ⊔ A := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXE,
        Subgroup.map_subgroupOf_eq_of_le hAE]
    rw [← hmap]
    exact hsup_pg.map _
  -- a Sylow `p`-subgroup of `M` containing `X ⊔ A`.
  have hXAM : X ⊔ A ≤ M := sup_le (hXE.trans h.E_le) hAM
  obtain ⟨PM, hPM⟩ := hXA_pg.comap_subtype.exists_le_sylow (G := M)
  set P : Subgroup G := (PM : Subgroup ↥M).map M.subtype with hPdef
  have hXAP : X ⊔ A ≤ P := by
    rw [hPdef, ← Subgroup.map_subgroupOf_eq_of_le hXAM]
    exact Subgroup.map_mono hPM
  have hP_le : P ≤ M := Subgroup.map_subtype_le _
  have hPpg : IsPGroup p ↥P := by rw [hPdef]; exact PM.isPGroup'.map _
  have hPsyl : ∀ R : Subgroup G, P ≤ R → R ≤ M → IsPGroup p ↥R → R = P := by
    intro R hPR hRM hRpg
    have hle : (PM : Subgroup ↥M) ≤ R.subgroupOf M := by
      refine le_trans (fun y hy => Subgroup.mem_subgroupOf.mpr ?_)
        (Subgroup.comap_mono hPR)
      rw [hPdef]
      exact Subgroup.mem_map_of_mem _ hy
    have heq : R.subgroupOf M = PM := PM.3 hRpg.comap_subtype hle
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, heq, hPdef]
  have homega := (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM hPpg
    (le_sup_right.trans hXAP) hP_le hPsyl).1
  rw [homega]
  intro x hx
  have hxP : x ∈ P := hXAP (Subgroup.mem_sup_left hx)
  have hxp : x ^ p = 1 := by
    simpa using congrArg Subtype.val (hX.1.pow_eq_one ⟨x, hx⟩)
  refine ⟨⟨x, hxP⟩, ?_, rfl⟩
  apply Subgroup.subset_closure
  change (⟨x, hxP⟩ : ↥P) ^ (p ^ 1) = 1
  rw [pow_one]
  exact Subtype.ext (by simpa using hxp)

/-- **BG Corollary 12.6(b)** (mmd L3194-3196): `C_G(A) ≤ E`, `N_M(A) = E`, and
`N_G(A) ⊄ M`. The Dedekind decomposition `N_M(A) = N_{M_σ}(A)·E` reduces to
`N_{M_σ}(A) = C_{M_σ}(A) = 1` (commutators land in `A ⊓ M_σ = 1`, then
Theorem 12.5(d)); `C_G(A) ≤ M` is Proposition 12.4(a); and `N_G(P) ≤ N_G(Ω₁(P)) =
N_G(A)` with `N_G(P) ⊄ M` from Theorem 12.5(b). -/
theorem centralizer_le_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃)
    {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M) {A : Subgroup G}
    (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    Subgroup.centralizer (A : Set G) ≤ E ∧
    M ⊓ Subgroup.normalizer (A : Set G) = E ∧
    ¬ (Subgroup.normalizer (A : Set G) ≤ M) := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have h125 := Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM
  have hd := h125.2.2.2.1
  have hNMA : M ⊓ Subgroup.normalizer (A : Set G) = E := by
    refine le_antisymm ?_
      (le_inf h.E_le (E_le_normalizer_of_tau2 hG h hp hA hAE))
    rintro x ⟨hxM, hxN⟩
    have : ((S10.Msigma M).subgroupOf M).Normal := by
      rw [S10.Msigma_subgroupOf]; infer_instance
    have hMσM : S10.Msigma M ≤ M := S10.Msigma_le M
    have hsub : (⟨x, hxM⟩ : ↥M) ∈ (S10.Msigma M).subgroupOf M ⊔ E.subgroupOf M := by
      rw [← Subgroup.subgroupOf_sup hMσM h.E_le, h.E_compl_sup]
      exact Subgroup.mem_subgroupOf.mpr hxM
    have hsub' : (⟨x, hxM⟩ : ↥M) ∈
        ((S10.Msigma M).subgroupOf M : Set ↥M) * (E.subgroupOf M : Set ↥M) := by
      rw [← Subgroup.normal_mul]
      exact hsub
    obtain ⟨s, hs, e, he, hse⟩ := hsub'
    have heE : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp he
    have heN : (e : G) ∈ Subgroup.normalizer (A : Set G) :=
      E_le_normalizer_of_tau2 hG h hp hA hAE heE
    have hseq : (s : G) = x * ((e : ↥M) : G)⁻¹ := by
      have h1 : (s : ↥M) = ⟨x, hxM⟩ * e⁻¹ := by rw [← hse]; group
      calc (s : G) = ((⟨x, hxM⟩ * e⁻¹ : ↥M) : G) := congrArg Subtype.val h1
        _ = x * ((e : ↥M) : G)⁻¹ := rfl
    have hsN : (s : G) ∈ Subgroup.normalizer (A : Set G) := by
      rw [hseq]
      exact Subgroup.mul_mem _ hxN (Subgroup.inv_mem _ heN)
    have hsMσ : (s : G) ∈ S10.Msigma M := Subgroup.mem_subgroupOf.mp hs
    -- `s` centralizes `A`: commutators land in `A ⊓ M_σ = ⊥`.
    have hAMσ_bot : A ⊓ S10.Msigma M = ⊥ := by
      rw [← le_bot_iff, ← h.E_compl_inf]
      exact le_inf inf_le_right (inf_le_left.trans hAE)
    have hsC : (s : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haM : a ∈ M := hAM ha
      have h1 : a * (s : G) * a⁻¹ * (s : G)⁻¹ ∈ S10.Msigma M := by
        have h2 : a * (s : G) * a⁻¹ ∈ S10.Msigma M :=
          (Subgroup.mem_normalizer_iff.mp ((le_normalizer_opiCoreInG _ _) haM) _).mp hsMσ
        exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hsMσ)
      have h2 : a * (s : G) * a⁻¹ * (s : G)⁻¹ ∈ A := by
        have h3 : (s : G) * a⁻¹ * (s : G)⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp hsN a⁻¹).mp (A.inv_mem ha)
        have h4 : a * ((s : G) * a⁻¹ * (s : G)⁻¹) ∈ A := A.mul_mem ha h3
        simpa [mul_assoc] using h4
      have h5 : a * (s : G) * a⁻¹ * (s : G)⁻¹ ∈ A ⊓ S10.Msigma M := ⟨h2, h1⟩
      rw [hAMσ_bot, Subgroup.mem_bot] at h5
      calc a * (s : G) = (a * (s : G) * a⁻¹ * (s : G)⁻¹) * ((s : G) * a) := by group
        _ = (s : G) * a := by rw [h5, one_mul]
    have hsbot : (s : G) ∈ S10.Msigma M ⊓ Subgroup.centralizer (A : Set G) :=
      ⟨hsMσ, hsC⟩
    rw [hd, Subgroup.mem_bot] at hsbot
    have hxe : (⟨x, hxM⟩ : ↥M) = e := by
      rw [← hse, show s = 1 from Subtype.ext hsbot]
      exact one_mul e
    have hxe' : x = ((e : ↥M) : G) := congrArg Subtype.val hxe
    rw [hxe']
    exact heE
  refine ⟨?_, hNMA, ?_⟩
  · have hCM : Subgroup.centralizer (A : Set G) ≤ M :=
      centralizer_le_of_elemAb_rank_two hG h.mem_maximal hA hAM
    rw [← hNMA]
    exact le_inf hCM (Subgroup.centralizer_le_normalizer _)
  · obtain ⟨P, hP_le, hPpg, hAP, hPsyl', hPnot⟩ := h125.2.1.2
    have homega := (omega1_eq_of_tau2 hG h.mem_maximal hp hA hAM hPpg hAP hP_le
      (fun R hPR hRM hRpg => (hPsyl' R hRM hRpg hPR).symm)).1
    intro hcon
    apply hPnot
    have hNP_NA : Subgroup.normalizer (P : Set G) ≤
        Subgroup.normalizer (A : Set G) := by
      have h1 := OddOrder.BG.AppB.normalizer_le_normalizer_map_of_characteristic
        (K := P) (W := Omega ↥P p 1)
      rwa [← homega] at h1
    exact hNP_NA.trans hcon

/-- The centralizer of `⟨x⟩` agrees with the centralizer of `{x}`. -/
theorem centralizer_zpowers_eq_singleton (x : G) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup G) : Set G)
      = Subgroup.centralizer ({x} : Set G) := by
  apply le_antisymm
  · exact Subgroup.centralizer_le (by
      rw [Set.singleton_subset_iff]
      exact SetLike.mem_coe.mpr (Subgroup.mem_zpowers x))
  · intro g hg
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hy
    obtain ⟨n, rfl⟩ := hy
    exact ((Commute.zpow_left (hg x (Set.mem_singleton x)) n) : _)

/-- **BG Corollary 12.6(c)** (mmd L3194): for a line `X ∈ ℰ¹(A)` with
`C_{M_σ}(X) ≠ 1`, `ℳ(C_G(X)) = {M}` (any other maximal over `C_G(X)` contains `A`,
contradicting Theorem 12.5(e)). -/
theorem maximalContaining_centralizer_line_eq_singleton [Finite G]
    (hG : IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {X : Subgroup G} (hX : X ∈ elemAbelianOfRank G p 1) (hXA : X ≤ A)
    (hCne : S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥) :
    maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have hAC : A ≤ Subgroup.centralizer (X : Set G) :=
    (le_centralizer_self_of_isElementaryAbelian hA.1).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXA))
  have h125e := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.2.2.1
  have hall : ∀ Mstar ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)),
      Mstar = M := by
    intro Mstar hMst
    by_contra hne
    obtain ⟨hco, hle⟩ := mem_maximalSubgroupsContaining.mp hMst
    have hbot := h125e Mstar
      (mem_maximalSubgroupsContaining.mpr ⟨hco, hAC.trans hle⟩) hne
    apply hCne
    rw [← le_bot_iff, ← hbot]
    exact le_inf inf_le_left (inf_le_right.trans hle)
  have hXne := ne_bot_of_mem_elemAbelianOfRank_one hX
  have hClt : Subgroup.centralizer (X : Set G) < ⊤ :=
    lt_of_le_of_lt (Subgroup.centralizer_le_normalizer _)
      (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal
        (hXA.trans (hAE.trans h.E_le)) hXne)
  obtain ⟨Mst, hco, hle⟩ := (eq_top_or_exists_le_coatom _).resolve_left hClt.ne
  have hmem : Mst ∈ maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨hco, hle⟩
  exact Set.eq_singleton_iff_unique_mem.mpr ⟨(hall Mst hmem) ▸ hmem, hall⟩

/-- **Corollary 12.6(d)(e), common core**: if `x ∈ M`, `x ≠ 1`, every prime of
`orderOf x` lies in `τ₁(M) ∪ τ₃(M)`, and `A ≤ C_G(x)`, then `C_{M_σ}(x) = 1`.
(Pass to a prime-order power `y` of `x`; Lemma 12.2(b) makes every maximal over
`N_G(⟨y⟩)` non-conjugate to `M`, hence `≠ M` and a member of `ℳ(A)`, so Theorem
12.5(e) kills `M_σ ∩ M* ⊇ C_{M_σ}(x)`.) -/
theorem Msigma_inf_centralizer_eq_bot_of_le_centralizer [Finite G]
    (hG : IsMinimalSimpleOdd G) {M E E₁ E₂ E₃ : Subgroup G}
    (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime] (hp : p ∈ tau2 M)
    {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E)
    {x : G} (hxM : x ∈ M) (hx1 : x ≠ 1)
    (hr : ∀ r ∈ (orderOf x).primeFactors, r ∈ tau1 M ∪ tau3 M)
    (hAC : A ≤ Subgroup.centralizer ({x} : Set G)) :
    S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  -- pass to the prime-order power `y` of `x`.
  have hordne : orderOf x ≠ 1 := fun h1 => hx1 (orderOf_eq_one_iff.mp h1)
  set r : ℕ := (orderOf x).minFac with hrdef
  have hr_prime : r.Prime := Nat.minFac_prime hordne
  have : Fact r.Prime := ⟨hr_prime⟩
  have hr_dvd : r ∣ orderOf x := Nat.minFac_dvd _
  set y : G := x ^ (orderOf x / r) with hydef
  have hord_pos : 0 < orderOf x := by
    have := orderOf_pos x
    exact this
  have hordy : orderOf y = r := by
    rw [hydef, orderOf_pow]
    rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd hr_dvd)]
    exact Nat.div_div_self hr_dvd hord_pos.ne'
  have hy1 : y ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hordy
    exact hr_prime.one_lt.ne hordy
  have hrτ : r ∈ tau1 M ∪ tau3 M := hr r
    (Nat.mem_primeFactors.mpr ⟨hr_prime, hr_dvd, hord_pos.ne'⟩)
  set X : Subgroup G := Subgroup.zpowers y with hXdef
  have hX_card : Nat.card ↥X = r := by rw [hXdef, Nat.card_zpowers, hordy]
  have hX_ne : X ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥X = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hX_card] at h1
    exact hr_prime.one_lt.ne' h1
  have hX_pg : IsPGroup r ↥X := IsPGroup.of_card (by rw [hX_card, pow_one])
  have hXM : X ≤ M := by
    rw [hXdef, Subgroup.zpowers_le]
    exact M.pow_mem hxM _
  -- `A` centralizes `y`, hence `X`.
  have hAy : A ≤ Subgroup.centralizer (X : Set G) := by
    rw [hXdef, centralizer_zpowers_eq_singleton]
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have hcomm : Commute x a :=
      Subgroup.mem_centralizer_iff.mp (hAC ha) x (Set.mem_singleton x)
    exact ((hcomm.pow_left _) : _)
  -- a maximal subgroup over `N_G(X)` is non-conjugate to `M`, hence `≠ M`.
  obtain ⟨Mst, hMst_co, hMst_le⟩ :=
    (eq_top_or_exists_le_coatom (Subgroup.normalizer (X : Set G))).resolve_left
      (normalizer_lt_top_of_le_of_ne_bot hG h.mem_maximal hXM hX_ne).ne
  have hnc := not_conj_of_mem_tau1_union_tau3_of_normalizer_le hG h.mem_maximal hrτ
    hXM hX_ne hX_pg hMst_le
  have hMne : Mst ≠ M := by
    rintro rfl
    exact hnc ⟨1, by rw [map_one, one_smul]⟩
  -- `M* ∈ ℳ(A)`, so Theorem 12.5(e) applies.
  have h125e := (Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM).2.2.2.2.1
  have hbot := h125e Mst
    (mem_maximalSubgroupsContaining.mpr
      ⟨hMst_co, (hAy.trans (Subgroup.centralizer_le_normalizer _)).trans hMst_le⟩) hMne
  rw [← le_bot_iff, ← hbot]
  refine le_inf inf_le_left (inf_le_right.trans ?_)
  -- `C_G(x) ≤ C_G(y) = C_G(X) ≤ N_G(X) ≤ M*`.
  refine le_trans ?_ ((Subgroup.centralizer_le_normalizer _).trans hMst_le)
  rw [hXdef, centralizer_zpowers_eq_singleton]
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg ⊢
  intro z hz
  rw [Set.mem_singleton_iff] at hz
  subst hz
  have hcomm : Commute x g := hg x (Set.mem_singleton x)
  exact ((hcomm.pow_left _) : _)

/-- **BG Corollary 12.6** (mmd L3179): `p ∈ τ₂(M)`, `A ∈ ℰ_p²(E)` のとき
(a) `A ⊴ E` かつ `ℰ_p¹(E)=ℰ¹(A)`; (b) `C_G(A) ⊆ N_M(A)=E`, `N_G(A) ⊄ M`;
(c) `X ∈ ℰ¹(A)` で `C_{M_σ}(X)≠1` なら `ℳ(C_G(X))={M}`; (d) `x ∈ E₃#` で `C_{M_σ}(x)=1`;
(e) `x ∈ C_{E₁}(A)#` で `C_{M_σ}(x)=1`; (f) `M^*` が `M` と非共役なら `M_σ ∩ M^*_σ = 1` かつ
`σ(M) ∩ σ(M^*) = ∅`。 -/
theorem elemAb_normal_in_E_of_tau2 [Finite G] (hG : IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    (E ≤ Subgroup.normalizer (A : Set G) ∧
      (∀ X ∈ elemAbelianOfRank G p 1, X ≤ E ↔ X ≤ A)) ∧
    (Subgroup.centralizer (A : Set G) ≤ E ∧
      M ⊓ Subgroup.normalizer (A : Set G) = E ∧ ¬ (Subgroup.normalizer (A : Set G) ≤ M)) ∧
    (∀ X ∈ elemAbelianOfRank G p 1, X ≤ A →
      S10.Msigma M ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ →
      maximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M}) ∧
    (∀ x ∈ E₃, x ≠ 1 → S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) ∧
    (∀ x ∈ E₁, x ∈ Subgroup.centralizer (A : Set G) → x ≠ 1 →
      S10.Msigma M ⊓ Subgroup.centralizer ({x} : Set G) = ⊥) ∧
    (∀ Mstar ∈ maximalSubgroups G, (¬ ∃ g : G, MulAut.conj g • M = Mstar) →
      S10.Msigma M ⊓ S10.Msigma Mstar = ⊥ ∧ Disjoint (S10.sigma M) (S10.sigma Mstar)) := by
  classical
  have hAM : A ≤ M := hAE.trans h.E_le
  have h125 := Msigma_nilpotent_of_tau2 hG h.mem_maximal hp hA hAM
  refine ⟨⟨E_le_normalizer_of_tau2 hG h hp hA hAE,
    fun X hX => ⟨fun hXE => line_le_of_le_E_of_tau2 hG h hp hA hAE hX hXE,
      fun hXA => hXA.trans hAE⟩⟩,
    centralizer_le_E_of_tau2 hG h hp hA hAE,
    fun X hX hXA hCne =>
      maximalContaining_centralizer_line_eq_singleton hG h hp hA hAE hX hXA hCne,
    ?_, ?_, ?_⟩
  · -- (d): `x ∈ E₃#`.
    intro x hx hx1
    -- primes of `orderOf x` lie in `τ₃(M)`.
    have hr : ∀ r ∈ (orderOf x).primeFactors, r ∈ tau1 M ∪ tau3 M := by
      intro r hrm
      refine Or.inr ?_
      have hr_prime := Nat.prime_of_mem_primeFactors hrm
      have h1 : r ∣ Nat.card ↥E₃ :=
        (Nat.mem_primeFactors.mp hrm).2.1.trans (Subgroup.orderOf_dvd_natCard E₃ hx)
      have h2 : r ∈ (Nat.card ↥(E₃.subgroupOf E)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
        exact Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩
      exact h.E₃_hall.1 r h2
    -- `A` centralizes `E₃` (`⁅A, E₃⁆ ≤ A ⊓ E₃ = ⊥`).
    have hAE₃_bot : A ⊓ E₃ = ⊥ := by
      rw [← Subgroup.card_eq_one]
      have h1 : Nat.card ↥(A ⊓ E₃ : Subgroup G) ∣ p ^ 2 := by
        rw [← hA.2]
        exact Subgroup.card_dvd_of_le inf_le_left
      have hnp : ¬ p ∣ Nat.card ↥(A ⊓ E₃ : Subgroup G) := by
        intro hdvd
        have h2 : p ∣ Nat.card ↥E₃ := hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)
        have h3 : p ∈ (Nat.card ↥(E₃.subgroupOf E)).primeFactors := by
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₃_le).toEquiv]
          exact Nat.mem_primeFactors.mpr ⟨Fact.out, h2, Nat.card_pos.ne'⟩
        have h4 := tau3_pRank_eq_one (h.E₃_hall.1 p h3)
        have h5 := tau2_pRank_eq_two hp
        omega
      exact Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.pow_right 2
          ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnp).symm) h1
    have hAcentE₃ : A ≤ Subgroup.centralizer (E₃ : Set G) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_bot_iff, ← hAE₃_bot]
      rw [Subgroup.commutator_le]
      intro a ha t ht
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : t * a⁻¹ * t⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp
            (E_le_normalizer_of_tau2 hG h hp hA hAE (h.E₃_le ht)) a⁻¹).mp (A.inv_mem ha)
        have h2 : a * (t * a⁻¹ * t⁻¹) ∈ A := A.mul_mem ha h1
        rw [commutatorElement_def]
        simpa [mul_assoc] using h2
      · have h1 : a * t * a⁻¹ ∈ E₃ :=
          (Subgroup.mem_normalizer_iff.mp (h.E3_normal hG (hAE ha)) t).mp ht
        have h2 : a * t * a⁻¹ * t⁻¹ ∈ E₃ := E₃.mul_mem h1 (E₃.inv_mem ht)
        rwa [commutatorElement_def]
    exact Msigma_inf_centralizer_eq_bot_of_le_centralizer hG h hp hA hAE
      (h.E3_le_M hx) hx1 hr
      (hAcentE₃.trans (Subgroup.centralizer_le
        (Set.singleton_subset_iff.mpr (SetLike.mem_coe.mpr hx))))
  · -- (e): `x ∈ C_{E₁}(A)#`.
    intro x hx hxC hx1
    have hr : ∀ r ∈ (orderOf x).primeFactors, r ∈ tau1 M ∪ tau3 M := by
      intro r hrm
      refine Or.inl ?_
      have hr_prime := Nat.prime_of_mem_primeFactors hrm
      have h1 : r ∣ Nat.card ↥E₁ :=
        (Nat.mem_primeFactors.mp hrm).2.1.trans (Subgroup.orderOf_dvd_natCard E₁ hx)
      have h2 : r ∈ (Nat.card ↥(E₁.subgroupOf E)).primeFactors := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E₁_le).toEquiv]
        exact Nat.mem_primeFactors.mpr ⟨hr_prime, h1, Nat.card_pos.ne'⟩
      exact h.E₁_hall.1 r h2
    have hAC : A ≤ Subgroup.centralizer ({x} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp hxC a ha).symm
    exact Msigma_inf_centralizer_eq_bot_of_le_centralizer hG h hp hA hAE
      (h.E1_le_M hx) hx1 hr hAC
  · -- (f): Lemma 10.12(b) with `M_σ` nilpotent.
    intro Mstar hMst hnc
    have h1012 := (S10.disjoint_of_not_conj hG h.mem_maximal hMst hnc).2 h125.1
    exact ⟨h1012.1, Set.disjoint_iff_inter_eq_empty.mpr h1012.2⟩

end OddOrder.BG.Ch3.S12


