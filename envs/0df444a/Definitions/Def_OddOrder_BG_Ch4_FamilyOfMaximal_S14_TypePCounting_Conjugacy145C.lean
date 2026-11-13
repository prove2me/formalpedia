-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Conjugacy145C
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_Conjugacy145C
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T09:15:48.631437+00:00
-- url     : https://prove2.me/theorems/4d5731f3-97e6-4b16-a2df-8a2a5fc0b632
-- title:
--   BG §14: type-$\mathcal{P}$ counting, conjugacy (14.5(c))
-- statement:
--   The conjugacy part of the §14 type-$\mathcal{P}$ counting development of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split from the $\sigma$-length-one file. It defines the genuine $\sigma$-decomposition data, BG's subgroup $R(x)$ (a normal Hall subgroup of $C_G(x)$) and the set $\widetilde M=\{xx' : x\in M_\sigma^\#,\ x'\in R(x)\}$.
--
--   Main declarations: `genuineSigmaDecomposition`; `Mtilde`; `Rsub`.
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Conjugacy145C.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S14_TypePCounting/Conjugacy145C.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S14_TypePCounting_LocalStructure

namespace OddOrder.BG.Ch4.S14

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch3.S13

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **`N_{M_σ}(A) = 1` for a rank-2 `τ₂(M)`-subgroup `A ≤ E`** (the crux of Theorem 14.4(c)).
If `M ∈ 𝓜`, `p ∈ τ₂(M)`, and `A ∈ ℰ_p²(E)` for an `E`-setup of `M`, then
`N_G(A) ⊓ M_σ = 1`: Corollary 12.6(b) gives `M ⊓ N_G(A) = E`, and `M_σ ⊓ E = 1`
(`E` complements `M_σ`), so `N_G(A) ⊓ M_σ = (M ⊓ N_G(A)) ⊓ M_σ = E ⊓ M_σ = 1`. -/
theorem Msigma_inf_normalizer_eq_bot_of_tau2 [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M E E₁ E₂ E₃ : Subgroup G} (h : SubgroupESetup M E E₁ E₂ E₃) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ tau2 M) {A : Subgroup G} (hA : A ∈ elemAbelianOfRank G p 2) (hAE : A ≤ E) :
    Subgroup.normalizer (A : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M = ⊥ := by
  have hNMA : M ⊓ Subgroup.normalizer (A : Set G) = E :=
    (centralizer_le_E_of_tau2 hG h hp hA hAE).2.1
  have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
  calc Subgroup.normalizer (A : Set G) ⊓ OddOrder.BG.Ch3.S10.Msigma M
      = Subgroup.normalizer (A : Set G) ⊓ (M ⊓ OddOrder.BG.Ch3.S10.Msigma M) := by
        rw [inf_eq_right.mpr hMσM]
    _ = (M ⊓ Subgroup.normalizer (A : Set G)) ⊓ OddOrder.BG.Ch3.S10.Msigma M := by
        rw [← inf_assoc, inf_comm (Subgroup.normalizer (A : Set G)) M]
    _ = E ⊓ OddOrder.BG.Ch3.S10.Msigma M := by rw [hNMA]
    _ = ⊥ := by rw [inf_comm]; exact h.E_compl_inf

/-- **BG Theorem 14.4** (mmd L3869, D. Sibley for part (f)): if `x ∈ G^#` and `𝓜_σ(x)` is
nonempty (equivalently `ℓ_σ(x) = 1`), then `C_G(x)` has a normal Hall subgroup `R(x)` acting
sharply transitively on `𝓜_σ(x)`.  Furthermore, if `|𝓜_σ(x)| > 1` then `C_G(x)` lies in a
unique `N = N(x) ∈ 𝓜`, and for every `M ∈ 𝓜_σ(x)`:
(a) `R(x) = C_{N_σ}(x) ⊋ 1` (a normal Hall `σ(N)`-subgroup of `C_G(x)`),
(b) `C_G(x) = C_{M∩N}(x) R(x)`,
(c) `π(⟨x⟩) ⊆ τ₂(N) ⊆ σ(M)`,
(d) `π(M) ∩ σ(N) ⊆ β(N)`,
(e) `M ∩ N` complements `N_σ` in `N`, and
(f) `N ∈ 𝓜_F ∪ 𝓜_{P₂}`.

**Faithfulness (2026-06-15):** the earlier scaffold's over-claim is fixed — the `N`/type
structure is now **guarded by `|𝓜_σ(x)| > 1`** (in the single-maximal case `R(x) = 1` and
there is no `N(x)`, so BG asserts no such structure).  `R(x)` is pinned to its concrete value
`C_{N_σ}(x) = M_σ(N) ⊓ C_G(x)` (part (a)), `N` is unique (`∃!`), and parts (a),(c),(d),(e),(f)
are recorded.  **Deferred to §16:** the headline "`R(x)` normal in `C_G(x)` and **sharply
transitive** on `𝓜_σ(x)`" and part (b) are preserved verbatim in §16 (`RData` /
`ConjSharplyTransitiveOn`, Theorem D); this surface should cite §16 at proof time rather than
restating them (importing §16 here would be circular).  Proof gated on §13 (Thm 13.9 + the
Cor 14.3 funnel).  See `notes/bg/s14_typeP_counting.md`. -/
theorem sigmaLength_one_centralizer_structure [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    {x : G} (hx : x ≠ 1) (hlen : D.length x = 1) :
    (maximalSigmaSubgroupsOfElement x).Nonempty ∧
      (1 < (maximalSigmaSubgroupsOfElement x).ncard →
        ∃! N : Subgroup G, N ∈ maximalSubgroups G ∧
          Subgroup.centralizer ({x} : Set G) ≤ N ∧
          OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
          Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
            ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
              (Subgroup.centralizer ({x} : Set G))) ∧
          (∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 N) ∧
          (IsTypeF N ∨ IsTypeP2 N) ∧
          ∀ M ∈ maximalSigmaSubgroupsOfElement x,
            tau2 N ∩ piSet N ⊆ OddOrder.BG.Ch3.S10.sigma M ∧
            OddOrder.BG.Ch3.S10.sigma N ∩ piSet M ⊆ OddOrder.BG.Ch3.S10.beta N ∧
            Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
              ((M ⊓ N).subgroupOf N) ∧
            -- **(Sharp transitivity, BG Thm 14.4 headline)**: `R(x) = N_σ ∩ C_G(x)` acts
            -- *regularly* (sharply transitively) on `𝓜_σ(x)` by conjugation: for every other
            -- `L ∈ 𝓜_σ(x)` there is a *unique* `r ∈ R(x)` with `M^r = L`.
            (∀ L ∈ maximalSigmaSubgroupsOfElement x,
              ∃! r : G, (r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) ∧
                MulAut.conj r • M = L)) := by
  classical
  -- (Nonempty) `𝓜_σ(x)` is nonempty because `ℓ_σ(x) = 1`.
  obtain ⟨-, hne⟩ := (D.length_one_iff x).mp hlen
  refine ⟨hne, fun hgt => ?_⟩
  -- Setup (BG L3877): pick `M ∈ 𝓜_σ(x)`, a prime `q ∣ |x|`, and `g ∈ ⟨x⟩` of order `q`,
  -- giving `X = ⟨g⟩ ∈ ℰ_q¹(⟨x⟩)` with `X ≤ M_σ` and `q ∈ σ(M)`.
  obtain ⟨M, hMmax, hxMσ⟩ := hne
  have hord1 : orderOf x ≠ 1 := fun h => hx (orderOf_eq_one_iff.mp h)
  obtain ⟨q, hqp, hqdvd⟩ := (orderOf x).exists_prime_and_dvd hord1
  have : Fact q.Prime := ⟨hqp⟩
  obtain ⟨gsub, hgord⟩ := exists_prime_orderOf_dvd_card' q
    (show q ∣ Nat.card ↥(Subgroup.zpowers x) by rw [Nat.card_zpowers]; exact hqdvd)
  have hgord' : orderOf (gsub : G) = q :=
    (orderOf_injective (Subgroup.zpowers x).subtype (Subgroup.zpowers x).subtype_injective
      gsub).trans hgord
  set X : Subgroup G := Subgroup.zpowers (gsub : G) with hXdef
  have hXcard : Nat.card ↥X = q := by rw [hXdef, Nat.card_zpowers, hgord']
  have hXelem : X ∈ elemAbelianOfRank G q 1 :=
    ⟨Subgroup.IsElementaryAbelian.of_card_prime hXcard, by rw [hXcard, pow_one]⟩
  have hXne : X ≠ ⊥ := ne_bot_of_mem_elemAbelianOfRank_one hXelem
  have hXx : X ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr gsub.2
  have hXMσ : X ≤ OddOrder.BG.Ch3.S10.Msigma M :=
    hXx.trans (Subgroup.zpowers_le.mpr hxMσ)
  have hqMσ : q ∣ Nat.card ↥(OddOrder.BG.Ch3.S10.Msigma M) :=
    hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hxMσ)
  have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q
      (Nat.mem_primeFactors.mpr ⟨hqp, hqMσ, Nat.card_pos.ne'⟩)
  have hXq : IsPGroup q ↥X := IsPGroup.of_card (by rw [hXcard, pow_one])
  have hXMle : X ≤ M := hXMσ.trans (OddOrder.BG.Ch3.S10.Msigma_le M)
  -- (Neighbour `N`) Since `|𝓜_σ(x)| ≥ 2`, pick `M' ∈ 𝓜_σ(x)` distinct from `M`.
  obtain ⟨M', hM'mem, hM'ne⟩ := Set.exists_ne_of_one_lt_ncard hgt M
  obtain ⟨hM'max, hxM'σ⟩ := hM'mem
  have hXM'σ : X ≤ OddOrder.BG.Ch3.S10.Msigma M' := hXx.trans (Subgroup.zpowers_le.mpr hxM'σ)
  have hXM'le : X ≤ M' := hXM'σ.trans (OddOrder.BG.Ch3.S10.Msigma_le M')
  have hqσM' : q ∈ OddOrder.BG.Ch3.S10.sigma M' :=
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M' q (Nat.mem_primeFactors.mpr
      ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M').orderOf_dvd_natCard hxM'σ),
        Nat.card_pos.ne'⟩)
  -- `M, M'` are conjugate (else Theorem 13.9 makes `σ(M), σ(M')` disjoint, but `q ∈ σ(M) ∩ σ(M')`).
  have hconj : ∃ g : G, MulAut.conj g • M = M' := by
    by_contra hnc
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hM'max hnc) hqσM hqσM'
  obtain ⟨g, hg⟩ := hconj
  -- Theorem 10.1(b): some `c ∈ C_G(X)` conjugates `M` to `M'`.
  have hX1 : X ≤ MulAut.conj (1 : G) • M := by rw [map_one, one_smul]; exact hXMle
  have hXg : X ≤ MulAut.conj g • M := by rw [hg]; exact hXM'le
  obtain ⟨c, hcC, hcconj⟩ :=
    (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hMmax hqσM hXne hXq).2.1 1 g hX1 hXg
  rw [map_one, one_smul] at hcconj
  have hcM' : MulAut.conj c • M = M' := by rw [hcconj]; exact hg
  -- Hence `C_G(X) ⊄ M`, so `N_G(X) ⊄ M`.
  have hNXM : ¬ Subgroup.normalizer (X : Set G) ≤ M := by
    intro hNXM
    have hcM : c ∈ M := hNXM (Subgroup.centralizer_le_normalizer (X : Set G) hcC)
    have hfix : MulAut.conj c • M = M :=
      conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hcM)
    have : M = M' := by rw [← hfix]; exact hcM'
    exact hM'ne this.symm
  -- Build the maximal `N ⊇ N_G(X)`; then `N ≠ M`.
  obtain ⟨N, hNmax, hNge⟩ :=
    OddOrder.BG.Ch2.S08.exists_maximalSubgroup_containing_normalizer_of_ne_bot_le_maximal
      hG hMmax hXne hXMle
  have hNne : N ≠ M := fun he => hNXM (he ▸ hNge)
  -- `C_G(x) ≤ N`: `C_G(x) ≤ C_G(X) ≤ N_G(X) ≤ N` (as `X ≤ ⟨x⟩`).
  have hCxCX : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.centralizer (X : Set G) := by
    rw [← centralizer_zpowers_eq_singleton' x]
    exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXx)
  have hCxN : Subgroup.centralizer ({x} : Set G) ≤ N :=
    hCxCX.trans ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNge)
  -- (Prop 12.15) Build `S = Sylow_q(M ∩ N) ⊇ X` and apply Proposition 12.15 to `(M, q, X, N, S)`.
  have hNmem : N ∈ maximalSubgroupsContaining (Subgroup.normalizer (X : Set G)) :=
    mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hNmax, hNge⟩
  have hXNle : X ≤ N := Subgroup.le_normalizer.trans hNge
  have hXMN : X ≤ M ⊓ N := le_inf hXMle hXNle
  have hXsub_pg : IsPGroup q ↥(X.subgroupOf (M ⊓ N)) :=
    hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXMN).symm
  obtain ⟨Psub, hPsub⟩ := hXsub_pg.exists_le_sylow
  set S : Subgroup G := (Psub : Subgroup ↥(M ⊓ N)).map (M ⊓ N).subtype with hSdef
  have hSle : S ≤ M ⊓ N := Subgroup.map_subtype_le _
  have hSq : IsPGroup q ↥S :=
    Psub.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M ⊓ N).subtype_injective)
  have hXS : X ≤ S := by
    rw [hSdef, ← Subgroup.map_subgroupOf_eq_of_le hXMN]; exact Subgroup.map_mono hPsub
  have hPsubeq : S.subgroupOf (M ⊓ N) = Psub := by
    rw [hSdef]; exact Subgroup.comap_map_eq_self_of_injective (M ⊓ N).subtype_injective _
  have hSmax : ∀ T : Subgroup G, T ≤ M ⊓ N → IsPGroup q ↥T → S ≤ T → S = T := by
    intro T hTle hTq hST
    have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M ⊓ N)) :=
      hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
    have hTeq := Psub.3 hTsub_pg (by rw [← hPsubeq]; exact Subgroup.comap_mono hST)
    rw [hSdef, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
  have h1215 := sigma_subgroup_maximal_interaction hG hMmax hqσM hXMle hXne hXq hNmem hNne
    hSle hXS hSq hSmax
  -- (a) `M, N` nonconjugate ⟹ (Theorem 13.9) `σ(M) ∩ σ(N) = ∅` ⟹ `q ∉ σ(N)`.
  have hqnσN : q ∉ OddOrder.BG.Ch3.S10.sigma N := fun hqσN =>
    Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hNmax h1215.1) hqσM hqσN
  -- Proposition 12.15(e): `q ∈ τ₂(N)`, `(d)`, and `(e)` (`M ∩ N` complements `N_σ` in `N`).
  obtain ⟨hqτ2N, hdN, hsigmaInf, hsigmaSup⟩ := h1215.2.2.2.2 hqnσN
  -- `x ∈ N` (as `x ∈ C_G(x) ≤ N`).
  have hxN : x ∈ N := hCxN (Subgroup.mem_centralizer_iff.mpr
    (fun h hh => by rw [Set.mem_singleton_iff.mp hh]))
  -- `R(x) = N_σ ∩ C_G(x) ≠ 1` (BG's `u`-construction: a nontrivial `σ(N)`-element of `C_G(x)`).
  have hxMmem : x ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  have hRx : OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ := by
    -- `N_G(M) = M` (maximal ⟹ self-normalizing).
    have hMne : M ≠ ⊥ := fun hb => hXne (le_bot_iff.mp (hb ▸ hXMle))
    have hNMle : Subgroup.normalizer M ≤ M := by
      rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M)) with heq | hlt
      · exact heq.ge
      · rcases hG.simple.eq_bot_or_eq_top_of_normal M
            (Subgroup.normalizer_eq_top_iff.mp ((mem_maximalSubgroups.mp hMmax).2 _ hlt)) with hb |
                ht
        · exact absurd hb hMne
        · exact absurd ht (mem_maximalSubgroups.mp hMmax).1
    -- Decompose `c = v * a` with `v ∈ N_σ`, `a ∈ M ⊓ N` (in `↥N`, since `N_σ ⊴ N`).
    have hcN : c ∈ N := ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNge) hcC
    have hMσN_le : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
    have hH'normal : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hsup' : (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N ⊔ (M ⊓ N).subgroupOf N = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hMσN_le inf_le_right, hsigmaSup, Subgroup.subgroupOf_self]
    have hc'mem : (⟨c, hcN⟩ : ↥N) ∈
        (↑((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) *
          ↑((M ⊓ N).subgroupOf N) : Set ↥N) := by
      rw [← Subgroup.normal_mul, hsup']; exact Subgroup.mem_top _
    obtain ⟨vsub, hvsub, asub, hasub, hva⟩ := hc'mem
    have hvMσ : (vsub : G) ∈ OddOrder.BG.Ch3.S10.Msigma N := Subgroup.mem_subgroupOf.mp hvsub
    have haM : (asub : G) ∈ M := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hasub)).1
    have hcva : (vsub : G) * (asub : G) = c := by
      have := congrArg (Subgroup.subtype N) hva; simpa using this
    -- `conj v • M = M'` (as `a ∈ M`), so `v ≠ 1`.
    have hvM' : MulAut.conj (vsub : G) • M = M' := by
      have ha_fix : MulAut.conj (asub : G) • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer haM)
      rw [← hcM', ← hcva, map_mul, mul_smul, ha_fix]
    have hvne : (vsub : G) ≠ 1 := by
      intro hv1; rw [hv1, map_one, one_smul] at hvM'; exact hM'ne hvM'.symm
    -- `x⁻¹ v x ∈ N_σ` (normal, `x ∈ N`).
    have hconjMσ : x⁻¹ * (vsub : G) * x ∈ OddOrder.BG.Ch3.S10.Msigma N := by
      have h := hH'normal.conj_mem vsub hvsub (⟨x, hxN⟩⁻¹)
      have := Subgroup.mem_subgroupOf.mp h; simpa using this
    -- `conj (x⁻¹ v x) • M = conj v • M` (key step: `M^x = M`, `M'^{x⁻¹} = M'`).
    have hxM'mem : x ∈ M' := OddOrder.BG.Ch3.S10.Msigma_le M' hxM'σ
    have hkey : MulAut.conj (x⁻¹ * (vsub : G) * x) • M = MulAut.conj (vsub : G) • M := by
      have hxM : MulAut.conj x • M = M :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxMmem)
      have hxM' : MulAut.conj x⁻¹ • M' = M' :=
        conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (M'.inv_mem hxM'mem))
      calc MulAut.conj (x⁻¹ * (vsub : G) * x) • M
          = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • (MulAut.conj x • M)) := by
            rw [map_mul, map_mul, mul_smul, mul_smul]
        _ = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • M) := by rw [hxM]
        _ = MulAut.conj x⁻¹ • M' := by rw [hvM']
        _ = M' := hxM'
        _ = MulAut.conj (vsub : G) • M := hvM'.symm
    -- `v⁻¹ (x⁻¹ v x) ∈ N_G(M) ∩ N_σ = M ∩ N_σ = ⊥`, hence `x⁻¹ v x = v`, i.e. `v ∈ C_G(x)`.
    have hmemNM : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ Subgroup.normalizer M := by
      apply mem_normalizer_of_conj_smul_eq_self
      rw [map_mul, mul_smul, hkey, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
    have hmemMσ : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ OddOrder.BG.Ch3.S10.Msigma N :=
      (OddOrder.BG.Ch3.S10.Msigma N).mul_mem
        ((OddOrder.BG.Ch3.S10.Msigma N).inv_mem hvMσ) hconjMσ
    have hmem1 : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) = 1 := by
      have hinbot : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ (⊥ : Subgroup G) := by
        rw [← hsigmaInf]
        exact Subgroup.mem_inf.mpr ⟨hmemMσ,
          Subgroup.mem_inf.mpr ⟨hNMle hmemNM, hMσN_le hmemMσ⟩⟩
      exact Subgroup.mem_bot.mp hinbot
    have hvx : x⁻¹ * (vsub : G) * x = (vsub : G) := (inv_mul_eq_one.mp hmem1).symm
    have hvCx : (vsub : G) ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy; rw [Set.mem_singleton_iff.mp hy]
      have hcomm : x * (vsub : G) = (vsub : G) * x := by nth_rewrite 1 [← hvx]; group
      exact hcomm
    intro hbot
    exact hvne (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_inf.mpr ⟨hvMσ, hvCx⟩))
  -- `π(⟨x⟩) ⊆ τ₂(N)` (Corollary 14.3, since `x` is not a `κ(N)`-element).
  have hcardx : Nat.card ↥(Subgroup.closure ({x} : Set G)) = orderOf x := by
    rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
  have hπτ2 : ∀ p ∈ piSet (Subgroup.closure {x}), p ∈ tau2 N := by
    -- A nonidentity `w ∈ N_σ` centralizing `x` (from `R(x) ≠ 1`).
    have : Nontrivial ↥(OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) :=
      (Subgroup.nontrivial_iff_ne_bot _).mpr hRx
    obtain ⟨wsub, hwsub⟩ :=
      exists_ne (1 : ↥(OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)))
    have hwmem := wsub.2
    have hwne : (wsub : G) ≠ 1 := fun h => hwsub (OneMemClass.coe_eq_one.mp h)
    obtain ⟨hwMσ, hwCx⟩ := Subgroup.mem_inf.mp hwmem
    have hwsharp : (wsub : G) ∈ sigmaSharp N := by
      rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
      exact ⟨hwMσ, hwne⟩
    have hxCw : x ∈ Subgroup.centralizer ({(wsub : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]; intro y hy; rw [Set.mem_singleton_iff.mp hy]
      exact (Subgroup.mem_centralizer_iff.mp hwCx x (Set.mem_singleton x)).symm
    -- `π(⟨x⟩) ⊆ σ(M) ⊆ σ(N)'` (since `x ∈ M_σ` and `σ(M) ∩ σ(N) = ∅` by Theorem 13.9).
    have hxσN : ∀ p ∈ piSet (Subgroup.closure {x}), p ∉ OddOrder.BG.Ch3.S10.sigma N := by
      intro p hp
      have hp' : p ∈ (orderOf x).primeFactors := by
        rw [piSet, Set.mem_ofPred_eq, hcardx] at hp; exact hp
      have hpσM : p ∈ OddOrder.BG.Ch3.S10.sigma M :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup M p (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hp', (Nat.dvd_of_mem_primeFactors hp').trans
            ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hxMσ), Nat.card_pos.ne'⟩)
      exact Set.disjoint_left.mp
        (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hMmax hNmax h1215.1) hpσM
    -- Corollary 14.3: branch κ is impossible (`q ∈ τ₂(N)` has `r_q = 2 ≠ 1`), so the τ₂ branch
    -- holds.
    rcases sigma_diagnostic hG D hNmax hwsharp hxN hx hxCw hxσN with ⟨hκ, _⟩ | ⟨hτ2, _, _⟩
    · exfalso
      have hqπ : q ∈ piSet (Subgroup.closure ({x} : Set G)) := by
        rw [piSet, Set.mem_ofPred_eq, hcardx]
        exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩
      have h2 := ((mem_tau2_iff N q).mp hqτ2N).2
      rcases (hκ q hqπ).2.1 with h1 | h3
      · exact absurd (((mem_tau1_iff N q).mp h1).2.2.symm.trans h2) (by norm_num)
      · exact absurd (((mem_tau3_iff N q).mp h3).2.2.symm.trans h2) (by norm_num)
    · exact hτ2
  -- `ℳ(C_G(x)) = {N}` (Corollary 14.3 uniqueness clause).
  have hsingleton : maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} :=
    maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx hπτ2 hRx
  refine ⟨N, ⟨hNmax, hCxN, hRx, ?_, hπτ2, ?_, ?_⟩, ?_⟩
  · -- `R(x) = N_σ ∩ C_G(x)` is a Hall `σ(N)`-subgroup of `C_G(x)`: it is a `σ(N)`-group, and its
    -- index `(N_σ).relIndex C_G(x) ∣ (N_σ).relIndex N = [N : N_σ] ∣ [G : N_σ]` is `σ(N)'`.
    have hK₀normal : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    refine ⟨?_, ?_⟩
    · intro p hp
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≤
          Subgroup.centralizer ({x} : Set G))).toEquiv] at hp
      exact OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1, (Nat.mem_primeFactors.mp hp).2.1.trans
          (Subgroup.card_dvd_of_le inf_le_left), Nat.card_pos.ne'⟩)
    · intro p hp hpσ
      rw [Subgroup.inf_subgroupOf_right] at hp
      have hdvd1 : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf
          (Subgroup.centralizer ({x} : Set G))).index ∣
          ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index := by
        have h := Subgroup.relIndex_dvd_index_of_normal
          (H := (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          (K := (Subgroup.centralizer ({x} : Set G)).subgroupOf N)
        rwa [Subgroup.relIndex_subgroupOf hCxN] at h
      have hdvd2 : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).index ∣
          (OddOrder.BG.Ch3.S10.Msigma N).index :=
        Subgroup.relIndex_dvd_index_of_le (OddOrder.BG.Ch3.S10.Msigma_le N)
      exact (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax).2 p (Nat.mem_primeFactors.mpr
        ⟨(Nat.mem_primeFactors.mp hp).1,
          ((Nat.mem_primeFactors.mp hp).2.1.trans hdvd1).trans hdvd2,
          Subgroup.index_ne_zero_of_finite⟩) hpσ
  · -- `(f)`: `N ∈ 𝓜_F ∪ 𝓜_{P₂}`.  Either `κ(N) = ∅` (type F), or `κ(N) ≠ ∅` and, since
    -- `q ∈ τ₂(N) ⊆ π(N) - σ(N)` but `q ∉ κ(N)` (as `κ(N) ⊆ τ₁(N) ∪ τ₃(N)` has `r_q = 1 ≠ 2`),
    -- `κ(N) ≠ π(N) - σ(N)`, so `N ∉ 𝓜_{P₁}` (type P₂).
    by_cases hk : kappa N = ∅
    · exact Or.inl hk
    · refine Or.inr ⟨Set.nonempty_iff_ne_empty.mpr hk, fun heq => ?_⟩
      have hq_notin : q ∉ kappa N := by
        intro hqk
        have h2 := ((mem_tau2_iff N q).mp hqτ2N).2
        rcases hqk.2.1 with h1 | h3
        · exact absurd (((mem_tau1_iff N q).mp h1).2.2.symm.trans h2) (by norm_num)
        · exact absurd (((mem_tau3_iff N q).mp h3).2.2.symm.trans h2) (by norm_num)
      have hq_in : q ∈ sigmaComplementPrimes N :=
        ⟨Nat.mem_primeFactors.mpr ⟨hqp, hXcard ▸ Subgroup.card_dvd_of_le hXNle, Nat.card_pos.ne'⟩,
          hqnσN⟩
      rw [heq] at hq_notin
      exact hq_notin hq_in
  · -- per-`M` part `(c)`, `(d)`, `(e)`.  Fix `M₂ ∈ 𝓜_σ(x)` and re-run Proposition 12.15 for
    -- `(M₂, q, X, N)`: `N ≠ M₂` (as `x ∈ M₂_σ` but `x ∉ N_σ`), and `q ∉ σ(N)`
    -- (`q ∈ π(⟨x⟩) ⊆ τ₂(N)`).
    intro M₂ hM₂mem
    obtain ⟨hM₂max, hxM₂σ⟩ := hM₂mem
    have hMσNnormal : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
      rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
    have hMσN_le : OddOrder.BG.Ch3.S10.Msigma N ≤ N := OddOrder.BG.Ch3.S10.Msigma_le N
    have hXM₂σ : X ≤ OddOrder.BG.Ch3.S10.Msigma M₂ := hXx.trans (Subgroup.zpowers_le.mpr hxM₂σ)
    have hXM₂le : X ≤ M₂ := hXM₂σ.trans (OddOrder.BG.Ch3.S10.Msigma_le M₂)
    have hqσM₂ : q ∈ OddOrder.BG.Ch3.S10.sigma M₂ :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ q (Nat.mem_primeFactors.mpr
        ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M₂).orderOf_dvd_natCard hxM₂σ),
          Nat.card_pos.ne'⟩)
    have hqπ : q ∈ piSet (Subgroup.closure ({x} : Set G)) := by
      rw [piSet, Set.mem_ofPred_eq, hcardx]
      exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos x).ne'⟩
    have hqnσN : q ∉ OddOrder.BG.Ch3.S10.sigma N := fun h => tau2_subset_sigma_compl N (hπτ2 q hqπ)
        h
    have hNM₂ : N ≠ M₂ := fun heq => hqnσN (heq ▸ hqσM₂)
    -- Build `S₂ = Sylow_q(M₂ ∩ N) ⊇ X`.
    have hXM₂N : X ≤ M₂ ⊓ N := le_inf hXM₂le hXNle
    have hXsub_pg₂ : IsPGroup q ↥(X.subgroupOf (M₂ ⊓ N)) :=
      hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXM₂N).symm
    obtain ⟨Psub₂, hPsub₂⟩ := hXsub_pg₂.exists_le_sylow
    set S₂ : Subgroup G := (Psub₂ : Subgroup ↥(M₂ ⊓ N)).map (M₂ ⊓ N).subtype with hS₂def
    have hS₂le : S₂ ≤ M₂ ⊓ N := Subgroup.map_subtype_le _
    have hS₂q : IsPGroup q ↥S₂ :=
      Psub₂.2.of_equiv (Subgroup.equivMapOfInjective _ _ (M₂ ⊓ N).subtype_injective)
    have hXS₂ : X ≤ S₂ := by
      rw [hS₂def, ← Subgroup.map_subgroupOf_eq_of_le hXM₂N]; exact Subgroup.map_mono hPsub₂
    have hPsub₂eq : S₂.subgroupOf (M₂ ⊓ N) = Psub₂ := by
      rw [hS₂def]; exact Subgroup.comap_map_eq_self_of_injective (M₂ ⊓ N).subtype_injective _
    have hSmax₂ : ∀ T : Subgroup G, T ≤ M₂ ⊓ N → IsPGroup q ↥T → S₂ ≤ T → S₂ = T := by
      intro T hTle hTq hST
      have hTsub_pg : IsPGroup q ↥(T.subgroupOf (M₂ ⊓ N)) :=
        hTq.of_equiv (Subgroup.subgroupOfEquivOfLe hTle).symm
      have hTeq := Psub₂.3 hTsub_pg (by rw [← hPsub₂eq]; exact Subgroup.comap_mono hST)
      rw [hS₂def, ← hTeq, Subgroup.map_subgroupOf_eq_of_le hTle]
    have h1215₂ := sigma_subgroup_maximal_interaction hG hM₂max hqσM₂ hXM₂le hXne hXq hNmem hNM₂
      hS₂le hXS₂ hS₂q hSmax₂
    obtain ⟨_, hdN₂, hsigmaInf₂, hsigmaSup₂⟩ := h1215₂.2.2.2.2 hqnσN
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- (c) `τ₂(N) ⊆ σ(M₂)` (Corollary 12.6 argument).  Take `A ∈ ℰ_p²(N)` inside the complement
      -- `M₂ ∩ N` (= an `E`-setup `E_N` of `N` by `exists_subgroupESetup_with_le`); then `A ⊴ E_N`
      -- (Cor 12.6(a)) and `x ∈ M₂∩N = E_N` normalises `A`, so `x ∈ N_{M₂σ}(A) ⊋ 1`.  As `A ≤ M₂`
      -- has rank 2, `p ∈ σ(M₂) ∪ τ₂(M₂)`; if `p ∈ τ₂(M₂)` the crux helper forces `N_{M₂σ}(A) = 1`.
      intro p hp
      obtain ⟨hpτ2N, hppiN⟩ := hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hppiN
      have : Fact p.Prime := ⟨hpp⟩
      have hM₂N_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma N)ᶜ) (M₂ ⊓ N) := by
        intro r hr
        rw [Set.mem_compl_iff]
        intro hrσN
        have : Fact r.Prime := ⟨Nat.prime_of_mem_primeFactors hr⟩
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' r
          (Nat.dvd_of_mem_primeFactors hr : r ∣ Nat.card ↥(M₂ ⊓ N))
        have hzord : orderOf (z : G) = r :=
          (orderOf_injective (M₂ ⊓ N).subtype (M₂ ⊓ N).subtype_injective z).trans hz
        have hzne : (z : G) ≠ 1 := by
          intro h; rw [h, orderOf_one] at hzord
          exact (Nat.prime_of_mem_primeFactors hr).ne_one hzord.symm
        have hzp_le : Subgroup.zpowers (z : G) ≤ M₂ ⊓ N := Subgroup.zpowers_le.mpr z.2
        have hzp_pi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma N)
            (Subgroup.zpowers (z : G)) := by
          intro s hs
          rw [Nat.card_zpowers, hzord,
            Nat.Prime.primeFactors (Nat.prime_of_mem_primeFactors hr), Finset.mem_singleton] at hs
          rw [hs]; exact hrσN
        have hzp_Msigma : Subgroup.zpowers (z : G) ≤ OddOrder.BG.Ch3.S10.Msigma N :=
          OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
            (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax) (hzp_le.trans inf_le_right) hzp_pi
        have hzp_bot : Subgroup.zpowers (z : G) ≤ ⊥ := by
          rw [← hsigmaInf₂]; exact le_inf hzp_Msigma hzp_le
        exact hzne (Subgroup.mem_bot.mp (hzp_bot (Subgroup.mem_zpowers (z : G))))
      obtain ⟨EN, E₁N, E₂N, E₃N, hN_E, hM₂N_le_EN, _⟩ :=
        exists_subgroupESetup_with_le hG hNmax inf_le_right hM₂N_pi
      have hEN_eq : EN = M₂ ⊓ N := by
        have hcompl_EN : Subgroup.IsComplement'
            ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) (EN.subgroupOf N) := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          · rw [disjoint_iff, eq_bot_iff]
            rintro a ha; rw [Subgroup.mem_inf] at ha
            have hav : (a : G) ∈ (⊥ : Subgroup G) := by
              rw [← hN_E.E_compl_inf]
              exact Subgroup.mem_inf.mpr
                ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
            rw [Subgroup.mem_bot] at hav; rw [Subgroup.mem_bot]; exact OneMemClass.coe_eq_one.mp hav
          · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hMσN_le hN_E.E_le,
              hN_E.E_compl_sup, Subgroup.subgroupOf_self, Subgroup.coe_top]
        have hcompl_M₂N : Subgroup.IsComplement'
            ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) ((M₂ ⊓ N).subgroupOf N) := by
          apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
          · rw [disjoint_iff, eq_bot_iff]
            rintro a ha; rw [Subgroup.mem_inf] at ha
            have hav : (a : G) ∈ (⊥ : Subgroup G) := by
              rw [← hsigmaInf₂]
              exact Subgroup.mem_inf.mpr
                ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
            rw [Subgroup.mem_bot] at hav; rw [Subgroup.mem_bot]; exact OneMemClass.coe_eq_one.mp hav
          · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup hMσN_le inf_le_right,
              hsigmaSup₂, Subgroup.subgroupOf_self, Subgroup.coe_top]
        have hcardEq : Nat.card ↥(EN.subgroupOf N) = Nat.card ↥((M₂ ⊓ N).subgroupOf N) :=
          Nat.eq_of_mul_eq_mul_left Nat.card_pos
              (hcompl_EN.card_mul_card.trans hcompl_M₂N.card_mul_card.symm)
        have hcard : Nat.card ↥EN = Nat.card ↥(M₂ ⊓ N) := by
          rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN_E.E_le).toEquiv,
            ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : M₂ ⊓ N ≤ N)).toEquiv]
          exact hcardEq
        exact (Subgroup.eq_of_le_of_card_ge hM₂N_le_EN (le_of_eq hcard)).symm
      obtain ⟨A₁, hA₁, hA₁N⟩ := exists_mem_elemAbelianOfRank_two_le_of_tau2 hpp hpτ2N
      obtain ⟨w, _, hwle⟩ := exists_conj_smul_le_hallPiece hG hN_E hN_E.E₂_le hN_E.E₂_hall
        (tau2_subset_sigma_compl N) hA₁N (by
          intro r hr
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₁N).toEquiv, hA₁.2,
            Nat.primeFactors_pow p two_ne_zero, Nat.Prime.primeFactors hpp] at hr
          rw [Finset.mem_singleton.mp hr]; exact hpτ2N)
      have hA : MulAut.conj w • A₁ ∈ elemAbelianOfRank G p 2 := conj_smul_mem_elemAbelianOfRank w
          hA₁
      have hAEN : MulAut.conj w • A₁ ≤ EN := hwle.trans hN_E.E₂_le
      have hAM₂ : MulAut.conj w • A₁ ≤ M₂ := by rw [hEN_eq] at hAEN; exact hAEN.trans inf_le_left
      -- `A ⊴ E_N` (Cor 12.6(a)); `x ∈ M₂∩N = E_N` ⟹ `x` normalises `A`; `x ∈ M₂_σ`.
      have hAnormalEN : EN ≤ Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G) :=
        (elemAb_normal_in_E_of_tau2 hG hN_E hpτ2N hA hAEN).1.1
      have hxEN : x ∈ EN := by
        rw [hEN_eq]; exact Subgroup.mem_inf.mpr ⟨OddOrder.BG.Ch3.S10.Msigma_le M₂ hxM₂σ, hxN⟩
      have hx_in : x ∈ Subgroup.normalizer ((MulAut.conj w • A₁ : Subgroup G) : Set G) ⊓
          OddOrder.BG.Ch3.S10.Msigma M₂ :=
        Subgroup.mem_inf.mpr ⟨hAnormalEN hxEN, hxM₂σ⟩
      -- If `p ∉ σ(M₂)` then `p ∈ τ₂(M₂)` (rank 2), so Cor 12.6(b) kills `N_{M₂σ}(A)` —
      -- contradiction.
      by_contra hpσM₂
      have hAM₂_pi : Subgroup.IsPiSubgroup ((OddOrder.BG.Ch3.S10.sigma M₂)ᶜ)
          (MulAut.conj w • A₁) := by
        intro r hr
        rw [hA.2, Nat.primeFactors_pow p two_ne_zero, Nat.Prime.primeFactors hpp,
          Finset.mem_singleton] at hr
        rw [hr]; exact hpσM₂
      obtain ⟨EM₂, _, _, _, hM₂_E, hAEM₂, _⟩ :=
        exists_subgroupESetup_with_le hG hM₂max hAM₂ hAM₂_pi
      have hpτ2M₂ : p ∈ tau2 M₂ := by
        rw [mem_tau2_iff]
        have hpcardEM₂ : p ∈ (Nat.card ↥EM₂).primeFactors := by
          refine Nat.mem_primeFactors.mpr ⟨hpp, ?_, Nat.card_pos.ne'⟩
          have hpA : p ∣ Nat.card ↥(MulAut.conj w • A₁) := by
            rw [hA.2]; exact dvd_pow_self p two_ne_zero
          exact hpA.trans (Subgroup.card_dvd_of_le hAEM₂)
        refine ⟨hpσM₂, le_antisymm (hM₂_E.pRank_M_le_two hG hpcardEM₂) ?_⟩
        have hAea' : ((MulAut.conj w • A₁).subgroupOf M₂).IsElementaryAbelian p :=
          IsElementaryAbelian.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hAM₂).symm
            (mem_elemAbelianOfRank.mp hA).1
        have h := le_pRank ((MulAut.conj w • A₁).subgroupOf M₂) hAea'
        rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM₂).toEquiv, hA.2,
          Nat.log_pow hpp.one_lt] at h
      have hbot := Msigma_inf_normalizer_eq_bot_of_tau2 hG hM₂_E hpτ2M₂ hA hAEM₂
      rw [hbot, Subgroup.mem_bot] at hx_in
      exact hx hx_in
    · -- (d) `σ(N) ∩ π(M₂) ⊆ β(N)`.
      intro r hr; exact hdN₂ r hr.2 hr.1
    · -- (e) `M₂ ∩ N` complements `N_σ` in `N` (Proposition 12.15(e)'s `⊓ = ⊥`, `⊔ = N`).
      have hinf₂' : Disjoint ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          ((M₂ ⊓ N).subgroupOf N) := by
        rw [disjoint_iff, eq_bot_iff]
        rintro a ha
        rw [Subgroup.mem_inf] at ha
        have hav : (a : G) ∈ (⊥ : Subgroup G) := by
          rw [← hsigmaInf₂]
          exact Subgroup.mem_inf.mpr
            ⟨Subgroup.mem_subgroupOf.mp ha.1, Subgroup.mem_subgroupOf.mp ha.2⟩
        rw [Subgroup.mem_bot] at hav
        rw [Subgroup.mem_bot]; exact OneMemClass.coe_eq_one.mp hav
      have hsup₂' : (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N ⊔ (M₂ ⊓ N).subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hMσN_le inf_le_right, hsigmaSup₂, Subgroup.subgroupOf_self]
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hinf₂'
      rw [← Subgroup.normal_mul, hsup₂', Subgroup.coe_top]
    · -- **(Sharp transitivity)**: `R(x) = N_σ ∩ C_G(x)` acts regularly on `𝓜_σ(x)`
      -- (BG L3896-3900). For `L ∈ 𝓜_σ(x)`: `L = M₂^c` for some `c ∈ C_G(X)` (Theorem 10.1(b)
      -- fusion); write `c = v·a`, `v ∈ N_σ`, `a ∈ M₂∩N` (complement `N = N_σ(M₂∩N)`), so
      -- `conj v • M₂ = L`. Then `conj (x⁻¹vx) • M₂ = conj v • M₂` + freeness (`N_G(M₂)∩N_σ = 1`)
      -- forces `x⁻¹vx = v`, i.e. `v ∈ C_G(x)`; uniqueness is the same freeness argument.
      intro L hLmem
      obtain ⟨hLmax, hxLσ⟩ := hLmem
      have hxM₂mem : x ∈ M₂ := OddOrder.BG.Ch3.S10.Msigma_le M₂ hxM₂σ
      have hxLmem : x ∈ L := OddOrder.BG.Ch3.S10.Msigma_le L hxLσ
      -- `N_G(M₂) = M₂` (maximal ⟹ self-normalizing).
      have hM₂ne : M₂ ≠ ⊥ := fun hb => hXne (le_bot_iff.mp (hb ▸ hXM₂le))
      have hN_M₂_le : Subgroup.normalizer M₂ ≤ M₂ := by
        rcases eq_or_lt_of_le (Subgroup.le_normalizer (H := M₂)) with heq | hlt
        · exact heq.ge
        · rcases hG.simple.eq_bot_or_eq_top_of_normal M₂
              (Subgroup.normalizer_eq_top_iff.mp
                ((mem_maximalSubgroups.mp hM₂max).2 _ hlt)) with hb | ht
          · exact absurd hb hM₂ne
          · exact absurd ht (mem_maximalSubgroups.mp hM₂max).1
      -- `L` conjugate to `M₂` (else Thm 13.9 σ-disjoint, but `q ∈ σ(M₂) ∩ σ(L)`).
      have hqσL : q ∈ OddOrder.BG.Ch3.S10.sigma L :=
        OddOrder.BG.Ch3.S10.Msigma_isPiGroup L q (Nat.mem_primeFactors.mpr
          ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma L).orderOf_dvd_natCard hxLσ),
            Nat.card_pos.ne'⟩)
      obtain ⟨gL, hgL⟩ : ∃ g : G, MulAut.conj g • M₂ = L := by
        by_contra hnc
        exact Set.disjoint_left.mp
          (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM₂max hLmax hnc) hqσM₂ hqσL
      -- Fusion (Theorem 10.1(b)): `c ∈ C_G(X)` with `conj c • M₂ = L`.
      have hXLle : X ≤ L :=
        (hXx.trans (Subgroup.zpowers_le.mpr hxLσ)).trans (OddOrder.BG.Ch3.S10.Msigma_le L)
      have hXM₂' : X ≤ MulAut.conj (1 : G) • M₂ := by rw [map_one, one_smul]; exact hXM₂le
      have hXgL : X ≤ MulAut.conj gL • M₂ := by rw [hgL]; exact hXLle
      obtain ⟨c, hcC, hcconj⟩ :=
        (OddOrder.BG.Ch3.S10.fusion_control_of_mem_sigma hG hM₂max hqσM₂ hXne hXq).2.1 1 gL
          hXM₂' hXgL
      rw [map_one, one_smul] at hcconj
      have hcL : MulAut.conj c • M₂ = L := by rw [hcconj, hgL]
      -- `c ∈ N`; decompose `c = v · a` with `v ∈ N_σ`, `a ∈ M₂ ⊓ N`.
      have hcN : c ∈ N := ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNge) hcC
      have hsup₂'' :
          (OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N ⊔ (M₂ ⊓ N).subgroupOf N = ⊤ := by
        rw [← Subgroup.subgroupOf_sup hMσN_le inf_le_right, hsigmaSup₂,
          Subgroup.subgroupOf_self]
      have hc'mem : (⟨c, hcN⟩ : ↥N) ∈
          (↑((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N) *
            ↑((M₂ ⊓ N).subgroupOf N) : Set ↥N) := by
        rw [← Subgroup.normal_mul, hsup₂'']; exact Subgroup.mem_top _
      obtain ⟨vsub, hvsub, asub, hasub, hva⟩ := hc'mem
      have hvMσ : (vsub : G) ∈ OddOrder.BG.Ch3.S10.Msigma N := Subgroup.mem_subgroupOf.mp hvsub
      have haM₂ : (asub : G) ∈ M₂ :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hasub)).1
      have hcva : (vsub : G) * (asub : G) = c := by
        have := congrArg (Subgroup.subtype N) hva; simpa using this
      -- `conj v • M₂ = L` (as `a ∈ M₂`).
      have hvL : MulAut.conj (vsub : G) • M₂ = L := by
        have ha_fix : MulAut.conj (asub : G) • M₂ = M₂ :=
          conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer haM₂)
        rw [← hcL, ← hcva, map_mul, mul_smul, ha_fix]
      -- `x⁻¹vx ∈ N_σ`; `conj (x⁻¹vx) • M₂ = conj v • M₂` (uses `x∈M₂`, `x∈L`).
      have hconjMσ : x⁻¹ * (vsub : G) * x ∈ OddOrder.BG.Ch3.S10.Msigma N := by
        have h := hMσNnormal.conj_mem vsub hvsub (⟨x, hxN⟩⁻¹)
        have := Subgroup.mem_subgroupOf.mp h; simpa using this
      have hkey :
          MulAut.conj (x⁻¹ * (vsub : G) * x) • M₂ = MulAut.conj (vsub : G) • M₂ := by
        have hxM₂ : MulAut.conj x • M₂ = M₂ :=
          conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hxM₂mem)
        have hxL : MulAut.conj x⁻¹ • L = L :=
          conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (L.inv_mem hxLmem))
        calc MulAut.conj (x⁻¹ * (vsub : G) * x) • M₂
            = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • (MulAut.conj x • M₂)) := by
              rw [map_mul, map_mul, mul_smul, mul_smul]
          _ = MulAut.conj x⁻¹ • (MulAut.conj (vsub : G) • M₂) := by rw [hxM₂]
          _ = MulAut.conj x⁻¹ • L := by rw [hvL]
          _ = L := hxL
          _ = MulAut.conj (vsub : G) • M₂ := hvL.symm
      have hmemNM : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ Subgroup.normalizer M₂ := by
        apply mem_normalizer_of_conj_smul_eq_self
        rw [map_mul, mul_smul, hkey, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
      have hmemMσ : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ OddOrder.BG.Ch3.S10.Msigma N :=
        (OddOrder.BG.Ch3.S10.Msigma N).mul_mem
          ((OddOrder.BG.Ch3.S10.Msigma N).inv_mem hvMσ) hconjMσ
      have hmem1 : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) = 1 := by
        have hinbot : (vsub : G)⁻¹ * (x⁻¹ * (vsub : G) * x) ∈ (⊥ : Subgroup G) := by
          rw [← hsigmaInf₂]
          exact Subgroup.mem_inf.mpr ⟨hmemMσ,
            Subgroup.mem_inf.mpr ⟨hN_M₂_le hmemNM, hMσN_le hmemMσ⟩⟩
        exact Subgroup.mem_bot.mp hinbot
      have hvx : x⁻¹ * (vsub : G) * x = (vsub : G) := (inv_mul_eq_one.mp hmem1).symm
      have hvCx : (vsub : G) ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy; rw [Set.mem_singleton_iff.mp hy]
        have hcomm : x * (vsub : G) = (vsub : G) * x := by nth_rewrite 1 [← hvx]; group
        exact hcomm
      -- Existence + uniqueness of `r ∈ R(x)` with `conj r • M₂ = L`.
      refine ⟨(vsub : G), ⟨Subgroup.mem_inf.mpr ⟨hvMσ, hvCx⟩, hvL⟩, ?_⟩
      rintro r ⟨hrR, hrL⟩
      obtain ⟨hrMσ, _hrCx⟩ := Subgroup.mem_inf.mp hrR
      have hconj_eq : MulAut.conj ((vsub : G)⁻¹ * r) • M₂ = M₂ := by
        rw [map_mul, mul_smul, hrL, ← hvL, ← mul_smul, ← map_mul, inv_mul_cancel,
          map_one, one_smul]
      have hmemN' : (vsub : G)⁻¹ * r ∈ Subgroup.normalizer M₂ :=
        mem_normalizer_of_conj_smul_eq_self hconj_eq
      have hmemMσ' : (vsub : G)⁻¹ * r ∈ OddOrder.BG.Ch3.S10.Msigma N :=
        (OddOrder.BG.Ch3.S10.Msigma N).mul_mem
          ((OddOrder.BG.Ch3.S10.Msigma N).inv_mem hvMσ) hrMσ
      have hbot' : (vsub : G)⁻¹ * r ∈ (⊥ : Subgroup G) := by
        rw [← hsigmaInf₂]
        exact Subgroup.mem_inf.mpr ⟨hmemMσ',
          Subgroup.mem_inf.mpr ⟨hN_M₂_le hmemN', hMσN_le hmemMσ'⟩⟩
      exact (inv_mul_eq_one.mp (Subgroup.mem_bot.mp hbot')).symm
  · -- Uniqueness: any qualifying `N'` lies in `ℳ(C_G(x)) = {N}`.
    intro N' hN'
    have hmem : N' ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) :=
      mem_maximalSubgroupsContaining.mpr ⟨mem_maximalSubgroups.mp hN'.1, hN'.2.1⟩
    rw [hsingleton] at hmem
    exact Set.mem_singleton_iff.mp hmem

/-- **σ-classes are equal or disjoint** (BG §1 partition, mmd L3789): if two maximal subgroups
share a `σ`-prime then their `σ`-sets coincide.  Combines Theorem 13.9 (nonconjugate ⟹ disjoint
`σ`) with the conjugation-equivariance of `σ` (`sigma_conj`).  This is the partition property the
`σ`-decomposition rests on; used to match the `σ`-factors of an element in Lemma 14.5(a). -/
theorem sigma_eq_of_mem_sigma_of_mem_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M M' : Subgroup G}
    (hM : M ∈ maximalSubgroups G) (hM' : M' ∈ maximalSubgroups G) {p : ℕ}
    (hpM : p ∈ OddOrder.BG.Ch3.S10.sigma M) (hpM' : p ∈ OddOrder.BG.Ch3.S10.sigma M') :
    OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma M' := by
  -- `M`, `M'` are conjugate (else Theorem 13.9 makes their `σ`-sets disjoint).
  obtain ⟨g, rfl⟩ : IsConjugateSubgroup M M' := by
    by_contra hnc
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM hM' hnc) hpM hpM'
  ext q
  refine ⟨fun hq => ?_, fun hq => ?_⟩
  · have : Fact q.Prime :=
      ⟨Nat.prime_of_mem_primeFactors ((OddOrder.BG.Ch3.S10.mem_sigma_iff M q).mp hq).1⟩
    exact OddOrder.BG.Ch3.S10.sigma_conj g hq
  · have : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors
      ((OddOrder.BG.Ch3.S10.mem_sigma_iff (MulAut.conj g • M) q).mp hq).1⟩
    have h := OddOrder.BG.Ch3.S10.sigma_conj g⁻¹ hq
    rwa [← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul] at h

/-- **Every prime divides some `σ(M)`** (BG §1, mmd L3789): for a prime `p ∣ |G|` there is a
maximal subgroup `M` with `p ∈ σ(M)`.  A Sylow `p`-subgroup `P` of `G` is non-normal (else `G`
would be a `p`-group, hence solvable, against `hG.notSolvable`), so `N_G(P)` lies in a maximal `M`;
then `P` is a Sylow `p`-subgroup of `M` whose `G`-normalizer `N_G(P) ≤ M`, which is exactly
`p ∈ σ(M)`.  Foundation for the σ-decomposition (every nonidentity element has a `σ`-piece). -/
theorem exists_mem_sigma_of_prime_dvd_card [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {p : ℕ} [Fact p.Prime] (hpG : p ∣ Nat.card G) :
    ∃ M : Subgroup G, M ∈ maximalSubgroups G ∧ p ∈ OddOrder.BG.Ch3.S10.sigma M := by
  classical
  have : IsSimpleGroup G := hG.simple
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  have hPcard : Nat.card ↥(P : Subgroup G) = p ^ (Nat.card G).factorization p :=
    P.card_eq_multiplicity
  have hfactG : (Nat.card G).factorization p ≠ 0 :=
    (Nat.Prime.factorization_pos_of_dvd Fact.out (Nat.card_pos).ne' hpG).ne'
  have hPne : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hpG
  have hNne : Subgroup.normalizer ((P : Subgroup G) : Set G) ≠ ⊤ := by
    intro hN_top
    have hPnormal : (P : Subgroup G).Normal := Subgroup.normalizer_eq_top_iff.mp hN_top
    rcases hPnormal.eq_bot_or_eq_top with hb | ht
    · exact hPne hb
    · refine hG.notSolvable ?_
      have hPG : IsPGroup p G := by
        have he : IsPGroup p ↥(⊤ : Subgroup G) := ht ▸ P.isPGroup'
        exact he.of_equiv Subgroup.topEquiv
      have := hPG.isNilpotent
      infer_instance
  obtain ⟨M, hMco, hNM⟩ := (eq_top_or_exists_le_coatom _).resolve_left hNne
  have hM : M ∈ maximalSubgroups G := mem_maximalSubgroups.mpr hMco
  have hPM : (P : Subgroup G) ≤ M := Subgroup.le_normalizer.trans hNM
  have hpP : p ∣ Nat.card ↥(P : Subgroup G) := by
    rw [hPcard]; exact dvd_pow_self p hfactG
  have hpdvdM : p ∣ Nat.card ↥M := hpP.trans (Subgroup.card_dvd_of_le hPM)
  have hpM : p ∈ (Nat.card ↥M).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Fact.out, hpdvdM, (Nat.card_pos).ne'⟩
  refine ⟨M, hM, ?_⟩
  rw [OddOrder.BG.Ch3.S10.mem_sigma_iff]
  refine ⟨hpM, ?_⟩
  -- `P` is a Sylow `p`-subgroup of `M` (the `p`-parts of `|M|` and `|G|` agree).
  have hmap : ((P : Subgroup G).subgroupOf M).map M.subtype = (P : Subgroup G) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPM]
  have hcardPM : Nat.card ↥((P : Subgroup G).subgroupOf M) = Nat.card ↥(P : Subgroup G) := by
    have h := Nat.card_congr (Subgroup.equivMapOfInjective
      ((P : Subgroup G).subgroupOf M) M.subtype M.subtype_injective).toEquiv
    rwa [hmap] at h
  have hfacteq : (Nat.card G).factorization p = (Nat.card ↥M).factorization p := by
    refine le_antisymm ?_ ?_
    · rw [← Nat.Prime.pow_dvd_iff_le_factorization Fact.out (Nat.card_pos).ne', ← hPcard]
      exact Subgroup.card_dvd_of_le hPM
    · exact (Nat.factorization_le_iff_dvd (Nat.card_pos).ne' (Nat.card_pos).ne').mpr
        (Subgroup.card_subgroup_dvd_card M) p
  have hQcard : Nat.card ↥((P : Subgroup G).subgroupOf M)
      = p ^ (Nat.card ↥M).factorization p := by rw [hcardPM, hPcard, hfacteq]
  refine ⟨Sylow.ofCard ((P : Subgroup G).subgroupOf M) hQcard, ?_⟩
  rw [Sylow.coe_ofCard, hmap]
  exact hNM

/-- **BG `ell_sigma0P`** (Coq BGsection14:222): the genuine σ-length of `x` is `0` iff `x = 1`.
If `x ≠ 1`, any prime `p ∣ orderOf x` divides `|G|`, hence is a `σ`-prime of some maximal `M`
(`exists_mem_sigma_of_prime_dvd_card`); then `sigmaPart M x ≠ 1` (else `x` would be a
`σ(M)′`-element
avoiding `p`), so `sigma_decomposition x` is nonempty.  (Placed after
`exists_mem_sigma_of_prime_dvd_card`, which it cites; the genuine `sigmaLength` is defined
earlier.) -/
theorem sigmaLength_eq_zero_iff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (x : G) :
    sigmaLength x = 0 ↔ x = 1 := by
  rw [sigmaLength, Set.ncard_eq_zero (Set.toFinite _)]
  constructor
  · intro hempty
    by_contra hx1
    have hox : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hox
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨M, hMmax, hpσ⟩ :=
      exists_mem_sigma_of_prime_dvd_card hG (hpdvd.trans (orderOf_dvd_natCard x))
    have hne : sigmaPart M x ≠ 1 := by
      intro hcontra
      have hcompl : IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ x :=
        isPiElement_compl_of_piPart_eq_one hcontra
      exact (hcompl p (Nat.mem_primeFactors.mpr ⟨hp, hpdvd, (orderOf_pos x).ne'⟩)) hpσ
    have hmem : sigmaPart M x ∈ sigmaDecomposition x := by
      refine ⟨⟨M, hMmax, rfl⟩, ?_⟩
      simp only [Set.mem_singleton_iff]; exact hne
    rw [hempty] at hmem
    exact Set.notMem_empty _ hmem
  · rintro rfl
    rw [Set.eq_empty_iff_forall_notMem]
    rintro y ⟨⟨M, hMmax, rfl⟩, hy⟩
    exact hy (by simp [sigmaPart, piPart_one])

/-- **σ-decomposition keystone** (BG §1, mmd L3793): a nonidentity `σ(M)`-element `x` has
`ℓ_σ(x) = 1`.  The cyclic group `⟨x⟩` is a nonidentity proper `σ(M)`-subgroup (proper since `G` is
non-solvable, hence non-cyclic), so by Corollary 12.16(a)
(`sigma_subgroup_conj_into_Msigma_general`) it is `G`-conjugate into `M_σ`; thus a conjugate of `M`
is a `σ`-maximal of `x`, giving `𝓜_σ(x) ≠ ∅`.  This is the existence half of the σ-decomposition
that drives Lemma 14.6 (extracting a `σ`-length-one factor of an element). -/
theorem exists_mem_Msigma_of_isPiElement_sigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ≠ 1) (hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) :
    (maximalSigmaSubgroupsOfElement x).Nonempty := by
  have hclosne : Subgroup.closure ({x} : Set G) ≠ ⊥ := fun h =>
    hx (Subgroup.mem_bot.mp (h ▸ Subgroup.subset_closure (Set.mem_singleton x)))
  have hlt : Subgroup.closure ({x} : Set G) < ⊤ := by
    refine lt_top_iff_ne_top.mpr (fun htop => hG.notSolvable
        (Group.isSolvable_of_comm fun a b => ?_))
    have hmem : ∀ y : G, y ∈ Subgroup.zpowers x := fun y => by
      rw [Subgroup.zpowers_eq_closure, htop]; exact Subgroup.mem_top y
    obtain ⟨m, rfl⟩ := hmem a
    obtain ⟨n, rfl⟩ := hmem b
    rw [← zpow_add, ← zpow_add, Int.add_comm]
  have hxpisub : Subgroup.IsPiSubgroup (OddOrder.BG.Ch3.S10.sigma M)
      (Subgroup.closure ({x} : Set G)) := fun p hp =>
    hxpi p (by rwa [← Subgroup.zpowers_eq_closure, Nat.card_zpowers] at hp)
  obtain ⟨g, hg⟩ := sigma_subgroup_conj_into_Msigma_general hG hM hclosne hlt hxpisub
    (fun hN hnc => sigma_disjoint_of_nonconjugate hG hM hN hnc)
  refine ⟨MulAut.conj g⁻¹ • M, mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g⁻¹, rfl⟩, ?_⟩
  rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  have he : (MulAut.conj g⁻¹)⁻¹ • x = MulAut.conj g • x := by
    rw [← map_inv (MulAut.conj) g⁻¹, inv_inv]
  rw [he]
  exact hg (Subgroup.smul_mem_pointwise_smul x (MulAut.conj g) _
    (Subgroup.subset_closure (Set.mem_singleton x)))

/-- The scaffold form: a nonidentity `σ(M)`-element `x` has `D.length x = 1` (it cites the genuine
existence half `exists_mem_Msigma_of_isPiElement_sigma` through `D.length_one_iff`). -/
theorem length_one_of_isPiElement_sigma [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G) {x : G}
    (hx : x ≠ 1) (hxpi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M) x) :
    D.length x = 1 :=
  (D.length_one_iff x).mpr ⟨hx, exists_mem_Msigma_of_isPiElement_sigma hG hM hx hxpi⟩

/-- **BG `ell_sigma1P`** (Coq BGsection14:272): `sigmaLength x = 1 ↔ x ≠ 1 ∧ 𝓜_σ(x) ≠ ∅`.  This is
*exactly* the characterization the `SigmaDecompositionData` scaffold posits as `length_one_iff`,
here **proved** for the genuine `sigmaLength`.  ⟸ is `Msigma_ell1`.  ⟹: a σ-length-`1` element has
all its primes in one `σ(M₀)` (each prime `p ∣ |x|` lands in some `σ(L)`, forcing the nonidentity
`sigmaPart L x` to equal the unique block `y = sigmaPart M₀ x`, so `p ∈ π(y) ⊆ σ(M₀)`), hence is a
`σ(M₀)`-element, and the existence half `exists_mem_Msigma_of_isPiElement_sigma` finishes. -/
theorem sigmaLength_eq_one_iff [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (x : G) :
    sigmaLength x = 1 ↔ x ≠ 1 ∧ (maximalSigmaSubgroupsOfElement x).Nonempty := by
  constructor
  · intro hlen
    have hx1 : x ≠ 1 := by
      intro h
      rw [h, (sigmaLength_eq_zero_iff hG 1).mpr rfl] at hlen
      exact zero_ne_one hlen
    refine ⟨hx1, ?_⟩
    obtain ⟨y, hy⟩ := Set.ncard_eq_one.mp hlen
    have hyMem : y ∈ sigmaDecomposition x := by rw [hy]; rfl
    obtain ⟨⟨M₀, hM₀, hy_eq⟩, hyne⟩ := hyMem
    have hxσ : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M₀) x := by
      intro p hp
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      obtain ⟨L, hL, hpL⟩ := exists_mem_sigma_of_prime_dvd_card hG
        ((Nat.dvd_of_mem_primeFactors hp).trans (orderOf_dvd_natCard x))
      have hLne : sigmaPart L x ≠ 1 := fun hc =>
        isPiElement_compl_of_piPart_eq_one hc p hp hpL
      have hLmem : sigmaPart L x ∈ sigmaDecomposition x :=
        ⟨⟨L, hL, rfl⟩, by simp only [Set.mem_singleton_iff]; exact hLne⟩
      rw [hy, Set.mem_singleton_iff] at hLmem
      have hpy : p ∣ orderOf (sigmaPart M₀ x) := by
        rw [← hy_eq, ← hLmem]
        exact prime_dvd_orderOf_piPart (Nat.prime_of_mem_primeFactors hp) hpL
          (Nat.dvd_of_mem_primeFactors hp)
      exact isPiElement_piPart (OddOrder.BG.Ch3.S10.sigma M₀) x p
        (Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors hp, hpy, (orderOf_pos _).ne'⟩)
    exact exists_mem_Msigma_of_isPiElement_sigma hG hM₀ hx1 hxσ
  · rintro ⟨hx1, M, hM, hxM⟩
    exact Msigma_ell1 hG hM hxM hx1

/-- The **genuine** `SigmaDecompositionData`: `length := sigmaLength` (the honestly constructed
σ-length) with `length_one_iff` discharged by `sigmaLength_eq_one_iff` (Coq `ell_sigma1P`).  This
*realizes* the carrier the scaffold only posited — downstream consumers can be fed this in place of
`dummySigmaDecomposition` ([[scaffold-sorry-free-not-done]]: the posited interface is
constructible). -/
noncomputable def genuineSigmaDecomposition [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) : SigmaDecompositionData G where
  length := sigmaLength
  length_one_iff := sigmaLength_eq_one_iff hG

open Classical in
/-- **BG's `R(x)`** (mmd L3906): the normal Hall subgroup of `C_G(x)` from Theorem 14.4.  When
`ℓ_σ(x) = 1` and `|𝓜_σ(x)| > 1`, `R(x) = N_σ ∩ C_G(x)` for the unique `N = N(x) ∈ 𝓜(C_G(x))`
of Theorem 14.4; otherwise (`x = 1`, `ℓ_σ(x) ≠ 1`, or `|𝓜_σ(x)| = 1`) `R(x) = 1`. -/
noncomputable def Rsub [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (x : G) : Subgroup G :=
  if h : x ≠ 1 ∧ D.length x = 1 ∧ 1 < (maximalSigmaSubgroupsOfElement x).ncard then
    OddOrder.BG.Ch3.S10.Msigma
        (((sigmaLength_one_centralizer_structure hG D h.1 h.2.1).2 h.2.2).exists.choose)
      ⊓ Subgroup.centralizer ({x} : Set G)
  else ⊥

/-- `R(x) ≤ C_G(x)` (immediate from the definition; holds in both branches). -/
theorem Rsub_le_centralizer [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) (x : G) :
    Rsub hG D x ≤ Subgroup.centralizer ({x} : Set G) := by
  rw [Rsub]; split_ifs
  · exact inf_le_right
  · exact bot_le

/-- The defining value of `R(x)` in the multi-maximal case: `R(x) = N_σ ∩ C_G(x)` for the
unique `N` of Theorem 14.4 (`.exists.choose`). -/
theorem Rsub_eq_inf [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hx : x ≠ 1) (hlen : D.length x = 1)
    (hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard) :
    Rsub hG D x = OddOrder.BG.Ch3.S10.Msigma
      (((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose)
      ⊓ Subgroup.centralizer ({x} : Set G) := by
  rw [Rsub, dif_pos ⟨hx, hlen, hgt⟩]

/-- **Packaged neighbour data for `R(x)`** (the multi-maximal case): the unique `N = N(x)` of
Theorem 14.4 together with `R(x) = N_σ ∩ C_G(x)`, `C_G(x) ≤ N`, `π(⟨x⟩) ⊆ τ₂(N)`, and the
complement property `M ∩ N` complements `N_σ` in `N` for every `M ∈ 𝓜_σ(x)` (14.4(e)).  This
is the interface consumed by Lemma 14.5(a)/(c) and Lemma 14.6. -/
theorem exists_neighbor_eq_Rsub [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hlen : D.length x = 1)
    (hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ N : Subgroup G, N ∈ maximalSubgroups G ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      Rsub hG D x = OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ∧
      (∀ p ∈ piSet (Subgroup.closure ({x} : Set G)), p ∈ tau2 N) ∧
      (∀ M ∈ maximalSigmaSubgroupsOfElement x,
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          ((M ⊓ N).subgroupOf N)) := by
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  set N := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose with hNdef
  have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
  refine ⟨N, spec.1, spec.2.1, Rsub_eq_inf hG D hx hlen hgt, spec.2.2.2.2.1, fun M hM => ?_⟩
  exact (spec.2.2.2.2.2.2 M hM).2.2.1

/-- **`R(z)` consists of `σ(M)′`-elements** for `M ∈ 𝓜_σ(z)`.  Crux of the σ-factor matching
in Lemma 14.5(a): with `z` a `σ(M)`-element, `g = z·r` (`r ∈ R(z)`) is a `(σ(M), σ(M)′)`-split.
Proof: `r ∈ N_σ` is a `σ(N)`-element (`N = N(z)`); a prime `p ∈ σ(M) ∩ σ(N)` forces
`σ(M) = σ(N)` (partition), but `π(⟨z⟩) ⊆ σ(M) = σ(N)` and `⊆ τ₂(N)` with `τ₂(N) ∩ σ(N) = ∅`
gives `z = 1`. (When `|𝓜_σ(z)| = 1`, `R(z) = 1`, trivially.) -/
theorem isPiElement_sigmaCompl_of_mem_Rsub [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G) {z : G}
    (hlen : D.length z = 1) {M : Subgroup G} (hM : M ∈ maximalSigmaSubgroupsOfElement z)
    {r : G} (hr : r ∈ Rsub hG D z) :
    OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M)ᶜ r := by
  intro p hp
  rw [Set.mem_compl_iff]
  intro hpσM
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement z).ncard
  · obtain ⟨N, hNmax, _, hReq, hπτ2, _⟩ := exists_neighbor_eq_Rsub hG D hlen hgt
    rw [hReq] at hr
    have hrN : r ∈ OddOrder.BG.Ch3.S10.Msigma N := (Subgroup.mem_inf.mp hr).1
    -- `p ∈ σ(N)` since `r ∈ N_σ`.
    have hpσN : p ∈ OddOrder.BG.Ch3.S10.sigma N :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup N p (Nat.mem_primeFactors.mpr
        ⟨Nat.prime_of_mem_primeFactors hp,
          (Nat.dvd_of_mem_primeFactors hp).trans
            ((OddOrder.BG.Ch3.S10.Msigma N).orderOf_dvd_natCard hrN),
          Nat.card_pos.ne'⟩)
    -- `σ(M) = σ(N)` since they share `p`.
    have hσeq : OddOrder.BG.Ch3.S10.sigma M = OddOrder.BG.Ch3.S10.sigma N :=
      sigma_eq_of_mem_sigma_of_mem_sigma hG hM.1 hNmax hpσM hpσN
    -- A prime `q ∣ |z|` lies in `σ(M)=σ(N)` and `τ₂(N)`, against `τ₂(N) ⊆ σ(N)ᶜ`.
    have hz1 : z ≠ 1 := ((D.length_one_iff z).mp hlen).1
    obtain ⟨q, hqp, hqdvd⟩ :=
      (orderOf z).exists_prime_and_dvd (fun h => hz1 (orderOf_eq_one_iff.mp h))
    have hcardz : Nat.card ↥(Subgroup.closure ({z} : Set G)) = orderOf z := by
      rw [← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
    have hqπ : q ∈ piSet (Subgroup.closure ({z} : Set G)) := by
      rw [piSet, Set.mem_ofPred_eq, hcardz]
      exact Nat.mem_primeFactors.mpr ⟨hqp, hqdvd, (orderOf_pos z).ne'⟩
    have hqσM : q ∈ OddOrder.BG.Ch3.S10.sigma M :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M q (Nat.mem_primeFactors.mpr
        ⟨hqp, hqdvd.trans ((OddOrder.BG.Ch3.S10.Msigma M).orderOf_dvd_natCard hM.2),
          Nat.card_pos.ne'⟩)
    rw [hσeq] at hqσM
    exact tau2_subset_sigma_compl N (hπτ2 q hqπ) hqσM
  · rw [Rsub, dif_neg (fun h => hgt h.2.2), Subgroup.mem_bot] at hr
    rw [hr, orderOf_one, Nat.primeFactors_one] at hp
    simp at hp

/-- **Sharp transitivity ⟹ `|R(x)| = |𝓜_σ(x)|`** (BG Theorem 14.4 headline): `R(x) = N_σ ∩ C_G(x)`
acts *regularly* on `𝓜_σ(x)` by conjugation (`r ↦ M₀ʳ`), so the two have equal cardinality.  In the
single-maximal case both sides equal `1` (`R(x) = 1`, `|𝓜_σ(x)| = 1`).  This is the per-element
input to the double count of Lemma 14.5(c). -/
theorem Rsub_ncard_eq [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x : G} (hlen : D.length x = 1) :
    Nat.card ↥(Rsub hG D x) = (maximalSigmaSubgroupsOfElement x).ncard := by
  classical
  have hx : x ≠ 1 := ((D.length_one_iff x).mp hlen).1
  have hne : (maximalSigmaSubgroupsOfElement x).Nonempty := ((D.length_one_iff x).mp hlen).2
  have hfin : (maximalSigmaSubgroupsOfElement x).Finite := Set.toFinite _
  by_cases hgt : 1 < (maximalSigmaSubgroupsOfElement x).ncard
  · -- Multi-maximal: the orbit map `r ↦ M₀ʳ` is a bijection `R(x) ≃ 𝓜_σ(x)` by sharp transitivity.
    obtain ⟨M0, hM0⟩ := hne
    have hReq : Rsub hG D x =
        OddOrder.BG.Ch3.S10.Msigma
          (((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose)
          ⊓ Subgroup.centralizer ({x} : Set G) :=
      Rsub_eq_inf hG D hx hlen hgt
    have spec := ((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose_spec
    have hsharp := (spec.2.2.2.2.2.2 M0 hM0).2.2.2
    have hmem : ∀ r ∈ Rsub hG D x, MulAut.conj r • M0 ∈ maximalSigmaSubgroupsOfElement x := by
      intro r hr
      have hrC : r ∈ Subgroup.centralizer ({x} : Set G) := Rsub_le_centralizer hG D x hr
      have hrx : r * x = x * r := (Subgroup.mem_centralizer_iff.mp hrC x rfl).symm
      refine ⟨mem_maximalSubgroups_of_isConjugateSubgroup hM0.1 ⟨r, rfl⟩, ?_⟩
      rw [Msigma_conj_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
      have hxfix : (MulAut.conj r)⁻¹ • x = x := by
        have h1 : (MulAut.conj r)⁻¹ • x = r⁻¹ * x * r := by
          rw [← map_inv (MulAut.conj) r, MulAut.smul_def, MulAut.conj_apply, inv_inv]
        rw [h1, mul_assoc, ← hrx, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hxfix]; exact hM0.2
    -- The forward orbit map (into `𝓜_σ(x)`) and its bijectivity.
    have hpred : ∀ r ∈ Rsub hG D x,
        r ∈ OddOrder.BG.Ch3.S10.Msigma
          (((sigmaLength_one_centralizer_structure hG D hx hlen).2 hgt).exists.choose)
          ⊓ Subgroup.centralizer ({x} : Set G) := fun r hr => hReq ▸ hr
    let f : ↥(Rsub hG D x) → ↥(maximalSigmaSubgroupsOfElement x) :=
      fun r => ⟨MulAut.conj (r : G) • M0, hmem r r.2⟩
    have hbij : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro ⟨r1, hr1⟩ ⟨r2, hr2⟩ heq
        have hL : MulAut.conj r1 • M0 = MulAut.conj r2 • M0 := congrArg Subtype.val heq
        exact Subtype.ext
          ((hsharp (MulAut.conj r1 • M0) (hmem r1 hr1)).unique
            ⟨hpred r1 hr1, rfl⟩ ⟨hpred r2 hr2, hL.symm⟩)
      · rintro ⟨L, hL⟩
        obtain ⟨r, hrpred, -⟩ := hsharp L hL
        exact ⟨⟨r, hReq ▸ hrpred.1⟩, Subtype.ext hrpred.2⟩
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.ofBijective f hbij)
  · -- Single-maximal: `R(x) = 1` and `|𝓜_σ(x)| = 1`.
    have hpos : 0 < (maximalSigmaSubgroupsOfElement x).ncard := by
      rw [Set.ncard_pos hfin]; exact hne
    have h1 : (maximalSigmaSubgroupsOfElement x).ncard = 1 := by omega
    rw [h1, Rsub, dif_neg (fun h => hgt h.2.2)]
    simp

/-- **BG Lemma 14.5(a)** (mmd L3919): for distinct `σ`-length-one elements `x`, `y`, the cosets
`x R(x)` and `y R(y)` are disjoint.  Proof (s-part-free, via the two-block decomposition):
`g = x·x'` makes `x` the `σ(M_x)`-part of `g`, `g = y·y''` makes `y` the `σ(M_y)`-part.  If the
`σ`-classes agree, `x = y` (contradiction); otherwise some prime of `y` forces `σ(M_y) = σ(N_x)`,
so `x' = y` and `x = y''`, and then Theorem 14.4(e) (`N_y ∩ N_x` complements `(N_x)_σ`) gives
`y ∈ (N_x)_σ ∩ N_y = 1`, a contradiction. -/
theorem xRsub_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {x y : G} (hx : D.length x = 1) (hy : D.length y = 1)
    (hxy : x ≠ y) :
    Disjoint {g : G | ∃ r ∈ Rsub hG D x, g = x * r}
      {g : G | ∃ r ∈ Rsub hG D y, g = y * r} := by
  classical
  rw [Set.disjoint_left]
  rintro g ⟨x', hx'R, rfl⟩ ⟨y'', hy''R, hg2⟩
  -- `g = x · x'`, and `hg2 : x · x' = y · y''`.
  have hx1 : x ≠ 1 := ((D.length_one_iff x).mp hx).1
  have hy1 : y ≠ 1 := ((D.length_one_iff y).mp hy).1
  obtain ⟨M_x, hMxmax, hxMx⟩ := ((D.length_one_iff x).mp hx).2
  obtain ⟨M_y, hMymax, hyMy⟩ := ((D.length_one_iff y).mp hy).2
  -- `x` is a `σ(M_x)`-element, `y` a `σ(M_y)`-element.
  have hxPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) x := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M_x p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans
          ((OddOrder.BG.Ch3.S10.Msigma M_x).orderOf_dvd_natCard hxMx),
        Nat.card_pos.ne'⟩)
  have hyPi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y) y := fun p hp =>
    OddOrder.BG.Ch3.S10.Msigma_isPiGroup M_y p (Nat.mem_primeFactors.mpr
      ⟨Nat.prime_of_mem_primeFactors hp,
        (Nat.dvd_of_mem_primeFactors hp).trans
          ((OddOrder.BG.Ch3.S10.Msigma M_y).orderOf_dvd_natCard hyMy),
        Nat.card_pos.ne'⟩)
  -- `x'` is a `σ(M_x)′`-element, `y''` a `σ(M_y)′`-element (the crux building block).
  have hx'Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ x' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hx ⟨hMxmax, hxMx⟩ hx'R
  have hy''Pi : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y)ᶜ y'' :=
    isPiElement_sigmaCompl_of_mem_Rsub hG D hy ⟨hMymax, hyMy⟩ hy''R
  -- `x` commutes with `x'`, `y` with `y''`.
  have hcx : Commute x x' :=
    Subgroup.mem_centralizer_iff.mp (Rsub_le_centralizer hG D x hx'R) x (Set.mem_singleton x)
  have hcy : Commute y y'' :=
    Subgroup.mem_centralizer_iff.mp (Rsub_le_centralizer hG D y hy''R) y (Set.mem_singleton y)
  by_cases hσeq : OddOrder.BG.Ch3.S10.sigma M_x = OddOrder.BG.Ch3.S10.sigma M_y
  · -- **Equal classes**: both decompositions are `(σ(M_x), σ(M_x)′)`, so `x = y`.
    have ha2 : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x) y := by
      rw [hσeq]; exact hyPi
    have hb2 : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_x)ᶜ y'' := by
      rw [hσeq]; exact hy''Pi
    exact hxy (OddOrder.GroupTheory.isPiElement_mul_unique rfl hcx hxPi hx'Pi
      hg2.symm hcy ha2 hb2).1
  · -- **Disjoint classes**: `σ(M_x) ∩ σ(M_y) = ∅`.
    have hdisj : Disjoint (OddOrder.BG.Ch3.S10.sigma M_x) (OddOrder.BG.Ch3.S10.sigma M_y) :=
      Set.disjoint_left.mpr fun p hpx hpy =>
        hσeq (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hMymax hpx hpy)
    -- `x` is a `σ(M_y)′`-element (disjoint).
    have hxPiCompl : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y)ᶜ x := by
      intro p hp
      exact fun hpy => Set.disjoint_left.mp hdisj (hxPi p hp) hpy
    -- `π(g) = π(x) ∪ π(x')` (coprime commuting factors).
    have hcox : Nat.Coprime (orderOf x) (orderOf x') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hxPi hx'Pi
    have hpg : (orderOf (x * x')).primeFactors =
        (orderOf x).primeFactors ∪ (orderOf x').primeFactors := by
      rw [hcx.orderOf_mul_eq_mul_orderOf_of_coprime hcox,
        Nat.primeFactors_mul (orderOf_pos x).ne' (orderOf_pos x').ne']
    -- `π(y) ⊆ π(g)` (`y` is a factor of `g`).
    have hcoy : Nat.Coprime (orderOf y) (orderOf y'') :=
      OddOrder.GroupTheory.coprime_orderOf_of_isPiElement hyPi hy''Pi
    have hyg : (orderOf y).primeFactors ⊆ (orderOf (x * x')).primeFactors := by
      rw [hg2, hcy.orderOf_mul_eq_mul_orderOf_of_coprime hcoy,
        Nat.primeFactors_mul (orderOf_pos y).ne' (orderOf_pos y'').ne']
      exact Finset.subset_union_left
    -- `y ≠ 1` gives a prime `p ∈ π(y)`.
    obtain ⟨p, hpy⟩ : (orderOf y).primeFactors.Nonempty := by
      apply Nat.nonempty_primeFactors.mpr
      have h0 := orderOf_pos y
      have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
      omega
    have hpσMy : p ∈ OddOrder.BG.Ch3.S10.sigma M_y := hyPi p hpy
    -- `|𝓜_σ(x)| > 1`: else `x' = 1` and `p ∈ π(x) ⊆ σ(M_x)`, forcing `σ(M_x) = σ(M_y)`.
    by_cases hgtx : 1 < (maximalSigmaSubgroupsOfElement x).ncard
    · -- **Main case.**
      obtain ⟨N_x, hNxmax, _, hReqx, hπτ2x, hcomplx⟩ := exists_neighbor_eq_Rsub hG D hx hgtx
      have hx'Nx : x' ∈ OddOrder.BG.Ch3.S10.Msigma N_x := by
        rw [hReqx] at hx'R; exact (Subgroup.mem_inf.mp hx'R).1
      have hx'PiNx : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma N_x) x' :=
        fun q hq => OddOrder.BG.Ch3.S10.Msigma_isPiGroup N_x q (Nat.mem_primeFactors.mpr
          ⟨Nat.prime_of_mem_primeFactors hq,
            (Nat.dvd_of_mem_primeFactors hq).trans
              ((OddOrder.BG.Ch3.S10.Msigma N_x).orderOf_dvd_natCard hx'Nx),
            Nat.card_pos.ne'⟩)
      -- `p ∈ π(x) ∪ π(x')`; the `π(x)` case is impossible, so `σ(M_y) = σ(N_x)`.
      have hpmem : p ∈ (orderOf x).primeFactors ∪ (orderOf x').primeFactors := hpg ▸ hyg hpy
      have hσMyNx : OddOrder.BG.Ch3.S10.sigma M_y = OddOrder.BG.Ch3.S10.sigma N_x := by
        rcases Finset.mem_union.mp hpmem with hpx | hpx'
        · exact absurd
            (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hMymax (hxPi p hpx) hpσMy) hσeq
        · exact sigma_eq_of_mem_sigma_of_mem_sigma hG hMymax hNxmax hpσMy (hx'PiNx p hpx')
      -- Hence `x'` is a `σ(M_y)`-element; `g = x'·x` is a `(σ(M_y), σ(M_y)′)`-split.
      have hx'PiMy : OddOrder.GroupTheory.IsPiElement (OddOrder.BG.Ch3.S10.sigma M_y) x' := by
        rw [hσMyNx]; exact hx'PiNx
      obtain ⟨hx'y, hxy''⟩ := OddOrder.GroupTheory.isPiElement_mul_unique
        (g := x * x') hcx.symm hcx.symm hx'PiMy hxPiCompl hg2.symm hcy hyPi hy''Pi
      -- `x'=y`, `x=y''`; then `N_y ∈ 𝓜_σ(x)` and 14.4(e) give the contradiction.
      have hy_in_NxSigma : y ∈ OddOrder.BG.Ch3.S10.Msigma N_x := hx'y ▸ hx'Nx
      -- `x = y'' ∈ R(y) ⊆ (N_y)_σ`, so `|𝓜_σ(y)| > 1` and `N_y ∈ 𝓜_σ(x)`.
      have hgty : 1 < (maximalSigmaSubgroupsOfElement y).ncard := by
        by_contra h
        rw [Rsub, dif_neg (fun hc => h hc.2.2), Subgroup.mem_bot] at hy''R
        exact hx1 (hxy''.trans hy''R)
      obtain ⟨N_y, hNymax, hCyNy, hReqy, _, _⟩ := exists_neighbor_eq_Rsub hG D hy hgty
      have hx_in_NySigma : x ∈ OddOrder.BG.Ch3.S10.Msigma N_y := by
        rw [hReqy] at hy''R
        rw [hxy'']; exact (Subgroup.mem_inf.mp hy''R).1
      have hNy_mem : N_y ∈ maximalSigmaSubgroupsOfElement x := ⟨hNymax, hx_in_NySigma⟩
      -- Theorem 14.4(e) for `x` with `M = N_y`: `N_y ∩ N_x` complements `(N_x)_σ` in `N_x`.
      -- `y ∈ (N_x)_σ ∩ (N_y ∩ N_x)`, but the complement makes that trivial; so `y = 1`.
      have hcompl := hcomplx N_y hNy_mem
      have hyNx : y ∈ N_x := (OddOrder.BG.Ch3.S10.Msigma_le N_x) hy_in_NxSigma
      have hyNy : y ∈ N_y := hCyNy (Subgroup.mem_centralizer_iff.mpr fun z hz => by
        rw [Set.mem_singleton_iff.mp hz])
      have hmem : (⟨y, hyNx⟩ : ↥N_x) ∈
          (OddOrder.BG.Ch3.S10.Msigma N_x).subgroupOf N_x ⊓ (N_y ⊓ N_x).subgroupOf N_x := by
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact ⟨hy_in_NxSigma, Subgroup.mem_inf.mpr ⟨hyNy, hyNx⟩⟩
      have hd := hcompl.disjoint
      rw [disjoint_iff] at hd
      rw [hd, Subgroup.mem_bot] at hmem
      exact hy1 (by simpa using congrArg (Subgroup.subtype N_x) hmem)
    · -- single-maximal case (`x' = 1`, `g = x`): forces `σ(M_x) = σ(M_y)`, a contradiction.
      rw [Rsub, dif_neg (fun hc => hgtx hc.2.2), Subgroup.mem_bot] at hx'R
      rw [hx'R, mul_one] at hpg hyg
      have hpmem : p ∈ (orderOf x).primeFactors := by
        have := hyg hpy
        rwa [hpg, orderOf_one, Nat.primeFactors_one, Finset.union_empty] at this
      exact hσeq (sigma_eq_of_mem_sigma_of_mem_sigma hG hMxmax hMymax (hxPi p hpmem) hpσMy)

/-- **BG's `M̃`** (mmd L3908): `{ x x' | x ∈ M_σ^#, x' ∈ R(x) }`, the `σ`-decompositions of
length `≤ 2` with leading factor in `M_σ^#`.  This is the genuine BG `M̃` (it adjoins the
`ℓ_σ = 2` twisted elements `x x'` that the under-approximation `sigmaSharp` omits). -/
def Mtilde [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (D : SigmaDecompositionData G)
    (M : Subgroup G) : Set G :=
  {g | ∃ x ∈ sigmaSharp M, ∃ x' ∈ Rsub hG D x, g = x * x'}

/-- **Signalizer branch ⟹ `M̃` membership** (the bridge from BG's `sigma_decomposition_dichotomy`
first branch to the cover): if `x ∈ M_σ^#` and `x⁻¹ g ∈ R(x)`, then `g = x · (x⁻¹ g) ∈ x R(x) ⊆ M̃`.
This is the coset-to-`M̃` step used to turn the dichotomy's signalizer branch into a cover. -/
theorem mem_Mtilde_of_mem_coset [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M : Subgroup G} {x g : G}
    (hx : x ∈ sigmaSharp M) (hg : x⁻¹ * g ∈ Rsub hG D x) :
    g ∈ Mtilde hG D M :=
  ⟨x, hx, x⁻¹ * g, hg, by group⟩

/-- **BG Lemma 14.5(b)** (mmd L3920), faithful `M̃` form: for nonconjugate maximal `M₁`, `M₂`,
the sets `M̃₁`, `M̃₂` are disjoint.  Immediate from 14.5(a): if `g = x·x' = w·w'` with
`x ∈ (M₁)_σ^#`, `w ∈ (M₂)_σ^#`, then `x ≠ w` (else `x` is a nonidentity element of
`σ(M₁) ∩ σ(M₂) = ∅`), so `g ∈ x R(x) ∩ w R(w) = ∅`. -/
theorem Mtilde_disjoint [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (D : SigmaDecompositionData G) {M₁ M₂ : Subgroup G} (hM₁ : M₁ ∈ maximalSubgroups G)
    (hM₂ : M₂ ∈ maximalSubgroups G) (hnc : ¬ IsConjugateSubgroup M₁ M₂) :
    Disjoint (Mtilde hG D M₁) (Mtilde hG D M₂) := by
  classical
  rw [Set.disjoint_left]
  rintro g ⟨x, hxsharp, x', hx'R, rfl⟩ ⟨w, hwsharp, w', hw'R, hgw⟩
  rw [sigmaSharp, sharpSubgroup, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe]
    at hxsharp hwsharp
  obtain ⟨hxM₁, hx1⟩ := hxsharp
  obtain ⟨hwM₂, hw1⟩ := hwsharp
  have hlx : D.length x = 1 := (D.length_one_iff x).mpr ⟨hx1, ⟨M₁, hM₁, hxM₁⟩⟩
  have hlw : D.length w = 1 := (D.length_one_iff w).mpr ⟨hw1, ⟨M₂, hM₂, hwM₂⟩⟩
  -- `x ≠ w`: else a prime of `x` lies in `σ(M₁) ∩ σ(M₂) = ∅`.
  have hxw : x ≠ w := by
    rintro rfl
    obtain ⟨p, hp, hpx⟩ :=
      (orderOf x).exists_prime_and_dvd (fun h => hx1 (orderOf_eq_one_iff.mp h))
    have hpσ1 : p ∈ OddOrder.BG.Ch3.S10.sigma M₁ :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₁ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpx.trans ((OddOrder.BG.Ch3.S10.Msigma M₁).orderOf_dvd_natCard hxM₁),
          Nat.card_pos.ne'⟩)
    have hpσ2 : p ∈ OddOrder.BG.Ch3.S10.sigma M₂ :=
      OddOrder.BG.Ch3.S10.Msigma_isPiGroup M₂ p (Nat.mem_primeFactors.mpr
        ⟨hp, hpx.trans ((OddOrder.BG.Ch3.S10.Msigma M₂).orderOf_dvd_natCard hwM₂),
          Nat.card_pos.ne'⟩)
    exact Set.disjoint_left.mp
      (OddOrder.BG.Ch3.S13.sigma_disjoint_of_nonconjugate hG hM₁ hM₂ hnc) hpσ1 hpσ2
  exact Set.disjoint_left.mp (xRsub_disjoint hG D hlx hlw hxw)
    ⟨x', hx'R, rfl⟩ ⟨w', hw'R, hgw⟩

end OddOrder.BG.Ch4.S14


