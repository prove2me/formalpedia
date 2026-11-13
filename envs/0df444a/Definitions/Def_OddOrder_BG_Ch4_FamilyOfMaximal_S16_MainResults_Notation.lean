-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_Notation
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_Notation
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:22:07.529878+00:00
-- url     : https://prove2.me/theorems/81418851-8e9a-4673-bb90-7034f8e500b3
-- title:
--   BG §16: notation for Theorems A–E
-- statement:
--   The notation layer for the main results of §16 of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, split off from the Theorems A–E file: $\hat M_\sigma$, $A(M)$, $A_0(M)$, the sharply transitive conjugation action language of Theorem D(3), the set of conjugates of $M$ containing $x$ and the local data for $R(x)$.
--
--   Main declarations: `hatMsigma` (BG Theorem E notation: `hat M_sigma = {a in M | C_{M_sigma}(a) != 1}`); `ASet` (BG Theorem E notation: `A(M) = hat M_sigma ∩ U M_sigma`); `A0Set`; `ConjSharplyTransitiveOn`; and 4 more.
--
--   The bundle also proves 12 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/Notation.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/Notation.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_SetupLemma151
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Theorem152Helpers
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_Corollary155
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_TIFailure
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S15_MF_WitnessPGroup
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_PairIntersection
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ExtraspecialSinger
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupType
import Definitions.Def_OddOrder_GroupTheory_MaximalSubgroupTypeConj
import Definitions.Def_OddOrder_GroupTheory_CoprimeAction
import Definitions.Def_OddOrder_GroupTheory_AInvariantComplement

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- BG Theorem E notation: `hat M_sigma = {a in M | C_{M_sigma}(a) != 1}`. -/
def hatMsigma (M : Subgroup G) : Set G :=
  {a | a ∈ M ∧ OddOrder.BG.Ch3.S10.Msigma M ⊓
    Subgroup.centralizer ({a} : Set G) ≠ ⊥}

/-- `M_σ# ⊆ \widehat{M_σ}`: every nonidentity element `x` of `M_σ` lies in `hatMsigma M`,
since `x ∈ M_σ ≤ M` and `x` centralizes itself, so `1 ≠ x ∈ M_σ ⊓ C_G(x)`.  `§14`-independent
building block for Theorems B/E (`A(M) = hatMsigma ∩ …`). -/
theorem sigmaSharp_subset_hatMsigma (M : Subgroup G) :
    S14.sigmaSharp M ⊆ hatMsigma M := by
  intro x hx
  simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
    Set.mem_singleton_iff] at hx
  obtain ⟨hxMσ, hx1⟩ := hx
  refine ⟨OddOrder.BG.Ch3.S10.Msigma_le M hxMσ, fun hbot => hx1 (Subgroup.mem_bot.mp ?_)⟩
  rw [← hbot]
  exact Subgroup.mem_inf.mpr ⟨hxMσ, Subgroup.mem_centralizer_iff.mpr
    (fun h hh => by rw [Set.mem_singleton_iff] at hh; subst hh; rfl)⟩

/-- BG Theorem E notation: `A(M) = hat M_sigma ∩ U M_sigma`. -/
def ASet (M U : Subgroup G) : Set G :=
  hatMsigma M ∩ ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) : Set G)

/-- BG Theorem E notation: `A_0(M) = hat M_sigma - C_M(K#)`, represented as the
part of `hat M_sigma` outside the `M`-conjugacy saturation of `K#`. -/
def A0Set (M K : Subgroup G) : Set G :=
  hatMsigma M \ conjClassSet (sharpSubgroup K)

/-- BG Theorem D(3) action language: `R` acts sharply transitively by conjugation on
a set of maximal subgroups. -/
def ConjSharplyTransitiveOn (R : Subgroup G) (S : Set (Subgroup G)) : Prop :=
  ∀ A ∈ S, ∀ B ∈ S, ∃! r : G, r ∈ R ∧ B = MulAut.conj r • A

/-- The set of conjugates of `M` that contain `x`, from BG Theorem D(3). -/
def maximalConjugatesContaining (M : Subgroup G) (x : G) : Set (Subgroup G) :=
  {N | ∃ g : G, N = MulAut.conj g • M ∧ x ∈ N}

/-- BG Theorem D(3) local data for `R(x)`: `C_M(x)` is a Hall subgroup of
`C_G(x)`, and `R` is a normal complement acting sharply transitively on the
maximal conjugates that contain `x`.

**Encoding fix (2026-06-29, lane δ; HUB-cleared `RData` is δ-internal, not a cross-lane contract):**
conjunct 1 was `IsHallSubgroup (σ M) (C_M(x))`, which is **false** for type-`P` `M`: at
`x ∈ Kstar^#`
the `κ`-Hall `K` (with `κ(M) ⊆ σ(M)ᶜ`) centralizes `x`, so `K ≤ C_M(x)`, making `C_M(x)` carry
`σ(M)′`-primes — not a `σ(M)`-group.  Coq Theorem 14.4(b)/(e) has `C_M(x)` a `σ(N)′`-Hall
of `C_G(x)`
(`N` = the signalizer maximal), i.e. *intrinsically* a Hall subgroup of `C_G(x)` (its order coprime
to
its index). We encode "`C_M(x)` is a Hall subgroup of `C_G(x)`" `σ`-agnostically as this
coprimality,
matching the docstring and avoiding the spurious `σ(M)` reference. -/
def RData (M : Subgroup G) (x : G) (R : Subgroup G) : Prop :=
  let Cx : Subgroup G := Subgroup.centralizer ({x} : Set G)
  Nat.Coprime (Nat.card ↥((M ⊓ Cx).subgroupOf Cx)) ((M ⊓ Cx).subgroupOf Cx).index ∧
    (R.subgroupOf Cx).Normal ∧
    Subgroup.IsComplement' ((M ⊓ Cx).subgroupOf Cx) (R.subgroupOf Cx) ∧
    ConjSharplyTransitiveOn R (maximalConjugatesContaining M x)

open Classical in
/-- BG `FT_signalizer_base x` (`N[x]`, Coq BGsection14:87): a maximal subgroup over `C_G(x)`
when `x`
has more than one `σ`-maximal (Coq picks one; Theorem D proves it unique), else `⊥`. -/
noncomputable def FT_signalizerBase (x : G) : Subgroup G :=
  if h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty then
    h.2.choose
  else ⊥

/-- BG `FT_signalizer x` (`R(x)`, Coq BGsection14:90): `(N[x])_σ ⊓ C_G(x)`. -/
noncomputable def FT_signalizer (x : G) : Subgroup G :=
  OddOrder.BG.Ch3.S10.Msigma (FT_signalizerBase x) ⊓ Subgroup.centralizer ({x} : Set G)

/-- `R(x) ≤ C_G(x)` (Coq `cent_FT_signalizer`). -/
theorem FT_signalizer_le_centralizer (x : G) :
    FT_signalizer x ≤ Subgroup.centralizer ({x} : Set G) :=
  inf_le_right

/-- In the nontrivial branch, `N[x]` is a maximal subgroup containing `C_G(x)`. -/
theorem centralizer_le_FT_signalizerBase {x : G}
    (h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty) :
    Subgroup.centralizer ({x} : Set G) ≤ FT_signalizerBase x := by
  have hb : FT_signalizerBase x = h.2.choose := dif_pos h
  rw [hb]
  exact (mem_maximalSubgroupsContaining.mp h.2.choose_spec).2

/-- **General `(N)_σ ⊓ C_G(x) ◁ C_G(x)` normality** (the core of Theorem D(3) `nsRCx`): for any `N`
with `C_G(x) ≤ N`, the centralizer normalizes `(N)_σ ⊓ C_G(x)` — it normalizes `(N)_σ ◁ N` (since
`C_G(x) ≤ N`) and itself, so it normalizes the intersection (`le_normalizer_inf`).  Applies both to
`N[x]` (`FT_signalizer_normal_in_centralizer`) and to the unique maximal from
`signalizer_structure_of_mem_sigmaSharp`. -/
theorem centralizer_le_normalizer_Msigma_inf_centralizer {x : G} {N : Subgroup G}
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ N) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) : Subgroup G) : Set G) :=
          by
  have hMσN : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have hbaseN : N ≤ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma N : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le _)).mp hMσN
  exact OddOrder.BG.Ch3.S12.le_normalizer_inf (hCN.trans hbaseN) Subgroup.le_normalizer

/-- **BG Theorem D(3), `R(x) ◁ C_G(x)`** (Coq `nsRCx`): the first-conjunct normality, the
`N = N[x]` instance of `centralizer_le_normalizer_Msigma_inf_centralizer`. -/
theorem FT_signalizer_normal_in_centralizer {x : G}
    (h : 1 < (maximalSigmaSubgroupsOfElement x).ncard ∧
      (maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G))).Nonempty) :
    Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (FT_signalizer x : Set G) :=
  centralizer_le_normalizer_Msigma_inf_centralizer (centralizer_le_FT_signalizerBase h)

/-- **Signalizer structure for a `σ`-sharp element** (the genuine bridge to Theorem D): for
`x ∈ M_σ^#` with more than one `σ`-maximal, the proven `sigmaLength_one_centralizer_structure`
(fed the genuine `genuineSigmaDecomposition`, with `ℓ_σ(x) = 1` from `Msigma_ell1`) yields the
unique
maximal `N = N[x]` over `C_G(x)` together with the Hall property of `R = N_σ ⊓ C_G(x)`, the sharp
transitivity on `𝓜_σ(x)`, the type-F/P2 dichotomy and the complement structure.  This is what the
Theorem D(3)/(4) data is assembled from. -/
theorem signalizer_structure_of_mem_sigmaSharp [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard) :
    ∃! N : Subgroup G, N ∈ maximalSubgroups G ∧
      Subgroup.centralizer ({x} : Set G) ≤ N ∧
      OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G) ≠ ⊥ ∧
      Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
        ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
          (Subgroup.centralizer ({x} : Set G))) ∧
      (∀ p ∈ S14.piSet (Subgroup.closure {x}), p ∈ tau2 N) ∧
      (S14.IsTypeF N ∨ S14.IsTypeP2 N) ∧
      ∀ M' ∈ S14.maximalSigmaSubgroupsOfElement x,
        tau2 N ∩ S14.piSet N ⊆ OddOrder.BG.Ch3.S10.sigma M' ∧
        OddOrder.BG.Ch3.S10.sigma N ∩ S14.piSet M' ⊆ OddOrder.BG.Ch3.S10.beta N ∧
        Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
          ((M' ⊓ N).subgroupOf N) ∧
        (∀ L ∈ S14.maximalSigmaSubgroupsOfElement x,
          ∃! r : G, (r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) ∧
            MulAut.conj r • M' = L) := by
  have hx1 : x ≠ 1 := hxM.2
  exact (S14.sigmaLength_one_centralizer_structure hG (S14.genuineSigmaDecomposition hG) hx1
    (S14.Msigma_ell1 hG hM hxM.1 hx1)).2 hgt

/-- **The conjugates of `M` containing `x` are exactly the `σ`-maximals of `x`** (for `x ∈ M_σ^#`):
`maximalConjugatesContaining M x = 𝓜_σ(x)`.  This identifies the set on which Theorem D(3)/(4)'s
`RData` asks for sharp transitivity (`maximalConjugatesContaining`) with the set the proven
structure
controls (`maximalSigmaSubgroupsOfElement`).
* `⊆`: a conjugate `N = M^g ∋ x` has `x` a `σ(N)`-element (`σ(N) = σ(M)`, `sigma_conj`), and the
  normal `σ(N)`-Hall `N_σ` absorbs the `σ(N)`-subgroup `⟨x⟩` (`sigma_subgroup_le_Msigma_of_isHall`),
  so `x ∈ N_σ`.
* `⊇`: `Theorem 14.4`'s `C_G(x)`-conjugacy (`exists_conj_centralizer_of_mem_maximalSigma`) makes any
  `N ∈ 𝓜_σ(x)` a conjugate `M^c` (`c ∈ C_G(x)`), and `x ∈ N_σ ≤ N`. -/
theorem maximalConjugatesContaining_eq_maximalSigma [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1) :
    maximalConjugatesContaining M x = S14.maximalSigmaSubgroupsOfElement x := by
  ext N
  constructor
  · rintro ⟨g, rfl, hxN⟩
    have hNmax : MulAut.conj g • M ∈ maximalSubgroups G :=
      S14.mem_maximalSubgroups_of_isConjugateSubgroup hM ⟨g, rfl⟩
    refine ⟨hNmax, ?_⟩
    have hxpi : Ch03.Subgroup.IsPiGroup (OddOrder.BG.Ch3.S10.sigma (MulAut.conj g • M))
        (Subgroup.zpowers x) := by
      intro p hp
      rw [Nat.card_zpowers] at hp
      have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors hp⟩
      exact OddOrder.BG.Ch3.S10.sigma_conj g (S14.isPiElement_sigma_of_mem_Msigma hxMσ p hp)
    exact OddOrder.BG.Ch3.S10.sigma_subgroup_le_Msigma_of_isHall
      (OddOrder.BG.Ch3.S10.Msigma_isHall hG hNmax) (Subgroup.zpowers_le.mpr hxN) hxpi
      (Subgroup.mem_zpowers x)
  · rintro ⟨hNmax, hxNσ⟩
    obtain ⟨c, _, hcconj⟩ := S14.exists_conj_centralizer_of_mem_maximalSigma hG
      (S14.genuineSigmaDecomposition hG) (S14.Msigma_ell1 hG hM hxMσ hx1) ⟨hM, hxMσ⟩ ⟨hNmax, hxNσ⟩
    exact ⟨c, hcconj.symm, OddOrder.BG.Ch3.S10.Msigma_le N hxNσ⟩

/-- **If `C_G(x) ≤ M` then `M` is the unique `σ`-maximal of `x`** (`𝓜_σ(x) = {M}`, for `x ∈ M_σ^#`):
any `L ∈ 𝓜_σ(x)` is `M^c` with `c ∈ C_G(x)` (`exists_conj_centralizer_of_mem_maximalSigma`), and
`c ∈ C_G(x) ≤ M ≤ N_G(M)` gives `M^c = M`.  The easy direction of the `|𝓜_σ(x)|`-vs-`C_G(x) ⊆ M`
dichotomy — the trivial (`R(x) = 1`) branch of Theorem D(3). -/
theorem maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    (hCM : Subgroup.centralizer ({x} : Set G) ≤ M) :
    S14.maximalSigmaSubgroupsOfElement x = {M} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hM, hxMσ⟩, fun L hL => ?_⟩
  obtain ⟨c, hcC, hcconj⟩ := S14.exists_conj_centralizer_of_mem_maximalSigma hG
    (S14.genuineSigmaDecomposition hG) (S14.Msigma_ell1 hG hM hxMσ hx1) ⟨hM, hxMσ⟩ hL
  rw [← hcconj]
  exact conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer (hCM hcC))

/-- **Pointed sharp transitivity upgrades to full sharp transitivity** (regular action): if `R`
acts on `S` so that every `L ∈ S` is `M₀^r` for a *unique* `r ∈ R`, then `R` is sharply transitive
on `S` — for `A, B ∈ S` the unique `r ∈ R` with `B = A^r` is `r = b a⁻¹` (where `A = M₀^a`,
`B = M₀^b`).  Supplies the `ConjSharplyTransitiveOn` conjunct of `RData` from the proven structure's
"from `M`" transitivity (`signalizer_structure_of_mem_sigmaSharp`). -/
theorem conjSharplyTransitiveOn_of_pointed {R : Subgroup G} {S : Set (Subgroup G)} {M₀ : Subgroup G}
    (hbase : ∀ L ∈ S, ∃! r : G, r ∈ R ∧ MulAut.conj r • M₀ = L) :
    ConjSharplyTransitiveOn R S := by
  intro A hA B hB
  obtain ⟨a, ⟨haR, haM⟩, _⟩ := hbase A hA
  obtain ⟨b, ⟨hbR, hbM⟩, hbuniq⟩ := hbase B hB
  refine ⟨b * a⁻¹, ⟨R.mul_mem hbR (R.inv_mem haR), ?_⟩, ?_⟩
  · show B = MulAut.conj (b * a⁻¹) • A
    rw [← haM, ← mul_smul, ← map_mul, show (b * a⁻¹) * a = b by group, hbM]
  · rintro r ⟨hrR, hrA⟩
    have hrab : MulAut.conj (r * a) • M₀ = B := by
      rw [map_mul, mul_smul, haM, ← hrA]
    have hra : r * a = b := hbuniq (r * a) ⟨R.mul_mem hrR haR, hrab⟩
    rw [← hra]; group

/-- **Theorem D(3) `RData` assembly** (gated-endpoint skeleton): from the proven structure's data
(the maximal `N ≥ C_G(x)` and its sharp transitivity on `𝓜_σ(x)`) plus the two deep `M`-side inputs
(`C_M(x)` a Hall subgroup of `C_G(x)`, and the complement `R ⋊ C_M(x) = C_G(x)`, Coq parts (e)/(b)),
the four `RData M x R` conjuncts assemble for `R = N_σ ⊓ C_G(x)`: conjunct 2 (`R ◁ C_G(x)`) is
`centralizer_le_normalizer_Msigma_inf_centralizer`, conjunct 4 (sharp transitivity on
`maximalConjugatesContaining M x = 𝓜_σ(x)`) is `conjSharplyTransitiveOn_of_pointed`.  Reduces hD3 to
the two genuinely-remaining inputs. -/
theorem RData_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M) (hx1 : x ≠ 1)
    {N : Subgroup G} (hCN : Subgroup.centralizer ({x} : Set G) ≤ N)
    (hsharp : ∀ L ∈ S14.maximalSigmaSubgroupsOfElement x,
      ∃! r : G, (r ∈ OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) ∧
        MulAut.conj r • M = L)
    (hRhall : Ch03.IsHallSubgroup (OddOrder.BG.Ch3.S10.sigma N)
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G))))
    (hconj3 : Subgroup.IsComplement'
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Subgroup.centralizer ({x} : Set G)))
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G)))) :
    RData M x (OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  refine ⟨?_, ?_, hconj3, ?_⟩
  · -- conjunct 1 (`C_M(x)` a Hall subgroup of `C_G(x)`): from `R` Hall + the complement,
    -- the order of `C_M(x)` (= the index of `R`) is coprime to its index (= the order of `R`).
    have hcop := hRhall.coprime_index
    rwa [hconj3.index_eq_card, Nat.coprime_comm, ← hconj3.symm.index_eq_card] at hcop
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
      (centralizer_le_normalizer_Msigma_inf_centralizer hCN)
  · rw [maximalConjugatesContaining_eq_maximalSigma hG hM hxMσ hx1]
    exact conjSharplyTransitiveOn_of_pointed hsharp

/-- **Theorem D(3) conjunct 3, the centralizer complement** (Coq Theorem 14.4(b),
`R ⋊ C_(M∩N)(x) = C(x)`): from the proven structure's `N`-complement `(N)_σ ⋊ (M ∩ N) = N`
(`hMcompl`), inside `C_G(x)` the subgroups `C_M(x) = M ⊓ C_G(x)` and `R = (N)_σ ⊓ C_G(x)` complement
each other. This is the engine `IsComplement'.inf_centralizer_of_normalizer` (mathcomp
`subcent_sdprod`)
applied with `K = (N)_σ` (normal in `N`), `H = M ∩ N`, and `a = x`: `x` normalizes `(N)_σ` (it lies
in
`N` since `C_G(x) ≤ N`, and `(N)_σ ◁ N`) and `M ∩ N` (it lies in `M ∩ N`).  Discharges the one
genuinely-deep `RData` input of `RData_of_inputs`. -/
theorem signalizer_centralizer_isComplement {M N : Subgroup G} {x : G}
    (hMcompl : Subgroup.IsComplement' ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N)
      ((M ⊓ N).subgroupOf N))
    (hCN : Subgroup.centralizer ({x} : Set G) ≤ N) (hxM : x ∈ M) :
    Subgroup.IsComplement'
      ((M ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf (Subgroup.centralizer ({x} : Set G)))
      ((OddOrder.BG.Ch3.S10.Msigma N ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf
        (Subgroup.centralizer ({x} : Set G))) := by
  have hxN : x ∈ N := hCN (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hKnorm : ((OddOrder.BG.Ch3.S10.Msigma N).subgroupOf N).Normal := by
    rw [OddOrder.BG.Ch3.S10.Msigma_subgroupOf]; infer_instance
  have haK : x ∈ Subgroup.normalizer (OddOrder.BG.Ch3.S10.Msigma N : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer (OddOrder.BG.Ch3.S10.Msigma_le N)).mp hKnorm) hxN
  have haH : x ∈ Subgroup.normalizer ((M ⊓ N : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_inf.mpr ⟨hxM, hxN⟩)
  have hgen := hMcompl.inf_centralizer_of_normalizer hKnorm
    (OddOrder.BG.Ch3.S10.Msigma_le N) hCN haK haH
  rw [show (M ⊓ N) ⊓ Subgroup.centralizer ({x} : Set G)
      = M ⊓ Subgroup.centralizer ({x} : Set G) from by
      rw [inf_assoc, inf_eq_right.mpr hCN]] at hgen
  exact hgen.symm

/-- **BG Theorem D(3) for the `|𝓜_σ(x)| > 1` branch** (`∃ R, RData M x R`): when `x ∈ M_σ^#`
has more
than one `σ`-maximal, the proven `signalizer_structure_of_mem_sigmaSharp` supplies the unique
maximal
`N ≥ C_G(x)`, the Hall property of `R = (N)_σ ⊓ C_G(x)` and the sharp transitivity from `M`; the
centralizer complement (conjunct 3) is `signalizer_centralizer_isComplement`, and `RData_of_inputs`
assembles all four `RData` conjuncts.  This is the genuinely-deep half of `hD3`; the remaining
`|𝓜_σ(x)| ≤ 1` branch needs `C_G(x) ≤ M` (the deep converse of
`maximalSigmaSubgroupsOfElement_eq_singleton_of_centralizer_le`). -/
theorem RData_of_gt_one [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hM : M ∈ maximalSubgroups G) {x : G} (hxM : x ∈ S14.sigmaSharp M)
    (hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard) :
    ∃ R : Subgroup G, RData M x R := by
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hxM.1
  have hx1 : x ≠ 1 := hxM.2
  have hxM_mem : x ∈ M := OddOrder.BG.Ch3.S10.Msigma_le M hxMσ
  obtain ⟨N, hN, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hxM hgt
  obtain ⟨_, hCN, _, hRhall, _, _, hforall⟩ := hN
  obtain ⟨_, _, hMcompl, hMsharp⟩ := hforall M ⟨hM, hxMσ⟩
  exact ⟨_, RData_of_inputs hG hM hxMσ hx1 hCN hMsharp hRhall
    (signalizer_centralizer_isComplement hMcompl hCN hxM_mem)⟩

end OddOrder.BG.Ch4.S16


