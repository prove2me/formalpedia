-- Prove2me | Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TaxonomyOutput
-- name    : OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TaxonomyOutput
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T10:56:39.637612+00:00
-- url     : https://prove2.me/theorems/8c7906ab-c7d9-4ede-afd8-1be86a269ceb
-- title:
--   BG §16: Proposition 16.1 taxonomy and Theorems I/II (output for Peterfalvi)
-- statement:
--   The Proposition 16.1 taxonomy and Theorems I and II of Bender–Glauberman, *Local Analysis for the Odd Order Theorem*, §16, in the form consumed by Peterfalvi's text. It consists of lemmas only, including `theoremII_conjunct1_of_inputs` and the tame embedding of Theorem II.
--
--   The bundle consists of lemmas only.
--
--   The bundle also proves 5 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TaxonomyOutput.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/BG/Ch4_FamilyOfMaximal/S16_MainResults/TaxonomyOutput.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_TypeBridges
import Definitions.Def_OddOrder_BG_Ch4_FamilyOfMaximal_S16_MainResults_LocalTaxonomy

namespace OddOrder.BG.Ch4.S16

open OddOrder.GroupTheory

open OddOrder.Isaacs

open OddOrder.BG.Ch3.S12

open OddOrder.BG.Ch4.S14

open OddOrder.BG.Ch4.S15

open scoped Pointwise

variable {G : Type*} [Group G]

/-- **Assembly for BG Theorem II (Ti)** (mmd L4546--L4550), as a `sorry`-free,
axiom-clean *gated-endpoint skeleton*.

The mmd proof decomposes `A_0(M)` into the disjoint pieces `M_σ`, `A(M) - M_σ`,
and `A_0(M) - A(M)`, observes that cross-piece elements have distinct orders (so
are never `G`-conjugate), and concludes:
* within `M_σ`, `G`-conjugacy is `M`-conjugacy by **Theorem D(1)** (`hD1`);
* within either TI piece (**Theorem B(5)**/`hTI_B`, **Theorem C(9)**/`hTI_C`),
  `G`-conjugacy forces the conjugator into `M` by the TI condition.

This bundles those three inputs plus the cross-piece exclusion `hPieceInv`
(`G`-conjugate elements of `X` share `M_σ`- and `A(M)`-membership — the formal
content of "distinct orders across pieces") and discharges (Ti) with no `sorry`
of its own.  The remaining gated obligation when this is applied is exactly
`hPieceInv` (BG Theorem E prime-structure of the pieces). -/
theorem theoremII_conjunct1_of_inputs {M K U : Subgroup G}
    (hD1 : ∀ x ∈ OddOrder.BG.Ch3.S10.Msigma M, ∀ y ∈ OddOrder.BG.Ch3.S10.Msigma M,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹)
    (hTI_B : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M)
    (hTI_C : IsTISubset (A0Set M K \ ASet M U) M)
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    (hPieceInv : ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) →
      (x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ y ∈ OddOrder.BG.Ch3.S10.Msigma M) ∧
        (x ∈ ASet M U ↔ y ∈ ASet M U)) :
    ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹ := by
  intro x hxX y hyX hconj
  obtain ⟨g, hg⟩ := hconj
  obtain ⟨hMσiff, hAiff⟩ := hPieceInv x hxX y hyX ⟨g, hg⟩
  by_cases hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M
  · -- Both in `M_σ`: Theorem D(1).
    exact hD1 x hxMσ y (hMσiff.mp hxMσ) ⟨g, hg⟩
  · -- `x ∉ M_σ`, hence `y ∉ M_σ`; `x, y` lie in a common TI piece.
    have hyMσ : y ∉ OddOrder.BG.Ch3.S10.Msigma M := fun h => hxMσ (hMσiff.mpr h)
    have hxMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    have hyMσ' : y ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    by_cases hxA : x ∈ ASet M U
    · -- `x, y ∈ A(M) - M_σ` (TI piece, Theorem B(5)): the conjugator lies in `M`.
      have hyA : y ∈ ASet M U := hAiff.mp hxA
      exact ⟨g, hTI_B g ⟨x, ⟨hxA, hxMσ'⟩, hg ▸ ⟨hyA, hyMσ'⟩⟩, hg⟩
    · -- `x ∉ A(M)`: only possible for `X = A_0(M)`.
      rcases hX with hXA | hXA0
      · exact absurd (hXA ▸ hxX) hxA
      · -- `x, y ∈ A_0(M) - A(M)` (TI piece, Theorem C(9)).
        have hyA : y ∉ ASet M U := fun h => hxA (hAiff.mpr h)
        exact ⟨g, hTI_C g ⟨x, ⟨hXA0 ▸ hxX, hxA⟩, hg ▸ ⟨hXA0 ▸ hyX, hyA⟩⟩, hg⟩

/-- **Assembly for BG Theorem II** (mmd L4548), as a *gated-endpoint skeleton* (`sorry`-free in its
own body).  `A(M)`/`A_0(M)` are tamely embedded — the BG form of the centralizer-control input used
by Peterfalvi (8.12)--(8.13).

The body is the full Theorem II proof, citing the §16 structure theorems A--D and Proposition 16.1
inline (those were `sorry`-stated when this skeleton was written and have since been proved).  What
the skeleton isolates are the two obligations *beyond* that standard A--D suite, as named hypotheses
(cf. `theoremII_conjunct1_of_inputs`):
* `hPieceInv` — the conjunct-1 cross-piece exclusion: `G`-conjugate elements of `X` share `M_σ`-
  and `A(M)`-membership (the "distinct orders across pieces" content of BG Theorem E);
* `hMaxUnique` — the conjunct-3 uniqueness `|ℳ(C_G(x))| = 1` for an escaping centralizer
  (BG §9--§10 Uniqueness), which pins the Type I/II maximal overgroup of `C_G(x)` to Theorem
  D(4)'s `N(x)`.

The wrapper `theoremII_tame_embedding` cites this with both obligations discharged. -/
theorem theoremII_tame_embedding_of_inputs [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    (hPieceInv : ∀ x ∈ X, ∀ y ∈ X, (∃ g : G, y = g * x * g⁻¹) →
      (x ∈ OddOrder.BG.Ch3.S10.Msigma M ↔ y ∈ OddOrder.BG.Ch3.S10.Msigma M) ∧
        (x ∈ ASet M U ↔ y ∈ ASet M U))
    (hMaxUnique : ∀ x : G, x ∈ X → x ≠ 1 →
      ¬ Subgroup.centralizer ({x} : Set G) ≤ M →
        ∀ N₁ N₂ : Subgroup G,
          N₁ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) →
          N₂ ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) → N₁ = N₂) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) := by
  classical
  -- Abbreviate the escaping set `D`.
  set D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M} with hDdef
  -- **Core gated reduction (mmd L4546-L4548).**  `A_0(M)` is the disjoint union of `M_σ`,
  -- `A(M) - M_σ`, and `A_0(M) - A(M)`; the latter two are `TI`-subsets of `G` with normalizer
  -- `M` (Theorem B(5) and Theorem C(9)), so every element of them has its `G`-centralizer inside
  -- `M`.  Hence an `x ∈ X` with `C_G(x) ⊄ M` must lie in `M_σ`, i.e. `D ⊆ M_σ#`.
  --
  -- This step needs the Hall data behind Theorem B(5)/C(9), which the *statement* of Theorem II
  -- does not carry (its `K`, `U` are free, not pinned to the `(κ ∪ σ)'`-Hall / `κ`-Hall factors).
  -- It is therefore isolated as a gated input; once it (and the dual-piece `TI` facts) land with
  -- their Hall hypotheses, `D ⊆ A(M)` (conjunct 2) becomes pure citation, as below.
  have hDsub : D ⊆ S14.sigmaSharp M := by
    intro x hxD
    obtain ⟨hxX, hx1, hxc⟩ := hxD
    -- `x ∈ M_σ#`: it suffices to show `x ∈ M_σ` (we already have `x ≠ 1`).
    simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe,
      Set.mem_singleton_iff]
    refine ⟨?_, hx1⟩
    by_contra hxnMσ
    -- `x ∉ M_σ`; the coerced form, and the TI piece for `A(M) - M_σ` (Theorem B(5)).
    have hxnMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
    have hTIB : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M :=
      theoremB_A_minus_Msigma_isTISubset hG hM hKM hUM hK hU
    rcases hX with hXA | hXA0
    · -- `X = A(M)`: `x ∈ A(M) - M_σ`, so `C_G(x) ≤ M` (Theorem B(5)) contradicts `C_G(x) ⊄ M`.
      exact hxc (hTIB.centralizer_le ⟨hXA ▸ hxX, hxnMσ'⟩)
    · -- `X = A_0(M)`.
      have hxA0 : x ∈ A0Set M K := hXA0 ▸ hxX
      by_cases hxA : x ∈ ASet M U
      · -- `x ∈ A(M) - M_σ`: Theorem B(5) again.
        exact hxc (hTIB.centralizer_le ⟨hxA, hxnMσ'⟩)
      · -- `x ∈ A_0(M) - A(M)`.
        by_cases hKbot : K = ⊥
        · -- **Type-F** (`K = ⊥`): `A_0(M) = \widehat{M_σ} ⊆ M = U M_σ` (Theorem A(3)),
          -- so `x ∈ A(M)`, contradicting `x ∉ A(M)`.
          refine hxA ⟨hxA0.1, ?_⟩
          have hxM : x ∈ M := hxA0.1.1
          have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
            (theoremA_maximal_structure_faithful hG hM hKM hUM hK rfl hU).2.2.1
          have hx' : x ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hxM
          rw [hKbot, bot_sup_eq] at hx'
          exact hx'
        · -- `K ≠ ⊥`: TI by Theorem C(9), giving `C_G(x) ≤ M`.
          obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
            theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
          exact hxc (hTIC.centralizer_le ⟨hxA0, hxA⟩)
  -- **`D ⊆ A(M)` (conjunct 2).**  `D ⊆ M_σ#` and `M_σ# ⊆ A(M)`: a nonidentity `x ∈ M_σ` lies in
  -- `\widehat{M_σ}` (`sigmaSharp_subset_hatMsigma`) and in `M_σ ≤ U M_σ`, so `x ∈ A(M)`.
  have hMσsharp_sub_A : S14.sigmaSharp M ⊆ ASet M U := by
    intro x hx
    refine ⟨sigmaSharp_subset_hatMsigma M hx, ?_⟩
    have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := (Set.mem_sdiff _).mp hx |>.1
    exact (le_sup_right : OddOrder.BG.Ch3.S10.Msigma M ≤
      (U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G)) hxMσ
  refine ⟨?_, hDsub.trans hMσsharp_sub_A, ?_⟩
  · -- **Conjunct 1 (Ti) (mmd L4546-L4550).**  Assembled from Theorem D(1) (`M_σ` fusion),
    -- Theorem B(5)/C(9) (the two TI pieces), and the cross-piece exclusion `hPieceInv`, via
    -- `theoremII_conjunct1_of_inputs`.  Only `hPieceInv` remains gated (BG Theorem E).
    have hTI_C : IsTISubset (A0Set M K \ ASet M U) M := by
      by_cases hKbot : K = ⊥
      · -- `K = ⊥` (type F): `A_0(M) = \widehat{M_σ} ⊆ M = U M_σ` (Thm A(3)), so the diff is empty.
        intro g hex
        obtain ⟨z, ⟨hzA0, hznA⟩, _⟩ := hex
        refine absurd ⟨hzA0.1, ?_⟩ hznA
        have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
          (theoremA_maximal_structure_faithful hG hM hKM hUM hK rfl hU).2.2.1
        have hz' : z ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hzA0.1.1
        rw [hKbot, bot_sup_eq] at hz'
        exact hz'
      · obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
          theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
        exact hTIC
    refine theoremII_conjunct1_of_inputs
      (theoremD_msigma_conjugacy_and_centralizers hG hM).1
      (theoremB_A_minus_Msigma_isTISubset hG hM hKM hUM hK hU) hTI_C hX ?_
    -- `hPieceInv`: `G`-conjugate elements of `X` share `M_σ`- and `A(M)`-membership — the
    -- "distinct orders across pieces" input of the mmd proof (BG Theorem E), a named obligation.
    exact hPieceInv
  · -- **Conjunct 3 (mmd L4552).**  For `x ∈ D ⊆ M_σ#` with `C_G(x) ⊄ M`, Theorem D(4) gives a
    -- unique maximal `N(x) ⊇ C_G(x)` that is of type `F` or `P₂`; Proposition 16.1(a)(b) rewrites
    -- this as Type I or Type II.  Existence and the type classification are pure citation; the
    -- *uniqueness* of the maximal overgroup is the residual gated input (BG §9-§10 Uniqueness).
    intro x hxD
    obtain ⟨hxX, hx1, hxc⟩ := hxD
    have hxMσsharp : x ∈ S14.sigmaSharp M := hDsub ⟨hxX, hx1, hxc⟩
    -- Theorem D(4): the `∃! N` with the type-`F`/`P₂` data attached to escaping centralizers.
    obtain ⟨_, _, _, hD4⟩ := theoremD_msigma_conjugacy_and_centralizers hG hM
    obtain ⟨_R, _hR, N₀, hQN₀, _hQuniq⟩ := hD4 x hxMσsharp hxc
    -- Unpack what Theorem II needs from the rich Theorem D(4) predicate `Q N₀`.
    obtain ⟨hN₀mem, _, _, _, hN₀type, _⟩ := hQN₀
    -- Convert `IsTypeF N₀ ∨ IsTypeP2 N₀` to `IsTypeI N₀ ∨ IsTypeII N₀` (Proposition 16.1(a)(b)).
    have hN₀ : N₀ ∈ maximalSubgroups G := (mem_maximalSubgroupsContaining.mp hN₀mem).1
    have htype : OddOrder.GroupTheory.IsTypeI N₀ ∨ OddOrder.GroupTheory.IsTypeII N₀ := by
      obtain ⟨hIiff, hIIiff, _⟩ := proposition_type_classification hG hN₀
      rcases hN₀type with hF | hP2
      · exact Or.inl (hIiff.mpr hF)
      · exact Or.inr (hIIiff.mpr hP2)
    refine ⟨N₀, ⟨hN₀mem, htype⟩, ?_⟩
    -- Uniqueness of the maximal overgroup of `C_G(x)`: the named obligation `hMaxUnique`.  Theorem
    -- D(4) gives uniqueness only for its *full* predicate `Q`; pinning the weaker "maximal
    -- overgroup, Type I/II" to the same `N₀` is exactly `|ℳ(C_G(x))| = 1` (BG §9--§10 Uniqueness).
    rintro N' ⟨hN'mem, _hN'type⟩
    exact hMaxUnique x hxX hx1 hxc N' N₀ hN'mem hN₀mem

/-- **The escaping piece of `A(M)`/`A_0(M)` lands in `M_σ#`** (the `D ⊆ M_σ#` reduction of Theorem
II's conjunct 2, extracted for reuse).  An `x ∈ X` (`X = A(M)` or `A_0(M)`) with `x ≠ 1` and
`C_G(x) ⊄ M` must lie in `M_σ`: the dual TI pieces `A(M) - M_σ` (Theorem B(5)) and `A_0(M) - A(M)`
(Theorem C(9), or empty in the type-`F` case via Theorem A(3)) have `G`-centralizer inside `M`. -/
theorem mem_sigmaSharp_of_mem_aSet_of_escape [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G)
    (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ) (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K)
    {x : G} (hxX : x ∈ X) (hx1 : x ≠ 1)
    (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    x ∈ S14.sigmaSharp M := by
  simp only [S14.sigmaSharp, sharpSubgroup, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  refine ⟨?_, hx1⟩
  by_contra hxnMσ
  have hxnMσ' : x ∉ (OddOrder.BG.Ch3.S10.Msigma M : Set G) := by rwa [SetLike.mem_coe]
  have hTIB : IsTISubset (ASet M U \ (OddOrder.BG.Ch3.S10.Msigma M : Set G)) M :=
    theoremB_A_minus_Msigma_isTISubset hG hM hKM hUM hK hU
  rcases hX with hXA | hXA0
  · exact hesc (hTIB.centralizer_le ⟨hXA ▸ hxX, hxnMσ'⟩)
  · have hxA0 : x ∈ A0Set M K := hXA0 ▸ hxX
    by_cases hxA : x ∈ ASet M U
    · exact hesc (hTIB.centralizer_le ⟨hxA, hxnMσ'⟩)
    · by_cases hKbot : K = ⊥
      · refine hxA ⟨hxA0.1, ?_⟩
        have hxM : x ∈ M := hxA0.1.1
        have hA3 : M = K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M :=
          (theoremA_maximal_structure_faithful hG hM hKM hUM hK rfl hU).2.2.1
        have hx' : x ∈ (K ⊔ U ⊔ OddOrder.BG.Ch3.S10.Msigma M : Subgroup G) := hA3 ▸ hxM
        rw [hKbot, bot_sup_eq] at hx'
        exact hx'
      · obtain ⟨_, _, _, _, _, _, _, _, _, hTIC, _, _⟩ :=
          theoremC_paired_structure hG hM hKbot hKM hUM hK rfl hU
        exact hesc (hTIC.centralizer_le ⟨hxA0, hxA⟩)

/-- **`ℳ(C_G(x))` is a singleton for an escaping `σ`-sharp element** (`|ℳ(C_G(x))| = 1`, the BG
§9--§10 uniqueness input of Theorem II's conjunct 3).  For `x ∈ M_σ#` with `C_G(x) ⊄ M`, the escape
forces `|𝓜_σ(x)| > 1` (`centralizer_le_of_maximalSigma_le_one`), so the signalizer structure
(`signalizer_structure_of_mem_sigmaSharp`) supplies the type-`F`/`P₂` neighbour `N` over `C_G(x)`
whose `τ₂`-element data feeds the Corollary-14.3 uniqueness
`maximalContaining_centralizer_eq_singleton_of_tau2_element`, pinning `ℳ(C_G(x)) = {N}`. -/
theorem maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hM : M ∈ maximalSubgroups G)
    {x : G} (hx : x ∈ S14.sigmaSharp M) (hesc : ¬ Subgroup.centralizer ({x} : Set G) ≤ M) :
    ∃ N : Subgroup G,
      maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) = {N} := by
  have hx1 : x ≠ 1 := hx.2
  have hxMσ : x ∈ OddOrder.BG.Ch3.S10.Msigma M := hx.1
  have hgt : 1 < (S14.maximalSigmaSubgroupsOfElement x).ncard := by
    by_contra h
    push Not at h
    exact hesc (centralizer_le_of_maximalSigma_le_one hG hM hxMσ hx1 h)
  obtain ⟨N, hNstruct, -⟩ := signalizer_structure_of_mem_sigmaSharp hG hM hx hgt
  obtain ⟨hNmax, hCN, hRne, _hRhall, hxtau2, _hNtype, _hforall⟩ := hNstruct
  have hxN : x ∈ N := hCN (Subgroup.mem_centralizer_iff.mpr
    (fun y hy => by rw [Set.mem_singleton_iff.mp hy]))
  exact ⟨N, maximalContaining_centralizer_eq_singleton_of_tau2_element hG hNmax hxN hx1 hxtau2 hRne⟩

/-- **BG Theorem II** (mmd L4548): `A(M)` and `A_0(M)` are tamely embedded.  The BG form of the
centralizer-control input used by Peterfalvi (8.12)--(8.13).  Cites the gated-endpoint skeleton
`theoremII_tame_embedding_of_inputs`; **both residual obligations are now discharged** — the BG
Theorem E cross-piece exclusion `hPieceInv` via the order-determined `M_σ`/`A(M)`-membership
(`mem_Msigma_iff_isPiElement_sigma` / `mem_U_sup_Msigma_iff_isPiElement_kappa_compl`), and the BG
§9--§10 maximal-overgroup uniqueness `hMaxUnique` via the signalizer uniqueness
(`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`).  The `_of_inputs`
skeleton cites the §16 structure theorems A--D inline; those are proved. -/
theorem theoremII_tame_embedding [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {M K U : Subgroup G} (hM : M ∈ maximalSubgroups G) (hKM : K ≤ M) (hUM : U ≤ M)
    (hK : Ch03.IsHallSubgroup (S14.kappa M) (K.subgroupOf M))
    (hU : Ch03.IsHallSubgroup ((S14.kappa M ∪ OddOrder.BG.Ch3.S10.sigma M)ᶜ)
      (U.subgroupOf M))
    {X : Set G} (hX : X = ASet M U ∨ X = A0Set M K) :
    (∀ x ∈ X, ∀ y ∈ X,
      (∃ g : G, y = g * x * g⁻¹) → ∃ m ∈ M, y = m * x * m⁻¹) ∧
      let D : Set G := {x | x ∈ X ∧ x ≠ 1 ∧ ¬ Subgroup.centralizer ({x} : Set G) ≤ M}
      -- BG Thm II: `D ⊆ A(M)` (not merely `D ⊆ X`); a genuine claim when `X = A_0(M)`.
      D ⊆ ASet M U ∧
        ∀ x : G, x ∈ D →
          ∃! N : Subgroup G,
            N ∈ maximalSubgroupsContaining (Subgroup.centralizer ({x} : Set G)) ∧
            (OddOrder.GroupTheory.IsTypeI N ∨ OddOrder.GroupTheory.IsTypeII N) :=
  theoremII_tame_embedding_of_inputs hG hM hKM hUM hK hU hX
    -- `hPieceInv`: BG Theorem E cross-piece exclusion.  `M_σ` (normal `σ`-Hall) and `U⊔M_σ` (normal
    -- `κ′`-Hall, Theorem A(3)) make `M_σ`- and `A(M)`-membership of an element of `M`
    -- order-determined
    -- (`mem_Msigma_iff_isPiElement_sigma` / `mem_U_sup_Msigma_iff_isPiElement_kappa_compl`), hence
    -- conjugation-invariant (`isPiElement_conj`).
    (by
      have hMσM : OddOrder.BG.Ch3.S10.Msigma M ≤ M := OddOrder.BG.Ch3.S10.Msigma_le M
      have hnorm : ((U ⊔ OddOrder.BG.Ch3.S10.Msigma M).subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hUM hMσM)).mpr
          (theoremA_ungated_conjuncts hG hM hKM hUM hK rfl hU).2.2.1
      intro x hxX y hyX hconj
      obtain ⟨g, hg⟩ := hconj
      have hxhat : x ∈ hatMsigma M := by
        rcases hX with h | h
        · have hm := h ▸ hxX; simp only [ASet, Set.mem_inter_iff] at hm; exact hm.1
        · have hm := h ▸ hxX; simp only [A0Set, Set.mem_sdiff] at hm; exact hm.1
      have hyhat : y ∈ hatMsigma M := by
        rcases hX with h | h
        · have hm := h ▸ hyX; simp only [ASet, Set.mem_inter_iff] at hm; exact hm.1
        · have hm := h ▸ hyX; simp only [A0Set, Set.mem_sdiff] at hm; exact hm.1
      refine ⟨?_, ?_⟩
      · rw [S14.mem_Msigma_iff_isPiElement_sigma hG hM hxhat.1,
          S14.mem_Msigma_iff_isPiElement_sigma hG hM hyhat.1]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hg]; exact S14.isPiElement_conj g h
        · rw [show x = g⁻¹ * y * (g⁻¹)⁻¹ from by rw [hg]; group]
          exact S14.isPiElement_conj g⁻¹ h
      · have hAx : x ∈ ASet M U ↔ x ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
          simp only [ASet, Set.mem_inter_iff, SetLike.mem_coe]
          exact ⟨fun h => h.2, fun h => ⟨hxhat, h⟩⟩
        have hAy : y ∈ ASet M U ↔ y ∈ U ⊔ OddOrder.BG.Ch3.S10.Msigma M := by
          simp only [ASet, Set.mem_inter_iff, SetLike.mem_coe]
          exact ⟨fun h => h.2, fun h => ⟨hyhat, h⟩⟩
        rw [hAx, hAy,
          S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm hxhat.1,
          S14.mem_U_sup_Msigma_iff_isPiElement_kappa_compl hG hM hUM hU hnorm hyhat.1]
        refine ⟨fun h => ?_, fun h => ?_⟩
        · rw [hg]; exact S14.isPiElement_conj g h
        · rw [show x = g⁻¹ * y * (g⁻¹)⁻¹ from by rw [hg]; group]
          exact S14.isPiElement_conj g⁻¹ h)
    -- `hMaxUnique`: BG §9--§10 maximal-overgroup uniqueness `|ℳ(C_G(x))| = 1`, discharged from the
    -- signalizer uniqueness
    -- (`maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape`)
    -- via the `D ⊆ M_σ#` reduction (`mem_sigmaSharp_of_mem_aSet_of_escape`).
    (fun x hxX hx1 hesc N₁ N₂ hN₁ hN₂ => by
      obtain ⟨N, hMC⟩ := maximalSubgroupsContaining_centralizer_eq_singleton_of_sigmaSharp_escape
        hG hM (mem_sigmaSharp_of_mem_aSet_of_escape hG hM hKM hUM hK hU hX hxX hx1 hesc) hesc
      rw [hMC, Set.mem_singleton_iff] at hN₁ hN₂
      exact hN₁.trans hN₂.symm)

end OddOrder.BG.Ch4.S16


