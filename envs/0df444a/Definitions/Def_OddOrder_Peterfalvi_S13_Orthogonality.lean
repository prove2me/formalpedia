-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_Orthogonality
-- name    : OddOrder_Peterfalvi_S13_Orthogonality
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:08:25.538837+00:00
-- url     : https://prove2.me/theorems/324a1761-667e-491f-8352-65440c3b7578
-- title:
--   Peterfalvi (11.8.6): the orthogonality endpoint, unconditional $\mathcal{S}(H_0C)$ coherence
-- statement:
--   Formalizes the (11.8.6) orthogonality endpoint (Peterfalvi, *Character Theory for the Odd Order Theorem*, §11, pp. 64-68), downstream of both Clifford branches of (9.7), proving the unconditional coherence of $\mathcal{S}(H_0C)$ on $A_0(M)$.
--
--   Main declarations: `coherent_sOf_H0Cprime_of_section9` (Peterfalvi (9.11) for the §11/§13 packaging, derived from the §9 argument); `coherent_sOf_H0Cprime` (Peterfalvi (9.11)); `coherent_sOf_H0C` (Peterfalvi (9.11), unconditional: `𝒮(H₀C)` is coherent on `A₀(M)`); `exists_glue_nu_H0C` ((11.8.6) narrow `τ₃` glue map `ν` exists).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_Orthogonality.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_Orthogonality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S13_CoreStructure
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCaseAResidual
import Definitions.Def_OddOrder_Peterfalvi_S13_MaximalIII_IV
import Definitions.Def_OddOrder_Peterfalvi_S07_Subcoherent
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenCoherence
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTwoSummand
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenMackeyNorm
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenTIWitness
import Definitions.Def_OddOrder_Peterfalvi_S13_SixTwoBridge
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenAlphaBound
import Definitions.Def_OddOrder_Peterfalvi_S11_NineElevenPairAdjoin
import Definitions.Def_OddOrder_Peterfalvi_S07_BridgeCoherent

namespace OddOrder.Peterfalvi.S13

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G]

/-- **Every `inducedKernelFamily`-member has integer degree.**  A member `φ = Ind_K^L θ` has degree
`φ(1) = |L:K|·θ(1)`, a product of natural numbers (`induce_apply_one`,
`irreducibleCharacter_apply_one_eq_pos_natCast`), hence an integer.  This is the `hdegX`/`hdegY`
integer-degree (character) datum of the `bridge_coherent` union engine. -/
theorem inducedKernelFamily_mem_intDegree {M : Subgroup G} [Fintype ↥M]
    {K : Subgroup ↥M} [Invertible (Nat.card ↥K : ℂ)] {X : Subgroup ↥M} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily K X) :
    ∃ n : ℤ, OddOrder.Peterfalvi.S03.characterDegree φ = (n : ℂ) := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  refine ⟨((K.index * d : ℕ) : ℤ), ?_⟩
  rw [OddOrder.Peterfalvi.S03.characterDegree_def, ClassFunction.induce_apply_one, hd]
  push_cast; ring

/-- **Every `inducedKernelFamily`-member has nonzero degree.**  `φ(1) = |L:K|·θ(1)` with both
factors positive naturals.  Supplies the `hdegχ` (nonzero anchor degree) input of `bridge_coherent`
for the reducible μ-column bridge. -/
theorem inducedKernelFamily_mem_apply_one_ne_zero {M : Subgroup G} [Fintype ↥M]
    {K : Subgroup ↥M} [Invertible (Nat.card ↥K : ℂ)] {X : Subgroup ↥M} {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily K X) :
    φ 1 ≠ 0 := by
  obtain ⟨θ, -, -, rfl⟩ := hφ
  obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  rw [ClassFunction.induce_apply_one, hd]
  exact mul_ne_zero (Nat.cast_ne_zero.mpr Subgroup.index_ne_zero_of_finite)
    (Nat.cast_ne_zero.mpr (by omega))

/-- **A degree-`0` element of `ℤ[inducedKernelFamily K X]` is `A₀`-supported** whenever `K^# ⊆ A₀`.
Every member `Ind_K^L θ` vanishes off the normal `K` (`induce_apply_eq_zero_of_not_mem_normal`),
so the whole integral span does; a span element with `φ(1) = 0` then has its support inside
`K ∖ {1} ⊆ A₀`.  This is the `hsuppX`/`hsuppY` degree/support dictionary of `bridge_coherent`,
uniform across the mixed degrees of `𝒮(H₀C)` (unlike `SHC_zSpan_vanish_support`, which anchors on a
fixed degree). -/
theorem inducedKernelFamily_zSpan_support_of_apply_one_eq_zero {M : Subgroup G} [Fintype ↥M]
    {K : Subgroup ↥M} [K.Normal] [Invertible (Nat.card ↥K : ℂ)] {X : Subgroup ↥M} {A0 : Set ↥M}
    (hKsupp : ∀ x : ↥M, x ∈ K → x ≠ 1 → x ∈ A0) {φ : ClassFunction ↥M ℂ}
    (hφ : φ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S08.inducedKernelFamily K X)) (h1 : φ 1 = 0) :
    φ.support ⊆ A0 := by
  have hsuppK : ∀ g : ↥M, g ∉ K →
      ∀ ψ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S08.inducedKernelFamily K X), ψ g = 0 := by
    intro g hg ψ hψ
    induction hψ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨θ, -, -, rfl⟩ := hx
        exact ClassFunction.induce_apply_eq_zero_of_not_mem_normal K _ hg
    | zero => rw [ClassFunction.zero_apply]
    | add x y _ _ hx hy => rw [ClassFunction.add_apply, hx, hy, add_zero]
    | smul c x _ hx => rw [← Int.cast_smul_eq_zsmul ℂ c x, ClassFunction.smul_apply, hx, mul_zero]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  by_cases hgK : g ∈ K
  · exact hKsupp g hgK (by rintro rfl; exact hg h1)
  · exact absurd (hsuppK g hgK φ hφ) hg

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11) for the §11/§13 packaging, derived from the §9 argument** (issue 1045
着手順 3) — this is what makes `coherent_sOf_H0Cprime` a corollary of `S11.nineEleven_coherent_A0`
rather than of the §13 chain `nineElevenPairBound` / `nineElevenSevenEightRefutation`.

Every input is definitional or an existing §10/§12 lemma:

* `τ` and `A₀` — `hyp.base.tau` *is* `dadeIntegralCharacterMap h46.dade0 h46.tau` and
  `hyp.base.A0` *is* `supportInSubgroup (A(M) ∪ V^M) M`, since `toHypothesis46` stores
  `dade0 := hyp.dadeData.dade` and `tau := …fullDadeIsometryData` and `tic_V` is `rfl`;
* `hKeq` — `h46.K` is the `typePData_toS06Hypothesis` field `(M')^{subgroupOf}`, and
  `S11.huSub_eq_derivedInG_subgroupOf` says `HU = M'`;
* `hHle` — `h46.subH` is *also* `M'` here ((4.6.c) is instantiated at `H = K`), and the §9 chain
  needs only `M_σ ≤ H` (`Msigma_le_derived`; the pin was relaxed for exactly this reason);
* `dd`/`hdd` — `hyp.base.dadeData` lives on `A₀(M)`, so it is restricted to `A(M)` by
  `S10.DadeSupportHypothesisData.restrict` with (8.16) `normalizer_typePA_eq`;
* `hKsupp`/`hVsub` — `mderivSharp_subset_A0` and `typePData_typePV_not_mem_derived`.

⚠ The **only** use of `hnc`/`htype` is the packaging dictionary `hyp.C = cSub s11Setup chief`
(`C_eq_cSub_of_noncoherent`), needed to see `H₀C′ = H₀ ⊔ C′` as the §9 family's index.  That is
precisely the "one-line dictionary" this issue kept finding at the bottom of every §13 producer:
the §9 argument itself never looks at the type. -/
theorem coherent_sOf_H0Cprime_of_section9 [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) := by
  have := hyp.base.finiteG
  classical
  have hCeq : hyp.C = OddOrder.Peterfalvi.S11.cSub hyp.s11Setup hyp.chief :=
    C_eq_cSub_of_noncoherent hG hyp hnc htype
  have hnorm : ∀ (l : ↥M) ⦃a : G⦄, a ∈ typePA M hyp.base.typeP →
      (↑l : G) * a * (↑l : G)⁻¹ ∈ typePA M hyp.base.typeP := fun l a ha =>
    ((Subgroup.mem_set_normalizer_iff).mp (hyp.base.le_normalizer_typePA l.2) a).mp ha
  have := OddOrder.Peterfalvi.S11.nineEleven_coherent_A0 hG hyp.base.maximal
    (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief)
    (hyp.base.toHypothesis46 hG hG.odd)
    (OddOrder.Peterfalvi.S11.huSub_eq_derivedInG_subgroupOf hyp.s11Setup).symm
    (Subgroup.subgroupOf_mono M (OddOrder.BG.Ch3.S10.Msigma_le_derived hG hyp.base.maximal))
      rfl hnorm hyp.base.mderivSharp_subset_A0
    (fun v hv => OddOrder.Peterfalvi.S10.typePData_typePV_not_mem_derived hyp.base.typeP hv)
    (hyp.base.dadeData.restrict Set.subset_union_left hnorm
      (OddOrder.Peterfalvi.S12.Hypothesis.normalizer_typePA_eq hG hyp.base)) rfl
  have hH0C' : hyp.H0Cprime
      = hyp.chief.H0 ⊔ (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief).Cprime := by
    change hyp.chief.H0 ⊔ derivedInG hyp.C = _
    rw [hCeq]
    rfl
  rw [hH0C']
  exact this

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11)** (Coq `Ptype_core_coherence`, `PFsection9.v:1484`): the family
`𝒮(H₀C′)` is coherent, **parametrized on the (11.3) non-coherence** `hnc` and the type
disjunction `htype` (instantiate with `S_H0C_not_coherent_unconditional` / `hyp.type_alt`
downstream; issue 9087).  The (9.11.7)–(9.11.8) coherent-pair construction
**Proved via the §9 argument** (`coherent_sOf_H0Cprime_of_section9`, issue 1045 着手順 3): the
underlying mathematics is `S11.nineEleven_coherent_A0`, which carries no type hypothesis at all.
The older §13 route (`coherent_sOf_H0Cprime_of_sevenEightRefutation` +
`nineElevenSevenEightRefutation`, issue 9083 Phase E-final) proves the same statement and is kept
for now; the two differ only in packaging. -/
theorem coherent_sOf_H0Cprime [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0Cprime) hyp.base.A0) :=
  coherent_sOf_H0Cprime_of_section9 hG hyp hnc htype

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (9.11), unconditional: `𝒮(H₀C)` is coherent on `A₀(M)`** — the Clifford dichotomy
`clifford_dichotomy` dispatches to caseB (landed `caseB_coherent_sOf_H0C`, issue 9075 via the (11.7)
transfer) and caseA (`caseA_coherent_sOf_H0Cprime_of_refuter` + the same transfer).

The caseA branch is **no longer gated**: the (9.11.1)--(9.11.8) squeeze is complete and
sorry-free across the twelve `S11_NineEleven*` leaves (~8,700 lines), and its endpoint
`S11.nineEleven_coherent_A0` takes **no refuter hypothesis** -- only the standard Hypothesis (4.6)
plumbing.  (The earlier reading of this docstring, "the caseA refuter is the sole sorried-cite",
predates that landing; re-measured 2026-07-27.)

The `𝒮(H₀C)`-restriction witness (shared by the transfer) is
the conjugate difference `μ̄ − μ` of a reducible μ-column (`columnSum_muColumnChar_mem_sOf_H0C`,
`w₂ ≥ 2`), `A₀`-supported and nonzero (odd-order no-real-characters).

This is the unconditional `X`-side (𝒮(H₀C)-coherence) input of the honest (11.8.6) world-bridge
union
glue `S07.coherentUnion_of_glued_of_bridge`; contradicting the (11.3) non-coherence closes (11.8)
without the
false wide uniform-degree route (issue 1019). -/
theorem coherent_sOf_H0C [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0) := by
  have := hyp.base.finiteG
  classical
  rcases OddOrder.Peterfalvi.S11.clifford_dichotomy hG
      (hyp.base.mkSection11CharacterData hyp.s11Setup hyp.chief) with hA | hB
  · -- **caseA**: (9.11) case-a coherence (the (9.11.2) squeeze, since landed and ungated),
    -- then the (11.7) `H₀C′ ≤ H₀C` transfer with the reducible-μ-column witness.
    have caseA := hA.some
    have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
    have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
      intro heq; have := congrArg Fin.val heq; simp at this
    set μ : ClassFunction ↥M ℂ := OddOrder.Peterfalvi.S06.columnSum
      (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩) with hμdef
    have hμmem : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1 hncH0C htype
    have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
        x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
        x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
          ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
      OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
        (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
    have hμc : μ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hμmem
    -- (9.11) itself, via the §9 argument
    -- (`coherent_sOf_H0Cprime` → `coherent_sOf_H0Cprime_of_section9`
    -- → `S11.nineEleven_coherent_A0`); this used to re-derive the whole §13 chain inline
    refine ⟨coherent_sOf_H0C_of_coherent_sOf_H0Cprime hyp
      (coherent_sOf_H0Cprime hG hyp hncH0C htype).some
      ⟨μ.conj - μ, ⟨?_, ?_⟩, ?_⟩⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span hμc) (Submodule.subset_span hμmem)
    · exact OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support
        hyp.base.mderivSharp_subset_A0 (hIKF hμmem)
    · intro h
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_hasNoRealCharacters
        (hyp.base.card_odd_of_isMinimalSimpleOdd hG) _ (hIKF hμmem) (sub_eq_zero.mp h)
  · -- **caseB**: the landed norm-general coherence (issue 9075) transferred to `𝒮(H₀C)`.
    exact ⟨caseB_coherent_sOf_H0C hG hyp hB.some hncH0C htype⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **(11.8.6) narrow `τ₃` glue map `ν` exists** — the world-bridge analogue of
`S12.Hypothesis.exists_glue_nu`.  From the two coherences `coh` (`S₁ = S(HC)`) and `hY`
(`S₂ = 𝒮(H₀C)`) there is an integral map `ν` agreeing with `coh.extension` on `S(HC)` and with
`hY.extension` on `𝒮(H₀C)` (Peterfalvi's `τ₃`).

Both `S(HC)` and `𝒮(H₀C)` embed into the pairwise-orthogonal general family
`inducedKernelFamily ((derivedInG M).subgroupOf M) _` (`SOf_eq`, `sOf_subset_SOf`), whose members
have nonzero (positive real) norm (`inducedKernelFamily_inner_self_real_pos`) and are finite
(`inducedKernelFamily_finite`); and `S(HC) ⊥ 𝒮(H₀C)` (`SOf_HC_inner_sOf_H0C_eq_zero`).  So the S07
non-orthonormal glue `exists_integralCharacterMap_glue_of_orthogonal` applies directly, supplying
the `ν`/`hagreeX`/`hagreeY` input of the narrow union-glue
`S07.coherentUnion_of_glued_of_bridge`. -/
theorem exists_glue_nu_H0C [Finite G] {M : Subgroup G} (hyp : Hypothesis M)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    (hY : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0) :
    ∃ ν : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G,
      (∀ x ∈ hyp.SOf hyp.HC, ν x = coh.extension x) ∧
      (∀ y ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C, ν y = hY.extension y) := by
  have := hyp.base.finiteG
  classical
  -- X-side bridge: `S(HC) = inducedKernelFamily K (HC.subgroupOf M)`
  have hXbridge : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf hyp.HC →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.HC.subgroupOf M) := fun {x} hx => by
    rw [hyp.SOf_eq] at hx; exact hx
  -- Y-side bridge: `𝒮(H₀C) ⊆ inducedKernelFamily K ⊥`
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  have hXfin : (hyp.SOf hyp.HC).Finite := by
    rw [hyp.SOf_eq]; exact OddOrder.Peterfalvi.S08.inducedKernelFamily_finite _
  have hYfin : (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C).Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite (⊥ : Subgroup ↥M)).subset
      (fun _ hx => hIKF hx)
  exact OddOrder.Peterfalvi.S07.IntegralCharacterMap.exists_integralCharacterMap_glue_of_orthogonal
    hXfin hYfin
    (fun _ hx _ hx' hne => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hXbridge hx) (hXbridge hx') hne)
    (fun _ hx => by
      obtain ⟨he, hpos⟩ :=
        OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hXbridge hx)
      rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne')
    (fun _ hy _ hy' hne => OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hy) (hIKF hy') hne)
    (fun _ hy => by
      obtain ⟨he, hpos⟩ :=
        OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hIKF hy)
      rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne')
    (fun _ hx _ hy => SOf_HC_inner_sOf_H0C_eq_zero hyp hx hy)
    coh.extension hY.extension

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **World-bridge for the σ-grids** (issue 1023 tick¹²): the §6 certain-type σ-image
`certainTypeOmegaSigma` of the `μ`-column character, dispatched by the `SOf_memberRFamily`
machinery over `h46 = hyp.toHypothesis46`, **is** the §10 `alignedOmegaSigmaGrid` entry.
Both are the (3.2) `σ` of the same TI-cyclic setup — `h46.tic` is *literally*
`typePData_toTICyclicHypothesis` (the `toHypothesis46` field), so `ticVdiff h46` and the
grid's `tic` agree definitionally — applied to pointwise-equal transported `ω`-characters
(`omegaProdCharTic_apply` vs the grid's `compHom e (chiColumn …)`; both transports are
carrier-identities, `coe_ticWEquivSdiffW`). -/
theorem certainTypeOmegaSigma_muColumnChar_eq_aligned [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    [NeZero (Nat.card (hyp.toHypothesis46 hG hG.odd).W1)]
    (hcw1 : Nat.card ↥(hyp.toHypothesis46 hG hG.odd).W1 = hyp.w1)
    (i : Fin hyp.w1) (j : Fin hyp.w2) :
    OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (hyp.toHypothesis46 hG hG.odd)
        (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i)
      = hyp.alignedOmegaSigmaGrid hG hG.odd i j := by
  have := hyp.finiteG
  classical
  -- the two setups agree definitionally (`toHypothesis46.tic` is the grid `tic` by field literal)
  change (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).sigma rfl
      (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (hyp.toHypothesis46 hG hG.odd))
      ((OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).omega
        (OddOrder.Peterfalvi.S06.omegaProdCharTic (hyp.toHypothesis46 hG hG.odd)
          (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i)))
    = hyp.alignedOmegaSigmaGrid hG hG.odd i j
  -- unfold the grid to its `σ`-form (defeq through the def's `let`s)
  rw [show hyp.alignedOmegaSigmaGrid hG hG.odd i j
      = (OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).sigma rfl
          (OddOrder.Peterfalvi.S06.ticVdiffFullDadeApplication (hyp.toHypothesis46 hG hG.odd))
          (ClassFunction.compHom
            (((Subgroup.subgroupOfEquivOfLe (OddOrder.Peterfalvi.S12.typePData_W_le_self
                hyp.typeP)).symm.trans
              (MulEquiv.subgroupCongr
                (OddOrder.Peterfalvi.S12.typePData_sup_subgroupOf_eq hyp.typeP).symm)).toMonoidHom)
            ((hyp.toHypothesis46 hG hG.odd).chiColumn (hyp.muColumnChar hG hG.odd j)
              (finCongr hcw1.symm i)
              : ClassFunction
                  (hyp.toHypothesis46 hG hG.odd).sdiffTICyclicHypothesis.W ℂ)) from rfl]
  -- same σ of pointwise-equal inputs
  congr 1
  ext w
  -- LHS value: `ω(ω_{ij}^{tic})(w) = chiColumn χ₂ i (ticWEquivSdiffW w)`
  have hL : ((OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).omega
        (OddOrder.Peterfalvi.S06.omegaProdCharTic (hyp.toHypothesis46 hG hG.odd)
          (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i))
        : ClassFunction _ ℂ) w
      = ((hyp.toHypothesis46 hG hG.odd).chiColumn (hyp.muColumnChar hG hG.odd j)
          (finCongr hcw1.symm i)
          : ClassFunction (hyp.toHypothesis46 hG hG.odd).sdiffTICyclicHypothesis.W ℂ)
        (OddOrder.Peterfalvi.S06.ticWEquivSdiffW (hyp.toHypothesis46 hG hG.odd) w) := by
    rw [(OddOrder.Peterfalvi.S06.ticVdiff (hyp.toHypothesis46 hG hG.odd)).omega_apply]
    exact OddOrder.Peterfalvi.S06.omegaProdCharTic_apply (hyp.toHypothesis46 hG hG.odd)
      (hyp.muColumnChar hG hG.odd j) (finCongr hcw1.symm i) w
  refine hL.trans ?_
  -- RHS value: `compHom e (chiColumn)(w) = chiColumn (e w)`; the two transports of `w`
  -- share the ambient element (`coe_ticWEquivSdiffW`), so `chiColumn` agrees.
  rw [ClassFunction.compHom_apply]
  refine congrArg _ ?_
  apply Subtype.ext
  apply Subtype.ext
  have h1 := OddOrder.Peterfalvi.S06.coe_ticWEquivSdiffW (hyp.toHypothesis46 hG hG.odd) w
  rw [h1]
  rfl

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The (5.8) `μ`-column pin for a narrow `𝒮(H₀C)`-coherence, irreducible case** (the Coq
`FTtypeP_coherent_TIred`-side of the (11.8.6) `tau2muj` WLOG, issue 1023 tick¹³): if `𝒮(H₀C)`
contains an irreducible `ξ`, then **any** coherent extension `c` of `𝒮(H₀C)` sends the
reducible `μ`-column sum `μ₁ = ∑_i μ_{i1}` to the aligned `ω^σ`-column `∑_i ω^σ_{i1}` — with
the *positive* sign.

The γ-trick: `γ = ξ(1)·μ₁ − μ₁(1)·ξ ∈ ℤ[𝒮(H₀C)]` has degree `0`, hence is `A₀`-supported and
`c`-extends as `τγ`; the Dade isometry on `A₀`-supported pairs gives
`⟨c(γ), τθ⟩ = ⟨γ, θ⟩ = ξ(1)·w₁` (`θ = μ₁ − dζ`, the capstone bridge).  Expanding the left side
along `τθ = ∑_i ω^σ_{i1} − d·ζ^{τ₁}` (`hθτ`, the column identity), every term except
`ξ(1)·⟨c(μ₁), ∑ω^σ⟩` vanishes: the `ζ^{τ₁}`-crosses by the two-stratum `coherent_ortho`
(`SOf_coherent_extension_cross_orthogonal`), the `⟨c(ξ), ∑ω^σ⟩`-cross by the (5.5) dispatch of
`ξ` (a `dadeOfDiff` pair) against the grid members (the σ-grid world-bridge
`certainTypeOmegaSigma_muColumnChar_eq_aligned` +
`certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP`).
So `⟨c(μ₁), ∑ω^σ⟩ = w₁`; with `‖c(μ₁)‖² = ‖μ₁‖² = w₁` (isometry) and `‖∑ω^σ‖² = w₁`
(orthonormal grid), positive-definiteness pins `c(μ₁) = ∑_i ω^σ_{i1}`. -/
theorem coherent_sOf_H0C_extension_muColumnSum_pin_of_irr [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (c : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    {ζ : ClassFunction ↥M ℂ} (hζHC : ζ ∈ hyp.SOf hyp.HC) {d : ℕ}
    (hw2 : 1 < hyp.base.w2)
    (hθsupp : (((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
        - (d : ℂ) • ζ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0)
    (hθτ : hyp.base.tau ((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
        - (d : ℂ) • ζ)
      = (∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i ⟨1, hw2⟩)
        - (d : ℂ) • coh.extension ζ)
    {ξ : ClassFunction ↥M ℂ}
    (hξ : ξ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C)
    (hξirr : IsIrreducibleCharacter ξ)
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    c.extension (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
      = ∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i ⟨1, hw2⟩ := by
  have := hyp.base.finiteG
  classical
  set μ : ClassFunction ↥M ℂ := ∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩
    with hμdef
  set Ω : ClassFunction G ℂ :=
    ∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i ⟨1, hw2⟩ with hΩdef
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  -- memberships and conjugates
  have hμmem : μ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
    rw [hμdef, hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩]
    exact columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1 hncH0C htype
  have hμc : μ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
    OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hμmem
  have hξc : ξ.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
    OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hξ
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  -- integer degrees `n_ξ = ξ(1)`, `n_μ = μ(1)` (nonzero)
  obtain ⟨nξ, hnξ⟩ := inducedKernelFamily_mem_intDegree (hIKF hξ)
  obtain ⟨nμ, hnμ⟩ := inducedKernelFamily_mem_intDegree (hIKF hμmem)
  rw [OddOrder.Peterfalvi.S03.characterDegree_def] at hnξ hnμ
  have hnξne : (nξ : ℂ) ≠ 0 := by
    rw [← hnξ]; exact inducedKernelFamily_mem_apply_one_ne_zero (hIKF hξ)
  -- the degree-0 combination `γ ∈ ℤ[𝒮(H₀C)]`, `A₀`-supported, extending as `τγ`
  set γ : ClassFunction ↥M ℂ := nξ • μ - nμ • ξ with hγdef
  have hγspan : γ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) :=
    Submodule.sub_mem _ (Submodule.smul_mem _ nξ (Submodule.subset_span hμmem))
      (Submodule.smul_mem _ nμ (Submodule.subset_span hξ))
  have hγ1 : γ 1 = 0 := by
    rw [hγdef, ClassFunction.sub_apply, ← Int.cast_smul_eq_zsmul ℂ nξ μ,
      ← Int.cast_smul_eq_zsmul ℂ nμ ξ, ClassFunction.smul_apply, ClassFunction.smul_apply,
      hnξ, hnμ]
    ring
  have hγsupp : γ.support ⊆ hyp.base.A0 := by
    refine inducedKernelFamily_zSpan_support_of_apply_one_eq_zero
      hyp.base.mderivSharp_subset_A0 (Submodule.span_mono (fun x hx => hIKF hx) hγspan) hγ1
  have hextγ : c.extension γ = hyp.base.tau γ :=
    c.extends_on_supported γ ⟨hγspan, hγsupp⟩
  -- the Dade-isometry inner: `⟨c(γ), τθ⟩ = ⟨γ, θ⟩`
  have hDade : ClassFunction.inner (c.extension γ)
      (hyp.base.tau (μ - (d : ℂ) • ζ)) = ClassFunction.inner γ (μ - (d : ℂ) • ζ) := by
    rw [hextγ]
    exact hyp.base.tau_inner_eq_of_supported hγsupp hθsupp
  -- character-level inners: `⟨μ,μ⟩ = w₁`, crosses vanish
  have hμμ : ClassFunction.inner μ μ = (hyp.base.w1 : ℂ) :=
    hyp.base.muGrid_column_sum_inner_self hG hG.odd ⟨1, hw2⟩
  have hζc : ζ.conj ∈ hyp.SOf hyp.HC := by
    rw [hyp.SOf_eq] at hζHC ⊢
    exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hζHC
  have hμζ : ClassFunction.inner μ ζ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      SOf_HC_inner_sOf_H0C_eq_zero hyp hζHC hμmem, star_zero]
  have hξζ : ClassFunction.inner ξ ζ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      SOf_HC_inner_sOf_H0C_eq_zero hyp hζHC hξ, star_zero]
  have hξself : ClassFunction.inner ξ ξ = 1 := hξirr.inner_self_eq_one
  have hξne_μ : ξ ≠ μ := by
    intro heq
    rw [heq] at hξself
    rw [hμμ] at hξself
    have hw1ge : 3 ≤ hyp.base.w1 := by
      have hodd : Odd hyp.base.w1 :=
        hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card hyp.base.W1)
      have hgt : 1 < hyp.base.w1 :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hyp.base.typeP.W1_nontrivial
      obtain ⟨k, hk⟩ := hodd; omega
    have h1' : (hyp.base.w1 : ℕ) = 1 := by exact_mod_cast hξself
    omega
  have hξμ : ClassFunction.inner ξ μ = 0 :=
    OddOrder.Peterfalvi.S08.inducedKernelFamily_pairwise_orthogonal
      (hIKF hξ) (hIKF hμmem) hξne_μ
  -- `⟨γ, θ⟩ = n_ξ · w₁`
  have hγθ : ClassFunction.inner γ (μ - (d : ℂ) • ζ) = (nξ : ℂ) * (hyp.base.w1 : ℂ) := by
    rw [hγdef, ← Int.cast_smul_eq_zsmul ℂ nξ μ, ← Int.cast_smul_eq_zsmul ℂ nμ ξ]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hμμ, hμζ, hξμ, hξζ, star_natCast, mul_zero, sub_zero]
  -- cross-vanishing at the image level
  have hsub1 : OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C ⊆ hyp.SOf hyp.H0C :=
    hyp.sOf_subset_SOf hyp.H0C
  have hcross_μζ : ClassFunction.inner (c.extension μ) (coh.extension ζ) = 0 := by
    refine SOf_coherent_extension_cross_orthogonal hG hyp hsub1
      (le_refl (hyp.SOf hyp.HC)) c coh hμmem hμc hζHC hζc ?_ ?_
    · intro heq
      rw [heq] at hμζ
      -- `⟨ζ, ζ⟩ ≠ 0`
      obtain ⟨he, hpos⟩ := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
        (show ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
            ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) by
          have h := hζHC; rw [hyp.SOf_eq] at h
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h)
      rw [he] at hμζ
      exact Complex.ofReal_ne_zero.mpr hpos.ne' hμζ
    · intro heq
      have hμζc : ClassFunction.inner μ ζ.conj = 0 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm,
          SOf_HC_inner_sOf_H0C_eq_zero hyp hζc hμmem, star_zero]
      rw [heq] at hμζc
      obtain ⟨he, hpos⟩ := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
        (show ζ.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
            ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) by
          have h := hζc; rw [hyp.SOf_eq] at h
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h)
      rw [he] at hμζc
      exact Complex.ofReal_ne_zero.mpr hpos.ne' hμζc
  have hcross_ξζ : ClassFunction.inner (c.extension ξ) (coh.extension ζ) = 0 := by
    refine SOf_coherent_extension_cross_orthogonal hG hyp hsub1
      (le_refl (hyp.SOf hyp.HC)) c coh hξ hξc hζHC hζc ?_ ?_
    · intro heq
      rw [heq] at hξζ
      obtain ⟨he, hpos⟩ := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
        (show ζ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
            ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) by
          have h := hζHC; rw [hyp.SOf_eq] at h
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h)
      rw [he] at hξζ
      exact Complex.ofReal_ne_zero.mpr hpos.ne' hξζ
    · intro heq
      have hξζc : ClassFunction.inner ξ ζ.conj = 0 := by
        rw [OddOrder.RepresentationTheory.inner_conj_symm,
          SOf_HC_inner_sOf_H0C_eq_zero hyp hζc hξ, star_zero]
      rw [heq] at hξζc
      obtain ⟨he, hpos⟩ := OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos
        (show ζ.conj ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
            ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) by
          have h := hζc; rw [hyp.SOf_eq] at h
          exact OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le h)
      rw [he] at hξζc
      exact Complex.ofReal_ne_zero.mpr hpos.ne' hξζc
  -- `⟨c(ξ), Ω⟩ = 0`: the (5.5) dispatch of `ξ` against the grid members via the world-bridge
  have hcw1 : Nat.card ↥(hyp.base.toHypothesis46 hG hG.odd).W1 = hyp.base.w1 :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.base.typeP.W1_le).toEquiv
  have hcross_ξΩ : ClassFunction.inner (c.extension ξ) Ω = 0 := by
    obtain ⟨E', hE'sub, hE'⟩ :=
      SOf_coherent_extension_eq_sum_memberRFamily hG hyp hsub1 c hξ hξc
    obtain ⟨hr, hs, himg⟩ := SOf_memberRFamily_imageSet_of_irr hG hyp (hsub1 hξ) hξirr
    have hPA : ((ξ.conj - ξ : ClassFunction ↥M ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.GroupTheory.typePA M hyp.base.typeP) M := by
      refine OddOrder.Peterfalvi.S08.inducedKernelFamily_conjDiff_support ?_ (hIKF hξ)
      intro y hyK hy1
      rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup,
        OddOrder.GroupTheory.typePA_eq_sharpSubgroup_derivedInG]
      exact ⟨Subgroup.mem_subgroupOf.mp hyK,
        fun h => hy1 (OneMemClass.coe_eq_one.mp (Set.mem_singleton_iff.mp h))⟩
    rw [hE', OddOrder.RepresentationTheory.inner_sum_left]
    refine Finset.sum_eq_zero fun α hα => ?_
    have hαdade := hE'sub hα
    rw [himg] at hαdade
    rw [hΩdef, OddOrder.RepresentationTheory.inner_sum_right]
    refine Finset.sum_eq_zero fun i _ => ?_
    -- the grid member is (a `±1`-multiple of) a `certainTypeR`-member via the world-bridge
    rw [← certainTypeOmegaSigma_muColumnChar_eq_aligned hG hyp.base hcw1 i ⟨1, hw2⟩]
    have hsign := ((hyp.base.toHypothesis46 hG hG.odd).columnFamily
      (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)).sign_eq
    have hmemR : OddOrder.Peterfalvi.S06.certainTypeRImage
        (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)
        (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)⁻¹ (false, finCongr hcw1.symm i)
        ∈ (OddOrder.Peterfalvi.S06.certainTypeR (hyp.base.toHypothesis46 hG hG.odd)
          (hyp.base.muColumnChar_ne_one hG hG.odd hk1)
          (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one
            (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)).symm).imageSet :=
      Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hRval : OddOrder.Peterfalvi.S06.certainTypeRImage
        (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)
        (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)⁻¹ (false, finCongr hcw1.symm i)
        = (((hyp.base.toHypothesis46 hG hG.odd).columnFamily
            (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)).sign : ℂ)
          • OddOrder.Peterfalvi.S06.certainTypeOmegaSigma (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩) (finCongr hcw1.symm i) := rfl
    have horth := certainTypeR_imageSet_orthogonal_dadeOfDiff_typeP hG hyp.base
      (hyp.base.muColumnChar_ne_one hG hG.odd hk1)
      (OddOrder.Peterfalvi.S06.columnSum_inv_apply_one (hyp.base.toHypothesis46 hG hG.odd)
        (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)).symm
      ⟨ξ, hξirr⟩ hr hPA hs _ hmemR α hαdade
    -- transfer `⟨R-member, α⟩ = 0` to `⟨α, ω^σ⟩ = 0` through the `±1` sign
    have hζval : OddOrder.Peterfalvi.S06.certainTypeOmegaSigma
        (hyp.base.toHypothesis46 hG hG.odd) (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)
        (finCongr hcw1.symm i)
        = (((hyp.base.toHypothesis46 hG hG.odd).columnFamily
            (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)).sign : ℂ)
          • OddOrder.Peterfalvi.S06.certainTypeRImage (hyp.base.toHypothesis46 hG hG.odd)
            (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)
            (hyp.base.muColumnChar hG hG.odd ⟨1, hw2⟩)⁻¹ (false, finCongr hcw1.symm i) := by
      rw [hRval, smul_smul]
      rcases hsign with h | h <;> rw [h] <;> norm_num
    rw [hζval, OddOrder.RepresentationTheory.inner_smul_right,
      OddOrder.RepresentationTheory.inner_conj_symm, horth, star_zero, mul_zero]
  -- the γ-equation gives `⟨c(μ), Ω⟩ = w₁`
  have hkey : ClassFunction.inner (c.extension μ) Ω = (hyp.base.w1 : ℂ) := by
    have hextsplit : c.extension γ
        = (nξ : ℂ) • c.extension μ - (nμ : ℂ) • c.extension ξ := by
      rw [hγdef, map_sub, map_zsmul, map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ nξ (c.extension μ),
        ← Int.cast_smul_eq_zsmul ℂ nμ (c.extension ξ)]
    have h1 := hDade
    rw [hθτ, hextsplit, hγθ] at h1
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hcross_μζ, hcross_ξζ, hcross_ξΩ, star_natCast, mul_zero, sub_zero] at h1
    exact mul_left_cancel₀ hnξne h1
  -- norms and positive-definiteness: `‖c(μ) − Ω‖² = 0`
  have hextnorm : ClassFunction.inner (c.extension μ) (c.extension μ) = (hyp.base.w1 : ℂ) := by
    rw [c.extension_inner_eq μ μ (Submodule.subset_span hμmem) (Submodule.subset_span hμmem),
      hμμ]
  have hrow : ∀ i : Fin hyp.base.w1,
      ClassFunction.inner (hyp.base.alignedOmegaSigmaGrid hG hG.odd i ⟨1, hw2⟩) Ω = 1 := by
    intro i
    rw [hΩdef, OddOrder.RepresentationTheory.inner_sum_right]
    rw [Finset.sum_eq_single i
      (fun i' _ hne => by
        rw [hyp.base.alignedOmegaSigmaGrid_inner hG hG.odd i i' ⟨1, hw2⟩ ⟨1, hw2⟩,
          if_neg (fun h => hne h.1.symm)])
      (fun h => absurd (Finset.mem_univ i) h)]
    rw [hyp.base.alignedOmegaSigmaGrid_inner hG hG.odd i i ⟨1, hw2⟩ ⟨1, hw2⟩, if_pos ⟨rfl, rfl⟩]
  have hΩnorm : ClassFunction.inner Ω Ω = (hyp.base.w1 : ℂ) := by
    conv_lhs => rw [hΩdef]
    rw [OddOrder.RepresentationTheory.inner_sum_left,
      Finset.sum_congr rfl (fun i _ => hrow i)]
    simp
  have hΩext : ClassFunction.inner Ω (c.extension μ) = (hyp.base.w1 : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hkey, star_natCast]
  have hdiff : ClassFunction.inner (c.extension μ - Ω) (c.extension μ - Ω) = 0 := by
    rw [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right, hextnorm, hΩnorm, hkey, hΩext]
    ring
  have hzero := OddOrder.Peterfalvi.S09.Cert.inner_self_eq_zero hdiff
  exact sub_eq_zero.mp hzero

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **The canonical pinned `𝒮(H₀C)`-coherence, all-reducible case** (the Coq
`uniform_prTIred_coherent` swap of the (11.8.6) `tau2muj` WLOG, issue 1023 tick¹⁴): if every
member of `𝒮(H₀C)` is reducible — hence a `μ`-column sum (`SOf_reducible_eq_columnSum`) — the
assignment `μ-column ↦ aligned ω^σ-column` extends to a coherent extension
(`coherentImageMap` over the orthogonal member family), *pinned by construction*.

Isometry: member pairs have `⟨μ_a, μ_b⟩ = w₁·[a=b] = ⟨Ω_a, Ω_b⟩` (column norms and the
orthonormal grid).  τ-agreement: an `A₀`-supported lattice element has value `0` at `1`
(`one_notMem_A0`); since all members share the degree `w₁·d` (`degree_independent`), the residual
`ν₀ − τ` is `(x 1 / D)`-proportional to the column-independent constant
`r = Ω_j − τ(μ_j)` (the `hcolC` column-identity differences), hence vanishes there. -/
theorem exists_pinned_coherent_sOf_H0C_of_all_reducible [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (c₀ : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0)
    {Xζ : ClassFunction G ℂ} {ζ : ClassFunction ↥M ℂ} {d : ℕ}
    (hw2 : 1 < hyp.base.w2)
    (hcolC : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      hyp.base.tau ((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) - (d : ℂ) • ζ)
        = (∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
          - (d : ℂ) • Xζ)
    (hallred : ∀ η ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C,
      ¬ IsIrreducibleCharacter η)
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    ∃ c : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
        (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0,
      c.extension (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
        = ∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i ⟨1, hw2⟩ := by
  have := hyp.base.finiteG
  classical
  set F : Set (ClassFunction ↥M ℂ) := OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C
    with hFdef
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ F →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  have hFfin : F.Finite :=
    (OddOrder.Peterfalvi.S08.inducedKernelFamily_finite (⊥ : Subgroup ↥M)).subset
      (fun _ hx => hIKF hx)
  -- per-member column and grid data
  have hcolof : ∀ a ∈ F, ∃ k : Fin hyp.base.w2, k ≠ 0 ∧
      a = ∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i k := by
    intro a ha
    obtain ⟨k, hk0, hkeq⟩ := SOf_reducible_eq_columnSum hG hyp
      (hyp.sOf_subset_SOf hyp.H0C ha) (hallred a ha)
    exact ⟨k, hk0, hkeq.trans (hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd k).symm⟩
  -- the enumeration and the canonical map
  set n := hFfin.toFinset.card with hndef
  set χ : Fin n → ClassFunction ↥M ℂ := fun i => ↑(hFfin.toFinset.equivFin.symm i) with hχdef
  have hχmem : ∀ i, χ i ∈ F := fun i =>
    hFfin.mem_toFinset.mp (hFfin.toFinset.equivFin.symm i).2
  have hχinj : Function.Injective χ := fun i j hij =>
    (Equiv.injective _ (Subtype.ext hij) :)
  set kf : Fin n → Fin hyp.base.w2 := fun i => (hcolof (χ i) (hχmem i)).choose with hkfdef
  have hkf0 : ∀ i, kf i ≠ 0 := fun i => (hcolof (χ i) (hχmem i)).choose_spec.1
  have hkfeq : ∀ i, χ i = ∑ i' : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i' (kf i) :=
    fun i => (hcolof (χ i) (hχmem i)).choose_spec.2
  set Ωof : Fin hyp.base.w2 → ClassFunction G ℂ :=
    fun k => ∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i k with hΩofdef
  -- pairwise data: `⟨μcol_j, μcol_k⟩ = w₁·[j=k]` and `⟨Ω_j, Ω_k⟩ = w₁·[j=k]`
  have hμcols : ∀ j k : Fin hyp.base.w2,
      ClassFunction.inner (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j)
        (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i k)
      = if j = k then (hyp.base.w1 : ℂ) else 0 := by
    intro j k
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      exact hyp.base.muGrid_column_sum_inner_self hG hG.odd j
    · rw [if_neg hjk, OddOrder.RepresentationTheory.inner_sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      exact Finset.sum_eq_zero fun i' _ =>
        hyp.base.muGrid_inner_cross_column hG hG.odd i i' hjk
  have hΩcols : ∀ j k : Fin hyp.base.w2,
      ClassFunction.inner (Ωof j) (Ωof k) = if j = k then (hyp.base.w1 : ℂ) else 0 := by
    intro j k
    rw [hΩofdef]
    rw [OddOrder.RepresentationTheory.inner_sum_left]
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      have hrow : ∀ i : Fin hyp.base.w1,
          ClassFunction.inner (hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
            (∑ i' : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i' j) = 1 := by
        intro i
        rw [OddOrder.RepresentationTheory.inner_sum_right]
        rw [Finset.sum_eq_single i
          (fun i' _ hne => by
            rw [hyp.base.alignedOmegaSigmaGrid_inner hG hG.odd i i' j j,
              if_neg (fun h => hne h.1.symm)])
          (fun h => absurd (Finset.mem_univ i) h)]
        rw [hyp.base.alignedOmegaSigmaGrid_inner hG hG.odd i i j j, if_pos ⟨rfl, rfl⟩]
      rw [Finset.sum_congr rfl (fun i _ => hrow i)]
      simp
    · rw [if_neg hjk]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [OddOrder.RepresentationTheory.inner_sum_right]
      refine Finset.sum_eq_zero fun i' _ => ?_
      rw [hyp.base.alignedOmegaSigmaGrid_inner hG hG.odd i i' j k,
        if_neg (fun h => hjk h.2)]
  -- distinct members have distinct columns
  have hkfinj : ∀ i i' : Fin n, kf i = kf i' → i = i' := by
    intro i i' hk
    apply hχinj
    rw [hkfeq i, hkfeq i', hk]
  -- member-pair inners
  have hχpair : ∀ i i' : Fin n, ClassFunction.inner (χ i) (χ i')
      = if i = i' then (hyp.base.w1 : ℂ) else 0 := by
    intro i i'
    rw [hkfeq i, hkfeq i', hμcols]
    by_cases hii : i = i'
    · subst hii; rw [if_pos rfl, if_pos rfl]
    · rw [if_neg (fun h => hii (hkfinj _ _ h)), if_neg hii]
  have hw1ne0 : (hyp.base.w1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hχorth : ∀ i j : Fin n, i ≠ j → ClassFunction.inner (χ i) (χ j) = 0 := by
    intro i j hij; rw [hχpair, if_neg hij]
  have hχnorm : ∀ i : Fin n, ClassFunction.inner (χ i) (χ i) ≠ 0 := by
    intro i; rw [hχpair, if_pos rfl]; exact hw1ne0
  -- the canonical map and its member images
  set ν₀ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥M G :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap χ
      (fun i => (ClassFunction.inner (χ i) (χ i))⁻¹ • Ωof (kf i)) with hν₀def
  have hν₀apply : ∀ i : Fin n, ν₀ (χ i) = Ωof (kf i) := fun i =>
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.coherentImageMap_apply_eq_of_orthogonal hχorth
        hχnorm i
  -- the column-independent residual `r = Ω_j − τ(μcol_j)`
  set r : ClassFunction G ℂ :=
    Ωof ⟨1, hw2⟩ - hyp.base.tau (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
    with hrdef
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  have hrconst : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      Ωof j - hyp.base.tau (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) = r := by
    intro j hj0
    have h1 := hcolC j hj0
    have h2 := hcolC ⟨1, hw2⟩ hk1
    rw [map_sub] at h1 h2
    rw [hrdef]
    -- `τ μ_j − τ μ₁ = Ω_j − Ω₁` after the `dζ`-cancel
    have hτdiff : hyp.base.tau (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j)
        - hyp.base.tau (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
        = Ωof j - Ωof ⟨1, hw2⟩ := by
      have := congrArg₂ (fun a b => a - b) h1 h2
      simp only [sub_sub_sub_cancel_right] at this
      exact this
    rw [sub_eq_sub_iff_sub_eq_sub]
    exact hτdiff.symm
  -- member degrees are the common `w₁·d ≠ 0` — via the value-at-1 of column sums
  have hdegs : ∀ i : Fin n, ((χ i : ClassFunction ↥M ℂ) : ↥M → ℂ) 1
      = (((∑ i' : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i' ⟨1, hw2⟩ :
          ClassFunction ↥M ℂ)) : ↥M → ℂ) 1 := by
    intro i
    have hmu := hyp.params_mu_eq hG hG.odd
    rw [hkfeq i, ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [← hmu, hyp.params.degree_independent i' (kf i) (hkf0 i),
      hyp.params.degree_independent i' ⟨1, hw2⟩ hk1]
  -- the member-index extraction from a set-membership
  have hidxof : ∀ a ∈ F, ∃ i : Fin n, χ i = a := by
    intro a ha
    exact ⟨hFfin.toFinset.equivFin ⟨a, hFfin.mem_toFinset.mpr ha⟩, by simp [hχdef]⟩
  -- the three lattice fields
  have hinner : ∀ x y : ClassFunction ↥M ℂ,
      x ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) F →
      y ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) F →
      ClassFunction.inner (ν₀ x) (ν₀ y) = ClassFunction.inner x y := by
    intro x y hx hy
    induction hy using Submodule.span_induction with
    | mem b hb =>
        induction hx using Submodule.span_induction with
        | mem a ha =>
            obtain ⟨i, rfl⟩ := hidxof a ha
            obtain ⟨j', rfl⟩ := hidxof b hb
            rw [hν₀apply i, hν₀apply j', hΩcols, hχpair]
            by_cases hij : i = j'
            · subst hij; rw [if_pos rfl, if_pos rfl]
            · rw [if_neg (fun h => hij (hkfinj _ _ h)), if_neg hij]
        | zero => rw [map_zero, ClassFunction.inner_zero_left,
            ClassFunction.inner_zero_left]
        | add u v hu hv ihu ihv =>
            rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left,
              ihu, ihv]
        | smul m u hu ihu =>
            rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ m (ν₀ u),
              ← Int.cast_smul_eq_zsmul ℂ m u, ClassFunction.inner_smul_left,
              ClassFunction.inner_smul_left, ihu]
    | zero => rw [map_zero, ClassFunction.inner_zero_right, ClassFunction.inner_zero_right]
    | add u v hu hv ihu ihv =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ihu, ihv]
    | smul m u hu ihu =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ m (ν₀ u),
          ← Int.cast_smul_eq_zsmul ℂ m u, OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ihu]
  have hD1ne : (((∑ i' : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i' ⟨1, hw2⟩ :
      ClassFunction ↥M ℂ)) : ↥M → ℂ) 1 ≠ 0 := by
    have hμ1mem' : (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩) ∈ F := by
      rw [hFdef, hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩]
      exact columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1 hncH0C htype
    exact inducedKernelFamily_mem_apply_one_ne_zero (hIKF hμ1mem')
  have hres : ∀ x ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) F,
      ν₀ x - hyp.base.tau x
        = ((x 1) / (((∑ i' : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i' ⟨1, hw2⟩ :
            ClassFunction ↥M ℂ)) : ↥M → ℂ) 1) • r := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := hidxof a ha
        rw [hν₀apply i, hdegs i, div_self hD1ne, one_smul]
        have h1 : Ωof (kf i) - hyp.base.tau (χ i) = r := by
          conv_lhs => rw [hkfeq i]
          exact hrconst (kf i) (hkf0 i)
        exact h1
    | zero => rw [map_zero, map_zero, ClassFunction.zero_apply, zero_div, zero_smul, sub_zero]
    | add u v hu hv ihu ihv =>
        rw [map_add, map_add, ClassFunction.add_apply, add_div, add_smul]
        rw [show ν₀ u + ν₀ v - (hyp.base.tau u + hyp.base.tau v)
            = (ν₀ u - hyp.base.tau u) + (ν₀ v - hyp.base.tau v) from by abel, ihu, ihv]
    | smul m u hu ihu =>
        rw [map_zsmul, map_zsmul, ← Int.cast_smul_eq_zsmul ℂ m (ν₀ u),
          ← Int.cast_smul_eq_zsmul ℂ m (hyp.base.tau u), ← Int.cast_smul_eq_zsmul ℂ m u,
          ClassFunction.smul_apply, ← smul_sub, ihu, smul_smul, mul_div_assoc]
  have hextends : ∀ x : ClassFunction ↥M ℂ,
      x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥M) F hyp.base.A0 →
      ν₀ x = hyp.base.tau x := by
    rintro x ⟨hxspan, hxsupp⟩
    have hx1 : x 1 = 0 := by
      by_contra h
      exact hyp.base.one_notMem_A0 (hxsupp (ClassFunction.mem_support.mpr h))
    have h := hres x hxspan
    rw [hx1, zero_div, zero_smul, sub_eq_zero] at h
    exact h
  have hZIrr : ∀ x : ClassFunction ↥M ℂ,
      x ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) F → ν₀ x ∈ ZIrr G := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem a ha =>
        obtain ⟨i, rfl⟩ := hidxof a ha
        rw [hν₀apply i]
        exact Submodule.sum_mem _ fun i' _ =>
          hyp.base.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i' (kf i)
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add u v hu hv ihu ihv => rw [map_add]; exact Submodule.add_mem _ ihu ihv
    | smul m u hu ihu => rw [map_zsmul]; exact Submodule.smul_mem _ m ihu
  -- assemble; the pin is `hν₀apply` at the `μ₁`-member index
  have hμ1mem : (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩) ∈ F := by
    rw [hFdef, hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩]
    exact columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1 hncH0C htype
  set i₁ : Fin n := hFfin.toFinset.equivFin
    ⟨_, hFfin.mem_toFinset.mpr hμ1mem⟩ with hi₁def
  have hχi₁ : χ i₁ = ∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩ := by
    rw [hχdef, hi₁def]
    simp
  have hkfi₁ : kf i₁ = ⟨1, hw2⟩ := by
    -- column uniqueness through the double computation of `⟨μcol_{kf i₁}, μcol_1⟩`
    have hcols_eq : (∑ i' : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i' (kf i₁))
        = ∑ i' : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i' ⟨1, hw2⟩ := by
      rw [← hkfeq i₁, hχi₁]
    have h2 : (if kf i₁ = (⟨1, hw2⟩ : Fin hyp.base.w2) then (hyp.base.w1 : ℂ) else 0)
        = (hyp.base.w1 : ℂ) := by
      rw [← hμcols, hcols_eq, hμcols, if_pos rfl]
    by_contra hne
    rw [if_neg hne] at h2
    exact hw1ne0 h2.symm
  refine ⟨{ nonzero := c₀.nonzero
            extension := ν₀
            extension_inner_eq := hinner
            extends_on_supported := hextends
            extension_mem_ZIrr := hZIrr }, ?_⟩
  change ν₀ (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
    = Ωof ⟨1, hw2⟩
  rw [← hχi₁, hν₀apply i₁, hkfi₁]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8.6) narrow union-coherence capstone** — targeting the *narrow* family `S(H₀C)`
via the `𝒮(H₀C)` coherence (contradicting (11.3)), NOT the deprecated wide `Sset \ SHCSet`
uniform-degree route (false for non-Galois type III/IV, issue 1019).

From the `S(HC)`-coherence `coh` (Peterfalvi's `τ₁`), the **unconditional** `𝒮(H₀C)`-coherence
`hsofC` (`coherent_sOf_H0C`, the `τ₂`), and the column identities `hcol`, the glued `τ₃` map
(`exists_glue_nu_H0C`) assembles a coherent extension of `S(H₀C) = 𝒮(H₀C) ∪ S(HC)` via **Coq's
`bridge_coherent`** engine `S07.coherentUnion_of_glued_of_bridge` (no generation hypothesis).

**Routed through `bridge_coherent`, the caseA-FALSE generation hypothesis `hgen` is gone.**  The old
generation engine `coherentUnion_of_glued_of_generator_mixed_inner_eq_withDiagonal` needed
`hgen : ℤ[𝒮(H₀C) ∪ S(HC)]_{A₀} ⊆ ℤ[…∪D]` with a single degree-`qu` diagonal — **FALSE in Clifford
caseA**, where `𝒮(H₀C)` is mixed degree `{qu, qa}` and `χ_qa − a·ζ` is `A₀`-supported yet outside
that span (issue 1019 update¹³).  `bridge_coherent` avoids generation entirely: it glues along a
**single** `A₀`-supported bridge `χ − φ = ∑ᵢ μ_{i1} − dζ` (`χ ∈ 𝒮(H₀C)`, `φ ∈ ℤ[S(HC)]`), the mixed
`qa` content living inside `hsofC`'s own coherence.  The structural inputs (source/image
orthogonality, integer degrees, the `A = L^#` degree/support dictionary) are all discharged here.

Remaining genuine §14/§9 character content (NONE of it the removed false `hgen`):
- `hmixed` — the (6.7) image-side orthogonality `⟨χ^{τ₂}, φ^{τ₁}⟩ = ⟨χ, φ⟩` (the `b ≡ 0` congruence,
  §14/Sibley-gated) — the SAME genuine content as the old `hmixed`;
- `hbridge_τ` — the (5.8) bridge `τ`-agreement `ν(∑ᵢ μ_{i1} − dζ) = τ(∑ᵢ μ_{i1} − dζ)`, which via
the
  `ν`-agreements + `hcol` is `hsofC.extension (∑ᵢ μ_{i1}) = ∑ᵢ ω^σ_{i1}` (the `𝒮(H₀C)` coherent
  extension sends the reducible μ-column to the aligned ω^σ-column).  `coherent_sOf_H0C` carries no
  such μ-column image pin — this is the honest heir of the old `hDτ` sorry, §14/§9-gated.

Two further bridge inputs (`hφY : dζ ∈ ℤ[S(HC)]`, `hbridge_supp : ∑ᵢ μ_{i1} − dζ` `A₀`-supported)
need `ζ ∈ S(HC)` and the degree match `(∑ᵢ μ_{i1})(1) = d·ζ(1)`, which the *signature* does not
carry (only `ζ ∈ inducedFamily M ⊋ S(HC)`); both are caller-supplied facts (`ζ` irreducible of
degree `w₁`; `secondDerived_eq_HC` + `SOf_secondDerived_eq`; `degree_independent`).  Threading
`ζ ∈ hyp.SOf hyp.HC` (+ degree) into the signature is what discharges them.  See issue 1019
update¹³. -/
theorem coherent_SOf_H0C_of_column_identities [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G} (hyp : Hypothesis M)
    [NeZero (Nat.card (hyp.base.toHypothesis46 hG hG.odd).W1)]
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.HC) hyp.base.A0)
    {ζ : ClassFunction ↥M ℂ} (_hζS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M) {d : ℕ}
    (hζHC : ζ ∈ hyp.SOf hyp.HC)
    (hζdeg : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) 1 = (d : ℂ) * ζ 1)
    (hcol : ∀ j : Fin hyp.base.w2, j ≠ 0 →
      hyp.base.tau ((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i j) - (d : ℂ) • ζ)
        = (∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
          - (d : ℂ) • coh.extension ζ)
    (hncH0C : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0))
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    Nonempty (OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau (hyp.SOf hyp.H0C) hyp.base.A0) := by
  have := hyp.base.finiteG
  classical
  -- The reducible μ-column bridge anchor `χ = ∑ᵢ μ_{i1} ∈ 𝒮(H₀C)`, at the nonzero column `j = 1`.
  have hw2 : 1 < hyp.base.w2 := hyp.params.w2_prime.one_lt
  have hk1 : (⟨1, hw2⟩ : Fin hyp.base.w2) ≠ 0 := by
    intro heq; have := congrArg Fin.val heq; simp at this
  -- Kernel-family embeddings of both families into the pairwise-orthogonal `S((M')^#)`.
  have hIKF : ∀ ⦃x : ClassFunction ↥M ℂ⦄,
      x ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := fun {x} hx =>
    OddOrder.Peterfalvi.S08.inducedKernelFamily_antitone bot_le
      (by rw [← hyp.SOf_eq]; exact hyp.sOf_subset_SOf hyp.H0C hx)
  have hXbridge : ∀ ⦃x : ClassFunction ↥M ℂ⦄, x ∈ hyp.SOf hyp.HC →
      x ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) (hyp.HC.subgroupOf M) := fun {x} hx => by
    rw [hyp.SOf_eq] at hx; exact hx
  have hχmem : (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
      ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C := by
    rw [hyp.base.muGrid_columnSum_eq_columnSum hG hG.odd ⟨1, hw2⟩]
    exact columnSum_muColumnChar_mem_sOf_H0C_of_noncoherent hG hyp ⟨1, hw2⟩ hk1 hncH0C htype
  -- `d·ζ ∈ ℤ[S(HC)]`: `ζ ∈ S(HC)` (`hζHC`) plus `(d:ℂ)•ζ = (d:ℤ)•ζ` (a `zsmul` of a span member).
  have hdζspan : (d : ℂ) • ζ ∈ Submodule.span ℤ (hyp.SOf hyp.HC) := by
    have hcast : (d : ℂ) • ζ = (d : ℤ) • ζ := by
      rw [← Int.cast_smul_eq_zsmul ℂ (d : ℤ) ζ, Int.cast_natCast]
    rw [hcast]
    exact Submodule.smul_mem _ (d : ℤ) (Submodule.subset_span hζHC)
  -- the `A₀`-support of the bridge `θ = ∑ᵢ μ_{i1} − dζ` (degree match `hζdeg`)
  have hθsupp : (((∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
      - (d : ℂ) • ζ : ClassFunction ↥M ℂ)).support ⊆ hyp.base.A0 := by
    have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
      hyp.base.mderivSharp_subset_A0 (hIKF hχmem) (hXbridge hζHC) (hζdeg ⟨1, hw2⟩ hk1)
    rwa [← Nat.cast_smul_eq_nsmul ℂ d ζ] at h
  -- **the pinned `𝒮(H₀C)`-coherence** (issue 1023, the Coq `tau2muj` WLOG made constructive):
  -- case-1 (γ-trick, an irreducible member exists) or case-2 (all-reducible canonical
  -- construction); `hpin` is the (5.8) μ-column image pin that discharges `hbridge_τ` below.
  obtain ⟨hsofC, hpin⟩ : ∃ c : OddOrder.Peterfalvi.S07.IsCoherent hyp.base.tau
      (OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C) hyp.base.A0,
      c.extension (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
        = ∑ i : Fin hyp.base.w1, hyp.base.alignedOmegaSigmaGrid hG hG.odd i ⟨1, hw2⟩ := by
    by_cases hirr : ∃ ξ ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C,
        IsIrreducibleCharacter ξ
    · obtain ⟨ξ, hξ, hξirr⟩ := hirr
      obtain ⟨c⟩ := coherent_sOf_H0C hG hyp hncH0C htype
      exact ⟨c, coherent_sOf_H0C_extension_muColumnSum_pin_of_irr hG hyp c coh hζHC hw2
        hθsupp (hcol ⟨1, hw2⟩ hk1) hξ hξirr hncH0C htype⟩
    · push Not at hirr
      exact exists_pinned_coherent_sOf_H0C_of_all_reducible hG hyp
        (coherent_sOf_H0C hG hyp hncH0C htype).some hw2 hcol hirr hncH0C htype
  obtain ⟨ν, hagreeSHC, hagreeSof⟩ := exists_glue_nu_H0C hyp coh hsofC
  refine ⟨?_⟩
  rw [hyp.SOf_H0C_eq_SOf_HC_union_sOf, Set.union_comm]
  -- **`bridge_coherent`** (no generation hypothesis) — engine `X = 𝒮(H₀C)`, `Y = S(HC)`.
  refine OddOrder.Peterfalvi.S07.coherentUnion_of_glued_of_bridge hsofC coh ν hagreeSof hagreeSHC
    (fun u hu v hv => by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        span_inner_SOf_HC_sOf_H0C_eq_zero hyp hv hu, star_zero])
    ?hmixed hyp.base.one_notMem_A0
    (fun x hx => inducedKernelFamily_mem_intDegree (hIKF hx))
    (fun y hy => inducedKernelFamily_mem_intDegree (hXbridge hy))
    (fun η hη hη0 => ⟨hη, inducedKernelFamily_zSpan_support_of_apply_one_eq_zero
      hyp.base.mderivSharp_subset_A0 (Submodule.span_mono (fun _ hx => hIKF hx) hη) hη0⟩)
    (fun η hη hη0 => ⟨hη, inducedKernelFamily_zSpan_support_of_apply_one_eq_zero
      hyp.base.mderivSharp_subset_A0 (Submodule.span_mono (fun _ hx => hXbridge hx) hη) hη0⟩)
    (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩) ((d : ℂ) • ζ)
    hχmem ?hφY (inducedKernelFamily_mem_apply_one_ne_zero (hIKF hχmem)) ?hbridge_supp ?hbridge_τ
  case hmixed =>
    -- **(6.7) image-side orthogonality** (the Coq `coherent_ortho`): after the `ν`-agreements
    -- the goal is `⟨χ^{τ₂}, φ^{τ₁}⟩ = ⟨χ, φ⟩` (`χ ∈ 𝒮(H₀C)`, `φ ∈ S(HC)`).  Both sides vanish:
    -- the characters are cross-orthogonal (`SOf_HC_inner_sOf_H0C_eq_zero`), and the coherent
    -- images are partial `R`-family sums over cross-orthogonal families
    -- (`SOf_coherent_extension_cross_orthogonal`, the two-stratum (5.5)+(5.2.e) engine,
    -- issue 1023).
    intro x hx y hy
    rw [hagreeSof x hx, hagreeSHC y hy]
    have hxc : x.conj ∈ OddOrder.Peterfalvi.S11.sOf hyp.s11Setup hyp.H0C :=
      OddOrder.Peterfalvi.S11.sOf_closedUnderConjugate hyp.s11Setup hyp.H0C hx
    have hyc : y.conj ∈ hyp.SOf hyp.HC := by
      rw [hyp.SOf_eq] at hy ⊢
      exact OddOrder.Peterfalvi.S08.inducedKernelFamily_closedUnderConjugate _ hy
    have hxy0 : ClassFunction.inner x y = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        SOf_HC_inner_sOf_H0C_eq_zero hyp hy hx, star_zero]
    have hxyc0 : ClassFunction.inner x y.conj = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        SOf_HC_inner_sOf_H0C_eq_zero hyp hyc hx, star_zero]
    have hxx : ClassFunction.inner x x ≠ 0 := by
      obtain ⟨he, hpos⟩ :=
        OddOrder.Peterfalvi.S08.inducedKernelFamily_inner_self_real_pos (hIKF hx)
      rw [he]; exact Complex.ofReal_ne_zero.mpr hpos.ne'
    have hne1 : x ≠ y := fun h => by cases h; exact hxx hxy0
    have hne2 : x ≠ y.conj := fun h => by cases h; exact hxx hxyc0
    rw [hxy0]
    exact SOf_coherent_extension_cross_orthogonal hG hyp
      (hyp.sOf_subset_SOf hyp.H0C) (le_refl (hyp.SOf hyp.HC)) hsofC coh
      hx hxc hy hyc hne1 hne2
  case hφY =>
    -- `(d:ℂ)•ζ ∈ ℤ[S(HC)]`: now discharged from `hζHC : ζ ∈ S(HC)` (threaded into the signature).
    exact hdζspan
  case hbridge_supp =>
    -- `∑ᵢ μ_{i1} − dζ ∈ ℤ[𝒮(H₀C) ∪ S(HC)]_{A₀}`.  The `ℤ`-span part is `hχmem` + `hdζspan`; the
    -- `A₀`-support part is `inducedKernelFamily_scaledDiff_support` from the degree match `hζdeg`
    -- (`(∑ᵢ μ_{i1})(1) = d·ζ(1)`).  Both are now threaded through the signature.
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, ?_⟩
    · exact Submodule.sub_mem _ (Submodule.subset_span (Set.mem_union_left _ hχmem))
        (Submodule.span_mono Set.subset_union_right hdζspan)
    · have h := OddOrder.Peterfalvi.S08.inducedKernelFamily_scaledDiff_support
        hyp.base.mderivSharp_subset_A0 (hIKF hχmem) (hXbridge hζHC) (hζdeg ⟨1, hw2⟩ hk1)
      rwa [← Nat.cast_smul_eq_nsmul ℂ d ζ] at h
  case hbridge_τ =>
    -- **(5.8) bridge `τ`-agreement `ν(∑ᵢ μ_{i1} − dζ) = τ(∑ᵢ μ_{i1} − dζ)`**: via the
    -- `ν`-agreements this is `hsofC.extension (∑ᵢ μ_{i1}) − d·ζ^{τ₁} = ∑ᵢ ω^σ_{i1} − d·ζ^{τ₁}`,
    -- i.e. the (5.8) μ-column image pin `hpin` of the pinned coherence (issue 1023), matched
    -- against the column identity `hcol`.
    have hνμ : ν (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩)
        = hsofC.extension (∑ i : Fin hyp.base.w1, hyp.base.muGrid hG hG.odd i ⟨1, hw2⟩) :=
      hagreeSof _ hχmem
    have hνζ : ν ((d : ℂ) • ζ) = (d : ℂ) • coh.extension ζ := by
      have hcast : (d : ℂ) • ζ = (d : ℤ) • ζ := by
        rw [← Int.cast_smul_eq_zsmul ℂ (d : ℤ) ζ, Int.cast_natCast]
      rw [hcast, map_zsmul, hagreeSHC ζ hζHC, ← Int.cast_smul_eq_zsmul ℂ (d : ℤ),
        Int.cast_natCast]
    rw [map_sub, hνμ, hνζ, hpin, hcol ⟨1, hw2⟩ hk1]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8), the genuine non-orthogonality — narrow `𝒮(H₀C)` route, refuter core**
(the honest replacement of `S12.exists_zeta_residual_not_orthogonal`, which routed through the
deprecated wide `Sset \ SHCSet` uniform-degree lemma, false for non-Galois type III/IV, issue
1019).  The closing (11.3) noncoherence is the `hrefute` hypothesis (issue 1020 Phase 3),
instantiated by the unconditional heir (`S_H0C_not_coherent_unconditional`,
`S13_TypeDetermination`; the legacy sorried (11.3) route is retired, issue 9087).

Under Hypothesis (10.1), there is an irreducible `ζ ∈ S = inducedFamily M` of degree `w₁` for which
the residual `(μ₀ − ζ)^τ − ∑_i ω_{i0}^σ` is **not** orthogonal to `(Irr W)^σ`.  Same statement as
the
S12 version; the proof reuses the S12 residual machinery (`exists_charParameters_full`,
`exists_coherent_extension_h114_of_orthogonal`, `tau_muColumnSum_sub_dzeta_eq_of_residualData`)
verbatim to build the coherent extension `ν` and the column identities `hcol` from the orthogonality
assumption, then closes via the **narrow** capstone `coherent_SOf_H0C_of_column_identities`
(coherence of `S(H₀C)`) contradicting the (11.3) non-coherence `hrefute` — instead of the wide
`S12.coherent_Sset_of_column_identities`/(10.8) route.

World-bridge threading: the residual machinery and the conclusion live in the §12 `hyp`-world, while
the narrow capstone/refuter (`coherent_sOf_H0C`, the (11.3) non-coherence) live in the §13
`s13hyp`-world
(`s13hyp.base = hyp` propositionally, via `exists_hypothesis_of_isTypeIIIorIV`). Since
`s13hyp.base =
hyp` holds only up to `hbase` (not definitionally), the whole goal is first `rw [←
hbase]`-transported
into the `s13hyp.base`-world, so the S12 machinery and the narrow endpoint share one world and the
`isCoherent_of_subset ν` restriction keeps `coh.extension = ν.extension` definitionally (feeding
`hcol`
into the capstone with no cast). -/
theorem zeta_residual_not_orthogonal_H0C_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0))
    {ζ : ClassFunction ↥M ℂ} (hζS : ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M)
    (hζirr : IsIrreducibleCharacter ζ) (hζdeg : ζ 1 = (hyp.w1 : ℂ)) :
      ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
        ClassFunction.inner
          ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
            - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  -- Move the whole goal into the §13 `s13hyp.base`-world so the S12 residual machinery and the
  -- narrow (11.3) endpoint share one world (`s13hyp.base = hyp` only propositionally).
  obtain ⟨s13hyp, hbase⟩ := OddOrder.Peterfalvi.S13.exists_hypothesis_of_isTypeIIIorIV hG hyp htype
  rw [← hbase] at hM2 hHcard hζdeg ⊢
  -- (10.2)/(10.3) character parameters built around the **given** `ζ` (the `∀ ζ` book form).
  obtain ⟨params, hzeq, hmu, -, hzS, hz1, -, hδpm, hδindep⟩ :=
    s13hyp.base.exists_charParameters_full_of_zeta hG hζS hζirr hζdeg
  intro h_orth
  rw [← hzeq] at h_orth
  -- (11.8.1) `δ = 1`; (11.8.4) the coherent extension `ν` and `h114` from orthogonality.
  have hδ1 : params.delta = 1 := s13hyp.base.charParam_delta_eq_one hG htype params hmu hδpm
  obtain ⟨ν, hνconj, h114⟩ :=
    s13hyp.base.exists_coherent_extension_h114_of_orthogonal hG hG.odd hzS params.zeta_irreducible
      hz1 h_orth
  -- (11.8.1)/(5.7) the orthonormal coherent image `R`, `|R| = n`.
  obtain ⟨R, hZ, hRorth, hRmem, hRrev, hRcard⟩ := s13hyp.base.exists_coherentImage_SHC ν
  have hRn : R.card = params.n :=
    hRcard.trans (s13hyp.base.card_SHCSet_filter_eq_charParam_n hG htype params hmu hδpm hM2 hHcard)
  have hnf : (params.n : ℤ) * (s13hyp.base.w1 : ℤ) = (params.d : ℤ) - 1 := by
    rw [← hδ1]; exact params.n_formula
  have hd : (params.d : ℂ) = (s13hyp.base.w1 : ℂ) * (params.n : ℂ) + 1 := by
    have h : (params.n : ℂ) * (s13hyp.base.w1 : ℂ) = (params.d : ℂ) - 1 := by exact_mod_cast hnf
    linear_combination -h
  have hμ0all : ∀ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i 0 1 = 1 :=
    fun i => s13hyp.base.muGrid_zero_column_apply_one hG hG.odd i
  -- (11.8.2)–(11.8.6 opening) the column identities `(μ_j − dζ)^τ = ∑_i ω_{ij}^σ − dζ^{τ₁}`.
  have hcol : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      s13hyp.base.tau ((∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j)
          - (params.d : ℂ) • params.zeta)
        = (∑ i : Fin s13hyp.base.w1, s13hyp.base.alignedOmegaSigmaGrid hG hG.odd i j)
          - (params.d : ℂ) • ν.extension params.zeta := by
    intro j hj
    have hdegall : ∀ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    have hδjj : s13hyp.base.muColumnSign hG hG.odd j = 1 := (hδindep j hj).trans hδ1
    exact s13hyp.base.tau_muColumnSum_sub_dzeta_eq_of_residualData hG ν hνconj hG.odd hj hzS
      params.zeta_irreducible hz1 params.w2_prime hd hnf hdegall hμ0all hδjj params.two_le_n
      hRn hZ hRorth hRmem hRrev h114
  -- `ζ ∈ S(HC)`: `ζ` is a degree-`w₁` irreducible in `S`, i.e. a member of `S(M'') = S(HC)`
  -- (`SOf_secondDerived_eq` characterizes `S(M'')` as the degree-`w₁` irreducible subfamily;
  -- `secondDerived_eq_HC` (11.5) identifies `M'' = HC`).
  have hζHC : params.zeta ∈ s13hyp.SOf s13hyp.HC := by
    rw [← secondDerived_eq_HC_of_noncoherent hG s13hyp (hrefute s13hyp) htype,
      s13hyp.SOf_secondDerived_eq hG]
    exact ⟨hzS, params.zeta_irreducible, hz1⟩
  -- Degree match `(∑ᵢ μ_{ij})(1) = d·ζ(1)`: each `μ_{ij}(1) = d` (`degree_independent`, `j ≠ 0`),
  -- so the `w₁`-term sum is `w₁·d = d·w₁ = d·ζ(1)` (`hz1 : ζ(1) = w₁`).
  have hζdeg : ∀ j : Fin s13hyp.base.w2, j ≠ 0 →
      (∑ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j) 1
        = (params.d : ℂ) * params.zeta 1 := by
    intro j hj
    have hall : ∀ i : Fin s13hyp.base.w1, s13hyp.base.muGrid hG hG.odd i j 1 = (params.d : ℂ) :=
      fun i => hmu ▸ params.degree_independent i j hj
    rw [ClassFunction.finset_sum_apply]
    simp only [hall, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hz1]
    ring
  -- (11.8.6) the narrow τ₃ union makes `S(H₀C)` coherent, contradicting the (11.3) non-coherence.
  -- `coh` = the `ν` (h_orth-derived `S(HC)` coherence) restricted to `S(HC) ⊆ SHCSet`
  -- (`isCoherent_of_subset`, keeping `coh.extension = ν.extension`); the narrow capstone consumes
  -- `hcol` and the unconditional `𝒮(H₀C)`-coherence (`coherent_sOf_H0C`, threaded inside).
  have : NeZero (Nat.card (s13hyp.base.toHypothesis46 hG hG.odd).W1) :=
    ⟨by have := (s13hyp.base.toHypothesis46 hG hG.odd).one_lt_card_W1; omega⟩
  exact hrefute s13hyp (coherent_SOf_H0C_of_column_identities hG s13hyp
    (isCoherent_of_subset ν (SOf_HC_subset_SHCSet hG s13hyp)
      (coherent_SOf_HC hG s13hyp).some.nonzero) hzS hζHC hζdeg hcol (hrefute s13hyp) htype)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (11.8), witness form.**  The `∃ ζ` shape consumed by (11.9.b)
(`w2_lt_w1_of_residual_not_orthogonal`): instantiate the `∀ ζ` core
`zeta_residual_not_orthogonal_H0C_of_refuter` at the `ζ` supplied by
`exists_zeta_in_inducedFamily_degree_w1`.

The book statement is the `∀` one — (11.8)'s proof fixes an arbitrary `ζ ∈ S(HC)` and derives a
contradiction with (11.3) — so the core carries the mathematics and this is only the existential
packaging its downstream happens to want. -/
theorem exists_zeta_residual_not_orthogonal_H0C_of_refuter [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) {M : Subgroup G}
    (hyp : OddOrder.Peterfalvi.S12.Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M)
    (hM2 : secondDerivedInAmbient M
      = hyp.typeP.H ⊔ (hyp.typeP.U ⊓ Subgroup.centralizer (hyp.typeP.H : Set G)))
    (hHcard : Nat.card ↥hyp.typeP.H = hyp.w2 ^ hyp.w1)
    (hrefute : ∀ s13hyp : Hypothesis M,
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        s13hyp.base.tau (s13hyp.SOf s13hyp.H0C) s13hyp.base.A0)) :
    ∃ ζ : ClassFunction ↥M ℂ, ζ ∈ OddOrder.Peterfalvi.S12.inducedFamily M ∧
      IsIrreducibleCharacter ζ ∧ ζ 1 = (hyp.w1 : ℂ) ∧
      ¬ ∀ (i : Fin hyp.w1) (j : Fin hyp.w2),
        ClassFunction.inner
          ((hyp.tau ((∑ i' : Fin hyp.w1, hyp.muGrid hG hG.odd i' 0) - ζ))
            - ∑ i' : Fin hyp.w1, hyp.alignedOmegaSigmaGrid hG hG.odd i' 0)
          (hyp.alignedOmegaSigmaGrid hG hG.odd i j) = 0 := by
  have := hyp.finiteG
  obtain ⟨ζ, hζS, hζirr, hζdeg⟩ :=
    OddOrder.Peterfalvi.S12.exists_zeta_in_inducedFamily_degree_w1 hyp.typeP hG.odd
      (OddOrder.Peterfalvi.S12.typePData_W1_hall_coprime hG hyp.maximal (hyp.bgTypeP hG) hyp.typeP)
  exact ⟨ζ, hζS, hζirr, hζdeg,
    zeta_residual_not_orthogonal_H0C_of_refuter hG hyp htype hM2 hHcard hrefute hζS hζirr hζdeg⟩

end OddOrder.Peterfalvi.S13


