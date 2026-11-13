-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S13_SixTwoBridge
-- name    : OddOrder_Peterfalvi_S13_SixTwoBridge
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T13:32:17.322125+00:00
-- url     : https://prove2.me/theorems/005e5792-b10d-437e-939b-001b76b4dbd7
-- title:
--   Peterfalvi §11: bridge to the general (6.2) index bound
-- statement:
--   Formalizes the routine pinning of Peterfalvi (11.3)/(11.4) to the general (6.2)/(6.3) index bound (Peterfalvi, *Character Theory for the Odd Order Theorem*, §11), discharging the hypotheses of the general result in the §10/§11 context.
--
--   Main declarations: `exists_source_index_le_two_psi` (The h56 producer, fully pinned to the §10/§11 context).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S13_SixTwoBridge.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S13_SixTwoBridge.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S12_MaximalIII_IV_V
import Definitions.Def_OddOrder_Peterfalvi_S08_SixTwoGeneral

namespace OddOrder.Peterfalvi.S12

open OddOrder.RepresentationTheory

open OddOrder.GroupTheory

open scoped FiniteInduce

variable {G : Type*} [Group G] {M : Subgroup G}

namespace Hypothesis

/-- **`hKsupp` pin: `(M')^# ⊆ A₀(M)` inside `M`.**  Peterfalvi's type-`P` support satisfies
`A(M) = (M')^#` (`typePA_eq_sharpSubgroup_derivedInG`) and `A₀(M) = A(M) ∪ V^M ⊇ A(M)`, so a
nonidentity element of `M' = (derivedInG M).subgroupOf M` lies in the Dade support.  This is
the `hKsupp` input of the h56 producer: member differences of the induced family vanish off
`(M')^#`, hence are `A₀`-supported. -/
theorem mderivSharp_subset_A0 (hyp : Hypothesis M) :
    ∀ x : ↥M, x ∈ (derivedInG M).subgroupOf M → x ≠ 1 → x ∈ hyp.A0 := by
  intro x hxK hx1
  simp only [A0, OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  refine Set.mem_union_left _ ?_
  rw [typePA_eq_sharpSubgroup_derivedInG]
  refine ⟨Subgroup.mem_subgroupOf.mp hxK, ?_⟩
  simp only [Set.mem_singleton_iff]
  intro hcoe
  exact hx1 (by ext; exact hcoe)

/-- **`h1A` pin: `1 ∉ A₀(M)`** (`S04.Hypothesis.ne_one`: the Dade support avoids the
identity). -/
theorem one_notMem_A0 (hyp : Hypothesis M) : (1 : ↥M) ∉ hyp.A0 := by
  have := hyp.finiteG
  intro h
  exact hyp.dadeData.dade.ne_one (a := ((1 : ↥M) : G)) h (OneMemClass.coe_one M)

/-- **`hodd` pin: `|M|` is odd** in the minimal-simple-odd ambient (`|M| ∣ |G|`). -/
theorem card_odd_of_isMinimalSimpleOdd [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (_hyp : Hypothesis M) : Odd (Nat.card ↥M) :=
  hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)

/-- **`|W₁|` is coprime to `|M'|`** (types III/IV): `M' = H ⋊ U` with
`(|H|, |U·W₁|) = 1` (Peterfalvi (8.4), `typeP_coprime_H_uW1`) killing the `H`-side, and
`U ⋊ W₁` Frobenius (`typeP_uW1_frobenius`) killing the `U`-side
(`coprime_card_kernel_complement`).  This is the coprimality input of the `W₁`-fixed-point
lifting on `M'/M''` behind the h56 anchor (Peterfalvi (8.4.d)). -/
theorem coprime_card_W1_derived [Finite G]
    (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    (htype : IsTypeIII M ∨ IsTypeIV M) :
    Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥(derivedInG M)) := by
  have : Fintype G := Fintype.ofFinite _
  have hnt : TypePNontrivialCore M hyp.typeP :=
    typePNontrivialCore_of_isTypeIIIorIV htype hyp.typeP
  have hU : hyp.typeP.U ≠ ⊥ := hnt.1
  -- `q` is coprime to `|H|`: `(|H|, |U ⊔ W₁|) = 1` and `|W₁| ∣ |U ⊔ W₁|`.
  have hcopH : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥hyp.typeP.H) := by
    refine Nat.Coprime.coprime_dvd_left ?_ (OddOrder.Peterfalvi.S11.typeP_coprime_H_uW1
      hyp.typeP hU).symm
    exact Subgroup.card_dvd_of_le le_sup_right
  -- `q` is coprime to `|U|`: `U ⋊ W₁` is Frobenius with kernel `U`, complement `W₁`.
  have hcopU : Nat.Coprime (Nat.card ↥hyp.W1) (Nat.card ↥hyp.typeP.U) := by
    have hF := OddOrder.Peterfalvi.S11.typeP_uW1_frobenius hyp.typeP hU
    have hc := hF.coprime_card_kernel_complement
    have h1 : Nat.card ↥(hyp.typeP.U.subgroupOf (hyp.typeP.U ⊔ hyp.typeP.W1))
        = Nat.card ↥hyp.typeP.U :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
    have h2 : Nat.card ↥(hyp.typeP.W1.subgroupOf (hyp.typeP.U ⊔ hyp.typeP.W1))
        = Nat.card ↥hyp.typeP.W1 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
    have : Nat.Coprime (Nat.card ↥hyp.typeP.U) (Nat.card ↥hyp.typeP.W1) := by
      rw [← h1, ← h2]; exact hc
    exact this.symm
  -- combine over `|M'| = |H| · |U|` (`derived_complement`).
  have hcard : Nat.card ↥(derivedInG M)
      = Nat.card ↥hyp.typeP.H * Nat.card ↥hyp.typeP.U := by
    have hmul := hyp.typeP.derived_complement.card_mul_card
    rw [← hmul,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.H_le).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hyp.typeP.U_le).toEquiv]
  rw [hcard]
  exact Nat.Coprime.mul_right hcopH hcopU

/-- **The h56 anchor, fully discharged for the §11 context**: for any `A' ≤ M'` (normal trace,
proper-commutator quotient — automatic for `A' ⊊ M'` by solvability), `S(A')` contains an
*irreducible* member of degree `|M : M'|`.  A nontrivial linear source `θ` trivial on `A'`
exists by `exists_irreducibleCharacter_ne_trivial_subset_kernel_of_commutator_ne_top`; its
`Ind_{M'}^M θ` then has degree `|M:M'|` — which is all Peterfalvi (6.2) asks for ("Since `K` is
solvable, `K/A` has a non-trivial irreducible character of degree 1, whence `S(A)` contains a
character of degree `|L:K|`", p. 30).  **No irreducibility, hence no inertia condition**: the (5.6)
engine carries the anchor norm `‖χ₁‖²` symbolically (`S08.crux1_of_memberFamilyW`), so the
`inertia θ = M'` route via (8.4.d) that the earlier formalization needed is not required. -/
theorem exists_anchor [Finite G]
    {A' : Subgroup ↥M} [(A'.subgroupOf ((derivedInG M).subgroupOf M)).Normal]
    (hA'comm : commutator (↥((derivedInG M).subgroupOf M)
      ⧸ A'.subgroupOf ((derivedInG M).subgroupOf M)) ≠ ⊤) :
    ∃ χ₁ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A',
      χ₁ 1 = ((((derivedInG M).subgroupOf M)).index : ℂ) :=
  S08.exists_inducedKernelFamily_member_degree_index hA'comm

/-- **Solvable-quotient commutator pin**: for a proper trace `X ⊓ M' ≠ M'`, the quotient
`M'/(X ⊓ M')` is a nontrivial solvable group, so its commutator subgroup is proper.  This is the
hypothesis feeding both the anchor (`exists_anchor`) and the `S(X)`-nonemptiness
(`inducedKernelFamily_nonempty_of_commutator_ne_top`); `M` is solvable as a proper subgroup of
the minimal counterexample (`isSolvable_of_lt_top`). -/
theorem commutator_quotient_ne_top [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {X : Subgroup ↥M} [(X.subgroupOf ((derivedInG M).subgroupOf M)).Normal]
    (hXne : X.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤) :
    commutator (↥((derivedInG M).subgroupOf M)
      ⧸ X.subgroupOf ((derivedInG M).subgroupOf M)) ≠ ⊤ := by
  have : Group.IsSolvable ↥M := hG.isSolvable_of_lt_top M (lt_top_iff_ne_top.mpr hyp.maximal.1)
  have : Group.IsSolvable ↥((derivedInG M).subgroupOf M) := inferInstance
  have : Group.IsSolvable (↥((derivedInG M).subgroupOf M)
      ⧸ X.subgroupOf ((derivedInG M).subgroupOf M)) := inferInstance
  have : Nontrivial (↥((derivedInG M).subgroupOf M)
      ⧸ X.subgroupOf ((derivedInG M).subgroupOf M)) := by
    obtain ⟨y, hy⟩ : ∃ y, y ∉ X.subgroupOf ((derivedInG M).subgroupOf M) := by
      by_contra hall
      push Not at hall
      exact hXne ((Subgroup.eq_top_iff' _).mpr hall)
    exact ⟨QuotientGroup.mk y, 1, fun h => hy ((QuotientGroup.eq_one_iff y).mp h)⟩
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne

end Hypothesis

/-- **The §10 family `S` is the general kernel-filter family at `X = ⊥`**: the `⊥`-kernel
condition is vacuous (`1 ∈ Ker θ` always), so `S12.inducedFamily M` (the pinned `Sset`) equals
`S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥`.  Through this identification the
whole `S08_SixTwoGeneral` layer (family structure, B2, the h56 producer) applies to the §11
family, with the §11 filtration `S(X)` given by `inducedKernelFamily K X`. -/
theorem inducedFamily_eq_inducedKernelFamily_bot [Finite G] :
    inducedFamily M = OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) (⊥ : Subgroup ↥M) := by
  ext φ
  constructor
  · rintro ⟨θ, hθne, rfl⟩
    refine ⟨θ, hθne, ?_, rfl⟩
    intro x hx
    have hx1 : x = 1 := by
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hx
      ext
      exact congrArg Subtype.val hx
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel, hx1]
    rfl
  · rintro ⟨θ, hθne, -, rfl⟩
    exact ⟨θ, hθne, rfl⟩

namespace Hypothesis

open scoped FiniteInduce in
/-- **The h56 producer, fully pinned to the §10/§11 context** (`S12.Hypothesis M`): Peterfalvi's
(6.2) break index bound `|M':A'| − 1 ≤ 2ψ(1)` over the genuine Dade data
(`hyp.dadeData.dade` on `A₀(M)`, `hyp.hconj`), kernel `K = M' = (derivedInG M).subgroupOf M`,
with the routine pins discharged (`mderivSharp_subset_A0`, `one_notMem_A0`,
`card_odd_of_isMinimalSimpleOdd`).  The remaining hypotheses are exactly the issue-2022
obligations: the **anchor** (an irreducible degree-`|M:M'|` member of `S(A')`, from the
`W₁`-action), `S(B)`-nonemptiness, and the **(5.2.d) decomposition data** (grid-backed).

The conclusion is the `h56` oracle shape of
`six_three_of_six_two_oracle`/`six_two_general` (`S08_Theorem62_63_Standalone`) at
`SOf X := inducedKernelFamily K X`, `τ := hyp.tau`, `A₀ := hyp.A0`. -/
theorem exists_source_index_le_two_psi
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {A' B : Subgroup ↥M} [A'.Normal]
    (hanchor : ∃ χ₁ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily
        ((derivedInG M).subgroupOf M) A',
      χ₁ 1 = (((derivedInG M).subgroupOf M).index : ℂ))
    (hSBne : (OddOrder.Peterfalvi.S08.inducedKernelFamily
      ((derivedInG M).subgroupOf M) B).Nonempty)
    (hdatum : ∀ (S₁ : Set (ClassFunction ↥M ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A' ∪
        OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        S₁ hyp.A0),
      ∀ (ψ : ClassFunction ↥M ℂ),
        ψ ∈ OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
        ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥M ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        (S₁ ∪ {ψ, ψ.conj}) hyp.A0) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
            (hyp.dadeData.dade.fullDadeIsometryData)) ψ (a • χ₁),
        Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData) ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
              (hyp.dadeData.dade.fullDadeIsometryData)) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A')
      hyp.A0))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      (OddOrder.Peterfalvi.S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
      hyp.A0)) :
    ∃ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      (↑(B.subgroupOf ((derivedInG M).subgroupOf M)) :
          Set ↥((derivedInG M).subgroupOf M)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) ∧
      (Nat.card (↥((derivedInG M).subgroupOf M) ⧸
          A'.subgroupOf ((derivedInG M).subgroupOf M)) : ℝ) - 1 ≤
        2 * (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (θ : ClassFunction
            ↥((derivedInG M).subgroupOf M) ℂ) 1).re := by
  have := hyp.finiteG
  have : ((derivedInG M).subgroupOf M).Normal := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
    infer_instance
  exact OddOrder.Peterfalvi.S08.exists_source_index_le_two_psi_of_break
    hyp.dadeData.dade (hyp.card_odd_of_isMinimalSimpleOdd hG)
    hyp.mderivSharp_subset_A0 hyp.one_notMem_A0 hanchor hSBne hdatum hAcoh hBncoh

/-- **The h56 producer with anchor and nonemptiness auto-discharged**: only the coherence
dichotomy and the grid-backed (5.2.d) decomposition data (`hdatum`) remain.  The anchor comes
from `exists_anchor` (Peterfalvi (8.4.d)) and `S(B)`-nonemptiness from the solvable-quotient
linear character, both via `commutator_quotient_ne_top` at the proper traces `A', B ⊊ M'`. -/
theorem exists_source_index_le_two_psi_of_ne_top
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {A' B : Subgroup ↥M} [A'.Normal]
    [(A'.subgroupOf ((derivedInG M).subgroupOf M)).Normal]
    [(B.subgroupOf ((derivedInG M).subgroupOf M)).Normal]
    (hA'ne : A'.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤)
    (hBne : B.subgroupOf ((derivedInG M).subgroupOf M) ≠ ⊤)
    (hdatum : ∀ (S₁ : Set (ClassFunction ↥M ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A' ∪
        S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        S₁ hyp.A0),
      ∀ (ψ : ClassFunction ↥M ℂ),
        ψ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
        ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥M ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        (S₁ ∪ {ψ, ψ.conj}) hyp.A0) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
            (hyp.dadeData.dade.fullDadeIsometryData)) ψ (a • χ₁),
        Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData) ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
              (hyp.dadeData.dade.fullDadeIsometryData)) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ)
    (hAcoh : Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      (S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A') hyp.A0))
    (hBncoh : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      (S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B) hyp.A0)) :
    ∃ θ : IrreducibleCharacter ↥((derivedInG M).subgroupOf M),
      (↑(B.subgroupOf ((derivedInG M).subgroupOf M)) :
          Set ↥((derivedInG M).subgroupOf M)) ⊆
        OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥((derivedInG M).subgroupOf M) ℂ) ∧
      (Nat.card (↥((derivedInG M).subgroupOf M) ⧸
          A'.subgroupOf ((derivedInG M).subgroupOf M)) : ℝ) - 1 ≤
        2 * (ClassFunction.induce ((derivedInG M).subgroupOf M)
          (θ : ClassFunction
            ↥((derivedInG M).subgroupOf M) ℂ) 1).re := by
  have := hyp.finiteG
  refine hyp.exists_source_index_le_two_psi hG
    (exists_anchor (hyp.commutator_quotient_ne_top hG hA'ne)) ?_ hdatum hAcoh hBncoh
  exact OddOrder.Peterfalvi.S08.inducedKernelFamily_nonempty_of_commutator_ne_top
    (hyp.commutator_quotient_ne_top hG hBne)

/-- **μ-column break decomposition** (named obligation, Peterfalvi (5.2.d)/(11.8.6)): the
full decomposition clause for a *reducible* break member `ψ` — a μ-grid column sum
(`muGrid_column_sum_mem_sOf_H0_and_reducible`).  The `Da`-data comes from the grid
`α`-parameters and the member `D`s from (5.8) extension-uniqueness. -/
theorem sixTwoDecompositionData_of_reducible_break [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M)
    (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (A' B : Subgroup ↥M)
    (S₁ : Set (ClassFunction ↥M ℂ))
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hsub : S₁ ⊆ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A' ∪
      S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      S₁ hyp.A0)
    (ψ : ClassFunction ↥M ℂ)
    (hψB : ψ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    (χ₁ : ClassFunction ↥M ℂ) (hχ₁S₁ : χ₁ ∈ S₁)
    (a : ℕ) (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1)
    (hbreak : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      (S₁ ∪ {ψ, ψ.conj}) hyp.A0))
    (hψred : ¬ IsIrreducibleCharacter ψ) :
    ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData)) ψ (a • χ₁),
      Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData) ∧
      ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
            (hyp.dadeData.dade.fullDadeIsometryData)) χ 0,
        D.imageFamily.Orthogonal Da.imageFamily ∧
        D.tau1 χ = hS₁coh.extension χ := by
  have := hyp.finiteG
  classical
  -- ψ is a nonzero μ-column sum; pick its conjugate column
  obtain ⟨k, hk0, hψcol⟩ := hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum
    hG hψB hψred
  subst hψcol
  obtain ⟨k', hk'0, hk'k, hcolconj⟩ := hyp.exists_conj_column hG hG.odd hk0
  -- `ζ` is not real (the induced family has no real characters)
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hzbot : params.zeta ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := by
    rw [← inducedFamily_eq_inducedKernelFamily_bot]
    exact hzS
  have hzconj : params.zeta.conj ≠ params.zeta :=
    S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hzbot
  -- family memberships and distinctness
  set ψ : ClassFunction ↥M ℂ := ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i k with hψdef
  have hψbot : ψ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
    S08.inducedKernelFamily_antitone bot_le hψB
  have hχ₁bot : χ₁ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := by
    rcases hsub hχ₁S₁ with h | h
    · exact S08.inducedKernelFamily_antitone bot_le h
    · exact S08.inducedKernelFamily_antitone bot_le h
  have hψconjbot : ψ.conj ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
    S08.inducedKernelFamily_closedUnderConjugate ⊥ hψbot
  have hψχ₁ne : ψ ≠ χ₁ := fun he => hψnotS1 (he ▸ hχ₁S₁)
  have hψcχ₁ne : ψ.conj ≠ χ₁ := fun he => hψcnotS1 (he ▸ hχ₁S₁)
  have hψnotreal : ψ.conj ≠ ψ :=
    S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hψbot
  -- degrees: `ψ̄(1) = ψ(1)` (character degrees are natural)
  obtain ⟨θψ, -, hψeq, hψ1⟩ := S08.inducedKernelFamily_apply_one hψbot
  obtain ⟨nθ, -, hnθ, -⟩ := θψ.isIrreducible.exists_natDegree_charValue_one_dvd_card
  have hψ1nat : ψ 1 = ((((derivedInG M).subgroupOf M).index * nθ : ℕ) : ℂ) := by
    rw [hψ1, hnθ]
    push_cast
    ring
  have hψconj1 : ψ.conj 1 = (1 : ℕ) • ψ 1 := by
    rw [ClassFunction.conj_apply, hψ1nat]
    simp
  -- supports of the sponsoring differences
  have hsupp1 : (ψ - (1 : ℕ) • ψ.conj).support ⊆ hyp.A0 :=
    S08.inducedKernelFamily_scaledDiff_support hyp.mderivSharp_subset_A0 hψbot hψconjbot
      (by rw [hψconj1]; simp)
  have hsupp1' : (ψ - ψ.conj).support ⊆ hyp.A0 := by
    simpa using hsupp1
  have hsupp2 : (ψ - a • χ₁).support ⊆ hyp.A0 :=
    S08.inducedKernelFamily_scaledDiff_support hyp.mderivSharp_subset_A0 hψbot hχ₁bot
      (by simpa using hψdeg)
  have hSdiff : ∀ s ∈ ({ψ - ψ.conj, ψ - a • χ₁} : Set (ClassFunction ↥M ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
    intro s hs
    rcases hs with rfl | rfl
    · exact hsupp1'
    · exact hsupp2
  -- integrality of `τ(ψ − a·χ₁)`
  have hmemZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) (ψ - a • χ₁) ∈ ZIrr G := by
    refine OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_mem_ZIrr_of_supported
      hyp.dadeData.dade hsupp2 ?_
    refine Submodule.sub_mem _ (S08.inducedKernelFamily_mem_ZIrr hψbot) ?_
    exact nsmul_mem (S08.inducedKernelFamily_mem_ZIrr hχ₁bot) a
  -- the three inner-product vanishings
  have hχ₁inner : ClassFunction.inner ψ χ₁ = 0 :=
    S08.inducedKernelFamily_pairwise_orthogonal hψbot hχ₁bot hψχ₁ne
  have hχ₁cinner : ClassFunction.inner ψ.conj χ₁ = 0 :=
    S08.inducedKernelFamily_pairwise_orthogonal hψconjbot hχ₁bot hψcχ₁ne
  have hsmulcast : (a • χ₁ : ClassFunction ↥M ℂ) = (a : ℂ) • χ₁ :=
    (Nat.cast_smul_eq_nsmul ℂ a χ₁).symm
  have hinner1 : ClassFunction.inner ψ (a • χ₁) = 0 := by
    rw [hsmulcast, ClassFunction.inner_smul_right, hχ₁inner, mul_zero]
  have hinner2 : ClassFunction.inner ψ.conj (a • χ₁) = 0 := by
    rw [hsmulcast, ClassFunction.inner_smul_right, hχ₁cinner, mul_zero]
  have hinner3 : ClassFunction.inner ψ ψ.conj = 0 :=
    S08.inducedKernelFamily_pairwise_orthogonal hψbot hψconjbot (Ne.symm hψnotreal)
  -- the break decomposition via the coherence-free column image family
  refine ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (hyp.columnImageFamilyCohFree hG hmu hzS hz1 hzconj hδpm hδj hk0 hk'0
      (Ne.symm hk'k) hcolconj)
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData))
    (fun φ ζ hφ hζ =>
      OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        hyp.dadeData.dade hSdiff hφ hζ)
    rfl hmemZ hinner1 hinner2 hinner3, rfl, ?_⟩
  -- member clause: per-`χ` decomposition against the column `Da`
  intro χ hχS₁
  have hS₁sub' : S₁ ⊆ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := by
    intro x hx
    rcases hsub hx with h | h
    · exact S08.inducedKernelFamily_antitone bot_le h
    · exact S08.inducedKernelFamily_antitone bot_le h
  have hχbot : χ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := hS₁sub' hχS₁
  have hχind : χ ∈ inducedFamily M := by
    rw [inducedFamily_eq_inducedKernelFamily_bot]
    exact hχbot
  by_cases hχirr : IsIrreducibleCharacter χ
  · -- irreducible member: the (5.8) member datum, orthogonal to the column via (A)+(B)
    obtain ⟨D, hDfam, hDtau⟩ := S08.inducedKernelFamily_memberDatum_of_irreducible
      hyp.dadeData.dade hModd hyp.mderivSharp_subset_A0 hS₁sub' hS₁conj hS₁coh
      hχS₁ hχirr
    refine ⟨D, ?_, hDtau⟩
    intro α hα β hβ
    -- norm-`2` of `τ(χ − χ̄)`
    have hχconjbot : χ.conj ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
      S08.inducedKernelFamily_closedUnderConjugate ⊥ hχbot
    have hχnr : χ.conj ≠ χ :=
      S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hχbot
    have hχsupp : (χ - χ.conj).support ⊆ hyp.A0 :=
      hyp.zeta_sub_conj_support hG hG.odd hχind hχirr
    have hχT2 : ClassFunction.inner (hyp.tau (χ - χ.conj)) (hyp.tau (χ - χ.conj)) = 2 := by
      have hset : ∀ s ∈ ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)), s.support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
        rintro s rfl
        exact hχsupp
      have hmem : χ - χ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
          ({χ - χ.conj} : Set (ClassFunction ↥M ℂ)) := Submodule.subset_span rfl
      have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
        hyp.dadeData.dade hset hmem hmem
      rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData) from rfl, hpres,
        ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
        ClassFunction.inner_sub_right]
      have h11 : ClassFunction.inner χ χ = 1 := by
        simpa using irreducibleCharacter_inner_eq_ite
          (⟨χ, hχirr⟩ : IrreducibleCharacter ↥M) ⟨χ, hχirr⟩
      have hcc : ClassFunction.inner χ.conj χ.conj = 1 := by
        simpa using irreducibleCharacter_inner_eq_ite
          (⟨χ.conj, hχirr.conj⟩ : IrreducibleCharacter ↥M) ⟨χ.conj, hχirr.conj⟩
      have hcr : ClassFunction.inner χ χ.conj = 0 :=
        S08.inducedKernelFamily_pairwise_orthogonal hχbot hχconjbot (Ne.symm hχnr)
      have hcr' : ClassFunction.inner χ.conj χ = 0 :=
        S08.inducedKernelFamily_pairwise_orthogonal hχconjbot hχbot hχnr
      rw [h11, hcc, hcr, hcr']
      ring
    -- `⟨α, ω⟩ = 0` for every σ-grid vector, via the (B) per-element lemma on `R(χ)`
    have hαω : ∀ (i' : Fin hyp.w1) (κ : Fin hyp.w2),
        ClassFunction.inner α (hyp.alignedOmegaSigmaGrid hG hG.odd i' κ) = 0 := by
      intro i' κ
      refine OddOrder.Peterfalvi.S12.OrthonormalCharacterImageFamily.elt_inner_eq_zero
        (R := D.imageFamily) hα (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i' κ) ?_ ?_ ?_
      · have := hyp.alignedOmegaSigmaGrid_inner hG hG.odd i' i' κ κ
        simpa using this
      · exact hχT2
      · exact hyp.tau_chidiff_inner_alignedOmega_eq_zero hG hG.odd hχind hχirr i' κ
    -- unfold the signed column element `β`
    have hβ' : β ∈ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta k k') := hβ
    rw [Finset.mem_image] at hβ'
    obtain ⟨⟨b, i⟩, -, rfl⟩ := hβ'
    rcases b with _ | _
    · simp only [Hypothesis.columnRImage]
      rw [OddOrder.RepresentationTheory.inner_smul_right, hαω, mul_zero]
    · simp only [Hypothesis.columnRImage]
      rw [OddOrder.RepresentationTheory.inner_smul_right, hαω, mul_zero]
  · -- reducible member: μ-column sum, column–column orthogonality
    obtain ⟨hSne, sExt, hSie, hSeos, hSmz⟩ := hS₁coh
    obtain ⟨kχ, hkχ0, hχcol⟩ := hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum
      hG hχbot hχirr
    subst hχcol
    obtain ⟨kχ', hkχ'0, hkχ'k, hχconj⟩ := hyp.exists_conj_column hG hG.odd hkχ0
    -- the member's column pair `{kχ, kχ'}` avoids the break's `{k, k'}`
    have hkχk : kχ ≠ k := by
      intro he
      apply hψnotS1
      rw [hψdef, ← he]
      exact hχS₁
    have hkχkc : kχ ≠ k' := by
      intro he
      apply hψcnotS1
      rw [hcolconj, ← he]
      exact hχS₁
    have hkχ'kb : kχ' ≠ k := by
      intro he
      apply hψnotS1
      rw [hψdef, ← he, ← hχconj]
      exact hS₁conj hχS₁
    have hkχ'kc : kχ' ≠ k' := by
      intro he
      apply hψcnotS1
      rw [hcolconj, ← he, ← hχconj]
      exact hS₁conj hχS₁
    set χc : ClassFunction ↥M ℂ := ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i kχ with hχcdef
    have hχconjS₁ : χc.conj ∈ S₁ := hS₁conj hχS₁
    have hχne : χc.conj ≠ χc :=
      S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hχbot
    obtain ⟨θχc, -, -, hχ1⟩ := S08.inducedKernelFamily_apply_one hχbot
    obtain ⟨nθχc, -, hnθχc, -⟩ := θχc.isIrreducible.exists_natDegree_charValue_one_dvd_card
    have hχ1nat : χc 1 = ((((derivedInG M).subgroupOf M).index * nθχc : ℕ) : ℂ) := by
      rw [hχ1, hnθχc]
      push_cast
      ring
    have hχconjbot : χc.conj ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
      S08.inducedKernelFamily_closedUnderConjugate ⊥ hχbot
    have hχconj1 : χc.conj 1 = (1 : ℕ) • χc 1 := by
      rw [ClassFunction.conj_apply, hχ1nat]
      simp
    have hsupp1χ : (χc - χc.conj).support ⊆ hyp.A0 := by
      have h := S08.inducedKernelFamily_scaledDiff_support hyp.mderivSharp_subset_A0
        hχbot hχconjbot (d := 1) (by rw [hχconj1]; push_cast; ring)
      simpa using h
    have hχspan : χc ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ :=
      Submodule.subset_span hχS₁
    have hχcspan : χc.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ :=
      Submodule.subset_span hχconjS₁
    have hdiffspan : χc - χc.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ :=
      Submodule.sub_mem _ hχspan hχcspan
    have h2span : ∀ φ ∈ ({χc - χc.conj, χc - 0} : Set (ClassFunction ↥M ℂ)),
        φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ := by
      rintro φ (rfl | rfl)
      · exact hdiffspan
      · rw [sub_zero]
        exact hχspan
    refine ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
      (hyp.columnImageFamilyCohFree hG hmu hzS hz1 hzconj hδpm hδj hkχ0 hkχ'0
        (Ne.symm hkχ'k) hχconj)
      sExt
      (fun φ ζ hφ hζ => hSie φ ζ
        (Submodule.span_le.mpr (fun φ' hφ' => h2span φ' hφ') hφ)
        (Submodule.span_le.mpr (fun φ' hφ' => h2span φ' hφ') hζ))
      (hSeos _ ⟨hdiffspan, hsupp1χ⟩)
      (by rw [sub_zero]; exact hSmz χc hχspan)
      (by simp)
      (by simp)
      (S08.inducedKernelFamily_pairwise_orthogonal hχbot hχconjbot (Ne.symm hχne)),
      ?_, ?_⟩
    · -- column–column orthogonality: all four column pairs are distinct
      intro α hα β hβ
      have hα' : α ∈ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta kχ kχ') := hα
      have hβ' : β ∈ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta k k') := hβ
      rw [Finset.mem_image] at hα' hβ'
      obtain ⟨⟨bα, iα⟩, -, rfl⟩ := hα'
      obtain ⟨⟨bβ, iβ⟩, -, rfl⟩ := hβ'
      have hcross : ∀ (i i' : Fin hyp.w1) (κ κ' : Fin hyp.w2), κ ≠ κ' →
          ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i κ)
            (hyp.alignedOmegaSigmaGrid hG hG.odd i' κ') = 0 := by
        intro i i' κ κ' hne
        rw [hyp.alignedOmegaSigmaGrid_inner hG hG.odd i i' κ κ',
          if_neg (fun hh => hne hh.2)]
      rcases bα with _ | _ <;> rcases bβ with _ | _
      · simp only [Hypothesis.columnRImage]
        rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          hcross _ _ _ _ hkχk, mul_zero, mul_zero]
      · simp only [Hypothesis.columnRImage]
        rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          hcross _ _ _ _ hkχkc, mul_zero, mul_zero]
      · simp only [Hypothesis.columnRImage]
        rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          hcross _ _ _ _ hkχ'kb, mul_zero, mul_zero]
      · simp only [Hypothesis.columnRImage]
        rw [ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
          hcross _ _ _ _ hkχ'kc, mul_zero, mul_zero]
    · -- `D.tau1 χc = extension χc`: definitional after destructuring `hS₁coh`
      rfl

/-- **μ-column member decomposition** (named obligation, Peterfalvi (11.8.6)/(5.8)): the
member clause for a *reducible* `χ ∈ S₁` (μ-grid column sum) against an irreducible break
`Da`. -/
theorem sixTwoMemberDatum_of_reducible_member [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M)
    (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    {B : Subgroup ↥M}
    {S₁ : Set (ClassFunction ↥M ℂ)}
    (hS₁conj : OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁)
    (hS₁sub : S₁ ⊆ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥)
    (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
        (hyp.dadeData.dade.fullDadeIsometryData))
      S₁ hyp.A0)
    {ψ : ClassFunction ↥M ℂ}
    (hψB : ψ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B)
    (hψirr : IsIrreducibleCharacter ψ)
    (hψnotS1 : ψ ∉ S₁) (hψcnotS1 : ψ.conj ∉ S₁)
    {χ₁ : ClassFunction ↥M ℂ} (hχ₁S₁ : χ₁ ∈ S₁)
    {a : ℕ} (hψdeg : ψ 1 = (a : ℂ) * χ₁ 1)
    {χ : ClassFunction ↥M ℂ} (hχS₁ : χ ∈ S₁)
    (hχred : ¬ IsIrreducibleCharacter χ) :
    ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData)) χ 0,
      D.imageFamily.Orthogonal
        (S08.inducedKernelFamily_breakDa_of_irreducible hyp.dadeData.dade
          (card_odd_of_isMinimalSimpleOdd hG hyp) hyp.mderivSharp_subset_A0 hS₁sub hψB hψirr
          hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).1.imageFamily ∧
      D.tau1 χ = hS₁coh.extension χ := by
  have := hyp.finiteG
  classical
  obtain ⟨hSne, sExt, hSie, hSeos, hSmz⟩ := hS₁coh
  -- `χ` is a nonzero μ-column sum; pick its conjugate column
  have hχbot : χ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := hS₁sub hχS₁
  obtain ⟨kχ, hkχ0, hχcol⟩ := hyp.reducible_mem_inducedKernelFamily_eq_muGrid_columnSum
    hG hχbot hχred
  rw [hχcol] at hχS₁ hχred hχbot ⊢
  set χc : ClassFunction ↥M ℂ := ∑ i : Fin hyp.w1, hyp.muGrid hG hG.odd i kχ with hχcdef
  obtain ⟨kχ', hkχ'0, hkχ'k, hχconj⟩ := hyp.exists_conj_column hG hG.odd hkχ0
  -- `ζ` nonreal, `χc` facts
  have hModd : Odd (Nat.card ↥M) := hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card M)
  have hzbot : params.zeta ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := by
    rw [← inducedFamily_eq_inducedKernelFamily_bot]
    exact hzS
  have hzconj : params.zeta.conj ≠ params.zeta :=
    S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hzbot
  have hχconjS₁ : χc.conj ∈ S₁ := hS₁conj hχS₁
  have hχne : χc.conj ≠ χc :=
    S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hχbot
  have hχind : χc ∈ inducedFamily M := by
    rw [inducedFamily_eq_inducedKernelFamily_bot]
    exact hχbot
  -- the coherent extension as `τ₁`
  set τexp := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
    (hyp.dadeData.dade.fullDadeIsometryData) with hτexp
  -- supports via the family scaled-diff (`d = 1`, reducible-safe)
  obtain ⟨θχc, -, -, hχ1⟩ := S08.inducedKernelFamily_apply_one hχbot
  obtain ⟨nθχc, -, hnθχc, -⟩ := θχc.isIrreducible.exists_natDegree_charValue_one_dvd_card
  have hχ1nat : χc 1 = ((((derivedInG M).subgroupOf M).index * nθχc : ℕ) : ℂ) := by
    rw [hχ1, hnθχc]
    push_cast
    ring
  have hχconjbot : χc.conj ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
    S08.inducedKernelFamily_closedUnderConjugate ⊥ hχbot
  have hχconj1 : χc.conj 1 = (1 : ℕ) • χc 1 := by
    rw [ClassFunction.conj_apply, hχ1nat]
    simp
  have hsupp1 : (χc - χc.conj).support ⊆ hyp.A0 := by
    have h := S08.inducedKernelFamily_scaledDiff_support hyp.mderivSharp_subset_A0
      hχbot hχconjbot (d := 1) (by rw [hχconj1]; push_cast; ring)
    simpa using h
  -- coherent-extension `τ₁` obligations
  have hχspan : χc ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ :=
    Submodule.subset_span hχS₁
  have hχcspan : χc.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ :=
    Submodule.subset_span hχconjS₁
  have hdiffspan : χc - χc.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ :=
    Submodule.sub_mem _ hχspan hχcspan
  have h2span : ∀ φ ∈ ({χc - χc.conj, χc - 0} : Set (ClassFunction ↥M ℂ)),
      φ ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M) S₁ := by
    rintro φ (rfl | rfl)
    · exact hdiffspan
    · rw [sub_zero]
      exact hχspan
  -- ψ-facts for the break-`Da` cross-orthogonality
  have hψbot : ψ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
    S08.inducedKernelFamily_subset_bot B hψB
  have hψind : ψ ∈ inducedFamily M := by
    rw [inducedFamily_eq_inducedKernelFamily_bot]
    exact hψbot
  have hψconjbot : ψ.conj ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ :=
    S08.inducedKernelFamily_closedUnderConjugate ⊥ hψbot
  have hψnr : ψ.conj ≠ ψ :=
    S08.inducedKernelFamily_hasNoRealCharacters hModd ⊥ hψbot
  have hψsupp : (ψ - ψ.conj).support ⊆ hyp.A0 :=
    hyp.zeta_sub_conj_support hG hG.odd hψind hψirr
  have hψT2 : ClassFunction.inner (hyp.tau (ψ - ψ.conj)) (hyp.tau (ψ - ψ.conj)) = 2 := by
    have hset : ∀ s ∈ ({ψ - ψ.conj} : Set (ClassFunction ↥M ℂ)), s.support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup (typePA0 M hyp.typeP) M := by
      rintro s rfl
      exact hψsupp
    have hmem : ψ - ψ.conj ∈ OddOrder.Peterfalvi.S07.zSpan (L := ↥M)
        ({ψ - ψ.conj} : Set (ClassFunction ↥M ℂ)) := Submodule.subset_span rfl
    have hpres := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
      hyp.dadeData.dade hset hmem hmem
    rw [show hyp.tau = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) from rfl, hpres,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_sub_right]
    have h11 : ClassFunction.inner ψ ψ = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ψ, hψirr⟩ : IrreducibleCharacter ↥M) ⟨ψ, hψirr⟩
    have hcc : ClassFunction.inner ψ.conj ψ.conj = 1 := by
      simpa using irreducibleCharacter_inner_eq_ite
        (⟨ψ.conj, hψirr.conj⟩ : IrreducibleCharacter ↥M) ⟨ψ.conj, hψirr.conj⟩
    have hcr : ClassFunction.inner ψ ψ.conj = 0 :=
      S08.inducedKernelFamily_pairwise_orthogonal hψbot hψconjbot (Ne.symm hψnr)
    have hcr' : ClassFunction.inner ψ.conj ψ = 0 :=
      S08.inducedKernelFamily_pairwise_orthogonal hψconjbot hψbot hψnr
    rw [h11, hcc, hcr, hcr']
    ring
  -- assemble `D` and its orthogonality to the break `Da`
  refine ⟨OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection
    (hyp.columnImageFamilyCohFree hG hmu hzS hz1 hzconj hδpm hδj hkχ0 hkχ'0
      (Ne.symm hkχ'k) hχconj)
    sExt
    (fun φ ζ hφ hζ => hSie φ ζ
      (Submodule.span_le.mpr (fun φ' hφ' => h2span φ' hφ') hφ)
      (Submodule.span_le.mpr (fun φ' hφ' => h2span φ' hφ') hζ))
    (hSeos _ ⟨hdiffspan, hsupp1⟩)
    (by rw [sub_zero]; exact hSmz χc hχspan)
    (by simp)
    (by simp)
    (S08.inducedKernelFamily_pairwise_orthogonal hχbot hχconjbot (Ne.symm hχne)),
    ?_, ?_⟩
  · -- Orthogonal to the irreducible break `Da`: per-pair via (A)+(B)
    intro α hα β hβ
    -- `α` is a signed σ-grid entry of the `χ`-column family
    have hα' : α ∈ Finset.univ.image (hyp.columnRImage hG hG.odd params.delta kχ kχ') := hα
    rw [Finset.mem_image] at hα'
    obtain ⟨⟨b, i⟩, -, rfl⟩ := hα'
    -- `⟨ω_pt, β⟩ = 0` via the (B) per-element lemma on the break family
    have hωβ : ∀ (i' : Fin hyp.w1) (k' : Fin hyp.w2),
        ClassFunction.inner (hyp.alignedOmegaSigmaGrid hG hG.odd i' k') β = 0 := by
      intro i' k'
      have hβ0 : ClassFunction.inner β (hyp.alignedOmegaSigmaGrid hG hG.odd i' k') = 0 := by
        refine OddOrder.Peterfalvi.S12.OrthonormalCharacterImageFamily.elt_inner_eq_zero
          (R := (S08.inducedKernelFamily_breakDa_of_irreducible hyp.dadeData.dade
            (card_odd_of_isMinimalSimpleOdd hG hyp) hyp.mderivSharp_subset_A0 hS₁sub hψB hψirr
            hψnotS1 hψcnotS1 hχ₁S₁ hψdeg).1.imageFamily) hβ
          (hyp.alignedOmegaSigmaGrid_mem_ZIrr hG hG.odd i' k') ?_ ?_ ?_
        · have := hyp.alignedOmegaSigmaGrid_inner hG hG.odd i' i' k' k'
          simpa using this
        · exact hψT2
        · exact hyp.tau_chidiff_inner_alignedOmega_eq_zero hG hG.odd hψind hψirr i' k'
      rw [OddOrder.RepresentationTheory.inner_conj_symm, hβ0, star_zero]
    -- unfold the two signed cases
    rcases b with _ | _
    · simp only [Hypothesis.columnRImage]
      rw [ClassFunction.inner_smul_left, hωβ, mul_zero]
    · simp only [Hypothesis.columnRImage]
      rw [neg_smul, ClassFunction.inner_neg_left, ClassFunction.inner_smul_left, hωβ,
        mul_zero, neg_zero]
  · -- `D.tau1 χ = extension χ`: definitional after destructuring `hS₁coh`
    rfl

/-- **The (5.2.d) decomposition data for the §11 family — the single remaining grid obligation
of the h56 chain** (issue 2022).  For any intermediate coherent set `S₁` between the `S(A')` and
`S(B)` layers and any break `ψ ∈ S(B)` with anchor ratio `a`, supplies the break decomposition
`Da` over the Dade map and, per member `χc ∈ S₁`, an `R(χc)`-decomposition compatible with the
coherent extension and orthogonal to `Da`'s family.

*Content*: for irreducible `ψ` and irreducible members this is fully general
(`inducedKernelFamily_breakDa_of_irreducible` /
`inducedKernelFamily_memberDatum_orthogonal_breakDa_of_irr_irr`, `S08_SixTwoGeneral`); the
genuinely open cases involve a reducible μ-column (as break or member): the column's
decomposition is the §10–§12 `muGrid`/`columnSum` structure, and the coupling
`D.tau1 χc = hS₁coh.extension χc` for a column member is the (11.8.6)/(5.8)-type
extension-uniqueness.  See issue 2022. -/
theorem sixTwoDecompositionData [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis M)
    {params : CharacterParameters hyp}
    (hmu : params.mu = hyp.muGrid hG hG.odd)
    (hδpm : params.delta = 1 ∨ params.delta = -1)
    (hδj : ∀ j : Fin hyp.w2, j ≠ 0 → hyp.muColumnSign hG hG.odd j = params.delta)
    (hzS : params.zeta ∈ inducedFamily M)
    (hz1 : params.zeta 1 = (hyp.w1 : ℂ))
    (A' B : Subgroup ↥M) :
    ∀ (S₁ : Set (ClassFunction ↥M ℂ)),
      OddOrder.Peterfalvi.S03.ClosedUnderConjugate S₁ →
      S₁ ⊆ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) A' ∪
        S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
      ∀ (hS₁coh : OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        S₁ hyp.A0),
      ∀ (ψ : ClassFunction ↥M ℂ),
        ψ ∈ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) B →
        ψ ∉ S₁ → ψ.conj ∉ S₁ →
      ∀ (χ₁ : ClassFunction ↥M ℂ), χ₁ ∈ S₁ →
      ∀ (a : ℕ), ψ 1 = (a : ℂ) * χ₁ 1 →
      ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData))
        (S₁ ∪ {ψ, ψ.conj}) hyp.A0) →
      ∃ Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
            (hyp.dadeData.dade.fullDadeIsometryData)) ψ (a • χ₁),
        Da.tau1 = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
          (hyp.dadeData.dade.fullDadeIsometryData) ∧
        ∀ χ ∈ S₁, ∃ D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥M) (G := G)
            (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp.dadeData.dade
              (hyp.dadeData.dade.fullDadeIsometryData)) χ 0,
          D.imageFamily.Orthogonal Da.imageFamily ∧
          D.tau1 χ = hS₁coh.extension χ := by
  intro S₁ hS₁conj hsub hS₁coh ψ hψB hψnotS1 hψcnotS1 χ₁ hχ₁S₁ a hψdeg hbreak
  have hS₁sub : S₁ ⊆ S08.inducedKernelFamily ((derivedInG M).subgroupOf M) ⊥ := by
    intro φ hφ
    rcases hsub hφ with h | h
    · exact S08.inducedKernelFamily_antitone bot_le h
    · exact S08.inducedKernelFamily_antitone bot_le h
  have hodd := card_odd_of_isMinimalSimpleOdd hG hyp
  by_cases hψirr : IsIrreducibleCharacter ψ
  · -- irreducible break: the S08 general discharge
    set bd := S08.inducedKernelFamily_breakDa_of_irreducible
      hyp.dadeData.dade hodd hyp.mderivSharp_subset_A0 hS₁sub hψB hψirr
      hψnotS1 hψcnotS1 hχ₁S₁ hψdeg with hbd
    refine ⟨bd.1, bd.2.1, ?_⟩
    intro χ hχS₁
    by_cases hχirr : IsIrreducibleCharacter χ
    · exact S08.inducedKernelFamily_memberDatum_orthogonal_breakDa_of_irr_irr
        hyp.dadeData.dade hodd hyp.mderivSharp_subset_A0 hS₁sub hS₁conj hS₁coh
        hψB hψirr hψnotS1 hψcnotS1 hχ₁S₁ hψdeg hχS₁ hχirr
    · exact sixTwoMemberDatum_of_reducible_member hG hyp hmu hδpm hδj hzS hz1 hS₁conj
        hS₁sub hS₁coh hψB hψirr
        hψnotS1 hψcnotS1 hχ₁S₁ hψdeg hχS₁ hχirr
  · -- reducible (μ-column) break: the named grid obligation
    exact sixTwoDecompositionData_of_reducible_break hG hyp hmu hδpm hδj hzS hz1
      A' B S₁ hS₁conj hsub hS₁coh ψ hψB hψnotS1 hψcnotS1 χ₁ hχ₁S₁ a hψdeg hbreak hψirr

end Hypothesis

end OddOrder.Peterfalvi.S12


