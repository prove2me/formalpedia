-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_GeneralAdjoinWeighted
-- name    : OddOrder_Peterfalvi_S08_GeneralAdjoinWeighted
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:19:33.264618+00:00
-- url     : https://prove2.me/theorems/b38f1f84-34a8-4e09-a210-8df7bd8d9bdd
-- title:
--   Peterfalvi (5.6): the norm-weighted coherence adjoin for an arbitrary isometry $\tau$
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §5, Theorem (5.6) under Hypothesis (5.2), in the norm-weighted, reducible-break form: members $\chi_i$ may have $\|\chi_i\|^2>1$ and projection coefficients are weighted by $1/\|\chi_i\|^2$. The file generalizes the earlier weighted engine to an arbitrary isometry $\tau$.
--
--   Results include `exists_indexed_projection_of_orthogonal_ZIrr` (orthogonal integer projection onto a norm-weighted family), `crux1_of_memberFamilyW_general`, the forward adjoin engines `xAdjoinStepW_general` and `xAdjoinStepW_k_general`, and the degree-square bound `coherentDegreeSqNormBound_of_not_coherentW_k_general`.
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_GeneralAdjoinWeighted.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_GeneralAdjoinWeighted.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_GeneralAdjoin
import Definitions.Def_OddOrder_Peterfalvi_S07_RetargetScaled

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped Classical in
/-- **Orthogonal integer projection onto a norm-weighted `ZIrr` family.**  The weighted analogue of
`exists_indexed_intProjection_of_orthonormal_ZIrr`: for `φ ∈ ℤ[Irr G]` and a family
`vc : ι → ClassFunction G ℂ` of `ZIrr`-members that are pairwise *orthogonal* with squared norms
`mc i = ⟨vc i, vc i⟩` (`horth i j = if i=j then mc i else 0`, `mc i > 0`), the inner products
`⟨φ, vc i⟩ = cZ i` are integers and `φ` decomposes as `φ = ∑ (cZ i / mc i)·vc i + Z` with the
remainder `Z` orthogonal to every `vc i`.  Unlike the orthonormal case the coefficients
`cZ i / mc i` are *rational* (the integer `cZ i` divided by the squared norm) — exactly the
`1/‖χᵢ‖²` projection coefficient of Peterfalvi (5.6).

Nothing here is Dade-specific (or even `τ`-specific): it is plain orthogonal projection in
`ℤ[Irr G]`. -/
theorem exists_indexed_projection_of_orthogonal_ZIrr {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {ι : Type*} (s : Finset ι) (vc : ι → ClassFunction G ℂ) (mc : ι → ℝ)
    (hvcZ : ∀ i ∈ s, vc i ∈ ZIrr G) (hmc_pos : ∀ i ∈ s, 0 < mc i)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (mc i : ℂ) else 0) :
    ∃ (cZ : ι → ℤ) (Z : ClassFunction G ℂ),
      (∀ i ∈ s, ClassFunction.inner φ (vc i) = (cZ i : ℂ)) ∧
      φ = (∑ i ∈ s, (((cZ i : ℝ) / mc i : ℝ) : ℂ) • vc i) + Z ∧
      ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0 := by
  classical
  have hint : ∀ i ∈ s, ∃ n : ℤ, ClassFunction.inner φ (vc i) = (n : ℂ) :=
    fun i hi => ClassFunction.inner_mem_ZIrr_int hφ (hvcZ i hi)
  choose! cZ hcZ using hint
  refine ⟨cZ, φ - ∑ i ∈ s, (((cZ i : ℝ) / mc i : ℝ) : ℂ) • vc i, hcZ, by abel, ?_⟩
  intro i hi
  rw [ClassFunction.inner_sub_left]
  have hsum : ClassFunction.inner (∑ j ∈ s, (((cZ j : ℝ) / mc j : ℝ) : ℂ) • vc j) (vc i)
      = (cZ i : ℂ) := by
    rw [inner_sum_left, Finset.sum_eq_single i]
    · rw [ClassFunction.inner_smul_left, horth i hi i hi, if_pos rfl]
      have hmci : (mc i : ℂ) ≠ 0 := by exact_mod_cast (hmc_pos i hi).ne'
      push_cast
      field_simp
    · intro j hj hji
      rw [ClassFunction.inner_smul_left, horth j hj i hi, if_neg hji, mul_zero]
    · intro hni; exact absurd hi hni
  rw [hsum, hcZ i hi, sub_self]

end OddOrder.Peterfalvi.S08

namespace OddOrder.Peterfalvi.S07

open OddOrder.RepresentationTheory

variable {L G : Type*} [Group L] [Group G]

/-- **`ℤ[univ, A] = CF(L, A)`.**  With the ambient family taken to be everything, membership in the
supported lattice `zSupportedSpan univ A` is *just* the support condition — the `ℤ`-span clause is
vacuous.  This is how an isometry defined on all `A`-supported class functions (rather than on the
`ℤ`-span of a specified family `𝒮`) instantiates the `Samb`-indexed `hisom` of the general adjoin:
take `Samb = univ`.  The Feit–Thompson Dade map is of that kind
(`dadeIntegralCharacterMap_inner_eq_on_supported_span` asks only for supports), so its
specializations of the general engines below go through `Samb = univ`. -/
theorem mem_zSupportedSpan_univ_iff {A : Set L} {φ : ClassFunction L ℂ} :
    φ ∈ zSupportedSpan (L := L) (Set.univ : Set (ClassFunction L ℂ)) A ↔ φ.support ⊆ A := by
  rw [mem_zSupportedSpan_iff]
  exact ⟨fun h => h.2, fun h => ⟨by rw [zSpan, Submodule.span_univ]; exact Submodule.mem_top, h⟩⟩

/-- **General `inner_Y_extension_member_eq`, integer-ratio form** (generalizes
`inner_Y_extension_member_eq`, `S08_CoherenceCorePart1/CoherentAdjoin.lean`, from the Dade map to an
arbitrary `τ`).

This is the `d₁ = 1` case of the scaled `inner_Y_extension_member_eq_general`: when the anchor ratio
is `1` (Peterfalvi's `χ₁(1) ∣ χⱼ(1)` for every member, which the weighted (5.6) chain has via
`deg i₁ = 1`), the degree-matched difference `χⱼ − aⱼ·χ₁` already has integer coefficients, so no
scaling by `d₁` is needed and the conclusion is division-free.

`m₁ = ‖χ₁‖²` is left symbolic — the weighted engine's anchor may be reducible. -/
theorem inner_Y_extension_member_eq_intRatio_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A)
    (χ : ClassFunction L ℂ) {chi1 cj : ClassFunction L ℂ} {a aj : ℕ}
    {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - τ (χ - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension (cj - aj • chi1)) =
      ClassFunction.inner (χ - a • chi1) (cj - aj • chi1))
    (hχcj : ClassFunction.inner χ cj = 0)
    (hχchi1 : ClassFunction.inner χ chi1 = 0)
    {m₁ : ℂ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = m₁) :
    ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * ClassFunction.inner chi1 cj -
        ((a : ℂ) * m₁ + ClassFunction.inner (τ (χ - a • chi1))
          (hS₁.extension chi1)) * (aj : ℂ) := by
  have h := inner_Y_extension_member_eq_general hS₁ χ 1 aj hYeq hXortho
    (by simpa using hfound) hχcj hχchi1 hchi1chi1
  push_cast at h
  linear_combination h

open scoped Classical in
/-- **General norm-weighted crux1** (generalizes `crux1_of_memberFamilyW`,
`S08_CoherenceWeighted.lean`; the Dade version's `hyp`/`_hτ` arguments are unused in its proof —
this drops them and the `L : Subgroup G` restriction).

**Peterfalvi (5.6.1)/(5.6.2) crux1, reducible member family:**
`⟨τ(χ − a·χ₁), ν χ₁⟩ = −a·‖χ₁‖²`.
The member family `χmem` is orthogonal with real squared norms `mc i`
(`hmemortho i j = if i=j then mc i else 0`) and the degree bound is the **weighted**
`2a < ∑ deg(i)²/mc i`.

**The anchor norm is arbitrary** — no `mc i₁ = 1`, i.e. no anchor irreducibility.  This tracks
Peterfalvi (5.6) exactly: its hypotheses are only that `S₁` is coherent, `χ₁(1) ∣ χ(1)`, and
`2χ(1)χ₁(1) < ∑ χᵢ(1)²/‖χᵢ‖²`; the proof carries `‖χ₁‖²` symbolically throughout, e.g. (5.6.1)'s
`(Y, χ₁^τ₁) = (a − λ/‖χ₁‖²)‖χ₁‖² = a‖χ₁‖² − λ`.

The proof is the orthonormal `crux1_of_memberFamily_general` with `1 ↦ mc i`: the orthogonal
projection (`S08.exists_indexed_projection_of_orthogonal_ZIrr`) gives integer `cZ i = ⟨Da.Y, ν χᵢ⟩`
and the *rational* expansion `Da.Y = ∑ (cZ i/mc i)·ν χᵢ + Z`; with `cZ i = a·mc i₁·[i=i₁] − λ·deg i`
this is the `λ`-form `∑ (a·[i=i₁] − λ·rc i)·ν χᵢ` with `λ = a·mc i₁ + μ`, `rc i = deg i/mc i`.  `λ`
is an *integer* because `mc i₁ = ⟨ν χ₁, ν χ₁⟩` is one (`ν χ₁ ∈ ℤ[Irr G]` and `ν` an isometry) —
the norm-general replacement for `mc i₁ = 1`.  The (5.6.2) engine `lambda_eq_zero_and_Z_eq_zero` is
already norm-general and forces `λ = 0`, i.e. `μ = −a·mc i₁`. -/
theorem crux1_of_memberFamilyW_general
    {τ : IntegralCharacterMap L G} {A : Set L}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A)
    (χ : ClassFunction L ℂ) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (mc i₁ : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) * (mc i₁ : ℂ) + ClassFunction.inner (τ (χ - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ (χ - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i) :
    ClassFunction.inner (τ (χ - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -((a : ℂ) * (mc i₁ : ℂ)) := by
  classical
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  -- the `ν`-images are orthogonal with the same norms `mc i`
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (mc i : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  -- **Integrality of the anchor norm** (the norm-general stand-in for `mc i₁ = 1`):
  -- `mc i₁ = ⟨ν χ₁, ν χ₁⟩` and `ν χ₁ ∈ ℤ[Irr G]`, so the norm is an integer `n₁`.
  obtain ⟨n₁, hn₁⟩ := ClassFunction.inner_mem_ZIrr_int (hνZ i₁ hi₁) (hνZ i₁ hi₁)
  have hmc₁C : ((mc i₁ : ℝ) : ℂ) = (n₁ : ℂ) := by
    have h := horth i₁ hi₁ i₁ hi₁
    rw [if_pos rfl, hn₁] at h
    exact h.symm
  -- orthogonal integer projection of `Da.Y`
  obtain ⟨cZ, Z, hcZval, hYsum, hZortho⟩ :=
    OddOrder.Peterfalvi.S08.exists_indexed_projection_of_orthogonal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) mc hνZ hmempos horth
  set lam : ℤ := n₁ * (a : ℤ) + μ with hlam_def
  -- coefficient identification `cZ i = a·mc i₁·[i=i₁] − λ·deg i` (in `ℂ`)
  have hcoeff_eq : ∀ i ∈ s, (cZ i : ℂ) =
      (a : ℂ) * (mc i₁ : ℂ) * (if i = i₁ then 1 else 0) - (lam : ℂ) * (deg i : ℂ) := by
    intro i hi
    rw [← hcZval i hi, hcoeffval i hi, hμeq, hmc₁C, hlam_def]; push_cast; ring
  -- the `λ`-form of `Da.Y`, with `rc i = deg i / mc i`
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0)
        - (lam : ℝ) * ((deg i : ℝ) / mc i) : ℝ) : ℂ) • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hmi : mc i ≠ 0 := (hmempos i hi).ne'
    congr 1
    rw [Complex.ofReal_inj]
    by_cases h : i = i₁
    · subst h
      have hci := hcoeff_eq i hi
      rw [if_pos rfl] at hci
      have hciR : (cZ i : ℝ) = (a : ℝ) * mc i - (lam : ℝ) * (deg i : ℝ) := by
        have : (cZ i : ℂ) = (((a : ℝ) * mc i - (lam : ℝ) * (deg i : ℝ) : ℝ) : ℂ) := by
          rw [hci]; push_cast; ring
        exact_mod_cast this
      rw [if_pos rfl, hciR]; field_simp
    · have hci := hcoeff_eq i hi
      rw [if_neg h] at hci
      have hciR : (cZ i : ℝ) = -((lam : ℝ) * (deg i : ℝ)) := by
        have : (cZ i : ℂ) = -((lam : ℂ) * (deg i : ℂ)) := by rw [hci]; ring
        exact_mod_cast this
      rw [if_neg h, hciR]; field_simp; ring
  -- the anchor norm computation `‖a·χ₁‖² = a²·mc i₁`
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * mc i₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast]
    rw [show (a : ℂ) * ((a : ℂ) * (mc i₁ : ℂ)) = (((a : ℝ) ^ 2 * mc i₁ : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]
  -- (5.6.2) integer forcing: `λ = a·mc i₁ + μ = 0`
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) lam Z
    (fun i => hS₁.extension (χmem i)) mc (fun i => (deg i : ℝ) / mc i)
    hY horth hZortho hψ
    (by
      have hmi : mc i₁ ≠ 0 := (hmempos i₁ hi₁).ne'
      field_simp
      exact_mod_cast ha1)
    (by positivity)
    (by
      refine hDeg.trans_le (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i hi => ?_
      have hmi : mc i ≠ 0 := (hmempos i hi).ne'
      field_simp)
  have hμval : μ = -(n₁ * (a : ℤ)) := by
    rw [hlam_def] at hlam0; linarith
  rw [hμeq, hμval]; push_cast [← hmc₁C]; ring

open scoped Classical in
/-- **General `retarget_isCoherent_of_extensionImage_k`** (generalizes
`S08.retarget_isCoherent_of_extensionImage_k`, `S08_RetargetReducible.lean`, from the Dade map to an
arbitrary isometry `τ`; equivalently, the `‖χ‖² ≠ 1` analogue of
`retarget_isCoherent_of_extensionImage_general`).

For a **possibly reducible** break character `χ` (conjugate-pair partner `chibar`, both orthogonal
to the coherent set `S₁` and to each other), the corrected extension image
`X := τ(χ − a·χ₁) + a·νχ₁` and its partner `X̄ := X − τ(χ − chibar)` satisfy the Gram-matching norms
`‖X‖² = ‖χ‖²`, `‖X̄‖² = ‖chibar‖²`, `⟨X,X̄⟩ = 0`, which feed the scaled (5.6.3) extension
`retarget_isCoherent_S` to produce `IsCoherent τ (S₁ ∪ {χ, chibar}) A`.

The **only** input over the source data is `hisom`: the lattice isometry of `τ` on `A`-supported
subsets of `ℤ[Samb]`, in the same `T`-indexed shape as
`retarget_isCoherent_of_extensionImage_general`
(Feit–Thompson: `S08.dade_hisom_of_zSupportedSpan`; abstract: `Hypothesis.adjoin_hisom`).  The two
crux inner products `hcrux1`/`hcrux2` (the (5.6) degree-inequality content) remain hypotheses. -/
noncomputable def retarget_isCoherent_of_extensionImage_k_general
    {τ : IntegralCharacterMap L G} {S₁ : Set (ClassFunction L ℂ)} {A : Set L}
    {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    (hS₁ : IsCoherent τ S₁ A) (hS₁Samb : S₁ ⊆ Samb)
    (χ chibar : ClassFunction L ℂ) {chi1 : ClassFunction L ℂ} {a : ℕ}
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (hdiffmem : χ - chibar ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • chi1 ∈ zSupportedSpan (L := L) Samb A)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner chibar chibar ≠ 0)
    (hχχbar : ClassFunction.inner χ chibar = 0)
    (hχbarχ : ClassFunction.inner chibar χ = 0)
    {m₁ : ℝ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = (m₁ : ℂ))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner chibar x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hτaχ1Z : τ (χ - a • chi1) ∈ ZIrr G)
    (hτdiffZ : τ (χ - chibar) ∈ ZIrr G)
    (hcrux1 : ClassFunction.inner (τ (χ - a • chi1)) (hS₁.extension chi1) = -((a : ℂ) * (m₁ : ℂ)))
    (hcrux2 : ClassFunction.inner (τ (χ - chibar)) (hS₁.extension chi1) = 0)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (zSupportedSpan (L := L) S₁ A ∪ {chi1}))
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, chibar}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - chibar, χ - a • chi1})) :
    IsCoherent τ (S₁ ∪ {χ, chibar}) A := by
  classical
  -- `χ₁ ⊥ χ, chibar` (both directions, from `hχ_S1`/`hχbar_S1` and conjugate symmetry).
  have hχchi1 : ClassFunction.inner χ chi1 = 0 := hχ_S1 chi1 hchi1
  have hchi1χ : ClassFunction.inner chi1 χ = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχchi1, star_zero]
  have hχbarchi1 : ClassFunction.inner chibar chi1 = 0 := hχbar_S1 chi1 hchi1
  have hchi1χbar : ClassFunction.inner chi1 chibar = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbarchi1, star_zero]
  -- The supported difference set `{χ−chibar, χ−a·χ₁}` and the isometry of `τ` on it.
  have hSdiff : ∀ s ∈ ({χ - chibar, χ - a • chi1} : Set (ClassFunction L ℂ)),
      s ∈ zSupportedSpan (L := L) Samb A := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact hdiffmem
    · exact hadiffmem
  have hmemu : χ - a • chi1 ∈
      Submodule.span ℤ ({χ - chibar, χ - a • chi1} : Set (ClassFunction L ℂ)) :=
    Submodule.subset_span (by simp)
  have hmemd : χ - chibar ∈
      Submodule.span ℤ ({χ - chibar, χ - a • chi1} : Set (ClassFunction L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdade : ∀ φ ψ, φ ∈ Submodule.span ℤ ({χ - chibar, χ - a • chi1} : Set (ClassFunction L ℂ)) →
      ψ ∈ Submodule.span ℤ ({χ - chibar, χ - a • chi1} : Set (ClassFunction L ℂ)) →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ :=
    fun φ ψ hφ hψ => hisom _ hSdiff φ ψ hφ hψ
  -- τ-image inner products (τ isometry + source orthogonality), symbolic in `⟨χ,χ⟩`.
  have huu : ClassFunction.inner (τ (χ - a • chi1)) (τ (χ - a • chi1))
      = ClassFunction.inner χ χ + (a : ℂ) ^ 2 * (m₁ : ℂ) := by
    rw [hdade _ _ hmemu hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχchi1, hchi1χ, hchi1chi1, star_natCast]
    ring
  have hud : ClassFunction.inner (τ (χ - a • chi1)) (τ (χ - chibar))
      = ClassFunction.inner χ χ := by
    rw [hdade _ _ hmemu hmemd, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, hχχbar, hchi1χ, hchi1χbar]
    ring
  have hdd : ClassFunction.inner (τ (χ - chibar)) (τ (χ - chibar))
      = ClassFunction.inner χ χ + ClassFunction.inner chibar chibar := by
    rw [hdade _ _ hmemd hmemd]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, hχχbar, hχbarχ]
    ring
  have hdu : ClassFunction.inner (τ (χ - chibar)) (τ (χ - a • chi1))
      = ClassFunction.inner χ χ := by
    rw [hdade _ _ hmemd hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right, hχchi1, hχbarχ, hχbarchi1, star_natCast]
    ring
  -- `ν χ₁` norm and the conjugates of the two crux inner products.
  have hvv : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = (m₁ : ℂ) := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hvu : ClassFunction.inner (hS₁.extension chi1) (τ (χ - a • chi1))
      = -((a : ℂ) * (m₁ : ℂ)) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux1]; simp
  have hvd : ClassFunction.inner (hS₁.extension chi1) (τ (χ - chibar)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux2, star_zero]
  set X : ClassFunction G ℂ := τ (χ - a • chi1) + a • hS₁.extension chi1 with hX
  set Xbar : ClassFunction G ℂ := X - τ (χ - chibar) with hXbar
  have hνchi1Z : hS₁.extension chi1 ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr chi1 (Submodule.subset_span hchi1)
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    refine Submodule.add_mem _ hτaχ1Z ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ a (hS₁.extension chi1)]
    exact Submodule.smul_mem _ (a : ℤ) hνchi1Z
  have hXbarZ : Xbar ∈ ZIrr G := by rw [hXbar]; exact Submodule.sub_mem _ hXZ hτdiffZ
  -- `‖X‖² = ‖χ‖²`, `‖X̄‖² = ‖chibar‖²`, `⟨X,X̄⟩ = ⟨X̄,X⟩ = 0` (the Gram matching).
  have hXX : ClassFunction.inner X X = ClassFunction.inner χ χ := by
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hcrux1, hvu, hvv, star_natCast]
    ring
  have hXbarXbar : ClassFunction.inner Xbar Xbar = ClassFunction.inner chibar chibar := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hdd, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  have hXXbar : ClassFunction.inner X Xbar = 0 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hcrux1, hvu, hvd, hvv, star_natCast]
    ring
  have hXbarX : ClassFunction.inner Xbar X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `⟨ν ξ, τ(χ−a·χ₁)⟩ = −a·⟨ξ, χ₁⟩` on the generating set `ℤ[S₁,A] ∪ {χ₁}`, then on `ℤ[S₁]`.
  have hkey : ∀ ξ ∈ Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ (χ - a • chi1)) =
        -(a : ℂ) * ClassFunction.inner ξ chi1 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner χ y = 0 :=
            IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hyχ : ClassFunction.inner y χ = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hySdiff : ∀ s ∈ ({y, χ - a • chi1} : Set (ClassFunction L ℂ)),
              s ∈ zSupportedSpan (L := L) Samb A := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact zSupportedSpan_mono_left hS₁Samb hsupp
            · exact hadiffmem
          rw [hνy, hisom _ hySdiff y (χ - a • chi1) (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp)), ← Nat.cast_smul_eq_nsmul ℂ a chi1]
          simp only [ClassFunction.inner_sub_right, OddOrder.RepresentationTheory.inner_smul_right,
            hyχ, star_natCast]
          ring
        · rw [Set.mem_singleton_iff.mp hy1, hvu, hchi1chi1]; ring
    | zero => simp
    | add y z _ _ ihy ihz =>
        rw [map_add, ClassFunction.inner_add_left, ihy, ihz, ClassFunction.inner_add_left]; ring
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          ← Int.cast_smul_eq_zsmul ℂ c y, ClassFunction.inner_smul_left]; ring
  have hX_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) X = 0 := by
    intro ξ hξ
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1), ClassFunction.inner_add_right,
      OddOrder.RepresentationTheory.inner_smul_right, hkey ξ (hSgen hξ),
      hS₁.extension_inner_eq ξ chi1 hξ (Submodule.subset_span hchi1)]
    simp only [star_natCast]; ring
  -- `⟨ν ξ, τ(χ−chibar)⟩ = 0` on `ℤ[S₁]` (same span induction; no `χ₁` term).
  have hkeyd : ∀ ξ ∈ Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ (χ - chibar)) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner χ y = 0 :=
            IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hχbary : ClassFunction.inner chibar y = 0 :=
            IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hmem.1
          have hyχ : ClassFunction.inner y χ = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hyχbar : ClassFunction.inner y chibar = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbary, star_zero]
          have hySdiff : ∀ s ∈ ({y, χ - chibar} : Set (ClassFunction L ℂ)),
              s ∈ zSupportedSpan (L := L) Samb A := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact zSupportedSpan_mono_left hS₁Samb hsupp
            · exact hdiffmem
          rw [hνy, hisom _ hySdiff y (χ - chibar) (Submodule.subset_span (by simp))
            (Submodule.subset_span (by simp))]
          simp only [ClassFunction.inner_sub_right, hyχ, hyχbar, sub_zero]
        · rw [Set.mem_singleton_iff.mp hy1, hvd]
    | zero => simp
    | add y z _ _ ihy ihz => rw [map_add, ClassFunction.inner_add_left, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih, mul_zero]
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0 := by
    intro ξ hξ
    rw [hXbar, ClassFunction.inner_sub_right, hX_ortho ξ hξ, hkeyd ξ (hSgen hξ), sub_zero]
  have himg : τ (χ - a • chi1) = X - a • hS₁.extension chi1 := by rw [hX]; abel
  exact retarget_isCoherent_S hS₁ hχχne hχbarχbarne hχχbar hχbarχ
    hXX hXbarXbar hXXbar hXbarX hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
/-- **General norm-weighted (5.6) forward adjoin engine, reducible break** (generalizes
`S08.xAdjoinStepW_k`, `S08_CoherenceWeighted.lean`, from the Feit–Thompson Dade map to an arbitrary
isometry `τ`).

This is **Peterfalvi Theorem (5.6)** in its fullest repo form: both the **break** pair
`{χ, chibar}` and the non-anchor **members** may be reducible, degrees enter through the integer
ratios `deg i` (`deg i₁ = 1`), the norms through `mc i = ‖χmem i‖²`, and the hypothesis is the
weighted bound `2a < ∑ deg(i)²/mc i`.

As in `S08.xAdjoinStepW_k`, the break decomposition `Da : CharacterPsiDecomposition τ χ (a·χ₁)` and
the per-member decompositions `Dmem i : CharacterPsiDecomposition τ (χmem i) 0` are **parameters**
(they carry the Hypothesis (5.2.d) image families `R(χ)`, `R(χmem i)`), together with the (5.2.e)
cross-orthogonality `hortho_mem` and the running-extension agreements `hDatau1`/`htau1Dmem`.

The Dade map is replaced by the single lattice-isometry hypothesis `hisom` (`Samb` = the ambient
family `𝒮` of Hypothesis (5.2)); the supported-membership hypotheses `hdiffmem`, `hadiffmem`,
`hmemdegdiffmem` replace the Dade version's support conditions.  See issue 0154. -/
noncomputable def xAdjoinStepW_k_general
    {τ : IntegralCharacterMap L G} {A : Set L} {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A) (hS₁Samb : S₁ ⊆ Samb)
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (χ : ClassFunction L ℂ)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffmem : ∀ i ∈ s,
      χmem i - deg i • χmem i₁ ∈ zSupportedSpan (L := L) S₁ A)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, CharacterPsiDecomposition (L := L) (G := G) τ (χmem i) 0)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = τ)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s), (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • χmem i₁ ∈ zSupportedSpan (L := L) Samb A)
    (htau1_memaχ : τ (χ - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (zSupportedSpan (L := L) S₁ A ∪ {χmem i₁}))
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, χ.conj}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - χ.conj, χ - a • χmem i₁})) :
    IsCoherent τ (S₁ ∪ {χ, χ.conj}) A := by
  classical
  -- `Da.X ∈ ZIrr` (integer combination of the supplied orthonormal `R(χ) = Da.imageFamily`).
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  -- (5.4) image equation, read off `Da.tau1_image` via `hDatau1 : Da.tau1 = τ`.
  have hYeq : Da.Y = Da.X - τ (χ - a • χmem i₁) := by
    have h := Da.tau1_image
    rw [hDatau1] at h
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁) (χmem i₁) = ((mc i₁ : ℝ) : ℂ) := by
    rw [hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl]
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i)) = 0 :=
    fun i hi => OddOrder.Peterfalvi.S08.inner_decomposition_X_extension_member_eq_zero hS₁ Da
      (Dmem i hi) (hortho_mem i hi) (htau1Dmem i hi)
  -- (5.6.1) cross-term `hfound` per member: `ν δ = τ δ` on the supported `δ`, then `hisom`.
  have hfound : ∀ i ∈ s, ClassFunction.inner (τ (χ - a • χmem i₁))
      (hS₁.extension (χmem i - deg i • χmem i₁)) =
      ClassFunction.inner (χ - a • χmem i₁) (χmem i - deg i • χmem i₁) := fun i hi => by
    rw [hS₁.extends_on_supported _ (hmemdegdiffmem i hi)]
    refine hisom {χ - a • χmem i₁, χmem i - deg i • χmem i₁} ?_ _ _
      (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    intro t ht; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hadiffmem
    · exact zSupportedSpan_mono_left hS₁Samb (hmemdegdiffmem i hi)
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * ((mc i₁ : ℝ) : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) * ((mc i₁ : ℝ) : ℂ) + ClassFunction.inner (τ (χ - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq_intRatio_general hS₁ χ hYeq (hXortho i hi)
      (hfound i hi) (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]; ring
  -- crux1 via the weighted λ-form collapse.
  have hcrux1 : ClassFunction.inner (τ (χ - a • χmem i₁)) (hS₁.extension (χmem i₁))
      = -((a : ℂ) * ((mc i₁ : ℝ) : ℂ)) :=
    crux1_of_memberFamilyW_general hS₁ χ s χmem deg i₁ hi₁ Da hDaY_ZIrr hmemS1
      mc hmempos hmemortho hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ.conj), ν χ₁⟩ = 0` from `R(χ) = Da.imageFamily ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner (τ (χ - χ.conj)) (hS₁.extension (χmem i₁)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) (htau1Dmem i₁ hi₁) hα), star_zero]
  -- `τ(χ − χ.conj) ∈ ZIrr` from the break image family.
  have hτdiffZ : τ (χ - χ.conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  exact retarget_isCoherent_of_extensionImage_k_general hS₁ hS₁Samb χ χ.conj hisom
    hdiffmem hadiffmem hχχne hχbarχbarne hχχbar hχbarχ hchi1chi1 hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ hcrux1 hcrux2 hSgen hgen

open scoped Classical in
/-- **General norm-weighted (5.6) forward adjoin engine, irreducible break** (generalizes
`S08.xAdjoinStepW`, `S08_CoherenceWeighted.lean`, from the Feit–Thompson Dade map to an arbitrary
isometry `τ`).

The `‖χ‖² = 1` case of `xAdjoinStepW_k_general`: the adjoined pair `{χ, χ̄}` is orthonormal (as in
case (A) of (6.8.3) and in every application where the break is irreducible), while the non-anchor
**members** may still be reducible.  The break's (5.2.d) image family `Rχ` is a parameter — the
Dade version builds it internally from `dadeOrthonormalCharacterImageFamilyOfDiff`, which needs
`χ ∈ Irr L`; here it is supplied, so the statement is `τ`-general.  The break decomposition is then
`decompositionDaFromDiff_general` (auxiliary isometry `τ` itself, so `Da.tau1 = τ` by `rfl`). -/
noncomputable def xAdjoinStepW_general
    {τ : IntegralCharacterMap L G} {A : Set L} {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A) (hS₁Samb : S₁ ⊆ Samb)
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (χ : ClassFunction L ℂ)
    (Rχ : OrthonormalCharacterImageFamily (L := L) (G := G) τ χ)
    (hχχ : ClassFunction.inner χ χ = 1)
    (hχbarχbar : ClassFunction.inner χ.conj χ.conj = 1)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffmem : ∀ i ∈ s, χmem i - deg i • χmem i₁ ∈ zSupportedSpan (L := L) S₁ A)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, CharacterPsiDecomposition (L := L) (G := G) τ (χmem i) 0)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Rχ)
    (htau1Dmem : ∀ i (hi : i ∈ s), (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • χmem i₁ ∈ zSupportedSpan (L := L) Samb A)
    (htau1_memaχ : τ (χ - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (zSupportedSpan (L := L) S₁ A ∪ {χmem i₁}))
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, χ.conj}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - χ.conj, χ - a • χmem i₁})) :
    IsCoherent τ (S₁ ∪ {χ, χ.conj}) A := by
  classical
  have hχaχ1 : ClassFunction.inner χ (a • χmem i₁ : ClassFunction L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner χ.conj (a • χmem i₁ : ClassFunction L ℂ) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  exact xAdjoinStepW_k_general hS₁ hS₁Samb hisom χ
    (by rw [hχχ]; norm_num) (by rw [hχbarχbar]; norm_num) hχχbar hχbarχ hχ_S1 hχbar_S1
    s χmem deg i₁ hi₁ hmemdegdiffmem hmemS1 mc hmempos hmemortho Dmem
    (decompositionDaFromDiff_general (τ := τ) (Samb := Samb) Rχ hisom hdiffmem hadiffmem
      htau1_memaχ hχaχ1 hχbaraχ1 hχχbar)
    rfl hortho_mem htau1Dmem hdiffmem hadiffmem htau1_memaχ ha1 hDeg hSgen hgen

open scoped Classical in
/-- **General norm-weighted (5.6) degree-square bound** (contrapositive of `xAdjoinStepW_k_general`;
generalizes `S08.coherentDegreeSqNormBound_of_not_coherentW_k` from the Dade map to an arbitrary
isometry `τ`).

**Peterfalvi (5.6)** in the shape its consumers use: if `S₁` is coherent but `S₁ ∪ {χ, χ.conj}` is
**not**, then the norm-weighted degree-square sum is bounded, `∑ deg(i)²/‖χmem i‖² ≤ 2a`. -/
theorem coherentDegreeSqNormBound_of_not_coherentW_k_general
    {τ : IntegralCharacterMap L G} {A : Set L} {Samb : Set (ClassFunction L ℂ)}
    [Fintype L] [Fintype G] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card G : ℂ)]
    {S₁ : Set (ClassFunction L ℂ)}
    (hS₁ : IsCoherent τ S₁ A) (hS₁Samb : S₁ ⊆ Samb)
    (hisom : ∀ (T : Set (ClassFunction L ℂ)), (∀ s ∈ T, s ∈ zSupportedSpan (L := L) Samb A) →
      ∀ φ ζ : ClassFunction L ℂ, φ ∈ Submodule.span ℤ T → ζ ∈ Submodule.span ℤ T →
        ClassFunction.inner (τ φ) (τ ζ) = ClassFunction.inner φ ζ)
    (χ : ClassFunction L ℂ)
    (hχχne : ClassFunction.inner χ χ ≠ 0)
    (hχbarχbarne : ClassFunction.inner χ.conj χ.conj ≠ 0)
    (hχχbar : ClassFunction.inner χ χ.conj = 0)
    (hχbarχ : ClassFunction.inner χ.conj χ = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner χ x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner χ.conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemdegdiffmem : ∀ i ∈ s,
      χmem i - deg i • χmem i₁ ∈ zSupportedSpan (L := L) S₁ A)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (mc : ι → ℝ) (hmempos : ∀ i ∈ s, 0 < mc i)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (mc i : ℂ) else 0)
    {a : ℕ}
    (Dmem : ∀ i ∈ s, CharacterPsiDecomposition (L := L) (G := G) τ (χmem i) 0)
    (Da : CharacterPsiDecomposition (L := L) (G := G) τ χ (a • χmem i₁))
    (hDatau1 : Da.tau1 = τ)
    (hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily)
    (htau1Dmem : ∀ i (hi : i ∈ s), (Dmem i hi).tau1 (χmem i) = hS₁.extension (χmem i))
    (hdiffmem : χ - χ.conj ∈ zSupportedSpan (L := L) Samb A)
    (hadiffmem : χ - a • χmem i₁ ∈ zSupportedSpan (L := L) Samb A)
    (htau1_memaχ : τ (χ - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (zSupportedSpan (L := L) S₁ A ∪ {χmem i₁}))
    (hgen : zSupportedSpan (L := L) (S₁ ∪ {χ, χ.conj}) A ⊆
      Submodule.span ℤ (zSupportedSpan (L := L) S₁ A ∪ {χ - χ.conj, χ - a • χmem i₁}))
    (hnc : ¬ Nonempty (IsCoherent τ (S₁ ∪ {χ, χ.conj}) A)) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 / mc i ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStepW_k_general hS₁ hS₁Samb hisom χ hχχne hχbarχbarne hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemdegdiffmem hmemS1 mc hmempos hmemortho
    Dmem Da hDatau1 hortho_mem htau1Dmem hdiffmem hadiffmem htau1_memaχ ha1 hlt hSgen hgen⟩

end OddOrder.Peterfalvi.S07


