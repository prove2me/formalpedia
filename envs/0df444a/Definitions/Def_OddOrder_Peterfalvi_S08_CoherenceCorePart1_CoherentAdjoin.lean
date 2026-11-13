-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1_CoherentAdjoin
-- name    : OddOrder_Peterfalvi_S08_CoherenceCorePart1_CoherentAdjoin
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:12:57.899032+00:00
-- url     : https://prove2.me/theorems/5be60bcd-3897-4984-9306-aec49739739c
-- title:
--   Peterfalvi §8: coherent-adjoin machinery
-- statement:
--   Projection, retargeting and coherent-adjoin machinery for the Peterfalvi §8 coherence proof.
--
--   Declarations: `exists_indexed_intProjection_of_orthonormal_ZIrr` (indexed integral orthogonal projection onto a $\mathbb{Z}[\mathrm{Irr}]$-orthonormal family), `crux1_of_memberFamily` ((5.6.1)/(5.6.2) crux 1: $\langle\tau(\chi-a\chi_1),\nu\chi_1\rangle=-a$), `retarget_isCoherent_of_extensionImage` (coherence from the corrected extension image), `xAdjoinStep` (per-step $X$-family coherence adjoin from a member family), `coherentDegreeSumBound_of_not_coherent` (Peterfalvi (5.6), quantitative coherence in contrapositive form) and `sum_div_normSq_induce_kernelFilter_eq` (Peterfalvi (6.2) step (ii): the $S(A)$ degree sum).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CoherenceCorePart1/CoherentAdjoin.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CoherenceCorePart1/CoherentAdjoin.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_YsetInner

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

/-- **(5.6.1) member coefficient `⟨Da.Y, ν χⱼ⟩` — the heart of the λ-form.**

The (5.6.1) projection coefficient (Peterfalvi p. 27): for a member `χⱼ` with degree-matched
difference `χⱼ − aⱼ·χ₁` (the value enters via `hfound`, `inner_dade_extension_of_supported` applied
to the supported `δ = χⱼ − aⱼ·χ₁`),

`⟨Y, ν χⱼ⟩ = a·⟨χ₁, χⱼ⟩ − (a·‖χ₁‖² + μ)·aⱼ`,   where `Y = X − τ(χ − a·χ₁)`,
`μ = ⟨τ(χ − a·χ₁), ν χ₁⟩`.

The computation: `⟨Y, νχⱼ⟩ = −⟨τ(χ−a·χ₁), νχⱼ⟩` (since `⟨X, νχⱼ⟩ = 0`, the member R-orthogonality);
split `νχⱼ = ν(χⱼ − aⱼ·χ₁) + aⱼ·νχ₁` (ν is `ℤ`-linear); the first part is `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩`
(`hfound`), which expands via `χ ⊥ χⱼ, χ₁` to `−a·⟨χ₁, χⱼ⟩ + a·aⱼ·‖χ₁‖²`; the second is `aⱼ·μ`.
With `λ := a·‖χ₁‖² + μ` this is `a·⟨χ₁,χⱼ⟩ − λ·aⱼ`, the `lambda_eq_zero_and_Z_eq_zero` coefficient.

**The anchor norm `‖χ₁‖² = m₁` is carried symbolically**, exactly as Peterfalvi (5.6.1) does
(`(Y, χ₁^τ₁) = (a − λ/‖χ₁‖²)‖χ₁‖² = a‖χ₁‖² − λ`): Theorem (5.6) never assumes the anchor is
irreducible, and the (6.2) anchor `Ind_K^L θ` (θ linear) is reducible unless `θ` has inertia `K`.
The orthonormal consumers instantiate `m₁ = 1`. -/
theorem inner_Y_extension_member_eq
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : ClassFunction ↥L ℂ) {chi1 cj : ClassFunction ↥L ℂ} {a aj : ℕ} {Xχ Y : ClassFunction G ℂ}
    (hYeq : Y = Xχ - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData) ((χ : ClassFunction ↥L ℂ) - a • chi1))
    (hXortho : ClassFunction.inner Xχ (hS₁.extension cj) = 0)
    (hfound : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension (cj - aj • chi1)) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1))
    (hχcj : ClassFunction.inner (χ : ClassFunction ↥L ℂ) cj = 0)
    (hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0)
    {m₁ : ℂ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = m₁) :
    ClassFunction.inner Y (hS₁.extension cj) =
      (a : ℂ) * ClassFunction.inner chi1 cj -
        ((a : ℂ) * m₁ + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
            ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1)) * (aj : ℂ) := by
  -- `ν cj = ν(cj − aⱼ·χ₁) + aⱼ·ν χ₁` (ν is ℤ-linear).
  have hνcj : hS₁.extension cj
      = hS₁.extension (cj - aj • chi1) + aj • hS₁.extension chi1 := by
    rw [map_sub, map_nsmul]; abel
  -- The source-side expansion `⟨χ − a·χ₁, χⱼ − aⱼ·χ₁⟩ = −a·⟨χ₁, χⱼ⟩ + a·aⱼ·‖χ₁‖²`.
  have hsrc : ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • chi1) (cj - aj • chi1)
      = -(a : ℂ) * ClassFunction.inner chi1 cj + (a : ℂ) * (aj : ℂ) * m₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a chi1, ← Nat.cast_smul_eq_nsmul ℂ aj chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχcj, hχchi1, hchi1chi1, star_natCast]
    ring
  -- The χ₁-side `⟨τ(χ − a·χ₁), aⱼ·ν χ₁⟩ = aⱼ·μ`.
  have hsmul : ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (aj • hS₁.extension chi1) =
      (aj : ℂ) * ClassFunction.inner
        (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
          ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) := by
    rw [← Nat.cast_smul_eq_nsmul ℂ aj (hS₁.extension chi1),
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hYeq, ClassFunction.inner_sub_left, hXortho, zero_sub, hνcj,
    ClassFunction.inner_add_right, hfound, hsrc, hsmul]
  ring

open scoped Classical in
/-- **Indexed integral orthogonal projection onto a ZIrr-orthonormal family.**

The `ι`-indexed form of `exists_intProjection_of_orthonormal_ZIrr`, the shape the (5.6.2)
integer-forcing `lambda_eq_zero_and_Z_eq_zero` consumes: for `φ ∈ ZIrr G` and an **injective**
orthonormal family `vc : ι → CF G` over `s : Finset ι` (each `vc i ∈ ZIrr G`), there are integer
coefficients `c i = ⟨φ, vc i⟩` and an orthogonal residual `Z` with

`φ = (∑_{i ∈ s} c i • vc i) + Z`    and    `⟨Z, vc i⟩ = 0`.

Reindexes the image-indexed primitive (`R = s.image vc`, `Finset.sum_image` with `hvcinj`). -/
theorem exists_indexed_intProjection_of_orthonormal_ZIrr
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {φ : ClassFunction G ℂ} (hφ : φ ∈ ZIrr G)
    {ι : Type*} (s : Finset ι) (vc : ι → ClassFunction G ℂ)
    (hvcZ : ∀ i ∈ s, vc i ∈ ZIrr G)
    (hvcinj : ∀ i ∈ s, ∀ j ∈ s, vc i = vc j → i = j)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (vc i) (vc j) = if i = j then (1 : ℂ) else 0) :
    ∃ (c : ι → ℤ) (Z : ClassFunction G ℂ),
      (∀ i ∈ s, ClassFunction.inner φ (vc i) = (c i : ℂ)) ∧
      φ = (∑ i ∈ s, (c i : ℂ) • vc i) + Z ∧
      ∀ i ∈ s, ClassFunction.inner Z (vc i) = 0 := by
  classical
  have hZR : ∀ α ∈ s.image vc, α ∈ ZIrr G := by
    intro α hα; rw [Finset.mem_image] at hα; obtain ⟨i, hi, rfl⟩ := hα; exact hvcZ i hi
  have horthR : ∀ α ∈ s.image vc, ∀ β ∈ s.image vc,
      ClassFunction.inner α β = if α = β then (1 : ℂ) else 0 := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨i, hi, rfl⟩ := hα; obtain ⟨j, hj, rfl⟩ := hβ
    rw [horth i hi j hj]
    by_cases hij : i = j
    · rw [if_pos hij, if_pos (by rw [hij])]
    · rw [if_neg hij, if_neg (fun h => hij (hvcinj i hi j hj h))]
  obtain ⟨c, Y, hcoeff, hsum, hY⟩ :=
    ClassFunction.exists_intProjection_of_orthonormal_ZIrr hφ hZR horthR
  refine ⟨fun i => c (vc i), Y, fun i hi => hcoeff (vc i) (Finset.mem_image_of_mem vc hi), ?_,
    fun i hi => hY (vc i) (Finset.mem_image_of_mem vc hi)⟩
  rw [hsum, Finset.sum_image hvcinj]

open scoped Classical in
/-- **(5.6.1)/(5.6.2) crux1 from the member family: `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`.**

The capstone of the crux1 discharge — the genuine (5.6.1)/(5.6.2) `Y`-collapse for the induced
X-family, producing crux1 directly.  Given the finite orthonormal member family `{χᵢ = χmem i}` (all
in `S₁`, `‖χᵢ‖² = 1` — the case-A `X ⊆ Irr L`), the per-member (5.6.1) coefficient values
`hcoeffval` (from `inner_Y_extension_member_eq`), `a₁ = 1`, and the (6.6) degree inequality
`2a < ∑ aᵢ²`:

* the indexed projection (`exists_indexed_intProjection_of_orthonormal_ZIrr`) writes
  `Da.Y = ∑ᵢ (cᵢ:ℂ)·νχᵢ + Z` with integer `cᵢ = ⟨Da.Y, νχᵢ⟩`;
* `hcoeffval` identifies `cᵢ = a·[i=i₁] − λ·aᵢ` with the integer `λ = a + μ`, `μ = ⟨τ(χ−a·χ₁), νχ₁⟩`
  (an integer since both are virtual characters);
* the (5.6.2) integer-forcing `lambda_eq_zero_and_Z_eq_zero` then forces `λ = 0` (`Z = 0`), i.e.
  `μ = −a` — which **is** crux1.

`μ ∈ ℤ` is the load-bearing fact making `λ = a + μ` an integer; the degree inequality (6.6) is what
forces it to vanish. -/
theorem crux1_of_memberFamily
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (_hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {a : ℕ}
    {ι : Type*} (s : Finset ι) (χmem : ι → ClassFunction ↥L ℂ) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (Da : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G) τ
      (χ : ClassFunction ↥L ℂ) (a • χmem i₁))
    (hDaY_ZIrr : Da.Y ∈ ZIrr G)
    (hmemS1 : ∀ i ∈ s, χmem i ∈ S₁)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i) (χmem j) = if i = j then (1 : ℂ) else 0)
    (hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y (hS₁.extension (χmem i)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
          (hS₁.extension (χmem i₁))) * (deg i : ℂ))
    (hμZ : τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2) :
    ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • χmem i₁))
      (hS₁.extension (χmem i₁)) = -(a : ℂ) := by
  classical
  -- `hνZ` is derived (route A): `χmem i ∈ S₁ ⊆ ℤ[S₁]`, so `ν (χmem i) ∈ ℤ[Irr G]` by the
  -- `IsCoherent.extension_mem_ZIrr` field — it need not be injected as a hypothesis.
  have hνZ : ∀ i ∈ s, hS₁.extension (χmem i) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr (χmem i) (Submodule.subset_span (hmemS1 i hi))
  obtain ⟨μ, hμeq⟩ := ClassFunction.inner_mem_ZIrr_int hμZ (hνZ i₁ hi₁)
  -- Orthonormality of the family `vc i = ν χᵢ` (ν isometry on `ℤ[S₁]` + member orthonormality).
  have horth : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (hS₁.extension (χmem i)) (hS₁.extension (χmem j)) =
        if i = j then (1 : ℂ) else 0 := by
    intro i hi j hj
    rw [hS₁.extension_inner_eq (χmem i) (χmem j) (Submodule.subset_span (hmemS1 i hi))
      (Submodule.subset_span (hmemS1 j hj)), hmemortho i hi j hj]
  have hvcinj : ∀ i ∈ s, ∀ j ∈ s,
      hS₁.extension (χmem i) = hS₁.extension (χmem j) → i = j := by
    intro i hi j hj hij
    by_contra hne
    have h0 := horth i hi j hj
    rw [if_neg hne, hij, horth j hj j hj, if_pos rfl] at h0
    exact one_ne_zero h0
  obtain ⟨c, Z, hc_coeff, hYsum, hZortho⟩ :=
    exists_indexed_intProjection_of_orthonormal_ZIrr hDaY_ZIrr s
      (fun i => hS₁.extension (χmem i)) hνZ hvcinj horth
  -- Coefficient identification `(c i : ℂ) = a·[i=i₁] − (a+μ)·aᵢ`.
  have hcoeff_eq : ∀ i ∈ s, (c i : ℂ) =
      (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ) := by
    intro i hi
    rw [← hc_coeff i hi, hcoeffval i hi, hμeq]
    by_cases h : i = i₁
    · simp only [if_pos h]; push_cast; ring
    · simp only [if_neg h]; push_cast; ring
  -- The (5.6.1) λ-form and the (5.6.2) integer-forcing.
  have hY : Da.Y =
      (∑ i ∈ s, (((a : ℝ) * (if i = i₁ then 1 else 0) - ((a : ℤ) + μ : ℤ) * (deg i : ℝ) : ℝ) : ℂ)
        • hS₁.extension (χmem i)) + Z := by
    rw [hYsum]; congr 1
    exact Finset.sum_congr rfl fun i hi => by rw [hcoeff_eq i hi]
  have hψ : (ClassFunction.inner (a • χmem i₁ : ClassFunction ↥L ℂ) (a • χmem i₁)).re
      = (a : ℝ) ^ 2 * 1 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁), ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, hmemortho i₁ hi₁ i₁ hi₁, if_pos rfl,
      star_natCast, mul_one,
      show (a : ℂ) * (a : ℂ) = (((a : ℝ) ^ 2 * 1 : ℝ) : ℂ) by push_cast; ring, Complex.ofReal_re]
  obtain ⟨hlam0, -⟩ := Da.lambda_eq_zero_and_Z_eq_zero s i₁ hi₁ (a : ℝ) ((a : ℤ) + μ) Z
    (fun i => hS₁.extension (χmem i)) (fun _ => 1) (fun i => (deg i : ℝ))
    hY horth hZortho hψ (by simp [ha1]) (by positivity)
    (by simp only [mul_one]; exact hDeg)
  -- `λ = a + μ = 0 ⟹ μ = −a`, which is crux1.
  have hμval : μ = -(a : ℤ) := by omega
  rw [hμeq, hμval]; push_cast; ring

/-- **(T8.11 surgery, option A) coherence from the corrected extension image.**

The (5.6) adjoining step for the *induced (unsupported)* X-family.  Instead of mapping the new pair
`{χ, χ̄}` to a supported `ψ = 0` decomposition image (which needs `τχ ∈ ZIrr`, false for the
unsupported `χ = Ind θ`), `χ` is mapped to the **corrected extension image**
`X := τ(χ − a·χ₁) + a·νχ₁` (both terms integral).  This makes the (5.6.2) image equation `himg`
definitional, **bypassing** the `htau1_chi1` requirement `τχ₁ = νχ₁` that fails for unsupported
`χ₁`.

Every remaining obligation of `retarget_isCoherent` is discharged from the source/Dade/ν isometries
plus the two crux inner products `hcrux1 : ⟨τ(χ−a·χ₁), νχ₁⟩ = −a·‖χ₁‖²` and
`hcrux2 : ⟨τ(χ−χ̄), νχ₁⟩ = 0` (the genuine (5.6) Feit–Sibley content,
to be discharged separately via
the degree inequality).  The lattice orthogonality `hX_ortho`/`hXbar_ortho` is a span induction over
`ℤ[S₁] ⊆ span(ℤ[S₁,A] ∪ {χ₁})` (`hSgen`): clean on a supported `ξ` (`νξ = τξ` + Dade isometry) and
on `χ₁` via `hcrux1`/`hcrux2`.

**The anchor norm `m₁ = ‖χ₁‖²` is arbitrary** (Peterfalvi (5.6) never assumes the anchor is
irreducible; see `inner_Y_extension_member_eq`).  It shows up only in `huu = 1 + a²·m₁`, `hvv = m₁`
and `hvu = −a·m₁`; the corrected image `X = τ(χ−a·χ₁) + a·νχ₁` still has `‖X‖² = 1`, `‖X̄‖² = 1`,
`⟨X, X̄⟩ = 0`, because the `a²·m₁` contributions cancel. -/
noncomputable def retarget_isCoherent_of_extensionImage
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap (↥L) G)
    (hτ : τ = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      τ S₁
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L) {chi1 : ClassFunction ↥L ℂ} {a : ℕ}
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hdiffasupp : ((χ : ClassFunction ↥L ℂ) - a • chi1).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    {m₁ : ℝ} (hchi1chi1 : ClassFunction.inner chi1 chi1 = (m₁ : ℂ))
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    (hchi1 : chi1 ∈ S₁)
    (hτaχ1Z : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) ∈ ZIrr G)
    (hτdiffZ : τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G)
    (hcrux1 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - a • chi1)) (hS₁.extension chi1) = -((a : ℂ) * (m₁ : ℂ)))
    (hcrux2 : ClassFunction.inner
      (τ
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) (hS₁.extension chi1) = 0)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • chi1})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      τ
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- `χ₁ ⊥ χ, χ̄` (both directions, from `hχ_S1`/`hχbar_S1` and conjugate symmetry).
  have hχchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ) chi1 = 0 := hχ_S1 chi1 hchi1
  have hchi1χ : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχchi1, star_zero]
  have hχbarchi1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj chi1 = 0 := hχbar_S1 chi1 hchi1
  have hchi1χbar : ClassFunction.inner chi1 (χ : ClassFunction ↥L ℂ).conj = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbarchi1, star_zero]
  -- The supported difference lattice `{χ−χ̄, χ−a·χ₁}` and the Dade isometry on it.
  have hSdiff : ∀ s ∈ ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
      (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
          -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
        ClassFunction.support_neg]
      exact hdiffsupp
    · exact hdiffasupp
  have hmemu : (χ : ClassFunction ↥L ℂ) - a • chi1 ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hmemd : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈ Submodule.span ℤ
      ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
        (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) :=
    Submodule.subset_span (by simp)
  have hdade : ∀ φ ψ, φ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ψ ∈ Submodule.span ℤ
        ({(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - a • chi1} : Set (ClassFunction ↥L ℂ)) →
      ClassFunction.inner (τ φ) (τ ψ) = ClassFunction.inner φ ψ := fun φ ψ hφ hψ => by
    rw [hτ]
    exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp
      hSdiff hφ hψ
  -- Dade-image inner products (Dade isometry + source orthonormality).
  have huu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 + (a : ℂ) ^ 2 * (m₁ : ℂ) := by
    rw [hdade _ _ hmemu hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hchi1χ, hchi1chi1, star_natCast]
    ring
  have hud : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - a • chi1))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 1 := by
    rw [hdade _ _ hmemu hmemd, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_smul_left,
      hχχ, hχχbar, hchi1χ, hchi1χbar]
    ring
  have hdd : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 2 := by
    rw [hdade _ _ hmemd hmemd]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      hχχ, hχχbar, hχbarχ, hχbarχbar]
    ring
  have hdu : ClassFunction.inner (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = 1 := by
    rw [hdade _ _ hmemd hmemu, ← Nat.cast_smul_eq_nsmul ℂ a chi1]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      OddOrder.RepresentationTheory.inner_smul_right,
      hχχ, hχchi1, hχbarχ, hχbarchi1, star_natCast]
    ring
  -- `hS₁.extension χ₁` norm and the conjugates of the two crux inner products.
  have hvv : ClassFunction.inner (hS₁.extension chi1) (hS₁.extension chi1) = (m₁ : ℂ) := by
    rw [hS₁.extension_inner_eq chi1 chi1 (Submodule.subset_span hchi1)
      (Submodule.subset_span hchi1), hchi1chi1]
  have hvu : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) = -((a : ℂ) * (m₁ : ℂ)) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux1]; simp
  have hvd : ClassFunction.inner (hS₁.extension chi1)
      (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcrux2, star_zero]
  set X : ClassFunction G ℂ :=
    τ ((χ : ClassFunction ↥L ℂ) - a • chi1) + a • hS₁.extension chi1 with hX
  set Xbar : ClassFunction G ℂ := X - τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
    with hXbar
  -- `X, X̄ ∈ ℤ[Irr G]`: the supported Dade images `(χ−a·χ₁)^τ`, `(χ−χ̄)^τ` are virtual
  -- (hypotheses),
  -- and `ν χ₁ ∈ ZIrr` is now recorded by the coherence's `extension_mem_ZIrr` field (`χ₁ ∈ S₁`).
  have hνchi1Z : hS₁.extension chi1 ∈ ZIrr G :=
    hS₁.extension_mem_ZIrr chi1 (Submodule.subset_span hchi1)
  have hXZ : X ∈ ZIrr G := by
    rw [hX]
    refine Submodule.add_mem _ hτaχ1Z ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ a (hS₁.extension chi1)]
    exact Submodule.smul_mem _ (a : ℤ) hνchi1Z
  have hXbarZ : Xbar ∈ ZIrr G := by rw [hXbar]; exact Submodule.sub_mem _ hXZ hτdiffZ
  -- `‖X‖² = 1`.
  have hXX : ClassFunction.inner X X = 1 := by
    rw [hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hcrux1, hvu, hvv, star_natCast]
    ring
  -- `‖X̄‖² = 1`.
  have hXbarXbar : ClassFunction.inner Xbar Xbar = 1 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hdu, hdd, hcrux1, hcrux2, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X, X̄⟩ = 0`.
  have hXXbar : ClassFunction.inner X Xbar = 0 := by
    rw [hXbar, hX, ← Nat.cast_smul_eq_nsmul ℂ a (hS₁.extension chi1)]
    simp only [ClassFunction.inner_sub_right,
      ClassFunction.inner_add_left, ClassFunction.inner_add_right,
      ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right,
      huu, hud, hcrux1, hvu, hvd, hvv, star_natCast]
    ring
  -- `⟨X̄, X⟩ = 0`.
  have hXbarX : ClassFunction.inner Xbar X = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hXXbar, star_zero]
  -- `⟨ντ, τ(χ−a·χ₁)⟩ = −a·⟨ξ, χ₁⟩` on the generating set `ℤ[S₁,A] ∪ {χ₁}`, then on `ℤ[S₁]`.
  have hkey : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ) (τ ((χ : ClassFunction ↥L ℂ) - a • chi1)) =
        -(a : ℂ) * ClassFunction.inner ξ chi1 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - a • chi1} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · exact hdiffasupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp)),
            ← Nat.cast_smul_eq_nsmul ℂ a chi1]
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
  -- `⟨hS₁.extension ξ, τ(χ−χ̄)⟩ = 0` on `ℤ[S₁]` (similar span induction; clean — no `χ₁` term).
  have hkeyd : ∀ ξ ∈ Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {chi1}),
      ClassFunction.inner (hS₁.extension ξ)
        (τ ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)) = 0 := by
    intro ξ hξ
    induction hξ using Submodule.span_induction with
    | mem y hy =>
        rcases hy with hsupp | hy1
        · have hmem := OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mp hsupp
          have hνy : hS₁.extension y = τ y := hS₁.extends_on_supported y hsupp
          have hχy : ClassFunction.inner (χ : ClassFunction ↥L ℂ) y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχ_S1 hmem.1
          have hχbary : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj y = 0 :=
            OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hχbar_S1 hmem.1
          have hyχ : ClassFunction.inner y (χ : ClassFunction ↥L ℂ) = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχy, star_zero]
          have hyχbar : ClassFunction.inner y (χ : ClassFunction ↥L ℂ).conj = 0 := by
            rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbary, star_zero]
          have hySdiff : ∀ s ∈ ({y, (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj} :
              Set (ClassFunction ↥L ℂ)),
              s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L := by
            intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl
            · exact hmem.2
            · rw [show (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj =
                  -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) from by abel,
                ClassFunction.support_neg]
              exact hdiffsupp
          rw [hνy, hτ, OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
            hyp hySdiff (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))]
          simp only [ClassFunction.inner_sub_right, hyχ, hyχbar, sub_zero]
        · rw [Set.mem_singleton_iff.mp hy1, hvd]
    | zero => simp
    | add y z _ _ ihy ihz => rw [map_add, ClassFunction.inner_add_left, ihy, ihz, add_zero]
    | smul c y _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ c (hS₁.extension y),
          ClassFunction.inner_smul_left, ih,
          mul_zero]
  have hXbar_ortho : ∀ ξ ∈ Submodule.span ℤ S₁, ClassFunction.inner (hS₁.extension ξ) Xbar = 0 := by
    intro ξ hξ
    rw [hXbar, ClassFunction.inner_sub_right, hX_ortho ξ hξ, hkeyd ξ (hSgen hξ), sub_zero]
  have himg : τ ((χ : ClassFunction ↥L ℂ) - a • chi1) = X - a • hS₁.extension chi1 := by
    rw [hX]; abel
  exact OddOrder.Peterfalvi.S07.retarget_isCoherent hS₁ hχχ hχbarχbar hχχbar hχbarχ
    hXX hXbarXbar hXXbar hXbarX hXZ hXbarZ hX_ortho hXbar_ortho rfl hχ_S1 hχbar_S1 hchi1 himg hgen

open scoped Classical in
/-- **(T-A1) Per-step X-family coherence adjoin from a member family.** (`noncomputable def`: the
conclusion `IsCoherent` lives in `Type`, carrying the new extension `ν`.)

The (5.6)/(6.6) per-step adjoining of a new induced X-pair `{χ, χ̄}` to a coherent set `S₁`,
packaged
as a function of the member-family enumeration data.  This wires the landed crux1 chain (the genuine
(5.6.1)/(5.6.2) `Y`-collapse, `crux1_of_memberFamily`) into the adjoining bridge
(`retarget_isCoherent_of_extensionImage`).

Inputs: `IsCoherent τ S₁ A` for the Dade map `τ`, a non-real irreducible `χ` orthogonal to all of
`S₁` (with `χ̄` likewise), and a finite orthonormal member family `{χmem i}ᵢ∈ₛ ⊆ S₁` with degree
ratios `deg i` (base member `i₁` of ratio `1`), the degree-matched supported differences
`χmem i − deg i·χmem i₁` and `χ − a·χmem i₁`, and the supported Dade-image ZIrr fact
`(χ − a·χmem i₁)^τ ∈ ZIrr`.  The members' ZIrr-codomain `ν χmem i ∈ ZIrr` is read off the
`IsCoherent.extension_mem_ZIrr` field (route A: `χmem i ∈ S₁ ⊆ ℤ[S₁]`), not passed as a hypothesis.
The construction:

* `Da := decompositionDaFromDadeOfDiff …` (the χ-decomposition for `χ − a·χ₁`), with `Da.Y ∈ ZIrr`
  derived from `Da.X ∈ ℤ[R(χ)]` and `(χ − a·χ₁)^τ ∈ ZIrr`;
* per member `i`, the (5.2.e) orthogonality `⟨Da.X, ν χᵢ⟩ = 0`
  (`inner_decomposition_X_extension_member_eq_zero`) and the (5.6.1) cross-term `hfound`
  (`inner_dade_extension_of_supported`) assemble the coefficient `⟨Da.Y, ν χᵢ⟩`
  (`inner_Y_extension_member_eq`);
* `crux1_of_memberFamily` collapses the λ-form (degree inequality `2a < ∑ aᵢ²`) into
  crux1 `⟨τ(χ − a·χ₁), ν χ₁⟩ = −a`;
* crux2 `⟨τ(χ − χ̄), ν χ₁⟩ = 0` is clean from `R(χ) ⊥ R(χ₁)`;
* the bridge concludes `IsCoherent τ (S₁ ∪ {χ, χ̄}) A`.

The lattice-generation conditions `hSgen`/`hgen` (structural facts about the accumulator `S₁`) are
threaded to the bridge; the chain fold (`xChainCoherent`) discharges them from the X-family
enumeration. -/
noncomputable def xAdjoinStep
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hDeg : 2 * (a : ℝ) < ∑ i ∈ s, ((deg i : ℝ)) ^ 2)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)})) :
    OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L) := by
  classical
  -- The ZIrr-codomain of each member is now recorded by the coherence's `extension_mem_ZIrr` field
  -- (`χmem i ∈ S₁ ⊆ ℤ[S₁]`), so it need not be passed as a hypothesis (route A).
  have hmemνZ : ∀ i ∈ s, hS₁.extension (χmem i : ClassFunction ↥L ℂ) ∈ ZIrr G :=
    fun i hi => hS₁.extension_mem_ZIrr _ (Submodule.subset_span (hmemS1 i hi))
  -- The trivially-derived orthogonalities `χ, χ̄ ⊥ a·χ₁` for the χ-decomposition `Da`.
  have hχaχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ)
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχ_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  have hχbaraχ1 : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (a • (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [← Nat.cast_smul_eq_nsmul ℂ a (χmem i₁ : ClassFunction ↥L ℂ),
      OddOrder.RepresentationTheory.inner_smul_right, hχbar_S1 _ (hmemS1 i₁ hi₁), mul_zero]
  -- The χ-decomposition for the degree-matched difference `χ − a·χ₁`.
  -- (`let`, not `have`/`set`, so `Da.tau1 = τ` / `Da.imageFamily = R(χ)` reduce definitionally.)
  let Da := OddOrder.Peterfalvi.S07.decompositionDaFromDadeOfDiff hyp χ hrealχ hdiffsuppχ
    hdiffasuppχ htau1_memaχ hχaχ1 hχbaraχ1 hχχbar
  -- `Da.X ∈ ZIrr` (integer combination of the orthonormal `R(χ)` family) ⟹ `Da.Y ∈ ZIrr`.
  have hDaX_ZIrr : Da.X ∈ ZIrr G := by
    rw [Da.X_eq]
    refine Submodule.sum_mem _ (fun α hα => ?_)
    rw [Int.cast_smul_eq_zsmul ℂ (Da.coeff α) α]
    exact Submodule.smul_mem _ (Da.coeff α) (Da.imageFamily.mem_ZIrr α hα)
  have hYeq : Da.Y = Da.X - OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) := by
    have h : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) = Da.X - Da.Y :=
      Da.tau1_image
    rw [h]; abel
  have hDaY_ZIrr : Da.Y ∈ ZIrr G := by
    rw [hYeq]; exact Submodule.sub_mem _ hDaX_ZIrr htau1_memaχ
  have hchi1chi1 : ClassFunction.inner (χmem i₁ : ClassFunction ↥L ℂ)
      (χmem i₁ : ClassFunction ↥L ℂ) = 1 := by rw [hmemortho i₁ hi₁ i₁ hi₁]; simp
  -- The four `χmem i ⊥ {χ, χ̄}` orthogonalities (conjugate symmetry of `hχ_S1`/`hχbar_S1`).
  have hmemχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmemS1 i hi), star_zero]
  have hmemχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmemS1 i hi), star_zero]
  have hmembarχ : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ) = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχ_S1 _ (hmembarS1 i hi), star_zero]
  have hmembarχbar : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 0 := fun i hi => by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hχbar_S1 _ (hmembarS1 i hi), star_zero]
  -- Per-member ν-aux decomposition `D'` and the (5.2.e) family orthogonality `R(χᵢ) ⊥ R(χ)`.
  -- (`let`, not `have`, so `(Dmem i hi).tau1 = ν` reduces definitionally for the `rfl` arguments.)
  let Dmem : ∀ i, i ∈ s → OddOrder.Peterfalvi.S07.CharacterPsiDecomposition (L := ↥L) (G := G)
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (χmem i : ClassFunction ↥L ℂ) 0 := fun i hi =>
    memberExtensionDecomposition hyp hS₁ (χmem i) (hmemreal i hi) (hmemdiffsupp i hi)
      (hmemS1 i hi) (hmembarS1 i hi) (hmemνZ i hi) (hmemconjortho i hi)
  have hortho_mem : ∀ i (hi : i ∈ s), (Dmem i hi).imageFamily.Orthogonal Da.imageFamily :=
    fun i hi =>
      dadeOrthonormalCharacterImageFamilyOfDiff_orthogonal hyp (hmemreal i hi)
        (hmemdiffsupp i hi) hrealχ hdiffsuppχ (hmemχ i hi) (hmemχbar i hi) (hmembarχ i hi)
        (hmembarχbar i hi)
  -- (5.2.e) `⟨Da.X, ν χᵢ⟩ = 0` per member.
  have hXortho : ∀ i ∈ s, ClassFunction.inner Da.X (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      0 :=
    fun i hi => inner_decomposition_X_extension_member_eq_zero hS₁ Da (Dmem i hi) (hortho_mem i hi)
        rfl
  -- (5.6.1) cross-term `hfound` per member (`inner_dade_extension_of_supported`).
  have hfound : ∀ i ∈ s, ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ))) =
      ClassFunction.inner ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ))
        ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)) := fun i hi => by
    refine inner_dade_extension_of_supported hyp hS₁ hdiffasuppχ ?_
    refine OddOrder.Peterfalvi.S07.mem_zSupportedSpan_iff.mpr ⟨?_, hmemdegdiffsupp i hi⟩
    refine Submodule.sub_mem _ (Submodule.subset_span (hmemS1 i hi)) ?_
    rw [← Nat.cast_smul_eq_nsmul ℤ (deg i) (χmem i₁ : ClassFunction ↥L ℂ)]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (hmemS1 i₁ hi₁))
  -- The (5.6.1) member coefficient `⟨Da.Y, ν χᵢ⟩` in the `lambda_eq_zero_and_Z_eq_zero` form.
  have hcoeffval : ∀ i ∈ s, ClassFunction.inner Da.Y
      (hS₁.extension (χmem i : ClassFunction ↥L ℂ)) =
      (a : ℂ) * (if i = i₁ then 1 else 0) -
        ((a : ℂ) + ClassFunction.inner
          (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
            ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
          (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ))) * (deg i : ℂ) := by
    intro i hi
    have key := inner_Y_extension_member_eq hyp hS₁ χ hYeq (hXortho i hi) (hfound i hi)
      (hχ_S1 _ (hmemS1 i hi)) (hχ_S1 _ (hmemS1 i₁ hi₁)) hchi1chi1
    rw [hmemortho i₁ hi₁ i hi] at key
    rw [key]
    rcases eq_or_ne i i₁ with h | h
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc : i₁ = i => h hc.symm)]; ring
  -- crux1 via the λ-form collapse.
  have hcrux1 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = -(a : ℂ) :=
    crux1_of_memberFamily hyp
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) rfl
      hS₁ χ s (fun i => (χmem i : ClassFunction ↥L ℂ)) deg i₁ hi₁ Da hDaY_ZIrr hmemS1
      hmemortho hcoeffval htau1_memaχ ha1 hDeg
  -- crux2 clean: `⟨τ(χ − χ̄), ν χ₁⟩ = 0` from `R(χ) ⊥ R(χ₁)`.
  have hcrux2 : ClassFunction.inner
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)
        ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj))
      (hS₁.extension (χmem i₁ : ClassFunction ↥L ℂ)) = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, Da.imageFamily.image_eq,
      OddOrder.RepresentationTheory.inner_sum_right,
      Finset.sum_eq_zero (fun α hα =>
        OddOrder.Peterfalvi.S07.inner_extension_member_orthogonal_imageSet hS₁ Da.imageFamily
          (Dmem i₁ hi₁) (hortho_mem i₁ hi₁) rfl hα), star_zero]
  -- `(χ − χ̄)^τ ∈ ZIrr` from the `R(χ)` family (`image_eq`); `(χ − a·χ₁)^τ ∈ ZIrr` is
  -- `htau1_memaχ`.
  have hτdiffZ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj) ∈ ZIrr G := by
    rw [Da.imageFamily.image_eq]
    exact Submodule.sum_mem _ (fun α hα => Da.imageFamily.mem_ZIrr α hα)
  -- Adjoin via the (T8.11 option A) bridge.
  exact retarget_isCoherent_of_extensionImage hyp
    (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData)) rfl
    hS₁ χ hdiffsuppχ hdiffasuppχ hχχ hχbarχbar hχχbar hχbarχ
    (m₁ := 1) (by rw [hchi1chi1]; norm_num) hχ_S1 hχbar_S1
    (hmemS1 i₁ hi₁) htau1_memaχ hτdiffZ (by rw [hcrux1]; norm_num) hcrux2 hSgen hgen

open scoped Classical in
/-- **Peterfalvi (5.6)** — quantitative coherence, contrapositive form ("B1").

The converse of the forward adjoining engine `xAdjoinStep`: under the same Dade /
member-family hypotheses, if `S₁ ∪ {χ, χ̄}` fails to be coherent then the degree
sum is bounded by `∑ᵢ (deg i)² ≤ 2 a`.  Writing `a = ψ(1)/χ₁(1)` and
`deg i = χᵢ(1)/χ₁(1)` this is Peterfalvi's non-coherence bound
`∑_{χ∈S₁} χ(1)² ≤ 2 ψ(1) χ₁(1)`, the quantitative input consumed by (6.2) on the
way to the degree bound (6.3)/(6.5).  Proof: contrapose `xAdjoinStep` over its
degree hypothesis `hDeg : 2 a < ∑ᵢ (deg i)²`. -/
theorem coherentDegreeSumBound_of_not_coherent
    {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)] {A : Set G}
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    {S₁ : Set (ClassFunction ↥L ℂ)}
    (hS₁ : OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      S₁ (OddOrder.Peterfalvi.S04.supportInSubgroup A L))
    (χ : IrreducibleCharacter ↥L)
    (hrealχ : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsuppχ : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hχχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ) = 1)
    (hχbarχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj
      (χ : ClassFunction ↥L ℂ).conj = 1)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0)
    (hχbarχ : ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj (χ : ClassFunction ↥L ℂ) = 0)
    (hχ_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ) x = 0)
    (hχbar_S1 : ∀ x ∈ S₁, ClassFunction.inner (χ : ClassFunction ↥L ℂ).conj x = 0)
    {ι : Type*} (s : Finset ι) (χmem : ι → IrreducibleCharacter ↥L) (deg : ι → ℕ) (i₁ : ι)
    (hi₁ : i₁ ∈ s)
    (hmemreal : ∀ i ∈ s, ¬ ClassFunction.IsReal (χmem i : ClassFunction ↥L ℂ))
    (hmemdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ).conj - (χmem i : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemdegdiffsupp : ∀ i ∈ s,
      ((χmem i : ClassFunction ↥L ℂ) - deg i • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
        OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (hmemS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ) ∈ S₁)
    (hmembarS1 : ∀ i ∈ s, (χmem i : ClassFunction ↥L ℂ).conj ∈ S₁)
    (hmemconjortho : ∀ i ∈ s, ClassFunction.inner (χmem i : ClassFunction ↥L ℂ)
      (χmem i : ClassFunction ↥L ℂ).conj = 0)
    (hmemortho : ∀ i ∈ s, ∀ j ∈ s,
      ClassFunction.inner (χmem i : ClassFunction ↥L ℂ) (χmem j : ClassFunction ↥L ℂ) =
        if i = j then (1 : ℂ) else 0)
    {a : ℕ}
    (hdiffasuppχ : ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    (htau1_memaχ : OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp
      (hyp.fullDadeIsometryData)
      ((χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)) ∈ ZIrr G)
    (ha1 : deg i₁ = 1)
    (hSgen : Submodule.span ℤ S₁ ≤ Submodule.span ℤ
      (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪ {(χmem i₁ : ClassFunction ↥L ℂ)}))
    (hgen : OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L)
        (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ⊆
      Submodule.span ℤ (OddOrder.Peterfalvi.S07.zSupportedSpan (L := ↥L) S₁
        (OddOrder.Peterfalvi.S04.supportInSubgroup A L) ∪
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
         (χ : ClassFunction ↥L ℂ) - a • (χmem i₁ : ClassFunction ↥L ℂ)}))
    (hnc : ¬ Nonempty (OddOrder.Peterfalvi.S07.IsCoherent
      (OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap hyp (hyp.fullDadeIsometryData))
      (S₁ ∪ {(χ : ClassFunction ↥L ℂ), (χ : ClassFunction ↥L ℂ).conj})
      (OddOrder.Peterfalvi.S04.supportInSubgroup A L))) :
    ∑ i ∈ s, ((deg i : ℝ)) ^ 2 ≤ 2 * (a : ℝ) := by
  by_contra hlt
  push Not at hlt
  exact hnc ⟨xAdjoinStep hyp hS₁ χ hrealχ hdiffsuppχ hχχ hχbarχbar hχχbar hχbarχ
    hχ_S1 hχbar_S1 s χmem deg i₁ hi₁ hmemreal hmemdiffsupp hmemdegdiffsupp hmemS1 hmembarS1
    hmemconjortho hmemortho hdiffasuppχ htau1_memaχ ha1 hlt hSgen hgen⟩

open scoped Classical in
/-- **Peterfalvi (6.2), step (ii) — the `S(A)` degree-sum (B2 assembled).**
For `H ⊴ G`, `A ⊴ G`, `A ≤ H`, the induced family
`S(A) = {Ind_H^G θ | θ ∈ Irr H, A ⊆ Ker θ, θ ≠ 1}` satisfies
`∑_{χ ∈ S(A)} χ(1)²/‖χ‖² = [G:H]·(|H : A| − 1)`.

This assembles the orbit-counted identity `sum_div_normSq_induce_image_eq`
(`∑ = [G:H]·∑_{θ∈T}θ(1)²`, fibres of `θ ↦ Ind θ` are `G`-conjugacy orbits) with the inflation
degree-sum `sumInflatedDegreeSq_ntrivial` (`∑_{θ∈T}θ(1)² = |H ⧸ A| − 1`, Burnside on `H ⧸ A`).
The index set `T = {θ ∈ Irr H | A ⊆ Ker θ, θ ≠ 1}` is `G`-conjugation-invariant because `A ⊴ G`:
`Ker(θ^g) = g·(Ker θ)·g⁻¹ ⊇ g·A·g⁻¹ = A`.  This is the (6.2) input "step (ii)" that, with the
(5.6) bound B1 and the θ-bound, yields `2|L:C|√|C:D| ≥ |K:A| − 1`. -/
theorem sum_div_normSq_induce_kernelFilter_eq {G : Type*} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)] {H : Subgroup G} [H.Normal] [Invertible (Nat.card ↥H : ℂ)]
    {A : Subgroup G} [A.Normal] :
    ∑ χ ∈ (Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
        (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
            (θ : ClassFunction ↥H ℂ) ∧
          θ ≠ trivialIrreducibleCharacter ↥H)).image
        (fun θ => ClassFunction.induce H θ.toClassFunction),
        χ 1 ^ 2 / ClassFunction.inner χ χ
      = (H.index : ℂ) * ((Nat.card (↥H ⧸ A.subgroupOf H) : ℂ) - 1) := by
  classical
  have hconj : ∀ θ ∈ Finset.univ.filter (fun θ : IrreducibleCharacter ↥H =>
      (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
          (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H),
      ∀ g : G, IrreducibleCharacter.conjBy g θ ∈ Finset.univ.filter
        (fun θ : IrreducibleCharacter ↥H =>
          (↑(A.subgroupOf H) : Set ↥H) ⊆ OddOrder.Peterfalvi.S03.characterKernel
              (θ : ClassFunction ↥H ℂ) ∧ θ ≠ trivialIrreducibleCharacter ↥H) := by
    intro θ hθ g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hθ ⊢
    obtain ⟨hker, hne⟩ := hθ
    refine ⟨?_, ?_⟩
    · -- `A ⊆ Ker(θ^g)`: each `a ∈ A` has `g·a·g⁻¹ ∈ A ⊆ Ker θ`.
      intro a ha
      have hmemA : (⟨g * (a : G) * g⁻¹, ‹H.Normal›.conj_mem (a : G) a.2 g⟩ : ↥H)
          ∈ A.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact ‹A.Normal›.conj_mem (a : G) (Subgroup.mem_subgroupOf.mp ha) g
      have hk := hker hmemA
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hk
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def, conjBy_apply_one,
        IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply, hk,
        OddOrder.Peterfalvi.S03.characterDegree_def]
    · -- `θ^g ≠ 1`: conjugation is injective and fixes the trivial character.
      intro hc
      apply hne
      have h1 : IrreducibleCharacter.conjBy g⁻¹ (IrreducibleCharacter.conjBy g θ) = θ := by
        rw [← IrreducibleCharacter.conjBy_mul, mul_inv_cancel, IrreducibleCharacter.conjBy_one]
      rw [← h1, hc, IrreducibleCharacter.ext_iff]
      ext h
      rw [IrreducibleCharacter.coe_conjBy, ClassFunction.conjBy_apply]
      simp
  rw [sum_div_normSq_induce_image_eq _ hconj]
  congr 1
  exact sumInflatedDegreeSq_ntrivial (N := A.subgroupOf H)

end OddOrder.Peterfalvi.S08


