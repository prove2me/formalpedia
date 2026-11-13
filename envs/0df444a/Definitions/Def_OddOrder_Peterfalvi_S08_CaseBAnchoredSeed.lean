-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAnchoredSeed
-- name    : OddOrder_Peterfalvi_S08_CaseBAnchoredSeed
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:22:33.212645+00:00
-- url     : https://prove2.me/theorems/4a9bf5dd-7462-4fcb-9d90-ccc57e684593
-- title:
--   Peterfalvi (6.8.2) case (B): per-column anchored seed
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §6, (6.8.2.3). The case-(B) coherence seed for $X(W_2)\cup Y$ is built by gluing the certain-type column coherence with the $Y$-coherence; this file produces the anchored $X$-coherence on the full $X(W_2)$.
--
--   Main definitions: `caseBXsetExtensionFun` and `caseBXsetExtension` (the dichotomy extension $\nu$, the case-(B) $\tau_2$ on the full $X$-set), `caseBXimg` (the anchored-image function) and `caseBXset_isCoherent` (the (6.8.2) case-(B) $X$-coherence via anchored images).
--
--   The bundle also proves 9 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBAnchoredSeed.lean

/-
Copyright (c) 2026 The Odd Order Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBAnchoredSeed.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBXChiCoherence
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBEnumeration
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBSeedSetup

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.3) per-member anchored image for an arbitrary `X`-member.**  Generalizes
`caseB_column_anchored_full` from a certain-type column to **any** `χ ∈ Xset W₂` (reducible column
or
irreducible).  Every such `χ = Ind^L_H θ` with `W₂ ⊄ Ker θ` (from `S_eq` and `χ ∉ S(W₂)`: had
`W₂ ⊆ Ker θ` then `χ ∈ S(W₂)`), so `caseB_member_anchored_image` supplies the (6.8.2.3) anchored
image with `a = χ(1)/|W₁| = θ(1)`.

This is the uniform (6.8.2.3) datum for the **whole** of `X` — the per-member input to the case-(B)
`Xset W₂ ∪ Y` coherence seed (Peterfalvi (6.8.2), built via the anchored-image isometry `τ₂`, *not*
the `(6.6)` chain — see roadmap cont.¹²). -/
theorem caseB_Xset_member_anchored
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Finite (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Finite ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H)
    (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset h46.W2)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ∃ (X : ClassFunction G ℂ) (a : ℕ),
      ((χ : ClassFunction ↥L ℂ) 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (χ - a • η₁) = X - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner X (cY.extension η₁) = 0 ∧
      X ∈ ZIrr G ∧
      (χ - a • η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  classical
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have : Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W := Fintype.ofFinite _
  have : Fintype ↥(h46.W2.subgroupOf H) := Fintype.ofFinite _
  obtain ⟨hχS, hχnotsub⟩ := hyp.mem_Xset.mp hχ
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne1, hχeq⟩ := hχS
  have hθne : ∃ w : ↥(h46.W2.subgroupOf H),
      (θ : ClassFunction ↥H ℂ) (w : ↥H) ≠ (θ : ClassFunction ↥H ℂ) 1 := by
    by_contra hc
    push Not at hc
    exact hχnotsub (hyp.mem_SsubFiltration.mpr ⟨θ, hθne1, fun g hg => by
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel]; exact hc ⟨g, hg⟩, hχeq⟩)
  obtain ⟨X, a, hdeg, hanc, hmix, hXZ⟩ :=
    caseB_member_anchored_image hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
      hW2cenL hc2 hFPF hη₁ θ hθne cY hcYgood
  subst hχeq
  have hsupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
    have h := hyp.sMember_smulDiffSupport_of_charValue_eq
      (hyp.Xset_subset_S hχ) (hyp.Yset_subset_S hη₁) (m := 1) (n := a)
      (by rw [Nat.cast_one, one_mul]; exact hdeg)
    rwa [one_smul] at h
  exact ⟨X, a, hdeg, hanc, hmix, hXZ, hsupp⟩

/-- **(6.8.2) cross-member isometry, varying degree.**  Generalizes `xchi_inner_eq_of_anchored`
from a single uniform anchor weight `a₀` (equal-degree columns) to **per-member** weights `aᵢ, aⱼ`
(arbitrary `X`-members of differing degree).  From the anchored images `τ(χᵢ − aᵢη₁) = Xᵢ − aᵢν₁`
(`hancᵢ`), the seams `⟨Xᵢ, ν₁⟩ = 0` (`hmixᵢ`), the source orthogonalities `⟨χᵢ, η₁⟩ = 0`
(`horthᵢ`, the `X ⊥ Y` pairing), the Dade isometry of `τ` on the `H^#`-supported anchored
differences, and `‖η₁‖² = ‖ν₁‖² = 1`:
`⟨Xᵢ, Xⱼ⟩ = (⟨χᵢ,χⱼ⟩ + aᵢaⱼ) − aᵢaⱼ − aᵢaⱼ + aᵢaⱼ = ⟨χᵢ, χⱼ⟩`.

This is the `hXinner` content for the **full** `Xset W₂` coherence (varying-degree generalization of
the certain-type `hXinner`). -/
theorem inner_eq_of_anchored_varying
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {χi χj : ClassFunction ↥L ℂ} {ai aj : ℕ} {Xi Xj : ClassFunction G ℂ}
    (hanci : hyp.tau (χi - ai • η₁) = Xi - (ai : ℂ) • cY.extension η₁)
    (hancj : hyp.tau (χj - aj • η₁) = Xj - (aj : ℂ) • cY.extension η₁)
    (hmixi : ClassFunction.inner Xi (cY.extension η₁) = 0)
    (hmixj : ClassFunction.inner Xj (cY.extension η₁) = 0)
    (horthi : ClassFunction.inner χi η₁ = 0) (horthj : ClassFunction.inner χj η₁ = 0)
    (hsuppi : (χi - ai • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hsuppj : (χj - aj • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ClassFunction.inner Xi Xj = ClassFunction.inner χi χj := by
  classical
  set ν := cY.extension η₁ with hνdef
  have hXi : Xi = hyp.tau (χi - ai • η₁) + (ai : ℂ) • ν := by
    rw [hanci]; abel
  have hXj : Xj = hyp.tau (χj - aj • η₁) + (aj : ℂ) • ν := by
    rw [hancj]; abel
  have hηirr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hηη : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hηirr⟩ : IrreducibleCharacter ↥L)
    rwa [if_pos rfl] at h
  have hνν : ClassFunction.inner ν ν = 1 := by
    rw [hνdef, cY.extension_inner_eq η₁ η₁ (Submodule.subset_span hη₁)
      (Submodule.subset_span hη₁), hηη]
  -- `⟨τ(χᵢ−aᵢη₁), τ(χⱼ−aⱼη₁)⟩ = ⟨χᵢ,χⱼ⟩ + aᵢaⱼ` (Dade isometry on the supported pair).
  have hττ : ClassFunction.inner (hyp.tau (χi - ai • η₁)) (hyp.tau (χj - aj • η₁))
      = ClassFunction.inner χi χj + (ai : ℂ) * (aj : ℂ) := by
    rw [OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span hyp.dade
      (S := ({χi - ai • η₁, χj - aj • η₁} : Set (ClassFunction ↥L ℂ)))
        (by intro s hs; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
            rcases hs with rfl | rfl; exacts [hsuppi, hsuppj])
        (Submodule.subset_span (Set.mem_insert _ _))
        (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))]
    have hηj : ClassFunction.inner η₁ χj = 0 := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm, horthj, star_zero]
    simp only [← Nat.cast_smul_eq_nsmul ℂ ai η₁, ← Nat.cast_smul_eq_nsmul ℂ aj η₁,
      ClassFunction.inner_sub_left, ClassFunction.inner_sub_right, ClassFunction.inner_smul_left,
      OddOrder.RepresentationTheory.inner_smul_right, star_natCast, horthi, hηj, hηη]
    ring
  -- the cross terms with `ν`.
  have hτiν : ClassFunction.inner (hyp.tau (χi - ai • η₁)) ν = -(ai : ℂ) := by
    rw [hanci]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
    rw [hmixi, hνν]; ring
  have hτjν : ClassFunction.inner (hyp.tau (χj - aj • η₁)) ν = -(aj : ℂ) := by
    rw [hancj]
    simp only [ClassFunction.inner_sub_left, ClassFunction.inner_smul_left]
    rw [hmixj, hνν]; ring
  have hντj : ClassFunction.inner ν (hyp.tau (χj - aj • η₁)) = -(aj : ℂ) := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hτjν, star_neg, star_natCast]
  rw [hXi, hXj]
  simp only [ClassFunction.inner_add_left, ClassFunction.inner_add_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right, star_natCast]
  rw [hττ, hτiν, hντj, hνν]; ring

/-- **(6.8.2) scaled-difference identity** (the `extends_on_supported` content for the full
`Xset W₂` coherence).  From two anchored images `τ(χᵢ − aᵢη₁) = Xᵢ − aᵢν₁`, `τ(χ₁ − a₁η₁) =
X₁ − a₁ν₁` with the **degree ratio** `aᵢ = dᵢ·a₁` (i.e. `χᵢ(1) = dᵢ·χ₁(1)`, integral since `H` is a
`p`-group), the `ν₁`-terms cancel and `τ` is linear, so the scaled difference maps homogeneously:
`Xᵢ − dᵢ·X₁ = τ(χᵢ − dᵢ·χ₁)`.

This is the textbook fact that on the supported generators `χᵢ − dᵢχ₁` the running extension
`τ₂` agrees with `τ` (the `(6.8.2)` `τ₂` defined via the anchored images), generalizing the
equal-degree column-difference identity to varying degree (cf. `span_subset_span_
zSupportedSpan_union_anchor_of_scaledDiffs`, the matching generation). -/
theorem anchoredImage_scaledDiff_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ}
    {χi χ1 : ClassFunction ↥L ℂ} {ai a1 di : ℕ} {Xi X1 : ClassFunction G ℂ}
    (hanci : hyp.tau (χi - ai • η₁) = Xi - (ai : ℂ) • cY.extension η₁)
    (hanc1 : hyp.tau (χ1 - a1 • η₁) = X1 - (a1 : ℂ) • cY.extension η₁)
    (hai : ai = di * a1) :
    Xi - di • X1 = hyp.tau (χi - di • χ1) := by
  have hχ : χi - di • χ1 = (χi - ai • η₁) - di • (χ1 - a1 • η₁) := by
    rw [smul_sub, ← mul_smul, ← hai]; abel
  have hνcancel : di • ((a1 : ℂ) • cY.extension η₁)
      = (ai : ℂ) • cY.extension η₁ := by
    rw [← Nat.cast_smul_eq_nsmul ℂ di ((a1 : ℂ) • cY.extension η₁), smul_smul,
      ← Nat.cast_mul, ← hai]
  rw [hχ, map_sub, map_nsmul, hanci, hanc1, smul_sub, hνcancel]; abel

/-- **(6.8.2) grid constituents are not `X`-members** — `μ_{iχ₂} ∉ Xset W₂`.  A certain-type grid
character has degree `≡ ±1 (mod |W₁|)` (`certainType_degree_modEq`, the sign `= ±1`), whereas every
`X`-member `Ind^L_H θ` has degree `|W₁|·θ(1) ≡ 0 (mod |W₁|)`; with `|W₁| ≠ 1` these are
incompatible.

This is the disjointness underlying the **dichotomy extension** for the full `Xset W₂` coherence: on
the basis `Irr L`, the irreducible `X`-members `χ ↦ Ximg χ` and the column grid members
`μ_{iχ₂} ↦ (column image, concentrated on `i = 0`)` never collide, so the extension is well-defined
and sends each column `columnSum χ₂ = ∑_i μ_{iχ₂}` to its image. -/
theorem grid_mu_notMem_Xset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Finite ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) ∉ hyp.Xset h46.W2 := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  intro hmem
  have hS := hyp.Xset_subset_S hmem
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hS
  obtain ⟨θ, -, hμeq⟩ := hS
  obtain ⟨a, ha⟩ := h46.certainType_degree_modEq χ₂ i
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
  have hindeg : ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
      = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
    rw [hμeq, ClassFunction.induce_apply_one, hd, hyp.index_H_eq_card_W1]
  rw [hindeg] at ha
  have hcard : (Nat.card h46.W1 : ℂ) = (Nat.card hyp.W1 : ℂ) := by rw [hW1]
  rw [hcard] at ha
  have hw1 : Nat.card hyp.W1 ≠ 1 := fun h => hyp.W1_nontrivial (Subgroup.card_eq_one.mp h)
  have hsignZ : (h46.columnFamily χ₂).sign = (Nat.card hyp.W1 : ℤ) * ((d : ℤ) - a) := by
    have hsign : ((h46.columnFamily χ₂).sign : ℂ)
        = (Nat.card hyp.W1 : ℂ) * ((d : ℂ) - (a : ℂ)) := by linear_combination -ha
    exact_mod_cast hsign
  have hdvd1 : (Nat.card hyp.W1 : ℤ) ∣ 1 := by
    have hdvd : (Nat.card hyp.W1 : ℤ) ∣ (h46.columnFamily χ₂).sign := ⟨(d : ℤ) - a, hsignZ⟩
    rcases (h46.columnFamily χ₂).sign_eq with hs | hs
    · rwa [hs] at hdvd
    · rw [hs] at hdvd; exact (dvd_neg).mp hdvd
  exact hw1 (Nat.dvd_one.mp (by exact_mod_cast hdvd1))

open scoped Classical in
/-- **(6.8.2) the dichotomy extension function** for the full `Xset W₂` coherence.  On the basis
`Irr L`: an irreducible `X`-member `ω ∈ Xset W₂` maps to its anchored image `Ximg ω`; everything
else falls back to the column extension `xChiExtensionFun` (which sends a grid `0`-row member
`μ_{0χ₂}` to `Ximg (columnSum χ₂)`, other grid members to `0`).  By `grid_mu_notMem_Xset` the two
branches never collide on the grid, so each column `columnSum χ₂` maps to `Ximg (columnSum χ₂)`. -/
noncomputable def caseBXsetExtensionFun
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ) :
    IrreducibleCharacter ↥L → ClassFunction G ℂ :=
  fun ω => if (ω : ClassFunction ↥L ℂ) ∈ hyp.Xset h46.W2 then Ximg (ω : ClassFunction ↥L ℂ)
    else xChiExtensionFun h46 (fun χ₂ => Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)) ω

/-- The dichotomy extension `ν` (the case-(B) `τ₂` on the full `X`-set): the global `ℤ`-linear
`CF(L) → CF(G)` built from `caseBXsetExtensionFun` on the basis `Irr L`. -/
noncomputable def caseBXsetExtension
    (hyp : SibleyDadeHypothesis G L H)
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  ((OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr ℂ
    (caseBXsetExtensionFun hyp h46 Ximg)).restrictScalars ℤ

/-- On a grid member `μ_{iχ₂}` (not an `X`-member, `grid_mu_notMem_Xset`) the dichotomy extension
agrees with the column extension `xChiExtension`. -/
theorem caseBXsetExtension_grid
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) (i : Fin (Nat.card h46.W1)) :
    caseBXsetExtension hyp h46 Ximg ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = xChiExtension h46 (fun χ₂ => Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂))
          ((h46.columnFamily χ₂).mu i) := by
  classical
  rw [caseBXsetExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu i)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu i), caseBXsetExtensionFun,
    if_neg (grid_mu_notMem_Xset hyp h46 hW1 χ₂ i),
    xChiExtension, LinearMap.restrictScalars_apply]
  conv_rhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu i)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu i)]

/-- On a certain-type column `columnSum χ₂` the dichotomy extension sends it to
`Ximg (columnSum χ₂)`:
every grid member maps via the column extension (`caseBXsetExtension_grid`), and only the `0`-row
survives (`xChiExtension_columnSum`). -/
theorem caseBXsetExtension_columnSum
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    caseBXsetExtension hyp h46 Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      = Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) := by
  classical
  rw [OddOrder.Peterfalvi.S06.columnSum_def, map_sum,
    Finset.sum_congr rfl (fun i _ => caseBXsetExtension_grid hyp h46 hW1 Ximg χ₂ i),
    ← map_sum, ← OddOrder.Peterfalvi.S06.columnSum_def, xChiExtension_columnSum]

/-- On an irreducible `X`-member `χ ∈ Xset W₂` the dichotomy extension sends it to `Ximg χ`
(the `ω ∈ Xset W₂` branch on the basis element `χ`). -/
theorem caseBXsetExtension_irr
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    {χ : ClassFunction ↥L ℂ} (hirr : IsIrreducibleCharacter χ)
    (hmem : χ ∈ hyp.Xset h46.W2) :
    caseBXsetExtension hyp h46 Ximg χ = Ximg χ := by
  classical
  have hcoe : ((⟨χ, hirr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ := rfl
  rw [caseBXsetExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← hcoe, ← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    (⟨χ, hirr⟩ : IrreducibleCharacter ↥L), caseBXsetExtensionFun, hcoe, if_pos hmem]

/-- **The dichotomy extension realizes the anchored images on the whole `X`-set**: `ν χ = Ximg χ`
for every `χ ∈ Xset W₂` (column or irreducible, via `caseB_S_member_column_or_irreducible`). -/
theorem caseBXsetExtension_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ClassFunction ↥L ℂ → ClassFunction G ℂ)
    {χ : ClassFunction ↥L ℂ} (hmem : χ ∈ hyp.Xset h46.W2) :
    caseBXsetExtension hyp h46 Ximg χ = Ximg χ := by
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hmem) with
    ⟨χ₂, -, hcol⟩ | hirr
  · rw [← hcol, caseBXsetExtension_columnSum hyp h46 hW1 Ximg χ₂]
  · exact caseBXsetExtension_irr hyp h46 Ximg hirr hmem

omit [Fintype G] [Invertible (Nat.card G : ℂ)] [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)] in
/-- **(6.8.2) supported generation by scaled differences** (the varying-degree analogue of
`mem_span_columnDiff_of_mem_zSupportedSpan`).  Given an anchor `χ₁ ∈ S₁` (with `χ₁(1) ≠ 0`) such
that
every `f ∈ S₁` has degree `f(1) = d·χ₁(1)` for some `d : ℕ` (the integral degree ratio, available
for
`X`-members since `H` is a `p`-group), every supported (degree-`0`) `φ ∈ Z[S₁, A₀]` lies in the span
of the scaled differences `f − d·χ₁`.

The support set is arbitrary subject to `1 ∉ A₀` — that is the only thing the argument uses of it
(it forces `φ(1) = 0`).  Stating it that way lets the same lemma serve the §9 route, where `A₀` is
`A(M) ∪ V^M` rather than `H^#`.

Proof mirrors the equal-degree case: the scaled differences vanish at `1` (`f(1) − d·χ₁(1) = 0`), so
`D = span{f − d·χ₁}` sits inside `ker(ev₁)`; `Z[S₁] ≤ D ⊔ ℤ·χ₁` (write `f = (f − d·χ₁) + d·χ₁`); and
a
supported `φ = y + n·χ₁` has `0 = φ(1) = n·χ₁(1)`, forcing `n = 0`, so `φ = y ∈ D`. -/
theorem mem_span_scaledDiff_of_mem_zSupportedSpan
    {A0 : Set ↥L} (h1A0 : (1 : ↥L) ∉ A0)
    {S₁ : Set (ClassFunction ↥L ℂ)} {χ₁ : ClassFunction ↥L ℂ}
    (hχ₁1 : (χ₁ : ClassFunction ↥L ℂ) 1 ≠ 0)
    (hdeg : ∀ f ∈ S₁, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    {φ : ClassFunction ↥L ℂ}
    (hφ : φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan S₁ A0) :
    φ ∈ Submodule.span ℤ
      {g : ClassFunction ↥L ℂ | ∃ f ∈ S₁, ∃ d : ℕ,
        (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1 ∧ g = f - d • χ₁} := by
  classical
  obtain ⟨hφspan, hφsupp⟩ := hφ
  set T : Set (ClassFunction ↥L ℂ) := {g | ∃ f ∈ S₁, ∃ d : ℕ,
    (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1 ∧ g = f - d • χ₁} with hT
  set ev1 : ClassFunction ↥L ℂ →+ ℂ := AddMonoidHom.mk' (fun ψ => ψ (1 : ↥L)) (fun _ _ => rfl)
    with hev1
  have hD_vanish : ∀ δ ∈ Submodule.span ℤ T, ev1 δ = 0 := by
    intro δ hδ
    induction hδ using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨f, _, d, hfd, rfl⟩ := hx
        change (f - d • χ₁) (1 : ↥L) = 0
        rw [ClassFunction.sub_apply, ← Nat.cast_smul_eq_nsmul ℂ d χ₁, ClassFunction.smul_apply,
          hfd, sub_self]
    | zero => exact map_zero ev1
    | add x y _ _ ihx ihy => rw [map_add, ihx, ihy, add_zero]
    | smul a x _ ih => rw [map_zsmul, ih, smul_zero]
  have hspan_le : Submodule.span ℤ S₁ ≤ Submodule.span ℤ T ⊔ Submodule.span ℤ {χ₁} := by
    rw [Submodule.span_le]
    intro f hf
    obtain ⟨d, hfd⟩ := hdeg f hf
    rw [show f = (f - d • χ₁) + d • χ₁ from by abel]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (Submodule.subset_span ⟨f, hf, d, hfd, rfl⟩))
      (Submodule.mem_sup_right ?_)
    rw [← Nat.cast_smul_eq_nsmul ℤ d χ₁]
    exact Submodule.smul_mem _ _ (Submodule.subset_span rfl)
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp (hspan_le hφspan)
  obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hφ1 : ev1 φ = 0 := by
    change φ (1 : ↥L) = 0
    by_contra hne
    exact h1A0 (hφsupp (ClassFunction.mem_support.mpr hne))
  rw [← hyz, map_add, hD_vanish y hy, zero_add, map_zsmul] at hφ1
  have hn : n = 0 := by
    rcases smul_eq_zero.mp hφ1 with hn | hd
    · exact hn
    · exact absurd hd (show ev1 χ₁ ≠ 0 from hχ₁1)
  rw [← hyz, hn, zero_smul, add_zero]; exact hy

open scoped Classical in
/-- **The case-(B) anchored-image function** `Ximg : CF(L) → CF(G)` on the `X`-set: each
`χ ∈ Xset W₂` maps to the `(6.8.2.3)` virtual character `X` (`caseB_Xset_member_anchored`, chosen),
elsewhere `0`. -/
noncomputable def caseBXimg
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ)) :
    ClassFunction ↥L ℂ → ClassFunction G ℂ :=
  fun χ => if hχ : χ ∈ hyp.Xset h46.W2 then
    (caseB_Xset_member_anchored hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
      hW2cenL hc2 hFPF hη₁ hχ cY hcYgood).choose
  else 0

/-- The defining property of `caseBXimg` on an `X`-member: the `(6.8.2.3)` anchored image, seam,
`ZIrr`-membership and support, with the chosen weight `a`. -/
theorem caseBXimg_spec
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset h46.W2) :
    ∃ a : ℕ, (χ 1 = (a : ℂ) * η₁ 1) ∧
      hyp.tau (χ - a • η₁) = caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
          hW2cenL hc2 hFPF hη₁ cY hcYgood χ - (a : ℂ) • cY.extension η₁ ∧
      ClassFunction.inner (caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
          hW2cenL hc2 hFPF hη₁ cY hcYgood χ) (cY.extension η₁) = 0 ∧
      caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF hη₁
          cY hcYgood χ ∈ ZIrr G ∧
      (χ - a • η₁).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  have : caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF hη₁
      cY hcYgood χ = (caseB_Xset_member_anchored hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime
        hW2comm hW2cenL hc2 hFPF hη₁ hχ cY hcYgood).choose := by
    rw [caseBXimg, dif_pos hχ]
  rw [this]
  exact (caseB_Xset_member_anchored hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm
    hW2cenL hc2 hFPF hη₁ hχ cY hcYgood).choose_spec

/-- **Peterfalvi (6.8.2) — case-(B) `X`-coherence via anchored images** (the full `Xset W₂`, varying
degree).  Given the case-(B) structural data, a degree anchor `χ₁ ∈ Xset W₂` with `χ₁(1) ≠ 0` whose
degree divides every `X`-member's (`hdvd`, integral since `H` is a `p`-group), and a nonzero
supported witness, `hyp.tau` is coherent on `Xset W₂` with extension the dichotomy map
`caseBXsetExtension` (sending each `χ` to its `(6.8.2.3)` anchored image `Ximg χ`).

The three coherence conditions are exactly the building blocks: the isometry is
`inner_eq_of_anchored_varying` (per member, varying degree), the supported `τ`-agreement is
`anchoredImage_scaledDiff_eq` over the scaled-difference generators
(`mem_span_scaledDiff_of_mem_zSupportedSpan`), and the `ZIrr`-codomain is the per-member bundle. -/
noncomputable def caseBXset_isCoherent
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Fintype ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    [h46.W2.Normal] [Invertible (Nat.card ↥h46.W2 : ℂ)]
    [Fintype ↥(h46.W2.subgroupOf H)] [Invertible (Nat.card ↥(h46.W2.subgroupOf H) : ℂ)]
    (hW2H : h46.W2 ≤ H) (hcen : h46.W2.subgroupOf H ≤ Subgroup.center ↥H)
    (hderiv : h46.W2.subgroupOf H ≤ commutator ↥H)
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    (hprime : (Nat.card h46.W2).Prime) (hW2comm : h46.W2 ≤ ⁅H, H⁆)
    (hW2cenL : h46.W2 ≤ Subgroup.center ↥L)
    (hc2 : 2 ≤ (h46.W2.subgroupOf H).index)
    (hFPF : (h46.W2.index : ℤ) < ((h46.W2.subgroupOf H).index : ℤ) ^ 2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hcYgood : ∀ φ : IrreducibleCharacter ↥h46.W2, (φ : ClassFunction ↥h46.W2 ℂ) 1 = 1 →
      φ ≠ trivialIrreducibleCharacter ↥h46.W2 →
      ClassFunction.inner (hyp.tau (ClassFunction.induce h46.W2 (φ : ClassFunction ↥h46.W2 ℂ)
          - ((h46.W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((h46.W2.subgroupOf H).index : ℂ))
    (hη₁1 : η₁ (1 : ↥L) ≠ 0)
    {χ₁ : ClassFunction ↥L ℂ} (hanchor : χ₁ ∈ hyp.Xset h46.W2) (hχ₁1 : χ₁ (1 : ↥L) ≠ 0)
    (hdvd : ∀ f ∈ hyp.Xset h46.W2, ∃ d : ℕ, (f : ClassFunction ↥L ℂ) 1 = (d : ℂ) * χ₁ 1)
    (hnonzero : ∃ φ : ClassFunction ↥L ℂ, φ ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset h46.W2) (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) ∧ φ ≠ 0) :
    OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset h46.W2)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) where
  nonzero := hnonzero
  extension := caseBXsetExtension hyp h46
    (caseBXimg hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
      hη₁ cY hcYgood)
  extension_inner_eq := by
    intro φ ψ hφ hψ
    rw [OddOrder.Peterfalvi.S07.zSpan] at hφ hψ
    induction hφ, hψ using Submodule.span_induction₂ with
    | mem_mem u v hu hv =>
        rw [caseBXsetExtension_eq hyp h46 hHK hW1 _ hu, caseBXsetExtension_eq hyp h46 hHK hW1 _ hv]
        obtain ⟨au, -, hauanc, hauseam, -, hausupp⟩ :=
          caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2
            hFPF hη₁ cY hcYgood hu
        obtain ⟨av, -, havanc, havseam, -, havsupp⟩ :=
          caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2
            hFPF hη₁ cY hcYgood hv
        exact inner_eq_of_anchored_varying hyp cY hη₁ hauanc havanc hauseam havseam
          (caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm u hu η₁ hη₁)
          (caseB_Xset_orthogonal_Yset hyp h46 hHK hW1 hW2comm v hv η₁ hη₁) hausupp havsupp
    | zero_left v _ => rw [map_zero, ClassFunction.inner_zero_left, ClassFunction.inner_zero_left]
    | zero_right u _ => rw [map_zero, ClassFunction.inner_zero_right,
        ClassFunction.inner_zero_right]
    | add_left u₁ u₂ v _ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_left, ClassFunction.inner_add_left, ih₁, ih₂]
    | add_right u v₁ v₂ _ _ _ ih₁ ih₂ =>
        rw [map_add, ClassFunction.inner_add_right, ClassFunction.inner_add_right, ih₁, ih₂]
    | smul_left r u v _ _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (caseBXsetExtension hyp h46 _ u),
          ← Int.cast_smul_eq_zsmul ℂ r u, ClassFunction.inner_smul_left,
          ClassFunction.inner_smul_left, ih]
    | smul_right r u v _ _ ih =>
        rw [map_zsmul, ← Int.cast_smul_eq_zsmul ℂ r (caseBXsetExtension hyp h46 _ v),
          ← Int.cast_smul_eq_zsmul ℂ r v, OddOrder.RepresentationTheory.inner_smul_right,
          OddOrder.RepresentationTheory.inner_smul_right, ih]
  extends_on_supported := by
    intro φ hφ
    refine OddOrder.Peterfalvi.S07.IntegralCharacterMap.eq_on_zSpan_of_eq_on ?_
      (mem_span_scaledDiff_of_mem_zSupportedSpan
        (by
          rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
          simp only [sharpImage, Set.mem_sdiff, Set.mem_singleton_iff]
          exact fun h => h.2 (by simp))
        hχ₁1 hdvd hφ)
    rintro _ ⟨f, hf, d, hfd, rfl⟩
    obtain ⟨af, hafdeg, hafanc, -, -, -⟩ :=
      caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
        hη₁ cY hcYgood hf
    obtain ⟨a1, ha1deg, ha1anc, -, -, -⟩ :=
      caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2 hFPF
        hη₁ cY hcYgood hanchor
    have haf : af = d * a1 := by
      have h1 : (af : ℂ) * η₁ 1 = ((d * a1 : ℕ) : ℂ) * η₁ 1 := by
        rw [← hafdeg, hfd, ha1deg]; push_cast; ring
      exact_mod_cast mul_right_cancel₀ hη₁1 h1
    rw [map_sub, map_nsmul, caseBXsetExtension_eq hyp h46 hHK hW1 _ hf,
      caseBXsetExtension_eq hyp h46 hHK hW1 _ hanchor]
    rw [show af = d * a1 from haf] at hafanc
    exact anchoredImage_scaledDiff_eq hyp cY hafanc ha1anc rfl
  extension_mem_ZIrr := by
    intro φ hφ
    rw [OddOrder.Peterfalvi.S07.zSpan] at hφ
    induction hφ using Submodule.span_induction with
    | mem u hu =>
        rw [caseBXsetExtension_eq hyp h46 hHK hW1 _ hu]
        obtain ⟨-, -, -, -, hZ, -⟩ :=
          caseBXimg_spec hyp h46 hHK hW1 hW2H hcen hderiv hcop hp hHp hprime hW2comm hW2cenL hc2
            hFPF hη₁ cY hcYgood hu
        exact hZ
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => rw [map_add]; exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih => rw [map_zsmul]; exact Submodule.smul_mem _ a ih

end OddOrder.Peterfalvi.S08


