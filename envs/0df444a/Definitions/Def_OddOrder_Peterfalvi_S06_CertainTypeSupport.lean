-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSupport
-- name    : OddOrder_Peterfalvi_S06_CertainTypeSupport
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:11:36.228257+00:00
-- url     : https://prove2.me/theorems/4be923bd-00b0-4dad-83bc-ce7a16bb835e
-- title:
--   Peterfalvi (4.7): the core support lemma for characters with $H\not\subseteq\mathrm{Ker}\chi$
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §4, pp. 21-24, statement (4.7). Under Hypothesis (4.6), an irreducible character $\chi$ of $K$ with $H\not\subseteq\mathrm{Ker}\chi$ is supported on $A\cup\{1\}$.
--
--   Results: `mem_A_of_apply_ne_zero_of_not_subset_characterKernel` (the core support statement), `apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel` ($\mathrm{Supp}\chi\subseteq A\cup\{1\}$), `induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel` (the induced-character support) and the $j\ge1$ kernel and support statements for the columns $\chi_j$.
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeSupport.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeSupport.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainHypothesis46
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeClifford
import Definitions.Def_OddOrder_Peterfalvi_S03b_Vanishing

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

omit [Fintype ↥L] [Fintype G] in
omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (4.7)**, core support statement, *structural form*.  This is the (4.7) core
depending
only on the (4.6.c)/(4.6.d) data — a normal `subH ≤ K` and the covering condition `A_covers` — and
**not** on the Dade isometry (`dade0`/`tau`) of `Hypothesis46`.  It therefore applies in any setting
that supplies these structural data (e.g. the §10 type-`P` setting, via `K = M'`, `subH = M_F`, and
`A = A(M)`), without constructing the enlarged-support Dade datum.

If `χ ∈ Irr(K)` satisfies `subH ⊄ Ker χ`, then every nonidentity `g ∈ K` with `χ(g) ≠ 0` maps into
`A` (i.e. `Supp χ ⊆ A ∪ {1}`). -/
theorem mem_A_of_apply_ne_zero_of_covers [Finite G]
    (K : Subgroup ↥L) (subH : Subgroup ↥L) (subH_normal : subH.Normal)
    (A_covers : ∀ (hh : ↥L), hh ∈ subH → hh ≠ 1 →
      ∀ (x : ↥L), x ∈ Subgroup.centralizer ({hh} : Set ↥L) ⊓ K → x ≠ 1 → (L.subtype x) ∈ A)
    (χ : IrreducibleCharacter ↥K)
    (hker : ¬ ((subH.subgroupOf K : Set ↥K) ⊆ S03.characterKernel (χ : ClassFunction ↥K ℂ)))
    {g : ↥K}
    (hg1 : L.subtype (K.subtype g) ≠ 1)
    (hval : (χ : ClassFunction ↥K ℂ) g ≠ 0) :
    L.subtype (K.subtype g) ∈ A := by
  classical
  have : Fintype G := Fintype.ofFinite G
  -- `subH` is normal in `K` (a normal subgroup of `L` contained in `K`).
  have hHK_normal : (subH.subgroupOf K).Normal := subH_normal.subgroupOf K
  -- (1.2) contrapositive: `χ(g) ≠ 0 ⟹ C_subH(g) ≠ 1`.
  have hCne : S03.centralizerInSubgroup (subH.subgroupOf K) g ≠ ⊥ := fun hbot =>
    hval (S03.irreducibleCharacter_apply_eq_zero_of_centralizerInSubgroup_eq_bot χ hker hbot)
  -- extract a nontrivial `c ∈ subH ∩ C_K(g)`.
  obtain ⟨c, hc_mem, hc_ne⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hCne
  rw [S03.mem_centralizerInSubgroup] at hc_mem
  obtain ⟨hc_H, hc_comm⟩ := hc_mem
  -- the images of `c` and `g` in `L`.
  set cL : ↥L := K.subtype c with hcL
  set gL : ↥L := K.subtype g with hgL
  have hcL_subH : cL ∈ subH := (Subgroup.mem_subgroupOf).mp hc_H
  have hcL_ne : cL ≠ 1 := fun he =>
    hc_ne (K.subtype_injective (he.trans (map_one K.subtype).symm))
  have hgL_K : gL ∈ K := g.2
  have hgL_ne : gL ≠ 1 := fun he => hg1 (by rw [he]; exact map_one L.subtype)
  -- `cL` and `gL` commute (image under the monoid hom `K.subtype` of `c * g = g * c`).
  have hcomm : cL * gL = gL * cL := by
    have := congrArg K.subtype hc_comm
    rwa [map_mul, map_mul] at this
  -- apply the covering condition (4.6.d).
  refine A_covers cL hcL_subH hcL_ne gL ?_ hgL_ne
  exact Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm, hgL_K⟩

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (4.7)**, core support statement.  Under Hypothesis (4.6), if
`χ ∈ Irr(K)` satisfies `H ⊄ Ker χ`, then every nonidentity `g ∈ K` with `χ(g) ≠ 0`
maps into `A` (i.e. `Supp χ ⊆ A ∪ {1}`).

The hypothesis `H ⊄ Ker χ` is phrased at the class-function level as
`¬ (H ⊆ characterKernel χ)`, matching Peterfalvi (1.2).  A thin specialization of the structural
`mem_A_of_apply_ne_zero_of_covers` to the `Hypothesis46` fields. -/
theorem mem_A_of_apply_ne_zero_of_not_subset_characterKernel
    (h : Hypothesis46Core A L)
    (χ : IrreducibleCharacter ↥h.K)
    (hker : ¬ ((h.subH.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (χ : ClassFunction ↥h.K ℂ)))
    {g : ↥h.K}
    (hg1 : L.subtype (h.K.subtype g) ≠ 1)
    (hval : (χ : ClassFunction ↥h.K ℂ) g ≠ 0) :
    L.subtype (h.K.subtype g) ∈ A :=
  mem_A_of_apply_ne_zero_of_covers h.K h.subH h.subH_normal h.A_covers χ hker hg1 hval

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (4.7)**, support form (`Supp χ ⊆ A ∪ {1}`).  Under Hypothesis (4.6),
an irreducible character `χ` of `K` with `H ⊄ Ker χ` vanishes at every `g ∈ K` whose
ambient image lies outside `A ∪ {1}`.

This is the contrapositive of `mem_A_of_apply_ne_zero_of_not_subset_characterKernel`,
phrased for downstream consumers (the induced-support half of (4.7) and (4.8)). -/
theorem apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
    (h : Hypothesis46Core A L)
    (χ : IrreducibleCharacter ↥h.K)
    (hker : ¬ ((h.subH.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (χ : ClassFunction ↥h.K ℂ)))
    {g : ↥h.K}
    (hgA : L.subtype (h.K.subtype g) ∉ A ∪ ({1} : Set G)) :
    (χ : ClassFunction ↥h.K ℂ) g = 0 := by
  by_contra hval
  rw [Set.mem_union, Set.mem_singleton_iff, not_or] at hgA
  exact hgA.1
    (mem_A_of_apply_ne_zero_of_not_subset_characterKernel h χ hker hgA.2 hval)

omit [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Peterfalvi (4.7)**, induced-character support (`Supp Ind_K^L χ ⊆ A ∪ {1}`).
Under Hypothesis (4.6), if `χ ∈ Irr(K)` has `H ⊄ Ker χ`, then the induced character
`Ind_K^L χ` vanishes at every `z ∈ L` whose ambient image lies outside `A ∪ {1}`.

Proof: a nonvanishing point `z` of `Ind_K^L χ` is `L`-conjugate to a point `w ∈ K` of
`Supp χ` (`support_induce_subset_conjugatesIntoSet`).  By the core support lemma the
ambient image of `w` is in `A ∪ {1}`; since `A` is closed under `L`-conjugation
(`L_normalizes_A`) and `z`, `w` are `L`-conjugate, the image of `z` is in `A ∪ {1}`. -/
theorem induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel
    (h : Hypothesis46Core A L) [Invertible (Nat.card ↥h.K : ℂ)]
    (χ : IrreducibleCharacter ↥h.K)
    (hker : ¬ ((h.subH.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (χ : ClassFunction ↥h.K ℂ)))
    {z : ↥L} (hz : L.subtype z ∉ A ∪ ({1} : Set G)) :
    ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ) z = 0 := by
  classical
  by_contra hnz
  -- `z` is `L`-conjugate into the support of `χ`.
  have hz_in : z ∈ ClassFunction.conjugatesIntoSet h.K ((χ : ClassFunction ↥h.K ℂ).support) :=
    ClassFunction.support_induce_subset_conjugatesIntoSet (subset_refl _) hnz
  rw [ClassFunction.mem_conjugatesIntoSet] at hz_in
  obtain ⟨x, hx, hxsupp⟩ := hz_in
  rw [Set.mem_union, Set.mem_singleton_iff, not_or] at hz
  obtain ⟨hzA, hz1⟩ := hz
  -- the `K`-element `w = x⁻¹ z x` and its `L`-image.
  have hKw : h.K.subtype (⟨x⁻¹ * z * x, hx⟩ : ↥h.K) = x⁻¹ * z * x := rfl
  have hconj : L.subtype z
      = L.subtype x * L.subtype (x⁻¹ * z * x) * (L.subtype x)⁻¹ := by
    rw [map_mul, map_mul, map_inv]; group
  have hw_val : (χ : ClassFunction ↥h.K ℂ) (⟨x⁻¹ * z * x, hx⟩ : ↥h.K) ≠ 0 :=
    Function.mem_support.mp hxsupp
  have hw_ne : L.subtype (h.K.subtype (⟨x⁻¹ * z * x, hx⟩ : ↥h.K)) ≠ 1 := by
    rw [hKw]; intro hw1; exact hz1 (by rw [hconj, hw1]; group)
  have hwA : L.subtype (h.K.subtype (⟨x⁻¹ * z * x, hx⟩ : ↥h.K)) ∈ A :=
    mem_A_of_apply_ne_zero_of_not_subset_characterKernel h χ hker hw_ne hw_val
  rw [hKw] at hwA
  exact hzA (by rw [hconj]; exact h.L_normalizes_A x hwA)

section ChiJ

open OddOrder.Peterfalvi.S05

variable {L₀ : Type*} [Group L₀] [Fintype L₀] [Invertible (Nat.card L₀ : ℂ)]

set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (4.7), `j ≥ 1` kernel step** (the `ω_{0j}` argument): for a nontrivial column
`χ₂ ≠ 1`, the certain-type restriction `χ_j = Res_K μ_{0j}` does **not** contain `W₂` in its
kernel.  Stated with `W₂` itself (the minimal kernel input); the (4.6.c) form `H ⊄ Ker χ_j`
follows by `W₂ ≤ H`. -/
theorem Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one
    (h : Hypothesis L₀) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    ¬ ((h.W2.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ)) := by
  intro hker
  apply hχ₂
  ext y
  rw [MonoidHom.one_apply]
  -- a nontrivial `x ∈ W₁`
  obtain ⟨x, hxW1, hx1⟩ :=
    (Subgroup.bot_or_exists_ne_one h.W1).resolve_left h.W1_nontrivial
  set μ₀ : IrreducibleCharacter L₀ := (h.columnFamily χ₂).mu 0 with hμ₀def
  -- `y` as an ambient element of `W₂`
  have hyW2 : ((y : ↥(h.W1 ⊔ h.W2)) : L₀) ∈ h.W2 := by
    have hy2 := y.2
    rwa [Subgroup.mem_subgroupOf] at hy2
  set yL : L₀ := ((y : ↥(h.W1 ⊔ h.W2)) : L₀) with hyLdef
  -- `yL ∈ Ker μ₀` through the restriction `χ_j = Res_K μ₀`
  have hyK : yL ∈ h.K := h.W2_le_K hyW2
  have hyker : yL ∈ S03.characterKernel (μ₀ : ClassFunction L₀ ℂ) := by
    have h1 := hker (Subgroup.mem_subgroupOf.mpr hyW2 :
      (⟨yL, hyK⟩ : ↥h.K) ∈ h.W2.subgroupOf h.K)
    rw [S03.mem_characterKernel, S03.characterDegree_def, coe_chiRestrict,
      ClassFunction.restrict_apply, ClassFunction.restrict_apply, OneMemClass.coe_one] at h1
    rw [S03.mem_characterKernel, S03.characterDegree_def]
    exact h1
  -- `x` and `x·y` lie in `V = W − W₂`
  have hxW : x ∈ h.W1 ⊔ h.W2 := (le_sup_left : h.W1 ≤ h.W1 ⊔ h.W2) hxW1
  have hyW : yL ∈ h.W1 ⊔ h.W2 := (le_sup_right : h.W2 ≤ h.W1 ⊔ h.W2) hyW2
  have hVdef : h.sdiffTICyclicHypothesis.V
      = ((h.W1 ⊔ h.W2 : Subgroup L₀) : Set L₀) \ (h.W2 : Set L₀) := rfl
  have hxV : x ∈ h.sdiffTICyclicHypothesis.V := by
    rw [hVdef]
    refine ⟨hxW, fun hxW2 => hx1 ?_⟩
    exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hxW1, hxW2⟩))
  have hvV : x * yL ∈ h.sdiffTICyclicHypothesis.V := by
    rw [hVdef]
    refine ⟨mul_mem hxW hyW, fun hvW2 => hx1 ?_⟩
    have hxW2 : x ∈ h.W2 := by
      have hxeq : x = (x * yL) * yL⁻¹ := by group
      rw [hxeq]
      exact mul_mem hvW2 (inv_mem hyW2)
    exact Subgroup.mem_bot.mp (h.W_disjoint.le_bot (Subgroup.mem_inf.mpr ⟨hxW1, hxW2⟩))
  -- (4.3.c) at `x·y` and at `x`, and kernel translation
  have hA := h.certainType_apply_eq_of_mem_V χ₂ 0 hvV
  have hB := h.certainType_apply_eq_of_mem_V χ₂ 0 hxV
  have hC : (μ₀ : ClassFunction L₀ ℂ) (x * yL) = (μ₀ : ClassFunction L₀ ℂ) x :=
    OddOrder.RepresentationTheory.apply_mul_eq_of_mem_characterKernel
      μ₀.isIrreducible hyker x
  -- the `ω_{0j}` values: `ω_{0j}(x·y) = χ₂(y)`, `ω_{0j}(x) = 1`
  have homega : ∀ (w : L₀) (hw : w ∈ h.sdiffTICyclicHypothesis.W),
      (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) ⟨w, hw⟩
        = ((χ₂ (h.sdiffTICyclicHypothesis.wSnd ⟨w, hw⟩) : ℂˣ) : ℂ) := by
    intro w hw
    rw [h.chiColumn_zero, TICyclicHypothesis.omega_apply,
      h.sdiffTICyclicHypothesis.omegaProdChar_one_left, MonoidHom.comp_apply]
    exact rfl
  -- assemble: `δ·χ₂(y) = μ₀(x·y) = μ₀(x) = δ·1`
  have hchain : ((h.columnFamily χ₂).sign : ℂ)
        * ((χ₂ (h.sdiffTICyclicHypothesis.wSnd
            ⟨x * yL, h.sdiffTICyclicHypothesis.V_subset_W hvV⟩) : ℂˣ) : ℂ)
      = ((h.columnFamily χ₂).sign : ℂ)
        * ((χ₂ (h.sdiffTICyclicHypothesis.wSnd
            ⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩) : ℂˣ) : ℂ) := by
    rw [← homega _ _, ← homega _ _, ← hA, ← hB]
    exact hC
  have hsign : ((h.columnFamily χ₂).sign : ℂ) ≠ 0 := by
    rcases (h.columnFamily χ₂).sign_eq with hs | hs <;> rw [hs] <;> norm_num
  have hval := mul_left_cancel₀ hsign hchain
  -- compute the two `wSnd` values (everything inside `↥sdiff.W` to keep `HMul` happy)
  have hyWs : yL ∈ h.sdiffTICyclicHypothesis.W := hyW
  have hy'mem : (⟨yL, hyWs⟩ : ↥h.sdiffTICyclicHypothesis.W)
      ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W :=
    Subgroup.mem_subgroupOf.mpr hyW2
  have hsplit : (⟨x * yL, h.sdiffTICyclicHypothesis.V_subset_W hvV⟩ :
        ↥h.sdiffTICyclicHypothesis.W)
      = (⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ : ↥h.sdiffTICyclicHypothesis.W)
        * (⟨yL, hyWs⟩ : ↥h.sdiffTICyclicHypothesis.W) := rfl
  have hxmem : (⟨x, h.sdiffTICyclicHypothesis.V_subset_W hxV⟩ :
        ↥h.sdiffTICyclicHypothesis.W)
      ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
    Subgroup.mem_subgroupOf.mpr hxW1
  have hysnd : h.sdiffTICyclicHypothesis.wSnd (⟨yL, hyWs⟩ : ↥h.sdiffTICyclicHypothesis.W)
      = (⟨⟨yL, hyWs⟩, hy'mem⟩ :
          ↥(h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W)) :=
    h.sdiffTICyclicHypothesis.wSnd_W2_subtype ⟨⟨yL, hyWs⟩, hy'mem⟩
  have hy'eq : (⟨⟨yL, hyWs⟩, hy'mem⟩ :
        ↥(h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W)) = y := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [hsplit, map_mul, h.sdiffTICyclicHypothesis.wSnd_eq_one_of_mem_W1 hxmem,
    hysnd, hy'eq, one_mul] at hval
  -- retype the `(1 : sdiff-form)` inside `hval` to the `h`-form (definitionally equal)
  have hval' : ((χ₂ y : ℂˣ) : ℂ)
      = ((χ₂ (1 : ↥(h.W2.subgroupOf (h.W1 ⊔ h.W2))) : ℂˣ) : ℂ) := hval
  rw [map_one] at hval'
  exact hval'

/-- **The trivial column `χ₂ = 1` gives `χ_0 = 1_K`** (Peterfalvi (4.4) anchor): `chiRestrict 1 =
Res^L_K μ_{00} = Res^L_K 1_L = 1_K` (`certainType_zero_column_anchor`).  This is the unique
reducible induction whose kernel contains every `H ≤ K`; it is the `j = 0` column removed by the
`H`-nontriviality of (9.9.b). -/
theorem Hypothesis.chiRestrict_one_eq_trivial
    (h : Hypothesis L₀) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] :
    h.chiRestrict 1 = trivialIrreducibleCharacter ↥h.K := by
  apply IrreducibleCharacter.ext
  rw [coe_chiRestrict, h.certainType_zero_column_anchor.2]
  simp

/-- **Peterfalvi (4.5.b) + (4.7), `H`-nontrivial reducible-induction count**: for a subgroup `H ≤ K`
containing `W₂` (the (4.6.c) covering condition), exactly `w₂ − 1` of the irreducible characters
`χ ∈ Irr(K)` induce a *reducible* character of `L` with `H ⊄ Ker χ` — the `μ_j`, `1 ≤ j < w₂`.

The `w₂` reducible inductions biject with the columns `Ŵ₂` (`card_reducible_induce_eq_W2`,
`induce_not_isIrreducible_iff`).  The trivial column `χ₂ = 1` gives `χ_0 = 1_K`
(`chiRestrict_one_eq_trivial`), whose kernel is all of `K ⊇ H`; every nontrivial column `χ₂ ≠ 1`
gives `W₂ ⊄ Ker χ_j` ((4.7), `not_subset_characterKernel_chiRestrict_of_ne_one`), hence
`H ⊄ Ker χ_j`.  Removing the one trivial column leaves `w₂ − 1`.  This is the count behind
Peterfalvi (9.9.b)/(9.8.b) (with `w₂ = p` and `H = H̄` after the (8.4.d) realization of `𝒮(H₀)`
as the `M/H₀`-induction family). -/
theorem Hypothesis.card_reducible_Hnontrivial_induce_eq_W2_sub_one
    (h : Hypothesis L₀) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {H : Subgroup ↥h.K} (hW2H : h.W2.subgroupOf h.K ≤ H) :
    Nat.card {χ : IrreducibleCharacter ↥h.K //
        ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ))
        ∧ ¬ ((H : Set ↥h.K) ⊆ S03.characterKernel (χ : ClassFunction ↥h.K ℂ))}
      = Nat.card h.W2 - 1 := by
  classical
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite ↥(h.W1 ⊔ h.W2)
  have : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  -- the forward map sends a nontrivial column `χ₂` to its reducible, `H`-nontrivial `χ_j`
  have hfwd : ∀ p : {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₂ ≠ 1},
      ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (h.chiRestrict p.1 : ClassFunction ↥h.K ℂ))
        ∧ ¬ ((H : Set ↥h.K) ⊆
            S03.characterKernel (h.chiRestrict p.1 : ClassFunction ↥h.K ℂ)) := by
    rintro ⟨χ₂, hχ₂⟩
    refine ⟨h.induce_chiRestrict_not_isIrreducible χ₂, fun hHker => ?_⟩
    exact h.not_subset_characterKernel_chiRestrict_of_ne_one hχ₂
      (Set.Subset.trans (SetLike.coe_subset_coe.mpr hW2H) hHker)
  -- bijection of the `H`-nontrivial reducibles with the nontrivial columns `Ŵ₂ ∖ {1}`
  have hcard : Nat.card {χ : IrreducibleCharacter ↥h.K //
        ¬ IsIrreducibleCharacter (ClassFunction.induce h.K (χ : ClassFunction ↥h.K ℂ))
        ∧ ¬ ((H : Set ↥h.K) ⊆ S03.characterKernel (χ : ClassFunction ↥h.K ℂ))}
      = Nat.card {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ // χ₂ ≠ 1} := by
    refine (Nat.card_congr (Equiv.ofBijective (fun p => ⟨h.chiRestrict p.1, hfwd p⟩) ⟨?_, ?_⟩)).symm
    · rintro ⟨a, ha⟩ ⟨b, hb⟩ hab
      exact Subtype.ext (h.chiRestrict_injective (Subtype.ext_iff.mp hab))
    · rintro ⟨χ, hred, hHnt⟩
      obtain ⟨χ₂, hχ₂⟩ := (h.induce_not_isIrreducible_iff χ).mp hred
      refine ⟨⟨χ₂, ?_⟩, Subtype.ext hχ₂⟩
      rintro rfl
      refine hHnt ?_
      rw [← hχ₂, h.chiRestrict_one_eq_trivial, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        S03.characterKernel_trivialClassFunction]
      exact Set.subset_univ _
  -- `|Ŵ₂ ∖ {1}| = |Ŵ₂| − 1 = w₂ − 1`
  rw [hcard, Nat.card_eq_fintype_card]
  simp only [ne_eq]
  rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card,
    h.card_charGroup_W2]

end ChiJ

omit [Invertible (Nat.card G : ℂ)] in
/-- **Peterfalvi (4.7), `j ≥ 1` kernel statement** in the Hypothesis (4.6) form: for a nontrivial
column `χ₂ ≠ 1`, `H ⊄ Ker χ_j` (`H` the (4.6.c) normal subgroup, `W₂ ≤ H`). -/
theorem not_subset_characterKernel_chiRestrict
    (h : Hypothesis46Core A L) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    ¬ ((h.subH.subgroupOf h.K : Set ↥h.K) ⊆
      S03.characterKernel (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ)) := by
  intro hker
  refine Hypothesis.not_subset_characterKernel_chiRestrict_of_ne_one
    h.toHypothesis hχ₂ ?_
  intro k hk
  refine hker ?_
  have hkW2 := Subgroup.mem_subgroupOf.mp hk
  exact Subgroup.mem_subgroupOf.mpr (h.W2_le_subH hkW2)

/-- **`χ_j ≠ 1_K`** (Peterfalvi (4.7), nontriviality of the certain-type restriction): for a
nontrivial column `χ₂ ≠ 1`, the irreducible restriction `χ_j = Res_K μ_{0j}` is **not** the trivial
character of `K`.  Were it trivial, its kernel would be all of `↥K`, in particular containing
`H.subgroupOf K`, contradicting `not_subset_characterKernel_chiRestrict`.

This is the `S`-membership input for the (6.8) case-(B) `X`-coherence: it certifies that the column
character `μ_j = Ind_K^L χ_j` is induced from a *nontrivial* irreducible of `K = H`, hence lies in
the Sibley set `S = {Ind_H^L θ | θ ≠ 1}`. -/
theorem chiRestrict_ne_trivialIrreducibleCharacter
    (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) :
    h.chiRestrict χ₂ ≠ trivialIrreducibleCharacter ↥h.K := by
  intro htriv
  refine not_subset_characterKernel_chiRestrict h.toCore hχ₂ ?_
  rw [htriv, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
    S03.characterKernel_trivialClassFunction]
  exact Set.subset_univ _

omit [Invertible (Nat.card G : ℂ)] in
/-- **Peterfalvi (4.7), `j ≥ 1` support**: `Supp χ_j ⊆ A ∪ {1}` for a nontrivial column
`χ₂ ≠ 1`. -/
theorem chiRestrict_apply_eq_zero_of_not_mem_union
    (h : Hypothesis46Core A L) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {g : ↥h.K} (hgA : L.subtype (h.K.subtype g) ∉ A ∪ ({1} : Set G)) :
    (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ) g = 0 :=
  apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel h (h.chiRestrict χ₂)
    (not_subset_characterKernel_chiRestrict h hχ₂) hgA

omit [Invertible (Nat.card G : ℂ)] in
/-- **Peterfalvi (4.7), `j ≥ 1` induced support**: `Supp μ_j ⊆ A ∪ {1}` for a nontrivial column
`χ₂ ≠ 1` (`μ_j = Ind_K^L χ_j = ∑_i μ_{ij}` by (4.5.a) `induce_restrict_certainType_eq`). -/
theorem induce_chiRestrict_apply_eq_zero_of_not_mem_union
    (h : Hypothesis46Core A L) [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {z : ↥L} (hz : L.subtype z ∉ A ∪ ({1} : Set G)) :
    ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ) z = 0 :=
  induce_apply_eq_zero_of_not_mem_union_of_not_subset_characterKernel h (h.chiRestrict χ₂)
    (not_subset_characterKernel_chiRestrict h hχ₂) hz

end OddOrder.Peterfalvi.S06


