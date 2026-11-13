-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBXChiCoherence
-- name    : OddOrder_Peterfalvi_S08_CaseBXChiCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:18:51.289547+00:00
-- url     : https://prove2.me/theorems/cf400123-07a1-452a-b5cc-0979f07a48f9
-- title:
--   Peterfalvi §8 case (B): the textbook $X$-coherence on the certain-type columns
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, (6.8.2). This file builds the textbook $X$-coherence on the certain-type column set, whose extension sends each column $\mu_j$ to its own (6.8.2.3) projection image.
--
--   Main definitions: `xChiExtensionFun` (the basis rule) and `xChiExtension` (the textbook $X_\chi$-extension $\nu$, the case-(B) $\tau_2$ on the certain-type columns), with evaluation lemmas `xChiExtension_mu_zero`, `xChiExtension_mu_ne_zero` and `xChiExtension_columnSum`.
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBXChiCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBXChiCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

open scoped Classical in
/-- **The basis rule for the textbook `X_χ`-extension.**  Sends the `0`-th-row certain-type
irreducible `μ_{0,χ₂}` of each column to that column's target image `Ximg χ₂`, and every other
irreducible to `0`.  The witness column `χ₂` is selected uniquely by `columnFamily_mu_injective`
(the grid `(χ₂, i) ↦ μ_{ij}` is injective, so `μ_{0,χ₂}` determines `χ₂`).

The "all on the `0`-th row" choice is one of many splittings of the column image `Ximg χ₂` across
the
`w₁` constituents `{μ_{ij}}`; any splitting yields the same value on the column sum
`μ_j = ∑_i μ_{ij}`,
and the coherence fields only see column-level values. -/
noncomputable def xChiExtensionFun
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ) :
    IrreducibleCharacter ↥L → ClassFunction G ℂ :=
  fun ω =>
    if hex : ∃ p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1),
        (h46.columnFamily p.1).mu p.2 = ω ∧ p.2 = 0 then Ximg hex.choose.1 else 0

/-- **The textbook `X_χ`-extension** `ν` (the case-(B) `τ₂` on the certain-type columns): the global
`ℤ`-linear `CF(L) → CF(G)` built from `xChiExtensionFun` on the basis `Irr(L)`. -/
noncomputable def xChiExtension
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ) :
    OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G :=
  ((OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr ℂ
    (xChiExtensionFun h46 Ximg)).restrictScalars ℤ

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- The `X_χ`-extension on the `0`-th-row certain-type irreducible: `ν(μ_{0,χ₂}) = Ximg χ₂`. -/
theorem xChiExtension_mu_zero
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    xChiExtension h46 Ximg ((h46.columnFamily χ₂).mu 0 : ClassFunction ↥L ℂ) = Ximg χ₂ := by
  classical
  rw [xChiExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu 0)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu 0), xChiExtensionFun]
  have hex : ∃ p : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) × Fin (Nat.card h46.W1),
      (h46.columnFamily p.1).mu p.2 = (h46.columnFamily χ₂).mu 0 ∧ p.2 = 0 := ⟨(χ₂, 0), rfl, rfl⟩
  rw [dif_pos hex]
  have hchoose : hex.choose = (χ₂, 0) := h46.columnFamily_mu_injective hex.choose_spec.1
  rw [hchoose]

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- The `X_χ`-extension on a higher-row certain-type irreducible: `ν(μ_{iχ₂}) = 0` for `i ≠ 0`. -/
theorem xChiExtension_mu_ne_zero
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) {i : Fin (Nat.card h46.W1)} (hi : i ≠ 0) :
    xChiExtension h46 Ximg ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) = 0 := by
  classical
  rw [xChiExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← OddOrder.Peterfalvi.S05.irreducibleCharacterBasis_apply (G := ↥L)
    ((h46.columnFamily χ₂).mu i)]
  rw [(OddOrder.Peterfalvi.S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _
    ((h46.columnFamily χ₂).mu i), xChiExtensionFun, dif_neg]
  rintro ⟨p, heq, hp2⟩
  have hpair : p = (χ₂, i) := h46.columnFamily_mu_injective heq
  rw [hpair] at hp2
  exact hi hp2

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **The `X_χ`-extension on a column sum**: `ν(μ_j) = ν(∑_i μ_{ij}) = Ximg χ₂`.  Only the
`0`-th-row
term survives (`xChiExtension_mu_zero`/`xChiExtension_mu_ne_zero`). -/
theorem xChiExtension_columnSum
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) [NeZero (Nat.card h46.W1)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    (Ximg : ((h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) → ClassFunction G ℂ)
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    xChiExtension h46 Ximg (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = Ximg χ₂ := by
  classical
  rw [OddOrder.Peterfalvi.S06.columnSum_def, map_sum,
    Finset.sum_eq_single (0 : Fin (Nat.card h46.W1))]
  · exact xChiExtension_mu_zero h46 Ximg χ₂
  · intro i _ hi; exact xChiExtension_mu_ne_zero h46 Ximg χ₂ hi
  · intro h0; exact absurd (Finset.mem_univ _) h0

/-- **A `(5.4)` decomposition's `X`-part is a virtual character** (`D.X ∈ ℤ[Irr G]`).  Generic
brick discharging the `hXzirr` obligation of the textbook `X_χ`-coherence:
`X = ∑_{α ∈ R(χ)} coeff α • α`
(`X_eq`) is a `ℤ`-combination of the orthonormal image-family members `α ∈ ZIrr G`
(`imageFamily.mem_ZIrr`).  For the column decomposition `columnDecompositionTau`, `imageFamily =
columnRFamilyTau` (`imageSet = certainTypeR.imageSet`, the signed `σ`-images), so its `X` lands in
`ZIrr G`. -/
theorem characterPsiDecomposition_X_mem_ZIrr
    {τ : OddOrder.Peterfalvi.S07.IntegralCharacterMap ↥L G} {χ ψ : ClassFunction ↥L ℂ}
    (D : OddOrder.Peterfalvi.S07.CharacterPsiDecomposition τ χ ψ) : D.X ∈ ZIrr G := by
  rw [D.X_eq]
  exact Submodule.sum_mem _ (fun α hα => by
    rw [Int.cast_smul_eq_zsmul ℂ (D.coeff α) α]
    exact Submodule.smul_mem _ (D.coeff α) (D.imageFamily.mem_ZIrr α hα))

end OddOrder.Peterfalvi.S08


