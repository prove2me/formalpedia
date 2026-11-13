-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence
-- name    : OddOrder_Peterfalvi_S08_CaseBCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:58:58.852216+00:00
-- url     : https://prove2.me/theorems/8f18af31-25e6-4fbc-913d-5e2351703f63
-- title:
--   Peterfalvi §8: case (B) coherence ($X\cup Y$ is coherent in case (B))
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, the (6.8.2) branch of the (6.8) coherence capstone: the case-(B) ($Z=W_2$, $W_2$ prime central) analogue of the case-(A)/Frobenius central-commutator program, showing $X\cup Y$ is coherent.
--
--   Main results: `coeff_eq_neg_or_edge_caseB` (the (6.8.2.2) coefficient dichotomy), `inner_tau_indW2_extension_Yset_eq_neg_caseB` (the good case for $|Y|\ge 3$) and `exists_Ycoherence_hgood_uniform_caseB` (uniform good-value $Y$-coherence), plus central-subgroup facts such as `inner_self_induce_eq_index_of_le_center`.
--
--   The bundle also proves 7 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBCoherence_CentralCongruence

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.2) norm preservation `‖α^τ‖² = ‖α‖²`** for `α = Ind^L_{W₂}φ − c·η₁` (`α(1) = 0`).
Since
`Supp(α) ⊆ H^#` (`support_indW2_sub_smul_subset_sharpImage`), the Dade isometry on the supported
singleton `{α}` (`dadeIntegralCharacterMap_inner_eq_on_supported_span`) gives
`⟨α^τ, α^τ⟩ = ⟨α, α⟩`.  This is the source of the norm bound `‖α^τ‖² = ‖α‖² = |L:Z| + |H:Z|²` in the
(6.8.2.2) trichotomy endgame (Peterfalvi (1.5.b)). -/
theorem SibleyDadeHypothesis.inner_self_tau_indW2_sub_smul
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 φ - c • η₁))
        (hyp.tau (ClassFunction.induce W2 φ - c • η₁))
      = ClassFunction.inner (ClassFunction.induce W2 φ - c • η₁)
        (ClassFunction.induce W2 φ - c • η₁) := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hsupp : (ClassFunction.induce W2 φ - c • η₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ c h1
  exact OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade
    (S := {ClassFunction.induce W2 φ - c • η₁})
    (by intro s hs; rw [Set.mem_singleton_iff] at hs; rw [hs]; exact hsupp)
    (Submodule.subset_span rfl) (Submodule.subset_span rfl)

/-- **(6.8.2.2) source cross-term `⟨Ind_{W₂}φ, η' − η⟩ = 0`** for `η, η' ∈ Y`.  Every `η ∈ Y` is
constant on `⁅H,H⁆ ⊇ W₂` (`Yset_apply_eq_apply_one_of_mem_commutator`) with value `η(1) = |W₁|`
(`Yset_apply_one`), so `Res^L_{W₂}η' = Res^L_{W₂}η` (both the constant `|W₁|` on `W₂`).  Frobenius
reciprocity `inner_induce_eq_inner_restrict` then gives
`⟨Ind_{W₂}φ, η'⟩ = ⟨φ, Res_{W₂}η'⟩ = ⟨φ, Res_{W₂}η⟩ = ⟨Ind_{W₂}φ, η⟩`, hence the difference is `0`.

This is the source half of the (6.8.2.2) cross-term `⟨α^τ, η_j^{τ₁} − η_1^{τ₁}⟩ = |H:Z|`: with
`⟨η₁, η_j − η_1⟩ = −1` it gives `⟨α, η_j − η_1⟩ = |H:Z|`. -/
theorem SibleyDadeHypothesis.inner_induce_W2_Yset_diff_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)] (hW2comm : W2 ≤ ⁅H, H⁆)
    (φ : ClassFunction ↥W2 ℂ) {η η' : ClassFunction ↥L ℂ}
    (hη : η ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) :
    ClassFunction.inner (ClassFunction.induce W2 φ) (η' - η) = 0 := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hRes : ClassFunction.restrict W2 η' = ClassFunction.restrict W2 η := by
    ext w
    have hmem : (↑w : ↥L) ∈ ⁅H, H⁆ := hW2comm (SetLike.coe_mem w)
    simp only [ClassFunction.restrict_apply]
    rw [hyp.Yset_apply_eq_apply_one_of_mem_commutator hη' hmem,
      hyp.Yset_apply_eq_apply_one_of_mem_commutator hη hmem,
      hyp.Yset_apply_one hη', hyp.Yset_apply_one hη]
  rw [ClassFunction.inner_sub_right, ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_induce_eq_inner_restrict, hRes, sub_self]

/-- **(6.8.2.2) cross-term `⟨α^τ, (η' − η₁)^τ⟩ = c`** for `α = Ind^L_{W₂}φ − c·η₁` and `η', η₁ ∈ Y`,
`η' ≠ η₁`.  By the Dade isometry on the supported pair `{α, η' − η₁}`
(`dadeIntegralCharacterMap_inner_eq_on_supported_span`; both supported on `H^#` via
`support_indW2_sub_smul_subset_sharpImage` / `sMember_diffSupport_of_charValue_eq`) it reduces to
the
source inner product `⟨α, η' − η₁⟩`, which expands to
`⟨Ind_{W₂}φ, η' − η₁⟩ − c·⟨η₁, η' − η₁⟩ = 0 − c·(0 − 1) = c` using the source orthogonality
`inner_induce_W2_Yset_diff_eq_zero` and the `Y`-orthonormality (the inner product is linear in its
first argument).

This is the (6.8.2.2) `j > 1` value `⟨α^τ, η_j^{τ₁} − η_1^{τ₁}⟩ = |H:Z|` in `τ`-form (the coherence
agreement `extension = τ` on the supported lattice converts `(η' − η₁)^τ` to `η'^{τ₁} − η₁^{τ₁}`),
with `c = (|H:W₂| : ℂ)`. -/
theorem SibleyDadeHypothesis.inner_tau_indW2_sub_smul_tau_Yset_diff
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) (hW2comm : W2 ≤ ⁅H, H⁆)
    [Invertible (Nat.card ↥W2 : ℂ)]
    (φ : ClassFunction ↥W2 ℂ) {η₁ η' : ClassFunction ↥L ℂ}
    (hη₁ : η₁ ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) (hne : η' ≠ η₁) (c : ℂ)
    (h1 : ClassFunction.induce W2 φ (1 : ↥L) = c * η₁ (1 : ↥L)) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 φ - c • η₁))
        (hyp.tau (η' - η₁)) = c := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hYirr : ∀ ψ ∈ hyp.Yset, IsIrreducibleCharacter ψ :=
    fun ψ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite (⟨ψ, hYirr ψ hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hYirr ψ' hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hsuppα : (ClassFunction.induce W2 φ - c • η₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.support_indW2_sub_smul_subset_sharpImage hW2H φ hη₁ c h1
  have hsuppY : (η' - η₁).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη₁)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη₁).symm)
  have hiso := OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_inner_eq_on_supported_span
    hyp.dade
    (S := ({ClassFunction.induce W2 φ - c • η₁, η' - η₁} : Set (ClassFunction ↥L ℂ)))
    (by intro s hs
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
        rcases hs with rfl | rfl
        · exact hsuppα
        · exact hsuppY)
    (Submodule.subset_span (Set.mem_insert _ _))
    (Submodule.subset_span (Set.mem_insert_of_mem _ rfl))
  rw [hiso, ClassFunction.inner_sub_left,
    hyp.inner_induce_W2_Yset_diff_eq_zero hW2comm φ hη₁ hη',
    ClassFunction.inner_smul_left, ClassFunction.inner_sub_right,
    hYon η₁ η' hη₁ hη', hYon η₁ η₁ hη₁ hη₁, if_neg (Ne.symm hne), if_pos rfl]
  ring

/-- **(6.8.2.1) coherence agreement `η'^{τ₁} − η₁^{τ₁} = (η' − η₁)^τ`** for `η₁, η' ∈ Y`.  The
`Y`-coherence extension `ν = ·^{τ₁}` agrees with the Dade map `τ` on the supported lattice
`zSupportedSpan Y H^#` (`IsCoherent.extends_on_supported`), and the equal-degree difference
`η' − η₁` lies there (`zSpan` membership + `sMember_diffSupport_of_charValue_eq` support).  Combined
with linearity (`map_sub`), `extension η' − extension η₁ = extension (η' − η₁) = τ (η' − η₁)`.

This converts the `τ`-form cross-term `inner_tau_indW2_sub_smul_tau_Yset_diff` into the
`𝒴^{τ₁}`-extension form used in the (6.8.2.2) decomposition `α^τ = X − |H:Z|η_1^{τ₁} + …`. -/
theorem SibleyDadeHypothesis.coherentYset_extension_Yset_diff_eq_tau
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {η₁ η' : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (hη' : η' ∈ hyp.Yset) :
    hyp.coherentYset.extension η' - hyp.coherentYset.extension η₁ = hyp.tau (η' - η₁) := by
  have hmem : (η' - η₁) ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ (Submodule.subset_span hη') (Submodule.subset_span hη₁), ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη') (hyp.Yset_subset_S hη₁)
      ((hyp.Yset_apply_one hη').trans (hyp.Yset_apply_one hη₁).symm)
  rw [← map_sub]
  exact hyp.coherentYset.extends_on_supported (η' - η₁) hmem

omit [Fintype G] [Fintype ↥L] [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)] in
/-- **Inertia of a class function on a central subgroup is everything.**  If `W₂ ≤ Z(↥L)` (so `W₂`
is
normal), conjugation by any `g ∈ ↥L` fixes each `w ∈ W₂` (`g·w·g⁻¹ = w`, centrality), hence
`conjBy g φ = φ` for every class function `φ` of `W₂`, i.e. `I_{↥L}(φ) = ⊤`.

In (6.8.2.2) this gives `‖Ind^L_{W₂}φ‖² = |L:W₂|` via
`card_mul_inner_self_induce_eq_card_inertia` (`|W₂|·‖Ind φ‖² = |I_L(φ)| = |L|`). -/
theorem inertia_eq_top_of_le_center
    {W2 : Subgroup ↥L} [W2.Normal] (hW2cen : W2 ≤ Subgroup.center ↥L)
    (φ : ClassFunction ↥W2 ℂ) :
    ClassFunction.inertia φ = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  rw [ClassFunction.mem_inertia]
  ext w
  rw [ClassFunction.conjBy_apply]
  have hval : g * (w : ↥L) * g⁻¹ = (w : ↥L) := by
    rw [Subgroup.mem_center_iff.mp (hW2cen w.2) g]
    exact mul_inv_cancel_right _ _
  exact congrArg (⇑φ) (Subtype.ext hval)

omit [Fintype G] [Invertible (Nat.card G : ℂ)] in
/-- **Norm of an induced character from a central subgroup: `‖Ind^L_{W₂}φ‖² = |L:W₂|`** for `φ` an
irreducible (linear) character of `W₂ ≤ Z(↥L)`.  By `card_mul_inner_self_induce_eq_card_inertia`,
`|W₂|·‖Ind^L_{W₂}φ‖² = |I_{↥L}(φ)|`, and `I_{↥L}(φ) = ⊤` (`inertia_eq_top_of_le_center`), so the
right side is `|↥L|`; cancelling `|W₂|` and using `|↥L| = |W₂|·[L:W₂]` (`card_mul_index`) gives
`‖Ind φ‖² = [L:W₂] = W₂.index`.

This is the `|I_L(φ):Z| = |L:Z|` term of the (6.8.2.2) norm `‖α‖² = |L:Z| + |H:Z|²`. -/
theorem inner_self_induce_eq_index_of_le_center
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    (φ : IrreducibleCharacter ↥W2) :
    ClassFunction.inner (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ))
        (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)) = (W2.index : ℂ) := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hcard := card_mul_inner_self_induce_eq_card_inertia φ
  rw [inertia_eq_top_of_le_center hW2cen (φ : ClassFunction ↥W2 ℂ), Subgroup.card_top] at hcard
  have hLeq : (Nat.card ↥L : ℂ) = (Nat.card ↥W2 : ℂ) * (W2.index : ℂ) := by
    rw [← Subgroup.card_mul_index W2]; push_cast; ring
  rw [hLeq] at hcard
  have hW2ne : (Nat.card ↥W2 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  exact mul_left_cancel₀ hW2ne hcard

/-- **(6.8.2.2) single cross-term `⟨Ind_{W₂}φ, η⟩ = 0`** for a *nontrivial* `φ ∈ Irr W₂` and
`η ∈ Y`.
By Frobenius reciprocity `⟨Ind_{W₂}φ, η⟩ = ⟨φ, Res^L_{W₂}η⟩`, and `Res^L_{W₂}η` is the constant
`|W₁|`
on `W₂` (each `η ∈ Y` is constant `η(1) = |W₁|` on `⁅H,H⁆ ⊇ W₂`,
`Yset_apply_eq_apply_one_of_mem_commutator` + `Yset_apply_one`); the inner product then factors as
`|W₂|⁻¹·(∑_{w} φ(w))·\overline{|W₁|} = 0` since `∑_w φ(w) = 0` for the nontrivial `φ`
(`sum_apply_eq_zero_of_ne_trivial`).

This is the cross term of the (6.8.2.2) norm `‖α‖² = ‖Ind_{W₂}φ‖² + |H:Z|²`
(`⟨Ind_{W₂}φ, η₁⟩ = 0`). -/
theorem SibleyDadeHypothesis.inner_induce_W2_Yset_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)] (hW2comm : W2 ≤ ⁅H, H⁆)
    (φ : IrreducibleCharacter ↥W2) (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)) η = 0 := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  rw [ClassFunction.inner_induce_eq_inner_restrict,
    ClassFunction.inner_eq_inv_card_mul_innerSum, ClassFunction.innerSum]
  have hconst : ∀ w : ↥W2, ClassFunction.restrict W2 η w = (Nat.card hyp.W1 : ℂ) := by
    intro w
    rw [ClassFunction.restrict_apply,
      hyp.Yset_apply_eq_apply_one_of_mem_commutator hη (hW2comm (SetLike.coe_mem w)),
      hyp.Yset_apply_one hη]
  simp only [hconst]
  rw [← Finset.sum_mul, sum_apply_eq_zero_of_ne_trivial hφ, zero_mul, mul_zero]

/-- **(6.8.2.2) source norm `‖α‖² = |L:W₂| + c·c̄`** for `α = Ind^L_{W₂}φ − c·η₁` (`φ` nontrivial
linear, `η₁ ∈ Y`, `W₂ ≤ Z(↥L)`).  Expanding the inner product and using `‖Ind_{W₂}φ‖² = |L:W₂|`
(`inner_self_induce_eq_index_of_le_center`), the vanishing cross terms `⟨Ind_{W₂}φ, η₁⟩ = 0`
(`inner_induce_W2_Yset_eq_zero`, and its conjugate), and `‖η₁‖² = 1` (irreducibility):
`‖α‖² = |L:W₂| + c·c̄`.

For the assembly coefficient `c = (|H:W₂| : ℂ)` (real), `c·c̄ = |H:W₂|²`, giving Peterfalvi's
`‖α‖² = |L:Z| + |H:Z|²`. Combined with `inner_self_tau_indW2_sub_smul` (`‖α^τ‖² = ‖α‖²`), this is
the
norm input to the (6.8.2.2) trichotomy. -/
theorem SibleyDadeHypothesis.inner_self_indW2_sub_smul_eq
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hW2comm : W2 ≤ ⁅H, H⁆) (hW2cen : W2 ≤ Subgroup.center ↥L)
    (φ : IrreducibleCharacter ↥W2) (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset) (c : ℂ) :
    ClassFunction.inner (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) - c • η₁)
        (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) - c • η₁)
      = (W2.index : ℂ) + c * star c := by
  have hIndnorm := inner_self_induce_eq_index_of_le_center hW2cen φ
  have hcross := hyp.inner_induce_W2_Yset_eq_zero hW2comm φ hφ hη₁
  have hcross' : ClassFunction.inner η₁ (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ))
      = 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm, hcross, star_zero]
  have hη₁n : ClassFunction.inner η₁ η₁ = 1 := by
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η₁, hyp.isIrreducibleCharacter_of_mem_Yset hη₁⟩ : IrreducibleCharacter ↥L)
      (⟨η₁, hyp.isIrreducibleCharacter_of_mem_Yset hη₁⟩ : IrreducibleCharacter ↥L)
    simpa using h
  simp only [ClassFunction.inner_sub_left, ClassFunction.inner_sub_right,
    ClassFunction.inner_smul_left, OddOrder.RepresentationTheory.inner_smul_right]
  rw [hIndnorm, hcross, hcross', hη₁n]
  ring

open scoped Classical in
/-- **(6.8.2.2) coefficient dichotomy** (the case-(B) analogue of
`coeff_eq_neg_or_edge_of_frobenius`).
For `α = Ind^L_{W₂}φ − |H:Z|·η₁` (`φ` nontrivial linear, `η₁ ∈ Y`), the multiplicity
`⟨α^τ, η₁^{τ₁}⟩` is either `−|H:Z|` or (when `|Y| = 2`) `0`.

Following Peterfalvi (6.8.2.2): set `bb = ⟨α^τ, η₁^{τ₁}⟩ ∈ ℤ` with `|H:Z| ∣ bb`
(`inner_tau_alpha_dvd_index`); for `η ≠ η₁`, `⟨α^τ, η^{τ₁}⟩ = bb + |H:Z|` (cross-term
`inner_tau_indW2_sub_smul_tau_Yset_diff` + agreement `coherentYset_extension_Yset_diff_eq_tau`).
Bessel's inequality over the orthonormal `𝒴^{τ₁}` (`sum_sq_le_inner_self_re`) with the norm
`‖α^τ‖² = |L:Z| + |H:Z|²` (`inner_self_tau_indW2_sub_smul` ∘ `inner_self_indW2_sub_smul_eq`) gives
`bb² + (m−1)(bb+|H:Z|)² ≤ |L:Z| + |H:Z|²`; with the fixed-point-free bound `|L:Z| < |H:Z|²`
(`hFPF`) this is `< 2|H:Z|²`, and `eq_zero_or_edge_of_dvd_of_normLt` forces `bb ∈ {−|H:Z|, 0}`.

`hc2` (`2 ≤ |H:Z|`) and `hFPF` (`|L:Z| < |H:Z|²`) are the deferred `W₁`-FPF-on-`H/W₂` inputs. -/
theorem SibleyDadeHypothesis.coeff_eq_neg_or_edge_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁)
        = -((W2.subgroupOf H).index : ℂ)
      ∨ (hyp.Yset.ncard = 2 ∧
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁) = 0) := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have h1 : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
      = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  obtain ⟨bb, hbb, habb⟩ :=
    hyp.inner_tau_alpha_dvd_index hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hη₁
  have hYon : ∀ ψ ψ' : ClassFunction ↥L ℂ, ψ ∈ hyp.Yset → ψ' ∈ hyp.Yset →
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ ψ' hψ hψ'
    have h := irreducibleCharacter_inner_eq_ite
      (⟨ψ, hyp.isIrreducibleCharacter_of_mem_Yset hψ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ', hyp.isIrreducibleCharacter_of_mem_Yset hψ'⟩ : IrreducibleCharacter ↥L)
    simpa using h
  have hEinj : ∀ η ∈ hyp.Yset, ∀ η' ∈ hyp.Yset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' := by
    intro η hη η' hη' heq
    by_contra hne
    have h0 : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 0 := by
      rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span hη)
        (Submodule.subset_span hη'), hYon η η' hη hη', if_neg hne]
    have h1' : ClassFunction.inner (hyp.coherentYset.extension η)
        (hyp.coherentYset.extension η') = 1 := by
      rw [heq, hyp.coherentYset.extension_inner_eq η' η' (Submodule.subset_span hη')
        (Submodule.subset_span hη'), hYon η' η' hη' hη', if_pos rfl]
    rw [h1'] at h0; exact one_ne_zero h0
  have hcoeff : ∀ η ∈ hyp.Yset,
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η)
        = ((if η = η₁ then bb else bb + (W2.subgroupOf H).index : ℤ) : ℂ) := by
    intro η hη
    by_cases hee : η = η₁
    · subst hee; rw [if_pos rfl]; exact hbb
    · rw [if_neg hee]
      have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm φ hη₁ hη hee
        ((W2.subgroupOf H).index : ℂ) h1
      rw [← hyp.coherentYset_extension_Yset_diff_eq_tau hη₁ hη,
        ClassFunction.inner_sub_right, hbb] at hconst
      push_cast
      linear_combination hconst
  have hmemt : ∀ {η}, η ∈ hyp.Yset_finite.toFinset ↔ η ∈ hyp.Yset :=
    fun {η} => hyp.Yset_finite.mem_toFinset
  have hEinj_t : ∀ η ∈ hyp.Yset_finite.toFinset, ∀ η' ∈ hyp.Yset_finite.toFinset,
      hyp.coherentYset.extension η = hyp.coherentYset.extension η' → η = η' :=
    fun η hη η' hη' => hEinj η (hmemt.mp hη) η' (hmemt.mp hη')
  have horth : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ∀ ψ' ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
    intro ψ hψ ψ' hψ'
    rw [Finset.mem_image] at hψ hψ'
    obtain ⟨η, hη, rfl⟩ := hψ
    obtain ⟨η', hη', rfl⟩ := hψ'
    rw [hyp.coherentYset.extension_inner_eq η η' (Submodule.subset_span (hmemt.mp hη))
      (Submodule.subset_span (hmemt.mp hη')), hYon η η' (hmemt.mp hη) (hmemt.mp hη')]
    by_cases hee : η = η'
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η' hη' h))]
  have hη₁t : η₁ ∈ hyp.Yset_finite.toFinset := hmemt.mpr hη₁
  have hβval : ∀ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) ψ
        = ((if ψ = hyp.coherentYset.extension η₁ then bb
            else bb + (W2.subgroupOf H).index : ℤ) : ℂ) := by
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨η, hη, rfl⟩ := hψ
    rw [hcoeff η (hmemt.mp hη)]
    by_cases hee : η = η₁
    · subst hee; simp
    · rw [if_neg hee, if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h))]
  have hbessel := OddOrder.RepresentationTheory.sum_sq_le_inner_self_re horth
    (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
      - ((W2.subgroupOf H).index : ℂ) • η₁)) hβval
  have hnorm_re : (ClassFunction.inner
      (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁))
      (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁))).re
      = ((W2.index + (W2.subgroupOf H).index ^ 2 : ℕ) : ℝ) := by
    rw [hyp.inner_self_tau_indW2_sub_smul hW2H φ hη₁ ((W2.subgroupOf H).index : ℂ) h1,
      hyp.inner_self_indW2_sub_smul_eq hW2comm hW2cen φ hφ hη₁ ((W2.subgroupOf H).index : ℂ),
      show (W2.index : ℂ) + ((W2.subgroupOf H).index : ℂ) * star ((W2.subgroupOf H).index : ℂ)
          = ((W2.index + (W2.subgroupOf H).index ^ 2 : ℕ) : ℂ) by
        rw [star_natCast]; push_cast; ring,
      Complex.natCast_re]
  rw [hnorm_re] at hbessel
  have hsum : ∑ ψ ∈ hyp.Yset_finite.toFinset.image hyp.coherentYset.extension,
      (if ψ = hyp.coherentYset.extension η₁ then bb else bb + (W2.subgroupOf H).index) ^ 2
      = bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2 := by
    rw [Finset.sum_image hEinj_t]
    have hsplit : ∀ η ∈ hyp.Yset_finite.toFinset,
        (if hyp.coherentYset.extension η = hyp.coherentYset.extension η₁ then bb
          else bb + (W2.subgroupOf H).index) ^ 2
        = if η = η₁ then bb ^ 2 else (bb + (W2.subgroupOf H).index) ^ 2 := by
      intro η hη
      by_cases hee : η = η₁
      · subst hee; simp
      · rw [if_neg (fun h => hee (hEinj_t η hη η₁ hη₁t h)), if_neg hee]
    rw [Finset.sum_congr rfl hsplit, ← Finset.add_sum_erase _ _ hη₁t, if_pos rfl]
    have hcrd : (hyp.Yset_finite.toFinset.erase η₁).card = hyp.Yset.ncard - 1 := by
      rw [Finset.card_erase_of_mem hη₁t, ← Set.ncard_eq_toFinset_card _ hyp.Yset_finite]
    have h1le : 1 ≤ hyp.Yset.ncard := by
      rw [Set.ncard_eq_toFinset_card _ hyp.Yset_finite]; exact Finset.one_le_card.mpr ⟨η₁, hη₁t⟩
    rw [Finset.sum_congr rfl (fun η hη => if_neg (Finset.ne_of_mem_erase hη)),
      Finset.sum_const, nsmul_eq_mul, hcrd, Nat.cast_sub h1le, Nat.cast_one]
  rw [hsum] at hbessel
  have hnorm_ineq : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2
      ≤ (W2.index : ℤ) + ((W2.subgroupOf H).index : ℤ) ^ 2 := by
    have hb := hbessel
    rw [show ((W2.index + (W2.subgroupOf H).index ^ 2 : ℕ) : ℝ)
        = (((W2.index : ℤ) + ((W2.subgroupOf H).index : ℤ) ^ 2 : ℤ) : ℝ) by push_cast; ring] at hb
    exact_mod_cast hb
  have hm2 : (2 : ℤ) ≤ (hyp.Yset.ncard : ℤ) := by exact_mod_cast hyp.two_le_Yset_ncard
  have hc2' : (2 : ℤ) ≤ ((W2.subgroupOf H).index : ℤ) := by exact_mod_cast hc2
  have hnorm_lt : ((bb + (W2.subgroupOf H).index) - ((W2.subgroupOf H).index : ℤ)) ^ 2
      + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2
      < 2 * ((W2.subgroupOf H).index : ℤ) ^ 2 := by
    rw [show (bb + ((W2.subgroupOf H).index : ℤ)) - ((W2.subgroupOf H).index : ℤ) = bb by ring]
    have : bb ^ 2 + ((hyp.Yset.ncard : ℤ) - 1) * (bb + (W2.subgroupOf H).index) ^ 2
        < 2 * ((W2.subgroupOf H).index : ℤ) ^ 2 := by linarith [hnorm_ineq, hFPF]
    convert this using 2
  have hdich := eq_zero_or_edge_of_dvd_of_normLt hc2' hm2 (dvd_add habb (dvd_refl _)) hnorm_lt
  rcases hdich with h | ⟨h1', h2⟩
  · left
    rw [hbb]
    have hbeq : bb = -((W2.subgroupOf H).index : ℤ) := by omega
    rw [hbeq]; push_cast; ring
  · right
    refine ⟨by exact_mod_cast h2, ?_⟩
    rw [hbb]
    have hbeq : bb = 0 := by omega
    rw [hbeq]; norm_num

open scoped Classical in
/-- **(6.8.2.2) good case for `|Y| ≥ 3`.**  When `m = |Y| ≥ 3`, the edge case (`m = 2`) of
`coeff_eq_neg_or_edge_caseB` is impossible, so the good value `⟨α^τ, η₁^{τ₁}⟩ = −|H:Z|` holds with
no
relabel.  Combined with `orthogonal_tau_indW2_add_extension_caseB`, this gives the (6.8.2.2)
decomposition `α^τ = X − |H:Z|·η₁^{τ₁}` (`X ⊥ 𝒴^{τ₁}`, `X ∈ ℤ[Irr G]`) unconditionally for `|Y| ≥ 3`
(the `m = 2` edge requires the `η₁^{τ₁} ↦ −η₂^{τ₁}` relabel, handled separately). -/
theorem SibleyDadeHypothesis.inner_tau_indW2_extension_Yset_eq_neg_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (φ : IrreducibleCharacter ↥W2) (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1)
    (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2)
    (hm3 : 3 ≤ hyp.Yset.ncard) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁)
      = -((W2.subgroupOf H).index : ℂ) := by
  rcases hyp.coeff_eq_neg_or_edge_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ hφ1 hφ hc2 hFPF with
    h | ⟨hm2, _⟩
  · exact h
  · exfalso; omega

/-- **(6.8.2.2) `φ`-independence of `⟨α^τ, η'^{τ₁}⟩`** (Peterfalvi's "`Y` is independent of `φ`").
For `α_φ = Ind^L_{W₂}φ − |H:W₂|·η₁` (`φ` a nontrivial linear character of the central `W₂`), the
multiplicity `⟨α_φ^τ, η'^{τ₁}⟩` against a *fixed* `η' ∈ Y` is the **same** for all nontrivial linear
`φ`.

Proof: by Dade reciprocity (`inner_tau_indW2_sub_smul_eq`) the multiplicity is
`⟨φ, Res_{W₂} Res_L η'^{τ₁}⟩ − |H:W₂|·⟨η₁, Res_L η'^{τ₁}⟩`; the second term is already `φ`-free, and
the first equals `(f 1 − f z)/|W₂|` (`apply_one_sub_apply_eq_card_mul_inner`, since
`f = Res_{W₂} Res_L η'^{τ₁}` is constant on `W₂^#` by (6.8.2.1)
`coherentYset_extension_const_on_W2`) — visibly independent of `φ`.  This is the fact that makes the
`m = 2` relabel choice in `exists_Ycoherence_hgood_uniform_caseB` uniform across all `φ`. -/
theorem SibleyDadeHypothesis.inner_tau_alpha_extension_phiIndep
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {W2 : Subgroup ↥L} [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    {η' : ClassFunction ↥L ℂ} (hη' : η' ∈ hyp.Yset)
    (φ φ' : IrreducibleCharacter ↥W2)
    (hφ1 : (φ : ClassFunction ↥W2 ℂ) 1 = 1) (hφ : φ ≠ trivialIrreducibleCharacter ↥W2)
    (hφ'1 : (φ' : ClassFunction ↥W2 ℂ) 1 = 1) (hφ' : φ' ≠ trivialIrreducibleCharacter ↥W2) :
    ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η')
      = ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ' : ClassFunction ↥W2 ℂ)
        - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η') := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  classical
  have hW2H : W2 ≤ H := by
    have hle : ⁅H, H⁆ ≤ H := by
      rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
      exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
    exact hW2comm.trans hle
  have hdeg : ∀ χ : ClassFunction ↥W2 ℂ, χ 1 = 1 →
      ClassFunction.induce W2 χ 1 = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
    intro χ hχ1
    rw [ClassFunction.induce_apply_one, hχ1, mul_one, hyp.Yset_apply_one hη₁]
    have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
      (Subgroup.relIndex_mul_index hW2H).symm
    rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
  rw [hyp.inner_tau_indW2_sub_smul_eq hW2H (φ : ClassFunction ↥W2 ℂ) hη₁
        ((W2.subgroupOf H).index : ℂ) (hdeg _ hφ1) (hyp.coherentYset.extension η'),
    hyp.inner_tau_indW2_sub_smul_eq hW2H (φ' : ClassFunction ↥W2 ℂ) hη₁
        ((W2.subgroupOf H).index : ℂ) (hdeg _ hφ'1) (hyp.coherentYset.extension η')]
  set f := ClassFunction.restrict W2 (ClassFunction.restrict L (hyp.coherentYset.extension η'))
    with hf
  have : Nontrivial ↥W2 := Finite.one_lt_card_iff_nontrivial.mp hprime.one_lt
  obtain ⟨z₀, hz₀1⟩ := exists_ne (1 : ↥W2)
  have hfconst : ∀ a : ↥W2, a ≠ 1 → f a = f z₀ := by
    intro a ha
    have hA1 : (W2.subtype a) ≠ 1 := fun h => ha (W2.subtype_injective (by simpa using h))
    have hZ1 : (W2.subtype z₀) ≠ 1 := fun h => hz₀1 (W2.subtype_injective (by simpa using h))
    have hc := hyp.coherentYset_extension_const_on_W2 hprime hW2comm hη'
      (SetLike.coe_mem z₀) hZ1 (SetLike.coe_mem a) hA1
    simp only [hf, ClassFunction.restrict_apply]
    exact hc
  have hcard : (Nat.card ↥W2 : ℂ) ≠ 0 := by
    have h := Nat.card_pos (α := ↥W2); exact_mod_cast h.ne'
  have key : ClassFunction.inner f (φ : ClassFunction ↥W2 ℂ)
      = ClassFunction.inner f (φ' : ClassFunction ↥W2 ℂ) := by
    apply mul_left_cancel₀ hcard
    rw [← apply_one_sub_apply_eq_card_mul_inner hφ1 hφ f (z := z₀) hfconst,
      ← apply_one_sub_apply_eq_card_mul_inner hφ'1 hφ' f (z := z₀) hfconst]
  rw [OddOrder.RepresentationTheory.inner_conj_symm f (φ : ClassFunction ↥W2 ℂ),
    OddOrder.RepresentationTheory.inner_conj_symm f (φ' : ClassFunction ↥W2 ℂ), key]

open scoped Classical in
/-- **(6.8.2.2) uniform good-value `Y`-coherence** (the `hYcard`-free strengthening of
`exists_Ycoherence_hgood_caseB`).  Produces a *single* `Y`-coherence `cY` whose (6.8.2.2) anchor
multiplicity is the good value `−|H:W₂|` **simultaneously for every** nontrivial linear
`φ ∈ Irr(W₂)`.

The `m = 2` relabel (`coherentEqualDegree_swap_neg`, `η₁ ↦ −η₂^{τ₁}`) is folded in *uniformly*:
by `φ`-independence (`inner_tau_alpha_extension_phiIndep`) the good/edge branch of
`coeff_eq_neg_or_edge_caseB` is the same for **all** `φ`, so one global choice of `cY` suffices —
`coherentYset` when `|Y| ≥ 3` or the good branch holds, and the sign-swap relabel in the `|Y| = 2`
edge.  This removes the `|Y| ≠ 2` side condition (`hYcard`) from the case-(B) `X ∪ Y`-coherence
chain. -/
theorem SibleyDadeHypothesis.exists_Ycoherence_hgood_uniform_caseB
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {W2 : Subgroup ↥L} [W2.Normal] [Invertible (Nat.card ↥W2 : ℂ)]
    (hprime : (Nat.card W2).Prime) (hW2comm : W2 ≤ ⁅H, H⁆)
    (hW2cen : W2 ≤ Subgroup.center ↥L)
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hc2 : 2 ≤ (W2.subgroupOf H).index)
    (hFPF : (W2.index : ℤ) < ((W2.subgroupOf H).index : ℤ) ^ 2) :
    ∃ cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L),
      ∀ (φ : IrreducibleCharacter ↥W2), (φ : ClassFunction ↥W2 ℂ) 1 = 1 →
        φ ≠ trivialIrreducibleCharacter ↥W2 →
        ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
          - ((W2.subgroupOf H).index : ℂ) • η₁)) (cY.extension η₁)
          = -((W2.subgroupOf H).index : ℂ) := by
  have : Fintype ↥W2 := Fintype.ofFinite _
  classical
  by_cases hYc : hyp.Yset.ncard = 2
  · -- `|Y| = 2` edge: pick the branch with one `φ₀`, propagate by `φ`-independence.
    by_cases hex : ∃ φ₀ : IrreducibleCharacter ↥W2,
        (φ₀ : ClassFunction ↥W2 ℂ) 1 = 1 ∧ φ₀ ≠ trivialIrreducibleCharacter ↥W2
    · obtain ⟨φ₀, hφ₀1, hφ₀⟩ := hex
      rcases hyp.coeff_eq_neg_or_edge_caseB hcop hp hHp hprime hW2comm hW2cen hη₁ φ₀ hφ₀1 hφ₀ hc2
        hFPF
        with hgood₀ | ⟨_, hbad₀⟩
      · -- good branch: `cY = coherentYset`.
        refine ⟨hyp.coherentYset, fun φ hφ1 hφ => ?_⟩
        rw [hyp.inner_tau_alpha_extension_phiIndep hprime hW2comm hη₁ hη₁ φ φ₀ hφ1 hφ hφ₀1 hφ₀]
        exact hgood₀
      · -- edge branch: `cY = coherentEqualDegree_swap_neg`.
        obtain ⟨η₂, hη₂Y, hη₂ne⟩ :=
          Set.exists_ne_of_one_lt_ncard (by omega : 1 < hyp.Yset.ncard) η₁
        have hpairsub : ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) ⊆ hyp.Yset := by
          intro x hx; rcases hx with rfl | rfl
          · exact hη₁
          · exact hη₂Y
        have hYeq : hyp.Yset = ({η₁, η₂} : Set (ClassFunction ↥L ℂ)) :=
          (Set.eq_of_subset_of_ncard_le hpairsub
            (hYc.le.trans_eq (Set.ncard_pair hη₂ne.symm).symm) hyp.Yset_finite).symm
        have hinner : ∀ ψ ψ' : ClassFunction ↥L ℂ, IsIrreducibleCharacter ψ →
            IsIrreducibleCharacter ψ' →
            ClassFunction.inner ψ ψ' = if ψ = ψ' then (1 : ℂ) else 0 := by
          intro ψ ψ' hψ hψ'
          have h := irreducibleCharacter_inner (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
            (⟨ψ', hψ'⟩ : IrreducibleCharacter ↥L)
          simp only [IrreducibleCharacter.coe_mk] at h
          rw [h]
          by_cases hpq : ψ = ψ'
          · rw [if_pos (Subtype.ext hpq), if_pos hpq]
          · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
        have hY1irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
        have hY2irr := hyp.isIrreducibleCharacter_of_mem_Yset hη₂Y
        have horth : ClassFunction.inner η₁ η₂ = 0 := by
          rw [hinner η₁ η₂ hY1irr hY2irr, if_neg (Ne.symm hη₂ne)]
        have hn1 : ClassFunction.inner η₁ η₁ = 1 := by rw [hinner η₁ η₁ hY1irr hY1irr, if_pos rfl]
        have hn2 : ClassFunction.inner η₂ η₂ = 1 := by rw [hinner η₂ η₂ hY2irr hY2irr, if_pos rfl]
        have hdegeq : (η₂ : ↥L → ℂ) 1 = (η₁ : ↥L → ℂ) 1 :=
          (hyp.Yset_apply_one hη₂Y).trans (hyp.Yset_apply_one hη₁).symm
        have hdeg0 : (η₁ : ↥L → ℂ) 1 ≠ 0 := by
          rw [hyp.Yset_apply_one hη₁]; exact_mod_cast Nat.card_pos.ne'
        have h1A : (1 : ↥L) ∉ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
          rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]; intro hmem; exact hmem.2 (by simp)
        have hsupp : (η₂ - η₁).support ⊆
            OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
          hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₂Y) (hyp.Yset_subset_S hη₁)
            hdegeq
        have hcY0map : (hYeq ▸ hyp.coherentYset).extension = hyp.coherentYset.extension :=
          OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq hyp.coherentYset
        obtain ⟨cY', hcY'1, _⟩ := OddOrder.Peterfalvi.S07.coherentEqualDegree_swap_neg
          (hYeq ▸ hyp.coherentYset) horth hn1 hn2 hdegeq hdeg0 h1A hsupp
        refine ⟨hYeq.symm ▸ cY', fun φ hφ1 hφ => ?_⟩
        have hW2H : W2 ≤ H := by
          have hle : ⁅H, H⁆ ≤ H := by
            rw [Subgroup.commutator_le]; intro a ha b hb; rw [commutatorElement_def]
            exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)
          exact hW2comm.trans hle
        have h1φ : ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ) 1
            = ((W2.subgroupOf H).index : ℂ) * η₁ 1 := by
          rw [ClassFunction.induce_apply_one, hφ1, mul_one, hyp.Yset_apply_one hη₁]
          have hidx : W2.index = (W2.subgroupOf H).index * H.index :=
            (Subgroup.relIndex_mul_index hW2H).symm
          rw [hidx, hyp.index_H_eq_card_W1]; push_cast; ring
        have hvφ : ClassFunction.inner (hyp.tau (ClassFunction.induce W2 (φ : ClassFunction ↥W2 ℂ)
            - ((W2.subgroupOf H).index : ℂ) • η₁)) (hyp.coherentYset.extension η₁) = 0 := by
          rw [hyp.inner_tau_alpha_extension_phiIndep hprime hW2comm hη₁ hη₁ φ φ₀ hφ1 hφ hφ₀1 hφ₀]
          exact hbad₀
        have hconst := hyp.inner_tau_indW2_sub_smul_tau_Yset_diff hW2H hW2comm
          (φ : ClassFunction ↥W2 ℂ) hη₁ hη₂Y hη₂ne ((W2.subgroupOf H).index : ℂ) h1φ
        rw [← hyp.coherentYset_extension_Yset_diff_eq_tau hη₁ hη₂Y,
          ClassFunction.inner_sub_right, hvφ, sub_zero] at hconst
        rw [OddOrder.Peterfalvi.S07.IsCoherent.extension_eqRec hYeq.symm cY', hcY'1, hcY0map,
          ClassFunction.inner_neg_right, hconst]
    · -- no nontrivial linear `φ`: the `∀ φ` is vacuous.
      exact ⟨hyp.coherentYset, fun φ hφ1 hφ => absurd ⟨φ, hφ1, hφ⟩ hex⟩
  · -- `|Y| ≥ 3`: every `φ` lies in the good branch; `cY = coherentYset`.
    refine ⟨hyp.coherentYset, fun φ hφ1 hφ => ?_⟩
    have hm3 : 3 ≤ hyp.Yset.ncard := by have := hyp.two_le_Yset_ncard; omega
    exact hyp.inner_tau_indW2_extension_Yset_eq_neg_caseB hcop hp hHp hprime hW2comm hW2cen hη₁
      φ hφ1 hφ hc2 hFPF hm3

end OddOrder.Peterfalvi.S08


