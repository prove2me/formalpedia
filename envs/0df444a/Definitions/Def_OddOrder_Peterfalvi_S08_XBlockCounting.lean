-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_XBlockCounting
-- name    : OddOrder_Peterfalvi_S08_XBlockCounting
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:39:35.361195+00:00
-- url     : https://prove2.me/theorems/74d7e472-724b-4dca-b678-624d80c10b3e
-- title:
--   Peterfalvi §6.7/§6.8.1: $X$-block counting and congruences
-- statement:
--   Part of the Peterfalvi §8 coherence core, containing the (6.7) wiring to the Sibley Frobenius setup and the (6.8.1) congruence and divisibility lemmas for $\eta^{\tau_1}$.
--
--   Main results: `peterfalvi_67_centralCommutator` and its case-(A) form (Peterfalvi (6.7) specialized to the Sibley Frobenius setup), `restrict_extension_Yset_charValue_cong_of_frobenius` (the (6.8.1) congruence for $\eta^{\tau_1}$) and `dvd_inner_restrict_extension_Yset_of_frobenius` (the (6.8.1) divisibility $a\mid c$).
--
--   The bundle also proves 18 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_XBlockCounting.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_XBlockCounting.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceBasic

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(T8 leaf 8) `2 ≤ |S₀|`**, case (A) / c2 form.  As `two_le_xBaseBlock_ncard`, but
`X`-irreducibility comes from the certain-type input `isIrreducibleCharacter_of_mem_Xset_c2_caseA`
(cert data `hK`/`hW1`/`hA`) instead of `hF`. -/
theorem two_le_xBaseBlock_ncard_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hXne : (hyp.Xset hyp.centralCommutator).Nonempty) :
    2 ≤ (hyp.xBaseBlock hyp.centralCommutator).ncard := by
  have := hyp.H_normal
  have := hyp.centralCommutator_normal
  exact hyp.two_le_xBaseBlock_ncard_of_irreducible_X hyp.centralCommutator_le
    (fun _ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h) hXne

/-- **Peterfalvi (6.8.1) image orthogonality `himg_ortho` via (4.1)** (Frobenius case, mmd 04.8
L166).
`X(Zc)^{τ₂} ⊥ Y^{τ₁}`: for `χ ∈ X(Zc)`, `η ∈ Y`, the coherent images are orthogonal,
`⟨χ^{τ₂}, η^{τ₁}⟩ = 0`.  This is the "by (4.1)" step, **independent** of the deep `b ≡ 0` argument.

Pick distinct references `χ' ≠ χ` in `X(Zc)` (`2 ≤ |X(Zc)|`, from `two_le_xBaseBlock_ncard` +
`xBaseBlock_subset`) and `η' ≠ η` in `Y` (`2 ≤ |Y|`, `two_le_Yset_ncard`), and apply
`pairwise_inner_eq_zero_of_orthogonal_signedDifference` with `α = η^{τ₁}, β = η'^{τ₁}, γ = χ^{τ₂},
δ = χ'^{τ₂}` and **degree coefficients** `u = χ'(1), v = χ(1)`.  Then `u•γ − v•δ =
(χ'(1)•χ − χ(1)•χ')^{τ₂}` is the τ₂-image of a *supported* (degree-`0`,
`sMember_smulDiffSupport_of_charValue_eq` — no divisibility needed) integer `X`-combination, and
`α − β = (η − η')^{τ₁}` the τ₁-image of a supported (equal-degree, `Yset_apply_one`) `Y`-difference;
the difference-orthogonality `inner_extension_eq_inner_of_supported` (`= 0` by `X ⊥ Y`) and
degree-`0`
`extension_apply_one_eq_zero_of_supported` discharge `hdiff`/`hα1`/`hγδ1`. The conclusion
`⟨α,γ⟩ = 0`
gives the claim by conjugate symmetry. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_general
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := cX with hXc_def
  set hYc := cY with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty := ⟨χ, hχ⟩
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard hF hyp.centralCommutator_le hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη), if_pos rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        if_pos rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ), if_pos rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        if_pos rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        if_neg (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        if_neg (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Case-(A)/c2 mirror of `inner_extension_Xset_centralCommutator_Yset_eq_zero_general`.**  Same
proof as the Frobenius original, with the Frobenius hypothesis `hF` replaced by the certain-type
case-(A) data bundle `cert`/`hK`/`hW1`/`hA`, and the Frobenius `X`-irreducibility /
`two_le_xBaseBlock_ncard` adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (cX : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner (cX.extension χ) (cY.extension η) = 0 := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set hXc := cX with hXc_def
  set hYc := cY with hYc_def
  -- irreducibility of members
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  have hYirr : ∀ φ ∈ hyp.Yset, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Yset h
  -- `if`-formula for inner products of irreducibles (orthonormality)
  have hinner : ∀ (φ ψ : ClassFunction ↥L ℂ), IsIrreducibleCharacter φ → IsIrreducibleCharacter ψ →
      ClassFunction.inner φ ψ = if φ = ψ then (1 : ℂ) else 0 := by
    intro φ ψ hφ hψ
    have h := irreducibleCharacter_inner (⟨φ, hφ⟩ : IrreducibleCharacter ↥L)
      (⟨ψ, hψ⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at h
    rw [h]
    by_cases hpq : φ = ψ
    · rw [if_pos (Subtype.ext hpq), if_pos hpq]
    · rw [if_neg (fun heq => hpq (Subtype.ext_iff.mp heq)), if_neg hpq]
  -- distinct references (n, m ≥ 2)
  have hXne : (hyp.Xset hyp.centralCommutator).Nonempty := ⟨χ, hχ⟩
  have hXfin : (hyp.Xset hyp.centralCommutator).Finite := hyp.xSet_finite_of_irreducible_X hXirr
  have hX2 : 2 ≤ (hyp.Xset hyp.centralCommutator).ncard :=
    le_trans (hyp.two_le_xBaseBlock_ncard_c2_caseA hK hW1 hA hXne)
      (Set.ncard_le_ncard (hyp.xBaseBlock_subset _) hXfin)
  obtain ⟨χ', hχ'X, hχ'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by omega : 1 < (hyp.Xset hyp.centralCommutator).ncard) χ
  obtain ⟨η', hη'Y, hη'ne⟩ :=
    Set.exists_ne_of_one_lt_ncard (by have := hyp.two_le_Yset_ncard; omega : 1 < hyp.Yset.ncard) η
  -- positive natural degrees of `χ`, `χ'`
  obtain ⟨d, hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'X⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  -- membership in the integral spans (`subset_span`)
  have hχs : χ ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ
  have hχ's : χ' ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator) := Submodule.subset_span hχ'X
  have hηs : η ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη
  have hη's : η' ∈ Submodule.span ℤ hyp.Yset := Submodule.subset_span hη'Y
  -- the two supported difference inputs of (4.1)
  set xdiff : ClassFunction ↥L ℂ := d' • χ - d • χ' with hxdiff_def
  set ydiff : ClassFunction ↥L ℂ := η - η' with hydiff_def
  have hx_supp : xdiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]; exact Submodule.smul_mem _ _ hχs
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']; exact Submodule.smul_mem _ _ hχ's
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ'X) (by rw [hd_eq, hd'_eq]; ring)
  have hy_supp : ydiff ∈ OddOrder.Peterfalvi.S07.zSupportedSpan hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨Submodule.sub_mem _ hηs hη's, ?_⟩
    exact hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη) (hyp.Yset_subset_S hη'Y)
      ((hyp.Yset_apply_one hη).trans (hyp.Yset_apply_one hη'Y).symm)
  -- the image of `xdiff` is exactly the degree-weighted `u•γ − v•δ`
  have hXeq : ((d' : ℝ) : ℂ) • hXc.extension χ - ((d : ℝ) : ℂ) • hXc.extension χ'
      = hXc.extension xdiff := by
    rw [hxdiff_def, map_sub, map_nsmul, map_nsmul,
      ← Nat.cast_smul_eq_nsmul ℂ d' (hXc.extension χ),
      ← Nat.cast_smul_eq_nsmul ℂ d (hXc.extension χ')]
    push_cast
    ring
  have hYeq : hYc.extension η - hYc.extension η' = hYc.extension ydiff := by
    rw [hydiff_def, map_sub]
  -- disjointness `X(Zc) ⊥ Y` and the source orthogonality `⟨xdiff, ydiff⟩ = 0`
  have hdisj : Disjoint (hyp.Xset hyp.centralCommutator) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration hyp.centralCommutator := by
      rw [Yset]; exact hyp.SsubFiltration_antitone hyp.centralCommutator_le_commutator
    exact Set.disjoint_of_subset_right hYsub
      (hyp.disjoint_Xset_SsubFiltration (Z := hyp.centralCommutator))
  have hsrc0 : ClassFunction.inner xdiff ydiff = 0 :=
    inner_eq_zero_of_mem_span_of_disjoint_irreducible
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hφ)
      (fun φ hφ => hyp.isIrreducibleCharacter_of_mem_Yset hφ) hdisj xdiff hx_supp.1 ydiff hy_supp.1
  -- discharge the (4.1) hypotheses and read off `⟨α,γ⟩ = 0`
  have hconcl := OddOrder.RepresentationTheory.pairwise_inner_eq_zero_of_orthogonal_signedDifference
    (Γ := G) (α := hYc.extension η) (β := hYc.extension η')
    (γ := hXc.extension χ) (δ := hXc.extension χ')
    (u := (d' : ℝ)) (v := (d : ℝ))
    (by exact_mod_cast hd'_pos.ne') (by exact_mod_cast hd_pos.ne')
    (hYc.extension_mem_ZIrr η hηs)
    (by rw [hYc.extension_inner_eq η η hηs hηs, hinner η η (hYirr η hη) (hYirr η hη), if_pos rfl])
    (hYc.extension_mem_ZIrr η' hη's)
    (by rw [hYc.extension_inner_eq η' η' hη's hη's, hinner η' η' (hYirr η' hη'Y) (hYirr η' hη'Y),
        if_pos rfl])
    (hXc.extension_mem_ZIrr χ hχs)
    (by rw [hXc.extension_inner_eq χ χ hχs hχs, hinner χ χ (hXirr χ hχ) (hXirr χ hχ), if_pos rfl])
    (hXc.extension_mem_ZIrr χ' hχ's)
    (by rw [hXc.extension_inner_eq χ' χ' hχ's hχ's, hinner χ' χ' (hXirr χ' hχ'X) (hXirr χ' hχ'X),
        if_pos rfl])
    (by rw [hYc.extension_inner_eq η η' hηs hη's, hinner η η' (hYirr η hη) (hYirr η' hη'Y),
        if_neg (fun h => hη'ne h.symm)])
    (by rw [hXc.extension_inner_eq χ χ' hχs hχ's, hinner χ χ' (hXirr χ hχ) (hXirr χ' hχ'X),
        if_neg (fun h => hχ'ne h.symm)])
    (by -- hdiff
      rw [hXeq, hYeq, inner_conj_symm (hXc.extension xdiff) (hYc.extension ydiff),
        inner_extension_eq_inner_of_supported hyp.dade hXc hYc hx_supp hy_supp,
        hsrc0, star_zero])
    (by -- hα1
      rw [hYeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hYc hy_supp)
    (by -- hγδ1
      rw [hXeq]; exact extension_apply_one_eq_zero_of_supported hyp.dade hXc hx_supp)
  rw [inner_conj_symm (hYc.extension η) (hXc.extension χ), hconcl.1, star_zero]

/-- **Peterfalvi (6.8.1) `himg_ortho`** at the fixed Frobenius-case witnesses `τ₂ =
`Xset_centralCommutator_isCoherent`, `τ₁ = coherentYset` (specialization of
`inner_extension_Xset_centralCommutator_Yset_eq_zero_general`). -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 :=
  hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general hF
    (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp)
    hyp.coherentYset hχ hη

/-- **Case-(A)/c2 mirror of `inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_Xset_centralCommutator_Yset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {χ : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension χ)
      (hyp.coherentYset.extension η) = 0 :=
  hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_general_c2_caseA hK hW1 hA
    (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp)
    hyp.coherentYset hχ hη

/-- **Span form of `himg_ortho`:** `⟨x^{τ₂}, η^{τ₁}⟩ = 0` for any `x ∈ ℤ[X(Zc)]` and `η ∈ Y`
(by `ℤ`-linearity from the per-member
`inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius`). -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_of_frobenius
        hF hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **Case-(A)/c2 mirror of
`inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_extension_span_Xset_centralCommutator_Yset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {x : ClassFunction ↥L ℂ} (hx : x ∈ Submodule.span ℤ (hyp.Xset hyp.centralCommutator))
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset) :
    ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 := by
  classical
  induction hx using Submodule.span_induction with
  | mem χ hχ =>
      exact hyp.inner_extension_Xset_centralCommutator_Yset_eq_zero_c2_caseA
        hK hW1 hA hHnonab hp hp3 hHp hχ hη
  | zero => rw [map_zero, ClassFunction.inner_zero_left]
  | add a b _ _ iha ihb => rw [map_add, ClassFunction.inner_add_left, iha, ihb, add_zero]
  | smul c a _ ih =>
      rw [map_zsmul,
        ← Int.cast_smul_eq_zsmul ℂ c
          ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp
            hp3 hHp).extension
            a),
        ClassFunction.inner_smul_left, ih, mul_zero]

/-- **(6.8.1) Res-decomposition orthogonality** (spine steps 1–2): `Res^G_L(η^{τ₁})` is orthogonal
to every *supported* `X(Zc)`-combination.  For `η ∈ Y` and `x ∈ ℤ[X(Zc), H^#]` (supported),
`⟨Res^G_L(η^{τ₁}), x⟩_L = 0`.  By Dade reciprocity (`inner_tau_eq_inner_restrict`,
`⟨x^τ, η^{τ₁}⟩_G = ⟨x, Res_L(η^{τ₁})⟩_L`) and `x^τ = x^{τ₂}` (supported), this reduces to the span
form of `himg_ortho` (`⟨x^{τ₂}, η^{τ₁}⟩_G = 0`).  Hence the `X`-components of `Res^G_L(η^{τ₁})` are
all proportional to `dᵢ`, i.e. `Res^G_L(η^{τ₁}) = c·∑dᵢχᵢ + χ′` with `χ′ ⊥ X(Zc)` (mmd 04.8
L170). -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extends_on_supported
      x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_frobenius hF hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_of_frobenius
      hF hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **Case-(A)/c2 mirror of `inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_restrict_extension_Yset_mem_span_Xset_eq_zero_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {x : ClassFunction ↥L ℂ}
    (hx : x ∈ OddOrder.Peterfalvi.S07.zSupportedSpan (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)) :
    ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) x = 0 := by
  classical
  have hrec := hyp.inner_tau_eq_inner_restrict hx.2 (hyp.coherentYset.extension η)
  have hτ : hyp.tau x =
      (hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp
        hp3 hHp).extension x :=
    ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3
      hHp).extends_on_supported x hx).symm
  have h0 : ClassFunction.inner
      ((hyp.Xset_centralCommutator_isCoherent_of_c2_caseA hK hW1 hA hHnonab hp hp3 hHp).extension x)
      (hyp.coherentYset.extension η) = 0 :=
    hyp.inner_extension_span_Xset_centralCommutator_Yset_eq_zero_c2_caseA
      hK hW1 hA hHnonab hp hp3 hHp hx.1 hη
  have hxr : ClassFunction.inner x
      (ClassFunction.restrict L (hyp.coherentYset.extension η)) = 0 := by
    rw [← hrec, hτ, h0]
  rw [inner_conj_symm x (ClassFunction.restrict L (hyp.coherentYset.extension η)), hxr, star_zero]

/-- **(6.8.1) Res `X`-coefficient proportionality** (mmd 04.8 L170).  For `χ, χ' ∈ X(Zc)` and
`R = Res^G_L(η^{τ₁})` (`η ∈ Y`), `χ'(1)·⟨R, χ⟩ = χ(1)·⟨R, χ'⟩` — the `X`-Fourier coefficients of `R`
are proportional to the degrees (`⟨R,χᵢ⟩ ∝ dᵢ`, the `Res^G_L(η₁^{τ₁}) = c∑dᵢχᵢ + χ′` decomposition).
Apply Res-orthogonality (`inner_restrict_extension_Yset_mem_span_Xset_eq_zero`) to the supported
integer combination `χ'(1)•χ − χ(1)•χ'` (degree-`0`, `sMember_smulDiffSupport_of_charValue_eq`). -/
theorem inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner
        (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_of_frobenius
    hF hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **Case-(A)/c2 mirror of `inner_restrict_extension_Yset_mul_degree_eq_of_frobenius`.**  Same as
the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`,
and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem inner_restrict_extension_Yset_mul_degree_eq_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Xset hyp.centralCommutator)
    (hχ' : χ' ∈ hyp.Xset hyp.centralCommutator) :
    (χ' 1) * ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ
      = (χ 1) * ClassFunction.inner
        (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ' := by
  classical
  have hXirr : ∀ φ ∈ hyp.Xset hyp.centralCommutator, IsIrreducibleCharacter φ :=
    fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h
  obtain ⟨d, _hd_pos, hd_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ, hXirr χ hχ⟩ : IrreducibleCharacter ↥L)
  obtain ⟨d', _hd'_pos, hd'_eq⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨χ', hXirr χ' hχ'⟩ : IrreducibleCharacter ↥L)
  simp only [IrreducibleCharacter.coe_mk] at hd_eq hd'_eq
  have hx_supp : (d' • χ - d • χ') ∈ OddOrder.Peterfalvi.S07.zSupportedSpan
      (hyp.Xset hyp.centralCommutator)
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := by
    refine ⟨?_, ?_⟩
    · refine Submodule.sub_mem _ ?_ ?_
      · rw [← Nat.cast_smul_eq_nsmul ℤ d' χ]
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ)
      · rw [← Nat.cast_smul_eq_nsmul ℤ d χ']
        exact Submodule.smul_mem _ _ (Submodule.subset_span hχ')
    · exact hyp.sMember_smulDiffSupport_of_charValue_eq (hyp.Xset_subset_S hχ)
        (hyp.Xset_subset_S hχ') (by rw [hd_eq, hd'_eq]; ring)
  have hortho := hyp.inner_restrict_extension_Yset_mem_span_Xset_eq_zero_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hx_supp
  rw [ClassFunction.inner_sub_right,
    ← Nat.cast_smul_eq_nsmul ℂ d' χ, ← Nat.cast_smul_eq_nsmul ℂ d χ',
    OddOrder.RepresentationTheory.inner_smul_right, OddOrder.RepresentationTheory.inner_smul_right,
    star_natCast, star_natCast, ← hd'_eq, ← hd_eq] at hortho
  exact sub_eq_zero.mp hortho

/-- **(6.8.1) `η^{τ₁}` constancy value on `Zc^#`** (mmd 04.8 L168, the key constant).  For `η ∈ Y`,
`χ₁ ∈ X(Zc)` and `z ∈ Zc^#`, with `R = Res^G_L(η^{τ₁})`,
`χ₁(1)·(R(z) − R(1)) = -⟨R, χ₁⟩·|L|`.  Since the right side is independent of `z`, this shows `R`
(hence `η^{τ₁}`) is **constant on `Zc^#`** (and gives the value `R(z) − R(1) = -c|H|/a` with
`c = ⟨R,χ₁⟩`, `χ₁(1) = a|W₁|`, after clearing the denominator).

Proof: Fourier-expand `R = ∑_{a∈Irr L} ⟨R,a⟩•a` (`classFunction_eq_sum_inner_smul`); split the sum
by `Zc ⊄ ker`.  On `Zc ⊆ ker` (the non-`X` part) `a(z) = a(1)`, so those terms vanish.  On `X(Zc)`
the coefficient relation `χ₁(1)⟨R,a⟩ = a(1)⟨R,χ₁⟩` (`inner_restrict_extension_Yset_mul_degree_eq`)
factors out `⟨R,χ₁⟩`, leaving `⟨R,χ₁⟩·∑_{a∈X} a(1)(a(z)−a(1)) = ⟨R,χ₁⟩·(-|L|)`
(`sum_filter_degree_mul_charValue_sub_eq`). -/
theorem restrict_extension_Yset_degree_value_eq_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_of_frobenius
      hF hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_degree_value_eq_of_frobenius`.**  Same as the
Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`,
and
the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_degree_value_eq_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (χ₁ 1) * ((ClassFunction.restrict L (hyp.coherentYset.extension η)) z
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1)
      = -(ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁)
          * (Nat.card ↥L : ℂ) := by
  classical
  have : (hyp.centralCommutator).Normal := hyp.centralCommutator_normal
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  have hval : R z - R 1 = ∑ a : IrreducibleCharacter ↥L,
      ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
        ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) := by
    conv_lhs => rw [OddOrder.RepresentationTheory.classFunction_eq_sum_inner_smul R]
    rw [ClassFunction.finset_sum_apply, ClassFunction.finset_sum_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply]; ring
  rw [hval, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun a : IrreducibleCharacter ↥L => ¬ ((hyp.centralCommutator : Set ↥L) ⊆
        OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ)))]
  have hnot : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1))) = 0 := by
    refine Finset.sum_eq_zero (fun a ha => ?_)
    rw [Finset.mem_filter, not_not] at ha
    have haz : (a : ClassFunction ↥L ℂ) z = (a : ClassFunction ↥L ℂ) 1 := by
      have hmem := ha.2 hz
      rw [OddOrder.Peterfalvi.S03.mem_characterKernel,
        OddOrder.Peterfalvi.S03.characterDegree_def] at hmem
      exact hmem
    rw [haz, sub_self, mul_zero, mul_zero]
  rw [hnot, add_zero]
  have hfilter : (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
        ¬ ((hyp.centralCommutator : Set ↥L) ⊆
          OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
        (χ₁ 1) * (ClassFunction.inner R (a : ClassFunction ↥L ℂ) *
          ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)))
      = (ClassFunction.inner R χ₁) *
        (∑ a ∈ Finset.univ.filter (fun a : IrreducibleCharacter ↥L =>
          ¬ ((hyp.centralCommutator : Set ↥L) ⊆
            OddOrder.Peterfalvi.S03.characterKernel (a : ClassFunction ↥L ℂ))),
          (a : ClassFunction ↥L ℂ) 1 *
            ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    rw [Finset.mem_filter] at ha
    have haX : (a : ClassFunction ↥L ℂ) ∈ hyp.Xset hyp.centralCommutator := by
      rw [hyp.Xset_eq_irreducible_not_subset_characterKernel hyp.centralCommutator_le
        (fun φ h => hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA h)]
      exact ⟨a.isIrreducible, ha.2⟩
    have hrel := hyp.inner_restrict_extension_Yset_mul_degree_eq_c2_caseA
      hK hW1 hA hHnonab hp hp3 hHp hη haX hχ₁
    rw [← hRdef] at hrel
    linear_combination ((a : ClassFunction ↥L ℂ) z - (a : ClassFunction ↥L ℂ) 1) * hrel
  rw [hfilter, OddOrder.RepresentationTheory.sum_filter_degree_mul_charValue_sub_eq
    (N := hyp.centralCommutator) hz hz1]
  ring

/-- **(6.8.1) `η^{τ₁}` is constant on `Zc^#`** (mmd 04.8 L168 conclusion).  For `η ∈ Y`, the
restriction `Res^G_L(η^{τ₁})` takes the same value at any two points of `Zc^#`.  Immediate from the
value identity `restrict_extension_Yset_degree_value_eq_of_frobenius` (whose right side
`-⟨R,χ₁⟩·|L|`
is independent of the point) and `χ₁(1) ≠ 0` (any anchor `χ₁ ∈ X(Zc)`, nonempty).  This is the exact
"character constant on `Z^#`" hypothesis of the (6.7) adapter `peterfalvi_67_centralCommutator`. -/
theorem restrict_extension_Yset_const_on_centralCommutator_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty hF hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁⟩ : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_const_on_centralCommutator_of_frobenius`.**
Same as the Frobenius original, with `hF` replaced by the certain-type case-(A) bundle
`cert`/`hK`/`hW1`/`hA`, and the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_const_on_centralCommutator_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z z' : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1)
    (hz' : z' ∈ hyp.centralCommutator) (hz'1 : z' ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z' := by
  obtain ⟨χ₁, hχ₁⟩ := hyp.Xset_centralCommutator_nonempty_c2_caseA hK hW1 hA hHnonab
  have hd : χ₁ 1 ≠ 0 := by
    obtain ⟨d, hd_pos, hd_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast
      (⟨χ₁, hyp.isIrreducibleCharacter_of_mem_Xset_c2_caseA hK hW1 hA hχ₁⟩
        : IrreducibleCharacter ↥L)
    simp only [IrreducibleCharacter.coe_mk] at hd_eq
    rw [hd_eq]; exact_mod_cast hd_pos.ne'
  have hv := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz hz1
  have hv' := hyp.restrict_extension_Yset_degree_value_eq_c2_caseA
    hK hW1 hA hHnonab hp hp3 hHp hη hχ₁ hz' hz'1
  have hcancel : (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
      = (ClassFunction.restrict L (hyp.coherentYset.extension η)) z'
        - (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1 :=
    mul_left_cancel₀ hd (hv.trans hv'.symm)
  linear_combination hcancel

/-- **(6.7)-wiring step (b): `N_G(H.map L.subtype) = L`.**  The normalizer (in `G`) of the kernel
realized in the ambient group is exactly `L`: `≤` is the `H^#` TI condition (`H_sharp_ti`; a
nontrivial `a ∈ Ĥ` and its conjugate witness the TI hypothesis), and `≥` holds because `H ◁ L`
(`L = range L.subtype` normalizes the image of the normal `H`, via `le_normalizer_map`). -/
theorem normalizer_map_subtype_eq (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    Subgroup.normalizer (H.map L.subtype) = L := by
  apply le_antisymm
  · have : Nontrivial ↥H := H.nontrivial_iff_ne_bot.mpr hyp.H_ne_bot
    obtain ⟨x, hx1⟩ := exists_ne (1 : ↥H)
    set a : G := ((x : ↥L) : G) with ha_def
    have haĤ : a ∈ H.map L.subtype := Subgroup.mem_map.mpr ⟨(x : ↥L), x.2, rfl⟩
    have ha1 : a ≠ 1 := by rw [ha_def]; simp only [ne_eq, OneMemClass.coe_eq_one]; exact hx1
    intro g hg
    refine hyp.H_sharp_ti g ⟨a, ⟨haĤ, ha1⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg a).mp haĤ
    · intro hc
      rw [Set.mem_singleton_iff, mul_inv_eq_one, mul_eq_left] at hc
      exact ha1 hc
  · calc L = L.subtype.range := (Subgroup.range_subtype L).symm
      _ = (⊤ : Subgroup ↥L).map L.subtype := MonoidHom.range_eq_map L.subtype
      _ = (Subgroup.normalizer H).map L.subtype := by
          rw [Subgroup.normalizer_eq_top_iff.mpr ‹H.Normal›]
      _ ≤ Subgroup.normalizer (H.map L.subtype) := H.le_normalizer_map L.subtype

/-- **`Ĥ = H.map L.subtype` is a Sylow `p`-subgroup of `G`, from the Hall coprimality** — the
coprimality-only core of `sylow_map_subtype_of_frobenius`.  Peterfalvi (6.8)(a) only assumes `H^#`
TI with normalizer `L`, which alone does *not* force `H` Sylow; the only extra input is
`gcd(|H|, |W₁|) = 1` (Frobenius: `hF.coprime_card_kernel_complement`; (6.8)(c2): the `cases` Hall
side condition).  With `H` a `p`-group and `H ◁ L` with coprime complement `W₁`, `H` is the unique
normal Sylow `p`-subgroup of `↥L`, so every `p`-subgroup of `↥L` (e.g. `Q ⊓ L` for a Sylow
`Q ⊇ Ĥ`) lies in `H`; with `N_G(Ĥ) ≤ L` (`H^#` TI) and the self-normalizing-Sylow criterion
`sylow_coe_eq_of_normalizer_inf_le`, this forces `Ĥ ∈ Syl_p(G)`.  (Lifted from `S08_CaseBCoherence`;
both Frobenius and case-(A)/(B) (6.7)-wirings delegate here.) -/
theorem sylow_map_subtype_of_coprime (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1))
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype := by
  have : Fact p.Prime := ⟨hp⟩
  set Ĥ : Subgroup G := H.map L.subtype with hĤ_def
  -- `Ĥ` is a `p`-group (image of the `p`-group `H` under the injective `L.subtype`).
  have hĤp : IsPGroup p ↥Ĥ := hHp.map L.subtype
  -- `p ∣ |H|` (nontrivial `p`-group) and `gcd(|H|, |W₁|) = 1`, so `p ∤ [L : H] = |W₁|`.
  have hpH : p ∣ Nat.card ↥H := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hHp
    have h1 : 1 < Nat.card ↥H := (Subgroup.one_lt_card_iff_ne_bot (H := H)).mpr hyp.H_ne_bot
    rw [hn] at h1 ⊢
    rcases n with _ | n
    · simp at h1
    · exact dvd_pow_self p (Nat.succ_ne_zero n)
  have hpidx : ¬ p ∣ H.index := by
    rw [hyp.index_H_eq_card_W1]
    exact (hp.coprime_iff_not_dvd).mp (Nat.Coprime.coprime_dvd_left hpH hcop)
  -- `H` is the unique (normal) Sylow `p`-subgroup of `↥L`.
  set HSyl : Sylow p ↥L := hHp.toSylow hpidx with hHSyl_def
  have hHSyl : (HSyl : Subgroup ↥L) = H := IsPGroup.toSylow_coe hHp hpidx
  have hHSylNormal : (HSyl : Subgroup ↥L).Normal := by rw [hHSyl]; exact ‹H.Normal›
  have : Unique (Sylow p ↥L) := Sylow.unique_of_normal HSyl hHSylNormal
  have hpsub : ∀ K : Subgroup ↥L, IsPGroup p K → K ≤ H := by
    intro K hK
    obtain ⟨R, hR⟩ := hK.exists_le_sylow
    calc K ≤ (R : Subgroup ↥L) := hR
      _ = (HSyl : Subgroup ↥L) := by rw [Subsingleton.elim R HSyl]
      _ = H := hHSyl
  -- `N_G(Ĥ) ≤ L` from `H^#` TI (the `normalizer_map_subtype_eq` equality).
  have hNle : Subgroup.normalizer Ĥ ≤ L := hyp.normalizer_map_subtype_eq.le
  -- a Sylow overgroup `Q ⊇ Ĥ`; then `N_G(Ĥ) ⊓ Q ≤ Ĥ` via the `p`-subgroup `Q.comap L.subtype ≤ H`.
  obtain ⟨Q, hĤQ⟩ := hĤp.exists_le_sylow
  refine ⟨Q, ?_⟩
  apply OddOrder.GroupTheory.sylow_coe_eq_of_normalizer_inf_le hĤQ
  intro x hx
  have hxL : x ∈ L := hNle hx.1
  have hQLp : IsPGroup p ((Q : Subgroup G).comap L.subtype : Subgroup ↥L) :=
    Q.isPGroup'.comap_of_injective L.subtype L.subtype_injective
  have hx'H : (⟨x, hxL⟩ : ↥L) ∈ H :=
    hpsub _ hQLp (Subgroup.mem_comap.mpr (by exact hx.2))
  exact Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hx'H, rfl⟩

/-- **(6.7)-wiring step (a): the kernel `H`, mapped into `G`, is a Sylow `p`-subgroup of `G`.**

Peterfalvi (6.7) is stated for a Sylow `p`-subgroup `P` of `G` with `L = N_G(P)`; the (6.8.1)
application uses it at `P = H` (modulus `|H|`).  In the **Frobenius case**, `H ◁ L` with complement
`W₁` of coprime order (`hF.coprime_card_kernel_complement`) makes `H` Sylow; delegates to the
coprimality core `sylow_map_subtype_of_coprime`. -/
theorem sylow_map_subtype_of_frobenius (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = H.map L.subtype :=
  hyp.sylow_map_subtype_of_coprime hF.coprime_card_kernel_complement hp hHp

open scoped OddOrder.AlgInt in
/-- **(6.7)-wiring capstone: Peterfalvi (6.7) specialized to the Sibley Frobenius setup.**

For an irreducible `ρ` whose character is **constant on `Z^# = (Z(H) ∩ H′)^#`** (the only
character-theoretic input, deferred to the caller — in (6.8.1) it is `η₁^{τ₁}`), the congruence

`ρ.character z ≡ ρ.character 1  (mod |H|)`

holds for `z ∈ Z^#`.  This discharges every structural hypothesis of `peterfalvi_67_of_odd` at
`P := Ĥ = H.map L.subtype` (Sylow in `G` by `sylow_map_subtype_of_frobenius`, with `N_G(Ĥ) = L` by
`normalizer_map_subtype_eq`) and `Z := centralCommutator.map L.subtype`: `hZP`, `hZnormal`
(`Z.subgroupOf L = centralCommutator ◁ ↥L`), `hti`/`hodd` (`H^#` TI / `|L|` odd), `hPz`
(`Ĥ ≤ C_G(z)`), and the `|C_L(·)|`-constancy clause of `hconst` (both sides `= |Ĥ|` by
`inf_centralizer_centralCommutator_map`).  The modulus `|Ĥ| = |H|` via `card_map_of_injective`. -/
theorem peterfalvi_67_centralCommutator (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ hyp.centralCommutator.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
        ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_frobenius hF hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : hyp.centralCommutator.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hyp.centralCommutator_le
  have hZnormal : ((hyp.centralCommutator.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (hyp.centralCommutator.map L.subtype).subgroupOf L = hyp.centralCommutator from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hyp.centralCommutator_normal
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hQeq]
    obtain ⟨w', hw', hw'z⟩ := Subgroup.mem_map.mp hz
    have hw'zc : (w' : G) = z := hw'z
    have hw'1 : w' ≠ 1 := fun h => hz1 (hw'zc ▸ OneMemClass.coe_eq_one.mpr h)
    have hbr := hyp.inf_centralizer_centralCommutator_map hF hw' hw'1
    rw [hw'zc] at hbr
    rw [← hbr]; exact inf_le_right
  have hconst : ∀ ⦃w : G⦄, w ∈ hyp.centralCommutator.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w', hw'cc, hw'w⟩ := Subgroup.mem_map.mp hw
    have hw'wc : (w' : G) = w := hw'w
    have hw'1 : w' ≠ 1 := fun h => hw1 (hw'wc ▸ OneMemClass.coe_eq_one.mpr h)
    obtain ⟨z', hz'cc, hz'z⟩ := Subgroup.mem_map.mp hz
    have hz'zc : (z' : G) = z := hz'z
    have hz'1 : z' ≠ 1 := fun h => hz1 (hz'zc ▸ OneMemClass.coe_eq_one.mpr h)
    rw [hNorm, ← hw'wc, ← hz'zc, hyp.inf_centralizer_centralCommutator_map hF hw'cc hw'1,
      hyp.inf_centralizer_centralCommutator_map hF hz'cc hz'1]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.7)-wiring capstone, case-(A) / c2 form.**  The (c2) analogue of
`peterfalvi_67_centralCommutator`: the (6.7) congruence `ρ.character z ≡ ρ.character 1 (mod |H|)`
for `z ∈ Zc^#` and `ρ` irreducible **constant on `Zc^#`**, *without* the Frobenius hypothesis.  `H`
is Sylow in `G` via the coprimality core `sylow_map_subtype_of_coprime` (coprimality from
`cert.card_coprime`), and the `|C_L(·)|`-constancy clause of `hconst` is the case-(A) FPF
`inf_centralizer_centralCommutator_map_c2_caseA`.  Otherwise structurally identical to the
Frobenius form. -/
theorem peterfalvi_67_centralCommutator_c2_caseA (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {p : ℕ} (hp : p.Prime) (hHp : IsPGroup p ↥H)
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    {z : G} (hz : z ∈ hyp.centralCommutator.map L.subtype) (hz1 : z ≠ 1)
    (hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
        ρ.character w = ρ.character z) :
    ρ.character z ≡ ρ.character 1 [ALGMOD (Nat.card ↥H : ℤ)] := by
  have : Fact p.Prime := ⟨hp⟩
  classical
  have hcop : Nat.Coprime (Nat.card ↥H) (Nat.card hyp.W1) := by
    have h := cert.card_coprime; rw [hK, hW1] at h; exact h
  obtain ⟨Q, hQeq⟩ := hyp.sylow_map_subtype_of_coprime hcop hp hHp
  have hNorm : Subgroup.normalizer ((Q : Subgroup G) : Set G) = L := by
    rw [hQeq]; exact hyp.normalizer_map_subtype_eq
  have hcard : Nat.card (Q : Subgroup G) = Nat.card ↥H := by
    rw [hQeq]; exact Subgroup.card_map_of_injective L.subtype_injective
  -- structural hypotheses of `peterfalvi_67_of_odd`
  have hZP : hyp.centralCommutator.map L.subtype ≤ (Q : Subgroup G) := by
    rw [hQeq]; exact Subgroup.map_mono hyp.centralCommutator_le
  have hZnormal : ((hyp.centralCommutator.map L.subtype).subgroupOf
      (Subgroup.normalizer ((Q : Subgroup G) : Set G))).Normal := by
    rw [hNorm,
      show (hyp.centralCommutator.map L.subtype).subgroupOf L = hyp.centralCommutator from
        Subgroup.comap_map_eq_self_of_injective L.subtype_injective _]
    exact hyp.centralCommutator_normal
  have hti : OddOrder.GroupTheory.IsTISubset (((Q : Subgroup G) : Set G) \ {1})
      (Subgroup.normalizer ((Q : Subgroup G) : Set G)) := by
    rw [hNorm, show ((Q : Subgroup G) : Set G) \ {1} = sharpImage H by rw [hQeq]; rfl]
    exact hyp.H_sharp_ti
  have hodd : Odd (Nat.card (Subgroup.normalizer ((Q : Subgroup G) : Set G))) := by
    rw [hNorm]; exact hyp.card_L_odd
  have hPz : (Q : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hQeq]
    obtain ⟨w', hw', hw'z⟩ := Subgroup.mem_map.mp hz
    have hw'zc : (w' : G) = z := hw'z
    have hw'1 : w' ≠ 1 := fun h => hz1 (hw'zc ▸ OneMemClass.coe_eq_one.mpr h)
    have hbr := hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hw' hw'1
    rw [hw'zc] at hbr
    rw [← hbr]; exact inf_le_right
  have hconst : ∀ ⦃w : G⦄, w ∈ hyp.centralCommutator.map L.subtype → w ≠ 1 →
      ρ.character w = ρ.character z ∧
        Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({w} : Set G)) =
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G) ⊓
            Subgroup.centralizer ({z} : Set G)) := by
    intro w hw hw1
    refine ⟨hψconst w hw hw1, ?_⟩
    obtain ⟨w', hw'cc, hw'w⟩ := Subgroup.mem_map.mp hw
    have hw'wc : (w' : G) = w := hw'w
    have hw'1 : w' ≠ 1 := fun h => hw1 (hw'wc ▸ OneMemClass.coe_eq_one.mpr h)
    obtain ⟨z', hz'cc, hz'z⟩ := Subgroup.mem_map.mp hz
    have hz'zc : (z' : G) = z := hz'z
    have hz'1 : z' ≠ 1 := fun h => hz1 (hz'zc ▸ OneMemClass.coe_eq_one.mpr h)
    rw [hNorm, ← hw'wc, ← hz'zc,
      hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hw'cc hw'1,
      hyp.inf_centralizer_centralCommutator_map_c2_caseA hK hW1 hA hz'cc hz'1]
  have key := OddOrder.RepresentationTheory.peterfalvi_67_of_odd ρ Q hZP hZnormal hti hodd
    hz hz1 hPz hconst
  rwa [hcard] at key

open scoped OddOrder.AlgInt in
/-- **(6.8.1) (6.7)-congruence for `η^{τ₁}`** (mmd 04.8 L168 → L176).  For `η ∈ Y` and `z ∈ Zc^#`,
`Res^G_L(η^{τ₁})(z) ≡ Res^G_L(η^{τ₁})(1) (mod |H|)`.  Wires the (6.7) adapter
`peterfalvi_67_centralCommutator` to `η^{τ₁}`: write `η^{τ₁} = ε•ξ` (`ε = ±1`, `ξ` irreducible, from
norm `1`); unpack `ξ = ρ.character` (`ρ` irreducible).  The const-on-`Zc^#`
(`restrict_extension_Yset_const_on_centralCommutator_of_frobenius`, transferred to `Zc.map`) is the
adapter's hypothesis, giving `ξ(z) ≡ ξ(1) (mod |H|)`; scale by `ε` (`Cong.smul_left`) to get
`η^{τ₁}(z) ≡ η^{τ₁}(1)`. -/
theorem restrict_extension_Yset_charValue_cong_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hηtnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η (Submodule.subset_span hη)
      (Submodule.subset_span hη)]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
    simpa using h
  obtain ⟨ε, ξ, hε, hηtε⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hηtZ hηtnorm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  -- the eval identity `η^{τ₁}(g) = ε · ξ(g)`.
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g
      = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  have : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ hyp.centralCommutator.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.restrict_extension_Yset_const_on_centralCommutator_of_frobenius
        hF hHnonab hp hp3 hHp hη hw₀ hw₀1 hz hz1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_centralCommutator hF hp hHp ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **Case-(A)/c2 mirror of `restrict_extension_Yset_charValue_cong_of_frobenius`.**  Same as the
Frobenius original, with `hF` replaced by the certain-type case-(A) bundle `cert`/`hK`/`hW1`/`hA`,
and
the Frobenius adapters replaced by their `_c2_caseA` counterparts. -/
theorem restrict_extension_Yset_charValue_cong_c2_caseA
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {z : ↥L} (hz : z ∈ hyp.centralCommutator) (hz1 : z ≠ 1) :
    (ClassFunction.restrict L (hyp.coherentYset.extension η)) z
      ≡ (ClassFunction.restrict L (hyp.coherentYset.extension η)) 1
        [ALGMOD (Nat.card ↥H : ℤ)] := by
  classical
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hηtnorm : ClassFunction.inner (hyp.coherentYset.extension η)
      (hyp.coherentYset.extension η) = 1 := by
    rw [hyp.coherentYset.extension_inner_eq η η (Submodule.subset_span hη)
      (Submodule.subset_span hη)]
    have h := irreducibleCharacter_inner_eq_ite
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
      (⟨η, hyp.isIrreducibleCharacter_of_mem_Yset hη⟩ : IrreducibleCharacter ↥L)
    simpa using h
  obtain ⟨ε, ξ, hε, hηtε⟩ := exists_zsmul_irreducibleCharacter_of_inner_self_one hηtZ hηtnorm
  have hεne : (ε : ℂ) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
  have hεint : IsIntegral ℤ (ε : ℂ) := by
    simpa using (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := ε))
  -- the eval identity `η^{τ₁}(g) = ε · ξ(g)`.
  have hsmul : ∀ g : G, (hyp.coherentYset.extension η) g
      = (ε : ℂ) * ((ξ : ClassFunction G ℂ) g) := by
    intro g
    rw [hηtε, ← Int.cast_smul_eq_zsmul ℂ ε (ξ : ClassFunction G ℂ), ClassFunction.smul_apply]
  obtain ⟨V, _, _, _, ρ, hρ, hξρ⟩ := ξ.isIrreducible
  have : ρ.IsIrreducible := hρ
  have hzGmem : (L.subtype z) ∈ hyp.centralCommutator.map L.subtype :=
    Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
  have hzG1 : (L.subtype z) ≠ 1 := fun h => hz1 (L.subtype_injective (by simpa using h))
  have hψconst : ∀ w ∈ hyp.centralCommutator.map L.subtype, w ≠ 1 →
      ρ.character w = ρ.character (L.subtype z) := by
    intro w hw hw1
    obtain ⟨w₀, hw₀, rfl⟩ := Subgroup.mem_map.mp hw
    have hw₀1 : w₀ ≠ 1 := fun h => hw1 (by rw [h]; simp)
    have hRw : (hyp.coherentYset.extension η) (L.subtype w₀)
        = (hyp.coherentYset.extension η) (L.subtype z) :=
      hyp.restrict_extension_Yset_const_on_centralCommutator_c2_caseA
        hK hW1 hA hHnonab hp hp3 hHp hη hw₀ hw₀1 hz hz1
    rw [← congrFun hξρ (L.subtype w₀), ← congrFun hξρ (L.subtype z)]
    apply mul_left_cancel₀ hεne
    rw [← hsmul (L.subtype w₀), ← hsmul (L.subtype z)]
    exact hRw
  have hcong := hyp.peterfalvi_67_centralCommutator_c2_caseA hK hW1 hA hp hHp ρ hzGmem hzG1 hψconst
  rw [← congrFun hξρ (L.subtype z), ← congrFun hξρ 1] at hcong
  have hcong2 := hcong.smul_left hεint
  simp only [← hsmul] at hcong2
  exact hcong2

open scoped OddOrder.AlgInt in
/-- **(6.8.1) `a ∣ c`** (mmd 04.8 L176, the `c ≡ 0 (mod a)` half of "`b ≡ c ≡ 0 (mod a)`").  For
`η ∈ Y` and an `X`-anchor `χ₁ ∈ X(Zc)` of degree `χ₁(1) = a·|W₁|` (`a > 0`, the degree ratio against
the `Y`-degree `|W₁|`), the multiplicity `c = ⟨Res^G_L(η^{τ₁}), χ₁⟩` is an **integer divisible by
`a`**.

This is the (6.7) divisibility step.  The value identity
`restrict_extension_Yset_degree_value_eq_of_frobenius` gives `χ₁(1)·(R(z)−R(1)) = −c·|L|` for
`z ∈ Zc^#` (`R = Res^G_L(η^{τ₁})`); with `χ₁(1) = a|W₁|` and `|L| = |H|·|W₁|`
(`index_H_eq_card_W1` + `index_mul_card`) it becomes `a·(R(z)−R(1)) = −c·|H|`, i.e.
`(R(z)−R(1))/|H| = −c/a`.  The (6.7)-congruence
`restrict_extension_Yset_charValue_cong_of_frobenius` says `(R(z)−R(1))/|H|` is an algebraic
integer;
so the rational `−c/a` is an algebraic integer, hence an integer (`isIntegral_rat_imp_int`), i.e.
`a ∣ c`.  (`c ∈ ℤ` because `R ∈ ZIrr L` and `χ₁` is irreducible, `mem_ZIrr_inner_int`.) -/
theorem dvd_inner_restrict_extension_Yset_of_frobenius
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    (hHnonab : _root_.commutator ↥H ≠ ⊥)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) (hHp : IsPGroup p ↥H)
    {η : ClassFunction ↥L ℂ} (hη : η ∈ hyp.Yset)
    {χ₁ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Xset hyp.centralCommutator)
    {a : ℕ} (ha_pos : 0 < a) (ha : χ₁ 1 = (a : ℂ) * (Nat.card hyp.W1 : ℂ)) :
    ∃ cc : ℤ,
      ClassFunction.inner (ClassFunction.restrict L (hyp.coherentYset.extension η)) χ₁ = (cc : ℂ)
        ∧ (a : ℤ) ∣ cc := by
  classical
  set R := ClassFunction.restrict L (hyp.coherentYset.extension η) with hRdef
  -- `c := ⟨R, χ₁⟩` is an integer (`R ∈ ZIrr L`, `χ₁` irreducible).
  have hηtZ : hyp.coherentYset.extension η ∈ ZIrr G :=
    hyp.coherentYset.extension_mem_ZIrr η (Submodule.subset_span hη)
  have hRZ : R ∈ ZIrr (↥L) := OddOrder.RepresentationTheory.ClassFunction.restrict_mem_ZIrr L hηtZ
  have hχ₁irr : IsIrreducibleCharacter χ₁ :=
    hyp.isIrreducibleCharacter_of_mem_Xset_of_frobenius hF hχ₁
  obtain ⟨cc, hcc⟩ := OddOrder.RepresentationTheory.mem_ZIrr_inner_int
    (⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) hRZ
  rw [show ((⟨χ₁, hχ₁irr⟩ : IrreducibleCharacter ↥L) : ClassFunction ↥L ℂ) = χ₁ from rfl] at hcc
  refine ⟨cc, hcc, ?_⟩
  have hW1ne : (Nat.card hyp.W1 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hane : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha_pos.ne'
  have hHne : (Nat.card ↥H : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  -- pick `z ∈ Zc^#`.
  obtain ⟨⟨z, hz⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (hyp.centralCommutator_ne_bot hHnonab)
  have hz1 : z ≠ 1 := fun h => hzne (Subtype.ext h)
  -- value identity: `χ₁(1)·(R z − R 1) = −c·|L|`, with `χ₁(1) = a|W₁|`, `c = cc`, `|L| = |H||W₁|`.
  have hval := hyp.restrict_extension_Yset_degree_value_eq_of_frobenius
    hF hHnonab hp hp3 hHp hη hχ₁ hz hz1
  rw [← hRdef, hcc, ha] at hval
  have hLcard : (Nat.card ↥L : ℂ) = (Nat.card ↥H : ℂ) * (Nat.card hyp.W1 : ℂ) := by
    have h := Subgroup.index_mul_card H
    rw [hyp.index_H_eq_card_W1] at h
    have hc : ((Nat.card hyp.W1 * Nat.card ↥H : ℕ) : ℂ) = (Nat.card ↥L : ℂ) := by rw [h]
    push_cast at hc; linear_combination -hc
  rw [hLcard] at hval
  -- cancel `|W₁|`: `a·(R z − R 1) = −c·|H|`.
  have haD : (a : ℂ) * (R z - R 1) = -(cc : ℂ) * (Nat.card ↥H : ℂ) := by
    apply mul_left_cancel₀ hW1ne
    linear_combination hval
  -- the (6.7)-congruence: `(R z − R 1)/|H|` is an algebraic integer.
  have hcong := hyp.restrict_extension_Yset_charValue_cong_of_frobenius
    hF hHnonab hp hp3 hHp hη hz hz1
  rw [← hRdef, OddOrder.AlgInt.cong_def, Int.cast_natCast] at hcong
  -- `c/a = −((R z − R 1)/|H|)`, so `c/a` is an algebraic integer.
  have hccdiv : (cc : ℂ) / (a : ℂ) = -((R z - R 1) / (Nat.card ↥H : ℂ)) := by
    rw [← neg_div, div_eq_div_iff hane hHne]
    linear_combination haD
  have hintc : IsIntegral ℤ ((cc : ℂ) / (a : ℂ)) := by rw [hccdiv]; exact hcong.neg
  -- a rational algebraic integer is an integer ⟹ `a ∣ c`.
  have hqcast : (((cc : ℚ) / (a : ℚ) : ℚ) : ℂ) = (cc : ℂ) / (a : ℂ) := by push_cast; ring
  obtain ⟨n, hn⟩ := OddOrder.RepresentationTheory.isIntegral_rat_imp_int
    (q := (cc : ℚ) / (a : ℚ)) (by rw [hqcast]; exact hintc)
  rw [hqcast, div_eq_iff hane] at hn
  refine ⟨n, ?_⟩
  have : (cc : ℂ) = ((a : ℤ) * n : ℤ) := by rw [hn]; push_cast; ring
  exact_mod_cast this

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


