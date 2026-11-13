-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy
-- name    : OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T14:00:32.745211+00:00
-- url     : https://prove2.me/theorems/db013626-c5bd-4e10-83a3-0d75d5b3d978
-- title:
--   Peterfalvi (12.4): constancy of $\rho$ (coherence pins onward)
-- statement:
--   The second half of the $\rho$-constancy development for type I maximal subgroups, starting from the coherence pins of Peterfalvi (12.4), including (5.5) for coherent extensions.
--
--   Main declarations: `constituent_diff_tau_mem_span` (Peterfalvi (12.4), pin (a)); `coherent_extension_mem_span_imageFamily` (Peterfalvi (5.5)); `coherent_extension_constituent_mem_span_Rset` (Peterfalvi (5.5) → (12.2.b), constituent form); `coherent_extension_constituent_orthogonal_Rset_of_nonconjugate` (Peterfalvi (5.5) + (12.3): the L-side Dade character `ψ = χ_L^{τ₁}` is orthogonal to `R(χ_M)`).
--
--   The bundle also proves 3 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S14_MaximalI/RhoConstancy.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S14_MaximalI/RhoConstancy.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancyDecomposition

namespace OddOrder.Peterfalvi.S14

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

variable {G : Type*} [Group G]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (a)** (coherence): for constituents `φ₁, φ₂ ∈ S(χ)`, the Dade image
`(φ₁ − φ₂)^τ` lies in `ℤ[R(χ)]`.

Proof (the (1.4) coherence content, now genuine): the conjugate-closed constituent set `T` is a
single coherent family under `τ` (`exists_uniform_image_of_constituents`), giving a uniform sign
`ε` and injection `μ : T → Irr G` with `τ(φ₁ − φ₂) = ε·(μ φ₁ − μ φ₂)`.  For each constituent `φ`,
the two presentations of `τ(φ − φ̄)` — the global `ε·(μ φ − μ φ̄)` and the per-`φ` block
`R₁(φ)`'s `ε_φ·(μ_φ − ν_φ)` (`R1cdi.image_eq`) — must share their irreducible pair
(`irreducibleCharacter_signed_difference_uniqueness`), so `μ φ ∈ {μ_φ, ν_φ} ⊆ ℤ[R(χ)]`
(`R1cdi_muNu_mem_span_Rset`).  Hence `μ φ₁, μ φ₂ ∈ ℤ[R(χ)]` and `τ(φ₁ − φ₂) ∈ ℤ[R(χ)]`. -/
theorem constituent_diff_tau_mem_span {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) ∈
      Submodule.span ℤ (Rset dχ) := by
  have := hyp.finiteG
  classical
  obtain ⟨ε, μ, hε, hμinj, hμrel⟩ := exists_uniform_image_of_constituents hyp dχ
  set T := dχ.constituents ∪ dχ.constituents.image (IrreducibleCharacter.conjPerm ↥L) with hTdef
  -- reconciliation: every `μ φ` (for a constituent `φ`) lies in `ℤ[R(χ)]`.
  have hmu_mem : ∀ φ ∈ dχ.constituents, (μ φ : ClassFunction G ℂ) ∈ Submodule.span ℤ (Rset dχ) := by
    intro φ hφ
    have hφT : φ ∈ T := Finset.mem_union_left _ hφ
    have hconjT : IrreducibleCharacter.conjPerm ↥L φ ∈ T :=
      Finset.mem_union_right _ (Finset.mem_image_of_mem _ hφ)
    set cdi := R1cdi dχ hφ with hcdi
    -- global vs per-`φ` presentation of `τ(φ − φ̄)`.
    have hglob := hμrel φ hφT (IrreducibleCharacter.conjPerm ↥L φ) hconjT
    rw [IrreducibleCharacter.conjPerm_apply_coe] at hglob
    have hcomb : ε • ((μ φ : ClassFunction G ℂ)
          - (μ (IrreducibleCharacter.conjPerm ↥L φ) : ClassFunction G ℂ))
        = cdi.sign • ((cdi.muClassFunction) - (cdi.nuClassFunction)) :=
      hglob.symm.trans cdi.image_eq
    have hcombℂ : (ε : ℂ) • ((μ φ : ClassFunction G ℂ)
          - (μ (IrreducibleCharacter.conjPerm ↥L φ) : ClassFunction G ℂ))
        = (cdi.sign : ℂ) • (((cdi.mu : ClassFunction G ℂ)) - ((cdi.nu : ClassFunction G ℂ))) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul]; exact hcomb
    -- the two distinct-pair hypotheses.
    have hφne : φ ≠ IrreducibleCharacter.conjPerm ↥L φ := fun h =>
      dχ.not_real φ hφ ((IrreducibleCharacter.conjPerm_eq_self_iff φ).mp h.symm)
    have hab : μ φ ≠ μ (IrreducibleCharacter.conjPerm ↥L φ) := fun h =>
      hφne (hμinj (Finset.mem_coe.mpr hφT) (Finset.mem_coe.mpr hconjT) h)
    have hs : (ε : ℂ) ≠ 0 := by rcases hε with h | h <;> simp [h]
    rcases irreducibleCharacter_signed_difference_uniqueness hab cdi.distinct hs hcombℂ with
      ⟨h1, _, _⟩ | ⟨h1, _, _⟩
    · rw [h1]; exact (R1cdi_muNu_mem_span_Rset dχ hφ).1
    · rw [h1]; exact (R1cdi_muNu_mem_span_Rset dχ hφ).2
  -- assemble.
  have hφ₁T : φ₁ ∈ T := Finset.mem_union_left _ h₁
  have hφ₂T : φ₂ ∈ T := Finset.mem_union_left _ h₂
  rw [hμrel φ₁ hφ₁T φ₂ hφ₂T]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (hmu_mem φ₁ h₁) (hmu_mem φ₂ h₂))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5)** (`χ^{τ₁} ∈ ℤ[R(χ)]` for a coherent extension).  For the coherent
extension `coh` of the type-I family `S` of a `Hypothesis L`, and a non-real member `χ ∈ S`
(as an `IrreducibleCharacter`) whose difference `χ − χ̄` is supported in the Dade domain `A(L)`
and which is orthogonal to its conjugate (`⟨χ, χ̄⟩ = 0`), the Dade character `ψ = χ^{τ₁} =
coh.extension χ` lies in the integral span of the orthonormal image family
`R(χ) = dadeOrthonormalCharacterImageFamilyOfDiff … χ`.

This is the `ψ = 0` case of the (5.4) decomposition `(χ − ψ)^{τ₁} = X − Y`.  Taking the coherent
extension as the auxiliary isometry `τ₁`, its `ZIrr`-codomain (`extension_mem_ZIrr`, the
virtual-character property the general **unsupported** `X`-family `Ind θ` lacks — `χ(1) ≠ 0`)
supplies the single number-theoretic input to `CharacterPsiDecomposition.ofProjection`; then
`eq_sum_of_psi_eq_zero` forces `Y = 0`, so `χ^{τ₁} = X = ∑_{α ∈ E ⊆ R(χ)} α ∈ ℤ[R(χ)]`.  This is
the L-side `ψ ∈ ℤ[R(χ_L)]` which, combined with the (12.3) cross-`L` orthogonality
`R(χ_L) ⊥ R(χ_M)` (`nonconjugate_typeI_R_orthogonal`), yields `ψ ⊥ R(χ_M)` — the `horth` input of
the (12.14) coset-constancy `psi_constant_on_xK`. -/
theorem coherent_extension_mem_span_imageFamily {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    (χ : IrreducibleCharacter ↥L)
    (hχmem : (χ : ClassFunction ↥L ℂ) ∈ hyp.Sset)
    (hχreal : ¬ ClassFunction.IsReal (χ : ClassFunction ↥L ℂ))
    (hdiffsupp : ((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L hyp.typeI) L)
    (hχχbar : ClassFunction.inner (χ : ClassFunction ↥L ℂ) (χ : ClassFunction ↥L ℂ).conj = 0) :
    coh.extension (χ : ClassFunction ↥L ℂ) ∈
      Submodule.span ℤ
        ((OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
          hyp.dadeData.dade χ hχreal hdiffsupp).imageSet :
          Set (ClassFunction G ℂ)) := by
  classical
  set imF := OddOrder.Peterfalvi.S07.dadeOrthonormalCharacterImageFamilyOfDiff
    hyp.dadeData.dade χ hχreal hdiffsupp with himF
  -- membership of `χ`, `χ̄`, and `χ − χ̄` in the coherent lattice `ℤ[S]`.
  have hχ_zSpan : (χ : ClassFunction ↥L ℂ) ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span hχmem
  have hχbar_mem : (χ : ClassFunction ↥L ℂ).conj ∈ hyp.Sset :=
    (Sset_closedUnderConjugate hyp).conj_mem hχmem
  have hχbar_zSpan : (χ : ClassFunction ↥L ℂ).conj ∈ OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.subset_span hχbar_mem
  have hdiff_zSpan : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj ∈
      OddOrder.Peterfalvi.S07.zSpan hyp.Sset :=
    Submodule.sub_mem _ hχ_zSpan hχbar_zSpan
  -- `χ − χ̄` is supported in `A(L)` (sign flip of the given `χ̄ − χ` support).
  have hdiffsupp' : ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj).support ⊆
      hyp.A := by
    have heq : (χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj
        = -((χ : ClassFunction ↥L ℂ).conj - (χ : ClassFunction ↥L ℂ)) := by abel
    rw [heq, ClassFunction.support_neg]
    exact hdiffsupp
  -- the sublattice `ℤ[χ − χ̄, χ − 0]` sits inside `ℤ[S]`.
  have hsub : OddOrder.Peterfalvi.S07.zSpan (L := ↥L)
        {(χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj,
          (χ : ClassFunction ↥L ℂ) - 0} ≤
      OddOrder.Peterfalvi.S07.zSpan hyp.Sset := by
    change Submodule.span ℤ _ ≤ Submodule.span ℤ _
    rw [Submodule.span_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact hdiff_zSpan
    · rw [sub_zero]; exact hχ_zSpan
  -- build the (5.4) decomposition with `ψ = 0` and `τ₁ = coh.extension`, forcing `Y = 0`.
  obtain ⟨-, hτ1χ, E, hEsub, hXsum, -⟩ :=
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.eq_sum_of_psi_eq_zero
      (OddOrder.Peterfalvi.S07.CharacterPsiDecomposition.ofProjection (ψ := 0) imF coh.extension
        (fun φ ζ hφ hζ => coh.extension_inner_eq φ ζ (hsub hφ) (hsub hζ))
        (coh.extends_on_supported
          ((χ : ClassFunction ↥L ℂ) - (χ : ClassFunction ↥L ℂ).conj)
          ⟨hdiff_zSpan, hdiffsupp'⟩)
        (by rw [sub_zero]; exact coh.extension_mem_ZIrr _ hχ_zSpan)
        (ClassFunction.inner_zero_right _)
        (ClassFunction.inner_zero_right _)
        hχχbar)
  -- `coh.extension χ = χ^{τ₁} = X = ∑_{α ∈ E} α ∈ ℤ[R(χ)]`.
  have hgoal : coh.extension (χ : ClassFunction ↥L ℂ) = ∑ α ∈ E, α := hτ1χ.trans hXsum
  rw [hgoal]
  exact Submodule.sum_mem _ fun α hα => Submodule.subset_span (Finset.mem_coe.mpr (hEsub hα))

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) → (12.2.b), constituent form**: the coherent Dade image `χ^{τ₁} =
coh.extension φ` of a constituent `φ ∈ S(χ)` (`data.constituents`) that is itself a member of the
family `S` lies in `ℤ[R(χ)] = Submodule.span ℤ (Rset data)`.

The (5.5) image family `dadeOrthonormalCharacterImageFamilyOfDiff … φ` is *definitionally* the block
`R₁(φ) = R1 data hφ` — both are the `toOrthonormalImage` of the same
`dadeCharacterDifferenceImageOfDiff hyp.dadeData.dade φ (data.not_real φ hφ)
(R1_diffsupp data hφ)` — which is a subfamily of `R(χ) = Rset data`, so
`coherent_extension_mem_span_imageFamily` lands in `ℤ[R(χ)]` after `span_mono`.  The orthogonality
`⟨φ, φ̄⟩ = 0` comes for free from `data.not_real φ hφ` (a non-real irreducible is orthogonal to its
conjugate).  This is the L-side `ψ ∈ ℤ[R(χ_L)]` for the (12.16) witness: the distinguished
`χ_L = Ind θ` is irreducible (Frobenius), so its unique constituent is itself, in `S`. -/
theorem coherent_extension_constituent_mem_span_Rset {L : Subgroup G} [Finite G]
    (hyp : Hypothesis L) (coh : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Sset hyp.A)
    {chi : ClassFunction ↥L ℂ} (data : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ data.constituents)
    (hφmem : (φ : ClassFunction ↥L ℂ) ∈ hyp.Sset) :
    coh.extension (φ : ClassFunction ↥L ℂ) ∈ Submodule.span ℤ (Rset data) := by
  classical
  -- a non-real irreducible is orthogonal to its complex conjugate.
  have hφne : φ ≠ IrreducibleCharacter.conjPerm ↥L φ := fun h =>
    data.not_real φ hφ ((IrreducibleCharacter.conjPerm_eq_self_iff φ).mp h.symm)
  have hχχbar :
      ClassFunction.inner (φ : ClassFunction ↥L ℂ) (φ : ClassFunction ↥L ℂ).conj = 0 := by
    have h0 := irreducibleCharacter_inner_eq_ite φ (IrreducibleCharacter.conjPerm ↥L φ)
    rw [if_neg hφne] at h0
    rwa [IrreducibleCharacter.conjPerm_apply_coe] at h0
  -- (5.5): `coh.extension φ ∈ ℤ[R₁(φ)]`; and `R₁(φ) ⊆ R(χ) = Rset data`.
  have h55 := coherent_extension_mem_span_imageFamily hyp coh φ hφmem
    (data.not_real φ hφ) (R1_diffsupp data hφ) hχχbar
  refine Submodule.span_mono ?_ h55
  intro α hα
  exact ⟨φ, hφ, Finset.mem_coe.mp hα⟩

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (5.5) + (12.3): the L-side Dade character `ψ = χ_L^{τ₁}` is orthogonal to
`R(χ_M)`.**  For two non-conjugate type-I maximal subgroups `L`, `M` and a constituent
`φ_L ∈ S(χ_L)` of the L-side family that is itself a member of `S` (the Frobenius witness case,
where `χ_L = Ind θ` is irreducible), the coherent Dade image `ψ = coh_L.extension φ_L` is orthogonal
to every element of `R(χ_M) = Rset data_M`.

Two ingredients combine: (5.5) `coherent_extension_constituent_mem_span_Rset` puts
`ψ ∈ ℤ[R(χ_L)]`, and (12.3) `nonconjugate_typeI_R_orthogonal` gives the cross-`L` orthogonality
`R(χ_L) ⊥ R(χ_M)`; since `⟨·,·⟩` is conjugate-symmetric and additive, orthogonality of `ψ` to all
of `R(χ_M)` follows from `inner_eq_zero_of_mem_zSpan`.  This is precisely the per-`χ_M` piece of the
`horth` hypothesis that the (12.4)/(12.14) coset-constancy chain (`Sset_coeff_equal`,
`psi_constant_on_xK`) consumes: `ψ` restricted to the `M`-structure has equal coefficients across
`S(χ_M)`, forcing `ψ` constant on the `M_F`-cosets. -/
theorem coherent_extension_constituent_orthogonal_Rset_of_nonconjugate {L M : Subgroup G}
    [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp_L : Hypothesis L)
    (coh_L : OddOrder.Peterfalvi.S07.IsCoherent hyp_L.tau hyp_L.Sset hyp_L.A)
    {chi_L : ClassFunction ↥L ℂ} (data_L : CharacterDecompositionData hyp_L chi_L)
    {φ_L : IrreducibleCharacter ↥L} (hφ_L : φ_L ∈ data_L.constituents)
    (hφ_L_mem : (φ_L : ClassFunction ↥L ℂ) ∈ hyp_L.Sset)
    (hyp_M : Hypothesis M) (hnot_conj : ¬ ∃ g : G, MulAut.conj g • L = M)
    {chi_M : ClassFunction ↥M ℂ} (data_M : CharacterDecompositionData hyp_M chi_M) :
    ∀ α ∈ Rset data_M,
      ClassFunction.inner (coh_L.extension (φ_L : ClassFunction ↥L ℂ)) α = 0 := by
  -- (5.5): `ψ = coh_L.extension φ_L ∈ ℤ[R(χ_L)]`.
  have h55 := coherent_extension_constituent_mem_span_Rset hyp_L coh_L data_L hφ_L hφ_L_mem
  -- (12.3): `R(χ_L) ⊥ R(χ_M)`.
  have horth := nonconjugate_typeI_R_orthogonal hG hyp_L hyp_M hnot_conj data_L data_M
  intro α hα
  -- `α ⊥ R(χ_L)` (conjugate-swap of (12.3)), hence `α ⊥ ℤ[R(χ_L)] ∋ ψ`; conjugate back.
  have hαperp : ∀ β ∈ Rset data_L, ClassFunction.inner α β = 0 := by
    intro β hβ
    rw [inner_conj_symm β α, horth β hβ α hα, star_zero]
  have h0 : ClassFunction.inner α (coh_L.extension (φ_L : ClassFunction ↥L ℂ)) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan hαperp h55
  rw [inner_conj_symm α (coh_L.extension (φ_L : ClassFunction ↥L ℂ)), h0, star_zero]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.5) support input** (the `A1xi12` step of the Coq `o_rpsi_S` proof): the
difference `χ₁ − χ₂` of two **equal-degree** members of `S` vanishes off `H^# = H ∖ {1}` — i.e. at
every `x` with `(x : G) ∉ H` (both `Ind_H^L`-characters vanish off the normal `H = L_F`,
`Sset_vanishes_off_H`) or `x = 1` (equal degree, so `(χ₁ − χ₂)(1) = 0`).  This is the
`xi1 − xi2 ∈ CF(L, H^#)` support hypothesis under which the type-I Dade isometry `τ` acts on the
difference (feeding `constituent_diff_tau_eq_induce` / the `chiRho_adjoint` reciprocity of the
(12.5) Fact-A rebuild). -/
theorem Sset_diff_vanishes_off_H_sharp {L : Subgroup G} (hyp : Hypothesis L)
    {χ₁ χ₂ : ClassFunction ↥L ℂ} (hχ₁ : χ₁ ∈ hyp.Sset) (hχ₂ : χ₂ ∈ hyp.Sset)
    (hdeg : χ₁ (1 : ↥L) = χ₂ (1 : ↥L)) {x : ↥L}
    (hx : (x : G) ∉ hyp.H ∨ x = 1) : (χ₁ - χ₂) x = 0 := by
  rw [ClassFunction.sub_apply]
  rcases hx with hxH | hx1
  · rw [Sset_vanishes_off_H hyp hχ₁ hxH, Sset_vanishes_off_H hyp hχ₂ hxH, sub_zero]
  · subst hx1; rw [hdeg, sub_self]

open scoped Classical in
/-- **General TI-induction self-value** (Isaacs 7.x / Peterfalvi (3.2.c) value half), generalized
from `TICyclicHypothesis.induce_apply_eq_self_of_mem_V` to an arbitrary TI subset.  For a TI subset
`A` relative to `L` (`L ⊆ N_G(A)`, `A ⊆ L`, `IsTISubset A L`) and a class function `α` of `L`
supported in `A`, the induced class function `Ind_L^G α` agrees with `α` on `A`: only the `|L|`
conjugators `x ∈ L` contribute to the induction sum (the others land outside `A`, where `α`
vanishes,
by the TI property), each with value `α(a)`.  This is **pin (b), step 1** — the value-half of the
"Dade map = Ind on the trivial-`H` part" bridge. -/
theorem induce_apply_eq_self_of_mem_tiSubset {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hAL : A ⊆ (L : Set G))
    (hnorm : ∀ x ∈ L, ∀ a ∈ A, x⁻¹ * a * x ∈ A)
    (hTI : OddOrder.GroupTheory.IsTISubset A L)
    (α : ClassFunction ↥L ℂ)
    (hαsupp : α.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A L)
    {a : G} (ha : a ∈ A) :
    ClassFunction.induce L α a = α ⟨a, hAL ha⟩ := by
  classical
  have : Fintype ↥L := Fintype.ofFinite _
  have haL : a ∈ L := hAL ha
  have hterm : ∀ x : G, ClassFunction.induceTerm L α x a
      = if x ∈ L then α ⟨a, haL⟩ else 0 := by
    intro x
    by_cases hx : x ∈ L
    · rw [if_pos hx]
      have haxL : x⁻¹ * a * x ∈ L := hAL (hnorm x hx a ha)
      rw [ClassFunction.induceTerm_of_mem _ haxL]
      have harg : (⟨x⁻¹ * a * x, haxL⟩ : ↥L)
          = ⟨x⁻¹, L.inv_mem hx⟩ * ⟨a, haL⟩ * ⟨x⁻¹, L.inv_mem hx⟩⁻¹ := by
        apply Subtype.ext; simp [inv_inv]
      rw [harg]
      exact α.conj_eq ⟨a, haL⟩ ⟨x⁻¹, L.inv_mem hx⟩
    · rw [if_neg hx]
      by_cases hax : x⁻¹ * a * x ∈ L
      · rw [ClassFunction.induceTerm_of_mem _ hax]
        have hnotA : x⁻¹ * a * x ∉ A := fun hV =>
          hx (by simpa using L.inv_mem (hTI x⁻¹ ⟨a, ha, by simpa using hV⟩))
        by_contra hne
        exact hnotA ((OddOrder.Peterfalvi.S04.mem_supportInSubgroup).mp
          (hαsupp (ClassFunction.mem_support.mpr hne)))
      · rw [ClassFunction.induceTerm_of_not_mem _ hax]
  rw [ClassFunction.induce_apply, Finset.sum_congr rfl (fun x _ => hterm x),
    ← Finset.sum_filter, Finset.sum_const]
  have hcard : (Finset.univ.filter (· ∈ L)).card = Nat.card ↥L := by
    rw [Nat.card_eq_fintype_card]; exact (Fintype.card_subtype _).symm
  rw [hcard, nsmul_eq_mul, ← mul_assoc, invOf_mul_self, one_mul]

open scoped Classical in
/-- **Peterfalvi (12.4) pin (b), step 2**: for a Dade hypothesis with all trivial stabilizers
`∀ a, H(a) = ⊥`, induction `Ind_L^G` (restricted to `CF(L, A)`) **is** the Dade map.  Generalizes
`TICyclicHypothesis.isDadeMap_inducedDadeMap`: the value half is the step-1 self-value
`induce_apply_eq_self_of_mem_tiSubset` (the coset condition collapses to `IsConj a g` since
`h ∈ ⊥`),
the support half is `induce_eq_zero_of_not_conjugatesIntoSet` (induced functions vanish off the
`A`-conjugates, which are the Dade support when `H = ⊥`).  Via `IsDadeMap.unique` this pins the
abstract Dade map to `Ind_L^G` on `CF(L, A)`. -/
theorem isDadeMap_induce_of_forall_H_eq_bot {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L)
    (hH : ∀ a, hyp.H a = ⊥) :
    OddOrder.Peterfalvi.S04.IsDadeMap hyp
      (fun α => ClassFunction.induce L (α : ClassFunction ↥L ℂ)) where
  map_eq_of_isConj_hCoset := by
    intro α g a h hh hconj
    have hh1 : h = 1 := Subgroup.mem_bot.mp (by rw [← hH a]; exact hh)
    subst hh1
    have hga : IsConj a.1 g := by simpa using hconj
    change ClassFunction.induce L (α : ClassFunction ↥L ℂ) g = _
    rw [← (ClassFunction.induce L (α : ClassFunction ↥L ℂ)).of_isConj hga]
    exact induce_apply_eq_self_of_mem_tiSubset hyp.subset_L
      (fun x hx a' ha' => by simpa using hyp.L_normalizes_A ⟨x⁻¹, L.inv_mem hx⟩ ha')
      (hyp.isTISubset_of_forall_H_eq_bot hH) _
      (ClassFunction.mem_supportedSubmodule.mp α.2) a.2
  map_eq_zero_of_not_mem_dadeSupport := by
    intro α g hg
    change ClassFunction.induce L (α : ClassFunction ↥L ℂ) g = 0
    refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet
      (ClassFunction.mem_supportedSubmodule.mp α.2) (fun hgin => hg ?_)
    rw [hyp.dadeSupport_eq_conjugatesOfSet_of_forall_H_eq_bot hH]
    obtain ⟨x, hx, hxV⟩ := hgin
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hxV
    exact Group.mem_conjugatesOfSet_iff.mpr ⟨x⁻¹ * g * x, hxV, isConj_iff.mpr ⟨x, by group⟩⟩

/-- **Peterfalvi (12.4) pin (b), step 3** (restriction assembly): if a sub-support `A₁ ⊆ A` carries
only trivial Dade stabilizers (`(hyp.restrict …).H a = ⊥`), then on `A₁`-supported functions the
abstract Dade map of `hyp` **is** induction `Ind_L^G`.  The restricted hypothesis has `H = ⊥`, so
its
Dade map is `Ind_L^G` (step 2 + `IsDadeMap.unique`); `Hypothesis.dadeMap_restrict_apply` identifies
it with `hyp.dadeMap` of the included function. -/
theorem dadeMap_eq_induce_of_supported_on_trivial_H {A : Set G} {L : Subgroup G}
    [Fintype G] [Invertible (Nat.card L : ℂ)]
    (hyp : OddOrder.Peterfalvi.S04.Hypothesis G A L) {A₁ : Set G} (hA₁A : A₁ ⊆ A)
    (hA₁norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, (hyp.restrict hA₁A hA₁norm).H a = ⊥)
    (α : OddOrder.Peterfalvi.S04.SupportedClassFunctions (G := G) ℂ A₁ L) :
    hyp.dadeMap (OddOrder.Peterfalvi.S04.SupportedClassFunctions.inclusion
        (G := G) (k := ℂ) (L := L) hA₁A α)
      = ClassFunction.induce L (α : ClassFunction ↥L ℂ) := by
  have h1 := OddOrder.Peterfalvi.S04.IsDadeMap.unique
    ((hyp.restrict hA₁A hA₁norm).isDadeMap_dadeMap (k := ℂ))
    (isDadeMap_induce_of_forall_H_eq_bot (hyp.restrict hA₁A hA₁norm) hH₁)
  rw [← hyp.dadeMap_restrict_apply hA₁A hA₁norm α]
  exact congrFun h1 α

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4) pin (b), type-I bridge**: for a type-I maximal `L`, on a class function `f`
supported in a trivial-`H` sub-support `A₁ ⊆ A(L)` (an `L`-invariant subset on which the type-I Dade
stabilizers vanish), the Dade isometry `τ` acts as induction `Ind_L^G`.  This instantiates the
general step-3 bridge `dadeMap_eq_induce_of_supported_on_trivial_H` at the type-I Dade map `hyp.tau`
(via `dadeIntegralCharacterMap_apply_of_support`, and `inclusion` to widen the support from
`A₁`). -/
theorem typeI_tau_eq_induce_of_supported_trivial_H {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {A₁ : Set G} (hA₁A : A₁ ⊆ hyp.ambientA)
    (hA₁norm : ∀ (l : L) ⦃a : G⦄, a ∈ A₁ → (l : G) * a * (l : G)⁻¹ ∈ A₁)
    (hH₁ : ∀ a, (hyp.dadeData.dade.restrict hA₁A hA₁norm).H a = ⊥)
    {f : ClassFunction ↥L ℂ}
    (hf : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup A₁ L) :
    hyp.tau f = ClassFunction.induce L f := by
  have := hyp.finiteG
  have hfA : f.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L :=
    hf.trans (OddOrder.Peterfalvi.S04.supportInSubgroup_mono hA₁A)
  have h1 : hyp.tau f = hyp.dadeData.dade.dadeMap (k := ℂ)
      ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hfA⟩ :=
    OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap_apply_of_support hyp.dadeData.dade
      (hyp.dadeData.dade.fullDadeIsometryData) hfA
  rw [h1]
  -- `⟨f, hfA⟩` is defeq to `inclusion hA₁A ⟨f, hf⟩` (same carrier `f`), so step 3 applies directly.
  exact dadeMap_eq_induce_of_supported_on_trivial_H hyp.dadeData.dade hA₁A hA₁norm hH₁
    ⟨f, (ClassFunction.mem_supportedSubmodule).mpr hf⟩

/-- The escaping-centralizer set `{a ∈ X : ¬ C_G(a) ≤ M}` is `M`-conjugation invariant when `X` is
(`C_G(gag⁻¹) = g·C_G(a)·g⁻¹` and `g ∈ M` normalizes `M`).  The `L`-invariance of the trivial-`H`
sub-support `A(L) ∖ escaping` rests on this. -/
private theorem escaping_conj_mem_iff {M : Subgroup G} {X : Set G} {g x : G}
    (hg : g ∈ M) (hmem : g * x * g⁻¹ ∈ X ↔ x ∈ X) :
    g * x * g⁻¹ ∈ escapingCentralizerSet M X ↔ x ∈ escapingCentralizerSet M X := by
  have hcent : (Subgroup.centralizer ({g * x * g⁻¹} : Set G) ≤ M)
      ↔ (Subgroup.centralizer ({x} : Set G) ≤ M) := by
    rw [← conj_smul_centralizer_singleton]
    conv_lhs => rw [← (conj_smul_eq_self_of_mem_normalizer (Subgroup.le_normalizer hg) :
      MulAut.conj g • M = M)]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff
  simp only [escapingCentralizerSet, Set.mem_ofPred_eq, hmem, hcent]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Constituents of `χ = Ind_K^L θ` (`K = (L_F).subgroupOf L ⊴ L`) have equal restriction to `K`**
(the multiplicity-one case of Clifford's theorem [Is] 6.2, character level).  Two constituents
`φ₁, φ₂ ∈ S(χ)` both occur in `χ = Ind_K^L θ` with multiplicity one, so both lie over `θ`; by
Clifford single-orbit (`restrictionConstituentsSingleOrbit_of_isIrreducible`) the constituents of
`Res_K φᵢ` are exactly the `L`-orbit of `θ`, each with the common multiplicity one, whence
`Res_K φ₁ = Res_K φ₂`.  Computed at the inner-product level via Fourier: for every `ψ ∈ Irr K`,
`⟨Res_K φᵢ, ψ⟩ = ⟨φᵢ, Ind_K ψ⟩` (Frobenius) is `1` when `ψ` is `L`-conjugate to `θ`
(`Ind_K ψ = Ind_K θ = χ`, multiplicity one) and `0` otherwise (single-orbit), independently of `i`.
This is the [Is] 6.2 input Peterfalvi (12.4) cites for `Supp(φ₁ − φ₂) ⊆ A(L) − H^#`. -/
theorem restrict_eq_of_mem_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ₁ : ClassFunction ↥L ℂ)
      = ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ₂ : ClassFunction ↥L ℂ) := by
  have := hyp.finiteG
  classical
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  set K := (hyp.typeI.typeF.H).subgroupOf L with hKdef
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := dχ.chi_mem
  -- Frobenius reciprocity: `⟨φ, Ind_K ψ⟩ = ⟨Res_K φ, ψ⟩`.
  have hfrob : ∀ (φ : IrreducibleCharacter ↥L) (ψ : IrreducibleCharacter ↥K),
      ClassFunction.inner (φ : ClassFunction ↥L ℂ) (ClassFunction.induce K (ψ : ClassFunction ↥K ℂ))
        = ClassFunction.inner (ClassFunction.restrict K (φ : ClassFunction ↥L ℂ))
          (ψ : ClassFunction ↥K ℂ) := by
    intro φ ψ
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ClassFunction.inner_induce_eq_inner_restrict,
      OddOrder.RepresentationTheory.inner_conj_symm, star_star]
  -- multiplicity-one: `⟨φ, χ⟩ = 1` for a constituent `φ`.
  have hmult : ∀ φ ∈ dχ.constituents, ClassFunction.inner (φ : ClassFunction ↥L ℂ) chi = 1 := by
    intro φ hφ
    rw [dχ.decomp, inner_sum_right,
      Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
        rw [irreducibleCharacter_inner, if_neg (Ne.symm hne)]),
      irreducibleCharacter_inner, if_pos rfl]
  -- per-`ψ` value of `⟨Res_K φ, ψ⟩`, independent of the constituent `φ`.
  have hval : ∀ φ ∈ dχ.constituents, ∀ ψ : IrreducibleCharacter ↥K,
      ClassFunction.inner (ClassFunction.restrict K (φ : ClassFunction ↥L ℂ))
          (ψ : ClassFunction ↥K ℂ)
        = if (∃ g : ↥L, IrreducibleCharacter.conjBy g θ = ψ) then (1 : ℂ) else 0 := by
    intro φ hφ ψ
    rw [← hfrob φ ψ]
    by_cases hc : ∃ g : ↥L, IrreducibleCharacter.conjBy g θ = ψ
    · rw [if_pos hc]
      obtain ⟨g, rfl⟩ := hc
      rw [IrreducibleCharacter.coe_conjBy, ClassFunction.induce_conjBy_eq, ← hchi_eq]
      exact hmult φ hφ
    · rw [if_neg hc]
      by_contra hne
      refine hc ?_
      have hoθ : IrreducibleCharacter.LiesOver K φ θ := by
        rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def,
          ← hfrob φ θ, ← hchi_eq, hmult φ hφ]
        exact one_ne_zero
      have hoψ : IrreducibleCharacter.LiesOver K φ ψ := by
        rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def, ← hfrob φ ψ]
        exact hne
      exact (restrictionConstituentsSingleOrbit_of_isIrreducible φ).exists_conj hoθ hoψ
  -- Fourier: equal inner products with every irreducible `ψ ∈ Irr K` force equality.
  rw [← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict K (φ₁ : ClassFunction ↥L ℂ)),
      ← OddOrder.RepresentationTheory.sum_inner_irreducibleCharacter_smul
        (ClassFunction.restrict K (φ₂ : ClassFunction ↥L ℂ))]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [hval φ₁ h₁ ψ, hval φ₂ h₂ ψ]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the §8 support obligation** ([Is] 6.2 + (8.12.a)): for constituents
`φ₁, φ₂ ∈ S(χ)`, the difference `φ₁ − φ₂` is supported on the **non-escaping** part of `A(L)`,
`A₁ = {a ∈ A(L) : C_G(a) ≤ L}` (= `A(L) − H^#`, exactly where the type-I Dade stabilizers vanish).
By [Is] 6.2 `Res_H φ₁ = Res_H φ₂` (`restrict_eq_of_mem_constituents`, the multiplicity-one Clifford
restriction), so `φ₁ − φ₂` vanishes on `H`; each `φᵢ` is supported on `A(L) ∪ {1}` (carrier
`supported`) and the difference cancels the value at `1` (equal degree).  The escaping points of
`A(L)` lie in `A₁ = H^#` ((8.13.b) `escaping_typeIA_mem_A1`), so the difference vanishes there. -/
theorem constituent_diff_support_subset_nonescaping [Finite G] {L : Subgroup G}
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup
        (hyp.ambientA \ escapingCentralizerSet L hyp.ambientA) L := by
  have := hyp.finiteG
  classical
  have hres := restrict_eq_of_mem_constituents hyp dχ h₁ h₂
  intro x hx
  rw [ClassFunction.mem_support] at hx
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup, Set.mem_sdiff]
  -- `x` lies in the support of `φ₁` or `φ₂`, hence in `A(L) ∪ {1}`.
  have hxsupp : x ∈ OddOrder.Peterfalvi.S04.supportInSubgroup hyp.ambientA L ∪ ({1} : Set ↥L) := by
    rcases ne_or_eq ((φ₁ : ClassFunction ↥L ℂ) x) 0 with h | h
    · exact dχ.supported φ₁ h₁ (ClassFunction.mem_support.mpr h)
    · refine dχ.supported φ₂ h₂ (ClassFunction.mem_support.mpr ?_)
      intro h2
      exact hx (by rw [ClassFunction.sub_apply, h, h2, sub_zero])
  -- `x ≠ 1`: the difference vanishes at `1` by equal degree.
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact hx (by rw [ClassFunction.sub_apply, ← dχ.equal_degree φ₁ h₁ φ₂ h₂, sub_self])
  have hxAmem : (x : G) ∈ hyp.ambientA := by
    rcases hxsupp with h | h
    · exact OddOrder.Peterfalvi.S04.mem_supportInSubgroup.mp h
    · exact absurd (Set.mem_singleton_iff.mp h) hx1
  refine ⟨hxAmem, fun hesc => ?_⟩
  -- an escaping point of `A(L)` lies in `A₁ = H^#`, so in `H`, where the two restrictions agree.
  have hxA1 : (x : G) ∈ A1 L PeterfalviType.I :=
    OddOrder.Peterfalvi.S10.escaping_typeIA_mem_A1 hG hyp.maximal hyp.typeI hesc
  have hxH : (x : G) ∈ hyp.typeI.typeF.H := by
    rw [hyp.typeI.typeF.H_eq]
    have hmem : (x : G) ∈ OddOrder.GroupTheory.sharpSubgroup (maxNilpotentNormalHall L) := hxA1
    exact ((Set.mem_sdiff _).mp hmem).1
  have hxK : x ∈ (hyp.typeI.typeF.H).subgroupOf L := Subgroup.mem_subgroupOf.mpr hxH
  refine hx ?_
  have hev : ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (φ₁ : ClassFunction ↥L ℂ) ⟨x, hxK⟩
      = ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L)
        (φ₂ : ClassFunction ↥L ℂ) ⟨x, hxK⟩ := by rw [hres]
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply] at hev
  rw [ClassFunction.sub_apply, hev, sub_self]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
set_option backward.isDefEq.respectTransparency false in
/-- **Peterfalvi (12.4), pin (b)** ([Is] 7.7 + (8.12.c) + [Is] 6.2): for constituents
`φ₁, φ₂ ∈ S(χ)`,
the Dade isometry acts as induction on the difference, `(φ₁ − φ₂)^τ = Ind_L^G(φ₁ − φ₂)`.

Proof (now genuine, modulo the §8 support obligation): `φ₁ − φ₂` is supported on the non-escaping
part `A₁ = {a ∈ A(L) : C_G(a) ≤ L}` (`constituent_diff_support_subset_nonescaping`), which is
`L`-invariant (`escaping_conj_mem_iff` + `A(L)` `L`-invariant) and carries only trivial Dade
stabilizers (`ftSupportKernel = ⊥` off the escaping set, via `H_eq_ftSupportKernel`).  On such a
trivial-`H` support the type-I Dade isometry coincides with `Ind_L^G`
(`typeI_tau_eq_induce_of_supported_trivial_H`, i.e. pin (b) steps 1–3 + the restriction
assembly). -/
theorem constituent_diff_tau_eq_induce {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    hyp.tau ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) =
      ClassFunction.induce L ((φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ)) := by
  have hmem : ∀ (l : L) (a : G), ((l : G) * a * (l : G)⁻¹ ∈ hyp.ambientA ↔ a ∈ hyp.ambientA) := by
    intro l a
    refine ⟨fun h => ?_, fun h => hyp.dadeData.dade.L_normalizes_A l h⟩
    have h2 := hyp.dadeData.dade.L_normalizes_A l⁻¹ h
    have h3 : a ∈ typeIA L hyp.typeI := by simpa [Subgroup.coe_inv, mul_assoc] using h2
    exact h3
  have hA₁A : hyp.ambientA \ escapingCentralizerSet L hyp.ambientA ⊆ hyp.ambientA :=
    Set.sdiff_subset
  have hA₁norm : ∀ (l : L) ⦃a : G⦄,
      a ∈ hyp.ambientA \ escapingCentralizerSet L hyp.ambientA →
      (l : G) * a * (l : G)⁻¹ ∈ hyp.ambientA \ escapingCentralizerSet L hyp.ambientA := by
    intro l a ha
    exact ⟨hyp.dadeData.dade.L_normalizes_A l ha.1,
      fun hesc => ha.2 ((escaping_conj_mem_iff l.2 (hmem l a)).mp hesc)⟩
  have hH₁ : ∀ a, (hyp.dadeData.dade.restrict hA₁A hA₁norm).H a = ⊥ := by
    intro a
    rw [OddOrder.Peterfalvi.S04.Hypothesis.restrict_H, hyp.dadeData.H_eq_ftSupportKernel]
    exact OddOrder.Peterfalvi.S10.ftSupportKernel_eq_bot_of_not_escaping a.2.2
  exact typeI_tau_eq_induce_of_supported_trivial_H hyp hA₁A hA₁norm hH₁
    (constituent_diff_support_subset_nonescaping hG hyp dχ h₁ h₂)

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), coherence → coefficient-equality bridge** (genuine).  If `ψ ⊥ R(χ)`, then
`Res_L ψ` has the *same* coefficient on every constituent of `χ`: `⟨Res_L ψ, φ₁⟩ = ⟨Res_L ψ, φ₂⟩`
for `φ₁, φ₂ ∈ S(χ)`.  Proof: `⟨Res_L ψ, φ₁ − φ₂⟩ = ⟨ψ, Ind_L^G(φ₁ − φ₂)⟩ = ⟨ψ, (φ₁ − φ₂)^τ⟩`
(Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry + pin (b)), and this is `0` because
`(φ₁ − φ₂)^τ ∈ ℤ[R(χ)]` (pin (a)) and `ψ ⊥ R(χ)` (`inner_eq_zero_of_mem_zSpan`).  This is the
genuine
content by which `ψ ⊥ R(χ)` forces the `∪S(χ)`-part of `Res_L ψ` to be `β = ∑_χ c_χ·χ ∈ ℂ[S]`. -/
theorem Sset_coeff_equal {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (dχ : CharacterDecompositionData hyp chi)
    {psi : ClassFunction G ℂ} (horth : ∀ α ∈ Rset dχ, ClassFunction.inner psi α = 0)
    {φ₁ φ₂ : IrreducibleCharacter ↥L} (h₁ : φ₁ ∈ dχ.constituents) (h₂ : φ₂ ∈ dχ.constituents) :
    ClassFunction.inner (ClassFunction.restrict L psi) (φ₁ : ClassFunction ↥L ℂ)
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₂ : ClassFunction ↥L ℂ) := by
  have := hyp.finiteG
  set f : ClassFunction ↥L ℂ :=
    (φ₁ : ClassFunction ↥L ℂ) - (φ₂ : ClassFunction ↥L ℂ) with hf
  -- `⟨ψ, τ f⟩ = 0`: `τ f ∈ ℤ[R(χ)]` (pin a) and `ψ ⊥ R(χ)`.
  have hψτ : ClassFunction.inner psi (hyp.tau f) = 0 :=
    OddOrder.Peterfalvi.S07.IntegralCharacterMap.inner_eq_zero_of_mem_zSpan horth
      (constituent_diff_tau_mem_span hyp dχ h₁ h₂)
  -- `⟨f, Res_L ψ⟩ = ⟨Ind_L^G f, ψ⟩ = ⟨τ f, ψ⟩ = star⟨ψ, τ f⟩ = 0`.
  have hfres : ClassFunction.inner f (ClassFunction.restrict L psi) = 0 := by
    rw [← ClassFunction.inner_induce_eq_inner_restrict L f psi,
      ← constituent_diff_tau_eq_induce hG hyp dχ h₁ h₂,
      inner_conj_symm psi (hyp.tau f), hψτ, star_zero]
  -- `⟨Res_L ψ, f⟩ = star⟨f, Res_L ψ⟩ = 0`, then split the difference.
  have hresf : ClassFunction.inner (ClassFunction.restrict L psi) f = 0 := by
    rw [inner_conj_symm f (ClassFunction.restrict L psi), hfres, star_zero]
  rw [hf, ClassFunction.inner_sub_right] at hresf
  exact sub_eq_zero.mp hresf

/-- The "`H ⊆ ker φ`" predicate: the Fitting subgroup `H = L_F` lies in the character kernel of the
irreducible character `φ` of `L`.  The `γ`-components of `Res_L ψ` in (12.4) are exactly those `φ`
with `InHKernel`; they are constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`). -/
def InHKernel {L : Subgroup G} (hyp : Hypothesis L) (φ : IrreducibleCharacter ↥L) : Prop :=
  ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) ⊆
    OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ)

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the off-kernel direction** (genuine): every constituent `φ ∈ S(χ)` of
a
member `χ = Ind_H^L θ ∈ S` (`θ ≠ 1_H`) is off-kernel, `H ⊄ ker φ`.  If `H ⊆ ker φ` then `Res_H φ` is
constant `= φ(1)` on `H` (`= φ(1)·1_H`), so by Frobenius
`⟨χ, φ⟩ = ⟨θ, Res_H φ⟩ = star(φ(1))·⟨θ, 1_H⟩
= 0` (`θ ≠ 1_H`); but `φ` a constituent of `χ` gives `⟨χ, φ⟩ = 1`.  This is the `⊇` inclusion
`S(χ) ⊆ {φ : H ⊄ ker φ}` of the partition `exists_offKernel_constituent_partition`. -/
theorem constituents_not_inHKernel {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {chi : ClassFunction ↥L ℂ} (hχ : chi ∈ hyp.Sset) (dχ : CharacterDecompositionData hyp chi)
    {φ : IrreducibleCharacter ↥L} (hφ : φ ∈ dχ.constituents) : ¬ InHKernel hyp φ := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, hθ_ne, hchi_eq⟩ := hχ
  intro hker
  set K := (hyp.typeI.typeF.H).subgroupOf L with hKdef
  -- `Res_K φ = φ(1) · 1_K` (since `H ⊆ ker φ`, `φ` is constant `= φ(1)` on `K`).
  have hrestrict : ClassFunction.restrict K (φ : ClassFunction ↥L ℂ)
      = OddOrder.Peterfalvi.S03.characterDegree (φ : ClassFunction ↥L ℂ) •
        (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ) := by
    ext k
    rw [ClassFunction.restrict_apply, ClassFunction.smul_apply]
    have hmem : (↑k : ↥L) ∈ OddOrder.Peterfalvi.S03.characterKernel (φ : ClassFunction ↥L ℂ) :=
      hker k.2
    rw [OddOrder.Peterfalvi.S03.mem_characterKernel] at hmem
    simp only [hmem, IrreducibleCharacter.coe_trivialIrreducibleCharacter,
      trivialClassFunction_apply, mul_one]
  -- `⟨χ, φ⟩ = ⟨θ, Res_K φ⟩ = star(φ(1)) · ⟨θ, 1_K⟩ = 0` (`θ ≠ 1_K`).
  have hzero : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 0 := by
    rw [hchi_eq, ClassFunction.inner_induce_eq_inner_restrict, hrestrict,
      OddOrder.RepresentationTheory.inner_smul_right, irreducibleCharacter_inner, if_neg hθ_ne,
      mul_zero]
  -- `⟨χ, φ⟩ = 1` (multiplicity-one constituent), contradiction.
  have hone : ClassFunction.inner chi (φ : ClassFunction ↥L ℂ) = 1 := by
    rw [dχ.decomp, inner_sum_left,
      Finset.sum_eq_single_of_mem φ hφ (fun φ' _ hne => by
        rw [irreducibleCharacter_inner, if_neg hne]),
      irreducibleCharacter_inner, if_pos rfl]
  rw [hone] at hzero
  exact one_ne_zero hzero

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), the capturing direction** (genuine): every off-kernel irreducible `φ`
(`H ⊄ ker φ`) is a constituent of some `χ ∈ S`.  By `exists_constituent_not_subset_characterKernel`
([Is] 6.5 / constituent transitivity), `Res_H φ` has a constituent `θ ≠ 1_H`; then
`χ := Ind_H^L θ ∈ S`
and `⟨φ, χ⟩ = ⟨Res_H φ, θ⟩ ≠ 0` (Frobenius `inner_induce_eq_inner_restrict` + conjugate symmetry),
so
`φ ∈ S(χ)`.  This is the `⊆` inclusion `{φ : H ⊄ ker φ} ⊆ ⋃ S(χ)` of the partition
`exists_offKernel_constituent_partition`. -/
theorem not_inHKernel_imp_mem_constituents {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ)
    {φ : IrreducibleCharacter ↥L} (hφ : ¬ InHKernel hyp φ) :
    ∃ (χ : ClassFunction ↥L ℂ) (hχ : χ ∈ hyp.Sset), φ ∈ (data χ hχ).constituents := by
  have := hyp.finiteG
  classical
  obtain ⟨θ, hlo, hθker⟩ :=
    exists_constituent_not_subset_characterKernel
      (le_refl ((hyp.typeI.typeF.H).subgroupOf L)) φ hφ
  -- `θ ≠ 1`: else `K = K.subgroupOf K ⊆ ker θ = univ`, contradicting `hθker`.
  have hθ_ne : θ ≠ trivialIrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L) := by
    rintro rfl
    exact hθker (by
      simp only [IrreducibleCharacter.coe_trivialIrreducibleCharacter,
        OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction, Set.subset_univ])
  -- `θ` is a genuine constituent of `Res_K φ`.
  have hlo' : ClassFunction.inner
      (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
      (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ) ≠ 0 := by
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def] at hlo
    exact hlo
  refine ⟨ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ), ⟨θ, hθ_ne, rfl⟩, ?_⟩
  -- `⟨φ, Ind_K θ⟩ = ⟨Res_K φ, θ⟩ ≠ 0` (Frobenius + conjugate symmetry).
  have hinner_ne : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
      (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L)
        (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)) ≠ 0 := by
    rw [OddOrder.RepresentationTheory.inner_conj_symm,
      ClassFunction.inner_induce_eq_inner_restrict,
      OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    exact hlo'
  by_contra hnotin
  apply hinner_ne
  rw [(data _ ⟨θ, hθ_ne, rfl⟩).decomp, inner_sum_right]
  refine Finset.sum_eq_zero fun φ' hφ' => ?_
  have hne : φ ≠ φ' := by rintro rfl; exact hnotin hφ'
  rw [irreducibleCharacter_inner, if_neg hne]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Toward (12.4) pin (c'), disjointness** (genuine, Clifford single-orbit): a `φ` that is a
constituent of both `χ, χ' ∈ S` forces `χ = χ'`.  Writing `χ = Ind_H^L θ`, `χ' = Ind_H^L θ'`, both
witnesses `θ, θ'` lie under `φ` (`⟨Res_H φ, θ⟩ = ⟨φ, χ⟩ ≠ 0`, Frobenius); by Clifford single-orbit
(`restrictionConstituentsSingleOrbit_of_isIrreducible` + `.exists_conj`) they are `L`-conjugate,
`conjBy g θ = θ'`, so `Ind θ = Ind θ'` (`induce_conjBy_eq`, Peterfalvi (1.5.a)).  This is the
`PairwiseDisjoint` content of `exists_offKernel_constituent_partition`. -/
theorem constituents_eq_of_mem {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    {χ χ' : ClassFunction ↥L ℂ} (hχ : χ ∈ hyp.Sset) (hχ' : χ' ∈ hyp.Sset)
    (dχ : CharacterDecompositionData hyp χ) (dχ' : CharacterDecompositionData hyp χ')
    {φ : IrreducibleCharacter ↥L} (hmem : φ ∈ dχ.constituents) (hmem' : φ ∈ dχ'.constituents) :
    χ = χ' := by
  have := hyp.finiteG
  classical
  have hKnormal : ((hyp.typeI.typeF.H).subgroupOf L).Normal := by
    rw [hyp.typeI.typeF.H_eq]
    exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L
  obtain ⟨θ, hθ_ne, rfl⟩ := hχ
  obtain ⟨θ', hθ'_ne, rfl⟩ := hχ'
  -- `θ`, `θ'` lie under `φ`: `⟨Res_K φ, η⟩ = ⟨φ, Ind_K η⟩ = 1 ≠ 0` for a constituent.
  have key : ∀ (η : IrreducibleCharacter ↥((hyp.typeI.typeF.H).subgroupOf L))
      (dη : CharacterDecompositionData hyp
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ)))
      (_ : φ ∈ dη.constituents),
      IrreducibleCharacter.LiesOver ((hyp.typeI.typeF.H).subgroupOf L) φ η := by
    intro η dη hη
    rw [IrreducibleCharacter.LiesOver, ClassFunction.restrictionMultiplicity_def]
    have hval : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ)) = 1 := by
      rw [dη.decomp, inner_sum_right,
        Finset.sum_eq_single_of_mem φ hη (fun φ' _ hne => by
          rw [irreducibleCharacter_inner, if_neg (Ne.symm hne)]),
        irreducibleCharacter_inner, if_pos rfl]
    have hrel : ClassFunction.inner (φ : ClassFunction ↥L ℂ)
        (ClassFunction.induce ((hyp.typeI.typeF.H).subgroupOf L) (η : ClassFunction _ ℂ))
        = ClassFunction.inner
          (ClassFunction.restrict ((hyp.typeI.typeF.H).subgroupOf L) (φ : ClassFunction ↥L ℂ))
          (η : ClassFunction _ ℂ) := by
      rw [OddOrder.RepresentationTheory.inner_conj_symm,
        ClassFunction.inner_induce_eq_inner_restrict,
        OddOrder.RepresentationTheory.inner_conj_symm, star_star]
    rw [← hrel, hval]; exact one_ne_zero
  obtain ⟨g, hg⟩ :=
    (restrictionConstituentsSingleOrbit_of_isIrreducible φ).exists_conj
      (key θ dχ hmem) (key θ' dχ' hmem')
  rw [← hg]
  exact (ClassFunction.induce_conjBy_eq (H := (hyp.typeI.typeF.H).subgroupOf L) g
    (θ : ClassFunction ↥((hyp.typeI.typeF.H).subgroupOf L) ℂ)).symm

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), pin (c)** ([Is] 6.2 capturing + (1.5.a)/(1.2)): the off-kernel irreducible
characters `{φ : H ⊄ ker φ}` partition into the constituent-sets `S(χ)`, `χ ∈ S`.  By [Is] 6.2,
`H ⊄ ker φ ⟹ Res_H φ` has a non-trivial constituent `θ`, so `φ ∈ S(Ind_H^L θ)`; the orbit `θ`
determines `χ = Ind θ` uniquely ((1.5.a)/(1.2)), so the `S(χ)` are pairwise disjoint and cover the
off-kernel irreducibles.  This is the genuine cross-section content (the [Is] 6.2 partition); the
`β`-vanishing regroup `Sset_offKernel_vanishes_off_H` is proved from it. -/
theorem exists_offKernel_constituent_partition {L : Subgroup G} [Finite G] (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) :
    ∃ parts : Finset {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset},
      Finset.univ.filter (fun φ => ¬ InHKernel hyp φ) =
        parts.biUnion (fun χ => (data χ.1 χ.2).constituents) ∧
      (↑parts : Set {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset}).PairwiseDisjoint
        (fun χ => (data χ.1 χ.2).constituents) := by
  have := hyp.finiteG
  classical
  by_cases hne : (Finset.univ.filter (fun φ => ¬ InHKernel hyp φ)).Nonempty
  · -- The off-kernel filter is nonempty, so `S` is nonempty; build the capturing map.
    obtain ⟨φ0, hφ0⟩ := hne
    rw [Finset.mem_filter] at hφ0
    obtain ⟨χ0, hχ0, -⟩ := not_inHKernel_imp_mem_constituents hyp data hφ0.2
    have : Nonempty {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset} := ⟨⟨χ0, hχ0⟩⟩
    let cap : IrreducibleCharacter ↥L → {χ : ClassFunction ↥L ℂ // χ ∈ hyp.Sset} :=
      fun φ => if h : ¬ InHKernel hyp φ then
        ⟨(not_inHKernel_imp_mem_constituents hyp data h).choose,
         (not_inHKernel_imp_mem_constituents hyp data h).choose_spec.choose⟩
      else Classical.arbitrary _
    refine ⟨(Finset.univ.filter (fun φ => ¬ InHKernel hyp φ)).image cap, ?_, ?_⟩
    · ext φ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
        Finset.mem_image]
      constructor
      · intro hφ
        refine ⟨cap φ, ⟨φ, hφ, rfl⟩, ?_⟩
        have hcapφ : cap φ = ⟨(not_inHKernel_imp_mem_constituents hyp data hφ).choose,
            (not_inHKernel_imp_mem_constituents hyp data hφ).choose_spec.choose⟩ := dif_pos hφ
        rw [hcapφ]
        exact (not_inHKernel_imp_mem_constituents hyp data hφ).choose_spec.choose_spec
      · rintro ⟨χs, ⟨φ', _, rfl⟩, hmem⟩
        exact constituents_not_inHKernel hyp (cap φ').2 (data (cap φ').1 (cap φ').2) hmem
    · intro χs _ χs' _ hne_s
      simp only [Function.onFun, Finset.disjoint_left]
      intro φ hmem hmem'
      exact hne_s (Subtype.ext (constituents_eq_of_mem hyp χs.2 χs'.2
        (data χs.1 χs.2) (data χs'.1 χs'.2) hmem hmem'))
  · -- The off-kernel filter is empty; the empty partition works.
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    exact ⟨∅, by rw [hne, Finset.biUnion_empty], by
      rw [Finset.coe_empty]; exact Set.pairwiseDisjoint_empty⟩

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4), the off-kernel regroup** (genuine, from the [Is] 6.2 partition pin): the
off-kernel Fourier part `β = ∑_{φ : H ⊄ ker φ} ⟨Res_L ψ, φ⟩·φ` of `Res_L ψ` vanishes on `L − H`.
Regroup the off-kernel irreducibles by the partition into `S(χ)`
(`exists_offKernel_constituent_partition`); on each `S(χ)` the coefficient `⟨Res_L ψ, φ⟩` is
constant
(`Sset_coeff_equal`, from `ψ ⊥ R(χ)`), so the `S(χ)`-block is `c_χ·∑_{φ ∈ S(χ)} φ = c_χ·χ`
(`decomp`), which vanishes at `g ∈ L − H` (`Sset_vanishes_off_H`). -/
theorem Sset_offKernel_vanishes_off_H {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {g : ↥L} (hg : (g : G) ∉ hyp.H) :
    (∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
      ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g = 0 := by
  obtain ⟨parts, hpart, hdisj⟩ := exists_offKernel_constituent_partition hyp data
  rw [classFunction_sum_apply, hpart, Finset.sum_biUnion hdisj]
  refine Finset.sum_eq_zero fun χ _ => ?_
  -- The `S(χ)`-block: `∑_{φ ∈ S(χ)} ⟨Res_L ψ, φ⟩ · φ(g) = c_χ · χ(g) = 0`.
  obtain ⟨φ₀, hφ₀⟩ := (data χ.1 χ.2).constituents_nonempty
  have hblock : ∑ φ ∈ (data χ.1 χ.2).constituents,
      (ClassFunction.inner (ClassFunction.restrict L psi) (φ : ClassFunction ↥L ℂ) •
        (φ : ClassFunction ↥L ℂ)) g
      = ClassFunction.inner (ClassFunction.restrict L psi) (φ₀ : ClassFunction ↥L ℂ) *
        ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply,
      Sset_coeff_equal hG hyp (data χ.1 χ.2) (horth χ.1 χ.2) hφ hφ₀]
  have hdecomp : ∑ φ ∈ (data χ.1 χ.2).constituents, (φ : ClassFunction ↥L ℂ) g = χ.1 g := by
    rw [← classFunction_sum_apply, ← (data χ.1 χ.2).decomp]
  rw [hblock, hdecomp, Sset_vanishes_off_H hyp χ.2 hg, mul_zero]

open scoped Classical OddOrder.Peterfalvi.S12.FiniteInduce in
/-- **Peterfalvi (12.4)**: a class function `ψ` orthogonal to every type-I family `R(χ)` (`χ ∈ S`)
is
constant on each coset `xH` with `x ∈ L − H`.

Proof: write `Res_L ψ = γ + β` by the Fourier expansion (`sum_inner_irreducibleCharacter_smul`),
splitting `Irr L` into `{H ⊆ ker φ}` (= `γ`) and `{H ⊄ ker φ}` (= `β`).  The kernel part `γ` is
constant on `H`-cosets (`apply_mul_eq_of_mem_characterKernel`, each `φ` with `H ⊆ ker φ`); the
off-kernel part `β` vanishes on `L − H` (`Sset_offKernel_vanishes_off_H`: by [Is] 6.2 + the
coefficient bridge `Sset_coeff_equal`, `β ∈ ℂ[S]` vanishes off `H`).  Hence
`ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`. -/
theorem orthogonal_character_constant_on_coset {L : Subgroup G} [Finite G]
    (hG : OddOrder.BG.IsMinimalSimpleOdd G) (hyp : Hypothesis L)
    (data : ∀ χ ∈ hyp.Sset, CharacterDecompositionData hyp χ) {psi : ClassFunction G ℂ}
    (horth : ∀ χ (hχ : χ ∈ hyp.Sset), ∀ α ∈ Rset (data χ hχ), ClassFunction.inner psi α = 0)
    {x : G} (hxL : x ∈ L) (hxH : x ∉ hyp.H) :
    ∀ h : G, h ∈ hyp.H → psi (x * h) = psi x := by
  have := hyp.finiteG
  classical
  intro h hh
  have hhL : h ∈ L := hyp.typeI.typeF.H_le hh
  set xL : ↥L := ⟨x, hxL⟩ with hxLdef
  set hL : ↥L := ⟨h, hhL⟩ with hhLdef
  set gf : ClassFunction ↥L ℂ := ClassFunction.restrict L psi with hgf
  -- Fourier split of `Res_L ψ = γ + β`.
  set γ : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hγ
  set β : ClassFunction ↥L ℂ := ∑ φ ∈ Finset.univ.filter (fun φ => ¬ InHKernel hyp φ),
    ClassFunction.inner gf (φ : ClassFunction ↥L ℂ) • (φ : ClassFunction ↥L ℂ) with hβ
  have hsplit : gf = γ + β := by
    rw [hγ, hβ, Finset.sum_filter_add_sum_filter_not]
    exact (sum_inner_irreducibleCharacter_smul gf).symm
  -- `hL` lies in `H` (as a subgroup of `L`).
  have hLmem : hL ∈ ((hyp.typeI.typeF.H).subgroupOf L : Set ↥L) :=
    Subgroup.mem_subgroupOf.mpr hh
  -- `γ` is constant on the `H`-coset `xL · hL`.
  have hγconst : γ (xL * hL) = γ xL := by
    rw [hγ, classFunction_sum_apply, classFunction_sum_apply]
    refine Finset.sum_congr rfl fun φ hφ => ?_
    rw [ClassFunction.smul_apply, ClassFunction.smul_apply,
      apply_mul_eq_of_mem_characterKernel φ.isIrreducible
        ((Finset.mem_filter.mp hφ).2 hLmem) xL]
  -- `β` vanishes on `L − H` (off-kernel part is in `ℂ[S]`).
  have hxhH : x * h ∉ hyp.H := fun hcon => hxH (by
    have hmem : x * h * h⁻¹ ∈ hyp.H := mul_mem hcon (inv_mem hh)
    rwa [mul_inv_cancel_right] at hmem)
  have hβxh : β (xL * hL) = 0 := by
    rw [hβ]
    exact Sset_offKernel_vanishes_off_H hG hyp data horth (g := xL * hL)
      (by rw [Subgroup.coe_mul]; exact hxhH)
  have hβx : β xL = 0 := by
    rw [hβ]; exact Sset_offKernel_vanishes_off_H hG hyp data horth (g := xL) hxH
  -- Assemble: `ψ(xh) = γ(xh) + β(xh) = γ(x) + 0 = γ(x) + β(x) = ψ(x)`.
  have key : gf (xL * hL) = gf xL := by
    simp only [hsplit, ClassFunction.add_apply, hγconst, hβxh, hβx, add_zero]
  have hgxh : gf (xL * hL) = psi (x * h) := by
    rw [hgf, ClassFunction.restrict_apply, Subgroup.coe_mul]
  have hgx : gf xL = psi x := by rw [hgf, ClassFunction.restrict_apply]
  rw [← hgxh, ← hgx]; exact key

/-- **Commutator bridge for the (12.5) core.**  For `H ≤ L` (subgroups of `G`), an element `x` of
`↥(H.subgroupOf L)` lies in the derived subgroup `[G_core, G_core]` of `G_core := ↥(H.subgroupOf L)`
iff its underlying `G`-element lies in `derivedInG H = [H, H]`.  Via the `MulEquiv`
`subgroupOfEquivOfLe : ↥(H.subgroupOf L) ≃* ↥H` (which preserves the commutator subgroup) and
`(derivedInG H).subgroupOf H = commutator ↥H`.  Lets the generic `DpsiH` core (whose `H_core` is
`commutator G_core`) translate its `x ∉ H_core` conclusion back to `h ∉ Hprime`. -/
theorem mem_commutator_subgroupOf_iff {L H : Subgroup G} (hHL : H ≤ L)
    (x : ↥(H.subgroupOf L)) :
    x ∈ commutator ↥(H.subgroupOf L) ↔ ((x : ↥L) : G) ∈ derivedInG H := by
  have hcomm_H : (derivedInG H).subgroupOf H = commutator ↥H := by
    rw [derivedInG, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  set e := Subgroup.subgroupOfEquivOfLe hHL with he
  have hmap : commutator ↥H = (commutator ↥(H.subgroupOf L)).map e.toMonoidHom := by
    rw [commutator, commutator, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  have hcoe : ((e x : ↥H) : G) = ((x : ↥L) : G) := rfl
  have hstep1 : x ∈ commutator ↥(H.subgroupOf L) ↔ e x ∈ commutator ↥H := by
    rw [hmap]
    exact (Subgroup.mem_map_iff_mem e.injective).symm
  have hstep2 : e x ∈ commutator ↥H ↔ ((e x : ↥H) : G) ∈ derivedInG H := by
    rw [← hcomm_H, Subgroup.mem_subgroupOf]
  rw [hstep1, hstep2, hcoe]

end OddOrder.Peterfalvi.S14


