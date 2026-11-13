-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_DegreeSums_CoherenceGlue
-- name    : OddOrder_Peterfalvi_S08_DegreeSums_CoherenceGlue
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:23:04.98583+00:00
-- url     : https://prove2.me/theorems/f21f3673-7d70-46b5-8f51-18e58e5fb73a
-- title:
--   Peterfalvi §8: $X/Y$ coherence glue
-- statement:
--   $Y$-set coherence, $X$-set character facts and the $X/Y$ glue for the Peterfalvi §8 coherence proof.
--
--   Main definitions: `coherentYset` (coherence of $Y=S(H')$ with the cardinal lower bound discharged internally) and `coherenceTarget_of_Xset_empty` (the (6.8) coherence in the case where $X$ is empty, i.e. $H$ abelian or no non-linear constituents).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_DegreeSums/CoherenceGlue.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_DegreeSums/CoherenceGlue.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_YsetConjugation
import Definitions.Def_OddOrder_Peterfalvi_S08_InducedKernelFamily

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

open scoped commutatorElement

variable {L G : Type*} [Group L] [Group G]

namespace SibleyDadeHypothesis

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- `Y = S(H')` is closed under complex conjugation. -/
theorem Yset_closedUnderConjugate (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S03.ClosedUnderConjugate hyp.Yset := by
  intro φ hφ
  rw [Yset, SsubFiltration] at hφ ⊢
  obtain ⟨θ, hθ_ne, hker, hφeq⟩ := hφ
  let θc : IrreducibleCharacter ↥H :=
    ⟨(θ : ClassFunction ↥H ℂ).conj, θ.isIrreducible.conj⟩
  refine ⟨θc, ?_, ?_, ?_⟩
  · intro hθc
    apply hθ_ne
    apply IrreducibleCharacter.ext
    have hval : (θ : ClassFunction ↥H ℂ).conj =
        (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
      simpa [θc] using congrArg
        (fun η : IrreducibleCharacter ↥H => (η : ClassFunction ↥H ℂ)) hθc
    calc
      (θ : ClassFunction ↥H ℂ) = ((θ : ClassFunction ↥H ℂ).conj).conj := by
        rw [ClassFunction.conj_conj]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ).conj := by
        rw [hval]
      _ = (OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥H :
          ClassFunction ↥H ℂ) := by
        ext x
        simp
  · simpa [θc, OddOrder.Peterfalvi.S03.characterKernel_conj] using hker
  · rw [hφeq]
    simpa [θc] using ClassFunction.induce_conj H (θ : ClassFunction ↥H ℂ)

/-- `Y = S(H')` has at least two members. -/
theorem two_le_Yset_ncard (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    2 ≤ hyp.Yset.ncard :=
  OddOrder.Peterfalvi.S07.two_le_ncard_of_conjugate_closed_of_noReal
    hyp.Yset_finite
    hyp.Yset_nonempty
    hyp.Yset_closedUnderConjugate
    hyp.Yset_hasNoRealCharacters

/-- `Y = S(H')` coherence, with the cardinal lower bound discharged internally. -/
noncomputable def coherentYset (hyp : SibleyDadeHypothesis G L H) [H.Normal] :
    OddOrder.Peterfalvi.S07.IsCoherent (L := ↥L) (G := G) hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :=
  hyp.coherentYset_of_two_le_ncard hyp.two_le_Yset_ncard

/-- **(6.8) coherence, `X`-empty case** (`H` abelian / no non-linear constituents).  When
`X = S − S([H,H])` is empty, the partition `S = X ∪ Y` (`Xset_union_Yset_eq_S`) collapses to
`S = Y = S([H,H])`, so the full target `IsCoherent τ S H^#` is exactly the already-built
`Y`-coherence `coherentYset` (T6: equal-degree `|W₁|` family).  This discharges the abelian branch
of the (6.8) capstone with no gluing required. -/
noncomputable def coherenceTarget_of_Xset_empty (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (hXe : hyp.Xset ⁅H, H⁆ = ∅) : hyp.CoherenceTarget := by
  have hSY : hyp.Yset = hyp.S := by
    rw [← hyp.Xset_union_Yset_eq_S, hXe, Set.empty_union]
  have h : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.S
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) := hSY ▸ hyp.coherentYset
  exact h

/-- **(6.8.1), case (c1):** in the Frobenius case every member of `S` is irreducible (hence
`X ⊆ Irr L`).  By [Is] Thm 6.34 (`isIrreducibleCharacter_induce_of_frobeniusGroup`), inducing any
nontrivial irreducible of the kernel `H` to the Frobenius group `L` gives an irreducible. -/
theorem isIrreducibleCharacter_of_mem_S_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.S) : IsIrreducibleCharacter φ := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hφ
  obtain ⟨θ, hθ_ne, rfl⟩ := hφ
  exact isIrreducibleCharacter_induce_of_frobeniusGroup hF θ hθ_ne

/-- **(6.8.1), case (c1):** `X ⊆ Irr L` in the Frobenius case, since `X ⊆ S` and `S ⊆ Irr L`.
This is the irreducibility input the §6 coherence engine (T8) consumes for the `X`-family (and the
`hX` hypothesis of the (6.6) characterization). -/
theorem isIrreducibleCharacter_of_mem_Xset_of_frobenius (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {Z : Subgroup ↥L} {φ : ClassFunction ↥L ℂ} (hφ : φ ∈ hyp.Xset Z) :
    IsIrreducibleCharacter φ :=
  hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF (hyp.mem_Xset.mp hφ).1

/-- **`S` contains no real characters** (Frobenius case).

Each member of `S` is an irreducible induced character `Ind_H^L θ` (`θ ≠ 1_H`,
`isIrreducibleCharacter_of_mem_S_of_frobenius`) of degree `|L:H|·θ(1) = |W₁|·θ(1) ≥ |W₁| > 1`, so
it is not the trivial irreducible character; odd order of `L` then gives non-realness by Peterfalvi
(1.1) (`not_isReal_of_ne_trivial_of_odd_card'`).  This `HasNoRealCharacters` fact and its
`SsubFiltration` corollary supply the no-real input to the conjugate-pair enumeration of any
`S(A) ⊆ S` consumed on the way to the (6.2)/(6.3) degree bound. -/
theorem S_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters hyp.S := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  intro φ hφ hreal
  have hirr : IsIrreducibleCharacter φ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hφ
  let η : IrreducibleCharacter ↥L := ⟨φ, hirr⟩
  have hη_ne : η ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro hη
    have hφ_one_triv : φ (1 : ↥L) = 1 := by
      have h := congrArg (fun ψ : IrreducibleCharacter ↥L =>
        (ψ : ClassFunction ↥L ℂ) (1 : ↥L)) hη
      simpa [η, trivialClassFunction_apply] using h
    rw [hyp.S_eq] at hφ
    obtain ⟨θ, -, hφeq⟩ := hφ
    obtain ⟨d, -, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hφ_one : φ (1 : ↥L) = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
      rw [hφeq, OddOrder.RepresentationTheory.ClassFunction.induce_apply_one, hd,
        hyp.index_H_eq_card_W1]
    refine absurd (hφ_one.symm.trans hφ_one_triv) ?_
    rw [← Nat.cast_mul]
    intro hcast
    have hnat : Nat.card hyp.W1 * d = 1 := by exact_mod_cast hcast
    exact hyp.W1_nontrivial (Subgroup.card_eq_one.mp (Nat.dvd_one.mp ⟨d, hnat.symm⟩))
  exact (OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card'
    hyp.card_L_odd hη_ne) hreal

/-- **`S(A)` contains no real characters** (Frobenius case), as `S(A) ⊆ S`. -/
theorem SsubFiltration_hasNoRealCharacters (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1) (A : Subgroup ↥L) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.SsubFiltration A) :=
  (hyp.S_hasNoRealCharacters hF).mono hyp.SsubFiltration_subset_S

/-- **`S`-member character facts** (Frobenius case): for `χ ∈ S` (irreducible by
`isIrreducibleCharacter_of_mem_S_of_frobenius`, non-real by `S_hasNoRealCharacters`) the conjugate
pair `{χ, χ̄}` is orthonormal (`‖χ‖² = ‖χ̄‖² = 1`, `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`).  These are the
per-member `hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar` facts that the (6.2) member-family
enumeration feeds to B1 (`coherentDegreeSumBound_of_not_coherent`) for each member of `S₁ ⊆ S`. -/
theorem sMember_characterFacts (hyp : SibleyDadeHypothesis G L H)
    (hF : OddOrder.Isaacs.Ch06.IsFrobeniusGroup (↥L) H hyp.W1)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  have hirr : IsIrreducibleCharacter χ := hyp.isIrreducibleCharacter_of_mem_S_of_frobenius hF hχS
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  have hreal : ¬ ClassFunction.IsReal χ := hyp.S_hasNoRealCharacters hF hχS
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **`S`-member conjugate-difference support** (any irreducible `χ ∈ S`): `χ̄ − χ` is supported on
`H^# = sharpImage H`.  Since `χ = Ind_H^L θ` with `H ⊴ L`, `support χ ⊆ H`, and `χ̄ − χ` vanishes at
`1` (the degree `χ(1)` is a real natural number), so it omits `1`.  This is the per-member
`hdiffsupp` fact for the (6.2)/B1 member-family over `S₁ ⊆ S`. -/
theorem sMember_diffSupport (hyp : SibleyDadeHypothesis G L H)
    {χ : ClassFunction ↥L ℂ} (hχS : χ ∈ hyp.S) (hirr : IsIrreducibleCharacter χ) :
    (χ.conj - χ).support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, -, hχeq⟩ := hχS
  obtain ⟨n, -, hn1, -⟩ := hirr.exists_natDegree_charValue_one_dvd_card
  intro g hg
  rw [ClassFunction.mem_support] at hg
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, hn1, star_natCast,
      sub_self])
  have hχg : χ g ≠ 0 := fun h0 =>
    hg (by rw [ClassFunction.sub_apply, ClassFunction.conj_apply, h0, star_zero, sub_zero])
  have hgH : g ∈ H := by
    have hsupp : χ.support ⊆ (H : Set ↥L) := by
      rw [hχeq]
      exact ClassFunction.support_induce_subset_of_normal H (θ : ClassFunction ↥H ℂ)
    exact hsupp (ClassFunction.mem_support.mpr hχg)
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  simp only [sharpImage, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff]
  exact ⟨Subgroup.mem_map.mpr ⟨g, hgH, rfl⟩, fun h1 => hg1 (OneMemClass.coe_eq_one.mp h1)⟩

/-- **(T7-c2 case A) `X ⊆ Irr L`.**  In case A every `χ ∈ X = S − S(Z)` is irreducible.  Writing
`χ = Ind_H^L θ` (`θ ≠ 1`, from `χ ∈ S`), membership `χ ∉ S(Z)` forces `Z.subgroupOf H ⊄ Ker θ`, so
`inertia_eq_H_of_c2_caseA` gives `I_L(θ) = H`, and [Is] Thm 6.34
(`isIrreducibleCharacter_induce_of_inertia_eq`) makes `Ind_H^L θ = χ` irreducible.  This is the
case-A analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius` (the Frobenius case). -/
theorem isIrreducibleCharacter_of_mem_Xset_caseA (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) (hZcentral : Z.subgroupOf H ≤ Subgroup.center ↥H)
    (hZnorm : ∀ w ∈ hyp.W1, w ∈ Subgroup.normalizer Z)
    (hZfpf : ∀ w ∈ hyp.W1, w ≠ 1 → Subgroup.centralizer ({w} : Set ↥L) ⊓ Z = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  let : H.Normal := hyp.H_normal
  have : Fintype ↥H := Fintype.ofFinite _
  obtain ⟨hχS, hχnotZ⟩ := hχX
  rw [hyp.S_eq] at hχS
  obtain ⟨θ, hθne, hχeq⟩ := hχS
  have hZker : ¬ ((Z.subgroupOf H : Set ↥H) ⊆
      OddOrder.Peterfalvi.S03.characterKernel (θ : ClassFunction ↥H ℂ)) :=
    fun hsub => hχnotZ ⟨θ, hθne, hsub, hχeq⟩
  have hinertia := hyp.inertia_eq_H_of_c2_caseA hZH hZcentral hZnorm hZfpf hZker
  rw [hχeq]
  exact isIrreducibleCharacter_induce_of_inertia_eq θ hinertia

/-- **(c2)+math-(A) `X ⊆ Irr L`** (Peterfalvi (6.8.1) in the CertainType branch, math-case A).
Every `χ ∈ X = S − S(Zc)` is irreducible at the central `Zc = Z(H) ∩ H'`.  This is the (c2)
analogue of `isIrreducibleCharacter_of_mem_Xset_of_frobenius`: it discharges the four hypotheses of
the FPF-generic `isIrreducibleCharacter_of_mem_Xset_caseA` at `Z = Zc` — centrality
(`centralCommutator_subgroupOf_le_center`), normality (`Zc ◁ L`, so every `w` normalizes it), and
fixed-point-freeness (`centralizer_inf_centralCommutator_eq_bot_of_c2_caseA`, from the math-(A)
hypothesis `hA : Z(H) ⊓ W₂ = 1`). -/
theorem isIrreducibleCharacter_of_mem_Xset_c2_caseA (hyp : SibleyDadeHypothesis G L H)
    {cert : OddOrder.Peterfalvi.S06.CertainTypeHypothesis (sharpImage H) L}
    (hK : cert.K = H) (hW1 : cert.W1 = hyp.W1)
    (hA : Subgroup.center ↥H ⊓ cert.W2.subgroupOf H = ⊥)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset hyp.centralCommutator) :
    letI : H.Normal := hyp.H_normal
    IsIrreducibleCharacter χ := by
  have := hyp.H_normal
  exact hyp.isIrreducibleCharacter_of_mem_Xset_caseA hyp.centralCommutator_le
    hyp.centralCommutator_subgroupOf_le_center
    (fun w _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr
        hyp.centralCommutator_normal]; exact Subgroup.mem_top w)
    (fun w hw hw1 => hyp.centralizer_inf_centralCommutator_eq_bot_of_c2_caseA hK hW1 hA hw hw1)
    hχX

/-- **The Sibley filtration is the general induced family at `K = H`.**  `SsubFiltration A` and
`inducedKernelFamily H A` (`S08_InducedKernelFamily`) unfold to the same set of induced characters,
so the identification is definitional.  This is what lets the Sibley layer read the (6.6)
`X`-characterization off the general-kernel theorem instead of carrying a `K = H` copy. -/
theorem SsubFiltration_eq_inducedKernelFamily (hyp : SibleyDadeHypothesis G L H)
    (A : Subgroup ↥L) :
    hyp.SsubFiltration A = inducedKernelFamily H A :=
  rfl

/-- **`X = S − S(Z)` is the general `𝒮 − 𝒮(Z)`** — `S = S(⊥)` (`SsubFiltration_bot`) turns the
Sibley `Xset` into the set difference the general (6.6) theorem is stated on. -/
theorem Xset_eq_inducedKernelFamily_sdiff (hyp : SibleyDadeHypothesis G L H) (Z : Subgroup ↥L) :
    hyp.Xset Z = inducedKernelFamily H ⊥ \ inducedKernelFamily H Z := by
  rw [Xset, ← hyp.SsubFiltration_bot, hyp.SsubFiltration_eq_inducedKernelFamily,
    hyp.SsubFiltration_eq_inducedKernelFamily]

/-- **Peterfalvi (6.6) `X`-characterization** (mmd 04.8 L74-76).  For a normal `Z ≤ H` such that
every member of `X = S − S(Z)` is irreducible (the (6.8) Frobenius/case-A input `hX`), `X` is
exactly the set of irreducible characters of `L` whose kernel does not contain `Z`:
`X = {χ ∈ Irr L | Z ⊄ Ker χ}`.

The Sibley (`K = H`) instance of the general-kernel
`inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel`
(`S08_InducedKernelFamily`), transported along `Xset_eq_inducedKernelFamily_sdiff`. -/
theorem Xset_eq_irreducible_not_subset_characterKernel (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    hyp.Xset Z = {χ : ClassFunction ↥L ℂ | IsIrreducibleCharacter χ ∧
      ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ)} := by
  let : H.Normal := hyp.H_normal
  rw [hyp.Xset_eq_inducedKernelFamily_sdiff Z] at hX ⊢
  exact inducedKernelFamily_sdiff_eq_irreducible_not_subset_characterKernel hZH hX

/-- **(T8 leaf 1) `X`-member character facts**, from the abstract input `X ⊆ Irr L`.

Every `χ ∈ X = S − S(Z)` is non-real (Peterfalvi (1.1), `L` odd) with
`‖χ‖² = ‖χ̄‖² = 1` and `⟨χ̄, χ⟩ = ⟨χ, χ̄⟩ = 0`.  These are the
`hreal`/`hχχ`/`hχbarχbar`/`hχbarχ`/`hχχbar'` fields of `S07.DadeChainStep`.
Non-triviality is read off the (6.6) characterization
(`Z ⊄ Ker χ` via `Xset_eq_irreducible_not_subset_characterKernel`, so `χ ≠ 1`),
then (1.1) (`not_isReal_of_ne_trivial_of_odd_card'`) gives non-realness and
`irreducibleCharacter_inner_eq_ite` gives the orthonormality.

This form is shared by the Frobenius case and the case-A `X ⊆ Irr L` bridge. -/
theorem xMember_characterFacts_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ)
    {χ : ClassFunction ↥L ℂ} (hχX : χ ∈ hyp.Xset Z) :
    ¬ ClassFunction.IsReal χ ∧
      ClassFunction.inner χ χ = 1 ∧
      ClassFunction.inner χ.conj χ.conj = 1 ∧
      ClassFunction.inner χ.conj χ = 0 ∧
      ClassFunction.inner χ χ.conj = 0 := by
  have : Fintype ↥H := Fintype.ofFinite _
  have hirr : IsIrreducibleCharacter χ := hX χ hχX
  have hconjirr : IsIrreducibleCharacter χ.conj := hirr.conj
  -- `Z ⊄ Ker χ` from the (6.6) characterization, hence `χ ≠ 1`.
  have hZker : ¬ ((Z : Set ↥L) ⊆ OddOrder.Peterfalvi.S03.characterKernel χ) := by
    have hXeq := hyp.Xset_eq_irreducible_not_subset_characterKernel hZH hX
    rw [hXeq] at hχX
    exact hχX.2
  have hne_triv : (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ≠
      OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥L := by
    intro htriv
    apply hZker
    have hχtriv : χ = OddOrder.RepresentationTheory.trivialClassFunction ↥L :=
      congrArg Subtype.val htriv
    rw [hχtriv, OddOrder.Peterfalvi.S03.characterKernel_trivialClassFunction]
    exact Set.subset_univ _
  have hreal : ¬ ClassFunction.IsReal χ :=
    OddOrder.RepresentationTheory.not_isReal_of_ne_trivial_of_odd_card' hyp.card_L_odd hne_triv
  have hbi_ne : (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L) ≠ ⟨χ, hirr⟩ :=
    fun h => hreal (congrArg Subtype.val h)
  refine ⟨hreal, ?_, ?_, ?_, ?_⟩
  · simpa using irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L) ⟨χ, hirr⟩
  · simpa using
      irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
        ⟨χ.conj, hconjirr⟩
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ.conj, hconjirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ, hirr⟩
    rwa [if_neg hbi_ne] at h
  · have h := irreducibleCharacter_inner_eq_ite (⟨χ, hirr⟩ : IrreducibleCharacter ↥L)
      ⟨χ.conj, hconjirr⟩
    rwa [if_neg (fun h => hbi_ne h.symm)] at h

/-- **(T8 leaf 3b) `X` has no real characters**, from the abstract input `X ⊆ Irr L`. -/
theorem Xset_hasNoRealCharacters_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (hZH : Z ≤ H) [Z.Normal]
    (hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    OddOrder.Peterfalvi.S03.HasNoRealCharacters (hyp.Xset Z) :=
  fun _ hχX => (hyp.xMember_characterFacts_of_irreducible_X hZH hX hχX).1

/-- **(T8 leaf 4) `X` is finite**, from the abstract input `X ⊆ Irr L`.

This is the `hXfin` input to the degree-monotone enumeration
`S07.exists_monotoneDegreeEnum` and the chain assembly. -/
theorem xSet_finite_of_irreducible_X (hyp : SibleyDadeHypothesis G L H)
    {Z : Subgroup ↥L} (_hX : ∀ φ ∈ hyp.Xset Z, IsIrreducibleCharacter φ) :
    (hyp.Xset Z).Finite :=
  hyp.Xset_finite Z

end SibleyDadeHypothesis

end OddOrder.Peterfalvi.S08


