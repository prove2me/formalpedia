-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S16_PairingCoherence
-- name    : OddOrder_Peterfalvi_S16_PairingCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T15:22:48.320047+00:00
-- url     : https://prove2.me/theorems/e309d4f9-bf84-4d45-beb5-2e42c8109cdf
-- title:
--   Peterfalvi (14.14): coherence pairing data for a type I pair
-- statement:
--   Formalizes coherence pairing data for a type I pair (Peterfalvi, *Character Theory for the Odd Order Theorem*, Section 16, p. 90, proof of (14.14)), including the bundle `TypeICoherent78Data`.
--
--   Main declarations: `TypeICoherent78Data` (The (14.14) single-side coherence bundle); `kernel` (The Fitting kernel `H = L_F` of the bundle); `kernelIn` (The kernel viewed inside `L`); `zeta` (The `i`-th induced character `ζ_i = Ind_H^L θ_i`).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_PairingCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_PairingCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_Hypothesis
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoConstancy
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_PairCoherence
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_FrobeniusStructure
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_MinimalCounterexample
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_DadeContradiction
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_RhoMEvaluation
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_NormPackage
import Definitions.Def_OddOrder_Peterfalvi_S14_MaximalI_TypeICovering
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_BrauerPermutationUnconditional
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusConjIndex
import Definitions.Def_OddOrder_Peterfalvi_S09_CrossOrthogonality
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis79
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_CharacterProduct

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Peterfalvi.S09

open OddOrder.Peterfalvi.S09.Cert

open scoped OddOrder.Peterfalvi.S12.FiniteInduce

variable {G : Type*} [Group G]

/-- **The (14.14) single-side coherence bundle** for a type-I Frobenius maximal
subgroup `L`: the (12.1) Dade setup `S14.Hypothesis` (type-I data + (8.15) Dade
support data), a Frobenius-complement witness for the Fitting kernel
`H = L_F`, the (12.6) coherence of the induced family, and a placed enumeration
`θ : Fin (n+1) → Irr H` of the distinct induced characters with the distinguished
member at `0` and `Ind 1_H` at `ind1H`.  From these the §7 interface
`S09.Hypothesis78` and all its (7.9) inputs are *derived* (no further character
theory is posited). -/
structure TypeICoherent78Data [Finite G] (L : Subgroup G) where
  /-- The (12.1) type-I Dade setup of `L`. -/
  typeIHyp : OddOrder.Peterfalvi.S14.Hypothesis L
  /-- A Frobenius complement for the kernel `H = L_F` in `L`. -/
  C : Subgroup ↥L
  /-- `L` is a Frobenius group with kernel `H = L_F` and complement `C`. -/
  hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥L
    ((typeIHyp.typeI.typeF.H).subgroupOf L) C
  /-- The (12.6) coherence of the induced family `S` over the support `A(L)`. -/
  coh : OddOrder.Peterfalvi.S07.IsCoherent typeIHyp.tau typeIHyp.Sset typeIHyp.A
  /-- Size parameter of the placed induced family. -/
  n : ℕ
  /-- The placed enumeration of `Irr H` inducing the distinct induced characters. -/
  θ : Fin (n + 1) → IrreducibleCharacter ↥((typeIHyp.typeI.typeF.H).subgroupOf L)
  /-- Index of the induced principal character `Ind 1_H`. -/
  ind1H : Fin (n + 1)
  /-- The distinguished member sits at `0 ≠ ind1H`. -/
  ind1H_ne_zero : ind1H ≠ 0
  /-- The distinguished member has degree `e = [L : H]`. -/
  deg0 : ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
      (θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    = (((typeIHyp.typeI.typeF.H).subgroupOf L).index : ℂ)
  /-- `θ ind1H = 1_H`. -/
  triv : θ ind1H = trivialIrreducibleCharacter ↥((typeIHyp.typeI.typeF.H).subgroupOf L)
  /-- The induced characters of the enumeration are distinct. -/
  inj : Function.Injective (fun i =>
    ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
      (θ i : ClassFunction _ ℂ))
  /-- The enumeration covers all induced characters. -/
  cover : ∀ φ : IrreducibleCharacter ↥((typeIHyp.typeI.typeF.H).subgroupOf L),
    ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
        (φ : ClassFunction _ ℂ) ∈
      Set.range (fun i =>
        ClassFunction.induce ((typeIHyp.typeI.typeF.H).subgroupOf L)
          (θ i : ClassFunction _ ℂ))
  /-- **The (8.3)/(12.1) support shape `A(L) = typeIA = H^#`** — carried as a discharged
  field: the producer (`nonempty`) proves it from the (12.7) Frobenius structure
  (`S14.Hypothesis.typeIA_eq_sharp`), whose Type-V exclusion input is the axiom-clean
  `no_typeV_maximal_unconditional` (issue 9087).  Bundling it here keeps the member
  theorems (`h78`, `psi_support`, …) free of the (10.10) hypothesis. -/
  typeIA_eq : typeIA L typeIHyp.typeI = (typeIHyp.typeI.typeF.H : Set G) \ {1}

namespace TypeICoherent78Data

variable [Finite G] {L : Subgroup G} (data : TypeICoherent78Data L)

/-- The Fitting kernel `H = L_F` of the bundle. -/
abbrev kernel : Subgroup G := data.typeIHyp.typeI.typeF.H

/-- The kernel viewed inside `L`. -/
abbrev kernelIn : Subgroup ↥L := (data.kernel).subgroupOf L

/-- The `i`-th induced character `ζ_i = Ind_H^L θ_i`. -/
noncomputable abbrev zeta (i : Fin (data.n + 1)) : ClassFunction ↥L ℂ :=
  ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ)

theorem kernel_le : data.kernel ≤ L := data.typeIHyp.typeI.typeF.H_le

theorem kernelIn_normal : (data.kernelIn).Normal := by
  have h : data.kernelIn = (maxNilpotentNormalHall L).subgroupOf L := by
    rw [show data.kernelIn = (data.typeIHyp.typeI.typeF.H).subgroupOf L from rfl,
      data.typeIHyp.typeI.typeF.H_eq]
  rw [h]
  exact OddOrder.BG.Ch4.S15.maxNilpotentNormalHall_subgroupOf_normal L

theorem kernel_conj_mem : ∀ (l : ↥L) {h : G}, h ∈ data.kernel →
    (l : G) * h * (l : G)⁻¹ ∈ data.kernel := by
  have := data.kernelIn_normal
  intro l h hh
  have hhL : h ∈ L := data.kernel_le hh
  have hmem : (⟨h, hhL⟩ : ↥L) ∈ data.kernelIn := Subgroup.mem_subgroupOf.mpr hh
  have hconj := data.kernelIn_normal.conj_mem ⟨h, hhL⟩ hmem l
  rw [Subgroup.mem_subgroupOf] at hconj
  simpa using hconj

/-- The type-I support is the sharp kernel: `A(L) = H \ {1}` (Peterfalvi (12.1)). -/
theorem typeIA_eq_sharp : typeIA L data.typeIHyp.typeI = (data.kernel : Set G) \ {1} :=
  data.typeIA_eq

/-- `θ 0 ≠ 1_H` (the distinguished member is not the induced principal). -/
theorem theta_zero_ne_trivial :
    data.θ 0 ≠ trivialIrreducibleCharacter ↥data.kernelIn := by
  intro h0
  refine data.ind1H_ne_zero ?_
  exact (data.inj (show data.zeta 0 = data.zeta data.ind1H by
    change ClassFunction.induce data.kernelIn ((data.θ 0 : ClassFunction _ ℂ))
      = ClassFunction.induce data.kernelIn ((data.θ data.ind1H : ClassFunction _ ℂ))
    rw [h0, data.triv])).symm

/-- `θ i ≠ 1_H` for `i ≠ ind1H`. -/
theorem theta_ne_trivial {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    data.θ i ≠ trivialIrreducibleCharacter ↥data.kernelIn := by
  intro h
  refine hi (data.inj ?_)
  change ClassFunction.induce data.kernelIn ((data.θ i : ClassFunction _ ℂ))
    = ClassFunction.induce data.kernelIn ((data.θ data.ind1H : ClassFunction _ ℂ))
  rw [h, data.triv]

/-- Each non-`ind1H` member of the placed family lies in the coherent source
family `S`. -/
theorem zeta_mem_Sset {i : Fin (data.n + 1)} (hi : i ≠ data.ind1H) :
    data.zeta i ∈ data.typeIHyp.Sset :=
  ⟨data.θ i, data.theta_ne_trivial hi, rfl⟩

/-- The degree coefficients `d_i = θ_i(1)`. -/
noncomputable def d (i : Fin (data.n + 1)) : ℂ :=
  (data.θ i : ClassFunction ↥data.kernelIn ℂ) (1 : ↥data.kernelIn)

/-- `ζ_i(1) = d_i · ζ_0(1)`. -/
theorem zeta_deg (i : Fin (data.n + 1)) :
    data.zeta i (1 : ↥L) = data.d i * data.zeta 0 (1 : ↥L) := by
  have := data.kernelIn_normal
  rw [show data.zeta i (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ i : ClassFunction _ ℂ) (1 : ↥L) from rfl,
    ClassFunction.induce_apply_one data.kernelIn (data.θ i : ClassFunction _ ℂ),
    show data.zeta 0 (1 : ↥L)
      = ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L) from rfl,
    data.deg0, d]
  ring

/-- `ζ_0(1) = ζ_{ind1H}(1)` (both are `[L:H]`). -/
theorem zeta_deg_match :
    data.zeta 0 (1 : ↥L) = data.zeta data.ind1H (1 : ↥L) := by
  have := data.kernelIn_normal
  change ClassFunction.induce data.kernelIn (data.θ 0 : ClassFunction _ ℂ) (1 : ↥L)
    = ClassFunction.induce data.kernelIn (data.θ data.ind1H : ClassFunction _ ℂ) (1 : ↥L)
  rw [data.deg0, data.triv]
  change (((data.kernelIn).index : ℂ))
    = ClassFunction.induce data.kernelIn (trivialClassFunction ↥data.kernelIn) (1 : ↥L)
  rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]

/-- `ψ_i = ζ_i − d_i ζ_0` is supported on `A(L)`. -/
theorem psi_support (_hG : OddOrder.BG.IsMinimalSimpleOdd G) (i : Fin (data.n + 1)) :
    (data.zeta i - data.d i • data.zeta 0).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (typeIA L data.typeIHyp.typeI) L := by
  have := data.kernelIn_normal
  refine (induce_diff_support (data.θ i) (data.θ 0) (data.d i) (data.zeta_deg i)).trans ?_
  intro x hx
  rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
  exact (mem_supportInSubgroup_sharp_subgroupOf_iff data.kernel
    (data.typeIA_eq_sharp) x).mpr ⟨hx.1, hx.2⟩

/-- The coherent extension preserves inner products on the placed family. -/
theorem nu_isometry (i j : Fin (data.n + 1)) (hi : i ≠ data.ind1H)
    (hj : j ≠ data.ind1H) :
    ClassFunction.inner (data.coh.extension (data.zeta i))
        (data.coh.extension (data.zeta j))
      = ClassFunction.inner (data.zeta i) (data.zeta j) :=
  coherence_extension_inner_eq_on_family data.coh (data.zeta_mem_Sset hi)
    (data.zeta_mem_Sset hj)

/-- The coherence agreement `τ(ψ_i) = ν ζ_i − d_i ν ζ_0` on the supported lattice. -/
theorem hagree (hG : OddOrder.BG.IsMinimalSimpleOdd G) (i : Fin (data.n + 1))
    (_hi0 : i ≠ 0) (hi : i ≠ data.ind1H) :
    data.typeIHyp.toHypothesis71.τ ⟨data.zeta i - data.d i • data.zeta 0,
        data.psi_support hG i⟩
      = data.coh.extension (data.zeta i)
        - data.d i • data.coh.extension (data.zeta 0) := by
  obtain ⟨deg_i, -, hdeg_i_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (data.θ i)
  exact coherence_hagree_dadeMap data.typeIHyp.dadeData.dade data.coh
    (data.zeta_mem_Sset hi) (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero))
    (m0 := 1) (mi := deg_i) (by norm_num)
    (by rw [show data.d i
        = (data.θ i : ClassFunction ↥data.kernelIn ℂ) (1 : ↥data.kernelIn) from rfl,
      hdeg_i_eq, Nat.cast_one, div_one]) (data.psi_support hG i)

/-- **The §7 coherence interface `S09.Hypothesis78`** of the bundle (Peterfalvi
(7.8) for `L`), over the type-I support `A(L) = typeIA L`.  Assembled by
`hypothesis78OfDade` exactly as in `exists_M_hypothesis78`. -/
noncomputable def h78 (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    Hypothesis78 G (typeIA L data.typeIHyp.typeI) L :=
  letI := data.kernelIn_normal
  hypothesis78OfDade data.typeIHyp.toHypothesis71
    (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeIsometry
    data.kernel data.kernel_le data.kernel_conj_mem (data.typeIA_eq_sharp)
    data.θ data.inj data.cover data.d (data.psi_support hG) data.zeta_deg
    data.ind1H data.ind1H_ne_zero data.triv data.zeta_deg_match
    data.coh.extension data.nu_isometry (data.hagree hG)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- The (7.1) layer of `h78` is the bundled (8.15) Dade data (definitional). -/
theorem h78_hyp_eq :
    (data.h78 hG).hyp76.hyp71.hyp = data.typeIHyp.dadeData.dade := rfl

/-- `‖ζ_0‖² = 1` (Frobenius irreducibility of the distinguished induced member). -/
theorem zeta_zero_norm_one :
    ClassFunction.inner (data.zeta 0) (data.zeta 0) = 1 := by
  have := data.kernelIn_normal
  exact inner_self_induce_eq_one_of_frobeniusGroup data.hFrob (data.θ 0)
    data.theta_zero_ne_trivial

/-- **The (7.8.a) `BetaDecomp` of the bundle** — via the concrete Dade-family constructor
`betaDecompOfDade`, with `ζ_0^ν ⊥ 1_G` from `witness_L_hzeta0nu` (odd order) and the
integer `a` from `exists_betaDecomp_a`. -/
noncomputable def betaDecomp (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).BetaDecomp :=
  letI := data.kernelIn_normal
  betaDecompOfDade data.typeIHyp.toHypothesis71
    (data.typeIHyp.dadeData.dade.fullDadeIsometryData
).toDadeIsometryData.isDadeIsometry
    data.kernel data.kernel_le data.kernel_conj_mem (data.typeIA_eq_sharp)
    data.θ data.inj data.cover data.d (data.psi_support hG) data.zeta_deg
    data.ind1H data.ind1H_ne_zero data.triv data.zeta_deg_match
    data.coh.extension data.nu_isometry (data.hagree hG)
    (OddOrder.Peterfalvi.S14.witness_L_hzeta0nu hG data.typeIHyp data.hFrob data.coh
      (data.typeIA_eq_sharp) (data.θ 0) data.theta_zero_ne_trivial)
    data.zeta_zero_norm_one
    (Classical.choose (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero))))))
    (Classical.choose_spec (exists_betaDecomp_a (data.h78 hG)
      (Submodule.sub_mem _
        (ClassFunction.induce_mem_ZIrr _ (data.θ data.ind1H).property.mem_ZIrr)
        (ClassFunction.induce_mem_ZIrr _ (data.θ 0).property.mem_ZIrr))
      (data.coh.extension_mem_ZIrr _ (Submodule.subset_span
        (data.zeta_mem_Sset (Ne.symm data.ind1H_ne_zero))))))

/-- **The §4 Dade support of the bundle is the faithful thickened support**
`Ã(L) = ⋃_{x ∈ A(L)} (x·R(x))^G` (via the (8.15) faithful data). -/
theorem dadeSupport_eq (hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    (data.h78 hG).hyp76.hyp71.hyp.dadeSupport
      = OddOrder.Peterfalvi.S10.ftThickenedSupport L (typeIA L data.typeIHyp.typeI) := by
  rw [data.h78_hyp_eq hG]
  exact data.typeIHyp.dadeData.dadeSupport_eq_ftThickenedSupport

/-- **The type-I support is the `A₁`-support**: `A(L) = A₁(L) = (L_F)^#` (both are the
sharp Fitting kernel). -/
theorem typeIA_eq_A1 (_hG : OddOrder.BG.IsMinimalSimpleOdd G) :
    typeIA L data.typeIHyp.typeI = A1 L PeterfalviType.I := by
  rw [data.typeIA_eq_sharp]
  change (data.kernel : Set G) \ {1} = sharpSubgroup (maxNilpotentNormalHall L)
  rw [show data.kernel = maxNilpotentNormalHall L from data.typeIHyp.typeI.typeF.H_eq]
  rfl

end TypeICoherent78Data

section Pairing

variable [Finite G] {L M : Subgroup G}

variable (dataL : TypeICoherent78Data L) (dataM : TypeICoherent78Data M)

variable (hG : OddOrder.BG.IsMinimalSimpleOdd G)

/-- **The two-subgroup (7.9) datum for a non-conjugate type-I pair** (Peterfalvi (14.14)
setup).  Bundles the two `Hypothesis78`s with the Dade-support disjointness, which is
Peterfalvi (8.17.c) (`ftThickenedSupport_A1_disjoint_of_nonconjugate`) after the
faithful-support and `A₁`-support bridges. -/
noncomputable def hypothesis79OfNonconjugate
    (hL : L ∈ maximalSubgroups G) (hM : M ∈ maximalSubgroups G)
    (hnc : ¬ OddOrder.BG.Ch4.S14.IsConjugateSubgroup L M) :
    Hypothesis79 G (typeIA L dataL.typeIHyp.typeI) L
      (typeIA M dataM.typeIHyp.typeI) M where
  odd_card := hG.odd
  first := dataL.h78 hG
  second := dataM.h78 hG
  dadeSupport_disjoint := by
    rw [dataL.dadeSupport_eq hG, dataM.dadeSupport_eq hG, dataL.typeIA_eq_A1 hG,
      dataM.typeIA_eq_A1 hG]
    exact OddOrder.Peterfalvi.S10.ftThickenedSupport_A1_disjoint_of_nonconjugate hG hL hM
      (show OddOrder.GroupTheory.HasPeterfalviType OddOrder.GroupTheory.PeterfalviType.I L from
        ⟨dataL.typeIHyp.typeI⟩)
      (show OddOrder.GroupTheory.HasPeterfalviType OddOrder.GroupTheory.PeterfalviType.I M from
        ⟨dataM.typeIHyp.typeI⟩) hnc

end Pairing

end OddOrder.Peterfalvi.S16


