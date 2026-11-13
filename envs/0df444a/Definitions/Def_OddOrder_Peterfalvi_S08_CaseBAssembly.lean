-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly
-- name    : OddOrder_Peterfalvi_S08_CaseBAssembly
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T07:15:57.616124+00:00
-- url     : https://prove2.me/theorems/ec6d2c37-1edf-4c04-88fd-8d690d4ba17d
-- title:
--   Peterfalvi §8: case (B) coherence, per-$\varphi$ constituent dispatch and $X\cup Y$ assembly
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §8, pp. 30-37, the (6.8.2.3) core of the (6.8) coherence capstone. This continues the case-(B) coherence assembly with the mixed per-$\varphi$ constituent dispatch and the $X\cup Y$ assembly.
--
--   Main definitions: `caseB_constituentDecomposition` (the (6.8.2.3) per-constituent decomposition, mixed dispatch) and `caseB_phi_family` (the mixed per-$\varphi$ decomposition family), with `inner_columnSum_cross_eq_zero` (distinct certain-type columns are orthogonal).
--
--   The bundle also proves 16 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S08_CaseBAssembly.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S08_CaseBAssembly.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S08_CaseBAssembly_BranchBundles

namespace OddOrder.Peterfalvi.S08

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G] [Invertible (Nat.card G : ℂ)]

variable {L : Subgroup G} [Fintype ↥L] [Invertible (Nat.card ↥L : ℂ)]

variable {H : Subgroup ↥L} [Invertible (Nat.card ↥H : ℂ)]

/-- **(6.8.2.3) per-constituent decomposition (mixed dispatch).**  For a constituent `θ : Irr H` of
`Ind^L_K φ` (with `K = H`, case (c2)), the (5.4) decomposition data of `Ind^L_H θ` against the
Sibley–Dade map `hyp.tau`, dispatched on whether `Ind^L_H θ` is a reducible certain-type column
`μ_j = columnSum h46 χ₂` or an irreducible induced character:

* **column branch** (`∃ χ₂ ≠ 1, columnSum h46 χ₂ = Ind^L_H θ`): `columnDecompositionTau` (the
  rebuilt certain-type `R(μ_j)` family), with the column character rewritten to `Ind^L_H θ` along
  the witness equation;
* **irreducible branch** (no nontrivial column equals `Ind^L_H θ`): `irreducibleDecompositionTau`
  (`decompositionDaFromDadeOfDiff hyp.dade`).

Both branches land in the *same* map `hyp.tau`, so the family
`fun i => caseB_constituentDecomposition …` feeds the pinning `per_phi_anchored_image`.  The per-`θ`
structural hypotheses of each branch are supplied by the (conditional) bundles `hcol` / `hirr`; they
are discharged at the family construction
from the §5/§6 X-member machinery (column: certain-type `(4.9)` reflection; irreducible: as in the
case-A Dade chain). -/
noncomputable def caseB_constituentDecomposition
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ) →
      (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1
          = ∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
              - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
      ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
            OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
          s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
          (a • η₁ : ClassFunction ↥L ℂ) = 0))
    (hirr : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
      ∧ (((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
            - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
          (a • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)) :
    OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) (a • η₁) := by
  classical
  by_cases hcase : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · -- column branch: the witness `χ₂` is extracted by choice (the goal is `Type`-valued, so a
    -- direct `obtain` on the `Prop`-`∃` would be an illegal large elimination).  The decomposition
    -- bundle is consumed by `.1`/`.2.…` projections (not `obtain`/`And.casesOn`) so that the `tau1`
    -- field reduces through `caseB_constituentDecomposition_tau1`; the index is cast by `heq ▸`.
    have hχ₂ne := hcase.choose_spec.1
    have heq := hcase.choose_spec.2
    have hb := hcol _ hχ₂ne heq
    exact heq ▸ columnDecompositionTau hyp h46 hχ₂ne hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1
      hb.2.2.2.2.1 hb.2.2.2.2.2
  · -- irreducible branch: no nontrivial column equals `Ind^L_H θ`
    have hnc : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
      fun χ₂ hne heq2 => hcase ⟨χ₂, hne, heq2⟩
    have hb := hirr hnc
    exact irreducibleDecompositionTau hyp θ hb.1 hb.2.1 hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2.1
      hb.2.2.2.2.2.1 hb.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2

/-- The `tau1` field of `caseB_constituentDecomposition` is `hyp.tau`, in both dispatch branches
(`columnDecompositionTau`/`irreducibleDecompositionTau` both build via `ofProjection … hyp.tau …`,
and `hyp.tau = dadeIntegralCharacterMap hyp.dade …`).  This is the `htau1` input of
`per_phi_anchored_image` for the mixed per-`φ` family. -/
theorem caseB_constituentDecomposition_tau1
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    {hcol _hirr} :
    (caseB_constituentDecomposition (a := a) (η₁ := η₁) hyp h46 θ hcol _hirr).tau1 = hyp.tau := by
  unfold caseB_constituentDecomposition
  split
  · rw [charPsiDecomp_eqRec_tau1]; rfl
  · rfl

/-- **(6.8.2.3) the mixed per-`φ` decomposition family.**  Over the positive-weight subtype
`{θ : Irr H // 0 < aθ}` (`aθ = ⟨φ, Res^H_{W₂} θ⟩`), each constituent `Ind^L_H θ` of `Ind^L_{W₂} φ`
is decomposed against `hyp.tau` by the per-`θ` dispatch `caseB_constituentDecomposition` (column /
irreducible).  This is the family `D` fed to `caseB_per_phi_anchored`; its `tau1 = hyp.tau` is
`caseB_constituentDecomposition_tau1`.  The per-`θ` column/irreducible bundles `hcol`/`hirr` are the
genuine §5/§6 discharge (supplied at the capstone). -/
noncomputable def caseB_phi_family
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H)
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ}
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        = ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) →
      (∑ k, ((h46.columnFamily χ₂).mu k : ClassFunction ↥L ℂ) 1
          = ∑ k, ((h46.columnFamily χ₂⁻¹).mu k : ClassFunction ↥L ℂ) 1)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
          = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
            (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
              - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
      ∧ (∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
            OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - constituentWeight hφ' i.val • η₁}
            : Set (ClassFunction ↥L ℂ)),
          s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - constituentWeight hφ' i.val • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
      IsIrreducibleCharacter (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
      ∧ (¬ ClassFunction.IsReal (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)))
      ∧ (((ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj
            - ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ ((ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
          - constituentWeight hφ' i.val • η₁).support ⊆
          OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
      ∧ (hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
          - constituentWeight hφ' i.val • η₁) ∈ ZIrr G)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj
          (constituentWeight hφ' i.val • η₁ : ClassFunction ↥L ℂ) = 0)
      ∧ (ClassFunction.inner (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ))
          (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)) :
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁) :=
  fun i => caseB_constituentDecomposition hyp h46 i.val (hcol i) (hirr i)

/-- The mixed per-`φ` family lands in `tau1 = hyp.tau` at every constituent — the `htau1` input of
`caseB_per_phi_anchored`. -/
theorem caseB_phi_family_tau1
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H)
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ} {hcol _hirr}
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    (caseB_phi_family hyp h46 hW2H hφ' (η₁ := η₁) hcol _hirr i).tau1 = hyp.tau :=
  caseB_constituentDecomposition_tau1 hyp h46 i.val

/-- **(6.8.2.3) seam-1 orthogonality, column branch.**
`⟨(columnDecompositionTau …).X, cY.ext η₁⟩ = 0`.  The column decomposition's image side
`X ∈ ℤ[R(μ_j)]` is orthogonal to the `Y`-anchor extension `cY.extension η₁`: by
`inner_X_Y_eq_zero_of_orthogonal` it suffices that each member of `R(μ_j) = certainTypeR.imageSet`
(a signed `±δ_j·ω_{ij}^σ`, `certainTypeRImage`) is `⊥ cY.extension η₁`, which is
`inner_coherent_extension_certainTypeOmegaSigma_eq_zero` (the certain-type seam-1, generic in the
coherence `cY`).  The partner anchor `η'` supplies the supported difference `η₁ − η'` the seam-1
proof needs (the `V`-vanishing of `cY.extension η₁ − cY.extension η'`). -/
theorem columnDecompositionTau_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h46.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hmapagree : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj)
      = OddOrder.Peterfalvi.S07.dadeIntegralCharacterMap h46.dade0 h46.tau
        (OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj))
    (hSdiff : ∀ s ∈ ({OddOrder.Peterfalvi.S06.columnSum h46 χ₂
        - (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj,
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁} : Set (ClassFunction ↥L ℂ)),
      s.support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (OddOrder.Peterfalvi.S06.columnSum h46 χ₂ - a • η₁) ∈ ZIrr G)
    (hχψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbarψ : ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η' : ClassFunction ↥L ℂ} (hη₁Y : η₁ ∈ hyp.Yset) (hη'Y : η' ∈ hyp.Yset)
    (hη₁irr : IsIrreducibleCharacter η₁) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L) :
    ClassFunction.inner
        (columnDecompositionTau hyp h46 hχ₂ hdeg hmapagree hSdiff htau1_mema hχψ hχbarψ).X
        (cY.extension η₁) = 0 := by
  classical
  apply inner_X_Y_eq_zero_of_orthogonal
  intro α hα
  change α ∈ Finset.univ.image (OddOrder.Peterfalvi.S06.certainTypeRImage h46 χ₂ χ₂⁻¹) at hα
  rw [Finset.mem_image] at hα
  obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
  cases b
  · simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cY hη₁Y hη'Y hη₁irr hη'irr
        hee hsupp χ₂ i, mul_zero]
  · simp only [OddOrder.Peterfalvi.S06.certainTypeRImage]
    rw [OddOrder.RepresentationTheory.inner_smul_right,
      inner_coherent_extension_certainTypeOmegaSigma_eq_zero hyp h46 hHK cY hη₁Y hη'Y hη₁irr hη'irr
        hee hsupp χ₂⁻¹ i, mul_zero]

/-- **(6.8.2.3) seam-1 orthogonality, irreducible branch.**
`⟨(irreducibleDecompositionTau …).X, cY.extension η₁⟩ = 0`.  The irreducible constituent's image
side is orthogonal to the `Y`-anchor extension — a re-instantiation of the case-A X-member
orthogonality `inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero` (the Dade
`R(Ind^L_H θ)` family is `⊥ cY.extension η₁` by the (5.2.e) family orthogonality), with
`χ = ⟨Ind^L_H θ, hirr⟩` and the `Y`-anchor `chi1 = ⟨η₁, hη₁irr⟩`.  The `χ`-facts are exactly
`irreducibleDecompositionTau`'s hypotheses; the `η₁`-facts (real, supports, `Yset`-membership,
`ZIrr` extension, orthogonality to the constituent) are the per-anchor data the (5.2.e) family
orthogonality needs. -/
theorem irreducibleDecompositionTau_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (θ : IrreducibleCharacter ↥H)
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ}
    (hreal : ¬ ClassFunction.IsReal (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (hdiffsupp : ((ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
        - ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hdiffasupp : (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (htau1_mema : hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G)
    (hχaχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχbaraχ1 : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj
      (a • η₁ : ClassFunction ↥L ℂ) = 0)
    (hχχbar' : ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1S1 : η₁ ∈ hyp.Yset) (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    (hc1χ : ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0)
    (hc1χbar : ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0)
    (hc1barχ : ClassFunction.inner η₁.conj (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0)
    (hc1barχbar : ClassFunction.inner η₁.conj
      (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    ClassFunction.inner
        (irreducibleDecompositionTau hyp θ hirr hreal hdiffsupp hdiffasupp htau1_mema
          hχaχ1 hχbaraχ1 hχχbar').X
        (cY.extension η₁) = 0 :=
  inner_decompositionDaFromDadeOfDiff_X_extension_member_eq_zero hyp.dade cY
    ⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ ⟨η₁, hη₁irr⟩
    hreal hdiffsupp hdiffasupp htau1_mema hχaχ1 hχbaraχ1 hχχbar'
    hrealc1 hdiffsuppc1 hc1S1 hc1barS1 hνZc1 hc1c1bar hc1χ hc1χbar hc1barχ hc1barχbar

/-- **(6.8.2.3) `hsq` over the positive-weight subtype.**  The Clifford square-sum
`∑_θ ⟨φ, Res^H_{W₂} θ⟩² = |H : W₂|` (`sum_inner_restrict_sq_eq_index`, `W₂` central in `H`),
reindexed to the positive-weight subtype `{θ // 0 < aθ}` (zero-weight constituents drop) and cast to
`ℤ`.  This is the `hsq` input of `per_phi_anchored_image` (the `n = |H : W₂|` of the (6.8.2.2)
aggregate). -/
theorem sum_constituentWeight_sq_subtype {M : Type*} [Group M] [Finite M]
    [Invertible (Nat.card M : ℂ)] {K H : Subgroup M} (hKH : K ≤ H)
    [Finite ↥H] [Fintype ↥(K.subgroupOf H)]
    [Invertible (Nat.card ↥H : ℂ)] [Invertible (Nat.card ↥(K.subgroupOf H) : ℂ)]
    (hcen : K.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥K ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hKH).toMonoidHom φ)) :
    ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
        ((constituentWeight hφ' i.val : ℤ)) ^ 2 = ((K.subgroupOf H).index : ℤ) := by
  classical
  have : Fintype ↥H := Fintype.ofFinite ↥H
  -- the full square-sum over `Irr H`, in `ℤ`-form
  have hfull : (∑ θ : IrreducibleCharacter ↥H, ((constituentWeight hφ' θ : ℤ)) ^ 2)
      = ((K.subgroupOf H).index : ℤ) := by
    have key := sum_inner_restrict_sq_eq_index (M := ↥H) (N := K.subgroupOf H) hcen hφ'
    simp only [constituentWeight_spec hφ'] at key
    have hcast : ((∑ θ : IrreducibleCharacter ↥H, ((constituentWeight hφ' θ : ℤ)) ^ 2 : ℤ) : ℂ)
        = (((K.subgroupOf H).index : ℤ) : ℂ) := by
      push_cast
      simp only [pow_two]
      exact key
    exact_mod_cast hcast
  refine Eq.trans ?_ hfull
  exact (sum_eq_sum_pos_weight_subtype (constituentWeight hφ')
    (fun θ => ((constituentWeight hφ' θ : ℤ)) ^ 2)
    (fun θ hθ => by
      change (constituentWeight hφ' θ : ℤ) ^ 2 = 0
      rw [hθ]; norm_num)).symm

/-- **(6.8.2.2)→(6.8.2.3) aggregate `hagg` for the mixed per-`φ` family.**  The (6.8.2.2)
decomposition `τ(Ind^L_{W₂} φ − |H:W₂|·η₁) = Xagg − |H:W₂|·Y₀` (`hdecomp`, from
`exists_decomposition_caseB`), combined with the constituent sum
`Ind^L_{W₂} φ − |H:W₂|·η₁ = ∑_θ aθ·(Ind^L_H θ − aθ·η₁)`
(`sum_smul_constituent_diff_pos_weight_subtype`) and the per-constituent images
`τ(Ind^L_H θ − aθ·η₁) = (D θ).X − (D θ).Y` (`(D θ).tau1_image`, `tau1 = hyp.tau` via `htau1`), gives
the `hagg` input of `per_phi_anchored_image`:
`Xagg − |H:W₂|·Y₀ = ∑_θ aθ·((D θ).X − (D θ).Y)`.  The source aggregate's `ℂ`-scalar `(aθ : ℂ)·η₁`
is reconciled with the family's `ℕ`-anchor `aθ • η₁` by `Nat.cast_smul_eq_nsmul`. -/
theorem caseB_hagg
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Finite ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    {η₁ : ClassFunction ↥L ℂ}
    (D : (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg Y₀ : ClassFunction G ℂ}
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • Y₀) :
    Xagg - (((W2.subgroupOf H).index : ℤ) : ℂ) • Y₀
      = ∑ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
          ((constituentWeight hφ' i.val : ℤ) : ℂ) • ((D i).X - (D i).Y) := by
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥W2 := Fintype.ofFinite _
  have hagg := aggregate_eq_sum_of_constituent (L := L) Finset.univ hyp.tau
    (fun i => ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)
      - constituentWeight hφ' i.val • η₁)
    (fun i => (D i).X) (fun i => (D i).Y) (fun i => (constituentWeight hφ' i.val : ℤ))
    (β := ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
    (n := ((W2.subgroupOf H).index : ℤ))
    -- `hmemimg`: each constituent image is `(D i).tau1_image`, with `tau1 = hyp.tau`.
    (fun i _ => by have h := (D i).tau1_image; rw [htau1 i] at h; exact h)
    -- `hconstit`: the source aggregate, with the `ℂ`-anchor reconciled to the `ℕ`-anchor.
    ((sum_smul_constituent_diff_pos_weight_subtype hW2H hcen φ hφ' η₁).trans
      (Finset.sum_congr rfl fun i _ => by
        simp only [Int.cast_natCast, Nat.cast_smul_eq_nsmul]))
    -- `hdecomp`: the (6.8.2.2) decomposition (`n = |H:W₂|`), bridging the `ℕ`/`ℤ` index cast.
    (by exact_mod_cast hdecomp)
  exact hagg

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image (mixed family, abstract `D`).**  For the
per-`φ` decomposition family `D` (each constituent `Ind^L_H θ` of `Ind^L_{W₂} φ` decomposed against
`hyp.tau`, e.g. by the dispatch `caseB_constituentDecomposition`), with `(D θ).tau1 = hyp.tau`, the
seam-`1` orthogonality `(D θ).X ⊥ Y₀` (`hXorth`) and integrality `⟨(D θ).Y, Y₀⟩ ∈ ℤ` (`hbi`), and
the (6.8.2.2) decomposition `hdecomp`/`hXaggorth` of `exists_decomposition_caseB`, the pinning gives
the **anchored image**
`(Ind^L_H θ − aθ·η₁)^{hyp.tau} = (D θ).X − aθ·Y₀`   (`Y₀ = cY.extension η₁`, `aθ = ⟨φ, Res θ⟩`).

This is the route-independent (6.8.2.3) core: the `Xagg`/`hsq`/`hagg` are assembled internally
(`caseB_hagg`, `sum_constituentWeight_sq_subtype`); only the family `D` (the constituent dispatch)
and its per-`θ` orthogonality/integrality remain for the capstone. -/
theorem caseB_per_phi_anchored
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Finite ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (D : (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) →
      OddOrder.Peterfalvi.S07.CharacterPsiDecomposition hyp.tau
        (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) (constituentWeight hφ' i.val • η₁))
    (htau1 : ∀ i, (D i).tau1 = hyp.tau)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    {b : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ} → ℤ}
    (hXorth : ∀ i, ClassFunction.inner (D i).X (cY.extension η₁) = 0)
    (hbi : ∀ i, ClassFunction.inner (D i).Y (cY.extension η₁) = (b i : ℂ))
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (D i).X - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ := by
  have : Fintype ↥H := Fintype.ofFinite _
  have : Fintype ↥W2 := Fintype.ofFinite _
  exact per_phi_anchored_image hyp cY hη₁ Finset.univ D htau1 hXaggorth
    (caseB_hagg hyp hW2H hcen hφ' D htau1 hdecomp)
    (sum_constituentWeight_sq_subtype hW2H hcen hφ')
    (fun i _ => hXorth i) (fun i _ => hbi i) i (Finset.mem_univ i) i.2

/-- **(6.8.2.3) the `τ₁`-image of the dispatch is a virtual character.**  For the per-constituent
dispatch `caseB_constituentDecomposition`, `hyp.tau (Ind^L_H θ − a·η₁) ∈ ZIrr G`, extracted from the
appropriate branch bundle (`hcol`/`hirr`): on the column branch the witness equation rewrites
`Ind^L_H θ` to `μ_j = columnSum h46 χ₂` and the column bundle's `ZIrr`-conjunct applies; on the
irreducible branch the irreducible bundle's `ZIrr`-conjunct applies directly.  This is the `hτmem`
input of `psiDecomp_Y_inner_int` for the dispatch (via `caseB_constituentDecomposition_tau1`). -/
theorem caseB_constituentDecomposition_tau1_mem_ZIrr
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : CaseBColBundle hyp h46 θ η₁ a) (hirr : CaseBIrrBundle hyp h46 θ η₁ a) :
    hyp.tau (ClassFunction.induce H (θ : ClassFunction ↥H ℂ) - a • η₁) ∈ ZIrr G := by
  classical
  by_cases hcase : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · obtain ⟨χ₂, hne, heq⟩ := hcase
    rw [← heq]
    exact (hcol χ₂ hne heq).2.2.2.1
  · exact (hirr (fun χ₂ hne heq2 => hcase ⟨χ₂, hne, heq2⟩)).2.2.2.2.1

/-- **(6.8.2.3) seam-1 orthogonality of the dispatch.**  `⟨(caseB_constituentDecomposition …).X,
cY.extension η₁⟩ =
0`, dispatched per branch through the index cast (`charPsiDecomp_eqRec_X`): on the
column branch the certain-type seam-1 `columnDecompositionTau_X_orthogonal` (using the partner
anchor
`η' ≠ η₁ ∈ Yset`), on the irreducible branch the Dade family seam-1
`irreducibleDecompositionTau_X_orthogonal` (using the per-`θ` anchor-vs-constituent orthogonality
`hirrAnc`). The partner data and the `η₁`-anchor data are explicit hypotheses (the genuine §5
content
discharged at the capstone); this lemma is the pure branch plumbing. -/
theorem caseB_constituentDecomposition_X_orthogonal
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : CaseBColBundle hyp h46 θ η₁ a) (hirr : CaseBIrrBundle hyp h46 θ η₁ a)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hη₁Y : η₁ ∈ hyp.Yset) (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    {η' : ClassFunction ↥L ℂ} (hη'Y : η' ∈ hyp.Yset) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hirrAnc : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0
      ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁.conj
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    ClassFunction.inner (caseB_constituentDecomposition hyp h46 θ hcol hirr).X
        (cY.extension η₁) = 0 := by
  classical
  unfold caseB_constituentDecomposition
  split
  · rw [charPsiDecomp_eqRec_X]
    exact columnDecompositionTau_X_orthogonal hyp h46 hHK _ _ _ _ _ _ _ cY
      hη₁Y hη'Y hη₁irr hη'irr hee hsupp
  · next hneg =>
    have hncond : ∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ) :=
      fun χ₂ hne heq2 => hneg ⟨χ₂, hne, heq2⟩
    obtain ⟨hc1χ, hc1χbar, hc1barχ, hc1barχbar⟩ := hirrAnc hncond
    exact irreducibleDecompositionTau_X_orthogonal hyp θ _ _ _ _ _ _ _ _ cY hη₁irr
      hrealc1 hdiffsuppc1 hη₁Y hc1barS1 hνZc1 hc1c1bar hc1χ hc1χbar hc1barχ hc1barχbar

/-- **(6.8.2.3) integrality of the dispatch's orthogonal side.**  `⟨(caseB_constituentDecomposition
…).Y, cY.extension η₁⟩ ∈ ℤ`, via the route-independent `psiDecomp_Y_inner_int`: the image side is
`⊥ cY.extension η₁` (`caseB_constituentDecomposition_X_orthogonal`), the `τ₁`-image is a virtual
character (`caseB_constituentDecomposition_tau1_mem_ZIrr`, read through
`caseB_constituentDecomposition_tau1`), and the anchor `cY.extension η₁ ∈ ZIrr G` (`hνZc1`).  This
is
the `hbi` of `caseB_per_phi_anchored` for the dispatch family. -/
theorem caseB_constituentDecomposition_Y_inner_int
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {η₁ : ClassFunction ↥L ℂ} {a : ℕ} (θ : IrreducibleCharacter ↥H)
    (hcol : CaseBColBundle hyp h46 θ η₁ a) (hirr : CaseBIrrBundle hyp h46 θ η₁ a)
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    (hη₁Y : η₁ ∈ hyp.Yset) (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    {η' : ClassFunction ↥L ℂ} (hη'Y : η' ∈ hyp.Yset) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hirrAnc : (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂
          ≠ ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) →
      ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁ (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0
      ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) = 0
      ∧ ClassFunction.inner η₁.conj
          (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)).conj = 0) :
    ∃ n : ℤ, ClassFunction.inner (caseB_constituentDecomposition hyp h46 θ hcol hirr).Y
      (cY.extension η₁) = (n : ℂ) := by
  apply psiDecomp_Y_inner_int (caseB_constituentDecomposition hyp h46 θ hcol hirr)
  · exact caseB_constituentDecomposition_X_orthogonal hyp h46 hHK θ hcol hirr cY hη₁Y hη₁irr
      hrealc1 hdiffsuppc1 hc1barS1 hνZc1 hc1c1bar hη'Y hη'irr hee hsupp hirrAnc
  · rw [caseB_constituentDecomposition_tau1]
    exact caseB_constituentDecomposition_tau1_mem_ZIrr hyp h46 θ hcol hirr
  · exact hνZc1

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image — concrete dispatch family.**  The
specialization of `caseB_per_phi_anchored` to the mixed dispatch family `caseB_phi_family`: the
abstract decomposition family `D`, its seam-1 orthogonality `hXorth` and integrality `hbi` are all
resolved (`caseB_phi_family` / `caseB_constituentDecomposition_X_orthogonal` /
`caseB_constituentDecomposition_Y_inner_int`, the latter's `b` read off by choice).  For each
constituent `θ = i.val` of `Ind^L_{W₂} φ` (with `aᵢ = ⟨φ, Res^H_{W₂} θ⟩ > 0`):
`(Ind^L_H θ − aᵢ·η₁)^{hyp.tau} = (caseB_phi_family … i).X − aᵢ·cY.extension η₁`.

The remaining inputs are exactly the genuine §5/§6 content discharged at the capstone: the per-`θ`
column/irreducible structural bundles `hcol`/`hirr`, the `Y`-anchor `η₁` data (`hη₁` and its real /
support / conjugate facts), the partner anchor `η' ≠ η₁ ∈ Yset`, the per-`θ` anchor-vs-constituent
orthogonality `hirrAnc`, and the (6.8.2.2) aggregate `hXaggorth`/`hdecomp`
(`exists_decomposition_caseB`). -/
theorem caseB_per_phi_anchored_family
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Finite ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBColBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBIrrBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hη₁irr : IsIrreducibleCharacter η₁)
    (hrealc1 : ¬ ClassFunction.IsReal η₁)
    (hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hc1barS1 : η₁.conj ∈ hyp.Yset)
    (hνZc1 : cY.extension η₁ ∈ ZIrr G)
    (hc1c1bar : ClassFunction.inner η₁ η₁.conj = 0)
    {η' : ClassFunction ↥L ℂ} (hη'Y : η' ∈ hyp.Yset) (hη'irr : IsIrreducibleCharacter η')
    (hee : ClassFunction.inner η₁ η' = 0)
    (hsupp : (η₁ - η').support ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L)
    (hirrAnc : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
        ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0
        ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁.conj
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (caseB_phi_family hyp h46 hW2H hφ' hcol hirr i).X
        - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ := by
  have hX : ∀ j, ClassFunction.inner
      (caseB_phi_family hyp h46 hW2H hφ' hcol hirr j).X (cY.extension η₁) = 0 :=
    fun j => caseB_constituentDecomposition_X_orthogonal hyp h46 hHK j.val (hcol j) (hirr j) cY
      hη₁ hη₁irr hrealc1 hdiffsuppc1 hc1barS1 hνZc1 hc1c1bar hη'Y hη'irr hee hsupp (hirrAnc j)
  have hY : ∀ j, ∃ n : ℤ, ClassFunction.inner
      (caseB_phi_family hyp h46 hW2H hφ' hcol hirr j).Y (cY.extension η₁) = (n : ℂ) :=
    fun j => caseB_constituentDecomposition_Y_inner_int hyp h46 hHK j.val (hcol j) (hirr j) cY
      hη₁ hη₁irr hrealc1 hdiffsuppc1 hc1barS1 hνZc1 hc1c1bar hη'Y hη'irr hee hsupp (hirrAnc j)
  exact caseB_per_phi_anchored hyp hW2H hcen hφ' cY hη₁
    (caseB_phi_family hyp h46 hW2H hφ' hcol hirr)
    (fun j => caseB_phi_family_tau1 hyp h46 hW2H hφ' j)
    hXaggorth hdecomp (b := fun j => (hY j).choose) hX (fun j => (hY j).choose_spec) i

/-- **Peterfalvi (6.8.2.3), the per-`φ` anchored image — `Y`-anchor data internalized.**
Strengthens
`caseB_per_phi_anchored_family` by discharging the entire `η₁`-anchor / partner block from
`η₁ ∈ Yset` alone, via the textbook choice of partner `η' = η̄₁` (the complex conjugate): `η̄₁ ∈ Y`
(`Yset_closedUnderConjugate`), `η₁ ≠ η̄₁` (`Yset_hasNoRealCharacters`, Peterfalvi (5.2.a): odd order
⇒
no nontrivial real irreducible), `⟨η₁, η̄₁⟩ = 0` (distinct irreducibles), and `η₁ − η̄₁`
`H^#`-supported
(equal degree `Yset_apply_one`, `sMember_diffSupport_of_charValue_eq`).  The remaining inputs are
the
genuinely hard §5/§6 content: the per-`θ` column/irreducible bundles `hcol`/`hirr`, the per-`θ`
anchor-vs-constituent orthogonality `hirrAnc`, and the (6.8.2.2) aggregate `hXaggorth`/`hdecomp`. -/
theorem caseB_per_phi_anchored_fromYset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal] [Finite ↥H]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    [Fintype (OddOrder.Peterfalvi.S06.ticVdiff h46).W]
    [Invertible (Nat.card (OddOrder.Peterfalvi.S06.ticVdiff h46).W : ℂ)]
    {W2 : Subgroup ↥L} (hW2H : W2 ≤ H) [Finite ↥W2] [Invertible (Nat.card ↥W2 : ℂ)]
    [Fintype ↥(W2.subgroupOf H)] [Invertible (Nat.card ↥(W2.subgroupOf H) : ℂ)]
    (hcen : W2.subgroupOf H ≤ Subgroup.center ↥H)
    {φ : ClassFunction ↥W2 ℂ}
    (hφ' : IsIrreducibleCharacter
      (ClassFunction.compHom (Subgroup.subgroupOfEquivOfLe hW2H).toMonoidHom φ))
    (cY : OddOrder.Peterfalvi.S07.IsCoherent hyp.tau hyp.Yset
      (OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L))
    {η₁ : ClassFunction ↥L ℂ} (hη₁ : η₁ ∈ hyp.Yset)
    (hcol : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBColBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hirr : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      CaseBIrrBundle hyp h46 i.val η₁ (constituentWeight hφ' i.val))
    (hirrAnc : ∀ i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ},
      (∀ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 →
          OddOrder.Peterfalvi.S06.columnSum h46 χ₂
            ≠ ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) →
        ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁ (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0
        ∧ ClassFunction.inner η₁.conj (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)) = 0
        ∧ ClassFunction.inner η₁.conj
            (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ)).conj = 0)
    {Xagg : ClassFunction G ℂ}
    (hXaggorth : ClassFunction.inner Xagg (cY.extension η₁) = 0)
    (hdecomp : hyp.tau (ClassFunction.induce W2 φ - ((W2.subgroupOf H).index : ℂ) • η₁)
      = Xagg - ((W2.subgroupOf H).index : ℂ) • cY.extension η₁)
    (i : {θ : IrreducibleCharacter ↥H // 0 < constituentWeight hφ' θ}) :
    hyp.tau (ClassFunction.induce H (i.val : ClassFunction ↥H ℂ) - constituentWeight hφ' i.val • η₁)
      = (caseB_phi_family hyp h46 hW2H hφ' hcol hirr i).X
        - (constituentWeight hφ' i.val : ℂ) • cY.extension η₁ := by
  have hη₁irr : IsIrreducibleCharacter η₁ := hyp.isIrreducibleCharacter_of_mem_Yset hη₁
  have hconj : η₁.conj ∈ hyp.Yset := hyp.Yset_closedUnderConjugate hη₁
  have hrealc1 : ¬ η₁.IsReal :=
    fun hreal => hyp.Yset_hasNoRealCharacters.not_mem_of_isReal hreal hη₁
  have hne : η₁ ≠ η₁.conj := fun heq => hrealc1 heq.symm
  have hee : ClassFunction.inner η₁ η₁.conj = 0 := by
    have h := irreducibleCharacter_inner_eq_ite (⟨η₁, hη₁irr⟩ : IrreducibleCharacter ↥L)
      (⟨η₁.conj, hη₁irr.conj⟩ : IrreducibleCharacter ↥L)
    rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at h
    simpa using h
  have hval : η₁ (1 : ↥L) = η₁.conj (1 : ↥L) :=
    (hyp.Yset_apply_one hη₁).trans (hyp.Yset_apply_one hconj).symm
  have hsupp : (η₁ - η₁.conj).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hη₁) (hyp.Yset_subset_S hconj) hval
  have hdiffsuppc1 : (η₁.conj - η₁).support ⊆
      OddOrder.Peterfalvi.S04.supportInSubgroup (sharpImage H) L :=
    hyp.sMember_diffSupport_of_charValue_eq (hyp.Yset_subset_S hconj) (hyp.Yset_subset_S hη₁)
      hval.symm
  exact caseB_per_phi_anchored_family hyp h46 hHK hW2H hcen hφ' cY hη₁ hcol hirr
    hη₁irr hrealc1 hdiffsuppc1 hconj
    (cY.extension_mem_ZIrr η₁ (Submodule.subset_span hη₁)) hee
    hconj hη₁irr.conj hee hsupp hirrAnc hXaggorth hdecomp i

/-- **(6.8.2) X-member dichotomy: column or irreducible.**  For a non-trivial `θ : Irr ↥H`, the
induced character `Ind^L_H θ` either equals a non-trivial certain-type column `columnSum h46 χ₂`
(`χ₂ ≠ 1`) — the reducible/column branch — or is itself irreducible — the irreducible branch.

This is the cover dichotomy underlying the case-(B) `X = 𝒳(W₂)` coherence: every `X`-member splits
into the certain-type column part (coherent as a set, `certainTypeSet_isCoherent_tau_canonical`) or
the irreducible part (adjoined as a `{χ, χ̄}` pair via
`adjoin_irr_nonreal_of_supportedDecomposition`).
The irreducible branch is `caseB_irr_induce_isIrreducible` (the value↔index seam, settled session 43
cont.⁹); the column branch is the witnessing `χ₂`. -/
theorem caseB_induce_column_or_irreducible
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hθne : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H) :
    (∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      ∨ IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)) := by
  classical
  by_cases hc : ∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
      OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
  · exact Or.inl hc
  · exact Or.inr (caseB_irr_induce_isIrreducible h46 hHK hθne
      (fun χ₂ hχ₂ heq => hc ⟨χ₂, hχ₂, heq⟩))

/-- **(6.8.2) irreducible `X`-member ⊥ certain-type column** — the cross-orthogonality the case-(B)
`X`-coherence fold needs (an irreducible `Ind^L_H θ` adjoined onto the column base `cX_col`).

`⟨Ind^L_H θ, columnSum h46 χ₂⟩ = 0`: by additivity `columnSum = ∑_i μ_{ij}`, it suffices each grid
character `μ_{ij}` is `⊥ Ind^L_H θ`.  Both are irreducible, and distinct **by degree mod `|W₁|`**:
`Ind^L_H θ` has degree `|W₁|·θ(1) ≡ 0 (mod |W₁|)` (`induce_apply_one` + `index_H_eq_card_W1`),
whereas
a grid degree is `≡ ±1 (mod |W₁|)` (`certainType_degree_modEq`, sign `= ±1`), with `|W₁| ≠ 1`. So
the
irreducible Kronecker inner product vanishes.  (This is the same degree argument as the `X ⊥ Y`
`inner_columnFamily_mu_Yset_eq_zero`, with the `Y`-degree `|W₁|` replaced by `|W₁|·θ(1)`.) -/
theorem caseB_inner_irr_columnSum_eq_zero
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {θ : IrreducibleCharacter ↥H}
    (hirr : IsIrreducibleCharacter (ClassFunction.induce H (θ : ClassFunction ↥H ℂ)))
    (χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ) :
    ClassFunction.inner (ClassFunction.induce H (θ : ClassFunction ↥H ℂ))
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂) = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, inner_sum_right]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hne : ClassFunction.induce H (θ : ClassFunction ↥H ℂ)
      ≠ ((h46.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) := by
    intro heq
    obtain ⟨a, ha⟩ := h46.certainType_degree_modEq χ₂ i
    obtain ⟨d, hdpos, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast θ
    have hindeg : ClassFunction.induce H (θ : ClassFunction ↥H ℂ) (1 : ↥L)
        = (Nat.card hyp.W1 : ℂ) * (d : ℂ) := by
      rw [ClassFunction.induce_apply_one, hd, hyp.index_H_eq_card_W1]
    rw [← heq, hindeg] at ha
    have hcard : (Nat.card h46.W1 : ℂ) = (Nat.card hyp.W1 : ℂ) := by rw [hW1]
    rw [hcard] at ha
    have hw1 : Nat.card hyp.W1 ≠ 1 := fun h => hyp.W1_nontrivial (Subgroup.card_eq_one.mp h)
    have hsign : ((h46.columnFamily χ₂).sign : ℂ)
        = (Nat.card hyp.W1 : ℂ) * ((d : ℂ) - (a : ℂ)) := by linear_combination -ha
    have hsignZ : (h46.columnFamily χ₂).sign = (Nat.card hyp.W1 : ℤ) * ((d : ℤ) - a) := by
      exact_mod_cast hsign
    have hdvd1 : (Nat.card hyp.W1 : ℤ) ∣ 1 := by
      have hdvd : (Nat.card hyp.W1 : ℤ) ∣ (h46.columnFamily χ₂).sign := ⟨(d : ℤ) - a, hsignZ⟩
      rcases (h46.columnFamily χ₂).sign_eq with hs | hs
      · rwa [hs] at hdvd
      · rw [hs] at hdvd; exact (dvd_neg).mp hdvd
    exact hw1 (Nat.dvd_one.mp (by exact_mod_cast hdvd1))
  have hkron := irreducibleCharacter_inner_eq_ite
    (⟨ClassFunction.induce H (θ : ClassFunction ↥H ℂ), hirr⟩ : IrreducibleCharacter ↥L)
    ((h46.columnFamily χ₂).mu i)
  rw [if_neg (fun heq => hne (Subtype.ext_iff.mp heq))] at hkron
  simpa using hkron

omit [Invertible (Nat.card ↥H : ℂ)] in
/-- **(6.8.2) distinct certain-type columns are orthogonal** — `⟨columnSum h46 χ₂, columnSum h46
χ₂'⟩
= 0` for `χ₂ ≠ χ₂'`.  By additivity over `columnSum = ∑_i μ_{ij}`, it reduces to the cross-column
grid orthogonality `⟨μ_{ij}, μ_{i'j'}⟩ = 0` (`columnFamily_cross_products_zero`, Peterfalvi (4.1)),
read off via the same `i, i' = 0` case split as `columnFamily_mu_ne`.

This is the cross-orthogonality between different certain-type columns the case-(B) `X`-coherence
needs to assemble the column base across degree classes (columns of distinct `W₂`-duals — in
particular distinct degrees — are mutually orthogonal). -/
theorem inner_columnSum_cross_eq_zero
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L)
    [NeZero (Nat.card h46.W1)] [Fintype ↥(h46.W1 ⊔ h46.W2)]
    [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {χ₂ χ₂' : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂') :
    ClassFunction.inner (OddOrder.Peterfalvi.S06.columnSum h46 χ₂)
      (OddOrder.Peterfalvi.S06.columnSum h46 χ₂') = 0 := by
  rw [OddOrder.Peterfalvi.S06.columnSum_def, OddOrder.Peterfalvi.S06.columnSum_def,
    inner_sum_left]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [inner_sum_right]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have hz : (⟨1, h46.one_lt_card_W1⟩ : Fin (Nat.card h46.W1)) ≠ 0 := Fin.ne_of_val_ne (by simp)
  rcases eq_or_ne i 0 with hi | hi <;> rcases eq_or_ne j 0 with hj | hj
  · subst hi; subst hj; exact (h46.columnFamily_cross_products_zero hne hz hz).2.2.2
  · subst hi; exact (h46.columnFamily_cross_products_zero hne hz hj).2.2.1
  · subst hj; exact (h46.columnFamily_cross_products_zero hne hi hz).2.1
  · exact (h46.columnFamily_cross_products_zero hne hi hj).1

/-- **(6.8.2) `S`-member dichotomy: column or irreducible** — the `S`-level cover lifting the
per-`θ`
`caseB_induce_column_or_irreducible` over `S = {Ind^L_H θ | θ ≠ 1}`.  Every member of the Sibley set
`S` is either a non-trivial certain-type column `columnSum h46 χ₂` or an irreducible character.

This is the cover used to assemble the case-(B) `X = 𝒳(W₂)`-coherence (`X ⊆ S`): every `X`-member
splits into the certain-type column part (coherent as a set) or the irreducible part (adjoined as a
`{χ, χ̄}` pair).  It also feeds the `X ⊥ Y` orthogonality `hpair` of the `X ∪ Y` glue (a column is
`⊥ Y` by `inner_columnSum_Yset_eq_zero`; an irreducible `X`-member is `⊥ Y` by
degree/distinctness). -/
theorem caseB_S_member_column_or_irreducible
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Fintype ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {x : ClassFunction ↥L ℂ} (hx : x ∈ hyp.S) :
    (∃ χ₂ : (h46.W2.subgroupOf (h46.W1 ⊔ h46.W2)) →* ℂˣ, χ₂ ≠ 1 ∧
        OddOrder.Peterfalvi.S06.columnSum h46 χ₂ = x)
      ∨ IsIrreducibleCharacter x := by
  rw [hyp.S_eq, Set.mem_ofPred_eq] at hx
  obtain ⟨θ, hθne, rfl⟩ := hx
  have hθne' : (θ : ClassFunction ↥H ℂ) ≠ trivialClassFunction ↥H := fun heq =>
    hθne (Subtype.ext (heq.trans (IrreducibleCharacter.coe_trivialIrreducibleCharacter).symm))
  exact caseB_induce_column_or_irreducible h46 hHK hθne'

/-- **(6.8.2) `X(W₂) ⊥ Y`** — the `hpair` orthogonality input of the case-(B) `X ∪ Y` glue
(`coherentXunionYset_caseB_of_glued`).  Every `X`-member is orthogonal to every `Y`-member: by the
`S`-level cover (`caseB_S_member_column_or_irreducible`) an `X`-member is either a certain-type
column
(`⊥ Y` by `inner_columnSum_Yset_eq_zero`) or an irreducible distinct from the `Y`-member (`⊥ Y` by
`inner_irr_Yset_eq_zero`); the distinctness is the disjointness `X(W₂) ∩ Y = ∅` (`Y = S(⁅H,H⁆) ⊆
S(W₂)` since `W₂ ⊆ ⁅H,H⁆`, antitone, and `X(W₂)` is disjoint from `S(W₂)`). -/
theorem caseB_Xset_orthogonal_Yset
    (hyp : SibleyDadeHypothesis G L H) [H.Normal]
    (h46 : OddOrder.Peterfalvi.S06.Hypothesis46 (sharpImage H) L) (hHK : h46.K = H)
    (hW1 : h46.W1 = hyp.W1)
    [NeZero (Nat.card h46.W1)] [Invertible (Nat.card ↥h46.K : ℂ)]
    [Finite ↥(h46.W1 ⊔ h46.W2)] [Invertible (Nat.card ↥(h46.W1 ⊔ h46.W2) : ℂ)]
    {W2 : Subgroup ↥L} (hW2comm : W2 ≤ ⁅H, H⁆) :
    ∀ x ∈ hyp.Xset W2, ∀ y ∈ hyp.Yset, ClassFunction.inner x y = 0 := by
  have : Fintype ↥(h46.W1 ⊔ h46.W2) := Fintype.ofFinite _
  have hdisj : Disjoint (hyp.Xset W2) hyp.Yset := by
    have hYsub : hyp.Yset ⊆ hyp.SsubFiltration W2 :=
      hyp.SsubFiltration_antitone hW2comm
    exact Set.disjoint_of_subset_right hYsub (hyp.disjoint_Xset_SsubFiltration (Z := W2))
  intro x hx y hy
  rcases caseB_S_member_column_or_irreducible hyp h46 hHK (hyp.Xset_subset_S hx) with
    ⟨χ₂, -, rfl⟩ | hirr
  · exact inner_columnSum_Yset_eq_zero hyp h46 hW1 hy χ₂
  · exact inner_irr_Yset_eq_zero hyp hirr hy (fun heq => Set.disjoint_left.mp hdisj hx (heq.symm ▸
      hy))

end OddOrder.Peterfalvi.S08


