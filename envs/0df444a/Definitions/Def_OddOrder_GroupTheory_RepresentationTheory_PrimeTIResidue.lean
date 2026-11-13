-- Prove2me | Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
-- name    : OddOrder_GroupTheory_RepresentationTheory_PrimeTIResidue
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:19:14.186869+00:00
-- url     : https://prove2.me/theorems/8a2f3914-72a7-4192-be4e-c58d9df333df
-- title:
--   Prime TI residue characters (Peterfalvi (4.5), Feit–Thompson (13.2–13.3))
-- statement:
--   Ports the core of the prime-TI residue theory from the mathcomp character library, with the datum `PrimeTIResidueData` and the characters `primeTIred` of Peterfalvi (4.5).
--
--   Main declarations: `PrimeTIResidueData` (Prime-TI residue datum); `primeTIred` (Peterfalvi (4.5.a), `primeTIred`); `charGroupW2Equiv` (Index bridge `Fin p ≃ Ŵ₂`).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/GroupTheory/RepresentationTheory/PrimeTIResidue.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_IsometryDifferencePair
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedCharacter
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_InducedTransport
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ZIrrFourier
import Definitions.Def_OddOrder_Peterfalvi_S05_SigmaIsometry
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeClifford
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeSupport
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceCorePart1

namespace OddOrder.RepresentationTheory

open scoped BigOperators

open OddOrder.Peterfalvi.S07 (zSpan)

/-- **Prime-TI residue datum** (Peterfalvi (4.3.b)+(4.5.a), Coq `PFsection4.v`).

Bundles, over the pair `PU ≤ S`, the data that mathcomp derives from a
`primeTI_hypothesis` via `cyclicTIiso`:

* `mu2 i j ∈ Irr(S)` — the prime-TI irreducibles (`mu2_ i j`), `i : Fin q`, `j : Fin p`;
* `chi j ∈ Irr(PU)` — the residue characters (`chi_ j`), `j : Fin p`;

together with their defining relations (each a mathcomp theorem):

* `mu2_orthonormal`  : `⟨mu2 i j, mu2 i' j'⟩ = [i=i' ∧ j=j']`   (Coq `cfdot_prTIirr`);
* `chi_res`          : `chi j = Res_{PU} (mu2 0 j)`               (Coq `cfRes_prTIirr`);
* `ind_chi`          : `Ind_{PU}^S (chi j) = ∑_i mu2 i j`         (Coq `cfInd_prTIres`);
* `chi_zero`         : `chi 0 = 1_{PU}`                           (Coq `prTIres0`).

The grid columns `i ↦ mu2 i j` correspond to `SignedIrreducibleDifferenceFamily` columns
(cf. `OddOrder.Peterfalvi.S06.Hypothesis.columnFamily`). -/
structure PrimeTIResidueData (S : Type*) [Group S] [Fintype S]
    [Invertible (Nat.card S : ℂ)] (PU : Subgroup S) [Fintype ↥PU]
    [Invertible (Nat.card ↥PU : ℂ)] (q p : ℕ) [NeZero q] [NeZero p] where
  /-- The prime-TI irreducibles `mu2_ i j ∈ Irr(S)` (Coq `primeTIirr`). -/
  mu2 : Fin q → Fin p → IrreducibleCharacter S
  /-- The residue characters `chi_ j ∈ Irr(PU)` (Coq `primeTIres`). -/
  chi : Fin p → IrreducibleCharacter ↥PU
  /-- **(4.3.b)** Orthonormality `⟨mu2 i j, mu2 i' j'⟩ = [(i,j) = (i',j')]` (Coq
  `cfdot_prTIirr`): the `mu2 i j` are pairwise-distinct irreducibles. -/
  mu2_orthonormal : ∀ (i i' : Fin q) (j j' : Fin p),
    ClassFunction.inner (mu2 i j : ClassFunction S ℂ) (mu2 i' j' : ClassFunction S ℂ)
      = (if i = i' ∧ j = j' then 1 else 0)
  /-- **(4.5.a)** Restriction to `PU`: `chi j = Res_{PU} (mu2 0 j)` (Coq `cfRes_prTIirr` at
  `i = 0`; the restriction of `mu2 i j` to `PU` is independent of `i`). -/
  chi_res : ∀ j : Fin p,
    (chi j : ClassFunction ↥PU ℂ) = ClassFunction.restrict PU (mu2 0 j : ClassFunction S ℂ)
  /-- **(4.5.a)** Induction formula: `Ind_{PU}^S (chi j) = ∑_i mu2 i j` (Coq
  `cfInd_prTIres`). -/
  ind_chi : ∀ j : Fin p,
    ClassFunction.induce PU (chi j : ClassFunction ↥PU ℂ)
      = ∑ i : Fin q, (mu2 i j : ClassFunction S ℂ)
  /-- **(4.5.a)** The `0`-residue is the trivial character (Coq `prTIres0`). -/
  chi_zero : (chi 0 : ClassFunction ↥PU ℂ) = trivialClassFunction ↥PU
  /-- The Sylow `p`-subgroup `P ≤ PU` (`= S_F` realised inside `PU`), carrying the kernel
  condition of the `(P)`-nonlinear induced family `seqIndD PU S P 1`.  In the Feit–Thompson
  application `P = S_F` is the Fitting subgroup of `S` (elementary abelian of order `p^q`),
  and the residues `chi_ j` (`j ≠ 0`) are exactly the `Irr(PU)`-characters non-trivial on `P`. -/
  P : Subgroup ↥PU
  /-- **(4.5.b), kernel condition** (Coq `cfker_prTIres`, `PFsection4.v:801`): for `j ≠ 0` the
  residue `chi_ j` does **not** have `P` in its kernel (it is `P`-nonlinear).  Equivalently
  `P ⊄ ker (chi_ j)`, so `μ_j = Ind_{PU}^S (chi_ j) ∈ seqIndD PU S P 1`.  A genuine mathcomp
  theorem (the `j = 0` residue is trivial with full kernel by `chi_zero`; every other residue
  is a non-principal constituent of `Res_P (mu2 0 j)`, hence non-trivial on `P`). -/
  cfker_prTIres : ∀ j : Fin p, j ≠ 0 →
    ¬ ((P : Set ↥PU) ⊆ OddOrder.Peterfalvi.S03.characterKernel (chi j : ClassFunction ↥PU ℂ))
  /-- **Peterfalvi (4.5.b), `prTIres_irr_cases`** (Coq `PFsection4.v:620`, a genuine mathcomp
  `Theorem`).  The constituent classification of a prime-TI residue: for every irreducible
  `θ ∈ Irr(PU)`, exactly one of

  * **(residue case)** `θ = chi_ j` for some `j`  (equivalently `Ind_{PU}^S θ = μ_j`); or
  * **(induced-irreducible case)** `Ind_{PU}^S θ ∈ Irr(S)` and `Ind θ ≠ mu2 i j` for all
    `i, j` (a fresh irreducible, not a prime-TI constituent).

  This is the dichotomy `S1cases` uses to split the induced constituents of a member of
  `calS1` into the reducible `μ_j` family and the `𝒮 ∩ Irr(S)` part.

  **Why a posited field, not a derived theorem.**  The mathcomp proof establishes the
  *inertia group* `'I_S[θ] = PU` for `θ ∉ {chi_ j}` (whence `Ind θ` is irreducible by
  `inertia_Ind_irr`, whose repo analogue `isIrreducibleCharacter_induce_of_inertia_eq` is
  available) via a **`p`-group fixed-point count**: on the `W1`-conjugation action on
  `Irr(PU)`, the `z`-fixed irreducibles (`z ∈ W1` a `p`-element) equal the `z`-fixed classes
  (`card_afix_irr_classes`, repo
  `card_fixedPoints_conjByPermIrr_eq_card_fixedPoints_conjClassPerm`),
  and `sylow.pgroup_fix_mod` (mathlib `IsPGroup.card_modEq_card_fixedPoints`) with the
  coprimality `p ∤ |PU|` pins the fixed set to the residue image `{chi_ j}` of size `p`.  This
  computation consumes the **cyclic-TI structure** — the group `W1`, the decomposition
  `S = PU ⋊ W1`, the `W1`-action on `Irr(PU)`, and `coprime |PU| |W1|` — none of which is data
  of this structure (it is deliberately abstracted away, being supplied by the eventual
  `cyclicTIiso`-based constructor together with `mu2`/`chi`).  So the classification is not
  determined by the other fields; like `mu2_orthonormal`, `chi_res`, `ind_chi`, `cfker_prTIres`
  (all mathcomp theorems of the same `cyclicTIiso` provenance), it is posited here and
  discharged by the constructor.  See the module docstring / `issues/9014-primeti-residue-api.md`
  continuation #1–#2. -/
  prTIres_irr_cases : ∀ θ : IrreducibleCharacter ↥PU,
    (∃ j : Fin p, (θ : ClassFunction ↥PU ℂ) = (chi j : ClassFunction ↥PU ℂ))
      ∨ (IsIrreducibleCharacter (ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ))
          ∧ ∀ (i : Fin q) (j : Fin p),
              ClassFunction.induce PU (θ : ClassFunction ↥PU ℂ)
                ≠ (mu2 i j : ClassFunction S ℂ))

namespace PrimeTIResidueData

variable {S : Type*} [Group S] [Fintype S] [Invertible (Nat.card S : ℂ)]

variable {PU : Subgroup S} [Fintype ↥PU] [Invertible (Nat.card ↥PU : ℂ)]

variable {q p : ℕ} [NeZero q] [NeZero p]

variable (D : PrimeTIResidueData S PU q p)

/-- **Peterfalvi (4.5.a), `primeTIred`.** The reducible residue character
`μ_j := ∑_i mu2_ i j ∈ ℂ CF(S)` (Coq `primeTIred ptiW j`). -/
noncomputable def primeTIred (j : Fin p) : ClassFunction S ℂ :=
  ∑ i : Fin q, (D.mu2 i j : ClassFunction S ℂ)

end PrimeTIResidueData

end OddOrder.RepresentationTheory

namespace OddOrder.Peterfalvi.S06.Hypothesis

open OddOrder.RepresentationTheory

variable {L : Type*} [Group L] [Fintype L] (h : Hypothesis L)
  [Invertible (Nat.card L : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
  [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] [Invertible (Nat.card ↥h.K : ℂ)]
  [NeZero (Nat.card h.W1)] [NeZero (Nat.card h.W2)]

/-- **Index bridge `Fin p ≃ Ŵ₂`** for the `PrimeTIResidueData` constructor.  From
`card_charGroup_W2 : |Ŵ₂| = |W₂| = p` we get an equiv `Fin p ≃ Ŵ₂`, then compose with a
transposition so that the trivial column `1 : Ŵ₂` sits at index `0` (`charGroupW2Equiv_zero`). -/
noncomputable def charGroupW2Equiv :
    Fin (Nat.card h.W2) ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
  haveI : Fintype ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) := Fintype.ofFinite _
  letI e0 : Fin (Nat.card h.W2) ≃ ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :=
    (Fintype.equivFinOfCardEq
      (by rw [← Nat.card_eq_fintype_card, h.card_charGroup_W2])).symm
  (Equiv.swap 0 (e0.symm 1)).trans e0

omit [NeZero (Nat.card ↥h.W1)] in
omit [Invertible (Nat.card L : ℂ)] in
omit [Fintype ↥(h.W1 ⊔ h.W2)] in
omit [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)] in
omit [Invertible (Nat.card ↥h.K : ℂ)] in
@[simp] theorem charGroupW2Equiv_zero :
    h.charGroupW2Equiv 0 = 1 := by
  classical
  simp only [charGroupW2Equiv, Equiv.trans_apply, Equiv.swap_apply_left, Equiv.apply_symm_apply]

end OddOrder.Peterfalvi.S06.Hypothesis


