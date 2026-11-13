-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSibley
-- name    : OddOrder_Peterfalvi_S09_FrobeniusSibley
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:12:14.851665+00:00
-- url     : https://prove2.me/theorems/51f0aac9-7b3e-418e-9c29-04a45230f20a
-- title:
--   Peterfalvi (6.8) coherence for a Frobenius family: wiring the Sibley datum
-- statement:
--   The (6.8) coherence capstone `sibleySetup_is_coherent` produces the coherent extension $\nu$ for the induced family $S=\{\mathrm{Ind}_H^L\theta\mid\theta\in\mathrm{Irr}\,H,\theta\ne1_H\}$ from a Sibley–Dade hypothesis. Its Frobenius case (c1) is the intended producer for Peterfalvi (7.10); this file wires the `FrobeniusFamily` hypothesis to it.
--
--   Main results: `sibleyDadeHypothesis_of_frobenius` (the (6.8) Sibley datum for the $i$-th Frobenius member, case (c1)) and `coherence` (the (6.8) coherence for the $i$-th Frobenius member).
--
--   The bundle also proves 1 supporting lemma used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusSibley.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusSibley.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_CertificateDischarge
import Definitions.Def_OddOrder_Peterfalvi_S08_CoherenceTheorems

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The Sibley kernel's sharp image is the Frobenius kernel's sharp set.**  For the `i`-th member,
`sharpImage ((H_i).subgroupOf L_i) = (H_i)^#`: since `H_i ≤ L_i`, mapping `(H_i).subgroupOf L_i`
back
through `L_i.subtype` recovers `H_i`, and `sharpImage`/`sharp` both remove the identity.  This
aligns
the `SibleyDadeHypothesis` support coordinate (a subgroup of `↥L_i`) with the `of_isTISubset` /
`hypothesis71` support `sharp (H_i)` (a subset of `G`). -/
lemma sharpImage_subgroupOf_eq (F : FrobeniusFamily G k) (i : Fin k) :
    OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))
      = OddOrder.Peterfalvi.S04.sharp (F.H i : Set G) := by
  have hmap : Subgroup.map (F.L i).subtype ((F.H i).subgroupOf (F.L i)) = F.H i := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (F.kernel_le i)]
  rw [OddOrder.Peterfalvi.S08.sharpImage, hmap]
  rfl

open scoped Classical in
/-- **The Peterfalvi (6.8) Sibley datum for the `i`-th Frobenius member** (case c1).  Assembles a
`SibleyDadeHypothesis G L_i ((H_i).subgroupOf L_i)` from the Frobenius structure `hFrob`
(`isNormal`/`isComplement`/`ne_bot_*`), the TI/Dade datum of `H_i^#` (`of_isTISubset`, whose local
subgroups are trivial), and the kernel-nilpotency `hnilp` (available from
`frobeniusKernelIsNilpotent`
for the solvable `L_i` in the FT spine).  Feeding this to `sibleySetup_is_coherent` yields the
coherent extension `ν` for `S = {Ind_{H_i}^{L_i} θ | θ ≠ 1}` (issue 0044). -/
noncomputable def sibleyDadeHypothesis_of_frobenius [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    OddOrder.Peterfalvi.S08.SibleyDadeHypothesis G (F.L i) ((F.H i).subgroupOf (F.L i)) :=
  letI dade0 : OddOrder.Peterfalvi.S04.Hypothesis G
      (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) :=
    OddOrder.Peterfalvi.S04.Hypothesis.of_isTISubset
      (by
        rw [sharpImage_subgroupOf_eq]
        intro x hx
        exact OddOrder.Peterfalvi.S04.mem_sharp.mpr
          ⟨Set.mem_univ x, (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).2⟩)
      (by
        rw [sharpImage_subgroupOf_eq]
        intro x hx
        exact F.kernel_le i (OddOrder.Peterfalvi.S04.mem_sharp.mp hx).1)
      (by
        rw [sharpImage_subgroupOf_eq]
        intro l a ha
        exact (F.mem_kernel_sharp_conj_iff_of_mem_L i l.2).mpr ha)
      (by
        rw [sharpImage_subgroupOf_eq]
        exact F.isTI i)
  { W1 := C
    H_ne_bot := hFrob.ne_bot_kernel
    H_normal := hFrob.isNormal
    H_nilpotent := hnilp
    split := hFrob.isComplement
    W1_nontrivial := hFrob.ne_bot_complement
    card_L_odd := hodd.of_dvd_nat (Subgroup.card_subgroup_dvd_card (F.L i))
    H_sharp_ti := by rw [sharpImage_subgroupOf_eq]; exact F.isTI i
    dade := dade0
    dade_H_eq_bot := fun _ => rfl
    S := {φ : ClassFunction ↥(F.L i) ℂ | ∃ θ : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)),
      θ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) ∧
      φ = OddOrder.RepresentationTheory.ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)}
    S_eq := rfl
    cases := Or.inl hFrob }

/-- **The Peterfalvi (6.8) coherence for the `i`-th Frobenius member** — the coherent extension `ν`.
Applies the sorry-free (6.8) capstone `sibleySetup_is_coherent` to
`sibleyDadeHypothesis_of_frobenius`, producing an `IsCoherent` for the induced family
`S = {Ind_{H_i}^{L_i} θ | θ ≠ 1}` relative to the real Dade map.  Its `.extension` is Peterfalvi's
`ν`; `extension_inner_eq` gives the isometry and `extends_on_supported` the Dade agreement — the
inputs the (7.8.b)/(7.9) estimates of `card_G0_lower_bound` consume. -/
noncomputable def coherence [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).CoherenceTarget :=
  OddOrder.Peterfalvi.S08.sibleySetup_is_coherent
    (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob)

end FrobeniusFamily

end OddOrder.Peterfalvi.S09


