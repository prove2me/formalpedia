-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusHypothesis78
-- name    : OddOrder_Peterfalvi_S09_FrobeniusHypothesis78
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T08:15:27.805059+00:00
-- url     : https://prove2.me/theorems/4ae372e8-4708-4967-83dd-dd0803987546
-- title:
--   Peterfalvi (7.8) for a Frobenius family: assembling the Hypothesis78
-- statement:
--   Downstream of the Frobenius Sibley wiring: each `FrobeniusFamily` member $i$ carries the full Peterfalvi (7.8) structure `Hypothesis78 G (H_i^#) L_i`, built from the (6.8) coherent extension for the induced family.
--
--   Main definitions: `PlacedInducedFamily` (data form of the placed induced family of (7.6)/(7.8)), `placedInducedFamily`, `sibleyToHypothesis71` (the (7.1) datum with the coherence's Dade map), `sibleyPlacedFamily` and `hypothesis78` (Peterfalvi (7.8) for the $i$-th Frobenius member).
--
--   The bundle also proves 2 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S09_FrobeniusHypothesis78.lean

/-
Copyright (c) 2026 Yawara ISHIDA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S09_FrobeniusHypothesis78.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S09_FrobeniusSibley

namespace OddOrder.Peterfalvi.S09

open OddOrder.RepresentationTheory

/-- **Data form of the placed induced family** (Peterfalvi (7.6)/(7.8)).  Bundles the `Fin (n+1)`-
indexed representatives `θ` with the distinguished induced character `χdist` at index `0` and the
trivial character `1_K` at `ind1H ≠ 0`, as *data* (not `∃`) so it can be projected inside a
`Type`-valued `Hypothesis78` construction.  Produced from `exists_placed_induced_family` via
`choose` (`Classical.choose`, hence `noncomputable`). -/
structure PlacedInducedFamily {L : Type*} [Group L] [Fintype L] (K : Subgroup L) [K.Normal]
    [Fintype ↥K] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    (χdist : ClassFunction L ℂ) where
  /-- One less than the number of distinct induced characters. -/
  n : ℕ
  /-- Representatives, distinguished member at `0`. -/
  θ : Fin (n + 1) → IrreducibleCharacter ↥K
  /-- The index of the trivial character `1_K`. -/
  ind1H : Fin (n + 1)
  ind1H_ne_zero : ind1H ≠ 0
  induce_zero_eq : ClassFunction.induce K (θ 0 : ClassFunction ↥K ℂ) = χdist
  triv : θ ind1H = trivialIrreducibleCharacter ↥K
  inj : Function.Injective (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))
  cover : ∀ φ : IrreducibleCharacter ↥K,
    ClassFunction.induce K (φ : ClassFunction ↥K ℂ) ∈
      Set.range (fun i => ClassFunction.induce K (θ i : ClassFunction ↥K ℂ))

/-- Construct the placed induced family as data from the existential
`exists_placed_induced_family`. -/
noncomputable def placedInducedFamily {L : Type*} [Group L] [Fintype L] (K : Subgroup L) [K.Normal]
    [Fintype ↥K] [Invertible (Nat.card L : ℂ)] [Invertible (Nat.card ↥K : ℂ)]
    (χdist : ClassFunction L ℂ)
    (hχ_range : χdist ∈ Set.range (fun φ : IrreducibleCharacter ↥K =>
      ClassFunction.induce K (φ : ClassFunction ↥K ℂ)))
    (hχ_ne : χdist ≠ ClassFunction.induce K
      (trivialIrreducibleCharacter ↥K : ClassFunction ↥K ℂ)) :
    PlacedInducedFamily K χdist := by
  choose n θ ind1H hind1H h0 htriv hinj hcover using
    OddOrder.Peterfalvi.S09.Cert.exists_placed_induced_family K χdist hχ_range hχ_ne
  exact ⟨n, θ, ind1H, hind1H, h0, htriv, hinj, hcover⟩

namespace FrobeniusFamily

variable {G : Type*} [Group G] {k : ℕ}

/-- **The (7.1) datum with the coherence's Dade map** (mirrors `S14.Hypothesis.toHypothesis71`).
Its `τ = (dade.fullDadeIsometryData hconj).toDadeIsometryData.toDadeMap` is *definitionally* the
Dade
map for which `F.coherence` is coherent (`coherence_hagree_dadeMap` produces exactly this), so it is
the `Hypothesis71` to feed `hypothesis78OfDade` alongside `ν = F.coherence.extension`. -/
noncomputable def sibleyToHypothesis71 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    Hypothesis71 G (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) where
  hyp := (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
  τ := (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
    |>.fullDadeIsometryData.toDadeIsometryData.toDadeMap
  isDadeMap := (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade
    |>.fullDadeIsometryData.toDadeIsometryData.isDadeMap

/-- **The distinguished character for the `i`-th Frobenius member** (Peterfalvi (7.8)/(12.13)
analog).
The Sibley family `S = {Ind θ | θ ∈ Irr K_i, θ ≠ 1}` contains a member of degree `[L_i:K_i]`, namely
`Ind_{K_i}^{L_i} θ` for a nontrivial **linear** `θ`. Exists because `K_i = (H_i).subgroupOf L_i` is
a
nontrivial nilpotent group (`hnilp` + `hFrob.ne_bot_kernel`), hence not perfect
(`exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top`); `induce_apply_one` gives
the induced degree `[L_i:K_i]·1`. -/
theorem exists_sibley_distinguished_char [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    ∃ χ ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S,
      χ (1 : ↥(F.L i)) = (((F.H i).subgroupOf (F.L i)).index : ℂ) := by
  have : ((F.H i).subgroupOf (F.L i)).Normal := hFrob.isNormal
  have : Nontrivial ↥((F.H i).subgroupOf (F.L i)) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hFrob.ne_bot_kernel
  have : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)) := hnilp
  have hcomm : commutator ↥((F.H i).subgroupOf (F.L i)) ≠ ⊤ :=
    (Group.IsSolvable.commutator_lt_top_of_nontrivial _).ne
  obtain ⟨θ, hθ_ne, hθ_deg⟩ :=
    OddOrder.Peterfalvi.S08.exists_irreducibleCharacter_ne_trivial_degree_one_of_commutator_ne_top
      hcomm
  refine ⟨ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ : ClassFunction _ ℂ),
    ⟨θ, hθ_ne, rfl⟩, ?_⟩
  rw [ClassFunction.induce_apply_one, hθ_deg, mul_one]

open OddOrder.Peterfalvi.S09.Cert in
/-- **The placed induced family used inside `hypothesis78`, exposed as data.**  Built with the same
distinguished character `Classical.choose (exists_sibley_distinguished_char …)` as the internal
`let pf` of `hypothesis78`; the range/nontriviality proof arguments of `placedInducedFamily` are
irrelevant (`Prop`), so this is *definitionally equal* to that internal `pf`.  This exposes the
family representatives `θ` and their `cover`/`inj` so the (7.9) conjugate index can be produced. -/
noncomputable def sibleyPlacedFamily [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Fintype ↥((F.H i).subgroupOf (F.L i))]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    PlacedInducedFamily ((F.H i).subgroupOf (F.L i))
      (Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)) := by
  classical
  refine placedInducedFamily ((F.H i).subgroupOf (F.L i)) _ ?_ ?_
  · obtain ⟨θlin, _, hχ_eq⟩ :=
      (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).1
    exact ⟨θlin, hχ_eq.symm⟩
  · obtain ⟨θlin, hθ_ne, hχ_eq⟩ :=
      (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).1
    exact hχ_eq ▸ induce_ne_trivialChar_induce ((F.H i).subgroupOf (F.L i)) θlin hθ_ne

open OddOrder.Peterfalvi.S09.Cert in
/-- **Peterfalvi (7.8) for the `i`-th Frobenius member**: `Hypothesis78 G (H_i^#) L_i`.  Assembles
`hypothesis78OfDade` from the (6.8) coherence `F.coherence` (extension `ν`, `nu_isometry`, (7.8.a)
agreement), the placed induced family (distinguished `Ind θ_lin` at `0`, trivial `1_{K_i}` at
`ind1H`), and the support/degree data — mirroring `S14.witness_L_hypothesis78`.  This is the (7.8)
hypothesis to which the (7.8.b) norm bound `zetaNuRhoNormSq_ge_of_facts` applies, en route to
`card_G0_lower_bound` (7.10, issue 0044).  Returned as **data** (not `Nonempty`) so the (7.9)
two-family `Hypothesis79` wiring can project its `hyp76.hyp71.hyp.dadeSupport`. -/
noncomputable def hypothesis78 [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    Hypothesis78 G (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i)))
      (F.L i) := by
  classical
  haveI hKnorm : ((F.H i).subgroupOf (F.L i)).Normal := hFrob.isNormal
  have coh := F.coherence i hodd hnilp C hFrob
  -- `H_i ≤ L_i` and the `L_i`-conjugation invariance of `H_i`.
  have hHL : F.H i ≤ F.L i := F.kernel_le i
  have hHnorm : ∀ (l : ↥(F.L i)) {h : G}, h ∈ F.H i →
      (l : G) * h * (l : G)⁻¹ ∈ F.H i :=
    fun l _h hh => (F.mem_kernel_conj_iff_of_mem_L i l.2).mpr hh
  -- The type-I support `A(L_i) = H_i^#`.
  have hAH : OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))
      = (F.H i : Set G) \ {1} := F.sharpImage_subgroupOf_eq i
  -- The placed induced family (as data), exposed via `sibleyPlacedFamily` (defeq to the inline
  -- `pf`).
  let pf := F.sibleyPlacedFamily i hodd hnilp C hFrob
  have hχdeg : (Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob))
      (1 : ↥(F.L i)) = (((F.H i).subgroupOf (F.L i)).index : ℂ) :=
    (Classical.choose_spec (F.exists_sibley_distinguished_char i hodd hnilp C hFrob)).2
  let n := pf.n
  let θ := pf.θ
  let ind1H := pf.ind1H
  have hind1H : ind1H ≠ 0 := pf.ind1H_ne_zero
  have h0 : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ 0 : ClassFunction _ ℂ)
      = Classical.choose (F.exists_sibley_distinguished_char i hodd hnilp C hFrob) :=
    pf.induce_zero_eq
  have htriv : θ ind1H = trivialIrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)) := pf.triv
  have hinj : Function.Injective
    (fun j => ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ j : ClassFunction _ ℂ)) := pf.inj
  have hcover : ∀ φ : IrreducibleCharacter ↥((F.H i).subgroupOf (F.L i)),
      ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (φ : ClassFunction _ ℂ) ∈
        Set.range fun j => ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (θ j : ClassFunction _ ℂ) := pf.cover
  -- `Ind (θ 0)(1) = [L_i:K_i]`.
  have hdeg0 : ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ 0 : ClassFunction _ ℂ)
      (1 : ↥(F.L i)) = (((F.H i).subgroupOf (F.L i)).index : ℂ) := by rw [h0]; exact hχdeg
  -- Every non-trivial member `Ind θ_j` (`j ≠ ind1H`) lies in the coherent family `S`.
  have hSmem : ∀ j, j ≠ ind1H →
      ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ j : ClassFunction _ ℂ)
        ∈ (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).S := by
    intro j hj
    refine ⟨θ j, fun htriv_j => hj (hinj ?_), rfl⟩
    change ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ j : ClassFunction _ ℂ)
        = ClassFunction.induce ((F.H i).subgroupOf (F.L i)) (θ ind1H : ClassFunction _ ℂ)
    rw [htriv_j, htriv]
  -- Degree coefficients `d_j = θ_j(1)`.
  let d : Fin (n + 1) → ℂ :=
    fun j => (θ j : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)
      (1 : ↥((F.H i).subgroupOf (F.L i)))
  have hd : ∀ j, d j = (θ j : ClassFunction ↥((F.H i).subgroupOf (F.L i)) ℂ)
      (1 : ↥((F.H i).subgroupOf (F.L i))) := fun _ => rfl
  -- `ζ_j(1) = d_j · ζ_0(1)`.
  have hdeg : ∀ j, ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ j : ClassFunction _ ℂ) (1 : ↥(F.L i))
      = d j * ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i)) := by
    intro j
    rw [ClassFunction.induce_apply_one ((F.H i).subgroupOf (F.L i))
        (θ j : ClassFunction _ ℂ), hdeg0, hd j]
    ring
  -- `ζ_0(1) = ζ_{ind1H}(1)` (both `[L_i:K_i]`).
  have hdeg_match : ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ 0 : ClassFunction _ ℂ) (1 : ↥(F.L i))
      = ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ ind1H : ClassFunction _ ℂ) (1 : ↥(F.L i)) := by
    rw [hdeg0, htriv]
    change (((F.H i).subgroupOf (F.L i)).index : ℂ)
        = ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (trivialClassFunction ↥((F.H i).subgroupOf (F.L i))) (1 : ↥(F.L i))
    rw [induce_trivialChar_apply_eq_index _ (Subgroup.one_mem _)]
  -- `ψ_j = ζ_j − d_j ζ_0` is supported on `A(L_i) = H_i^#`.
  have psi_support : ∀ j, (ClassFunction.induce ((F.H i).subgroupOf (F.L i))
        (θ j : ClassFunction _ ℂ)
      - d j • ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          (θ 0 : ClassFunction _ ℂ)).support
      ⊆ OddOrder.Peterfalvi.S04.supportInSubgroup
          (OddOrder.Peterfalvi.S08.sharpImage ((F.H i).subgroupOf (F.L i))) (F.L i) := by
    intro j
    refine (induce_diff_support (θ j) (θ 0) (d j) (hdeg j)).trans ?_
    intro x hx
    rw [Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff] at hx
    exact (mem_supportInSubgroup_sharp_subgroupOf_iff (F.H i) hAH x).mpr ⟨hx.1, hx.2⟩
  -- Assemble the `Hypothesis78` via `hypothesis78OfDade`.  The `hτ` isometry is the coherence
  -- Dade map's own `isDadeIsometry` (matching `sibleyToHypothesis71.τ` definitionally).
  refine hypothesis78OfDade (F.sibleyToHypothesis71 i hodd hnilp C hFrob)
    (OddOrder.Peterfalvi.S04.isDadeIsometry_of_isDadeMap _ _
      (F.sibleyToHypothesis71 i hodd hnilp C hFrob).isDadeMap)
    (F.H i) hHL hHnorm hAH θ hinj hcover d psi_support hdeg ind1H hind1H htriv hdeg_match
    coh.extension ?_ ?_
  · -- `nu_isometry`: the coherent extension is isometric on the family members.
    intro a b ha hb
    exact coherence_extension_inner_eq_on_family coh (hSmem a ha) (hSmem b hb)
  · -- `hagree`: the (7.8.a) coherence agreement `τ ψ_j = ν ζ_j − d_j ν ζ_0`.
    intro a _ha0 ha_ind
    obtain ⟨deg_a, -, hdeg_a_eq⟩ := irreducibleCharacter_apply_one_eq_pos_natCast (θ a)
    exact coherence_hagree_dadeMap
      (F.sibleyDadeHypothesis_of_frobenius i hodd hnilp C hFrob).dade coh
      (hSmem a ha_ind) (hSmem 0 (Ne.symm hind1H)) (m0 := 1) (mi := deg_a) (by norm_num)
      (by rw [hd a, hdeg_a_eq, Nat.cast_one, div_one]) (psi_support a)

/-- **Projection: the `hypothesis78` family is `Ind ∘ θ` of the exposed placed family** (defeq). -/
theorem hypothesis78_hyp76_zeta_eq [Fintype G] [Invertible (Nat.card G : ℂ)]
    (F : FrobeniusFamily G k) (i : Fin k) (hodd : Odd (Nat.card G))
    [Fintype ↥(F.L i)] [Invertible (Nat.card ↥(F.L i) : ℂ)]
    [Fintype ↥((F.H i).subgroupOf (F.L i))]
    [Invertible (Nat.card ↥((F.H i).subgroupOf (F.L i)) : ℂ)]
    [((F.H i).subgroupOf (F.L i)).Normal]
    (hnilp : Group.IsNilpotent ↥((F.H i).subgroupOf (F.L i)))
    (C : Subgroup ↥(F.L i))
    (hFrob : OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(F.L i) ((F.H i).subgroupOf (F.L i)) C) :
    (F.hypothesis78 i hodd hnilp C hFrob).hyp76.zeta
      = fun j => ClassFunction.induce ((F.H i).subgroupOf (F.L i))
          ((F.sibleyPlacedFamily i hodd hnilp C hFrob).θ j : ClassFunction _ ℂ) := rfl

end FrobeniusFamily

end OddOrder.Peterfalvi.S09


