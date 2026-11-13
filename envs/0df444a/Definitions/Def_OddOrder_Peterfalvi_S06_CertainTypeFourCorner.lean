-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeFourCorner
-- name    : OddOrder_Peterfalvi_S06_CertainTypeFourCorner
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:17:50.642204+00:00
-- url     : https://prove2.me/theorems/cf6cf067-a231-4b24-9baa-5a6679d6da65
-- title:
--   Peterfalvi (4.10): the four-corner Dade identity
-- statement:
--   Formalizes Peterfalvi (4.10) (Peterfalvi, *Character Theory for the Odd Order Theorem*, §4, p. 24): for $0 \le i < w_1$ and $0 \le j < w_2$, $(\delta_j \mu_{ij} - \delta_j \mu_{0j} - \mu_{i0} + \mu_{00})^\tau = \omega_{ij}^\sigma - \omega_{0j}^\sigma - \omega_{i0}^\sigma + \omega_{00}^\sigma$.
--
--   Main declarations: `chiFourCornerOnV` ((4.10), piece (b), packaged); `fourCornerDiffSupported` ((4.10), the L-side four-corner `β` packaged in `CF(L, A₀)`); `omegaTic_fourcorner_mem_supportedSubmodule` ((4.10), G-side four-corner support).
--
--   The bundle also proves 11 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeFourCorner.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeFourCorner.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeIsometry

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **(4.10), piece (a): the `L`-side four-corner is the induced `W`-side four-corner.**
`δ_j(μ_{ij} − μ_{0j}) − δ_0(μ_{i0} − μ_{00}) = Ind_W^L(ω_{ij} − ω_{0j} − ω_{i0} + ω_{00})`, by the
(1.4) image relation `Ind_W^L(ω_{·j} − ω_{0j}) = δ_j(μ_{·j} − μ_{0j})` (`columnFamily_spec`,
`isometryDifferenceImage_induceZ`) for columns `χ₂` and `1`, with `Ind` additivity. -/
theorem fourcorner_signedDiff_eq_induce (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).signedDifference i - (h.columnFamily 1).signedDifference i
      = ClassFunction.induce h.sdiffTICyclicHypothesis.W
          ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
            - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
              - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite ↥(h.W1 ⊔ h.W2)
  rw [← h.columnFamily_spec χ₂ i, ← h.columnFamily_spec 1 i,
    h.isometryDifferenceImage_induceZ χ₂ i, h.isometryDifferenceImage_induceZ 1 i]
  simp only [← h.sdiffTICyclicHypothesis.induceLinear_apply]
  rw [← map_sub]

/-- On `W₂`, the column character `ω_{ij} = chiColumn χ₂ i` is independent of the row `i`:
`wFst` kills `W₂` (`wFst_eq_one_of_mem_W2`), so the `W₁`-character factor `(w1CharEquiv i)(wFst w)`
collapses to `1` and `ω_{ij}(w) = χ₂(wSnd w)` for every row.  The `W₂` companion of
`chiColumn_apply_of_mem_W1`. -/
theorem chiColumn_apply_of_mem_W2 (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {w : ↥h.sdiffTICyclicHypothesis.W}
    (hw : w ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W) :
    (h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) w
      = (χ₂ (h.sdiffTICyclicHypothesis.wSnd w) : ℂ) := by
  have hχ : (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w) = 1 := by
    rw [h.sdiffTICyclicHypothesis.wFst_eq_one_of_mem_W2 hw]; exact map_one _
  have h1 : h.sdiffTICyclicHypothesis.omegaProdChar (h.w1CharEquiv i) χ₂ w
      = (h.w1CharEquiv i) (h.sdiffTICyclicHypothesis.wFst w)
        * χ₂ (h.sdiffTICyclicHypothesis.wSnd w) := rfl
  rw [Hypothesis.chiColumn, h.sdiffTICyclicHypothesis.omega_apply, h1, hχ, one_mul]

/-- **(4.10), piece (b): the `W`-side four-corner is supported on `V = W − (W₁ ∪ W₂)`.**
The four-corner `ω_{ij} − ω_{0j} − (ω_{i0} − ω_{00})` vanishes off `V` because it dies on both
`W₁` and `W₂`:
* on `W₂` (`chiColumn_apply_of_mem_W2`) every `ω` collapses to its `χ₂`-value, independent of the
  row, so `ω_{ij} − ω_{0j} = 0` and `ω_{i0} − ω_{00} = 0`;
* on `W₁` (`chiColumn_apply_of_mem_W1`) every `ω` collapses to its `W₁`-character value,
  independent of the column, so `ω_{ij} − ω_{i0} = 0` and `ω_{0j} − ω_{00} = 0` (the four-corner
  rearranges to a cancelling pair).

This is the strong support `CF(W, W − (W₁ ∪ W₂)) = SupportedOnV ℂ toTICyclicHypothesis` that the
induced four-corner `Ind_W^L(·)` (piece (a)) needs for `Supp ⊆ V^L ⊆ A₀`, sidestepping the
`chiColumn`/`alphaCF` coercion mismatch of the direct `= alphaCF` route. -/
theorem chiColumn_fourcorner_mem_supportedSubmodule (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)))
      ∈ ClassFunction.supportedSubmodule
          (OddOrder.Peterfalvi.S04.supportInSubgroup h.toTICyclicHypothesis.V
            h.sdiffTICyclicHypothesis.W) := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro w hw
  rw [ClassFunction.mem_support] at hw
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  -- `toTICyclicHypothesis.V = ↑(W₁ ⊔ W₂) ∖ (↑W₁ ∪ ↑W₂)`
  have hVdef : h.toTICyclicHypothesis.V
      = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ ((h.W1 : Set ↥L) ∪ (h.W2 : Set ↥L)) := rfl
  rw [hVdef, Set.mem_sdiff, Set.mem_union, not_or]
  refine ⟨w.2, fun h1 => hw ?_, fun h2 => hw ?_⟩
  · -- `(w : L) ∈ W₁`: column difference cancels (row-only dependence)
    have hwmem : w ∈ h.sdiffTICyclicHypothesis.W1.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr h1
    simp only [ClassFunction.sub_apply, chiColumn_apply_of_mem_W1 h.toCore χ₂ i hwmem,
      chiColumn_apply_of_mem_W1 h.toCore χ₂ 0 hwmem, chiColumn_apply_of_mem_W1 h.toCore 1 i hwmem,
      chiColumn_apply_of_mem_W1 h.toCore 1 0 hwmem]
    ring
  · -- `(w : L) ∈ W₂`: row difference cancels (column-only dependence)
    have hwmem : w ∈ h.sdiffTICyclicHypothesis.W2.subgroupOf h.sdiffTICyclicHypothesis.W :=
      Subgroup.mem_subgroupOf.mpr h2
    simp only [ClassFunction.sub_apply, chiColumn_apply_of_mem_W2 h χ₂ i hwmem,
      chiColumn_apply_of_mem_W2 h χ₂ 0 hwmem, chiColumn_apply_of_mem_W2 h 1 i hwmem,
      chiColumn_apply_of_mem_W2 h 1 0 hwmem]
    ring

/-- **(4.10), piece (b), packaged**: the `W`-side four-corner as an element of
`CF(W, W − (W₁ ∪ W₂)) = SupportedOnV ℂ toTICyclicHypothesis`, the carrier fed to the L-side
induction `Ind_W^L` (its `toTICyclic` Dade map).  This bundles the membership
`chiColumn_fourcorner_mem_supportedSubmodule` as a subtype element
(`sdiff.W = toTICyclicHypothesis.W` definitionally). -/
noncomputable def chiFourCornerOnV (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ h.toTICyclicHypothesis :=
  ⟨(h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
      - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)),
   chiColumn_fourcorner_mem_supportedSubmodule h χ₂ i⟩

/-- **(4.10) L-side support bridge**: an `L`-conjugate of a point of `V = W − (W₁ ∪ W₂)` lands in
`A₀ = A ∪ {l·v·l⁻¹ | l ∈ L, v ∈ tic.V}`.  Since `V ⊆ W − W₂` maps (via `L ↪ G`) into
`tic.V = ↑W \ ↑W₂` (`tic_W_eq_map` for the `W`-part, `L.subtype` injectivity for the `∉ W₂` part),
every such conjugate has the required `A₀` form.  This is the group-theory core of
`Supp(Ind_W^L α) ⊆ V^L ⊆ A₀`, the L-side packaging that feeds the certain-type Dade map `h.tau`. -/
theorem coe_mem_A0_of_mem_conjugatesOfSet_toTICV (h : Hypothesis46 A L)
    {z : ↥L} (hz : z ∈ Group.conjugatesOfSet h.toTICyclicHypothesis.V) :
    (L.subtype z) ∈ (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V : Set G) := by
  obtain ⟨v, hvV, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hz
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hVdef : h.toTICyclicHypothesis.V
      = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ ((h.W1 : Set ↥L) ∪ (h.W2 : Set ↥L)) := rfl
  rw [hVdef, Set.mem_sdiff, Set.mem_union, not_or] at hvV
  obtain ⟨hvW, hvnW1, hvnW2⟩ := hvV
  have hvtic : (L.subtype v) ∈ h.tic.V := by
    rw [h.tic_V, Set.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [tic_W_eq_map h]
      exact Subgroup.mem_map.mpr ⟨v, hvW, rfl⟩
    · rintro (hmem | hmem)
      · rw [h.tic_W1] at hmem
        obtain ⟨w, hwW1, hweq⟩ := Subgroup.mem_map.mp hmem
        exact hvnW1 (L.subtype_injective hweq ▸ hwW1)
      · rw [h.tic_W2] at hmem
        obtain ⟨w, hwW2, hweq⟩ := Subgroup.mem_map.mp hmem
        exact hvnW2 (L.subtype_injective hweq ▸ hwW2)
  refine Or.inr ⟨L.subtype v, hvtic, L.subtype c, c.2, ?_⟩
  rw [← hc]
  simp [map_mul, map_inv]

/-- **(4.10) off-`V^G` foundation**: a point of `V = W − (W₁ ∪ W₂)` is self-centralizing into `L`,
`C_G(v) ⊆ L`.  This is the book's "for `x ∈ V`, `C_G(x) = W ⊂ L`": any `c` centralizing `v ∈ V`
conjugates `v` back into `V`, so by the TI property `V_ti` of (3.1) (`IsTISubset V W`) `c ∈ W`, and
`W = tic.W = (W₁ ⊔ W₂).map L.subtype ⊆ L`.  This forces the certain-type local subgroup `H(a) = ⊥`
on `V^L` (via `centralizer_eq_sup`/`centralizer_disjoint`), the structural fact behind
`β^τ` vanishing off `V^G`. -/
theorem centralizer_le_L_of_mem_ticVdiffV (h : Hypothesis46 A L) {v : G}
    (hv : v ∈ (ticVdiff h).V) :
    Subgroup.centralizer ({v} : Set G) ≤ L := by
  intro c hc
  have hcomm : c * v = v * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hconj : c * v * c⁻¹ = v := by rw [hcomm]; group
  have hcW : c ∈ (ticVdiff h).W := (ticVdiff h).V_ti c ⟨v, hv, by rw [hconj]; exact hv⟩
  exact le_trans (tic_W_eq_map h).le (Subgroup.map_subtype_le _) hcW

/-- The L-side `V = W − (W₁ ∪ W₂)` maps (under `L ↪ G`) into the G-side `ticVdiff.V`: both are
`W − (W₁ ∪ W₂)`, identified by `tic_W_eq_map`/`tic_W1`/`tic_W2` and `L.subtype` injectivity. -/
theorem coe_mem_ticVdiffV_of_mem_toTICV (h : Hypothesis46 A L) {v : ↥L}
    (hv : v ∈ h.toTICyclicHypothesis.V) :
    (L.subtype v) ∈ (ticVdiff h).V := by
  have hVdef : h.toTICyclicHypothesis.V
      = ((h.W1 ⊔ h.W2 : Subgroup ↥L) : Set ↥L) \ ((h.W1 : Set ↥L) ∪ (h.W2 : Set ↥L)) := rfl
  rw [hVdef, Set.mem_sdiff, Set.mem_union, not_or] at hv
  obtain ⟨hvW, hvnW1, hvnW2⟩ := hv
  refine ⟨?_, ?_⟩
  · rw [tic_W_eq_map h]
    exact Subgroup.mem_map.mpr ⟨v, hvW, rfl⟩
  · rw [Set.mem_union, not_or, h.tic_W1, h.tic_W2]
    refine ⟨fun hmem => ?_, fun hmem => ?_⟩
    · obtain ⟨w, hwW1, hweq⟩ := Subgroup.mem_map.mp hmem
      exact hvnW1 (L.subtype_injective hweq ▸ hwW1)
    · obtain ⟨w, hwW2, hweq⟩ := Subgroup.mem_map.mp hmem
      exact hvnW2 (L.subtype_injective hweq ▸ hwW2)

/-- Conjugation closure of `centralizer_le_L_of_mem_ticVdiffV`: a point `L`-conjugate (inside `L`)
to a point of `V` is still self-centralizing into `L`, `C_G(w) ⊆ L`.  If `c` centralizes
`w = l·v·l⁻¹` then `l⁻¹·c·l` centralizes `v`, hence lies in `L` (the base case), so
`c = l·(l⁻¹cl)·l⁻¹ ∈ L`.  Used for the `Supp β ⊆ V^L` base points of (4.10) off-`V^G`. -/
theorem centralizer_le_L_of_mem_conj_toTICV (h : Hypothesis46 A L) {w : ↥L}
    (hw : w ∈ Group.conjugatesOfSet h.toTICyclicHypothesis.V) :
    Subgroup.centralizer ({L.subtype w} : Set G) ≤ L := by
  obtain ⟨v, hvV, hconjv⟩ := Group.mem_conjugatesOfSet_iff.mp hw
  obtain ⟨l, hl⟩ := isConj_iff.mp hconjv
  intro c hc
  have hcw : c * L.subtype w = L.subtype w * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hwG : L.subtype w = L.subtype l * L.subtype v * (L.subtype l)⁻¹ := by
    rw [← hl]; simp [map_mul, map_inv]
  have hc' : (L.subtype l)⁻¹ * c * L.subtype l ∈ Subgroup.centralizer ({L.subtype v} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hvG : L.subtype v = (L.subtype l)⁻¹ * L.subtype w * L.subtype l := by rw [hwG]; group
    rw [hvG]
    calc (L.subtype l)⁻¹ * c * L.subtype l * ((L.subtype l)⁻¹ * L.subtype w * L.subtype l)
        = (L.subtype l)⁻¹ * (c * L.subtype w) * L.subtype l := by group
      _ = (L.subtype l)⁻¹ * (L.subtype w * c) * L.subtype l := by rw [hcw]
      _ = (L.subtype l)⁻¹ * L.subtype w * L.subtype l
            * ((L.subtype l)⁻¹ * c * L.subtype l) := by group
  have hc'L : (L.subtype l)⁻¹ * c * L.subtype l ∈ L :=
    centralizer_le_L_of_mem_ticVdiffV h (coe_mem_ticVdiffV_of_mem_toTICV h hvV) hc'
  have hceq : c = L.subtype l * ((L.subtype l)⁻¹ * c * L.subtype l) * (L.subtype l)⁻¹ := by group
  rw [hceq]
  exact L.mul_mem (L.mul_mem l.2 hc'L) (L.inv_mem l.2)

/-- **(4.10), the L-side four-corner is the toTICyclic Dade image of the carrier.**
`β = δ_j(μ_{ij} − μ_{0j}) − (μ_{i0} − μ_{00}) = Ind_W^L α` (piece (a)), and the toTICyclic Dade map
of `(L, W − (W₁ ∪ W₂))` *is* `Ind_W^L` (`tau_eq_induce`); since `↑(chiFourCornerOnV) = α` and
`sdiff.W = toTICyclicHypothesis.W` definitionally, the two agree.  Expressing `β` as a Dade image
controls its support (off `V^L`) via `full_map_eq_zero_of_not_mem_conjugatesOfSet_V`. -/
theorem signedDiff_fourcorner_eq_toTICDade (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (h.columnFamily χ₂).signedDifference i - (h.columnFamily 1).signedDifference i
      = h.toTICyclicFullDadeApplication.tau.toDadeMap (chiFourCornerOnV h χ₂ i) := by
  rw [fourcorner_signedDiff_eq_induce h χ₂ i]
  exact (h.toTICyclicHypothesis.tau_eq_induce
    h.toTICyclicFullDadeApplication.tau.toDadeIsometryData (chiFourCornerOnV h χ₂ i)).symm

/-- **(4.10), the L-side four-corner `β` packaged in `CF(L, A₀)`.**  `β = Ind_W^L α` is the Dade
image of the `V`-supported carrier (`signedDiff_fourcorner_eq_toTICDade`), so it vanishes off
`conjugatesOfSet(V)` (`full_map_eq_zero_of_not_mem_conjugatesOfSet_V`); every point of
`conjugatesOfSet(V)` maps into `A₀` (`coe_mem_A0_of_mem_conjugatesOfSet_toTICV`).  This is the
domain element fed to the certain-type Dade isometry `τ = h.tau` in (4.10). -/
noncomputable def fourCornerDiffSupported (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
      (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L :=
  ⟨(h.columnFamily χ₂).signedDifference i - (h.columnFamily 1).signedDifference i, by
    rw [ClassFunction.mem_supportedSubmodule]
    intro z hz
    rw [ClassFunction.mem_support] at hz
    rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
    apply coe_mem_A0_of_mem_conjugatesOfSet_toTICV h
    by_contra hc
    apply hz
    rw [signedDiff_fourcorner_eq_toTICDade h χ₂ i]
    exact h.toTICyclicHypothesis.full_map_eq_zero_of_not_mem_conjugatesOfSet_V
      h.toTICyclicFullDadeApplication (chiFourCornerOnV h χ₂ i) hc⟩

/-- **(4.10), crux (d): `β^τ` vanishes off `V^G`.**  `β^τ(g) = 0` whenever `g ∉ V^G`
(`= conjugatesOfSet (ticVdiff h).V`).  This is the book's "`β^τ(g) = 0` if `g ∉ V^G`", a
consequence of `Supp β ⊆ V^L` and the certain-type Dade map structure.

`β^τ = h.dade0.dadeMap β` (`IsDadeMap.unique`).  Off `dadeSupport` the value is `0`.  On
`dadeSupport`, `g` is `G`-conjugate to `a·h` with `a ∈ A₀`, `h ∈ H(a)`, and the value is `β(a)`;
if it is nonzero then `a ∈ Supp β ⊆ V^L`, so `C_G(a) ⊆ L` (`centralizer_le_L_of_mem_conj_toTICV`),
forcing `H(a) = ⊥` (`H_eq_bot_of_centralizer_le`), hence `h = 1` and `g` is conjugate to `a ∈ V^G`,
contradicting `g ∉ V^G`. -/
theorem fourCornerDade_eq_zero_of_not_mem_conjugatesV (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {g : G} (hg : g ∉ Group.conjugatesOfSet (ticVdiff h).V) :
    h.tau.toDadeMap (fourCornerDiffSupported h χ₂ i) g = 0 := by
  have hcoe : (fourCornerDiffSupported h χ₂ i :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ _ L) =
      h.toTICyclicFullDadeApplication.tau.toDadeMap (chiFourCornerOnV h χ₂ i) :=
    signedDiff_fourcorner_eq_toTICDade h χ₂ i
  have hsupp : ∀ z : ↥L,
      (fourCornerDiffSupported h χ₂ i : ClassFunction ↥L ℂ) z ≠ 0 →
      z ∈ Group.conjugatesOfSet h.toTICyclicHypothesis.V := fun z hz => by
    by_contra hc
    exact hz (by
      rw [hcoe]
      exact h.toTICyclicHypothesis.full_map_eq_zero_of_not_mem_conjugatesOfSet_V
        h.toTICyclicFullDadeApplication (chiFourCornerOnV h χ₂ i) hc)
  rw [show h.tau.toDadeMap = h.dade0.dadeMap (k := ℂ) from
      OddOrder.Peterfalvi.S04.IsDadeMap.unique h.tau.toDadeIsometryData.isDadeMap
        h.dade0.isDadeMap_dadeMap, h.dade0.dadeMap_apply]
  by_cases hgs : g ∈ h.dade0.dadeSupport
  · obtain ⟨a, hh', hh'mem, hga⟩ := h.dade0.mem_dadeSupport_iff.mp hgs
    rw [h.dade0.dadeValue_eq _ hh'mem hga]
    by_contra hne
    have hac := hsupp _ hne
    have hHbot := h.dade0.H_eq_bot_of_centralizer_le a
      (centralizer_le_L_of_mem_conj_toTICV h hac)
    rw [hHbot, Subgroup.mem_bot] at hh'mem
    rw [hh'mem, mul_one] at hga
    apply hg
    obtain ⟨v, hvV, hconjv⟩ := Group.mem_conjugatesOfSet_iff.mp hac
    rw [Group.mem_conjugatesOfSet_iff]
    refine ⟨L.subtype v, coe_mem_ticVdiffV_of_mem_toTICV h hvV, ?_⟩
    obtain ⟨cc, hcc⟩ := isConj_iff.mp hconjv
    refine IsConj.trans (isConj_iff.mpr ⟨L.subtype cc, ?_⟩) hga
    have := congrArg L.subtype hcc
    simpa [map_mul, map_inv] using this
  · rw [h.dade0.dadeValue_of_not_mem_dadeSupport _ hgs]

set_option backward.isDefEq.respectTransparency false in
/-- **(4.10), G-side four-corner support**: the `G`-side four-corner of the `ω_{ij}^{tic}`
characters lies in `CF(W, V) = SupportedOnV ℂ ticVdiff`.  Via `omegaProdCharTic_apply` the value
at `g` equals the `sdiff`-side four-corner at the bridge partner `e g`, so the W-side support
(`chiColumn_fourcorner_mem_supportedSubmodule`) transports: `e g ∈ V` (L-side) gives
`(g : G) ∈ ticVdiff.V` (`coe_mem_ticVdiffV_of_mem_toTICV`, `coe_ticWEquivSdiffW`).  This is the
carrier whose `σ` is the RHS of (4.10) — `σ` being a Dade map on it, the RHS vanishes off `V^G`. -/
theorem omegaTic_fourcorner_mem_supportedSubmodule (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    (((ticVdiff h).omega (omegaProdCharTic h χ₂ i) : ClassFunction (ticVdiff h).W ℂ)
        - ((ticVdiff h).omega (omegaProdCharTic h χ₂ 0) : ClassFunction (ticVdiff h).W ℂ)
        - (((ticVdiff h).omega (omegaProdCharTic h 1 i) : ClassFunction (ticVdiff h).W ℂ)
          - ((ticVdiff h).omega (omegaProdCharTic h 1 0) : ClassFunction (ticVdiff h).W ℂ)))
      ∈ ClassFunction.supportedSubmodule
          (OddOrder.Peterfalvi.S04.supportInSubgroup (ticVdiff h).V (ticVdiff h).W) := by
  rw [ClassFunction.mem_supportedSubmodule]
  intro g hg
  rw [ClassFunction.mem_support] at hg
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup]
  have e : ∀ (χ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (k : Fin (Nat.card h.W1)),
      ((ticVdiff h).omega (omegaProdCharTic h χ k) : ClassFunction (ticVdiff h).W ℂ) g
        = (h.chiColumn χ k : ClassFunction h.sdiffTICyclicHypothesis.W ℂ) (ticWEquivSdiffW h g) :=
    fun χ k => by rw [(ticVdiff h).omega_apply]; exact omegaProdCharTic_apply h χ k g
  rw [ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.sub_apply, e, e, e, e] at hg
  have hF := chiColumn_fourcorner_mem_supportedSubmodule h χ₂ i
  rw [ClassFunction.mem_supportedSubmodule] at hF
  have hgsupp : ticWEquivSdiffW h g ∈ ClassFunction.support
      ((h.chiColumn χ₂ i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - (h.chiColumn χ₂ 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
        - ((h.chiColumn 1 i : ClassFunction h.sdiffTICyclicHypothesis.W ℂ)
          - (h.chiColumn 1 0 : ClassFunction h.sdiffTICyclicHypothesis.W ℂ))) := by
    rw [ClassFunction.mem_support, ClassFunction.sub_apply, ClassFunction.sub_apply,
      ClassFunction.sub_apply]
    exact hg
  have hmem := hF hgsupp
  rw [OddOrder.Peterfalvi.S04.mem_supportInSubgroup] at hmem
  rw [← coe_ticWEquivSdiffW h g]
  exact coe_mem_ticVdiffV_of_mem_toTICV h hmem

/-- **(4.10), crux (c): the two sides agree on `V`.**  For `v ∈ V = W − (W₁ ∪ W₂)`,
`β^τ(v) = ω_{ij}^σ(v) − ω_{0j}^σ(v) − ω_{i0}^σ(v) + ω_{00}^σ(v)`.

Both reduce to the `sdiff`-side four-corner at the bridge partner `w = e v`: the LHS because
`τ` preserves values on `A₀ ⊇ V` (`tau_toDadeMap_apply_of_mem`) and `β = Ind_W^L α = σ_L(α)`
(`signedDiff_fourcorner_eq_toTICDade` + `sigma_eq_tau`) takes the value `α(w)` on `V`
(`sigma_apply_of_mem_V`); the RHS by `certainTypeOmegaSigma_apply_of_mem_V`. -/
theorem fourCornerDade_apply_eq_of_mem_V (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1))
    {v : G} (hv : v ∈ (ticVdiff h).V) :
    h.tau.toDadeMap (fourCornerDiffSupported h χ₂ i) v
      = certainTypeOmegaSigma h χ₂ i v - certainTypeOmegaSigma h χ₂ 0 v
        - (certainTypeOmegaSigma h 1 i v - certainTypeOmegaSigma h 1 0 v) := by
  have hv_ticV : v ∈ h.tic.V := by rw [h.tic_V]; exact hv
  have hvA0 : v ∈ (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V : Set G) :=
    Or.inr (OddOrder.GroupTheory.subset_conjClassSetIn hv_ticV)
  set w : h.sdiffTICyclicHypothesis.W := ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩ with hw
  have hwG : ((w : ↥L) : G) = v := coe_ticWEquivSdiffW h ⟨v, (ticVdiff h).V_subset_W hv⟩
  have hwL : (w : ↥L) = ⟨v, h.dade0.mem_L hvA0⟩ := Subtype.ext hwG
  have hwtoTICV : (w : ↥L) ∈ h.toTICyclicHypothesis.V := by
    refine ⟨w.2, fun hmem => ?_⟩
    rcases hmem with hW1 | hW2
    · exact hv.2 (Or.inl (by rw [h.tic_W1]; exact ⟨(w : ↥L), hW1, hwG⟩))
    · exact hv.2 (Or.inr (by rw [h.tic_W2]; exact ⟨(w : ↥L), hW2, hwG⟩))
  have hβsig : (fourCornerDiffSupported h χ₂ i : ClassFunction ↥L ℂ)
      = h.toTICyclicHypothesis.sigma rfl h.toTICyclicFullDadeApplication
          (chiFourCornerOnV h χ₂ i) :=
    (signedDiff_fourcorner_eq_toTICDade h χ₂ i).trans
      (h.toTICyclicHypothesis.sigma_eq_tau rfl h.toTICyclicFullDadeApplication
        (chiFourCornerOnV h χ₂ i)).symm
  rw [tau_toDadeMap_apply_of_mem h _ hvA0, hβsig, ← hwL,
    h.toTICyclicHypothesis.sigma_apply_of_mem_V rfl h.toTICyclicFullDadeApplication _ hwtoTICV,
    certainTypeOmegaSigma_apply_of_mem_V h χ₂ i hv,
    certainTypeOmegaSigma_apply_of_mem_V h χ₂ 0 hv,
    certainTypeOmegaSigma_apply_of_mem_V h 1 i hv,
    certainTypeOmegaSigma_apply_of_mem_V h 1 0 hv]
  rfl

/-- **Peterfalvi (4.10)** (the four-corner Dade identity).  For `0 ≤ i < w₁` and `0 ≤ j < w₂`,
`(δ_j μ_{ij} − δ_j μ_{0j} − μ_{i0} + μ_{00})^τ = ω_{ij}^σ − ω_{0j}^σ − ω_{i0}^σ + ω_{00}^σ`.

Both sides are class functions on `G`.  Off `V^G` both vanish — the LHS by crux (d)
(`fourCornerDade_eq_zero_of_not_mem_conjugatesV`), the RHS because it is `σ(α_G)` (σ-linearity)
with `α_G ∈ CF(W, V)` (`omegaTic_fourcorner_mem_supportedSubmodule`), so `σ(α_G) = τ_G(α_G)`
(`sigma_eq_tau`) vanishes off `V^G` (`full_map_eq_zero_of_not_mem_conjugatesOfSet_V`).  On `V^G`,
class-function invariance (`conj_eq`) reduces to a point of `V`, where the two agree by crux (c)
(`fourCornerDade_apply_eq_of_mem_V`). -/
theorem fourCorner_dade_eq (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)] [Fintype ↥(h.W1 ⊔ h.W2)]
    [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    h.tau.toDadeMap (fourCornerDiffSupported h χ₂ i)
      = certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂ 0
        - (certainTypeOmegaSigma h 1 i - certainTypeOmegaSigma h 1 0) := by
  set γ : OddOrder.Peterfalvi.S05.TICyclicHypothesis.SupportedOnV ℂ (ticVdiff h) :=
    ⟨((ticVdiff h).omega (omegaProdCharTic h χ₂ i) : ClassFunction (ticVdiff h).W ℂ)
        - ((ticVdiff h).omega (omegaProdCharTic h χ₂ 0) : ClassFunction (ticVdiff h).W ℂ)
        - (((ticVdiff h).omega (omegaProdCharTic h 1 i) : ClassFunction (ticVdiff h).W ℂ)
          - ((ticVdiff h).omega (omegaProdCharTic h 1 0) : ClassFunction (ticVdiff h).W ℂ)),
     omegaTic_fourcorner_mem_supportedSubmodule h χ₂ i⟩ with hγ
  have hRHSeq : (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂ 0
        - (certainTypeOmegaSigma h 1 i - certainTypeOmegaSigma h 1 0))
      = (ticVdiff h).sigma rfl (ticVdiffFullDadeApplication h) (↑γ) := by
    simp only [certainTypeOmegaSigma]
    rw [← map_sub, ← map_sub, ← map_sub]
  ext g
  by_cases hg : g ∈ Group.conjugatesOfSet (ticVdiff h).V
  · obtain ⟨v, hvV, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hg
    obtain ⟨x, hx⟩ := isConj_iff.mp hconj
    rw [← hx, ClassFunction.conj_eq _ v x, ClassFunction.conj_eq _ v x,
      ClassFunction.sub_apply, ClassFunction.sub_apply, ClassFunction.sub_apply]
    exact fourCornerDade_apply_eq_of_mem_V h χ₂ i hvV
  · rw [fourCornerDade_eq_zero_of_not_mem_conjugatesV h χ₂ i hg, hRHSeq,
      (ticVdiff h).sigma_eq_tau rfl (ticVdiffFullDadeApplication h) γ]
    exact ((ticVdiff h).full_map_eq_zero_of_not_mem_conjugatesOfSet_V
      (ticVdiffFullDadeApplication h) γ hg).symm

end OddOrder.Peterfalvi.S06


