-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeCoherence
-- name    : OddOrder_Peterfalvi_S06_CertainTypeCoherence
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T06:23:12.604189+00:00
-- url     : https://prove2.me/theorems/37d6a403-21e1-49d4-8c5c-17d9fc4de60f
-- title:
--   Peterfalvi (4.9)(b): coherence of the certain-type characters
-- statement:
--   Peterfalvi, *Character Theory for the Odd Order Theorem*, §4, p. 24, Theorem (4.9): the certain-type Dade data is packaged into a coherent isometry. Fix a column $k$ and let $\mathcal{T}$ be the set of certain-type column characters of $L$ of the same degree as $\mu_k$.
--
--   Main definitions: `columnSum` (the column character $\mu_j=\sum_i\mu_{ij}$, Peterfalvi (4.5.a)), `certainTypeExtension` (the coherent extension $\nu$ of (4.9)(b)), `certainTypeRImage` and `certainTypeR` (the reducible $R(\mu_j)$ image family of (5.2.d)/(5.3.b)) and `certainTypeMemberDecomposition` (the per-column $\nu$-aux decomposition). Also proves the cross-orthogonality (5.2.e) of two distinct column families.
--
--   The bundle also proves 15 supporting lemmas used by later statements.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainTypeCoherence.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainTypeCoherence.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_CertainTypeConjugation
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_DifferenceImage
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_NormInequalities
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_PsiDecomposition
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_CoherenceUnion
import Definitions.Def_OddOrder_Peterfalvi_S07_Coherence_FamilyBundleDade

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

open scoped IsMulCommutative

variable {G : Type*} [Group G] [Fintype G]

variable {A : Set G} {L : Subgroup G} [Fintype ↥L]

variable [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]

/-- **The certain-type column character** `μ_j = ∑_{0≤i<w₁} μ_{ij}` (Peterfalvi (4.5.a)).  This is
the character `μ_j` appearing in Theorem (4.9); `certainType_columnSum_conj` identifies its complex
conjugate as the column `μ_{j'}`, and `columnFamily_mu_sum_inner` gives its Gram matrix
`⟨μ_j, μ_k⟩ = w₁·δ_{jk}`. -/
noncomputable def columnSum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) : ClassFunction ↥L ℂ :=
  ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)

theorem columnSum_def (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    columnSum h χ₂ = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) :=
  rfl

open scoped Classical in
/-- **The per-basis rule of the coherent extension.**  On the irreducible `ω`, return the signed
`σ`-image `δ_j ω_{ij}^σ` if `ω = μ_{ij}` is a certain-type character, and `0` otherwise.  The
choice of witness `(χ₂, i)` is irrelevant by `columnFamily_mu_injective`. -/
noncomputable def certainTypeExtensionFun (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)] :
    IrreducibleCharacter ↥L → ClassFunction G ℂ :=
  fun ω =>
    if hex : ∃ p : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) × Fin (Nat.card h.W1),
        (h.columnFamily p.1).mu p.2 = ω then
      (h.columnFamily hex.choose.1).sign • certainTypeOmegaSigma h hex.choose.1 hex.choose.2
    else 0

/-- **The coherent extension `ν` of Peterfalvi (4.9)(b).**  The global `ℤ`-linear map
`CF(L) → CF(G)` sending each certain-type irreducible `μ_{ij}` to `δ_j ω_{ij}^σ` (every other
irreducible to `0`), built on the basis `Irr(L)` (`irreducibleCharacterBasis`) and restricted to
`ℤ`-scalars to land in `S07.IntegralCharacterMap`. -/
noncomputable def certainTypeExtension (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)] :
    S07.IntegralCharacterMap ↥L G :=
  ((S05.irreducibleCharacterBasis (G := ↥L)).constr ℂ (certainTypeExtensionFun h)).restrictScalars ℤ

/-- **Defining value of `ν` on a certain-type irreducible**: `ν(μ_{ij}) = δ_j ω_{ij}^σ`.  The basis
rule `certainTypeExtensionFun` selects the unique witness `(χ₂, i)` by
`columnFamily_mu_injective`. -/
theorem certainTypeExtension_mu (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    certainTypeExtension h ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)
      = (h.columnFamily χ₂).sign • certainTypeOmegaSigma h χ₂ i := by
  classical
  rw [certainTypeExtension, LinearMap.restrictScalars_apply]
  conv_lhs => rw [← S05.irreducibleCharacterBasis_apply (G := ↥L) ((h.columnFamily χ₂).mu i)]
  rw [(S05.irreducibleCharacterBasis (G := ↥L)).constr_basis ℂ _ ((h.columnFamily χ₂).mu i),
    certainTypeExtensionFun]
  have hex : ∃ p : ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) × Fin (Nat.card h.W1),
      (h.columnFamily p.1).mu p.2 = (h.columnFamily χ₂).mu i := ⟨(χ₂, i), rfl⟩
  rw [dif_pos hex]
  have hchoose : hex.choose = (χ₂, i) := h.columnFamily_mu_injective hex.choose_spec
  rw [hchoose]

/-- **Defining value of `ν` on the column sum**: `ν(μ_j) = δ_j ∑_{0≤i<w₁} ω_{ij}^σ`. -/
theorem certainTypeExtension_columnSum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    certainTypeExtension h (columnSum h χ₂)
      = (h.columnFamily χ₂).sign • ∑ i, certainTypeOmegaSigma h χ₂ i := by
  rw [columnSum_def, map_sum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => certainTypeExtension_mu h χ₂ i

/-- **The `σ`-image `ω_{ij}^σ` is a virtual character.**  `ω_{ij}^σ = σ_G(ω(P_{ij}))` and `σ_G` maps
`ZIrr(W) → ZIrr(G)` (`sigma_mem_ZIrr`); the source `ω(P_{ij})` is irreducible. -/
theorem certainTypeOmegaSigma_mem_ZIrr (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (i : Fin (Nat.card h.W1)) :
    certainTypeOmegaSigma h χ₂ i ∈ ZIrr G := by
  rw [certainTypeOmegaSigma]
  exact (ticVdiff h).sigma_mem_ZIrr rfl (ticVdiffFullDadeApplication h)
    ((ticVdiff h).omega (omegaProdCharTic h χ₂ i)).mem_ZIrr

/-- **`μ_j` vanishes off `A ∪ {1}`** (Peterfalvi (4.7)).  `μ_j = Ind_K^L χ_j` (`(4.5.a)`
`induce_restrict_certainType_eq`, `chiRestrict = Res_K μ_{0j}`); the induced character vanishes
outside `A ∪ {1}` for a nontrivial column `χ₂ ≠ 1`
(`induce_chiRestrict_apply_eq_zero_of_not_mem_union`). -/
theorem columnSum_apply_eq_zero_of_not_mem (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    {z : ↥L} (hz : (L.subtype z) ∉ A ∪ ({1} : Set G)) :
    (columnSum h χ₂ : ClassFunction ↥L ℂ) z = 0 := by
  have hbridge : columnSum h χ₂
      = ClassFunction.induce h.K (h.chiRestrict χ₂ : ClassFunction ↥h.K ℂ) := by
    rw [columnSum_def, ← h.induce_restrict_certainType_eq χ₂, h.coe_chiRestrict χ₂]
  rw [hbridge]
  exact induce_chiRestrict_apply_eq_zero_of_not_mem_union h.toCore hχ₂ hz

/-- Evaluation of the column sum at `1`: `μ_j(1) = ∑_i μ_{ij}(1)` (the column degree). -/
theorem columnSum_apply_one (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    (columnSum h χ₂ : ClassFunction ↥L ℂ) 1
      = ∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1 := by
  rw [columnSum_def]
  exact map_sum (AddMonoidHom.mk' (fun φ : ClassFunction ↥L ℂ => φ (1 : ↥L)) (fun _ _ => rfl))
    (fun i => ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ)) Finset.univ

/-- **Column sign equality from equal degree** (Peterfalvi (4.8) step (1), column form).  If two
certain-type columns have the same degree `∑_i μ_{ij}(1) = ∑_i μ_{ik}(1)`, their signs coincide
(reduce to the per-row `(4.8)` sign equality at any row via the degree bridge). -/
theorem certainType_columnSign_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ}
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    (h.columnFamily χ₂).sign = (h.columnFamily χ₂').sign := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  exact certainType_sign_eq_of_degree_eq h.toCore χ₂ χ₂' 0
    (forall_columnFamily_mu_apply_one_eq_of_sum_eq h χ₂ χ₂' hdeg 0)

/-- **`Supp(μ_j − μ_k) ⊆ supportInSubgroup A L`** for same-degree certain-type columns.  Both
`μ_j, μ_k` vanish off `A ∪ {1}` ((4.7) `columnSum_support_subset`); the difference additionally
vanishes at `1` (equal degree), so its support sits inside the certain subgroup `A`. -/
theorem columnDiff_support_subset (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    (columnSum h χ₂ - columnSum h χ₂').support ⊆ S04.supportInSubgroup A L := by
  intro z hz
  rw [ClassFunction.mem_support, ClassFunction.sub_apply] at hz
  by_contra hzA
  rw [S04.mem_supportInSubgroup] at hzA
  by_cases hz1 : z = 1
  · subst hz1
    exact hz (by rw [columnSum_apply_one, columnSum_apply_one, hdeg, sub_self])
  · have hnm : L.subtype z ∉ A ∪ ({1} : Set G) := by
      rintro (hA | h1)
      · exact hzA hA
      · exact hz1 (Subtype.ext (Set.mem_singleton_iff.mp h1))
    rw [columnSum_apply_eq_zero_of_not_mem h hχ₂ hnm,
      columnSum_apply_eq_zero_of_not_mem h hχ₂' hnm, sub_zero] at hz
    exact hz rfl

/-- **Generator-level `τ`-agreement** (Peterfalvi (4.8)/(4.9)): on a certain-type difference
`μ_j − μ_k` (same degree), the coherent extension `ν` agrees with the Dade map
`τ = dadeIntegralCharacterMap`.  Both sides equal `δ_j ∑_i (ω_{ij}^σ − ω_{ik}^σ)`:

* RHS: `μ_j − μ_k` is supported on `A ⊆ A₀` (`columnDiff_support_subset`), so
  `τ(μ_j − μ_k) = h.dade0.dadeMap ⟨·⟩` (`dadeIntegralCharacterMap_apply_of_support`)
  `= h.tau.toDadeMap ⟨·⟩` (`IsDadeMap.unique`) `= δ_j ∑(ω^σ − ω^σ)`
  (`certainType_diff_dade_sum_eq`, after identifying `⟨μ_j − μ_k, _⟩ = ∑ certainTypeDiffSupported`);
* LHS: `ν(μ_j − μ_k) = δ_j ∑ω_{ij}^σ − δ_k ∑ω_{ik}^σ`, and `δ_j = δ_k`
(`certainType_columnSign_eq`). -/
theorem certainTypeExtension_columnDiff_eq_dade (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    certainTypeExtension h (columnSum h χ₂ - columnSum h χ₂')
      = S07.dadeIntegralCharacterMap h.dade0 h.tau (columnSum h χ₂ - columnSum h χ₂') := by
  by_cases hχeq : χ₂ = χ₂'
  · subst hχeq; rw [sub_self, map_zero, map_zero]
  -- both sides equal `δ_j • ∑_i (ω_{ij}^σ − ω_{ik}^σ)`
  have hdi := forall_columnFamily_mu_apply_one_eq_of_sum_eq h χ₂ χ₂' hdeg
  have hsupp : (columnSum h χ₂ - columnSum h χ₂').support ⊆
      S04.supportInSubgroup
        (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L :=
    (columnDiff_support_subset h hχ₂ hχ₂' hdeg).trans
      (S04.supportInSubgroup_mono Set.subset_union_left)
  have hval : ((∑ i, certainTypeDiffSupported h.toCore hχ₂ hχ₂' i (hdi i) :
        OddOrder.Peterfalvi.S04.SupportedClassFunctions ℂ
          (A ∪ OddOrder.GroupTheory.conjClassSetIn L h.tic.V) L) :
        ClassFunction ↥L ℂ)
      = columnSum h χ₂ - columnSum h χ₂' := by
    rw [AddSubmonoidClass.coe_finsetSum, columnSum_def, columnSum_def, ← Finset.sum_sub_distrib]
    rfl
  have hLHS : certainTypeExtension h (columnSum h χ₂ - columnSum h χ₂')
      = (h.columnFamily χ₂).sign •
          ∑ i, (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) := by
    rw [map_sub, certainTypeExtension_columnSum, certainTypeExtension_columnSum,
      ← certainType_columnSign_eq h hdeg, ← smul_sub, ← Finset.sum_sub_distrib]
  rw [hLHS,
    S07.dadeIntegralCharacterMap_apply_of_support h.dade0 h.tau hsupp,
    S04.IsDadeMap.unique (k := ℂ) h.dade0.isDadeMap_dadeMap h.tau.toDadeIsometryData.isDadeMap,
    ← certainType_diff_dade_sum_eq h hχeq hχ₂ hχ₂' hdi]
  congr 1
  exact Subtype.ext hval

/-- **Degree of the conjugate column** `μ_{k⁻¹}(1) = μ_k(1)`.  The conjugate column character is the
complex conjugate `μ_{k⁻¹} = mapRingEquiv conj μ_k` (`certainType_columnSum_conj`), and the degree
`μ_k(1) = ∑_i μ_{ik}(1)` is a sum of positive integers, hence fixed by complex conjugation. -/
theorem columnSum_inv_apply_one (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Finite ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (k : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    (∑ i, ((h.columnFamily k⁻¹).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily k).mu i : ClassFunction ↥L ℂ) 1) := by
  have : Fintype ↥(h.W1 ⊔ h.W2) := Fintype.ofFinite _
  rw [← columnSum_apply_one, ← columnSum_apply_one]
  have h1 : columnSum h k⁻¹
      = ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (columnSum h k) := by
    rw [columnSum_def, columnSum_def, ← certainType_columnSum_conj]
  rw [h1, ClassFunction.mapRingEquiv_apply, columnSum_apply_one, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  obtain ⟨d, _, hd⟩ := irreducibleCharacter_apply_one_eq_pos_natCast ((h.columnFamily k).mu i)
  rw [hd, map_natCast]

/-- **R(μ_j) member family** (Peterfalvi (5.3.b)).  Indexed by `Bool × Fin w₁`:
`(false, i) ↦ δ_j ω_{ij}^σ`, `(true, i) ↦ −δ_j ω_{ik}^σ` (sign `δ_j = (columnFamily χ₂).sign`,
columns `j = χ₂`, `k = χ₂'`).  Its image is the orthonormal set `R(μ_j)` of Hypothesis (5.2.d)
(orthonormality: `certainTypeRImage_inner`; the `(μ_j − μ̄_j)^τ = ∑ R(μ_j)` image equation is
`certainType_diff_dade_sum_eq`). -/
noncomputable def certainTypeRImage (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    Bool × Fin (Nat.card h.W1) → ClassFunction G ℂ
  | (false, i) => ((h.columnFamily χ₂).sign : ℂ) • certainTypeOmegaSigma h χ₂ i
  | (true, i) => (-((h.columnFamily χ₂).sign : ℂ)) • certainTypeOmegaSigma h χ₂' i

/-- **Orthonormality of `R(μ_j)`** (Peterfalvi (5.2.d) for the reducible `μ_j`).  The signed
`σ`-image family `certainTypeRImage` is orthonormal: `⟨R(μ_j) p, R(μ_j) q⟩ = δ_{p,q}`.  The sign
`δ_j = ±1` (`sign_eq`) gives `δ_j · \overline{δ_j} = 1`, and `certainTypeOmegaSigma_inner` supplies
the grid orthonormality `⟨ω_{χ₂,i}^σ, ω_{χ₂',i'}^σ⟩ = [χ₂ = χ₂' ∧ i = i']`; the two halves
(`χ₂ ≠ χ₂'`) are cross-orthogonal. -/
theorem certainTypeRImage_inner (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂')
    (p q : Bool × Fin (Nat.card h.W1)) :
    ClassFunction.inner (certainTypeRImage h χ₂ χ₂' p) (certainTypeRImage h χ₂ χ₂' q)
      = if p = q then (1 : ℂ) else 0 := by
  have hδstar : star ((h.columnFamily χ₂).sign : ℂ) = ((h.columnFamily χ₂).sign : ℂ) := by
    rcases (h.columnFamily χ₂).sign_eq with h1 | h1 <;> rw [h1] <;> norm_num
  have hδsq : ((h.columnFamily χ₂).sign : ℂ) * ((h.columnFamily χ₂).sign : ℂ) = 1 := by
    rcases (h.columnFamily χ₂).sign_eq with h1 | h1 <;> rw [h1] <;> norm_num
  obtain ⟨bp, ip⟩ := p
  obtain ⟨bq, iq⟩ := q
  cases bp <;> cases bq <;>
    simp only [certainTypeRImage, ClassFunction.inner_smul_left,
      RepresentationTheory.inner_smul_right, certainTypeOmegaSigma_inner, hδstar, star_neg,
      mul_neg, neg_mul, neg_neg, Prod.mk.injEq, reduceCtorEq, false_and, true_and, ↓reduceIte]
  · -- (false,false): δ·(δ·[ip=iq]) = [ip=iq]
    rw [← mul_assoc, hδsq, one_mul]
  · -- (false,true): χ₂ ≠ χ₂' ⟹ 0
    rw [if_neg (fun hcon => hne hcon.1)]; ring
  · -- (true,false): χ₂' ≠ χ₂ ⟹ 0
    rw [if_neg (fun hcon => hne hcon.1.symm)]; ring
  · -- (true,true): δ·(δ·[ip=iq]) = [ip=iq]
    rw [← mul_assoc, hδsq, one_mul]

/-- `R(μ_j)` is injective on `Bool × Fin w₁` (distinct orthonormal vectors are distinct): a
corollary of `certainTypeRImage_inner`, since `R p = R q` would force `⟨R p, R q⟩ = 1 ≠ 0`. -/
theorem certainTypeRImage_injective (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hne : χ₂ ≠ χ₂') :
    Function.Injective (certainTypeRImage h χ₂ χ₂') := by
  intro p q hpq
  by_contra hpqne
  have h0 := certainTypeRImage_inner h hne p q
  rw [if_neg hpqne, hpq, certainTypeRImage_inner h hne, if_pos rfl] at h0
  exact one_ne_zero h0

/-- The sum of the `R(μ_j)` family over `Bool × Fin w₁` is `δ_j ∑_i (ω_{ij}^σ − ω_{ik}^σ)`, the
right-hand side of the (4.9) summed isometry `certainType_diff_dade_sum_eq`.  This is the image-side
of the `(μ_j − μ̄_j)^τ = ∑_{α ∈ R(μ_j)} α` equation (the left half being the column difference). -/
theorem certainTypeRImage_sum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    ∑ p : Bool × Fin (Nat.card h.W1), certainTypeRImage h χ₂ χ₂' p
      = ((h.columnFamily χ₂).sign : ℂ) •
          ∑ i, (certainTypeOmegaSigma h χ₂ i - certainTypeOmegaSigma h χ₂' i) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Finset.smul_sum]
  simp only [certainTypeRImage, neg_smul, smul_sub]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => by abel)

/-- **The (5.2.d) image equation for `R(μ_j)`** (Peterfalvi (5.3.b) / (4.9)(b)): the Dade image of
the column difference `μ_j − μ_k` is the sum of the `R(μ_j)` family,
`(μ_j − μ_k)^τ = ∑_{p} R(μ_j) p`.  Combines the (4.9) summed isometry — packaged as
`certainTypeExtension_columnDiff_eq_dade` (which discharges the `dadeIntegralCharacterMap` /
`toDadeMap` seam) and `certainTypeExtension_columnSum` — with `certainTypeRImage_sum`; the sign
equality `certainType_columnSign_eq` (degrees match) identifies `δ_j = δ_k`. -/
theorem dadeICM_columnDiff_eq_sum (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)) :
    S07.dadeIntegralCharacterMap h.dade0 h.tau (columnSum h χ₂ - columnSum h χ₂')
      = ∑ p : Bool × Fin (Nat.card h.W1), certainTypeRImage h χ₂ χ₂' p := by
  rw [← certainTypeExtension_columnDiff_eq_dade h hχ₂ hχ₂' hdeg, certainTypeRImage_sum,
    map_sub, certainTypeExtension_columnSum, certainTypeExtension_columnSum,
    ← certainType_columnSign_eq h hdeg, ← smul_sub, ← Finset.sum_sub_distrib]
  exact (Int.cast_smul_eq_zsmul ℂ _ _).symm

/-- **The conjugate of a column character is the inverse column** (`ClassFunction.conj` form of
`certainType_columnSum_conj`): `(μ_j)‾ = μ_{j⁻¹}`.  Bridges `ClassFunction.conj` (pointwise `star`)
to the `mapRingEquiv Complex.conjAe` form proved in (4.9)(a). -/
theorem columnSum_conj_eq (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) :
    (columnSum h χ₂).conj = columnSum h χ₂⁻¹ := by
  rw [columnSum_def, columnSum_def, ← certainType_columnSum_conj h.toHypothesis χ₂]
  ext g
  rw [ClassFunction.conj_apply, ClassFunction.mapRingEquiv_apply]
  rfl

open scoped Classical in
/-- **The reducible `R(μ_j)` image family** (Peterfalvi (5.2.d) via (5.3.b) / (4.9)).  For a
nontrivial column `χ₂ ≠ 1`, the certain-type column character `μ_j = columnSum χ₂` carries the
orthonormal difference-image family `R(μ_j)` of Hypothesis (5.2.d): the signed `σ`-images
`certainTypeRImage h χ₂ χ₂⁻¹` (with `μ̄_j = μ_{χ₂⁻¹}`), orthonormal (`certainTypeRImage_inner`,
`certainTypeRImage_injective`) and satisfying `(μ_j − μ̄_j)^τ = ∑ R(μ_j)`
(`dadeICM_columnDiff_eq_sum` through `columnSum_conj_eq`).  This is the reducible counterpart of
`dadeOrthonormalCharacterImageFamilyOfDiff` (irreducible `χ`), feeding the (6.8.2.3) per-constituent
`R(χᵢ)` decomposition. -/
noncomputable def certainTypeR (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1)) :
    S07.OrthonormalCharacterImageFamily (S07.dadeIntegralCharacterMap h.dade0 h.tau)
      (columnSum h χ₂) where
  imageSet := Finset.univ.image (certainTypeRImage h χ₂ χ₂⁻¹)
  mem_ZIrr := by
    intro α hα
    rw [Finset.mem_image] at hα
    obtain ⟨⟨b, i⟩, _, rfl⟩ := hα
    cases b
    · simp only [certainTypeRImage]
      rw [Int.cast_smul_eq_zsmul]
      exact (ZIrr G).smul_mem _ (certainTypeOmegaSigma_mem_ZIrr h χ₂ i)
    · simp only [certainTypeRImage]
      rw [neg_smul, Int.cast_smul_eq_zsmul]
      exact neg_mem ((ZIrr G).smul_mem _ (certainTypeOmegaSigma_mem_ZIrr h χ₂⁻¹ i))
  orthonormal := by
    intro α hα β hβ
    rw [Finset.mem_image] at hα hβ
    obtain ⟨p, _, rfl⟩ := hα
    obtain ⟨q, _, rfl⟩ := hβ
    rw [certainTypeRImage_inner h (column_inv_ne_self h hχ₂).symm]
    by_cases hpq : p = q
    · subst hpq; simp
    · rw [if_neg hpq, if_neg (fun he =>
        hpq (certainTypeRImage_injective h (column_inv_ne_self h hχ₂).symm he))]
  image_eq := by
    rw [columnSum_conj_eq, Finset.sum_image
      (fun p _ q _ hpq => certainTypeRImage_injective h (column_inv_ne_self h hχ₂).symm hpq)]
    exact dadeICM_columnDiff_eq_sum h hχ₂
      ((@inv_ne_one ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _ χ₂).mpr hχ₂) hdeg

open scoped Classical in
/-- **(5.2.e) cross-orthogonality of two distinct certain-type column families `R(μ_j) ⊥ R(μ_k)`.**
For two columns `χ₂`, `χ₂'` whose pairs `{χ₂, χ₂⁻¹}`, `{χ₂', χ₂'⁻¹}` are disjoint (`χ₂ ≠ χ₂'` and
`χ₂ ≠ χ₂'⁻¹`), every `σ`-image of `R(μ_j) = certainTypeR χ₂` is orthogonal to every `σ`-image of
`R(μ_k) = certainTypeR χ₂'`.  Each `R`-member is `±δ·ω_{·}^σ` built from a column in
`{χ₂, χ₂⁻¹}` (resp. `{χ₂', χ₂'⁻¹}`); since the two column pairs are disjoint, the grid
orthonormality `certainTypeOmegaSigma_inner` (`⟨ω_{c,i}^σ, ω_{c',i'}^σ⟩ = [c = c' ∧ i = i']`)
makes every cross inner product vanish.  This is the reducible-column counterpart of
`certainTypeRImage_inner` (same family) and the `R(μ_j) ⊥ R(χ)` lemma
`certainTypeR_imageSet_orthogonal_dadeOfDiff` (column vs irreducible break). -/
theorem certainTypeR_imageSet_orthogonal_certainTypeR (h : Hypothesis46 A L)
    [NeZero (Nat.card h.W1)] [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ χ₂' : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1) (hχ₂' : χ₂' ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (hdeg' : (∑ i, ((h.columnFamily χ₂').mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂'⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    (hne1 : χ₂ ≠ χ₂') (hne2 : χ₂ ≠ χ₂'⁻¹) :
    ∀ α ∈ (certainTypeR h hχ₂ hdeg).imageSet,
    ∀ β ∈ (certainTypeR h hχ₂' hdeg').imageSet,
      ClassFunction.inner α β = 0 := by
  have hδstar : ∀ c : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ,
      star ((h.columnFamily c).sign : ℂ) = ((h.columnFamily c).sign : ℂ) := fun c => by
    rcases (h.columnFamily c).sign_eq with h1 | h1 <;> rw [h1] <;> norm_num
  intro α hα β hβ
  simp only [certainTypeR, Finset.mem_image, Finset.mem_univ, true_and] at hα hβ
  obtain ⟨⟨bp, ip⟩, rfl⟩ := hα
  obtain ⟨⟨bq, iq⟩, rfl⟩ := hβ
  cases bp <;> cases bq <;>
    simp only [certainTypeRImage, ClassFunction.inner_smul_left,
      RepresentationTheory.inner_smul_right, certainTypeOmegaSigma_inner, hδstar, star_neg,
      mul_neg, neg_mul, neg_neg]
  · rw [if_neg (fun hcon => hne1 hcon.1)]; ring
  · rw [if_neg (fun hcon => hne2 hcon.1)]; ring
  · rw [if_neg (fun hcon => hne2 (by
      rw [← hcon.1,
        (@inv_inv ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _ χ₂)]))]
    ring
  · rw [if_neg (fun hcon => hne1 (inv_injective hcon.1))]; ring

/-- **Per-column ν-aux decomposition for a reducible certain-type member `μ_j` (ψ = 0).**

The reducible analogue of `memberExtensionDecomposition` (irreducible `χ`): for a coherent set `S₁`
containing the certain-type column `μ_j = columnSum χ₂` and its conjugate `μ̄_j = columnSum χ₂⁻¹`,
builds the (5.5) `ψ = 0` decomposition `D' : CharacterPsiDecomposition τ μ_j 0` whose auxiliary
isometry `τ₁` is the **running coherence extension `ν = hS₁.extension`** (not the Dade base map `τ`,
unlike `certainTypeDecompositionDa`).  It uses the reducible image family `R(μ_j) = certainTypeR`
(Peterfalvi (5.3.b)) in place of the irreducible Dade family
`dadeOrthonormalCharacterImageFamilyOfDiff`.

This is the `Dmem`-style member decomposition for a reducible column member of the weighted (5.6)
adjoin engine `xAdjoinStepW` (its `htau1Dmem` field `(Dmem i).tau1 = ν` then holds by `rfl`); the
remaining `xAdjoinStepW`-side input is the (5.2.e) cross-family orthogonality against the break
family.

The coherence `hS₁` and decomposition are stated over a **general** integral map `τ'` (the engine's
Dade map, e.g. the Sibley–Dade `hyp.tau`), agreeing with the certain-type Dade map
`dadeIntegralCharacterMap h.dade0 h.tau` on the conjugate column difference (`hagree`, supplied for
case (B) by `caseB_column_mapagree`); the reducible image family `R(μ_j) = certainTypeR` is
transported to `τ'` by replacing only its `image_eq` field (the orthonormal `imageSet ⊆ ZIrr G` is
map-independent). -/
noncomputable def certainTypeMemberDecomposition (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Invertible (Nat.card ↥h.K : ℂ)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    {χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ} (hχ₂ : χ₂ ≠ 1)
    (hdeg : (∑ i, ((h.columnFamily χ₂).mu i : ClassFunction ↥L ℂ) 1)
      = (∑ i, ((h.columnFamily χ₂⁻¹).mu i : ClassFunction ↥L ℂ) 1))
    {τ' : S07.IntegralCharacterMap (↥L) G}
    (hagree : τ' (columnSum h χ₂ - (columnSum h χ₂).conj)
      = S07.dadeIntegralCharacterMap h.dade0 h.tau (columnSum h χ₂ - (columnSum h χ₂).conj))
    {S₁ : Set (ClassFunction ↥L ℂ)} {A' : Set ↥L}
    (hS₁ : S07.IsCoherent τ' S₁ A')
    (hμ_S1 : columnSum h χ₂ ∈ S₁) (hμbar_S1 : (columnSum h χ₂).conj ∈ S₁)
    (hνZ : hS₁.extension (columnSum h χ₂) ∈ ZIrr G)
    (hdiffsupported : columnSum h χ₂ - (columnSum h χ₂).conj ∈
      S07.zSupportedSpan (L := ↥L) S₁ A') :
    S07.CharacterPsiDecomposition τ' (columnSum h χ₂) 0 := by
  have hχmem : columnSum h χ₂ ∈ Submodule.span ℤ S₁ := Submodule.subset_span hμ_S1
  have hχbarmem : (columnSum h χ₂).conj ∈ Submodule.span ℤ S₁ := Submodule.subset_span hμbar_S1
  -- The (5.4) sponsoring set `{μ_j − μ̄_j, μ_j − 0}` lies in `ℤ[S₁]`.
  have hle : Submodule.span ℤ ({columnSum h χ₂ - (columnSum h χ₂).conj, columnSum h χ₂ - 0} :
      Set (ClassFunction ↥L ℂ)) ≤ Submodule.span ℤ S₁ := by
    rw [Submodule.span_le]
    intro s hs
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl
    · exact Submodule.sub_mem _ hχmem hχbarmem
    · rw [sub_zero]; exact hχmem
  have hχχbar : ClassFunction.inner (columnSum h χ₂) (columnSum h χ₂).conj = 0 := by
    rw [columnSum_conj_eq, columnSum_def, columnSum_def, columnFamily_mu_sum_inner,
      if_neg (column_inv_ne_self h hχ₂).symm]
  -- The reducible image family `R(μ_j) = certainTypeR`, transported from the certain-type Dade map
  -- to `τ'` by replacing only `image_eq` (`hagree`); the orthonormal `imageSet ⊆ ZIrr G` is shared.
  exact S07.CharacterPsiDecomposition.ofProjection
    ({ imageSet := (certainTypeR h hχ₂ hdeg).imageSet
       mem_ZIrr := (certainTypeR h hχ₂ hdeg).mem_ZIrr
       orthonormal := (certainTypeR h hχ₂ hdeg).orthonormal
       image_eq := by rw [hagree]; exact (certainTypeR h hχ₂ hdeg).image_eq } :
      S07.OrthonormalCharacterImageFamily τ' (columnSum h χ₂))
    hS₁.extension
    (fun φ ζ hφ hζ => hS₁.extension_inner_eq φ ζ (hle hφ) (hle hζ))
    (hS₁.extends_on_supported _ hdiffsupported)
    (by rw [sub_zero]; exact hνZ)
    (by simp)
    (by simp)
    hχχbar

open scoped Classical in
/-- **Complex conjugation acts on the `R(μ_j)`-family as minus the half-swap involution**
(the (11.9.c) `t ≠ 0` input, issue 1024): for the signed `σ`-image family
`certainTypeRImage h χ₂ χ₂⁻¹`, conjugation sends the member at `(b, i)` to the *negative* of the
member at `(¬b, rowInv i)` — the `(4.9)(a)` grid conjugation `certainTypeOmegaSigma_conj_eq`
swaps the two column halves (`χ₂ ↔ χ₂⁻¹`) and inverts the row, while the fixed sign
`δ = (columnFamily χ₂).sign` flips against the `(true, ·)`-half's built-in `−δ`. -/
theorem certainTypeRImage_conj (h : Hypothesis46 A L) [NeZero (Nat.card h.W1)]
    [Fintype ↥(h.W1 ⊔ h.W2)] [Invertible (Nat.card ↥(h.W1 ⊔ h.W2) : ℂ)]
    [Fintype (ticVdiff h).W] [Invertible (Nat.card (ticVdiff h).W : ℂ)]
    (χ₂ : (h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) (p : Bool × Fin (Nat.card h.W1)) :
    ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv (certainTypeRImage h χ₂ χ₂⁻¹ p)
      = -(certainTypeRImage h χ₂ χ₂⁻¹ (!p.1, rowInv h.toHypothesis p.2)) := by
  obtain ⟨b, i⟩ := p
  cases b
  · -- `(false, i) ↦ δ•ω_{χ₂,i}`; conjugate = `δ•ω_{χ₂⁻¹, rowInv i} = −((true, rowInv i))`
    change ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        (((h.columnFamily χ₂).sign : ℂ) • certainTypeOmegaSigma h χ₂ i)
      = -((-((h.columnFamily χ₂).sign : ℂ)) • certainTypeOmegaSigma h χ₂⁻¹
          (rowInv h.toHypothesis i))
    rw [Int.cast_smul_eq_zsmul, ClassFunction.mapRingEquiv_zsmul,
      certainTypeOmegaSigma_conj_eq, neg_smul, neg_neg, Int.cast_smul_eq_zsmul]
  · -- `(true, i) ↦ −δ•ω_{χ₂⁻¹,i}`; conjugate = `−δ•ω_{χ₂, rowInv i} = −((false, rowInv i))`
    change ClassFunction.mapRingEquiv Complex.conjAe.toRingEquiv
        ((-((h.columnFamily χ₂).sign : ℂ)) • certainTypeOmegaSigma h χ₂⁻¹ i)
      = -(((h.columnFamily χ₂).sign : ℂ) • certainTypeOmegaSigma h χ₂ (rowInv h.toHypothesis i))
    rw [show (-((h.columnFamily χ₂).sign : ℂ)) = ((-(h.columnFamily χ₂).sign : ℤ) : ℂ) from by
        push_cast; ring,
      Int.cast_smul_eq_zsmul, ClassFunction.mapRingEquiv_zsmul, certainTypeOmegaSigma_conj_eq,
      (@inv_inv ((h.W2.subgroupOf (h.W1 ⊔ h.W2)) →* ℂˣ) _ χ₂)]
    rw [show ((-(h.columnFamily χ₂).sign : ℤ)) • certainTypeOmegaSigma h χ₂
          (rowInv h.toHypothesis i)
        = -(((h.columnFamily χ₂).sign : ℂ) • certainTypeOmegaSigma h χ₂
            (rowInv h.toHypothesis i)) from by
      rw [← Int.cast_smul_eq_zsmul ℂ]; push_cast; rw [neg_smul]]

end OddOrder.Peterfalvi.S06


