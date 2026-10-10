-- Prove2me | Definitions.Def_OAIErdos3B153
-- name    : OAIErdos3B153
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T00:36:24.432112+00:00
-- url     : https://prove2.me/theorems/4cc9fbe9-ca8d-460c-86f7-c0ce1ad7b677
-- title:
--   OpenAI Erdős-3 split, definitions bundle 154 of 177
-- statement:
--   Definitions bundle 154 of 177 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B152`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 154 available.
--
--   Modules: `OAI.Erdos3.RationalFilteredNilmanifold.AllocatedMarkedCoveredLowerDiagram`, `OAI.Erdos3.RationalFilteredNilmanifold.exists_allocated_marked_covered_lower_diagram`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B155

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
namespace OAI

namespace Erdos3

open Module

variable {L M ι κ α β : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] [Fintype ι] [Fintype κ] [Fintype β]

end Erdos3

namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

end Erdos3.RationalFilteredNilmanifold

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d f : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (Fmark : RationalFilteredNilmanifold M (s + 1) f)
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

structure AllocatedMarkedCoveredLowerDiagram (k q : ℕ) (p cost : ℝ) where
  Dref : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W)
    (s + 1) (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W))
  Dref_filtration : Dref.filtration = D.filtration.gradedRefiltration W
  Dref_lattice : Dref.lattice = D.lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
      (D.filtration.gradedRefiltrationSubalgebra W).incl)
  Dref_geometry : Dref.GeometryComplexityLE cost
  inclusion_height : ∀ i j, rationalLogHeight (D.basis.repr (Dref.basis j : L) i) ≤ cost
  Fbase : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1)
    (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  Fbase_filtration : Fbase.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
  Fbase_lattice : Fbase.lattice = Fmark.lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := (Fmark.filtration.gradedRefiltration
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).lowerCentralSeries_eq_bot)
      (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))).incl)
  nQ : ℕ
  nQ_le : nQ ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)
  Qbase : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ
  Qbase_filtration : Qbase.filtration = Dref.filtration.quotientTop
  Qbase_lattice : Qbase.lattice = Dref.lattice.map
    (Dref.filtration.quotientStepHom (Dref.filtration.layerIdeal (s + 1)) le_rfl)
  Fref : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1)
    (finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  Fref_filtration : Fref.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))
  Fref_basis : Fref.basis = Fbase.basis
  Fref_lattice : Fref.lattice ≤ Fbase.lattice
  Fref_geometry : Fref.GeometryComplexityLE cost
  marked_inclusion_height : ∀ i j,
    rationalLogHeight (Fmark.basis.repr (Fref.basis j : M) i) ≤ cost
  restricted_mark_height : ∀ i j, rationalLogHeight (Fref.basis.repr
    (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis i)) j) ≤ cost
  Q : RationalFilteredNilmanifold
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ
  Q_filtration : Q.filtration = Dref.filtration.quotientTop
  Q_basis : Q.basis = Qbase.basis
  Q_lattice : Q.lattice ≤ Qbase.lattice
  Q_geometry : Q.GeometryComplexityLE cost
  quotient_height : ∀ i j, rationalLogHeight (Q.basis.repr
    (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ cost
  refiltered_mark_strong : ∀ j, ∀ y ∈ Fref.filtration.layer j,
    ∃ x ∈ Dref.filtration.layer j,
      D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x = y
  nQF : ℕ
  nQF_le : nQF ≤ finrank ℚ (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
  Fquot : RationalFilteredNilmanifold
    ((Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) ⧸
      Fref.filtration.layerIdeal (s + 1)) s nQF
  Fquot_filtration : Fquot.filtration = Fref.filtration.quotientTop
  Fquot_lattice : Fquot.lattice = Fref.lattice.map
    (Fref.filtration.quotientStepHom (Fref.filtration.layerIdeal (s + 1)) le_rfl)
  Fquot_geometry : Fquot.GeometryComplexityLE cost
  marked_quotient_height : ∀ i j, rationalLogHeight (Fquot.basis.repr
    (lieQuotientMap (Fref.filtration.layerIdeal (s + 1)) (Fref.basis j)) i) ≤ cost
  lower_mark_height : ∀ i j, rationalLogHeight (Fquot.basis.repr
    (Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      (Q.basis i)) j) ≤ cost
  lower_mark_filtered : ∀ j, ∀ x ∈ Q.filtration.layer j,
    Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      x ∈ Fquot.filtration.layer j
  lower_mark_strong : ∀ j, ∀ y ∈ Fquot.filtration.layer j,
    ∃ x ∈ Q.filtration.layer j, Dref.topQuotientMarkedMap Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      (D.refilteredMarkedMap_mem_layer Fmark φ hφ W Dref Dref_filtration Fref Fref_filtration)
      x = y
  pCover : ℝ
  pCover_nonneg : 0 ≤ pCover
  pCover_le : pCover ≤ cost
  recovery :
    letI := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 Fref.basis
    letI := moduleTopology ℝ (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)))
    letI : IsTopologicalAddGroup (ℝ ⊗[ℚ]
      ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1))) :=
      IsModuleTopology.topologicalAddGroup ℝ _
    letI := realification_moduleTopology_t2 Q.basis
    letI := Q.metricSpace
    letI := Fref.metricSpace
    let diagram := Dref.markedTopQuotientDiagram Fref
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q
    let K : ℝ≥0 := ⟨Real.exp pCover, (Real.exp_pos _).le⟩
    ∀ a r : D.RealGroup,
      (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
      ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
        (letI := D.metricSpace; LipschitzWith ℓ S) →
        (∀ y, (S y).im = 0 ∧ 0 ≤ (S y).re ∧ (S y).re ≤ 1) →
        let frozen := fun x : Dref.RealGroup => S (QuotientGroup.mk
          (a * realificationMap (hnil := Dref.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl x * r))
        ∀ x : Dref.RealGroup,
          positiveImageSlice diagram K frozen (diagram x).2 (diagram x).1 = frozen x

end Erdos3.RationalFilteredNilmanifold

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_allocated_marked_covered_lower_diagram (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type u} {κ : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] [Fintype κ]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d f nb nf : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (b : Basis (Fin nb) ℚ L) (ω : Fin nb → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis (Fin nf) ℚ M) (ν : Fin nf → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : κ → D.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
      ∀ {p : ℝ}, 1 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
      (∀ i j, rationalLogHeight
        ((D.filtration.associatedGradedBasis b ω hD).repr (v i) j) ≤ p) →
      (∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        Nonempty (AllocatedMarkedCoveredLowerDiagram D Fmark φ hφ W k q p ((p + C) ^ C)) := by
  obtain ⟨A, _, hnative⟩ := exists_marked_refiltered_native_diagram
  obtain ⟨B, _, hcover⟩ := exists_allocated_marked_diagram_recovery_covers s k
  obtain ⟨T, _, hlower⟩ := exists_controlled_marked_top_quotient
  obtain ⟨C, hC, hbudget⟩ := exists_allocatedMarkedCoveredLowerDiagramBudget A B T
  refine ⟨C, hC, ?_⟩
  intro L M κ _ _ _ _ _ _ _ _ _ d f nb nf D Fmark b ω hD c ν hF φ hφ hsurj
    W v hspan hW p hp hDgeom hFgeom hκ hb hc hφheight hv hker q hq hqp
  have hp0 : 0 ≤ p := le_trans zero_le_one hp
  let p₀ := p + (p + A) ^ A
  let pCover := (p₀ + B) ^ B
  let p₁ := p₀ + pCover
  obtain ⟨hp₀, hpp₀, hnative₀, hp₀p₁, hcover₁, hp₁C, hlowerC⟩ := hbudget p hp
  have hnativeC : (p + A) ^ A ≤ (p + C) ^ C := hnative₀.trans (hp₀p₁.trans hp₁C)
  have hcoverC : pCover ≤ (p + C) ^ C := hcover₁.trans hp₁C
  have hp₀0 : 0 ≤ p₀ := le_trans zero_le_one hp₀
  have hp₁0 : 0 ≤ p₁ := hp₀0.trans hp₀p₁
  have hdata := hnative D Fmark b ω hD c ν hF φ hφ hsurj W v hspan hW
    hp0 hDgeom hFgeom hκ hb hc hφheight hv
  unfold MarkedRefilteredNativeDiagramData at hdata
  obtain ⟨E, hEfil, hElat, hEgeom, hEinc, F, hFfil, hFlat, hFgeo, hFinc,
    hmark, _, _, hsource, _⟩ := hdata
  obtain ⟨nQ, hnQ, Q, hQfil, hQlat, hQgeom, hQproj⟩ := hsource
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W)) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 F.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ]
    ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  have hcovers := hcover D Fmark φ hφ W E hEfil F Q hp₀
    (hEgeom.mono E hnative₀) (hDgeom.mono D hpp₀)
    (hQgeom.mono Q hnative₀) (hFgeo.mono F hnative₀)
    (fun i j => (hEinc i j).trans hnative₀)
    (fun i j => (hQproj i j).trans hnative₀)
    (fun i j => (hmark j i).trans hnative₀) hker q hq
    (hqp.trans (Real.exp_le_exp.mpr hpp₀))
  unfold AllocatedMarkedDiagramRecoveryCovers at hcovers
  obtain ⟨Q', hQ'fil, hQ'basis, hQ'lat, hQ'geom, F', hF'fil, hF'basis,
    hF'lat, hF'geom, hrec⟩ := hcovers
  have hQ'F : Q'.filtration = E.filtration.quotientTop := hQ'fil.trans hQfil
  have hF'F : F'.filtration = Fmark.filtration.gradedRefiltration
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)) := hF'fil.trans hFfil
  have hmarked := D.refilteredMarkedMap_mem_layer Fmark φ hφ W E hEfil F' hF'F
  have hstrong := D.refilteredMarkedMap_layer_surjective Fmark φ hφ W E hEfil F' hF'F
    b ω hD c ν hF hW hsurj
  have hproj₁ : ∀ i j, rationalLogHeight (Q'.basis.repr
      (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ p₁ := by
    intro i j
    rw [hQ'basis]
    exact (hQproj i j).trans (hnative₀.trans hp₀p₁)
  have hmark₁ : ∀ i j, rationalLogHeight (F'.basis.repr
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (E.basis i)) j) ≤ p₁ := by
    intro i j
    rw [hF'basis]
    exact (hmark i j).trans (hnative₀.trans hp₀p₁)
  obtain ⟨nQF, hnQF, QF, hQFfil, hQFlat, hQFgeom, hQFproj, hQFmark, hQFfiltered, hQFstrong⟩ :=
    hlower E F' (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      hmarked Q' hQ'F hstrong hp₁0 (hEgeom.mono E (hnative₀.trans hp₀p₁))
      (hF'geom.mono F' hcover₁) (hQ'geom.mono Q' hcover₁) hproj₁ hmark₁
  refine ⟨{
    Dref := E
    Dref_filtration := hEfil
    Dref_lattice := hElat
    Dref_geometry := hEgeom.mono E hnativeC
    inclusion_height := fun i j => (hEinc i j).trans hnativeC
    Fbase := F
    Fbase_filtration := hFfil
    Fbase_lattice := hFlat
    nQ := nQ
    nQ_le := hnQ
    Qbase := Q
    Qbase_filtration := hQfil
    Qbase_lattice := hQlat
    Fref := F'
    Fref_filtration := hF'F
    Fref_basis := hF'basis
    Fref_lattice := hF'lat
    Fref_geometry := hF'geom.mono F' hcoverC
    marked_inclusion_height := ?_
    restricted_mark_height := fun i j => (hmark₁ i j).trans hp₁C
    Q := Q'
    Q_filtration := hQ'F
    Q_basis := hQ'basis
    Q_lattice := hQ'lat
    Q_geometry := hQ'geom.mono Q' hcoverC
    quotient_height := fun i j => (hproj₁ i j).trans hp₁C
    refiltered_mark_strong := hstrong
    nQF := nQF
    nQF_le := hnQF
    Fquot := QF
    Fquot_filtration := hQFfil
    Fquot_lattice := hQFlat
    Fquot_geometry := hQFgeom.mono QF hlowerC
    marked_quotient_height := fun i j => (hQFproj i j).trans hlowerC
    lower_mark_height := fun i j => (hQFmark i j).trans hlowerC
    lower_mark_filtered := hQFfiltered
    lower_mark_strong := hQFstrong
    pCover := pCover
    pCover_nonneg := pow_nonneg (add_nonneg hp₀0 (Nat.cast_nonneg B)) B
    pCover_le := hcoverC
    recovery := ?_ }⟩
  · intro i j
    rw [hF'basis]
    exact (hFinc i j).trans hnativeC
  · dsimp only
    intro a r ha hr S ℓ hℓ hS hpositive
    apply hrec a r (fun i => (ha i).trans ?_) hr S ℓ
      (hℓ.trans (Real.exp_le_exp.mpr hpp₀)) hS hpositive
    exact Real.exp_le_exp.mpr (pow_le_pow_left₀ (by linarith) (by linarith) k)

end Erdos3.RationalFilteredNilmanifold

end

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

end Erdos3.RationalFilteredNilmanifold

end OAI

end


