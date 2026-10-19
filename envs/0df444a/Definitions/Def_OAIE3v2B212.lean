-- Prove2me | Definitions.Def_OAIE3v2B212
-- name    : OAIE3v2B212
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:16:07.007552+00:00
-- url     : https://prove2.me/theorems/9685dc35-5bab-4394-8e34-937640053d3a
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 216 of 311
-- statement:
--   Definitions bundle 216 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B299`, `OAIE3v2B180`, `OAIE3v2B181`, `OAIE3v2B186`, `OAIE3v2B190`, `OAIE3v2B191`, `OAIE3v2B192`, `OAIE3v2B193` of this split.
--
--   Modules: `Dynamics/AllocatedExternalCandidatePrimitivePhysicalBudget.lean`, `Estimates/AdaptedDiagramNativeExternalNet.lean`, `Estimates/MarkedRefilteredLowerNativeDiagram.lean`, `Estimates/NativeMarkedDiagramOrbitLift.lean`, `Estimates/NativeOptionFixedSourceQuotientMarkStrong.lean`, `Estimates/NativeProductVerticalization.lean`, `Estimates/PrescribedPartitionExpansionCore.lean`, `Estimates/UniformFiniteMarkedFactorParameters.lean`, `Estimates/UnitVerticalNativeInverseModels.lean`, `Lattices/AllocatedAffineScaleEnvelope.lean`, `Lattices/ForecastNativeResidueTest.lean`, `Lattices/NativePairAffineCellStepDrop.lean`, `Lattices/RefilteredResidueExpansionSpec.lean`, `Linear/AllocatedModularRankMixedUniform.lean`, `Linear/FixedAdaptedSymbolFactorizationBasis.lean`, `Nilpotent/CommonVariableDimensionNiltests.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B299
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B186
import Definitions.Def_OAIE3v2B190
import Definitions.Def_OAIE3v2B191
import Definitions.Def_OAIE3v2B192
import Definitions.Def_OAIE3v2B193

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedDiagramOrbitLift
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s d n : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    (G : NilpotentLieFiltration M (s + 1))
    (φ : L →ₗ⁅ℚ⁆ M)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ G.layer j)
    (Q : RationalFilteredNilmanifold
      (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
    (hQ : Q.filtration = D.filtration.quotientTop) {w : σ → ℕ}

theorem exists_prescribed_marked_topQuotientOrbit_lift
    (hsurj : ∀ j, ∀ y ∈ G.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : G.realification.PolynomialOrbit w)
    (hcompat : map
      (realLieHomToRat (realificationLieHom
        (lieQuotientProjection (D.filtration.layerIdeal (s + 1))
          (G.layerIdeal (s + 1)) φ (hφ (s + 1))))).toLinearMap q.log =
      map (realLieHomToRat (realificationLieHom
        (lieQuotientMap (G.layerIdeal (s + 1))))).toLinearMap marked.log) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := G.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          G.realification.polynomialOrbitRealEval w z marked := by
  let q' : D.filtration.quotientTop.realification.PolynomialOrbit w :=
    polynomialOrbitOfLog q.log (by rw [← hQ]; exact q.adapted)
  obtain ⟨g, hquot, hmark⟩ :=
    D.filtration.exists_real_quotient_fiber_polynomialOrbit_lift G φ hφ hsurj w
      q' marked hcompat
  have hq : D.topQuotientOrbit Q hQ g = q := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact hquot
  refine ⟨g, hq, hmark, ?_, ?_⟩
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
      (eval₂ z g.log) = eval₂ z q.log
    change map (realLieHomToRat (realificationLieHom
      (lieQuotientMap (D.filtration.layerIdeal (s + 1))))).toLinearMap g.log =
      q.log at hquot
    rw [← hquot]
    exact (eval₂_map
      (realificationLieHom (lieQuotientMap (D.filtration.layerIdeal (s + 1)))).toLinearMap
      z g.log).symm
  · intro z
    apply NilpotentLieBCHGroup.ext
    change realificationLieHom φ (eval₂ z g.log) = eval₂ z marked.log
    rw [← hmark]
    exact (eval₂_map (realificationLieHom φ).toLinearMap z g.log).symm

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)

variable (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

theorem exists_marked_topQuotientOrbit_lift_of_quotient_eq
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      (∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := Q.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)))
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          Q.filtration.realification.polynomialOrbitRealEval w z q) ∧
      ∀ z : σ → ℝ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.filtration.lowerCentralSeries_eq_bot)
        (hM := E.filtration.lowerCentralSeries_eq_bot) φ
        (D.filtration.realification.polynomialOrbitRealEval w z g) =
          E.filtration.realification.polynomialOrbitRealEval w z marked :=
  D.exists_prescribed_marked_topQuotientOrbit_lift E.filtration φ hφ Q hQ hsurj q marked
    ((D.topQuotientMarkedOrbit_eq_iff E φ hφ Q hQ QF hQF q marked).mp heq)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration VectorPolynomial

variable {L M ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d f nE nF : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (Fmark : RationalFilteredNilmanifold M (s + 1) f)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
  (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
  (E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nE)
  (hE : E.filtration = D.filtration.gradedRefiltration W)
  (EF : RationalFilteredNilmanifold
    (Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
  (hEF : EF.filtration = Fmark.filtration.gradedRefiltration
    (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))

include hE hEF

theorem refilteredMarkedMap_layer_surjective
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (c : Basis κ ℚ M) (ν : κ → ℕ)
    (hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
    (hW : BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule)
    (hsurj : ∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (j : ℕ) (y : Fmark.filtration.gradedRefiltrationSubalgebra
      (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)))
    (hy : y ∈ EF.filtration.layer j) :
    ∃ x ∈ E.filtration.layer j,
      D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W x = y := by
  rw [hEF] at hy
  obtain ⟨x, hx, heq⟩ := D.filtration.gradedRefiltrationMap_layer_surjective
    Fmark.filtration b ω hD c ν hF φ hφ W hW hsurj j y hy
  exact ⟨x, by rwa [hE], heq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct NNReal

variable {L M σ : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s d e n m : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  (E : RationalFilteredNilmanifold M (s + 1) e)
  (φ : L →ₗ⁅ℚ⁆ M)
  (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
  (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
  (hQ : Q.filtration = D.filtration.quotientTop)
  (QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m)
  (hQF : QF.filtration = E.filtration.quotientTop) {w : σ → ℕ}

theorem exists_marked_topQuotientOrbit_lift_diagram
    (hsurj : ∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y)
    (q : Q.filtration.realification.PolynomialOrbit w)
    (marked : E.filtration.realification.PolynomialOrbit w)
    (heq : D.topQuotientMarkedOrbit E φ hφ Q hQ QF hQF q = E.topQuotientOrbit QF hQF marked) :
    ∃ g : D.filtration.realification.PolynomialOrbit w,
      D.topQuotientOrbit Q hQ g = q ∧
      map (realLieHomToRat (realificationLieHom φ)).toLinearMap g.log = marked.log ∧
      ∀ z : σ → ℝ,
        D.markedTopQuotientDiagram E φ Q
          (D.filtration.realification.polynomialOrbitRealEval w z g) =
        ((QuotientGroup.mk (Q.filtration.realification.polynomialOrbitRealEval w z q) : Q.Space),
         (QuotientGroup.mk (E.filtration.realification.polynomialOrbitRealEval w z marked) : E.Space)) := by
  obtain ⟨g, hg, hm, hqeval, hmeval⟩ :=
    D.exists_marked_topQuotientOrbit_lift_of_quotient_eq E φ hφ Q hQ QF hQF hsurj q marked heq
  refine ⟨g, hg, hm, ?_⟩
  intro z
  simp only [markedTopQuotientDiagram, hqeval z, hmeval z]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOptionFixedSourceQuotientMarkStrong
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold
open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {s t d f : ℕ}

theorem exists_native_fixedSource_adapted_mark_geometry :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
        {s t d f : ℕ} (D : RationalFilteredNilmanifold L s d)
        (Fmark : RationalFilteredNilmanifold M t f)
        (source : D.AdaptedModelData) (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ},
        0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
        (∀ i j, rationalLogHeight (D.basis.repr (source.basis i) j) ≤ p + 1) →
        (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
        Nonempty (D.FixedSourceAdaptedMarkGeometryData Fmark source φ p ((p + 2) ^ C)) := by
  obtain ⟨C, hC, hbudget⟩ := exists_adaptedMapGeometryBudget_fixed_power
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s t d f D Fmark source φ p hp hD hF hsource hφ
  obtain ⟨target, htarget, htargetForward⟩ := Fmark.exists_adapted_model_data hp hF
  obtain ⟨htargetDim, htargetInverse, _⟩ :=
    Fmark.basis_geometry_of_forward_height target.basis hp hF htargetForward
  have hp1 : 0 ≤ p + 1 := by linarith
  have hmap := D.markedMap_basisChange_logHeight Fmark source.basis target.basis φ.toLinearMap
    hp1 (hD.mono D (by linarith)) (hF.mono Fmark (by linarith))
    hsource htargetForward (fun i j => (hφ i j).trans (by linarith))
  let r := adaptedMapGeometryBudget p
  have hr : 0 ≤ r := adaptedMapGeometryBudget_nonneg hp
  have hgeomr : (p + 3) ^ 11 ≤ r := adaptedMapGeometryBudget_geometry hp
  have hinverser : (p + 4) ^ 5 ≤ r :=
    (pow_le_pow_right₀ (by linarith : 1 ≤ p + 4) (by decide : (5 : ℕ) ≤ 11)).trans
      (adaptedMapGeometryBudget_inverse hp)
  have hmapr : adaptedMarkedMapHeightBudget (p + 1) ≤ r :=
    adaptedMapGeometryBudget_markedMap hp
  have hrq : r ≤ (p + 2) ^ C :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans (hbudget p hp)
  have htargetq := htarget.mono target.model (hgeomr.trans hrq)
  let H := ⌈Real.exp r⌉₊
  exact ⟨{
    target := target
    target_geometry := htargetq
    target_dimension := by simpa only [Fintype.card_fin] using htargetDim
    target_forward := htargetForward
    target_inverse := fun i j => (htargetInverse i j).trans (hinverser.trans hrq)
    target_structure := htargetq.2.2.1
    entries_height := H
    entries_height_pos := lt_of_lt_of_le Nat.zero_lt_one (one_le_ceil_exp r)
    entries_bound := (ceil_exp_le_exp_add_one hr).trans (Real.exp_le_exp.mpr (hbudget p hp))
    entries := fun i j => rationalHeightLE_ceil_exp ((hmap j i).trans hmapr)
    entries_logHeight := fun i j => (hmap j i).trans (hmapr.trans hrq)
  }⟩

end Erdos3.RationalFilteredNilmanifold

end

section

universe u v

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

noncomputable def nativeOptionFixedSourceMarkExponent : ℕ :=
  Classical.choose exists_native_fixedSource_adapted_mark_geometry.{u, v}

variable {Pivot : Type v} [Fintype Pivot]
    {L M : Type u} {Partner : Pivot → Type u}
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    [∀ a, LieRing (Partner a)] [∀ a, LieAlgebra ℚ (Partner a)]
    {s d f dQ : ℕ} {dp : Pivot → ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (Mmark : RationalFilteredNilmanifold M s f)
    (ideal : LieIdeal ℚ L)
    (hkill : D.filtration.layer (s + 1) ≤ ideal.toSubmodule)
    (Q : RationalFilteredNilmanifold (L ⧸ ideal) s dQ)
    (hQ : Q.filtration = D.filtration.quotientLie ideal hkill)
    (atoms : ∀ a, RationalFilteredNilmanifold (Partner a) s (dp a))
    (φ : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ ideal, φ x = 0)
    (hφ : ∀ k, ∀ x ∈ D.filtration.layer k, φ x ∈ Mmark.filtration.layer k)
    (source : (optionProduct Q atoms).AdaptedModelData)

include hQ hφ in

theorem exists_nativeOptionFixedSourceQuotientMarkGeometry
    {p : ℝ} (hp : 0 ≤ p)
    (hD : D.GeometryComplexityLE p) (hMmark : Mmark.GeometryComplexityLE p)
    (hQgeometry : Q.GeometryComplexityLE p)
    (hAtoms : ∀ a, (atoms a).GeometryComplexityLE p)
    (hPivot : (Fintype.card Pivot : ℝ) ≤ p)
    (hprojection : ∀ i j, rationalLogHeight
      (Q.basis.repr (lieQuotientMap ideal (D.basis j)) i) ≤ p)
    (hmark : ∀ i j, rationalLogHeight (Mmark.basis.repr (φ (D.basis j)) i) ≤ p)
    (hsource : ∀ i j, rationalLogHeight
      ((optionProduct Q atoms).basis.repr (source.basis i) j) ≤ (p + 3) ^ 2 + 1) :
    ∃ markGeometry : (optionProduct Q atoms).FixedSourceAdaptedMarkGeometryData
        (optionProduct Mmark atoms) source
        (optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker))
        (nativeOptionFixedSourceQuotientMarkInput p)
        ((nativeOptionFixedSourceQuotientMarkInput p + 2) ^ nativeOptionFixedSourceMarkExponent.{max u v, max u v}),
      markGeometry.target.model.filtration =
        NilpotentLieFiltration.pi
          (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) ∧
      ∀ k, ∀ x ∈ source.model.filtration.layer k,
        optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker) x ∈
          markGeometry.target.model.filtration.layer k := by
  have hinput := nativeOptionFixedSourceQuotientMarkInput_bounds hp
  have hinduced := D.quotientInducedMark_native_logHeight Mmark ideal Q φ hker
    hp hD hQgeometry hprojection hmark
  have hinduced0 : 0 ≤ quotientInducedMarkHeightBudget p := by
    unfold quotientInducedMarkHeightBudget
    positivity
  have hoption := optionMarkedLieMap_native_logHeight Q Mmark atoms
    (quotientInducedMark ideal φ hker) hinduced0 hinduced
  have hsourceGeo := optionProduct_geometry Q atoms hp hPivot hQgeometry hAtoms
  have htargetGeo := optionProduct_geometry Mmark atoms hp hPivot hMmark hAtoms
  obtain ⟨markGeometry⟩ :=
    (Classical.choose_spec exists_native_fixedSource_adapted_mark_geometry.{max u v, max u v}).2
      (optionProduct Q atoms) (optionProduct Mmark atoms) source
      (optionMarkedLieMap (L := Partner) (quotientInducedMark ideal φ hker))
      hinput.1
      (hsourceGeo.mono (optionProduct Q atoms) hinput.2.1)
      (htargetGeo.mono (optionProduct Mmark atoms) hinput.2.1)
      (fun i j => (hsource i j).trans (by linarith only [hinput.2.1]))
      (fun i j => (hoption j i).trans hinput.2.2)
  have hMark : markGeometry.target.model.filtration =
      NilpotentLieFiltration.pi
        (optionFiltrations Mmark.filtration (fun a => (atoms a).filtration)) := by
    change NilpotentLieFiltration.pi (fun i => (optionFactors Mmark atoms i).filtration) = _
    congr 1
    funext i
    cases i <;> rfl
  refine ⟨markGeometry, hMark, ?_⟩
  intro k x hx
  rw [hMark]
  exact D.nativeOptionFixedSourceQuotientMark_mem_layer Mmark ideal hkill Q hQ
    atoms φ hker hφ source k x hx

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CommonVariableDimensionNiltests
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_common_native_niltest_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G σ : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s d) {w : σ → ℕ}
      (T : ∀ h, (D h).Niltest w) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s d,
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest w),
          H' ⊆ H ∧ h₀ ∈ H' ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).normBound = (T h).normBound ∧
            (∀ x : σ → ℤ, (S h).eval x = (T h).eval x) ∧
            ((T h).UnitIntervalValued → (S h).UnitIntervalValued) := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_integral_models s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + 2) ^ 2)
  refine ⟨C, hC, ?_⟩
  intro G σ L _ _ _ _ _ _ d D w T H hH p hp hT
  let q := p + (p + c) ^ c
  have hc0 : 0 ≤ (p + c) ^ c := by positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hc0
  have hcq : (p + c) ^ c ≤ q := le_add_of_nonneg_left hp
  have hq0 : 0 ≤ q := hp.trans hpq
  have hbud : q + (q + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right (sq_nonneg _)).trans hbud
  obtain ⟨B, Λ, hB, hin, hout, hcover, h₀, hh₀, H', hsub, hh₀', hsame, hlarge⟩ :=
    hmodels D H hH hp (fun h => (hT h).1)
  let E₀ := (D h₀).withLattice (Λ h₀) (B h₀) (hB h₀) (hin h₀) (hout h₀)
  have hE₀ : E₀.GeometryComplexityLE q := (hcover h₀).2.2.2.mono E₀ hcq
  have hbuild (h : {h // h ∈ H'}) : ∃ S : E₀.Niltest w,
      S.ComplexityLE ((p + C) ^ C) ∧ S.normBound = (T h.val).normBound ∧
      (∀ x : σ → ℤ, S.eval x = (T h.val).eval x) ∧
      ((T h.val).UnitIntervalValued → S.UnitIntervalValued) := by
    let E₁ := (D h.val).withLattice (Λ h.val) (B h.val) (hB h.val) (hin h.val) (hout h.val)
    have hE₁ : E₁.GeometryComplexityLE q := (hcover h.val).2.2.2.mono E₁ hcq
    have hcode : E₁.rationalModelCoordinates = E₀.rationalModelCoordinates := (hsame h.val h.property).2
    have hcoords₁ : bchSubgroupCoordinates E₁.basis E₁.lattice = scaledIntegerGrid (B h₀) := by
      change bchSubgroupCoordinates (D h.val).basis (Λ h.val) = _
      rw [(hcover h.val).2.2.1, (hsame h.val h.property).1]
    let e := nativeModelEquivOfCoordinates E₁ E₀ hcode (B h₀) hcoords₁ (hcover h₀).2.2.1
    let T₁ := (T h.val).onSublattice (Λ h.val) (B h.val) (hB h.val)
      (hin h.val) (hout h.val) (hcover h.val).2.1
    have hT₁ : T₁.ComplexityLE q := (T h.val).onSublattice_complexity
      (Λ h.val) (B h.val) (hB h.val) (hin h.val) (hout h.val) (hcover h.val).2.1
      ((hT h.val).mono hpq) hE₁
    refine ⟨e.transport T₁, (e.transport_complexity T₁ hq0 hT₁ hE₀).mono hbud, rfl, ?_, ?_⟩
    · intro x
      exact e.transport_eval T₁ x
    · intro ht
      apply e.transport_unit_interval
      exact (T h.val).onSublattice_unit_interval (Λ h.val) (B h.val) (hB h.val)
        (hin h.val) (hout h.val) (hcover h.val).2.1 ht
  choose S hS using hbuild
  let S₀ : G → E₀.Niltest w := fun h =>
    if hh : h ∈ H' then S ⟨h, hh⟩ else Niltest.const E₀ w 0
  refine ⟨h₀, hh₀, E₀, hE₀.mono E₀ hqC, H', S₀, hsub, hh₀', ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (hcq.trans hqC)))
      (Nat.cast_nonneg _)).trans hlarge
  · intro h hh
    simpa only [S₀, dif_pos hh] using hS ⟨h, hh⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem exists_common_variable_dimension_niltest_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G σ : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h)) {w : σ → ℕ}
      (T : ∀ h, (D h).Niltest w) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest w),
          H' ⊆ H ∧ h₀ ∈ H' ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          ∀ h ∈ H', (S h).ComplexityLE ((p + C) ^ C) ∧ (S h).normBound = (T h).normBound ∧
            (∀ x : σ → ℤ, (S h).eval x = (T h).eval x) ∧
            ((T h).UnitIntervalValued → (S h).UnitIntervalValued) := by
  classical
  obtain ⟨c, _, hmodels⟩ := exists_common_native_niltest_model s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C c) ^ c + X + 1)
  refine ⟨C, hC, ?_⟩
  intro G σ L _ _ _ _ _ _ d D w T H hH p hp hT
  let q := (p + c) ^ c
  have hbud : q + p + 1 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hpexp : p ≤ Real.exp p := by linarith [Real.add_one_le_exp p]
  obtain ⟨hbase, _, H₀, hsub₀, hhbase, hsame, hlarge₀⟩ :=
    exists_common_bounded_moduli H hH (fun h (_ : Unit) => d h) hp
      (fun h _ _ => (hT h).1.1.trans hpexp)
  have hdim (h : {h // h ∈ H₀}) : d h.val = d hbase := congrFun (hsame h.val h.property) ()
  let D₀ := fun h : {h // h ∈ H₀} => (D h.val).castDimension (hdim h)
  let T₀ := fun h : {h // h ∈ H₀} => (T h.val).castDimension (hdim h)
  have hT₀ (h : {h // h ∈ H₀}) : (T₀ h).ComplexityLE p :=
    ((T h.val).castDimension_complexity (hdim h) p).mpr (hT h.val)
  obtain ⟨a, _, E₀, hE₀, H₁, S₁, _, ha, hlarge₁, hS₁⟩ :=
    hmodels D₀ T₀ Finset.univ ⟨⟨hbase, hhbase⟩, Finset.mem_univ _⟩ hp hT₀
  let E := E₀.castDimension (hdim a).symm
  let H' := H₁.image Subtype.val
  let S : G → E.Niltest w := fun h => if hh : h ∈ H₀ then
    (S₁ ⟨h, hh⟩).castDimension (hdim a).symm else Niltest.const E w 0
  have hcard : H'.card = H₁.card := Finset.card_image_of_injective _ Subtype.val_injective
  have hcard₀ : (Finset.univ : Finset {h // h ∈ H₀}).card = H₀.card := by simp
  have hlarge₀' : Real.exp (-(p + 1)) * H.card ≤ (H₀.card : ℝ) := by
    simpa only [Fintype.card_unit, Nat.cast_one, mul_one] using hlarge₀
  have hlarge₁' : Real.exp (-q) * H₀.card ≤ (H'.card : ℝ) := by
    rw [hcard]
    simpa only [hcard₀] using hlarge₁
  refine ⟨a.val, hsub₀ a.property, E,
    (E₀.castDimension_geometry (hdim a).symm _).mpr (hE₀.mono E₀ hqC), H', S, ?_, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hh
    exact hsub₀ g.property
  · exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤ Real.exp (-(q + (p + 1))) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith))) (Nat.cast_nonneg _)
      _ = Real.exp (-q) * (Real.exp (-(p + 1)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-q) * H₀.card := mul_le_mul_of_nonneg_left hlarge₀' (Real.exp_pos _).le
      _ ≤ H'.card := hlarge₁'
  · intro h hh
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hh
    have hSg := hS₁ g hg
    dsimp only [S]
    rw [dif_pos g.property]
    refine ⟨((S₁ g).castDimension_complexity (hdim a).symm _).mpr (hSg.1.mono hqC), ?_, ?_, ?_⟩
    · calc
        _ = (S₁ g).normBound := (S₁ g).castDimension_normBound _
        _ = (T₀ g).normBound := hSg.2.1
        _ = (T g.val).normBound := (T g.val).castDimension_normBound _
    · intro x
      calc
        _ = (S₁ g).eval x := (S₁ g).castDimension_eval _ x
        _ = (T₀ g).eval x := hSg.2.2.1 x
        _ = (T g.val).eval x := (T g.val).castDimension_eval _ x
    · intro ht
      apply ((S₁ g).castDimension_unit_interval (hdim a).symm).mpr
      apply hSg.2.2.2
      exact ((T g.val).castDimension_unit_interval (hdim g)).mpr ht

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RefilteredResidueExpansionSpec
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_kernel_residue_representatives (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
      (w : σ → ℕ), (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ M m : ℕ, 0 < M ∧ 0 < m ∧
        (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ g : (D.filtration.realification.adaptedPolynomialFiltration w).Group,
          D.filtration.PolynomialRationalGrid D.basis w q g →
          (∀ x : σ → ℤ, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
            (hM := F.lowerCentralSeries_eq_bot) φ
            (D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g) = 1) →
          ∃ r : (σ → ZMod M) → D.RealGroup,
            (∀ a, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := F.lowerCentralSeries_eq_bot) φ (r a) = 1 ∧
              (∀ i, |(D.basis.baseChange ℝ).repr (r a).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (D.basis.baseChange ℝ).equivFun (r a).coord ∈ realDenominatorGrid m) ∧
            ∀ x : σ → ℤ, ∃ γ ∈ D.realLattice,
              D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g =
                r (fun j => (x j : ZMod M)) * γ := by
  obtain ⟨a, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨b, _, hrep⟩ := exists_native_marked_kernel_representatives s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a +
    (Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c φ w hw p hp hD hσ hκ hφ q hq hqp
  obtain ⟨M, hM, hMb, hper⟩ := hperiod D w hw p hp hD hσ q hq hqp
  obtain ⟨m, hm, hmb, hreps⟩ := hrep D c φ p hp hD hκ hφ q hq hqp
  have hsum : (p + a) ^ a + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have haC : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hp (Nat.cast_nonneg b)) _)).trans hsum
  have hbC : (p + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) _)).trans hsum
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr haC),
    hmb.trans (Real.exp_le_exp.mpr hbC), ?_⟩
  intro g hg hmark
  let f := fun x : σ → ℤ => D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) g
  let A := fun r : D.RealGroup =>
    realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ r = 1 ∧
    (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
      (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m
  have hf (x : σ → ℤ) : ∃ r : D.RealGroup, A r ∧ ∃ γ ∈ D.realLattice, f x = r * γ := by
    have hxK := (mem_realificationSubgroup_ker_iff
      (hM := F.lowerCentralSeries_eq_bot) φ (f x)).mpr (hmark x)
    obtain ⟨r, hrK, hr, hrgrid, γ, hγ, hfac⟩ := hreps (f x) hxK
      (D.filtration.polynomialRationalGrid_value D.basis w q g hg x)
    refine ⟨r, ⟨?_, fun i => (hr i).trans (Real.exp_le_exp.mpr hbC), hrgrid⟩, γ, hγ, hfac⟩
    exact (mem_realificationSubgroup_ker_iff (hM := F.lowerCentralSeries_eq_bot) φ r).mp hrK
  obtain ⟨r, hr, hfac⟩ := exists_residue_class_right_lattice_factors D.realLattice f M A
    (fun x y hxy => (hper g hg x y hxy).1) hf
  exact ⟨r, hr, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_native_refiltration_model_of_bases {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s d : ℕ} (D : RationalFilteredNilmanifold L s d)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (b : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W))) ℚ
      (D.filtration.gradedRefiltrationSubalgebra W))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (D.basis.repr (b i : L) k) H)
    (hlayers : ∀ j, 1 ≤ j →
      ∃ a : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W j))) ℚ
        (D.filtration.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hgrid : (D.grid : ℝ) ≤ Real.exp p) :
    ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
        (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
      E.filtration = D.filtration.gradedRefiltration W ∧ E.basis = b ∧
      E.lattice = D.lattice.comap
        (NilpotentLieBCHGroup.map
          (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
          (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
      E.GeometryComplexityLE ((p + 2) ^ 11) := by
  classical
  let K := D.filtration.gradedRefiltrationSubalgebra W
  let F := D.filtration.gradedRefiltration W
  have hr : (finrank ℚ K : ℝ) ≤ p :=
    (Nat.cast_le.mpr (lie_subalgebra_finrank_le D.basis K)).trans (by simpa only [Fintype.card_fin] using hd)
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hr' : (Fintype.card (Fin (finrank ℚ K)) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hr
  have hmatrix : ∀ i j, RationalHeightLE (LinearMap.toMatrix b D.basis K.incl.toLinearMap i j) H := by
    intro i j
    rw [LinearMap.toMatrix_apply]
    change RationalHeightLE (D.basis.repr (b j : L) i) H
    exact hb j i
  obtain ⟨N, hN, hNb, hin, hout⟩ := exists_bchSubgroup_comap_grid_exp_bound
    (hM := F.lowerCentralSeries_eq_bot) b D.basis K.incl
    (fun _ _ h => Subtype.ext h) D.lattice hH D.grid_pos hmatrix D.inner_grid D.outer_grid
    hp hd' hr' hHp hgrid
  obtain ⟨_, _, _, hbracket⟩ := exists_bounded_lie_embedding_retraction b D.basis K.incl
    (fun _ _ h => Subtype.ext h) hH hc hmatrix
  have hbracketBudget := rationalLieStructureHeight_inverse_budget d (finrank ℚ K) H hp hd hr hHp
  have hLayer : ∀ i : Fin (s + 1),
      ∃ a : Basis (Fin (finrank ℚ (F.layer (i.val + 1)))) ℚ (F.layer (i.val + 1)),
        ∀ j k, rationalLogHeight (b.repr (a j : K) k) ≤ (p + 2) ^ 8 := by
    intro i
    obtain ⟨a, ha⟩ := hlayers (i.val + 1) (Nat.le_add_left 1 _)
    exact D.filtration.exists_native_refiltration_layer_basis W D.basis b (i.val + 1)
      (Nat.le_add_left 1 _) a hH hb ha hp hd' hr' hHp
  choose a ha using hLayer
  let E : RationalFilteredNilmanifold K s (finrank ℚ K) :=
    { filtration := F
      basis := b
      layerBasis := a
      lattice := D.lattice.comap (NilpotentLieBCHGroup.map (hnil := F.lowerCentralSeries_eq_bot) K.incl)
      grid := N
      grid_pos := hN
      inner_grid := hin
      outer_grid := hout }
  have hp1 : 1 ≤ p + 2 := by linarith
  have h9 : (p + 2) ^ 9 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  have h8 : (p + 2) ^ 8 ≤ (p + 2) ^ 11 := pow_le_pow_right₀ hp1 (by decide)
  refine ⟨E, rfl, rfl, rfl, hr.trans (le_power_budget hp (by decide)),
    hNb.trans (Real.exp_le_exp.mpr h9), ?_, ?_⟩
  · intro i j k
    apply rationalLogHeight_le_of_height (hbracket i j k)
    simpa only [Fintype.card_fin] using hbracketBudget
  · intro i j k
    exact (ha i j k).trans h8

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_refiltration_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d : ℕ} (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded) (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) s
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∀ i k, rationalLogHeight (D.basis.repr (E.basis i : L) k) ≤ (p + C) ^ C := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + 1 + (X + 1 + (X + 1 + 2) ^ 7 + 2) ^ 9
  let P := Q + (Q + 2) ^ 11
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d D w hF W v hspan p hp hD hκ hv
  let A := ⌈Real.exp p⌉₊
  have hA : 1 ≤ A := one_le_ceil_exp p
  have hAp : (A : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hp1 : 0 ≤ p + 1 := add_nonneg hp zero_le_one
  have hpp1 : p ≤ p + 1 := le_add_of_nonneg_right zero_le_one
  obtain ⟨B, hB, hBp, hBases⟩ := D.filtration.exists_uniform_refiltration_layer_bases D.basis w hF
    W v hspan hA (fun i k => rationalHeightLE_ceil_exp (hv i k)) hp1
    (by simpa only [Fintype.card_fin] using hD.1.trans hpp1)
    (hκ.trans hpp1) hAp
  let q := p + 1 + (p + 1 + (p + 1 + 2) ^ 7 + 2) ^ 9
  have hpq : p + 1 ≤ q := le_add_of_nonneg_right (by positivity)
  have hq : 0 ≤ q := hp1.trans hpq
  have hBq : (B : ℝ) ≤ Real.exp q :=
    hBp.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hp1))
  have hAq : (A : ℝ) ≤ Real.exp q := hAp.trans (Real.exp_le_exp.mpr hpq)
  let H := max B A
  have hH : 1 ≤ H := hB.trans (Nat.le_max_left _ _)
  have hHq : (H : ℝ) ≤ Real.exp q := by simpa only [H, Nat.cast_max] using max_le hBq hAq
  obtain ⟨b, hb⟩ := hBases 1
  have hLayers : ∀ j, 1 ≤ j →
      ∃ a : Basis (Fin (finrank ℚ (D.filtration.gradedRefiltrationLayer W j))) ℚ
        (D.filtration.gradedRefiltrationLayer W j),
        ∀ i k, RationalHeightLE (D.basis.repr (a i : L) k) H := by
    intro j _
    obtain ⟨a, ha⟩ := hBases j
    exact ⟨a, fun i k => (ha i k).mono (Nat.le_max_left _ _)⟩
  have hc : ∀ i j k, RationalHeightLE (lieStructureConstants D.basis i j k) H :=
    fun i j k => (rationalHeightLE_ceil_exp (hD.2.2.1 i j k)).mono (Nat.le_max_right _ _)
  obtain ⟨E, hEF, hEb, hEL, hEc⟩ := exists_native_refiltration_model_of_bases D W b hH
    (fun i k => (hb i k).mono (Nat.le_max_left _ _)) hLayers hc hq
    (hD.1.trans (hpp1.trans hpq)) hHq
    (hD.2.1.trans (Real.exp_le_exp.mpr (hpp1.trans hpq)))
  have hbound : q + (q + 2) ^ 11 ≤ (p + C) ^ C := by
    simpa [P, Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg hq (by norm_num)) 11)).trans hbound
  have hcost : (q + 2) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  refine ⟨E, hEF, hEL, hEc.mono E hcost, ?_⟩
  intro i k
  rw [hEb]
  exact (rationalLogHeight_le_of_height (hb i k) hBq).trans hqC

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_controlled_adapted_refiltration_model :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L s d)
      (b : Basis (Fin n) ℚ L) (w : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b w hF).repr (v i) j) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra U) s
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra U)),
        E.filtration = D.filtration.gradedRefiltration U ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration U).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra U).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∀ i j, rationalLogHeight (D.basis.repr (E.basis i : L) j) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hmodel⟩ := exists_controlled_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := (X + 4) ^ 11 + X + 1
  let R := T + (T + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (R + (R + 2) ^ 4)
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d n D b w hF U v hspan p hp hD hκ hb hv
  obtain ⟨m, hm, hin, hout, hB⟩ := D.exists_prescribed_adapted_model b w hF hp hD
    (fun i j => (hb i j).trans (by linarith))
  let B := D.filtration.ofAdaptedBasis b w hF D.lattice m hm hin hout
  let t := (p + 4) ^ 11 + p + 1
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hpt : p ≤ t := by dsimp [t]; linarith [pow_nonneg (by linarith : 0 ≤ p + 4) 11]
  have hBt : B.GeometryComplexityLE t := hB.mono B (by dsimp [t]; linarith)
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hmodel B w hF U v hspan ht hBt
    (hκ.trans hpt) (fun i j => (hv i j).trans hpt)
  let r := t + (t + A) ^ A
  have htr : t ≤ r := le_add_of_nonneg_right (by positivity)
  have hr : 0 ≤ r := ht.trans htr
  have hEr : (t + A) ^ A ≤ r := le_add_of_nonneg_left ht
  have hsum : r + (r + 2) ^ 4 ≤ (p + C) ^ C := by
    simpa [T, R, X, t, r, Polynomial.eval₂_pow] using hbudget p hp
  have hrC : r ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hheightC : (r + 2) ^ 4 ≤ (p + C) ^ C := (le_add_of_nonneg_left hr).trans hsum
  have hn : (Fintype.card (Fin n) : ℝ) ≤ r := by
    rw [← finrank_eq_card_basis b, finrank_eq_card_basis D.basis, Fintype.card_fin]
    exact hD.1.trans (hpt.trans htr)
  refine ⟨E, hEF, hEL, hE.mono E (hEr.trans hrC), ?_⟩
  intro i j
  exact (linearMap_coordinate_logHeight b D.basis (LinearMap.id : L →ₗ[ℚ] L) hr hn
    (fun a c => (hb a c).trans (hpt.trans htr)) (E.basis i : L)
    (fun k => (hinc i k).trans hEr) j).trans hheightC

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_adapted_single_refiltered_models :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L κ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype κ]
      {s d n : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
      (b : Basis (Fin n) ℚ L) (w : Fin n → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded)
      (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis b w hF).repr (v i) k) ≤ p) →
      ∃ E : RationalFilteredNilmanifold (D.filtration.gradedRefiltrationSubalgebra W) (s + 1)
          (finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W)),
        E.filtration = D.filtration.gradedRefiltration W ∧
        E.lattice = D.lattice.comap
          (NilpotentLieBCHGroup.map
            (hnil := (D.filtration.gradedRefiltration W).lowerCentralSeries_eq_bot)
            (D.filtration.gradedRefiltrationSubalgebra W).incl) ∧
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        (∀ i j, rationalLogHeight (D.basis.repr (E.basis j : L) i) ≤ (p + C) ^ C) ∧
        ∃ m : ℕ, m ≤ finrank ℚ (D.filtration.gradedRefiltrationSubalgebra W) ∧
          ∃ Q : RationalFilteredNilmanifold
              ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s m,
            Q.filtration = E.filtration.quotientTop ∧
            Q.lattice = E.lattice.map
              (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
            Q.GeometryComplexityLE ((p + C) ^ C) ∧
            ∀ i j, rationalLogHeight (Q.basis.repr
              (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤ (p + C) ^ C := by
  obtain ⟨A, _, hsource⟩ := exists_controlled_adapted_refiltration_model
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 11)
  refine ⟨C, hC, ?_⟩
  intro L κ _ _ _ s d n D b w hF W v hspan p hp hD hκ hb hv
  obtain ⟨E, hEF, hEL, hE, hinc⟩ := hsource D b w hF W v hspan hp hD hκ hb hv
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨m, hm, Q, hQF, hQL, hQ, hproj, _⟩ := E.exists_controlled_top_quotient ht (hE.mono E hAt)
  have hsum : t + (t + 3) ^ 11 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hQC : (t + 3) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  exact ⟨E, hEF, hEL, hE.mono E (hAt.trans htC),
    (fun i j => (hinc j i).trans (hAt.trans htC)), m, hm, Q, hQF, hQL,
    hQ.mono Q hQC, fun i j => (hproj j i).trans (h5.trans hQC)⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FixedAdaptedSymbolFactorizationBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

theorem exists_fixed_adapted_symbol_factorization_basis (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d) {p : ℝ},
      0 ≤ p → D.GeometryComplexityLE p →
      ∃ (c : Basis (Fin (finrank ℚ L)) ℚ L)
        (ν : Fin (finrank ℚ L) → ℕ) (N : ℕ),
      ∃ hC : ∀ j, D.filtration.layer j =
        Submodule.span ℚ (c '' {i | j ≤ ν i}),
      Monotone ν ∧ IsCentralLieBasis c ∧
      (∀ j i, rationalLogHeight (D.basis.repr (c j) i) ≤ p + 1) ∧
      (∀ i j, rationalLogHeight (c.repr (D.basis i) j) ≤ (p + 3) ^ 5) ∧
      (∀ i j k, rationalLogHeight (lieStructureConstants c i j k) ≤ (p + 3) ^ 11) ∧
      0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 3) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates c D.lattice ∧
      bchSubgroupCoordinates c D.lattice ⊆ denominatorGrid N ∧
      ∀ {q : ℝ}, p ≤ q →
      ∀ {σ : Type*} [Fintype σ], (Fintype.card σ : ℝ) ≤ q →
      ∀ (b : Basis (Fin (finrank ℚ L)) ℚ L)
        (ω : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j =
          Submodule.span ℚ (b '' {i | j ≤ ω i})),
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ q) →
      ∀ (T : σ → ℝ), (∀ i, 0 < T i) →
      ∀ (η : L →ₗ[ℚ] ℚ)
        (X : D.filtration.RealPolynomialSymbolGroup (fun _ : σ => 1)),
        D.filtration.ControlledSymbolFactorization b ω hF η T X q →
        D.filtration.ControlledSymbolFactorization c ν hC η T X
          ((fixedAdaptedSymbolTransferInput p q + C) ^ C) := by
  obtain ⟨C, hC, hchange⟩ :=
    NilpotentLieFiltration.exists_controlled_symbol_basis_change s
  refine ⟨C, hC, ?_⟩
  intro L _ _ d D p hp hD
  obtain ⟨c, ν, N, hν, hc, hlayers, hcoord, hinv, hbracket,
    hN, hNp, hin, hout⟩ := D.exists_controlled_adapted_basis hp hD
  refine ⟨c, ν, N, hlayers, hν, hc, hcoord, hinv, hbracket,
    hN, hNp, hin, hout, ?_⟩
  intro q hpq σ _ hσ b ω hF hb T hT η X hX
  let t : ℝ := (p + 3) ^ 5 + q + 1
  let R : ℝ := (t + 2) ^ 4 + q + 1
  have hq : 0 ≤ q := hp.trans hpq
  have hA : 0 ≤ (p + 3) ^ 5 := by positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hqt : q ≤ t := by dsimp [t]; linarith
  have hqR : q ≤ R := by
    dsimp only [R]
    linarith [show 0 ≤ (t + 2) ^ 4 by positivity]
  have hR : 0 ≤ R := hq.trans hqR
  have hd : (Fintype.card (Fin d) : ℝ) ≤ q := by
    simpa only [Fintype.card_fin] using hD.1.trans hpq
  have hdim : (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q := by
    simpa only [Fintype.card_fin, finrank_eq_card_basis D.basis] using hd
  have hH₀ : (⌈Real.exp ((p + 3) ^ 5)⌉₊ : ℝ) ≤ Real.exp t :=
    (ceil_exp_le_exp_add_one hA).trans
      (Real.exp_le_exp.mpr (by dsimp [t]; linarith))
  have hbc : ∀ i j, rationalLogHeight (c.repr (b i) j) ≤ (t + 2) ^ 4 := by
    intro i j
    exact rational_basis_coordinates_logHeight D.basis c ht (hd.trans hqt) hH₀
      (fun i j => rationalHeightLE_ceil_exp (hinv i j)) (b i)
      (fun j => (hb i j).trans hqt) j
  have hH : (⌈Real.exp ((t + 2) ^ 4)⌉₊ : ℝ) ≤ Real.exp R :=
    (ceil_exp_le_exp_add_one (by positivity)).trans
      (Real.exp_le_exp.mpr (by dsimp [R]; linarith))
  apply hchange D.filtration b ω hF c ν hlayers
    ⌈Real.exp ((t + 2) ^ 4)⌉₊ R (one_le_ceil_exp _) hR
    (hdim.trans hqR) (hdim.trans hqR) (hσ.trans hqR) hH
    (fun i j => rationalHeightLE_ceil_exp (hbc i j)) T hT η X
  exact hX.mono D.filtration b ω hF hqR hT

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open CircleFourier
open scoped TensorProduct BigOperators

theorem exists_common_vertical_correlators :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h ∈ H, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) →
      (∀ h k, (T h).observable = (T k).observable) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)) (eta : L →ₗ[ℚ] ℚ),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ i, rationalLogHeight (eta (D.basis i)) ≤ (p + C) ^ C) ∧
        (∀ h, (S h).orbit = (T h).orbit ∧ (S h).normBound ≤ 1 ∧
          (S h).ComplexityLE ((p + C) ^ C)) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        (∀ h z, z ∈ D.filtration.realification.subgroup s → ∀ x,
          (S h).observable (z • x) =
            character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) * (S h).observable x) ∧
        (∀ z : D.RealGroup, z ∈ D.filtration.realification.subgroup s → z ∈ D.realLattice →
          ∃ n : ℤ, realifyFunctional eta z.coord = n) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  classical
  obtain ⟨a, _, hverticalBudget⟩ := exists_verticalDecompositionBudget_bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (X + 1 + (X + 1 + Polynomial.C a) ^ a + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ s d D T H hH p hp hT hcap hsame N _ weight hweight hcorr
  obtain ⟨h₀, hh₀⟩ := hH
  let q := (p + 1 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hcost : p + 1 + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p + 1 ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hVq : verticalDecompositionBudget (p + 1) ≤ q := hverticalBudget (p + 1) (by linarith)
  have hrho : 0 < Real.exp (-p) / 2 := by positivity
  have hrhoinv : (Real.exp (-p) / 2)⁻¹ ≤ Real.exp (p + 1) := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp p := by rw [inv_div, Real.exp_neg]; field_simp
      _ ≤ Real.exp 1 * Real.exp p := mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨J, inst, eta, V, hcard, hheight, hV, hvert, hint, happ, _⟩ :=
    (T h₀).exists_vertical_decomposition_preserving_bounds (by linarith : 0 ≤ p + 1)
      ((hT h₀ hh₀).mono (by linarith : p ≤ p + 1)) hrho hrhoinv
  let := inst
  have hcardq : (Fintype.card J : ℝ) ≤ Real.exp q := hcard.trans (Real.exp_le_exp.mpr hVq)
  let U (h : G) (j : J) : D.Niltest (fun _ : Unit => 1) := { V j with orbit := (T h).orbit }
  have hchoose (h : {h // h ∈ H}) : ∃ j : J,
      Real.exp (-p) / (2 * Real.exp q) ≤
        ‖𝔼 x, weight h.val x * star ((U h.val j).evalCyclic N (fun _ => x))‖ := by
    apply exists_correlating_summand Finset.univ_nonempty (weight h.val)
      (fun x => (T h.val).evalCyclic N (fun _ => x))
      (fun j x => (U h.val j).evalCyclic N (fun _ => x))
      (Real.exp_pos (-p)) (Real.exp_pos q) hcardq
      (fun x _ => hweight h.val h.property x) _ (hcorr h.val h.property)
    intro x _
    change ‖(∑ j, (V j).observable (QuotientGroup.mk
      (D.filtration.realification.polynomialOrbitEval (fun _ => 1)
        (fun _ => (x.val : ℤ)) (T h.val).orbit))) -
      (T h.val).observable (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ => 1)
          (fun _ => (x.val : ℤ)) (T h.val).orbit))‖ ≤ _
    rw [hsame h.val h₀]
    exact happ _
  choose choice hchoice using hchoose
  let code : G → J := fun h => if hh : h ∈ H then choice ⟨h, hh⟩ else choice ⟨h₀, hh₀⟩
  obtain ⟨j, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H ⟨h₀, hh₀⟩ code Set.univ (Set.toFinite _)
      (fun _ _ => Set.mem_univ _) (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hcardq)
  have hselected (h : G) (hh : h ∈ H') : Real.exp (-p) / (2 * Real.exp q) ≤
      ‖𝔼 x, weight h x * star ((U h j).evalCyclic N (fun _ => x))‖ := by
    have hcode : choice ⟨h, hsub hh⟩ = j := by
      simpa only [code, dif_pos (hsub hh)] using hconstant h hh
    simpa only [hcode] using hchoice ⟨h, hsub hh⟩
  have hne : ∃ x, (V j).observable x ≠ 0 := by
    by_contra! hz
    obtain ⟨h, hh⟩ := hnonempty
    have hc := hselected h hh
    have hzero (x : ZMod N) : (U h j).evalCyclic N (fun _ => x) = 0 := hz _
    simp only [hzero, star_zero, mul_zero, Finset.expect_const_zero, norm_zero] at hc
    exact (not_le_of_gt (by positivity : 0 < Real.exp (-p) / (2 * Real.exp q))) hc
  refine ⟨H', fun h => U h j, eta j, hsub, hnonempty, ?_, ?_, ?_, fun _ _ => rfl,
    fun _ z hz x => hvert j z hz x, hint j hne, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro i
    exact (hheight j i).trans (hVq.trans hqC)
  · intro h
    refine ⟨rfl, ?_, ?_⟩
    · change (V j).normBound ≤ 1
      rw [(hV j).2.2.1]
      exact hcap h₀ hh₀
    · exact (hV j).1.mono hpC
  · intro h hh
    apply le_trans _ (hselected h hh)
    calc
      _ ≤ Real.exp (-(p + q) - 1) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-(p + q)) / 2 := exp_sub_one_le_half_exp _
      _ = Real.exp (-p) / (2 * Real.exp q) := by
        rw [show -(p + q) = -p - q by ring, Real.exp_sub]
        ring

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

def PrescribedPartitionExpansionSpec (s r b₀ k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) ((s + 1) + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) (s + 1) (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ (s + 1) d₀),
      let T := optionFactors D₀ Z
      ∀ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded) {dR dQ : ℕ}
        (R : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra W) (s + 1) dR)
        (Q₀ : RationalFilteredNilmanifold
          (((pi T).filtration.gradedRefiltrationSubalgebra W) ⧸ R.filtration.layerIdeal (s + 1)) s dQ)
        [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)] {p cost : ℝ} (q : ℕ),
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → 0 ≤ cost → cost ≤ (p + b₀) ^ b₀ →
      RefilteredProductExpansionSpec T none W R Q₀ p q r cost →
      let H := (pi T).filtration.gradedRefiltrationSubalgebra W
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
      letI := realification_moduleTopology_t2 Q₀.basis
      ∃ Q' : RationalFilteredNilmanifold (H ⧸ R.filtration.layerIdeal (s + 1)) s dQ,
        Q'.filtration = Q₀.filtration ∧ Q'.basis = Q₀.basis ∧ Q'.lattice ≤ Q₀.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (c : ι → ℤ) (N : ℕ) [NeZero N] {ε : ℝ},
        0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
        ∃ (I : Type) (inst : Fintype I), letI := inst;
          (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : I → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1 + 1) N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
            ∀ {J₀ : Type} (freq : J₀ → ∀ i, optionLieSpace L₀
              (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (S : ZMod N → (T none).Niltest (fun _ : Unit => 1)),
                (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                (∀ h z, z ∈ (T none).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (freq j none) z.coord = 0) →
                  ∀ x, (S h).observable (z • x) = (S h).observable x) →
                ∀ (Hsh : Set (ZMod N))
                  (gT : ZMod N → ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (branch : ZMod N → ι → Fin 2) (η γ : ZMod N → ∀ i, (D i).RealGroup)
                  (rSq : ZMod N → ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (qSq : ZMod N → ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                  (∀ h ∈ Hsh, gT h none = (S h).orbit) →
                  (∀ h ∈ Hsh, ∀ i, gT h (some i) = sumOrbits E Q g (qSq h) i) →
                  (∀ h ∈ Hsh, ∀ i, γ h i ∈ (D i).realLattice) →
                  (∀ h ∈ Hsh, ∀ i j, |((D i).basis.baseChange ℝ).repr (η h i).coord j| ≤
                    Real.exp ((p + 2) ^ k₀)) →
                  (∀ h ∈ Hsh, ∀ i (z : Unit → ℤ),
                    (D i).filtration.realSquareFstHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (η h i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => (h.val : ℤ) - ((branch h i).val : ℤ) * N) (g₀ i) * (γ h i)⁻¹ ∧
                    (D i).filtration.realSquareSndHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => c i) (g₀ i)) →
                  (∀ h ∈ Hsh, ∀ i, qSq h i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
                    ((D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h i)) →
                  ∀ (slow middle rat : ZMod N →
                      ((pi T).filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
                    (δ : ZMod N → (pi T).RealGroup),
                    (∀ h ∈ Hsh, δ h ∈ (pi T).realLattice) →
                    (∀ h ∈ Hsh, slow h * middle h * rat h *
                      (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (δ h) =
                        ⟨⟨(piRealOrbit (fun i => (T i).filtration) (gT h)).log,
                          (piRealOrbit (fun i => (T i).filtration) (gT h)).property⟩⟩) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1) q (rat h)) →
                    (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) α ∈
                        (pi T).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α)) →
                    (∀ h ∈ Hsh, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) 0 = 0) →
                    ∃ U : I → I → ZMod N → Q'.Niltest (fun _ : Unit => 1),
                      (∀ i j h, (U i j h).UnitIntervalValued) ∧
                      (∀ i j h, (U i j h).ComplexityLE ((p + C) ^ C)) ∧
                      (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ε ∧ 0 < A i x * A j (x + h)) →
                        ∀ x, (U i j h).eval x = 0) ∧
                      ∃ err : ZMod N → ZMod N → ℝ,
                        (∀ h ∈ Hsh, ∀ x, ((S h).evalCyclic N (fun _ => x)).re =
                          (∑ i, ∑ j, A i x * A j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                        ∀ h, (𝔼 x, |err h x|) ≤ Real.exp ((p + B) ^ B) * ε + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnitVerticalNativeInverseModels
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

theorem exists_common_observable_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G : Type*} {L : G → Type*}
      [∀ h, LieRing (L h)] [∀ h, LieAlgebra ℚ (L h)]
      [∀ h, TopologicalSpace (ℝ ⊗[ℚ] L h)] [∀ h, IsTopologicalAddGroup (ℝ ⊗[ℚ] L h)]
      [∀ h, ContinuousSMul ℝ (ℝ ⊗[ℚ] L h)] [∀ h, T2Space (ℝ ⊗[ℚ] L h)] {d : G → ℕ}
      (D : ∀ h, RationalFilteredNilmanifold (L h) s (d h))
      (T : ∀ h, (D h).Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → (∀ h, (T h).ComplexityLE p) →
      (∀ h ∈ H, (T h).normBound ≤ 1) → ∀ {N : ℕ} [NeZero N]
      (weight : G → ZMod N → ℂ), (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ h₀ ∈ H, ∃ E : RationalFilteredNilmanifold (L h₀) s (d h₀),
        E.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ (H' : Finset G) (S : G → E.Niltest (fun _ : Unit => 1)),
          H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
          (∀ h, (S h).normBound ≤ 1 ∧ (S h).UnitIntervalValued ∧
            (S h).ComplexityLE ((p + C) ^ C)) ∧
          (∀ h k, (S h).observable = (S k).observable) ∧
          ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
            ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  obtain ⟨c, _, hmodels⟩ := exists_common_variable_dimension_niltest_model s
  obtain ⟨k, _, hfixed⟩ := exists_fixed_observable_correlators s
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C c) ^ c + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C k) ^ k + (X + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hT hcap N _ weight hweight hcorr
  let q := p + (p + c) ^ c + 2
  have hpow : 0 ≤ (p + c) ^ c := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hmodelq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := hp.trans hpq
  have hfixed0 : 0 ≤ (q + k) ^ k := by positivity
  have hcost : q + (q + k) ^ k + (p + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hfixedC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  have hmodelC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨h₀, hh₀, E, hE, H₁, P, hsub₁, hh₀', hlarge₁, hP⟩ :=
    hmodels D T H hH hp hT
  have hPeval (h : G) (hh : h ∈ H₁) (x : ZMod N) :
      (P h).evalCyclic N (fun _ => x) = (T h).evalCyclic N (fun _ => x) :=
    (hP h hh).2.2.1 _
  obtain ⟨H₂, S, hsub₂, hH₂, hlarge₂, hS, hsame, hcorrS⟩ :=
    hfixed E P H₁ ⟨h₀, hh₀'⟩ hq (hE.mono E hmodelq)
      (fun h hh => (hP h hh).1.mono hmodelq)
      (fun h hh => by rw [(hP h hh).2.1]; exact hcap h (hsub₁ hh)) weight
      (fun h hh x => hweight h (hsub₁ hh) x)
      (fun h hh => by
        simp_rw [hPeval h hh]
        exact (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans (hcorr h (hsub₁ hh)))
  refine ⟨h₀, hh₀, E, hE.mono E hmodelC, H₂, S, hsub₂.trans hsub₁, hH₂, ?_,
    fun h => ⟨(hS h).2.1, (hS h).2.2.1, (hS h).2.2.2.mono hfixedC⟩, hsame, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * H.card ≤
          Real.exp (-((q + k) ^ k + (p + c) ^ c)) * H.card :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg (by linarith)))
          (Nat.cast_nonneg _)
      _ = Real.exp (-((q + k) ^ k)) * (Real.exp (-((p + c) ^ c)) * H.card) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((q + k) ^ k)) * H₁.card :=
        mul_le_mul_of_nonneg_left hlarge₁ (Real.exp_nonneg _)
      _ ≤ _ := hlarge₂
  · intro h hh
    exact (Real.exp_le_exp.mpr (neg_le_neg hfixedC)).trans (hcorrS h hh)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedModularRankMixedUniform
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*}

abbrev AllocatedSelectedCoefficientIndex (X : Type*) (E : Fin m → Type*)
    (inactive : LayerSamplerAxis I n → Prop) (L : ℕ) :=
  Σ j : Fin m, AllocatedTaggedRankOutput X E inactive j × Fin L

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformFiniteMarkedFactorParameters
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_marked_rational_factor_freezing_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
      (w : σ → ℕ), (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∀ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
      Function.RightInverse S φ →
      (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
        (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) →
      ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
      D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) := by
  obtain ⟨a, _, hgrid⟩ := NilpotentLieFiltration.exists_marked_kernel_rational_grid_bound s
  obtain ⟨b, _, hreps⟩ := exists_native_marked_kernel_residue_representatives s
  let U : Polynomial ℕ := (Polynomial.X + 3) ^ 11
  let V : Polynomial ℕ := (U + Polynomial.C a) ^ a + U
  let P : Polynomial ℕ := (V + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c ω hlayers φ hφ w hw p hp hD hσ hκ hφb
    S hS hright hSb l hl hlp
  classical
  let p0 := p + 1
  let u := (p0 + 2) ^ 11
  let v := (u + a) ^ a + u
  let H := ⌈Real.exp p⌉₊
  have hp0 : 0 ≤ p0 := by dsimp [p0]; positivity
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpu : p ≤ u := (show p ≤ p0 by dsimp [p0]; linarith).trans
    (le_power_budget hp0 (by decide : 1 ≤ 11))
  have huv : u ≤ v := le_add_of_nonneg_left (by positivity)
  have hpv : p ≤ v := hpu.trans huv
  have hv : 0 ≤ v := hu.trans huv
  have hd0 : (Fintype.card (Fin d) : ℝ) ≤ p0 := by
    simpa only [Fintype.card_fin] using hD.1.trans (show p ≤ p0 by dsimp [p0]; linarith)
  have hκ0 : (Fintype.card κ : ℝ) ≤ p0 := hκ.trans (by dsimp [p0]; linarith)
  have hH : (H : ℝ) ≤ Real.exp p0 := ceil_exp_le_exp_add_one hp
  have hφH : ∀ i j, RationalHeightLE (c.repr (φ (D.basis j)) i) H :=
    fun i j => rationalHeightLE_ceil_exp (hφb i j)
  have hden : ((matrixDenominator (LinearMap.toMatrix c D.basis S) * l : ℕ) : ℝ) ≤
      Real.exp u := by
    apply filtered_section_single_denominator_le_exp
      (LinearMap.toMatrix D.basis c φ.toLinearMap) (LinearMap.toMatrix c D.basis S) l
      hp0 hd0 hκ0 hH
    · intro i j
      rw [LinearMap.toMatrix_apply]
      exact hφH i j
    · simpa only [LinearMap.toMatrix_apply] using hSb
    · exact hlp.trans (Real.exp_le_exp.mpr (by dsimp [p0]; linarith))
  have hHpu : (H : ℝ) ≤ Real.exp u := hH.trans
    (Real.exp_le_exp.mpr (le_power_budget hp0 (by decide : 1 ≤ 11)))
  obtain ⟨q, hq, hqb, _, hqgrid⟩ := hgrid D.filtration F D.basis c ω hlayers w hw H u
    (one_le_ceil_exp p) hu (by simpa only [Fintype.card_fin] using hD.1.trans hpu)
    (hσ.trans hpu) hHpu (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k))
    S hS l hl hden
  have hqv : (q : ℝ) ≤ Real.exp v := hqb.trans
    (Real.exp_le_exp.mpr (le_add_of_nonneg_right hu))
  obtain ⟨M, m, hM, hm, hMb, hmb, hfreeze⟩ := hreps D F c φ w hw v hv
    (GeometryComplexityLE.mono D hD hpv) (hσ.trans hpv) (hκ.trans hpv)
    (fun i j => (hφb i j).trans hpv) q hq hqv
  have hb : (v + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, V, U, v, u, p0, Polynomial.eval₂_pow, add_assoc,
      show (1 : ℝ) + 2 = 3 by norm_num] using hbudget p hp
  refine ⟨M, m, hM, hm, hMb.trans (Real.exp_le_exp.mpr hb),
    hmb.trans (Real.exp_le_exp.mpr hb), ?_⟩
  intro R RF hR hRF hmark
  let KR := (D.filtration.filteredRealPolynomialSection F w S hS RF)⁻¹ * R
  have hKR : D.filtration.realPolynomialGroupMap F φ hφ w KR = 1 := by
    dsimp only [KR]
    rw [map_mul, map_inv, hmark,
      D.filtration.realPolynomialGroupMap_filteredSection F w φ hφ S hS hright RF,
      inv_mul_cancel]
  have hpoint (x : σ → ℤ) : realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
      (hM := F.lowerCentralSeries_eq_bot) φ
      (D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ)) KR) = 1 := by
    rw [← D.filtration.realPolynomialGroupMap_value F φ hφ w, hKR, map_one]
  obtain ⟨r, hr, hfac⟩ := hfreeze KR (hqgrid R RF hR hRF) hpoint
  refine ⟨r, fun z => ⟨(hr z).1, fun i => ((hr z).2.1 i).trans
    (Real.exp_le_exp.mpr hb), (hr z).2.2⟩, ?_⟩
  intro x
  obtain ⟨γ, hγ, heq⟩ := hfac x
  refine ⟨γ, hγ, heq, ?_⟩
  have heq' := heq
  dsimp only [KR] at heq'
  rw [map_mul, map_inv] at heq'
  calc
    _ = D.filtration.adaptedPolynomialRealValueHom w (fun j => (x j : ℝ))
        (D.filtration.filteredRealPolynomialSection F w S hS RF) *
        (r (fun j => (x j : ZMod M)) * γ) := by
      rw [← heq']
      group
    _ = _ := (mul_assoc _ _ _).symm

theorem exists_native_marked_rational_factor_freezing (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) := by
  obtain ⟨C, hC, hfreeze⟩ := exists_native_marked_rational_factor_freezing_bound s
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hright, hS, hSb⟩ := D.filtration.exists_bounded_filtered_section F D.basis ω
    hDlayers c τ hFlayers φ.toLinearMap hsurj (one_le_ceil_exp p)
    (fun i j => rationalHeightLE_ceil_exp (hφb i j))
  exact ⟨S, hS, hright, hSb,
    hfreeze D F c ω hDlayers φ hφ w hw p hp hD hσ hκ hφb S hS hright hSb⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_marked_factor_parameters (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.MarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) ∧
            D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨A, _, hrat⟩ := exists_native_marked_rational_factor_freezing s
  obtain ⟨B, _, hslow⟩ := NilpotentLieFiltration.exists_actual_marked_slow_kernel_cells s (max a 7) u
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C A) ^ A +
    (Polynomial.X + 1 + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  classical
  obtain ⟨S, hS, hright, hSb, hratS⟩ := hrat D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  have hsum : (p + A) ^ A + (p + 1 + B) ^ B ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hA : (p + A) ^ A ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (p + 1 + B) ^ B)).trans hsum
  have hB : (p + 1 + B) ^ B ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity : 0 ≤ (p + A) ^ A)).trans hsum
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  refine ⟨(hratS l hl hlp).mono (Real.exp_le_exp.mpr hA), ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  let H := ⌈Real.exp p⌉₊
  have hp1 : 0 ≤ p + 1 := by positivity
  have hp_le : p ≤ p + 1 := by linarith
  have hH : (H : ℝ) ≤ Real.exp (p + 1) := ceil_exp_le_exp_add_one hp
  have hK := rationalKernelHeight_le_budget (Fintype.card κ) H hp1 (hκ.trans hp_le) hH
  have hentry : ∀ i j, |(D.basis.repr (S (c j)) i : ℝ)| ≤
      Real.exp (((p + 1) + 2) ^ max a 7) := by
    intro i j
    apply ((hSb i j).abs_real_le.trans hK).trans
    apply Real.exp_le_exp.mpr
    exact pow_le_pow_right₀ (by linarith : 1 ≤ (p + 1) + 2) (le_max_right _ _)
  obtain ⟨N, Q, hN, hQ, hNcard, hQcard, center, hmark, hcap, hfreeze⟩ :=
    hslow D.filtration F D.basis c ω hDlayers w hw φ hφ S hS hright H (p + 1)
      (one_le_ceil_exp p) hp1 (by simpa only [Fintype.card_fin] using hD.1.trans hp_le)
      (hκ.trans hp_le) (hσ.trans hp_le) hH
      (fun i j k => rationalHeightLE_ceil_exp (hD.2.2.1 i j k)) hentry Tbox hT
  refine ⟨N, Q, hN, hQ, hNcard.trans (Real.exp_le_exp.mpr hB),
    hQcard.trans (Real.exp_le_exp.mpr hB), center, hmark,
    fun j i => (hcap j i).trans (Real.exp_le_exp.mpr hB), ?_⟩
  intro E EF hE hEF hproj
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp (((p + 1) + 2) ^ max a 7) := by
    apply Real.exp_le_exp.mpr
    exact (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
      (by linarith : p + 2 ≤ (p + 1) + 2) a).trans
      (pow_le_pow_right₀ (by linarith : 1 ≤ (p + 1) + 2) (le_max_left _ _))
  obtain ⟨label, hlabel⟩ := hfreeze E EF
    (D.filtration.polynomialSlowBound_mono D.basis w Tbox hT hinput E hE)
    (F.polynomialSlowBound_mono c w Tbox hT hinput EF hEF) hproj
  refine ⟨label, ?_⟩
  intro j v hv hvj
  apply (hlabel j v hv hvj).trans
  apply Real.exp_le_exp.mpr
  exact neg_le_neg (pow_le_pow_left₀ (by linarith : 0 ≤ p + 2)
    (by linarith : p + 2 ≤ (p + 1) + 2) u)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold
open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_uniform_finite_marked_factor_parameters (s a u : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d t : ℕ} (D : RationalFilteredNilmanifold L s d)
      (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
      (ω : Fin d → ℕ)
      (_hDlayers : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
      (τ : κ → ℕ) (_hFlayers : ∀ j, F.layer j = Submodule.span ℚ (c '' {i | j ≤ τ i}))
      (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j),
      (∀ j, ∀ y ∈ F.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ w : σ → ℕ, (∀ i, 0 < w i) → ∀ p : ℝ,
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (c.repr (φ (D.basis j)) i) ≤ p) →
      ∃ (S : T →ₗ[ℚ] L) (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j),
        Function.RightInverse S φ ∧
        (∀ i j, RationalHeightLE (D.basis.repr (S (c j)) i)
          (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)) ∧
        ∀ l : ℕ, 0 < l → (l : ℝ) ≤ Real.exp p →
          ∀ Tbox : σ → ℝ, (∀ i, 0 < Tbox i) →
            D.FiniteMarkedRationalFactorFreezing F c φ hφ w S hS l (Real.exp ((p + C) ^ C)) ∧
            D.MarkedSlowFactorFreezing F c φ hφ w S hS Tbox
              (Real.exp ((p + 2) ^ a)) (Real.exp (-((p + 2) ^ u)))
              (Real.exp ((p + C) ^ C)) := by
  obtain ⟨A, hA, hparams⟩ := exists_uniform_marked_factor_parameters s a u
  let X : Polynomial ℕ := Polynomial.X
  let U := (X + Polynomial.C A) ^ A
  let P := U + (X + U + 2) ^ 3
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ κ L T _ _ _ _ _ _ _ _ _ _ _ d t D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  obtain ⟨S, hS, hright, hSb, hboth⟩ := hparams D F c ω hDlayers τ hFlayers φ hφ hsurj
    w hw p hp hD hσ hκ hφb
  refine ⟨S, hS, hright, hSb, ?_⟩
  intro l hl hlp Tbox hT
  obtain ⟨hrat, hslow⟩ := hboth l hl hlp Tbox hT
  let q := p + (p + A) ^ A
  have hAp : 0 ≤ (p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_add_of_nonneg_right hAp
  have hAq : (p + A) ^ A ≤ q := le_add_of_nonneg_left hp
  have hbud : (p + A) ^ A + (q + 2) ^ 3 ≤ (p + C) ^ C := by
    simpa [P, U, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hAcap : (p + A) ^ A ≤ (p + C) ^ C := by
    have : 0 ≤ (q + 2) ^ 3 := by positivity
    linarith
  have hqcap : (q + 2) ^ 3 ≤ (p + C) ^ C := by linarith
  have hBB : Real.exp ((p + A) ^ A) ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hAcap
  refine ⟨?_, hslow.mono_bound hBB⟩
  obtain ⟨M, m, n, hM, hm, hn, hMb, hmb, hnb, center, hcenter, hfac⟩ :=
    MarkedRationalFactorFreezing.finite_enumeration D F c φ hφ w S hS l hq
      (hD.1.trans hpq) (Real.exp_le_exp.mpr hAq) hrat
  exact ⟨M, m, n, hM, hm, hn, hMb.trans hBB, hmb.trans hBB,
    hnb.trans (Real.exp_le_exp.mpr hqcap), center,
    fun j => ⟨(hcenter j).1, fun i => ((hcenter j).2.1 i).trans hBB, (hcenter j).2.2⟩, hfac⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
namespace OAI


namespace Erdos3.RationalFilteredNilmanifold

open NilpotentLieFiltration

theorem exists_controlled_marked_top_quotient :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {s d e n : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (E : RationalFilteredNilmanifold M (s + 1) e)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ E.filtration.layer j)
      (Q : RationalFilteredNilmanifold (L ⧸ D.filtration.layerIdeal (s + 1)) s n)
      (_hQ : Q.filtration = D.filtration.quotientTop),
      (∀ j, ∀ y ∈ E.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      Q.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (D.filtration.layerIdeal (s + 1)) (D.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis i)) j) ≤ p) →
      ∃ m : ℕ, m ≤ e ∧
        ∃ QF : RationalFilteredNilmanifold (M ⧸ E.filtration.layerIdeal (s + 1)) s m,
          QF.filtration = E.filtration.quotientTop ∧
          QF.lattice = E.lattice.map
            (E.filtration.quotientStepHom (E.filtration.layerIdeal (s + 1)) le_rfl) ∧
          QF.GeometryComplexityLE ((p + C) ^ C) ∧
          (∀ i j, rationalLogHeight (QF.basis.repr
            (lieQuotientMap (E.filtration.layerIdeal (s + 1)) (E.basis j)) i) ≤
              (p + C) ^ C) ∧
          (∀ i j, rationalLogHeight
            (QF.basis.repr (D.topQuotientMarkedMap E φ hφ (Q.basis i)) j) ≤
              (p + C) ^ C) ∧
          (∀ j, ∀ x ∈ Q.filtration.layer j,
            D.topQuotientMarkedMap E φ hφ x ∈ QF.filtration.layer j) ∧
          ∀ j, ∀ y ∈ QF.filtration.layer j, ∃ x ∈ Q.filtration.layer j,
            D.topQuotientMarkedMap E φ hφ x = y := by
  obtain ⟨C, hC, hbudget⟩ := exists_nativeMarkedQuotientHeightBudget 11
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ s d e n D E φ hφ Q hQ hsurj p hp hD hE hQgeom hproj hmark
  obtain ⟨m, hm, QF, hQF, hQFL, hQFgeom, hprojF, _⟩ :=
    E.exists_controlled_top_quotient hp hE
  have hpA : p ≤ (p + 11) ^ 11 := by
    calc
      p ≤ (p + 2) ^ 11 := le_power_budget hp (by decide)
      _ ≤ (p + 11) ^ 11 := by gcongr; norm_num
  have hgeoA : (p + 3) ^ 11 ≤ (p + 11) ^ 11 := by gcongr; norm_num
  have hprojA : (p + 3) ^ 5 ≤ (p + 11) ^ 11 := by
    calc
      (p + 3) ^ 5 ≤ (p + 3) ^ 11 :=
        pow_le_pow_right₀ (by linarith) (by decide)
      _ ≤ (p + 11) ^ 11 := hgeoA
  obtain ⟨hAC, hmapC⟩ := hbudget p hp
  refine ⟨m, hm, QF, hQF, hQFL, hQFgeom.mono QF (hgeoA.trans hAC),
    (fun i j => (hprojF j i).trans (hprojA.trans hAC)), ?_, ?_, ?_⟩
  · intro i j
    exact (D.topQuotientMarkedMap_basis_logHeight E φ hφ Q QF (hp.trans hpA)
      (hD.mono D hpA) (hE.mono E hpA) (hQgeom.mono Q hpA)
      (fun i j => (hproj i j).trans hpA) (fun i j => (hmark i j).trans hpA)
      (fun i j => (hprojF j i).trans hprojA) i j).trans hmapC
  · exact D.topQuotientMarkedMap_mem_layer E φ hφ Q hQ QF hQF
  · exact D.topQuotientMarkedMap_layer_surjective E φ hφ Q hQ QF hQF hsurj

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

universe u

theorem exists_marked_refiltered_native_diagram :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L M : Type u} {κ : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] [Fintype κ]
      {s d f n k : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (b : Basis (Fin n) ℚ L) (ω : Fin n → ℕ)
      (hD : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (c : Basis (Fin k) ℚ M) (ν : Fin k → ℕ)
      (_hF : ∀ j, Fmark.filtration.layer j = Submodule.span ℚ (c '' {i | j ≤ ν i}))
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j),
      (∀ j, ∀ y ∈ Fmark.filtration.layer j, ∃ x ∈ D.filtration.layer j, φ x = y) →
    ∀ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (v : κ → D.filtration.AssociatedGraded),
      Submodule.span ℚ (Set.range v) = W.toSubmodule →
      BasisGradedSubmodule (D.filtration.associatedGradedBasis b ω hD) ω W.toSubmodule →
    ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → Fmark.GeometryComplexityLE p →
      (Fintype.card κ : ℝ) ≤ p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (c i) j) ≤ p) →
      (∀ i j, rationalLogHeight (Fmark.basis.repr (φ (D.basis i)) j) ≤ p) →
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis b ω hD).repr (v i) j) ≤ p) →
      MarkedRefilteredNativeDiagramData D Fmark φ hφ W ((p + C) ^ C) := by
  obtain ⟨A, _, hmodels⟩ := exists_adapted_single_refiltered_models
  obtain ⟨C, hC, hbudget⟩ := exists_markedRefilteredModelInput_budget A
  refine ⟨C, hC, ?_⟩
  intro L M κ _ _ _ _ _ s d f n k D Fmark b ω hD c ν hF φ hφ hsurj
    W v hspan hW p hp hDgeom hFgeom hκ hb hc hφheight hv
  obtain ⟨hq, hpq, hmapq, ht, hqt, himaget, hr, hpr, hmodelr⟩ :=
    markedRefilteredModelInput_bounds A hp
  obtain ⟨hrC, hmarkC⟩ := hbudget p hp
  have hpt := hpq.trans hqt
  have hmodelC := hmodelr.trans hrC
  have hbn : (Fintype.card (Fin n) : ℝ) ≤ p :=
    (D.basis_geometry_of_forward_height b hp hDgeom
      (fun i j => (hb i j).trans (by linarith))).1
  have hadapted (i : Fin n) (j : Fin k) :
      rationalLogHeight (c.repr (φ (b i)) j) ≤ markedRefilteredBasisInput p :=
    (D.markedMap_basisChange_logHeight Fmark b c φ.toLinearMap hp hDgeom hFgeom
      hb hc hφheight i j).trans hmapq
  let V := W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ)
  let imagev : κ → Fmark.filtration.AssociatedGraded := D.filtration.gradedImageSpanningFamily Fmark.filtration φ hφ v
  obtain ⟨himage, _, himageH⟩ :=
    D.filtration.gradedImage_bounded_spanning Fmark.filtration φ hφ
      b ω hD c ν hF W v hspan hW hq (hbn.trans hpq)
      (fun i j => (hv i j).trans hpq) hadapted
  obtain ⟨E, hEF, hEL, hEgeom, hEinc, m, hm, Q, hQF, hQL, hQgeom, hQmap⟩ :=
    hmodels D b ω hD W v hspan ht (hDgeom.mono D hpt) (hκ.trans hpt)
      (fun i j => (hb i j).trans hpt) (fun i j => (hv i j).trans hpt)
  have himageSpan : Submodule.span ℚ (Set.range imagev) = V.toSubmodule := by
    with_reducible exact himage
  have htarget := by
    with_reducible exact (hmodels (L := M) (κ := κ) (s := s) (d := f) (n := k) Fmark c ν hF V imagev himageSpan (p := markedRefilteredMapInput p) ht (hFgeom.mono Fmark hpt) (hκ.trans hpt) (fun i j => (hc i j).trans hpt) (fun i j => (himageH i j).trans himaget))
  obtain ⟨EF, hEFF, hEFL, hEFgeom, hEFinc, mf, hmf, QF, hQFF, hQFL, hQFgeom, hQFmap⟩ := htarget
  let mark := D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W
  have hmarked (i) (j) : rationalLogHeight (EF.basis.repr (mark (E.basis i)) j) ≤
      (p + C) ^ C := by
    apply (restrictedLieMap_coordinate_logHeight D.basis Fmark.basis
      (D.filtration.gradedRefiltrationSubalgebra W)
      (Fmark.filtration.gradedRefiltrationSubalgebra V) E.basis EF.basis φ
      (fun x hx => D.filtration.gradedRefiltrationLayer_map_mem Fmark.filtration φ hφ W 1 x hx)
      hr (by simpa only [Fintype.card_fin] using hDgeom.1.trans hpr)
      (by simpa only [Fintype.card_fin] using hFgeom.1.trans hpr)
      (by simpa only [Fintype.card_fin] using hEFgeom.1.trans hmodelr)
      (fun i j => (hφheight i j).trans hpr)
      (fun i j => (hEinc j i).trans hmodelr)
      (fun i j => (hEFinc j i).trans hmodelr) i j).trans hmarkC
  unfold MarkedRefilteredNativeDiagramData
  refine ⟨E, hEF, hEL, hEgeom.mono E hmodelC,
    fun i j => (hEinc i j).trans hmodelC,
    EF, hEFF, hEFL, hEFgeom.mono EF hmodelC,
    fun i j => (hEFinc i j).trans hmodelC, hmarked, ?_, ?_, ?_, ?_⟩
  · intro j x hx
    rw [hEF] at hx
    rw [hEFF]
    exact D.filtration.gradedRefiltrationMap_mem_layer Fmark.filtration φ hφ W j x hx
  · intro j y hy
    rw [hEFF] at hy
    obtain ⟨x, hx, heq⟩ := D.filtration.gradedRefiltrationMap_layer_surjective
      Fmark.filtration b ω hD c ν hF φ hφ W hW hsurj j y hy
    exact ⟨x, by rwa [hEF], heq⟩
  · exact ⟨m, hm, Q, hQF, hQL, hQgeom.mono Q hmodelC,
      fun i j => (hQmap i j).trans hmodelC⟩
  · exact ⟨mf, hmf, QF, hQFF, hQFL, hQFgeom.mono QF hmodelC,
      fun i j => (hQFmap i j).trans hmodelC⟩

end Erdos3.RationalFilteredNilmanifold


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativePairAffineCellStepDrop
namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*}

theorem pairOrbit_substitute_log {w : σ → ℕ} {v : τ → ℕ}
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) :
    (pairOrbit D E
      (D.filtration.realification.polynomialOrbitSubstitute f hf p)
      (E.filtration.realification.polynomialOrbitSubstitute f hf q)).log =
      VectorPolynomial.substitute f (pairOrbit D E p q).log := by
  simp only [pairOrbit, NilpotentLieFiltration.piRealOrbit,
    NilpotentLieFiltration.PolynomialOrbit.log, NilpotentLieFiltration.polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> exact VectorPolynomial.map_substitute f _ _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedAffineScaleEnvelope
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {α : Type*} [Fintype α] {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

 theorem AllocatedComparisonDimensions.active_tuples {D : ℝ}
    (hdim : AllocatedComparisonDimensions (G := G) B α O D)
    (partition : LayerSamplerAxis I n → Prop) :
    (Fintype.card (PrincipalTupleIndex (fun a : {a // ¬partition a} => B a.val)
      (fun a => layerSamplerDegree I n a.val)) : ℝ) ≤ D :=
  (Nat.cast_le.mpr (dependentAxis_card_restrict_le
    (fun a => B a × Fin (layerSamplerDegree I n a)) (fun a => ¬partition a))).trans hdim.tuples

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ForecastNativeResidueTest
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped Classical Matrix

variable {m : ℕ} {X : Type*} {I E : Fin m → Type*} {n : Fin m → ℕ}
variable (inactive : LayerSamplerAxis I n → Prop)

def forecastNativeFreeDeckResidue {R : Type*}
    (out : Sigma (AllocatedCongruenceRankOutput X E inactive) → R)
    (j : Fin m) (e : E j) : R := out ⟨j, .inr (.inl e)⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedExternalCandidatePrimitivePhysicalBudget
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

theorem exists_nativeMarkedFreezingPhysicalParameter_bound (Cfree : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ p : ℝ, 0 ≤ p →
      nativeMarkedFreezingPhysicalParameter p Cfree ≤ (p + A) ^ A := by
  let poly : Polynomial ℕ :=
    (Polynomial.X + 3) ^ 36 + (Polynomial.X + Polynomial.C Cfree) ^ Cfree
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget poly
  refine ⟨A, hA, ?_⟩
  intro p hp
  simpa [poly, nativeMarkedFreezingPhysicalParameter, Polynomial.eval₂_pow] using hbound p hp

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end


