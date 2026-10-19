-- Prove2me | Definitions.Def_OAIE3v2B182
-- name    : OAIE3v2B182
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:53:24.122992+00:00
-- url     : https://prove2.me/theorems/c614e7e4-5fa4-451a-880b-9768b23a4f66
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 185 of 311
-- statement:
--   Definitions bundle 185 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B161`, `OAIE3v2B162`, `OAIE3v2B164`, `OAIE3v2B165`, `OAIE3v2B166`, `OAIE3v2B167` of this split.
--
--   Modules: `Dynamics/CompatibleReducedFastReset.lean`, `Estimates/BiasedSynchronizedSquareFamily.lean`, `Estimates/CommonFixedNativeSquareFamily.lean`, `Estimates/CommonNativeSquareFactors.lean`, `Estimates/FastHorizontalFactorization.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/ReducedRelativeCoefficientBounds.lean`, `Estimates/ReindexSymbolFactorization.lean`, `Estimates/SourceUnitCover.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Geometry/FullFastCoefficientCoordinates.lean`, `Geometry/SquareQuotientHeightTransport.lean`, `Nilpotent/NativeSquareNiltest.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B161
import Definitions.Def_OAIE3v2B162
import Definitions.Def_OAIE3v2B164
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B166
import Definitions.Def_OAIE3v2B167

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ReducedFastResetSpec s a C := by
  have hresetExists := exists_controlled_reduced_fast_reset s a
  obtain ⟨c, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := 3 * (Polynomial.X + Polynomial.C (s + 2)) ^ (s + 2) *
    (Polynomial.X + 1) + 2 * Polynomial.X + 2
  let B := (Q + Polynomial.C c) ^ c
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let : Finite (ReducedSquareSymbolIndex s w ω) := F.reducedSquareSymbolIndex_finite e ω hF w hw
  let : Fintype (ReducedSquareSymbolIndex s w ω) := Fintype.ofFinite _
  let : Finite (QuotientTopSymbolIndex s w ω) := F.quotientTopSymbolIndex_finite e ω hF w hw
  let : Fintype (QuotientTopSymbolIndex s w ω) := Fintype.ofFinite _
  let q := reducedMatrixParameter s p
  have hq : 0 ≤ q := reducedMatrixParameter_nonneg s hp
  have hpq : p ≤ q := le_reducedMatrixParameter s hp
  have hdims := F.reduced_lift_matrix_dimensions e ω hF w hw hp hι hσ hκ
  have hfinal : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [B, Q, q, reducedMatrixParameter, Polynomial.eval₂_pow] using hbound p hp
  have hrawExists := hreset F e ω hF w hw U v hspan hU H l q hH hl hq
    hdims.1 (hσ.trans hpq) hdims.2.1 hdims.2.2 (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hlp.trans (Real.exp_le_exp.mpr hpq)) hc hv
  obtain ⟨S, m, hm, hmp, hlm, hraw⟩ := hrawExists
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hfinal), hlm, ?_⟩
  intro T hT E P R A D hP hleft hright hE hR hLeftSlow hRightRat
  have hinput : Real.exp ((p + 2) ^ a) ≤ Real.exp ((q + 2) ^ a) :=
    Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) (by linarith) a)
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT hinput E hE
  have hLeftSlow' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hT hinput _ hLeftSlow
  have hresult := hraw T hT E P R A D hP hleft hright hE' hR hLeftSlow' hRightRat
  obtain ⟨hprod, hfast, hA, hD, hmid, hslow, hgrid⟩ := hresult
  refine ⟨hprod, hfast, hA, hD, hmid, ?_, hgrid⟩
  exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hT
    (Real.exp_le_exp.mpr hfinal) _ hslow

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_compatible_reduced_fast_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CompatibleReducedFastResetSpec s a C := by
  have hcomparisonExists := exists_reduced_projected_comparison s a
  obtain ⟨cc, _, hcomparison⟩ := hcomparisonExists
  have hresetExists := exists_reduced_fast_reset s 1
  obtain ⟨cr, _, hreset⟩ := hresetExists
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C cc) ^ cc +
    (Q + Polynomial.C cr) ^ cr
  have hboundExists := exists_natPolynomial_eval_budget B
  obtain ⟨C, hC, hbound⟩ := hboundExists
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F e ω hF w hw U v hspan hU H l p hH hl hp hι hσ hκ hHp hlp hc hv
  let q := (p + cc) ^ cc + (p + 2) ^ a + p + 2
  have hc0 : 0 ≤ (p + cc) ^ cc := by positivity
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hcq : (p + cc) ^ cc ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hsum : (p + cc) ^ cc + (q + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hr0 : 0 ≤ (q + cr) ^ cr := by positivity
  have hcb : (p + cc) ^ cc ≤ (p + C) ^ C := (le_add_of_nonneg_right hr0).trans hsum
  have hrb : (q + cr) ^ cr ≤ (p + C) ^ C := (le_add_of_nonneg_left hc0).trans hsum
  have hcompdata := hcomparison F e ω hF w hw U v hspan H l p hH hl hp hι hσ hκ hHp hlp hc hv
  obtain ⟨n, hn, hnp, hln, hcompare⟩ := hcompdata
  have hresetdata := hreset F e ω hF w hw U v hspan hU H n q hH hn hq
    (hι.trans hpq) (hσ.trans hpq) (hκ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq))
    (hnp.trans (Real.exp_le_exp.mpr hcq)) hc hv
  obtain ⟨S, m, hm, hmp, hnm, hresetFactors⟩ := hresetdata
  refine ⟨S, m, hm, hmp.trans (Real.exp_le_exp.mpr hrb), hln.trans hnm, ?_⟩
  intro T hT E P R A B D hP hB heq hE hR hA hD
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hcomp := hcompare T (fun i => (Real.exp_le_exp.mpr hcb).trans (hT i))
    E P R A B D hP hB heq hE hA hR hD
  have hE' := F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hTpos
    (Real.exp_le_exp.mpr haq) E hE
  have hA' := F.quotientTop.symbolSlowBound_mono (F.quotientTopBasis e ω hF)
    (fun i => ω i.val) (F.quotientTopBasis_layers e ω hF) w T hTpos
    (Real.exp_le_exp.mpr (hcq.trans
      (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 2)))) _ hcomp.2.2.1
  have hR' := F.squareFiltration.quotientTop.symbolRationalGrid_mono (F.reducedSquareBasis e ω hF)
    (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w hl hln R hR
  have hresult := hresetFactors T hTpos E P R A D hP hcomp.1 hcomp.2.1
    (by simpa only [pow_one] using hE') hR' (by simpa only [pow_one] using hA') hcomp.2.2.2
  refine ⟨hresult.1, hresult.2.1, hresult.2.2.1, hresult.2.2.2.1, ?_, ?_, hresult.2.2.2.2.2.2⟩
  · rw [hresult.2.2.2.2.1, ← heq]
    group
  · exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis e ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF) w T hTpos
      (Real.exp_le_exp.mpr hrb) _ hresult.2.2.2.2.2.1

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReducedRelativeCoefficientBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))

theorem realFastCoefficientAction_horizontal {ι : Type*}
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (g : F.realFastDiagonalSubgroup w U) (x : F.RealFastCoefficientModule w hw U) :
    F.realFastCoefficientHorizontal w hw (F.reducedSquareFastRelativeSubmodule w U)
      (F.realFastCoefficientAction w hw U g x) =
      F.realFastCoefficientHorizontal w hw (F.reducedSquareFastRelativeSubmodule w U) x := by
  obtain ⟨x, rfl⟩ := (F.realFirstCoefficientFastSubmodule w hw
    (F.reducedSquareFastRelativeSubmodule w U)).mkQ_surjective x
  rw [F.realFastCoefficientAction_mk]
  exact F.realFirstCoefficientHorizontal_adjoint e ω hF w g.val x

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SourceUnitCover
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

namespace NativeMultidegreeNilcharacter

variable {σ : Type*} [Fintype σ] {bound : σ → ℕ} {p q : ℝ}
  (W : NativeMultidegreeNilcharacter bound p)

theorem unit_eval (x : σ → ℤ) : ∑ i, ‖W.eval i x‖ ^ 2 = 1 := W.vertical.unit _

end NativeMultidegreeNilcharacter

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct NNReal

variable {L σ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem exists_uniform_square_niltest_with_budget {w : σ → ℕ} (T : D.Niltest w)
    {p : ℝ} (hp : 0 ≤ p) (hT : T.ComplexityLE p) (a b c : ℕ)
    (hrec : ∀ (m n H : ℕ) (ℓ B : ℝ≥0) (r : ℝ),
      0 ≤ r → (m : ℝ) ≤ r → (n : ℝ) ≤ r → (H : ℝ) ≤ Real.exp r →
      (ℓ : ℝ) ≤ Real.exp r → (B : ℝ) ≤ Real.exp r →
      (rationalReconstructionLipschitzBound s m n H ℓ B : ℝ) ≤ Real.exp ((r + c) ^ c)) :
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout
      Q.GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (ε : D.RealGroup) (q : D.filtration.squareFiltration.realification.PolynomialOrbit w)
        (χ : D.RealGroup → CircleFourier.Circle),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ (A : ℝ≥0), (A : ℝ) ≤ Real.exp (normalizedSquareLeftBudget a b p) →
        (letI := D.metricSpace; LipschitzWith A (fun x : D.Space => ε • x)) →
      ∃ S : Q.Niltest w,
        S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl q ∧
        (∀ z : D.filtration.squareFiltration.realification.Group,
          S.observable (QuotientGroup.mk (D.filtration.squareFiltration.realQuotientStepHom
            (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl z)) =
            D.filtration.realSquareObservable D.lattice ε T.observable (QuotientGroup.mk z)) ∧
        S.normBound = T.normBound ^ 2 ∧
        S.ComplexityLE (normalizedSquareComplexityBudget a b c p) ∧
        ∀ x : σ → ℤ, S.eval x = D.filtration.realSquareObservable D.lattice ε T.observable
          (QuotientGroup.mk (D.filtration.squareFiltration.realification.polynomialOrbitEval w x q)) := by
  obtain ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeom, hgeomQ⟩ :=
    D.exists_controlled_reduced_square_geometry hp hT.1
  let m := Fintype.card (Fin (finrank ℚ L) ⊕ {i // 2 ≤ v₀ i})
  let bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra := D.filtration.squareFinBasis b₀ v₀ (hlayers 2)
  let v : Fin m → ℕ := squareFinWeight v₀
  have hls := D.filtration.squareFinBasis_layers b₀ v₀ hlayers
  let Q := D.filtration.squareFiltration.topQuotientModel bs v hls
    (D.filtration.squareLattice D.lattice) N hN hin hout
  refine ⟨b₀, v₀, hlayers, N, hN, hin, hout, hb₀, hgeomQ, ?_⟩
  intro ε q χ hvert A hA hALip
  have hQ : Q.GeometryComplexityLE (squareGeometryBudget p) := hgeomQ
  have hm : (m : ℝ) ≤ squareGeometryBudget p := hgeom.1
  have hQ0 := squareGeometryBudget_nonneg hp
  have hObs0 := normalizedSquareObservableBudget_nonneg a b hp
  have hB : (T.normBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.lipBound.coe_nonneg]
  have hK : (T.lipBound : ℝ) ≤ Real.exp p := by
    have hh := T.observable_budget hT
    linarith [T.normBound.coe_nonneg]
  let Hproj := ⌈Real.exp (p + 1)⌉₊
  have hproj := D.filtration.squareFinBasis_projection_height D.basis b₀ v₀ (hlayers 2)
    (one_le_ceil_exp (p + 1)) (fun i j => rationalHeightLE_ceil_exp (hb₀ j i))
  let P := coordinateLipschitzBound (Fintype.card (Fin d)) (Fintype.card (Fin m)) Hproj
  have hP : (P : ℝ) ≤ Real.exp (normalizedSquareProjectionBudget p) := by
    have heq : normalizedSquareProjectionBudget p = (squareGeometryBudget p + p + 2 + 2) ^ 2 := by
      unfold normalizedSquareProjectionBudget
      ring
    rw [heq]
    apply coordinateLipschitzBound_le_exp _ _ Hproj
      (show 0 ≤ squareGeometryBudget p + p + 2 by linarith)
    · simpa only [Fintype.card_fin] using hT.1.1.trans (by linarith : p ≤ squareGeometryBudget p + p + 2)
    · simpa only [Fintype.card_fin] using hm.trans (by linarith : squareGeometryBudget p ≤ squareGeometryBudget p + p + 2)
    · exact (ceil_exp_le_exp_add_one (by linarith : 0 ≤ p + 1)).trans
        (Real.exp_le_exp.mpr (by linarith))
  let ℓ := T.normBound * (T.lipBound * P) + T.normBound * (T.lipBound * (A * P))
  have hℓLip : letI := realificationQuotientMetricSpace bs (D.filtration.squareLattice D.lattice) N hN hout
      LipschitzWith ℓ (D.filtration.realSquareObservable D.lattice ε T.observable) :=
    D.filtration.realSquareObservable_lipschitz D.basis bs D.lattice D.grid N Hproj D.grid_pos hN
      D.outer_grid hout (fun k i => (hproj i k).1) (fun k i => (hproj i k).2)
      ε T.observable A T.lipBound T.normBound hALip T.lipschitz T.norm_le
  have hℓ : (ℓ : ℝ) ≤ Real.exp (normalizedSquareObservableBudget a b p) :=
    squareObservableLipschitz_le_exp A T.normBound T.lipBound P
      (normalizedSquareLeftBudget_nonneg a b hp) hA hB hK hP
  let H := ⌈Real.exp (squareGeometryBudget p)⌉₊
  have he (i j) : RationalHeightLE (Q.basis.repr
      (lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1)) (bs j)) i) H := by
    exact (quotientFinBasis_projection_height bs
      (D.filtration.squareFiltration.layerIdeal (s + 1)) {i | s + 1 ≤ v i}
      (hls (s + 1)) j i).mono (one_le_ceil_exp _)
  obtain ⟨S, hOrbit, hObs, hSB, hSK, hSval⟩ := D.filtration.exists_square_quotient_niltest_with_orbit D.lattice
    bs v hls N hN hin hout w q ε T.observable χ hvert ℓ T.normBound hℓLip T.norm_le
    H (one_le_ceil_exp _) he (fun i j k => rationalHeightLE_ceil_exp (hQ.2.2.1 i j k))
  let r := normalizedSquareReconstructionBudget a b p
  have hr : 0 ≤ r := normalizedSquareReconstructionBudget_nonneg a b hp
  have hQr : squareGeometryBudget p + 1 ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hUr : normalizedSquareObservableBudget a b p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hpr : 2 * p ≤ r := by dsimp [r, normalizedSquareReconstructionBudget]; linarith
  have hB2 : (((T.normBound ^ 2 : ℝ≥0) : ℝ)) ≤ Real.exp (2 * p) := by
    rw [NNReal.coe_pow]
    calc
      _ ≤ (Real.exp p) ^ 2 := pow_le_pow_left₀ T.normBound.coe_nonneg hB 2
      _ = _ := by rw [← Real.exp_nat_mul]; norm_num
  have hSKBound : (S.lipBound : ℝ) ≤ Real.exp ((r + c) ^ c) := by
    rw [hSK]
    apply hrec _ _ H ℓ (T.normBound ^ 2) r hr
    · exact hm.trans (by linarith)
    · exact hQ.1.trans (by linarith)
    · exact (ceil_exp_le_exp_add_one hQ0).trans (Real.exp_le_exp.mpr hQr)
    · exact hℓ.trans (Real.exp_le_exp.mpr hUr)
    · exact hB2.trans (Real.exp_le_exp.mpr hpr)
  have hSBBound : (S.normBound : ℝ) ≤ Real.exp (2 * p) := by rw [hSB]; exact hB2
  have hlog := niltest_log_bound_of_exp S.normBound S.lipBound
    (by linarith : 0 ≤ 2 * p) (by positivity : 0 ≤ (r + c) ^ c) hSBBound hSKBound
  refine ⟨S, hOrbit, hObs, hSB, ?_, hSval⟩
  constructor
  · apply hQ.mono
    change squareGeometryBudget p ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    have hpow : 0 ≤ (r + c) ^ c := by positivity
    linarith
  · apply hlog.trans
    change 2 * p + (r + c) ^ c + 4 ≤ squareGeometryBudget p + 2 * p + (r + c) ^ c + 4
    linarith

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  (D : RationalFilteredNilmanifold L (s + 1) d)
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

omit [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] in
theorem HasNativeBiasedSquareInModel.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {A : Finset (σ → ℤ)} {h : σ → ℤ} {p q : ℝ}
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h p) (hpq : p ≤ q) :
    D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η A h q := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative,
    ξ, V, hOrbit, hV, hheight, hchar, hint, hrestriction, hbias⟩ := hdata
  exact ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)),
    r, hf, hsecond, hderivative, ξ, V, hOrbit,
    hV.mono hpq, (fun i => (hheight i).trans hpq), hchar, hint, hrestriction,
    (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans hbias⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct BigOperators

namespace RationalFilteredNilmanifold

universe uσ uL

variable {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)

variable {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

variable [DecidableEq σ]
  [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]
  [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
    D.filtration.squareFiltration.layerIdeal (s + 1)))]

theorem HasNativeBiasedSquareInModel.factorization {c : ℕ}
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {origin h : σ → ℤ} {lengths : σ → ℕ} {p : ℝ}
    (hp : 0 ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p) (hlengths : ∀ i, 0 < lengths i)
    (hlarge : ∀ i, Real.exp ((p + c) ^ c) ≤ (lengths i : ℝ))
    (hdata : D.HasNativeBiasedSquareInModel bs v hls N hN hin hout hs g η
      (translatedIntegerBox origin lengths) h p) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h p ((p + c) ^ c) := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative,
    ξ, V, hOrbit, hV, hheight, hchar, _, hrestriction, hbias⟩ := hdata
  have hfactor := hI Q (quotientFinWeight v {i | s + 1 ≤ v i}) hQ p hp hσ V hV ξ hheight hchar
    origin lengths hlengths hlarge hbias
  have hsymbol : V.symbol (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ =
      D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r := by
    have he := congrArg (fun a : (Q).filtration.realification.PolynomialOrbit (fun _ : σ => 1) =>
      (Q).filtration.realPolynomialSymbolHom (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i})
        hQ (fun _ => 1) ⟨⟨a.log, a.property⟩⟩) hOrbit
    exact he.trans (D.filtration.squareFiltration.nativeReducedPolynomialOrbit_symbol
      (fun _ => 1) (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ r)
  rw [hsymbol] at hfactor
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

theorem HasNativeFactoredSquareInModel.exists_fixed {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) → (Q).filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
        (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ).repr
          (u i) j) ≤ p) ∧
      D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  obtain ⟨l, W, u, hl, hlp, hu, hW, hcoordinates, hη, hfixed⟩ :=
    ControlledSymbolFactorization.exists_in (Q).filtration (Q).basis
      (quotientFinWeight v {i | s + 1 ≤ v i}) hQ hfactor
  refine ⟨l, W, u, hl, hlp, hu, hW, hcoordinates, ?_⟩
  exact ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hη, hfixed⟩

theorem HasFixedNativeSquareFactors.mono {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p q : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W)
    (hpq : p ≤ q) (hS : ∀ i, 0 < S i) :
    D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h q l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hη, hfixed⟩ := hdata
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpq)), r,
    hf, hsecond, hderivative, ξ, (fun i => (hheight i).trans hpq), hrestriction, hη, ?_⟩
  exact SymbolFactorizationIn.mono (Q).filtration (Q).basis
    (quotientFinWeight v {i | s + 1 ≤ v i}) hQ hfixed hpq hS

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d)
  {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
  (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers bs v hls
  (D.filtration.squareLattice D.lattice) N hN hin hout

theorem exists_common_native_square_factors (hs : 1 ≤ s)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (η : L →ₗ[ℚ] ℚ) (S : σ → ℝ) (H : Finset (σ → ℤ)) (hH : H.Nonempty)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i} : ℝ) ≤ p)
    (hdata : ∀ h ∈ H, D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) → (Q).filtration.AssociatedGraded)
      (H' : Finset (σ → ℤ)),
      H' ⊆ H ∧ H'.Nonempty ∧
      Real.exp (-((p + 2) ^ 5 + p)) * H.card ≤ (H'.card : ℝ) ∧
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧
      Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule
        ((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ)
        (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight
        (((Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ).repr
          (u i) j) ≤ p) ∧
      ∀ h ∈ H', D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W := by
  classical
  let J := Fin (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i})
  let bG := (Q).filtration.associatedGradedBasis (Q).basis (quotientFinWeight v {i | s + 1 ≤ v i}) hQ
  obtain ⟨h₀, hh₀⟩ := hH
  have htags : ∀ h : σ → ℤ, ∃ (l : ℕ) (W : LieSubalgebra ℚ (Q).filtration.AssociatedGraded)
      (u : J → (Q).filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule bG (quotientFinWeight v {i | s + 1 ≤ v i}) W.toSubmodule ∧
      (∀ i j, rationalLogHeight (bG.repr (u i) j) ≤ p) ∧
      (h ∈ H → D.HasFixedNativeSquareFactors bs v hls N hN hin hout hs g η S h p l W) := by
    intro h
    by_cases hh : h ∈ H
    · obtain ⟨l, W, u, hl, hlp, hu, hW, hhgt, hfixed⟩ :=
        HasNativeFactoredSquareInModel.exists_fixed D bs v hls N hN hin hout (hdata h hh)
      exact ⟨l, W, u, hl, hlp, hu, hW, hhgt, fun _ => hfixed⟩
    · obtain ⟨l, W, u, hl, hlp, hu, hW, hhgt, _⟩ :=
        HasNativeFactoredSquareInModel.exists_fixed D bs v hls N hN hin hout (hdata h₀ hh₀)
      exact ⟨l, W, u, hl, hlp, hu, hW, hhgt, fun he => False.elim (hh he)⟩
  choose l W u hl hlp hu hW hhgt hfixed using htags
  have hdim : (Fintype.card J : ℝ) ≤ p := by simpa only [J, Fintype.card_fin] using hd
  obtain ⟨a₀, _, H', hsub, ha, hsame, hlarge⟩ :=
    exists_common_fast_subalgebra_and_denominator bG H ⟨h₀, hh₀⟩ W l
      (Fintype.card {i : Fin m // ¬ s + 1 ≤ v i}) hp hd hdim
      (fun h _ => ⟨u h, hu h, hhgt h⟩) (fun h _ => ⟨hl h, hlp h⟩)
  refine ⟨l a₀, W a₀, u a₀, H', hsub, ⟨a₀, ha⟩, hlarge,
    hl a₀, hlp a₀, hu a₀, hW a₀, hhgt a₀, ?_⟩
  intro h hh
  simpa only [(hsame h hh).1, (hsame h hh).2] using hfixed h (hsub hh)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFixedNativeSquareFamily
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def UniformNativeBiasedSquareSpec (s C : ℕ) : Prop :=
  ∀ (hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L (s + 1) d)
    [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
      D.filtration.squareFiltration.layerIdeal (s + 1)))]
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (h : σ → ℤ) (A : Finset (σ → ℤ)), A.Nonempty →
        Real.exp (-(2 * p + 1)) ≤ ‖𝔼 x ∈ A, T.eval (x + h) * star (T.eval x)‖ →
        D.HasNativeBiasedSquareInModel
          (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η A h ((p + C) ^ C)

theorem exists_uniform_native_biased_square (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ UniformNativeBiasedSquareSpec.{uσ, uL} s C := by
  obtain ⟨a, _, hnorm⟩ := exists_native_normalized_square.{uσ, 0, uL} s
  obtain ⟨b, _, hleft⟩ := exists_bounded_normalization_left_lipschitz (s + 1) a
  obtain ⟨c, _, hrec⟩ := exists_rationalReconstructionLipschitzBound_exp s
  obtain ⟨d, _, hbudget⟩ := exists_normalizedSquareComplexityBudget_bound a b c
  obtain ⟨v, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  let R : Polynomial ℕ := (Polynomial.X + Polynomial.C d) ^ d +
    (Polynomial.X + 1 + Polynomial.C a) ^ a + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := R + (R + Polynomial.C v) ^ v + 2 * Polynomial.X + 2
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ n _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let q := (p + d) ^ d + (p + 1 + a) ^ a + 2 * p + 2
  have hd0 : 0 ≤ (p + d) ^ d := by positivity
  have ha0 : 0 ≤ (p + 1 + a) ^ a := by positivity
  have hdq : (p + d) ^ d ≤ q := by dsimp [q]; linarith
  have haq : (p + 1 + a) ^ a ≤ q := by dsimp [q]; linarith
  have hpq : 2 * p + 2 ≤ q := by dsimp [q]; linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hv := hvertical q hq
  have hpow : 0 ≤ (q + v) ^ v := by positivity
  have hfinal' : q + (q + v) ^ v + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [P, R, q, Polynomial.eval₂_pow] using hfinal p hp
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hvC : verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  have hbC : 2 * p + 2 + verticalDecompositionBudget q ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ :=
    D.exists_uniform_square_niltest_with_budget T hp hT a b c hrec
  obtain ⟨A₀, _, hA₀, hLip⟩ := hleft D p hp hT.1
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert h A hA hbias
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative⟩ :=
    hnorm D e ω hF p hp hT.1 (fun i => (h i : ℚ)) g
  let qr := D.filtration.squareFiltration.nativePolynomialOrbit (fun _ : σ => 1) r
  obtain ⟨S, hOrbit, hObs, _, hS, hSval⟩ := hconstruct ε qr
    (fun z => ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle))
    hvert A₀ hA₀ (hLip ε hε)
  have hEval (x : σ → ℤ) : S.eval x = T.eval (x + h) * star (T.eval x) := by
    apply (hSval x).trans
    have hprod := D.filtration.nativeNormalizedSquareObservable_product (fun _ => 1)
      D.lattice h ε γ hγ T.observable g r hf hsecond x
    rw [hg] at hprod
    exact hprod
  have herror : (Real.exp (-(2 * p + 1)) / 2)⁻¹ ≤ Real.exp q := by
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ = 2 * Real.exp (2 * p + 1) := by rw [inv_div, Real.exp_neg, div_inv_eq_mul]
      _ ≤ Real.exp 1 * Real.exp (2 * p + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (2 * p + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr hpq
  have hc : Real.exp (-(2 * p + 1)) ≤ ‖finiteCorrelation A (fun _ => 1) S.eval‖ := by
    rw [norm_finiteCorrelation_one]
    have hmean : (𝔼 x ∈ A, S.eval x) = 𝔼 x ∈ A, T.eval (x + h) * star (T.eval x) :=
      Finset.expect_congr rfl (fun x _ => hEval x)
    rw [hmean]
    exact hbias
  obtain ⟨ξ, V, hV, hVO, hheight, hchar, hint, hrestriction, hCorr⟩ :=
    D.filtration.exists_correlating_square_vertical_mode D.lattice
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hs (fun _ : σ => 1) ε η T.observable hvert r S hOrbit hObs hq
      (hS.mono ((hbudget p hp).trans hdq)) (Real.exp_pos _) herror hA
      (fun _ => 1) (fun _ _ => by norm_num) hc
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr (haq.trans hqC))),
    r, hf, hsecond, ?_, ξ, V, hVO, hV.mono hqC,
    (fun i => (hheight i).trans hvC), hchar, hint, hrestriction, ?_⟩
  · simpa only [Rat.cast_intCast] using hderivative
  · rw [norm_finiteCorrelation_one] at hCorr
    apply le_trans _ hCorr
    calc
      _ ≤ Real.exp ((-(2 * p + 1) - verticalDecompositionBudget q) - 1) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ ≤ Real.exp (-(2 * p + 1) - verticalDecompositionBudget q) / 2 := exp_sub_one_le_half_exp _
      _ = _ := by rw [Real.exp_sub]; ring

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

theorem exists_common_native_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hsingle⟩ := exists_uniform_native_biased_square.{uσ, uL} s
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a + 5 * Polynomial.X + 6
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ n _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  have hbound : (p + a) ^ a + 5 * p + 6 ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have haC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  have h5 : 5 * p + 6 ≤ (p + C) ^ C := by linarith
  have h4 : 4 * p + 6 ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hsingle hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert origin lengths hlengths hσ hbias
  obtain ⟨H, hH, hcount, hgood⟩ := exists_many_biased_box_shifts origin lengths hlengths T.eval hp hσ
    (fun x _ => T.eval_budget hT x) hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h4))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hmean⟩ := hgood h hh
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg h5))
        (Nat.cast_nonneg (lengths i))).trans_lt (hsides i)
    · have hA : (derivativeSupport (translatedIntegerBox origin lengths) h).Nonempty := by
        by_contra hn
        rw [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.expect_empty, norm_zero] at hmean
        exact (not_le_of_gt (Real.exp_pos _)) hmean
      exact RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        (hconstruct g hg η hvert h (derivativeSupport (translatedIntegerBox origin lengths) h) hA hmean) haC

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

namespace RationalFilteredNilmanifold

theorem HasNativeFactoredSquareInModel.mono
    {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    {hs : 1 ≤ s} {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S : σ → ℝ} {h : σ → ℤ} {p q p' q' : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p q)
    (hpp : p ≤ p') (hqq : q ≤ q') (hS : ∀ i, 0 < S i) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p' q' := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  refine ⟨ε, γ, hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hpp)), r,
    hf, hsecond, hderivative, ξ, (fun i => (hheight i).trans hpp), hrestriction, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.mono _ _ _ _ hfactor hqq hS

theorem HasNativeFactoredSquareInModel.rescale
    {σ : Type uσ} {L : Type uL} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L (s + 1) d)
    {m : ℕ} (bs : Basis (Fin m) ℚ D.filtration.squareLieSubalgebra) (v : Fin m → ℕ)
    (hls : ∀ j, D.filtration.squareFiltration.layer j = Submodule.span ℚ (bs '' {i | j ≤ v i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates bs (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    {hs : 1 ≤ s} {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ} {h : σ → ℤ} {p q r : ℝ}
    (hdata : D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η S h p q)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hr : 0 ≤ r) (hST : ∀ i, Real.exp (-r) * T i ≤ S i) :
    D.HasNativeFactoredSquareInModel bs v hls N hN hin hout hs g η T h p (q + (s : ℝ) * r) := by
  obtain ⟨ε, γ, hγ, hε, a, hf, hsecond, hderivative, ξ, hheight, hrestriction, hfactor⟩ := hdata
  refine ⟨ε, γ, hγ, hε, a, hf, hsecond, hderivative, ξ, hheight, hrestriction, ?_⟩
  exact NilpotentLieFiltration.ControlledSymbolFactorization.rescale _ _ _ _ hfactor hS hT hr hST

end RationalFilteredNilmanifold

theorem exists_inductive_native_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ InductiveNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, ha, hfamily⟩ := exists_common_native_square_family.{uσ, uL} s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let P : Polynomial ℕ := B + ((B + Polynomial.C c) ^ c + Polynomial.C s * B)
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let q : ℝ := (p + a) ^ a
  let r : ℝ := (q + c) ^ c
  let t : ℝ := r + (s : ℝ) * q
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbound : q + t ≤ (p + C) ^ C := by
    simpa [P, B, q, r, t, Polynomial.eval₂_pow] using hfinal p hp
  have hqC : q ≤ (p + C) ^ C := (le_add_of_nonneg_right ht).trans hbound
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_left hq).trans hbound
  have hqr : q + r ≤ (p + C) ^ C := by
    have hrt : r ≤ t := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hq)
    exact (add_le_add (le_refl q) hrt).trans hbound
  have hpq : p ≤ q := by
    have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
    apply (show p ≤ p + a by linarith).trans
    exact (pow_one (p + a)).symm.le.trans
      (pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + a) (by omega : 1 ≤ a))
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hfamily hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hg η hvert origin lengths hlengths hσ hlarge hbias
  obtain ⟨H, hH, hcount, hgood⟩ := hconstruct g hg η hvert origin lengths hlengths hσ hbias
  refine ⟨H, hH, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · intro h hh
    obtain ⟨hbox, hsides, hdata⟩ := hgood h hh
    have hlargeOverlap : ∀ i, Real.exp r ≤ (((lengths i : ℤ) - |h i|).toNat : ℝ) := by
      intro i
      have hsize : Real.exp (q + r) ≤ (lengths i : ℝ) :=
        (Real.exp_le_exp.mpr hqr).trans (hlarge i)
      have heq : Real.exp r = Real.exp (-q) * Real.exp (q + r) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [heq]
      exact (mul_le_mul_of_nonneg_left hsize (Real.exp_pos _).le).trans (hsides i).le
    have hpos : ∀ i, 0 < ((lengths i : ℤ) - |h i|).toNat := by
      intro i
      have hposR := (Real.exp_pos r).trans_le (hlargeOverlap i)
      exact_mod_cast hposR
    rw [derivativeSupport_translatedIntegerBox] at hdata
    have hfactor := RationalFilteredNilmanifold.HasNativeBiasedSquareInModel.factorization D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hI hq (hσ.trans hpq) hpos hlargeOverlap hdata
    have hscaled := RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.rescale D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hfactor
      (fun i => by exact_mod_cast hpos i) (fun i => by exact_mod_cast hlengths i)
      hq (fun i => (hsides i).le)
    refine ⟨hbox, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
        (Nat.cast_nonneg (lengths i))).trans_lt (hsides i)
    · exact RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        hscaled hqC htC (fun i => by exact_mod_cast hlengths i)

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

theorem exists_common_fixed_native_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ CommonFixedNativeSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_inductive_native_square_family s c hI
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + G
  let P : Polynomial ℕ := B + ((Q + 2) ^ 5 + Q) + Q
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let b : ℝ := (p + a) ^ a
  let q : ℝ := b + squareGeometryBudget p
  let k : ℝ := (q + 2) ^ 5 + q
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hg := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := add_nonneg hb hg
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbound : b + k + q ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, b, q, k, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hbC : b ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hbkC : b + k ≤ (p + C) ^ C := by linarith
  have hbq : b ≤ q := le_add_of_nonneg_right hg
  have hgq : squareGeometryBudget p ≤ q := le_add_of_nonneg_left hb
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, hconstruct⟩ := hfamily hs D p hp T hT
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeom, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨H, hH, hcount, hgood⟩ := hconstruct g hgOrbit η hvert origin lengths hlengths hσ
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) hbias
  have hdata : ∀ h ∈ H, D.HasNativeFactoredSquareInModel
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h q q := by
    intro h hh
    exact RationalFilteredNilmanifold.HasNativeFactoredSquareInModel.mono D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      (hgood h hh).2.2 hbq hbq hTpos
  obtain ⟨l, W, u, H', hsub, hH', hlarge', hl, hlq, hu, hW, hheight, hfixed⟩ :=
    D.exists_common_native_square_factors
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      hs g η (fun i => (lengths i : ℝ)) H hH hq (hgeom.1.trans hgq) hdata
  refine ⟨H', l, W, u, hH', ?_, hl, hlq.trans (Real.exp_le_exp.mpr hqC), hu, hW,
    ?_, ?_⟩
  · calc
      Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤
          Real.exp (-(b + k)) * (∏ i, (lengths i : ℝ)) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbkC))
          (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))
      _ = Real.exp (-k) * (Real.exp (-b) * (∏ i, (lengths i : ℝ))) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-k) * H.card := mul_le_mul_of_nonneg_left hcount (Real.exp_pos _).le
      _ ≤ H'.card := hlarge'
  · intro i j
    exact (hheight i j).trans hqC
  · intro h hh
    have hprior := hgood h (hsub hh)
    refine ⟨hprior.1, ?_, ?_⟩
    · intro i
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hbC))
        (Nat.cast_nonneg (lengths i))).trans_lt (hprior.2.1 i)
    · exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono D
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
        (hfixed h hh) hqC hTpos

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastHorizontalFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))
  (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol (fun _ : σ => 1)))

variable {ι : Type*} (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

include e ω hF

theorem realFastCoefficientDirectionMap_mul
    (g h : F.realFastDiagonalSubgroup (fun _ : σ => 1) U) (v : σ → ℝ) :
    F.realFastCoefficientDirectionMap U (g * h).val v =
      F.realFastCoefficientDirectionMap U g.val v +
        F.realFastCoefficientAction (fun _ => 1) (fun _ => Nat.zero_lt_one) U g
          (F.realFastCoefficientDirectionMap U h.val v) := by
  change (F.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
    (F.reducedSquareFastRelativeSubmodule (fun _ => 1) U)).mkQ
      (F.realFirstCoefficientDirectionMap (g.val * h.val).coord v) = _
  rw [F.realFirstCoefficientDirectionMap_mul e ω hF, map_add]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1))

variable (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "ωQ" => (fun i : QuotientTopBasisIndex s ω => ω (Subtype.val i))

theorem fastPointwiseDiagonal_eq [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W) =
      F.quotientTop.symbolPointwiseSubalgebra (F.quotientTopBasis e ω hF) ωQ
        (F.quotientTopBasis_layers e ω hF) w (F.fastGradedDiagonal W) := by
  let : Fintype (SymbolBasisIndex w ωQ) := symbolBasisIndexFintype w ωQ s hw
    (F.quotientTop.adaptedBasis_weight_le_step (F.quotientTopBasis e ω hF) ωQ
      (F.quotientTopBasis_layers e ω hF))
  exact F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_map F.quotientTop
    (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    F.reducedSquareSnd F.reducedSquareSnd_mem w W hW

theorem fullFastPointwise_eq_comap [Fintype σ] [Fintype ι] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule) :
    F.symbolPointwiseSubalgebra e ω hF w (F.fullFastGradedDiagonal W) =
      (F.reducedSquareFastDiagonalSubalgebra w (F.fastPointwiseSquare e ω hF w W)).comap
        (F.quotientTopSymbolMap w) := by
  rw [F.fastPointwiseDiagonal_eq e ω hF w hw W hW]
  exact (F.symbolPointwiseSubalgebra_comap F.quotientTop e ω hF
    (F.quotientTopBasis e ω hF) ωQ (F.quotientTopBasis_layers e ω hF)
    (lieQuotientMap (F.layerIdeal (s + 1))) (fun _ _ hx => F.quotientLie_mem _ le_rfl hx)
    w (F.fastGradedDiagonal W)).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullFastCoefficientCoordinates
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped Matrix

def FullFastCoefficientCoordinateSpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i})) (w : σ → ℕ)
    (hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (_hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val)
        (F.reducedSquareBasis_layers e ω hF))
      (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val) W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hspan : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hv : ∀ j i, RationalHeightLE
      ((F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun a : ReducedSquareBasisIndex s ω => squareBasisWeight ω a.val)
        (F.reducedSquareBasis_layers e ω hF)).repr (v j) i) H)
    {p : ℝ} (_hp : 0 ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hκ : (Fintype.card κ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p),
    let U := F.fastPointwiseSquare e ω hF w W
    let J := F.realFirstCoefficientFastSubmodule w hw (F.reducedSquareFastRelativeSubmodule w U)
    ∃ d : ℕ, d ≤ Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1) ∧
      ∃ rows : Fin d → FirstCoefficientIndex w ω, Function.Injective rows ∧
      ∃ b : Basis (Fin d) ℝ (F.RealFirstCoefficientModule w ⧸ J),
      ∃ R : (Fin d → ℝ) →ₗ[ℝ] F.RealFirstCoefficientModule w,
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ l x, F.FirstCoefficientGrid e ω hF w l x →
          b.equivFun (J.mkQ x) ∈ realDenominatorGrid (m * l)) ∧
        (∀ l (y : Fin d → ℝ), y ∈ realDenominatorGrid l →
          F.FirstCoefficientGrid e ω hF w (m * l) (R y)) ∧
        (∀ y : Fin d → ℝ, J.mkQ (R y) = b.equivFun.symm y) ∧
        (∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
          (∀ x, F.FirstCoefficientSlowBound e ω hF w T M x → ∀ i,
            |b.equivFun (J.mkQ x) i| ≤
              Real.exp ((p + C) ^ C) * M / monomialScale T (rows i).val.1) ∧
          (∀ y : Fin d → ℝ, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
            F.FirstCoefficientSlowBound e ω hF w T (Real.exp ((p + C) ^ C) * M) (R y))) ∧
        (∀ i j, (rows j).val.1 ≠ i.val.1 →
          b.repr (J.mkQ (F.realFirstCoefficientBasis e ω hF w i)) j = 0) ∧
        ∀ (g : F.RealAdaptedPolynomialGroup w)
          (hg : (F.adaptedReducedRealSymbolHom w g).coord ∈
            realificationLieSubalgebra (F.reducedSquareFastDiagonalSubalgebra w U))
          (a c : Fin d), ω (rows a).val.2 ≤ ω (rows c).val.2 →
            LinearMap.toMatrix b b (F.realFastCoefficientAdjoint w hw U g hg).toLinearMap a c =
              (1 : Matrix (Fin d) (Fin d) ℝ) a c

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped Matrix TensorProduct

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "Q" => (E ⧸ J)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf

def BoundedInitialStateFactorization (g₀ : G) (T : σ → ℝ) (rankBound : ℕ) (p : ℝ) : Prop :=
  ∃ k : ℕ, k ≤ rankBound ∧
    ∃ (K : Submodule ℚ (L ⧸ F.layer 2)) (bK : Basis (Fin k) ℚ K),
    ∃ Hk : ℕ, 1 ≤ Hk ∧ (Hk : ℝ) ≤ Real.exp p ∧
      (∀ i j, RationalHeightLE ((F.layerOneBasis e ω hF).repr (bK j).val i) Hk) ∧
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
        ∃ x g z : G, x * g * z = g₀ ∧
          F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp p) x.val.coord ∧
          F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
          ∃ X : F.associatedGradedFiltration.FormalInductionState (F.associatedGradedBasis e ω hF) ω
            (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
            (F.fullFastGradedRelative e ω hF W) (F.gradedHorizontalKernel e ω hF K)
            (F.gradedHorizontalKernelBasis e ω hF K bK) T 2 p,
            X.P = F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val

def CommonInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (b : Basis (Fin d) ℝ Q) (rows : Fin d → FirstCoefficientIndex (fun _ : σ => 1) ω)
    (sectionMap : (Fin d → ℝ) →ₗ[ℝ] E)
    (_hsection : ∀ y, (J).mkQ (sectionMap y) = b.equivFun.symm y)
    (Cscale : ℝ) (_hC : 0 ≤ Cscale) (_hCp : Cscale ≤ Real.exp p)
    (_hweighted : ∀ (T : σ → ℝ), (∀ i, 0 < T i) → ∀ M : ℝ, 0 ≤ M →
      (∀ x, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M x → ∀ i,
        |b.equivFun ((J).mkQ x) i| ≤ Cscale * M / monomialScale T (rows i).val.1) ∧
      (∀ y, (∀ i, |y i| ≤ M / monomialScale T (rows i).val.1) →
        F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T (Cscale * M) (sectionMap y)))
    (δ : ℕ) (_hδ : 0 < δ) (_hδp : (δ : ℝ) ≤ Real.exp p)
    (_hprojectionGrid : ∀ m x, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) m x →
      b.equivFun ((J).mkQ x) ∈ realDenominatorGrid (δ * m))
    (_hsectionGrid : ∀ m (y : Fin d → ℝ), y ∈ realDenominatorGrid m →
      F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) (δ * m) (sectionMap y))
    (_hblock : ∀ i j, (rows j).val.1 ≠ i.val.1 →
      b.repr ((J).mkQ (F.realFirstCoefficientBasis e ω hF (fun _ : σ => 1) i)) j = 0)
    (_haction : ∀ i j, ω (rows i).val.2 ≤ ω (rows j).val.2 →
      LinearMap.toMatrix b b (ρ g₀).toLinearMap i j = (1 : Matrix (Fin d) (Fin d) ℝ) i j)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.BoundedInitialStateFactorization e ω hF W g₀ T d ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

omit [Fintype σ] [DecidableEq σ] [Fintype ι] in
theorem BoundedInitialStateFactorization.mono
    {g₀ : G} {T : σ → ℝ} {d d' : ℕ} {p q : ℝ}
    (h : F.BoundedInitialStateFactorization e ω hF W g₀ T d p)
    (hd : d ≤ d') (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.BoundedInitialStateFactorization e ω hF W g₀ T d' q := by
  obtain ⟨k, hk, K, bK, Hk, hHk, hHkp, hKb, m, hm, hmp, x, g, z, hfactor, hx, hz, X, hX⟩ := h
  have hepq := Real.exp_le_exp.mpr hpq
  refine ⟨k, hk.trans hd, K, bK, Hk, hHk, hHkp.trans hepq, hKb, m, hm, hmp.trans hepq,
    x, g, z, hfactor, ?_, hz, X.enlarge hpq hT, hX⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT hepq x.val.coord hx

def FullInitialStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.BoundedInitialStateFactorization e ω hF W g₀ T
      (Fintype.card ι * (s + 2) * (Fintype.card σ + 1) ^ (s + 1)) ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [Fintype ι] [Fintype τ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)

def NormalizedTerminalFactorization (g₀ : G) (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (T : σ → ℝ) (p : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp p ∧
    ∃ x g z : G, x * g * z = g₀ ∧
      F.RealAdaptedCoefficientBound e ω hF (fun _ : σ => 1) T (Real.exp p) x.val.coord ∧
      F.RealAdaptedCoefficientGrid e ω hF (fun _ : σ => 1) m z.val.coord ∧
      F.FastTerminalFactorization e ω hF W η T
        (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val) p

omit [Fintype σ] [Fintype ι] in
theorem NormalizedTerminalFactorization.mono
    {g₀ : G} {η : F.AssociatedGraded →ₗ[ℚ] ℚ} {T : σ → ℝ} {p q : ℝ}
    (h : F.NormalizedTerminalFactorization e ω hF W g₀ η T p)
    (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.NormalizedTerminalFactorization e ω hF W g₀ η T q := by
  obtain ⟨m, hm, hmp, x, g, z, hfactor, hx, hz, hterminal⟩ := h
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hpq), x, g, z, hfactor, ?_, hz,
    hterminal.mono F e ω hF W hpq hT⟩
  exact F.realAdaptedCoefficientBound_mono e ω hF (fun _ => 1) T hT
    (Real.exp_le_exp.mpr hpq) x.val.coord hx

def NormalizedTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hsp : (s + 1 : ℕ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (g₀ : G) (d : ℕ) (_hd : (d : ℝ) ≤ p)
    (_hinitial : F.BoundedInitialStateFactorization e ω hF W g₀ T d p),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonTerminalStateSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)

def TerminalCompositionSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ) (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (g₀ : G),
    F.NormalizedTerminalFactorization e ω hF W g₀ η T p →
    F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g₀.val) ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.FastTerminalFactorization e ω hF W η T
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g₀.val) ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def CommonSymbolFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G) (_hzero : coefficients (F.realAdaptedPolynomialMap (fun _ : σ => 1) g₀.val.coord) 0 = 0)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ : σ => 1) g₀.val)) ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

universe uσ uι uτ uL

variable {σ : Type uσ} {ι : Type uι} {τ : Type uτ} {L : Type uL}
  [Fintype σ] [DecidableEq σ] [Fintype ι] [Fintype τ]
  [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "Uf" => F.reducedSquareFastRelativeSubmodule (fun _ : σ => 1) Wf
local notation "J" => F.realFirstCoefficientFastSubmodule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Uf
local notation "E" => F.RealFirstCoefficientModule (fun _ : σ => 1)
local notation "G" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf

def UnnormalizedCommonSymbolFactorizationSpec (C : ℕ) : Prop :=
  ∀ (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p) (_hs : 1 ≤ s)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hstructure : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H)
    (_hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : τ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) H)
    (η : F.AssociatedGraded →ₗ[ℚ] ℚ)
    (_hη : ∀ x ∈ F.fullFastGradedRelative e ω hF W,
      basisGradeProjection (F.associatedGradedBasis e ω hF) ω (s + 1) x = x → η x = 0)
    (g₀ : G)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (M : ℝ) (_hM : 0 ≤ M) (_hMp : M ≤ Real.exp p)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (Hshifts : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ Hshifts)
    (S R : (σ → ℤ) → E) (Z : E)
    (_hbox : ∀ h ∈ Hshifts, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hcommon : ∀ h ∈ Hshifts, F.realFirstCoefficientDirectionMap g₀.val.coord (fun i => (h i : ℝ)) -
      (S h + F.realFirstCoefficientAdjoint (fun _ : σ => 1) g₀.val (R h) + Z) ∈ J)
    (_hS : ∀ h ∈ Hshifts, F.FirstCoefficientSlowBound e ω hF (fun _ : σ => 1) T M (S h))
    (_hR : ∀ h ∈ Hshifts, F.FirstCoefficientGrid e ω hF (fun _ : σ => 1) l (R h))
    (density : ℝ) (_hdensity : 0 < density) (_hdensityp : density⁻¹ ≤ Real.exp p)
    (_hdense : density * ∏ i, T i ≤ (Hshifts.card : ℝ)),
    F.SymbolTerminalFactorization e ω hF W η T
      (F.realPolynomialSymbolHom e ω hF (fun _ : σ => 1)
        (F.realAdaptedPolynomialGroupHom (fun _ : σ => 1) g₀.val)) ((p + C) ^ C)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReindexSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))

theorem symbolFactorizationIn_reindex_iff (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.SymbolFactorizationIn (b.reindex e) (fun k => ω (e.symm k)) hF' T X p l W ↔
      F.SymbolFactorizationIn b ω hF T X p l W := by
  simp only [SymbolFactorizationIn,
    F.symbolSlowBound_reindex_iff b ω hF e hF',
    F.symbolRationalGrid_reindex_iff b ω hF e hF',
    F.symbolPointwiseSubalgebra_basis_independent b ω hF
      (b.reindex e) (fun k => ω (e.symm k)) hF']

theorem symbolFactorizationIn_iff_of_basis_reindex (c : Basis κ ℚ L) (ν : κ → ℕ)
    (hC : ∀ j, F.layer j = Submodule.span ℚ (c '' {k | j ≤ ν k}))
    (hc : c = b.reindex e) (hν : ν = fun k => ω (e.symm k))
    (T : σ → ℝ) (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (p : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded) :
    F.SymbolFactorizationIn c ν hC T X p l W ↔ F.SymbolFactorizationIn b ω hF T X p l W := by
  subst c
  subst ν
  exact F.symbolFactorizationIn_reindex_iff b ω hF e hC T X p l W

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SquareQuotientHeightTransport
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (Γ : Subgroup F.squareFiltration.Group) (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ)
  (hout : bchSubgroupCoordinates (F.squareFinBasis b ω (hF 2)) Γ ⊆ denominatorGrid N)

local notation "Q" => F.squareFiltration.topQuotientModel (F.squareFinBasis b ω (hF 2))
  (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "hQ" => F.squareFiltration.topQuotientModel_basis_layers
  (F.squareFinBasis b ω (hF 2)) (squareFinWeight ω) (F.squareFinBasis_layers b ω hF) Γ N hN hin hout
local notation "bq" => F.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => F.reducedSquareBasis_layers b ω hF

theorem squareTopQuotientModel_factorization_iff (T : σ → ℝ)
    (X : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (p : ℝ) (l : ℕ) (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded) :
    (Q).filtration.SymbolFactorizationIn (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ T X p l W ↔
      F.squareFiltration.quotientTop.SymbolFactorizationIn bq ωq hq T X p l W := by
  exact F.squareFiltration.quotientTop.symbolFactorizationIn_iff_of_basis_reindex bq ωq hq
    (reducedSquareFinIndexEquiv s ω) (Q).basis
    (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ
    (F.squareTopQuotientModel_basis_reindex b ω hF Γ N hN hin hout) rfl T X p l W

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BiasedSynchronizedSquareFamily
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def SynchronizedReducedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hv : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis b ω hF w) (fun z => z.val.1) U.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis b ω hF w).repr (v i) j) H),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ {α : Type*} (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (S : Finset α) (a₀ : α) (_ha₀ : a₀ ∈ S)
        (E P R : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
        (_hP : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolFastIn w U (P a))
        (_hE : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T (Real.exp p) (E a))
        (_hR : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w l (R a))
        (_hprojection : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (E a * P a * R a) =
          F.reducedSquareRealSymbolHom w (E a₀ * P a₀ * R a₀)),
        ∃ E' P' R' : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w,
          (∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
            F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
            F.reducedSquareRealSymbolHom w (E' a) = F.reducedSquareRealSymbolHom w (E a₀) ∧
            F.reducedSquareRealSymbolHom w (R' a) = F.reducedSquareRealSymbolHom w (R a₀) ∧
            F.reducedSquareRealSymbolHom w (P' a) = F.reducedSquareRealSymbolHom w (P a₀) ∧
            F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
              w T (Real.exp ((p + C) ^ C)) (E' a) ∧
            F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a)) ∧
          ∀ a ∈ S, F.ReducedSquareRelativeCongruent w U (P' a) (P' a₀)

theorem exists_synchronized_reduced_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedReducedSquareFamilySpec s C := by
  obtain ⟨C, hC, hreset⟩ := exists_compatible_reduced_fast_reset s 1
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw U v hv hU H l p hH hl hp hι hσ hκ hHp hlp hc hh
  obtain ⟨sectionMap, m, hm, hmp, hlm, hsync⟩ :=
    hreset F b ω hF w hw U v hv hU H l p hH hl hp hι hσ hκ hHp hlp hc hh
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α T hT S a₀ ha₀ E P R hP hE hR hprojection
  let π := F.reducedSquareRealSymbolHom w
  let A := π (E a₀)
  let B := π (P a₀)
  let D := π (R a₀)
  let c := fun a => F.reducedSquareRealLinearLift w sectionMap (A⁻¹ * π (E a))
  let d := fun a => F.reducedSquareRealLinearLift w sectionMap (π (R a) * D⁻¹)
  let E' := fun a => E a * (c a)⁻¹
  let P' := fun a => c a * P a * d a
  let R' := fun a => (d a)⁻¹ * R a
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hEin : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T
      (Real.exp ((p + 2) ^ 1)) (E a) := by
    intro a ha
    exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T hTpos
      (Real.exp_le_exp.mpr (by norm_num)) (E a) (hE a ha)
  have hA := F.reducedSquareRealSymbolHom_slow b ω hF w T (Real.exp ((p + 2) ^ 1)) (E a₀) (hEin a₀ ha₀)
  have hD := F.reducedSquareRealSymbolHom_grid b ω hF w l (R a₀) (hR a₀ ha₀)
  have hB := F.reducedSquareRealSymbolHom_fast w U (P a₀) (hP a₀ ha₀)
  have hresult : ∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
      F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
      π (E' a) = A ∧ π (R' a) = D ∧ π (P' a) = B ∧
      F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
        w T (Real.exp ((p + C) ^ C)) (E' a) ∧
      F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a) := by
    intro a ha
    have heq : A * B * D = π (E a * P a * R a) := by
      simpa only [A, B, D, π, map_mul] using (hprojection a ha).symm
    exact hsync T hT (E a) (P a) (R a) A B D (hP a ha) hB heq
      (hEin a ha) (hR a ha) hA hD
  refine ⟨E', P', R', hresult, ?_⟩
  intro a ha
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw U
    (hresult a ha).2.1 (hresult a₀ ha₀).2.1
    ((hresult a ha).2.2.2.2.1.trans (hresult a₀ ha₀).2.2.2.2.1.symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def PointwiseSynchronizedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : 2 * (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE
      ((F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)).repr (v i) j) H),
    let U := F.squareFiltration.quotientTop.symbolPointwiseSubalgebra (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w W
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ {α : Type*} (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (S : Finset α) (a₀ : α) (_ha₀ : a₀ ∈ S)
        (E P R : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
        (_hP : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolFastIn w U (P a))
        (_hE : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T (Real.exp p) (E a))
        (_hR : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w l (R a))
        (_hprojection : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (E a * P a * R a) =
          F.reducedSquareRealSymbolHom w (E a₀ * P a₀ * R a₀)),
        ∃ E' P' R' : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w,
          (∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
            F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
            F.reducedSquareRealSymbolHom w (E' a) = F.reducedSquareRealSymbolHom w (E a₀) ∧
            F.reducedSquareRealSymbolHom w (R' a) = F.reducedSquareRealSymbolHom w (R a₀) ∧
            F.reducedSquareRealSymbolHom w (P' a) = F.reducedSquareRealSymbolHom w (P a₀) ∧
            F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
              w T (Real.exp ((p + C) ^ C)) (E' a) ∧
            F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a)) ∧
          ∀ a ∈ S, F.ReducedSquareRelativeCongruent w U (P' a) (P' a₀)

theorem exists_pointwise_synchronized_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PointwiseSynchronizedSquareFamilySpec s C := by
  obtain ⟨a, _, hfamily⟩ := exists_synchronized_reduced_square_family s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 3)) ^ (s + 3)
  let B : Polynomial ℕ := (Q + Polynomial.C a) ^ a
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  let bq := F.reducedSquareBasis b ω hF
  let ωq := fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val
  let hq := F.reducedSquareBasis_layers b ω hF
  let U := F.squareFiltration.quotientTop.symbolPointwiseSubalgebra bq ωq hq w W
  let v' := F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily bq ωq hq w v
  let : Fintype (ReducedSquareSymbolIndex s w ω) :=
    symbolBasisIndexFintype w ωq s hw
      (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step bq ωq hq)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hqpos : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hιp : (Fintype.card ι : ℝ) ≤ p := by
    have hi := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
    linarith
  have hdim : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p := by
    have hnat : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have hreal : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ 2 * (Fintype.card ι : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans hι
  have hcount : (Fintype.card (ReducedSquareSymbolIndex s w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (ReducedSquareSymbolIndex s w ω × κ) ≤
        Fintype.card (ReducedSquareBasisIndex s ω) * (s + 1) * (Fintype.card σ + 1) ^ s *
          Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ωq s hw
        (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step bq ωq hq))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hdim hσ hκ)
  have hbound : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  obtain ⟨m, hm, hmp, hlm, hsync⟩ := hfamily F b ω hF w hw U v'
    (F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_span bq ωq hq w W hW v hv)
    (F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_blockInvariant bq ωq hq w W)
    H l q hH hl hqpos (hιp.trans hpq) (hσ.trans hpq) hcount
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hc
    (F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_height bq ωq hq w v hH hh)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbound), hlm, ?_⟩
  intro α T hT S a₀ ha₀ E P R hP hE hR hprojection
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hEin : ∀ x ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound bq ωq hq w T
      (Real.exp q) (E x) := fun x hx =>
    F.squareFiltration.quotientTop.symbolSlowBound_mono bq ωq hq w T hTpos
      (Real.exp_le_exp.mpr hpq) (E x) (hE x hx)
  have hchosen := hsync T
    (fun i => (Real.exp_le_exp.mpr hbound).trans (hT i)) S a₀ ha₀ E P R
  obtain ⟨E', P', R', hgood, hrelative⟩ := hchosen hP hEin hR hprojection
  refine ⟨E', P', R', ?_, hrelative⟩
  intro x hx
  obtain ⟨heq, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood x hx
  exact ⟨heq, hfast, hleft, hright, hmiddle,
    F.squareFiltration.quotientTop.symbolSlowBound_mono bq ωq hq w T hTpos
      (Real.exp_le_exp.mpr hbound) (E' x) hslow, hrat⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "bq" => D.filtration.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => D.filtration.reducedSquareBasis_layers b ω hF

theorem HasFixedNativeSquareFactors.canonical_factors {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {h : σ → ℤ} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors (D.filtration.squareFinBasis b ω (hF 2))
      (squareFinWeight ω) (D.filtration.squareFinBasis_layers b ω hF)
      N hN hin hout hs g η T h p l W) :
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        D.filtration.squareFiltration.quotientTop.SymbolFactorizationIn bq ωq hq T
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) p l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, _, _, _, hfixed⟩ := hdata
  refine ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ?_⟩
  exact (D.filtration.squareTopQuotientModel_factorization_iff b ω hF
    (D.filtration.squareLattice D.lattice) N hN hin hout T _ p l W).mp hfixed

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

def SynchronizedNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
      (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
      (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : 2 * (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF)).repr
          (v i) j) H),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (hs : 1 ≤ s) (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (η : L →ₗ[ℚ] ℚ) (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
        (_hdata : ∀ h ∈ S, D.HasFixedNativeSquareFactors
          (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers b ω hF) N hN hin hout hs g η T h p l W),
        D.SynchronizedNativeSquareData b ω hF T g S h₀ W p ((p + C) ^ C) l m

theorem exists_synchronized_native_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeSquareFamilySpec s C := by
  obtain ⟨C, hC, hfamily⟩ := exists_pointwise_synchronized_square_family s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ d D b ω hF N hN hin hout W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  obtain ⟨m, hm, hmp, hlm, hsync⟩ := hfamily D.filtration b ω hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT hs g η S h₀ hh₀ hdata
  have hcanonical := fun h hh =>
    RationalFilteredNilmanifold.HasFixedNativeSquareFactors.canonical_factors D b ω hF
      N hN hin hout (hdata h hh)
  choose! ε γ hγ hε r hf hsecond hderivative hfactor using hcanonical
  have hfastFactors := fun h hh => SymbolFactorizationIn.exists_fast_factors
    D.filtration.squareFiltration.quotientTop (D.filtration.reducedSquareBasis b ω hF)
    (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF) (hfactor h hh)
  choose! E P R hprod hE hR hP using hfastFactors
  let π := D.filtration.reducedSquareRealSymbolHom (fun _ : σ => 1)
  have hprojection : ∀ h ∈ S, π (E h * P h * R h) = D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) g := by
    intro h hh
    rw [hprod h hh]
    change D.filtration.reducedSquareRealSymbolHom (fun _ => 1)
      (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h)) = _
    rw [D.filtration.adaptedReducedRealSymbolHom_square_projection, hsecond h hh]
  obtain ⟨E', P', R', hgood, hrelative⟩ := hsync T hT S h₀ hh₀ E P R hP hE hR
    (fun h hh => (hprojection h hh).trans (hprojection h₀ hh₀).symm)
  refine ⟨ε, γ, r, E', P', R', π (E h₀), π (P h₀), π (R h₀), ?_, ?_, ?_, ?_, ?_, hrelative⟩
  · rw [← map_mul, ← map_mul]
    exact hprojection h₀ hh₀
  · exact D.filtration.reducedSquareRealSymbolHom_slow b ω hF (fun _ => 1) T (Real.exp p) (E h₀) (hE h₀ hh₀)
  · exact D.filtration.reducedSquareRealSymbolHom_grid b ω hF (fun _ => 1) l (R h₀) (hR h₀ hh₀)
  · exact D.filtration.symbolFastIn_reducedSquareRealSymbolHom (fun _ => 1) _ (P h₀) (hP h₀ hh₀)
  · intro h hh
    obtain ⟨heq, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood h hh
    exact ⟨hγ h hh, hε h hh, hf h hh, hsecond h hh, hderivative h hh,
      heq.trans (hprod h hh), hfast, hleft, hright, hmiddle, hslow, hrat⟩

end Erdos3

end

end OAI
end


