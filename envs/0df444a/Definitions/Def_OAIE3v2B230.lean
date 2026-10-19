-- Prove2me | Definitions.Def_OAIE3v2B230
-- name    : OAIE3v2B230
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:28:24.102038+00:00
-- url     : https://prove2.me/theorems/5866a208-b490-4e22-ad65-f402eedec918
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 235 of 311
-- statement:
--   Definitions bundle 235 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B204`, `OAIE3v2B205`, `OAIE3v2B206`, `OAIE3v2B210`, `OAIE3v2B211`, `OAIE3v2B212` of this split.
--
--   Modules: `Dynamics/PreparedEarlyStructuralPowerBudget.lean`, `Estimates/AllocatedMarkedDictionaryRecovery.lean`, `Estimates/CoveredInducedCorrelationFamily.lean`, `Estimates/MarkedRefilteredLowerNativeDiagram.lean`, `Estimates/NativeDetectorContradictionSpec.lean`, `Estimates/NativeIteratedDifferencing.lean`, `Estimates/NativeMarkedFreezingPhysicalData.lean`, `Estimates/NativeResidualCrossInduction.lean`, `Estimates/PreparedFamilyCanonicalGeometry.lean`, `Estimates/QuadraticBoundedFamily.lean`, `Geometry/CommonRefilteredFactorsSymbolTransport.lean`, `Lattices/CertifiedFullChartAffineTerminal.lean`, `Lattices/PreparedIntegerRemainder.lean`, `Lattices/QuadraticMarkedAffine.lean`, `Lattices/SpatialAffineFullMass.lean`, `Lattices/UniformExternalMarkedAffineSliceFreezingDictionary.lean`, `Linear/RankPreparationPaddedFreezingLifts.lean`, `Nilpotent/NativeIntegerChartNiltest.lean`, `Polynomial/PolynomialPatchTaggedBufferedScore.lean`, `Polynomial/PreparedPolynomialIdentity.lean`, `Polynomial/PreparedPolynomialPullback.lean`, `Sampling/PreparedEarlyLateSamplerGeometry.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B204
import Definitions.Def_OAIE3v2B205
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B210
import Definitions.Def_OAIE3v2B211
import Definitions.Def_OAIE3v2B212

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedMarkedDictionaryRecovery
namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

attribute [local instance_reducible] optionLieSpace optionDimension

theorem exists_uniform_frozen_two_target_reconstruction (t k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {H M L₀ L₁ : Type u}
      [LieRing H] [LieAlgebra ℚ H] [LieRing M] [LieAlgebra ℚ M]
      [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
      [TopologicalSpace (ℝ ⊗[ℚ] H)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] H)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] H)] [T2Space (ℝ ⊗[ℚ] H)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)]
      [TopologicalSpace (ℝ ⊗[ℚ] L₁)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₁)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₁)] [T2Space (ℝ ⊗[ℚ] L₁)]
      {s e f d₀ d₁ : ℕ}
      (E : RationalFilteredNilmanifold H t e) (D : RationalFilteredNilmanifold M t f)
      (Q : RationalFilteredNilmanifold L₀ s d₀) (_hst : s ≤ t)
      (F₁ : RationalFilteredNilmanifold L₁ t d₁)
      (φ : H →ₗ⁅ℚ⁆ M) (ψ₀ : H →ₗ⁅ℚ⁆ L₀) (ψ₁ : H →ₗ⁅ℚ⁆ L₁) {p : ℝ},
      1 ≤ p →
      E.GeometryComplexityLE p → D.GeometryComplexityLE p → Q.GeometryComplexityLE p →
      F₁.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (φ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr (ψ₀ (E.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (F₁.basis.repr (ψ₁ (E.basis j)) i) ≤ p) →
      Function.Injective (optionProductMap ψ₀ (fun _ : Unit => ψ₁)) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Q' : RationalFilteredNilmanifold L₀ s d₀,
        Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
        Q'.GeometryComplexityLE ((p + C) ^ C) ∧
        ∃ F' : RationalFilteredNilmanifold L₁ t d₁,
          F'.filtration = F₁.filtration ∧ F'.basis = F₁.basis ∧ F'.lattice ≤ F₁.lattice ∧
          F'.GeometryComplexityLE ((p + C) ^ C) ∧
          ∀ a r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p + 2) ^ k)) →
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid q →
            ∀ (S : D.Space → ℂ) (ℓ : ℝ≥0), (ℓ : ℝ) ≤ Real.exp p →
              (letI := D.metricSpace; LipschitzWith ℓ S) →
              (∀ x, (S x).im = 0 ∧ 0 ≤ (S x).re ∧ (S x).re ≤ 1) →
              ∃ (v : Q'.Space × F'.Space → ℂ) (K : ℝ≥0),
                (K : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                (letI := Q'.metricSpace; letI := F'.metricSpace; LipschitzWith K v) ∧
                (∀ x, (v x).im = 0 ∧ 0 ≤ (v x).re ∧ (v x).re ≤ 1) ∧
                ∀ x : E.RealGroup,
                  v (QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := Q'.filtration.lowerCentralSeries_eq_bot) ψ₀ x),
                    QuotientGroup.mk (realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := F'.filtration.lowerCentralSeries_eq_bot) ψ₁ x)) =
                    S (QuotientGroup.mk (a * realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
                      (hM := D.filtration.lowerCentralSeries_eq_bot) φ x * r)) := by
  obtain ⟨A, _, hfrozen⟩ := exists_uniform_frozen_reconstruction t k
  obtain ⟨B, _, hsplit⟩ := exists_lowered_split_reconstruction_cover
  let X : Polynomial ℕ := Polynomial.X
  let P₀ := (X + 3) ^ 2
  let P₁ := P₀ + (P₀ + Polynomial.C A) ^ A
  let P₂ := P₁ + (P₁ + Polynomial.C B) ^ B + (X + 2) ^ 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P₂
  refine ⟨C, hC, ?_⟩
  intro H M L₀ L₁ _ _ _ _ _ _ _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    s e f d₀ d₁ E D Q hst F₁ φ ψ₀ ψ₁ p hpone hE hD hQ hF₁ hφ hψ₀ hψ₁ hψinj q hq hqp
  have hp : 0 ≤ p := le_trans zero_le_one hpone
  let F := fun _ : Unit => F₁
  let ψ := fun _ : Unit => ψ₁
  have hι : (Fintype.card Unit : ℝ) ≤ p := by simpa using hpone
  have hF : ∀ i, (F i).GeometryComplexityLE p := fun _ => hF₁
  have hψ : ∀ a i j, rationalLogHeight ((F a).basis.repr (ψ a (E.basis j)) i) ≤ p :=
    fun _ => hψ₁
  let Z₀ := pi F
  let T := optionProduct (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (Unit → L₁))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (Unit → L₁))
  let := realification_moduleTopology_t2 Z₀.basis
  let Mprod := ∀ i : Option Unit, optionLieSpace L₀ (fun _ : Unit => L₁) i
  let Aprod := optionFactors (Q.raiseStep hst) F
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Mprod)
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] Mprod)
  let := realification_moduleTopology_t2 T.basis
  let p₀ := (p + 3) ^ 2
  let p₁ := p₀ + (p₀ + A) ^ A
  have hp₀ : 0 ≤ p₀ := sq_nonneg _
  have hpp₀ : p ≤ p₀ := by dsimp only [p₀]; nlinarith [sq_nonneg p]
  have hp₀p₁ : p₀ ≤ p₁ := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hp₁ : 0 ≤ p₁ := hp₀.trans hp₀p₁
  have hAp₁ : (p₀ + A) ^ A ≤ p₁ := le_add_of_nonneg_left hp₀
  have hsum : p₁ + (p₁ + B) ^ B + (p + 2) ^ 2 ≤ (p + C) ^ C := by
    simpa [P₂, P₁, P₀, X, p₀, p₁, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p₁ + B) ^ B ≤ (p + C) ^ C := by
    nlinarith [sq_nonneg (p + 2)]
  have htotal : (p₁ + B) ^ B + (p + 2) ^ 2 ≤ (p + C) ^ C := by linarith
  have hT : T.GeometryComplexityLE p₀ :=
    optionProduct_geometry (Q.raiseStep hst) F hp hι (Q.raiseStep_geometry hst hQ) hF
  have hmap : ∀ i j, rationalLogHeight (T.basis.repr (optionProductMap ψ₀ ψ (E.basis j)) i) ≤ p₀ := by
    intro i j
    exact (optionProductMap_logHeight (Q.raiseStep hst) F E.basis ψ₀ ψ hψ₀ hψ i j).trans hpp₀
  obtain ⟨Λ, _, _, _, _, _, m, hm, hin, hout, hV, hrec⟩ :=
    hfrozen E D T φ (optionProductMap ψ₀ ψ) p₀ hp₀ (hE.mono E hpp₀)
      (hD.mono D hpp₀) hT (fun i j => (hφ i j).trans hpp₀) hmap q hq
      (hqp.trans (Real.exp_le_exp.mpr hpp₀))
  obtain ⟨Δ, N, hN, hNin, hNout, _, hindex, hQfil, hQle, hQgeom, hGgeom, hZgeom, hsplitrec⟩ :=
    hsplit Q hst F Λ m hm hin hout hp₁ (hι.trans (hpp₀.trans hp₀p₁))
      (hQ.mono Q (hpp₀.trans hp₀p₁))
      (fun i => (hF i).mono (F i) (hpp₀.trans hp₀p₁))
      (hV.2.1.trans (Real.exp_le_exp.mpr hAp₁))
  let G := fun i => (Aprod i).withLattice (Δ i) (N i) (hN i) (hNin i) (hNout i)
  let Q' := Q.loweredCover hst (Δ none) (N none) (hN none) (hNin none) (hNout none)
  let F' : RationalFilteredNilmanifold L₁ t d₁ := G (some ())
  let Z := pi (fun _ : Unit => F')
  refine ⟨Q', hQfil, rfl, hQle, hQgeom.mono Q' hcost,
    F', rfl, rfl, (hindex (some ())).1, (hGgeom (some ())).mono F' hcost, ?_⟩
  intro a r ha hr S ℓ hℓ hS hpositive
  have hkernel := frozenDiagramKernelInvariance_of_injective E D T φ (optionProductMap ψ₀ ψ)
    hψinj S a r
  have ha₀ : ∀ i, |(D.basis.baseChange ℝ).repr a.coord i| ≤ Real.exp ((p₀ + 2) ^ k) := by
    intro i
    exact (ha i).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith) (by linarith) k))
  obtain ⟨u, K₀, hK₀, hu, hunit, _, heval⟩ := hrec a r ha₀ hr S ℓ
    (hℓ.trans (Real.exp_le_exp.mpr hpp₀)) hS hpositive hkernel
  obtain ⟨v, K, hK, hv, hpos, hveval⟩ :=
    hsplitrec u K₀ (hK₀.trans (Real.exp_le_exp.mpr hAp₁)) hu hunit
  let := Q'.metricSpace
  let := F'.metricSpace
  let := Z.metricSpace
  let L : ℝ≥0 := max 1 (productMetricBound (fun _ : Unit => d₁))
  let v' : Q'.Space × F'.Space → ℂ := fun z => v (z.1, F'.singletonProductSpace z.2)
  have hmapLip : LipschitzWith L (fun z : Q'.Space × F'.Space =>
      (z.1, F'.singletonProductSpace z.2)) := by
    have h := (LipschitzWith.prod_fst (β := F'.Space)).prodMk
      (F'.singletonProductSpace_lipschitz.comp
        (LipschitzWith.prod_snd (α := Q'.Space)))
    simpa only [mul_one, Function.comp_def, optionDimension, L] using h
  have hL : (L : ℝ) ≤ Real.exp ((p + 2) ^ 2) := by
    exact max_le (Real.one_le_exp (sq_nonneg _))
      (productMetricBound_singleton_le_exp hp hF₁.1)
  have hKL : (K * L : ℝ≥0) ≤ Real.exp ((p + C) ^ C) := by
    calc
      (K * L : ℝ≥0) = (K : ℝ) * (L : ℝ) := NNReal.coe_mul K L
      _ ≤ Real.exp ((p₁ + B) ^ B) * Real.exp ((p + 2) ^ 2) :=
        mul_le_mul hK hL (NNReal.coe_nonneg L) (Real.exp_nonneg _)
      _ = Real.exp ((p₁ + B) ^ B + (p + 2) ^ 2) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr htotal
  refine ⟨v', K * L, hKL, hv.comp hmapLip, fun z => hpos _, ?_⟩
  intro x
  dsimp only [v', Prod.fst, Prod.snd]
  rw [F'.singletonProductSpace_realificationMap E.filtration ψ₁ x]
  let maps := optionMaps ψ₀ ψ
  let y : (pi G).RealGroup := realificationMap (hnil := E.filtration.lowerCentralSeries_eq_bot)
    (hM := (pi G).filtration.lowerCentralSeries_eq_bot) (liePiMap maps) x
  have hfirst := lowered_productProjectionHom_realificationMap E.filtration G Q maps x
  have hsecond := congrArg Prod.snd (optionProductSpaceEquiv_realificationMap E.filtration G maps x)
  have hargs := congrArg₂ Prod.mk
    (congrArg (QuotientGroup.mk : Q'.RealGroup → Q'.Space) hfirst.symm) hsecond.symm
  exact (congrArg v hargs).trans ((hveval y).trans (heval x))

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem exists_allocated_marked_diagram_recovery_covers (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type u}
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d f nD nF nQ : ℕ}
      (D : RationalFilteredNilmanifold L (s + 1) d)
      (Fmark : RationalFilteredNilmanifold M (s + 1) f)
      (φ : L →ₗ⁅ℚ⁆ M)
      (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ Fmark.filtration.layer j)
      (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
      (Dref : RationalFilteredNilmanifold
        (D.filtration.gradedRefiltrationSubalgebra W) (s + 1) nD)
      (_hDref : Dref.filtration = D.filtration.gradedRefiltration W)
      (Fref : RationalFilteredNilmanifold
        (Fmark.filtration.gradedRefiltrationSubalgebra
          (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))) (s + 1) nF)
      (Q : RationalFilteredNilmanifold
        ((D.filtration.gradedRefiltrationSubalgebra W) ⧸ Dref.filtration.layerIdeal (s + 1)) s nQ)
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.gradedRefiltrationSubalgebra W))]
      [TopologicalSpace (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [T2Space (ℝ ⊗[ℚ] (Fmark.filtration.gradedRefiltrationSubalgebra
        (W.map (D.filtration.associatedGradedMap Fmark.filtration φ hφ))))]
      [TopologicalSpace (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] ((D.filtration.gradedRefiltrationSubalgebra W) ⧸
        Dref.filtration.layerIdeal (s + 1)))] {p : ℝ},
      1 ≤ p → Dref.GeometryComplexityLE p → D.GeometryComplexityLE p →
      Q.GeometryComplexityLE p → Fref.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (Dref.basis j : L) i) ≤ p) →
      (∀ i j, rationalLogHeight (Q.basis.repr
        (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)) (Dref.basis j)) i) ≤ p) →
      (∀ i j, rationalLogHeight (Fref.basis.repr
        (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W (Dref.basis j)) i) ≤ p) →
      (∀ x : L, x ∈ D.filtration.gradedRefiltrationLayer W (s + 1) → φ x = 0 → x = 0) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
        AllocatedMarkedDiagramRecoveryCovers D Fmark φ hφ W Dref Fref Q k q p ((p + C) ^ C) := by
  obtain ⟨C, hC, hconstruct⟩ := exists_uniform_frozen_two_target_reconstruction (s + 1) k
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d f nD nF nQ D Fmark φ hφ W Dref hDref Fref Q
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p hp hDrefGeom hDGeom hQGeom hFrefGeom
    hinc hquot hmark hker q hq hqp
  obtain ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, hrec⟩ :=
    hconstruct Dref D Q (Nat.le_succ s) Fref
      (D.filtration.gradedRefiltrationSubalgebra W).incl
      (lieQuotientMap (Dref.filtration.layerIdeal (s + 1)))
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W)
      hp hDrefGeom hDGeom hQGeom hFrefGeom hinc hquot hmark
      (D.allocatedMarkedDiagram_injective_of_top_kernel Fmark φ hφ W Dref hDref hker)
      q hq hqp
  refine ⟨Q', hQfil, hQbasis, hQlat, hQgeom, F', hFfil, hFbasis, hFlat, hFgeom, ?_⟩
  let K : ℝ≥0 := ⟨Real.exp ((p + C) ^ C), (Real.exp_pos _).le⟩
  let := Q'.metricSpace
  let := F'.metricSpace
  dsimp only
  intro a r ha hr S ℓ hℓ hS hpositive x
  obtain ⟨v, Lrec, hLrec, hv, _, heval⟩ := hrec a r ha hr S ℓ hℓ hS hpositive
  have hL : Lrec ≤ K := hLrec
  refine positiveImageSlice_eq _ _ _ (fun x => hpositive _) ?_ x
  intro y z
  have h := (hv.weaken hL).dist_le_mul
    (Dref.markedTopQuotientDiagram F'
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q' y)
    (Dref.markedTopQuotientDiagram F'
      (D.filtration.gradedRefiltrationMap Fmark.filtration φ hφ W) Q' z)
  simpa only [dist_eq_norm, markedTopQuotientDiagram, heval] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDetectorContradictionSpec
namespace OAI

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def PrescribedCommonFactorizationSpec (s C : ℕ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L : (Fin B.count × Bool) → Type u}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
        [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ F : ∀ i, (D i).SquareModelData,
        (∀ i, (F i).fullModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i, (F i).quotientModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i j k, rationalLogHeight ((D i).basis.repr ((F i).basis j) k) ≤ (p + C) ^ C) ∧
        ∃ h₀ ∈ H, ∃ branches : Fin B.count → Bool × Bool,
          ∃ (A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1))
            (R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1))
            (η γ : ZMod N → ∀ j, (D (j, false)).RealGroup)
            (rSq : ZMod N → ∀ j,
              (D (j, false)).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ j, (A j).normBound ≤ 1 ∧ (A j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x)) ∧
            (∀ h j, γ h j ∈ (D (j, false)).realLattice ∧
              (∀ i, |((D (j, false)).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : Unit → ℤ,
                (D (j, false)).filtration.realSquareFstHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (η h j)⁻¹ * (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h (branches j).1) (T (j, false)).orbit * (γ h j)⁻¹ ∧
                (D (j, false)).filtration.realSquareSndHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h₀ (branches j).2) (T (j, false)).orbit) ∧
              (R h j).orbit = (D (j, false)).filtration.squareFiltration.realQuotientPolynomialOrbit
                ((D (j, false)).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
              (R h j).normBound ≤ 1 ∧ (R h j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (R h j).eval x =
                (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                  star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2))) ∧
            Nonempty (B.CommonFactorization (fun j => (F (j, true)).quotientModel)
              (fun j => (F (j, false)).quotientModel) A R h₀ H ((p + C) ^ C))

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

def FactoredPositiveShiftContradictionSpec (s Dexp : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      {L M : Fin B.count → Type}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1 + 1) (e j))
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, T2Space (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, T2Space (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      (Y : ∀ j, (E j).SquareModelData)
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (Y j).quotientModel.Niltest (fun _ : Unit => 1))
      (anchor : ZMod N) (H : Finset (ZMod N)) {p : ℝ}
      (F : B.CommonFactorization D (fun j => (Y j).quotientModel) A R anchor H p),
      H ⊆ B.shifts → 2 ≤ p → q ≤ p →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      (∀ j, (Y j).fullModel.GeometryComplexityLE p) →
      (∀ j, (Y j).quotientModel.GeometryComplexityLE p) →
      (∀ j i k, rationalLogHeight ((E j).basis.repr ((Y j).basis i) k) ≤ p) →
      ∀ (g₀ : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (branches : Fin B.count → Bool × Bool)
        (η γ : ZMod N → ∀ j, (E j).RealGroup)
        (rSq : ZMod N → ∀ j,
          (E j).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ h ∈ F.shifts, ∀ j, γ h j ∈ (E j).realLattice) →
        (∀ h ∈ F.shifts, ∀ j i, |((E j).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp p) →
        (∀ h ∈ F.shifts, ∀ j (x : Unit → ℤ),
          (E j).filtration.realSquareFstHom
            ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ => 1) x (rSq h j)) =
              (η h j)⁻¹ * (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
                (x + fun _ => cyclicBranchOffset h (branches j).1) (g₀ j) * (γ h j)⁻¹ ∧
          (E j).filtration.realSquareSndHom
            ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ => 1) x (rSq h j)) =
              (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
                (x + fun _ => cyclicBranchOffset anchor (branches j).2) (g₀ j)) →
        (∀ h ∈ F.shifts, ∀ j, (R h j).orbit =
          (E j).filtration.squareFiltration.realQuotientPolynomialOrbit
            ((E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h j)) →
        Odd N → Real.exp ((productExpansionBudget p + 2) ^ Dexp) ≤ N →
        (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
        (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
        (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
        CyclicNiltestUpperComparison.{0} (s + 2) N ((productExpansionBudget p + 2) ^ Dexp)
          (Real.exp (-((productExpansionBudget p + 2) ^ Dexp))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativeDetectorContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
    (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
    (w : Fin B.dim → ℕ),
    (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
    ∀ {p p₁ p₂ K M beta₁ beta₂ : ℝ},
      2 ≤ p → 2 ≤ p₁ → 2 ≤ p₂ → q ≤ p → p₁ ≤ p → p₂ ≤ p →
      0 < K → 0 < M → 0 < beta₁ → 0 < beta₂ →
      (∀ n, ‖((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ)‖ ≤ M) →
      (∀ n, ‖(weight n : ℂ)‖ ≤ K) →
      2 / beta₁ ≤ Real.exp p → 2 / beta₂ ≤ Real.exp p →
      let eta := Real.exp (-(2 * q + 2))
      (1 + 4 * K ^ 2 / (beta₁ ^ 2 * (eta / 4) ^ 2)) *
        (1 + 4 / (beta₂ ^ 2 * (eta * beta₁ / 8) ^ 2)) ≤ Real.exp p →
      NativeModelDetector (s + 1 + 1) N p₁
        (shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily) K M beta₁ (eta / 4) →
      (∀ f ∈ nativeCyclicFunctions (s + 1 + 1) N p₁,
        NativeModelDetector (s + 1 + 1) N p₂
          (shiftTestingSeminorm f (translatedTestFamily B.testingFamily))
          1 K beta₂ (eta * beta₁ / 8)) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeIteratedDifferencing
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

open scoped TensorProduct BigOperators

theorem exists_univariate_cyclic_difference_models (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type} {I : Type*} [Fintype I]
      [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d) {p e : ℝ}
      (V : D.UnitVerticalObservable (D.filtration.realification.subgroup (s + 1)) I p)
      (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card I : ℝ) ≤ Real.exp p → 0 ≤ e →
      ∀ {N : ℕ} [NeZero N], Real.exp (e + 16) ≤ (N : ℝ) →
      ∀ (i j : I) (k : ZMod N), ∃ K : (Unit → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : Unit => 1) s ((p + e + C) ^ C) K) ∧
        (𝔼 n : ZMod N,
          ‖(V.test g i).eval (fun _ => (n.val : ℤ)) *
              star ((V.test g j).eval (fun _ => ((n + k).val : ℤ))) -
            K (fun _ => (n.val : ℤ))‖) ≤ Real.exp (-e) := by
  obtain ⟨C, hC, htwo⟩ := exists_cyclic_second_difference_models_degree s hs
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d D p e V g hp hD hI he N _ hN i j k
  let A : Unit → ((Fin 2 → ℤ) →+ ℤ) := fun _ =>
    { toFun := fun x => x 1, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let g₂ := ((V.test g i).linearPullbackHom A).orbit
  have heval (l : I) (x : Fin 2 → ℤ) :
      (V.test g₂ l).eval x = (V.test g l).eval (fun _ => x 1) := by
    change ((V.test g l).linearPullbackHom A).eval x = _
    exact (V.test g l).eval_linearPullbackHom A x
  obtain ⟨K, ⟨E⟩, herr⟩ := htwo D V g₂ hp hD hI he hN i j k
  let B : Fin 2 → ((Unit → ℤ) →+ ℤ) :=
    ![0, { toFun := fun x => x (), map_zero' := rfl, map_add' := fun _ _ => rfl }]
  have hB (x : Unit → ℤ) : (fun l => B l x) = ![0, x ()] := by
    funext l
    fin_cases l <;> rfl
  refine ⟨fun x => K ![0, x ()], ?_, ?_⟩
  · exact ⟨by simpa only [hB] using E.linearPullbackHom B⟩
  · simpa only [cyclicSecondDifference, heval, Matrix.cons_val_one, Matrix.cons_val_zero] using herr 0

end Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoveredInducedCorrelationFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal

theorem second_marked_span : markedLieSpan generators weights marked 0 2 0 ≤
    (⊥ : LieIdeal ℚ Seed).toSubmodule := by
  rw [markedLieSpan_marked_terminal filtration generators weights marked weight_pos generator_mem]
  exact bot_le

noncomputable def evaluation (t : ℕ) :=
  markedBaseEvaluation filtration generators weights marked t (⊥ : LieIdeal ℚ Seed) second_marked_span 0

theorem filtration_layers (j : ℕ) : filtration.associatedDegree.layer j =
    Submodule.span ℚ (RationalTorus.basis 1 '' {i | j ≤ weights i}) := by
  simpa only [filtration, NilpotentLieFiltration.canonicalDegreeRank_associatedDegree_layer, weights]
    using RationalTorus.basis_layers 1 j

theorem generator_height {p : ℝ} (hp : 0 ≤ p) (i j : Fin 1) :
    rationalLogHeight ((RationalTorus.basis 1).repr (generators i) j) ≤ p :=
  rationalLogHeight_le_of_height (basis_repr_height_one _ _ _)
    (by simpa only [Nat.cast_one] using Real.one_le_exp hp)

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.QuadraticMarkedAffine
namespace OAI

section

namespace Erdos3.QuadraticMarked

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def seedVector (a : ℝ) : ℝ ⊗[ℚ] Seed := a ⊗ₜ[ℚ] generators 0

theorem seedVector_mem (a : ℝ) :
    seedVector a ∈ (markedLieSpan generators weights marked 1 1 1).baseChange ℝ := by
  apply Submodule.tmul_mem_baseChange_of_mem
  simpa only [weights, marked, Bool.true_eq, ite_true] using
    markedLieSpan_leaf generators weights marked (0 : Fin 1)

noncomputable def affineCoefficient (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    (markedPolynomialLayer (σ := Fin t) generators weights marked 1 0 1).baseChange ℝ :=
  ⟨realAffinePolynomial (seedVector a) (fun i => seedVector (b i)),
    realAffinePolynomial_mem_marked generators weights marked
      (Submodule.baseChange_mono ℝ
        (markedLieSpan_antitone generators weights marked le_rfl (by omega) le_rfl)
        (seedVector_mem a)) (fun i => seedVector_mem (b i))⟩

noncomputable def sourceLift (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    ℝ ⊗[ℚ] markedShiftSubalgebra filtration generators weights marked t :=
  realMarkedPolynomialLift filtration generators weights marked weight_pos generator_mem t 1 0 1
    (affineCoefficient t a b)

noncomputable def projectedLift (t : ℕ) (a : ℝ) (b : Fin t → ℝ) : ℝ ⊗[ℚ] Algebra t :=
  (lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
    (sourceLift t a b)

theorem sourceLift_eval (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (u : Fin t → ℚ) :
    (markedShiftEval filtration generators weights marked t u).baseChange ℝ (sourceLift t a b) =
      seedVector a + ∑ i, (u i : ℝ) • seedVector (b i) := by
  apply (realMarkedPolynomialLift_eval filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (affineCoefficient t a b) u).trans
  simpa only [affineCoefficient, ← Rat.cast_smul_eq_qsmul ℝ] using
    realAffinePolynomial_eval (seedVector a) (fun i => seedVector (b i)) u

theorem projectedLift_mem (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    projectedLift t a b ∈ (multidegree t).realification.layer (correlationInput 0 1) :=
  realMarkedPolynomialLift_quotient_mem filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (affineCoefficient t a b)

theorem projectedLift_pure (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    projectedLift t a b ∈
      (markedQuotientPolynomialAlgebra filtration generators weights marked t).toSubmodule.baseChange ℝ := by
  change projectedLift t a b ∈
    (LinearMap.ker (markedQuotientPhase filtration generators weights marked t).toLinearMap).baseChange ℝ
  rw [realification_ker, LinearMap.mem_ker]
  change (markedQuotientPhase filtration generators weights marked t).toLinearMap.baseChange ℝ
    ((lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
      (sourceLift t a b)) = 0
  rw [markedQuotientPhase_real_map]
  exact realMarkedPolynomialLift_phase filtration generators weights marked weight_pos generator_mem
    t 1 0 1 (by decide) (affineCoefficient t a b)

theorem seedCoordinate_seedVector (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0) (a : ℝ) :
    seedCoordinate η (seedVector a) = a := by
  have he : generators (0 : Fin 1) (0 : Fin 1) = 1 := by
    change (Pi.basisFun ℚ (Fin 1)) 0 0 = 1
    simp
  simp only [seedCoordinate, seedVector, LinearMap.comp_apply, LinearMap.baseChange_tmul,
    realifyFunctional_tmul]
  change a * ((η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) (generators 0))) : ℝ) = a
  rw [hη, he, Rat.cast_one, mul_one]

theorem sourceLift_shift_coordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (t : ℕ) (a : ℝ) (b u : Fin t → ℝ) :
    seedCoordinate η ((markedShiftEval filtration generators weights marked t 0).baseChange ℝ
      (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t u
        (sourceLift t a b))) = a + ∑ i, u i * b i := by
  rw [realMarkedAffineShift_eval_affine filtration generators weights marked weight_pos generator_mem
    t u (sourceLift t a b) (seedVector a) (fun i => seedVector (b i)) (sourceLift_eval t a b)]
  simp only [map_add, map_sum, map_smul, seedCoordinate_seedVector η hη, smul_eq_mul]

theorem shiftedLift_coordinate (η : RationalTorus.BottomQuotient 1 →ₗ[ℚ] ℚ)
    (hη : ∀ x : Seed, η (lieQuotientMap (⊥ : LieIdeal ℚ Seed) x) = x 0)
    (t : ℕ) (a : ℝ) (b u : Fin t → ℝ) :
    realifyFunctional η ((evaluation t).baseChange ℝ
      ((lieQuotientMap (markedShiftSecondIdeal filtration generators weights marked t)).toLinearMap.baseChange ℝ
        (realMarkedAffineShift filtration generators weights marked weight_pos generator_mem t u
          (sourceLift t a b)))) = a + ∑ i, u i * b i := by
  rw [evaluation, markedBaseEvaluation_real_map]
  exact sourceLift_shift_coordinate η hη t a b u

noncomputable def pureOrbit (t : ℕ) (a : ℝ) (b : Fin t → ℝ) :
    (multidegree t).realification.PolynomialOrbit :=
  (multidegree t).realification.polynomialOrbitOfLog
    (monomial (correlationExponent 0 1) (projectedLift t a b)) (by
      apply (multidegree t).realification.monomial_mem_adaptedSubmodule
      simpa only [correlationExponent_apply] using projectedLift_mem t a b)

theorem pureOrbit_eval (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (h n : ℤ) :
    ((multidegree t).realification.polynomialOrbitEval (correlationInput h n) (pureOrbit t a b)).coord =
      (n : ℝ) • projectedLift t a b := by
  change eval (fun i => ((correlationInput h n i : ℤ) : ℚ))
    (monomial (correlationExponent 0 1) (projectedLift t a b)) = _
  rw [eval_correlation_monomial]
  change ((h : ℚ) ^ 0 * (n : ℚ) ^ 1) • projectedLift t a b = _
  rw [pow_zero, pow_one, one_mul]
  simpa only [Rat.cast_intCast] using
    (Rat.cast_smul_eq_qsmul ℝ (n : ℚ) (projectedLift t a b)).symm

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticBoundedFamily
namespace OAI

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

noncomputable def affineElement (t : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) :
    (multidegree t).realification.Group := ⟨n • projectedLift t a b⟩

noncomputable def centeredElement (t m : ℕ) (a : ℝ) (b : Fin t → ℝ) (n : ℝ) (v : Fin t → ℝ) :
    (multidegree t).realification.Group :=
  affineElement t a (fun i => (m : ℝ)⁻¹ * b i) n * parameter t ((m : ℝ) • -v)

end Erdos3.QuadraticMarked

end

section

namespace Erdos3.QuadraticMarked

open NilpotentLieBCHGroup
open scoped BigOperators

noncomputable def latticeCorrection {N : ℕ} (t m : ℕ) (u c : Fin t → ℝ) (h₀ h : ZMod N) :
    (multidegree t).realification.Group :=
  parameter t ((m : ℝ) • fun i => ((-affineCyclicTorusCarry u c h₀ h i : ℤ) : ℝ))

end Erdos3.QuadraticMarked

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeResidualCrossInduction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exp_le_gowers_of_mean_derivative {G : Type*} [AddCommGroup G] [Fintype G]
    (s : ℕ) (f : G → ℂ) {p : ℝ} (hp : 0 ≤ p)
    (hcorr : Real.exp (-p) ≤ 𝔼 k, gowersNorm (s + 1) (multiplicativeDerivative f k)) :
    Real.exp (-p) ≤ gowersNorm (s + 2) f := by
  have hexp : Real.exp (-p) ^ (2 ^ (s + 2)) ≤ Real.exp (-p) ^ (2 ^ (s + 1)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    rw [show s + 2 = (s + 1) + 1 by omega, pow_succ]
    push_cast
    nlinarith [mul_nonneg hp (show (0 : ℝ) ≤ 2 ^ (s + 1) by positivity)]
  have hpower := hexp.trans ((pow_le_pow_left₀ (Real.exp_nonneg _) hcorr _).trans
    (mean_derivative_gowers_power_le s f))
  exact (pow_le_pow_iff_left₀ (Real.exp_nonneg _) (gowersNorm_nonneg (s + 1) f)
    (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0))).mp hpower

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedEarlyStructuralPowerBudget
namespace OAI

section

namespace Erdos3

open VectorPolynomial

theorem preparationCoordinateCap_bounds {I J : Type} {s D t T : ℕ}
    {L : RankPreparationFamily I J s} (h : L.Sized D t) (ht : t ≤ T) (i : Fin s) :
    Fintype.card (L i).Coord ≤ preparationCoordinateCap s D T ∧
      Fintype.card (L i).Column ≤ preparationCoordinateCap s D T ∧
      Fintype.card (L i).Row + 1 ≤ preparationCoordinateCap s D T := by
  obtain ⟨hc, hb, hr⟩ := h.uniform ht i
  dsimp only [preparationCoordinateCap]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedRefilteredLowerNativeDiagram
namespace OAI


section

universe u

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


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.UniformExternalMarkedAffineSliceFreezingDictionary
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

def ExternalMarkedAffineSliceFreezing
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T) (φ : L →ₗ⁅ℚ⁆ T)
    (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (S : T →ₗ[ℚ] L)
    (hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j)
    (l : ℕ) (Tbox : σ → ℝ) (A ε B : ℝ) : Prop :=
  ∃ N Q M m n : ℕ, 0 < N ∧ 0 < Q ∧ (Q : ℝ) ≤ max 1 B ∧ 0 < M ∧ 0 < m ∧ 0 < n ∧
    (Fintype.card (Fin d → Fin (N + 1)) : ℝ) ≤ B ∧
    (Fintype.card (σ → Fin (Q + 1)) : ℝ) ≤ B ∧
    (M : ℝ) ≤ B ∧ (m : ℝ) ≤ B ∧ (n : ℝ) ≤ B ∧
    (Fintype.card ((Fin d → Fin (N + 1)) × Fin n) : ℝ) ≤ B ^ 2 ∧
    ∃ (left : (Fin d → Fin (N + 1)) → D.RealGroup) (right : Fin n → D.RealGroup),
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (left j) = 1 ∧
        ∀ i, |(D.basis.baseChange ℝ).repr (left j).coord i| ≤ B) ∧
      (∀ j, realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
          (hM := F.lowerCentralSeries_eq_bot) φ (right j) = 1 ∧
        (∀ i, |(D.basis.baseChange ℝ).repr (right j).coord i| ≤ B) ∧
        (D.basis.baseChange ℝ).equivFun (right j).coord ∈ realDenominatorGrid m) ∧
      ∀ (E : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (EF : (F.realification.adaptedPolynomialFiltration w).Group)
        (R : (D.filtration.realification.adaptedPolynomialFiltration w).Group)
        (RF : (F.realification.adaptedPolynomialFiltration w).Group),
        D.filtration.PolynomialSlowBound D.basis w Tbox A E →
        F.PolynomialSlowBound c w Tbox A EF →
        D.filtration.PolynomialRationalGrid D.basis w l R →
        F.PolynomialRationalGrid c w l RF →
        D.filtration.realPolynomialGroupMap F φ hφ w E = EF →
        D.filtration.realPolynomialGroupMap F φ hφ w R = RF →
        (∀ i j,
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedLeft F w S hS EF (left i)) = EF ∧
          D.filtration.realPolynomialGroupMap F φ hφ w
            (D.filtration.frozenMarkedRight F w S hS RF (right j)) = RF) ∧
        ∀ (tests : X → D.Niltest w) (physical : (σ → ℤ) → X)
          (weight : (σ → ℤ) → ℂ) (Bweight Bobs Lip : ℝ),
          0 ≤ Bweight → 0 ≤ Bobs → 0 ≤ Lip →
          (∀ x : σ → ℤ, (∀ i, |(x i : ℝ)| ≤ Tbox i) → ‖weight x‖ ≤ Bweight) →
          (∀ z, ((tests z).normBound : ℝ) ≤ Bobs) →
          (∀ z, ((tests z).lipBound : ℝ) ≤ Lip) →
          ∀ (g P : (D.filtration.realification.adaptedPolynomialFiltration w).Group),
          E * P * R = g →
          ∀ Nparent : σ → ℕ, (∀ i, 0 < Nparent i) →
          ∀ (origin : σ → ℤ) (step : ℕ),
          (∀ i v, v < Nparent i → |(origin i : ℝ) + step * v| ≤ Tbox i) →
          (∀ i, (step : ℝ) * Nparent i ≤ 2 * Tbox i) →
          (∀ i, 2 * (M : ℝ) ≤ (1 / (Q : ℝ)) * Nparent i) →
          ∀ τ θ Sscore : ℝ, 0 ≤ τ → 0 < θ →
          (Sscore ≤ 𝔼 x : (∀ i, Fin (Nparent i)),
            (weight (affineParentIntegerPoint Nparent origin step x) *
              (tests (physical (affineParentIntegerPoint Nparent origin step x))).observable
                (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                  (fun i => (affineParentIntegerPoint Nparent origin step x i : ℝ)) g))).re) →
          τ + Bweight * (Lip * ε) + (Bweight * Bobs) * θ < Sscore →
          ∃ A : ResidueBoxSlice Nparent M, (∀ i, 0 < A.length i) ∧
            (∀ i, θ * Nparent i / (4 * M * Q * (Fintype.card σ + 1 : ℝ)) ≤ A.length i) ∧
            ∃ i j,
              (∀ x : ∀ i, Fin (A.length i),
                ‖(tests (physical (A.affineIntegerPoint origin step x))).observable
                    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                      (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                    F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)‖ ≤ Lip * ε) ∧
              (∀ x : ∀ i, Fin (A.length i),
                ‖weight (A.affineIntegerPoint origin step x) *
                    (tests (physical (A.affineIntegerPoint origin step x))).observable
                      (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w
                        (fun i => (A.affineIntegerPoint origin step x i : ℝ)) g)) -
                  weight (A.affineIntegerPoint origin step x) *
                    (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                      F w S hS EF RF P (left i) (right j)
                      (A.affineIntegerPoint origin step x)‖ ≤ Bweight * (Lip * ε)) ∧
              τ < 𝔼 x : (∀ i, Fin (A.length i)),
                (weight (A.affineIntegerPoint origin step x) *
                  (tests (physical (A.affineIntegerPoint origin step x))).markedFrozenValue
                    F w S hS EF RF P (left i) (right j)
                    (A.affineIntegerPoint origin step x)).re

theorem BoundedCellMarkedPolynomialFreezing.external_affine_slice
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.BoundedCellMarkedPolynomialFreezing F c φ hφ w S hS l Tbox A ε B)
    (hT : ∀ i, 0 < Tbox i) (hε : 0 ≤ ε) :
    D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox A ε B := by
  obtain ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, hfreeze⟩ := hfreeze
  refine ⟨N, Q, M, m, n, hN, hQ, hQb, hM, hm, hn, hNc, hQc, hMb, hmb, hnb,
    hpair, left, right, hl, hr, ?_⟩
  intro E EF R RF hE hEF hR hRF hEproj hRproj
  obtain ⟨leftLabel, rightLabel, hmarks, herror⟩ := hfreeze E EF R RF hE hEF hR hRF hEproj hRproj
  refine ⟨hmarks, ?_⟩
  intro tests physical weight Bweight Bobs Lip hBw hBo hLip hweight hnorm hlip
    g P hfac Nparent hNp origin step hparent hwidth hlarge τ θ Sscore hτ hθ hscore hbudget
  let observed : (σ → ℤ) → ℂ := fun x => (tests (physical x)).observable
    (QuotientGroup.mk (D.filtration.adaptedPolynomialRealValueHom w (fun i => (x i : ℝ)) g))
  let frozen := fun i j x => (tests (physical x)).markedFrozenValue
    F w S hS EF RF P (left i) (right j) x
  let weighted := fun x => weight x * observed x
  let weightedFrozen := fun i j x => weight x * frozen i j x
  have hcap (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i) :
      (1 : ℝ) * (weighted x).re ≤ Bweight * Bobs := by
    have ho : ‖observed x‖ ≤ Bobs := ((tests (physical x)).norm_le _).trans (hnorm _)
    calc
      _ = (weighted x).re := one_mul _
      _ ≤ ‖weighted x‖ := (le_abs_self _).trans (Complex.abs_re_le_norm _)
      _ = ‖weight x‖ * ‖observed x‖ := norm_mul _ _
      _ ≤ Bweight * Bobs := mul_le_mul (hweight x hx) ho (norm_nonneg _) hBw
  have hpoint (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖observed x - frozen (leftLabel a) (rightLabel (fun i => (x i : ZMod M))) x‖ ≤
        Lip * ε :=
    (herror (tests (physical x)) g P hfac a x hx ha).trans
      (mul_le_mul_of_nonneg_right (hlip _) hε)
  have hclose (a) (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ Tbox i)
      (ha : ∀ i, |(x i : ℝ) - normalizedRealBoxGrid Tbox Q a i| ≤ Tbox i * (2 / Q)) :
      ‖weighted x - weightedFrozen (leftLabel a)
        (rightLabel (fun i => (x i : ZMod M))) x‖ ≤ Bweight * (Lip * ε) := by
    change ‖weight x * observed x - weight x * frozen _ _ x‖ ≤ _
    rw [← mul_sub, norm_mul]
    exact mul_le_mul (hweight x hx) (hpoint a x hx ha) (norm_nonneg _) hBw
  obtain ⟨A, hlen, hlong, z, hcell, herr, hretained⟩ :=
    exists_long_affine_residue_cell_frozen_score_with_cell
      Nparent hNp M Q hM hQ origin step Tbox hT hparent hwidth hlarge
      (fun _ => (1 : ℝ)) weighted weightedFrozen leftLabel rightLabel
      (mul_nonneg hBw hBo) hτ (mul_nonneg hBw (mul_nonneg hLip hε)) hθ
      (fun _ _ => by norm_num) hcap hclose
      (by simpa only [one_mul] using hscore) hbudget
  refine ⟨A, hlen, hlong, leftLabel z,
    rightLabel (fun i => ((origin i + (step : ℤ) * A.start i : ℤ) : ZMod M)), ?_, herr, ?_⟩
  · intro x
    have hx (i) : |(A.affineIntegerPoint origin step x i : ℝ)| ≤ Tbox i := by
      simpa only [ResidueBoxSlice.affineIntegerPoint, Int.cast_add, Int.cast_mul,
        Int.cast_natCast] using hparent i (A.point x i).val (A.point x i).isLt
    have hp := hpoint z (A.affineIntegerPoint origin step x) hx (hcell x)
    simpa only [A.affineIntegerPoint_residue origin step x] using hp
  · simpa only [one_mul] using hretained

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct NNReal BigOperators

namespace ExternalMarkedAffineSliceFreezing

theorem exists_dictionary
    {X σ κ L T : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
    [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {F : NilpotentLieFiltration T t} {c : Basis κ ℚ T} {φ : L →ₗ⁅ℚ⁆ T}
    {hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j}
    {w : σ → ℕ} {S : T →ₗ[ℚ] L}
    {hS : ∀ j, ∀ y ∈ F.layer j, S y ∈ D.filtration.layer j}
    {l : ℕ} {Tbox : σ → ℝ} {A ε B : ℝ}
    (hfreeze : D.ExternalMarkedAffineSliceFreezing (X := X) F c φ hφ w S hS l Tbox A ε B) :
    Nonempty (Dictionary (X := X) D F c φ hφ w S hS l Tbox A ε B) := by
  obtain ⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hQbound,
    hmodulus, hdenominator, hrightCount, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightCountBound, hpairCard, left, right, hleft, hright,
    hselect⟩ := hfreeze
  exact ⟨⟨grid, Q, modulus, denominator, rightCount, hgrid, hQ, hmodulus,
    hdenominator, hrightCount, hQbound, hgridCard, hcellCard, hmodulusBound,
    hdenominatorBound, hrightCountBound, hpairCard, left, right, hleft, hright,
    hselect⟩⟩

end ExternalMarkedAffineSliceFreezing

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeMarkedFreezingPhysicalData
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {X σ κ L T : Type} [Fintype σ] [DecidableEq σ] [Fintype κ] [DecidableEq κ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing T] [LieAlgebra ℚ T]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {s d t : ℕ} (D : RationalFilteredNilmanifold L s d)
    (F : NilpotentLieFiltration T t) (c : Basis κ ℚ T)
    (φ : L →ₗ⁅ℚ⁆ T) (hφ : ∀ j, ∀ x ∈ D.filtration.layer j, φ x ∈ F.layer j)
    (w : σ → ℕ) (l : ℕ) (Tbox : σ → ℝ) (slow p : ℝ) (C : ℕ)

structure NativeMarkedFreezingPhysicalData where
  sectionMap : T →ₗ[ℚ] L
  section_filtered : ∀ j, ∀ y ∈ F.layer j, sectionMap y ∈ D.filtration.layer j
  section_rightInverse : Function.RightInverse sectionMap φ
  section_height : ∀ i j, RationalHeightLE
    (LinearMap.toMatrix c D.basis sectionMap i j)
    (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊)
  section_height_bound :
    (rationalKernelHeight (Fintype.card κ) ⌈Real.exp p⌉₊ : ℝ) ≤
      Real.exp (nativeMarkedFreezingPhysicalParameter p C)
  dictionary : ExternalMarkedAffineSliceFreezing.Dictionary (X := X)
    D F c φ hφ w sectionMap section_filtered l Tbox slow
    (Real.exp (-((p + 2) ^ 3))) (Real.exp ((p + C) ^ C))
  denominator_bound :
    ((matrixDenominator (LinearMap.toMatrix c D.basis sectionMap) * l *
      dictionary.denominator : ℕ) : ℝ) ≤
        Real.exp (nativeMarkedFreezingPhysicalParameter p C)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PreparedFamilyCanonicalGeometry
namespace OAI

section

namespace Erdos3.RankPreparationFamily
open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.exists_canonical_sampler_geometry
    {p : ℝ} {R M : ℕ} (hL : L.PreparedHeights p R)
    (hp : 0 ≤ p) (hR : 1 ≤ R)
    (hM : ∀ j, Fintype.card (L j).Coord ≤ M) :
    ∃ (b : ∀ j, Basis (Fin (preparedSamplerTransverse L j)) ℝ
        (euclideanSubspace (L j).space)ᗮ)
      (_o : ∀ j, OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
        (euclideanSubspace (L j).space))
      (_bW : ∀ j, Basis (PreparedSamplerContinuous L j) ℤ
        (latticeSection (standardEuclideanLattice (L j).Coord)
          (euclideanSubspace (L j).space))),
      (∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (L j).space)) ∧
      (∀ j z, ‖normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j) z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j z, ‖(normalizedOrthogonalChart (euclideanSubspace (L j).space) (b j)).symm z‖ ≤
        Real.exp (allocatedUniformChartLog (M : ℝ)) * ‖z‖) ∧
      (∀ j, 0 ≤ mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ∧
        mixedDensityCovolumeRatio (euclideanSubspace (L j).space) (b j) ≤
          Real.exp (allocatedUniformChartLog (M : ℝ))) := by
  let := fun j => hL.lattice_full L hp hR j
  obtain ⟨b, hb, hf, hi, hv⟩ := hL.exists_uniform_charts L hp hR
    (fun j => Nat.cast_le.mpr (hM j))
  let o (j : Fin m) : OrthonormalBasis (PreparedSamplerContinuous L j) ℝ
      (euclideanSubspace (L j).space) :=
    (stdOrthonormalBasis ℝ (euclideanSubspace (L j).space)).reindex
      (finCongr (L j).euclidean_finrank)
  let bW (j : Fin m) : Basis (PreparedSamplerContinuous L j) ℤ
      (latticeSection (standardEuclideanLattice (L j).Coord)
        (euclideanSubspace (L j).space)) :=
    (finiteLatticeBasis (latticeSection (standardEuclideanLattice (L j).Coord)
      (euclideanSubspace (L j).space))).reindex (finCongr (L j).euclidean_finrank)
  exact ⟨b, o, bW, hb, hf, hi, hv⟩

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CommonRefilteredFactorsSymbolTransport
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped Classical

variable {σ R : Type*} [CommRing R]

namespace NilpotentLieFiltration

open Module VectorPolynomial

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem weightedAdaptedRealChartHom_nested_nested_zero
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
      (fun _ : {i // keepLater i} => 1)
      (nestedFrozenCoordinate keepOriginal keepLater 0)
      (nestedFrozenCoordinate_support keepOriginal keepLater 0) g =
    F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
      (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLong i} => 1) (nestedFrozenCoordinate keepOriginal keepLong 0)
        (nestedFrozenCoordinate_support keepOriginal keepLong 0) g) := by
  have hcomp := F.weightedAdaptedRealChartHom_comp
    (fun _ : {i // keepOriginal i} => 1) (fun _ : {i // keepLong i} => 1)
    (fun _ : {i // keepLater i} => 1)
    (nestedFrozenCoordinate keepOriginal keepLong 0)
    (nestedFrozenCoordinate keepLong keepLater 0)
    (nestedFrozenCoordinate_support keepOriginal keepLong 0)
    (nestedFrozenCoordinate_support keepLong keepLater 0)
    (weightedRealChart_comp_support _ _ _ _ _
      (nestedFrozenCoordinate_support keepOriginal keepLong 0)
      (nestedFrozenCoordinate_support keepLong keepLater 0)) g
  simpa only [nestedFrozenCoordinate_zero_comp keepOriginal keepLong keepLater hsub] using hcomp

theorem realPolynomialSymbolHom_nested_frozenCoordinate_independent
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepOriginal keepLater : σ → Prop)
    (fixed fixed' : {i : {i // keepOriginal i} // ¬keepLater i.val} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed)
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed')
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed') g) := by
  rw [F.realPolynomialSymbolHom_weightedAdaptedRealChart,
    F.realPolynomialSymbolHom_weightedAdaptedRealChart]
  have htop :
      (fun i => weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
        (nestedFrozenCoordinate keepOriginal keepLater fixed i)) =
      (fun i => weightedHomogeneousComponent (fun _ : {i // keepLater i} => 1) 1
        (nestedFrozenCoordinate keepOriginal keepLater fixed' i)) := by
    funext i
    exact nestedFrozenCoordinate_top_independent keepOriginal keepLater fixed fixed' i
  congr 1
  congr 1

theorem realPolynomialSymbolHom_nested_nested_frozenCoordinate
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (keepOriginal keepLong keepLater : σ → Prop)
    (hsub : ∀ i, keepLater i → keepLong i)
    (fixed : {i : {i // keepOriginal i} // ¬keepLater i.val} → ℝ)
    (g : (F.realification.adaptedPolynomialFiltration
      (fun _ : {i // keepOriginal i} => 1)).Group) :
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
        (fun _ : {i // keepLater i} => 1)
        (nestedFrozenCoordinate keepOriginal keepLater fixed)
        (nestedFrozenCoordinate_support keepOriginal keepLater fixed) g) =
    F.realPolynomialSymbolHom b ω hF (fun _ : {i // keepLater i} => 1)
      (F.weightedAdaptedRealChartHom (fun _ : {i // keepLong i} => 1)
        (fun _ : {i // keepLater i} => 1) (nestedFrozenCoordinate keepLong keepLater 0)
        (nestedFrozenCoordinate_support keepLong keepLater 0)
        (F.weightedAdaptedRealChartHom (fun _ : {i // keepOriginal i} => 1)
          (fun _ : {i // keepLong i} => 1) (nestedFrozenCoordinate keepOriginal keepLong 0)
          (nestedFrozenCoordinate_support keepOriginal keepLong 0) g)) := by
  rw [← F.weightedAdaptedRealChartHom_nested_nested_zero keepOriginal keepLong keepLater hsub g]
  exact F.realPolynomialSymbolHom_nested_frozenCoordinate_independent
    b ω hF keepOriginal keepLater fixed 0 g

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CertifiedFullChartAffineTerminal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators Classical

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedAffineMapChart_support
    (P : ∀ j, (J j → ℝ) →ₗ[ℝ] (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (v : X ⊕ (Σ j, J j)) :
    fullTaggedAffineMapChart J P c v ∈
      weightedSupportLE (fullTaggedVariableWeight J) (fullTaggedVariableWeight J v) := by
  cases v with
  | inl x => exact weightedSupportLE_X _ _
  | inr v =>
    apply (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    apply (weightedSupportLE _ _).sum_mem
    intro a _
    exact (weightedSupportLE _ _).smul_mem _
      (weightedSupportLE_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr ⟨v.1, a⟩))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialIdentity
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace VectorPolynomial

noncomputable def integerCoordinates {I J : Type*} [Fintype J] (ip : J → MvPolynomial I ℤ) :
    VectorPolynomial I ℝ (J → ℝ) :=
  ofCoordinates (Pi.basisFun ℝ J) (fun j => MvPolynomial.map (Int.castRingHom ℝ) (ip j))

end VectorPolynomial

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PreparedIntegerRemainder
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} [Fintype J] [DecidableEq J] {m : ℕ}
variable (L : RankPreparationFamily X J m)

noncomputable def integerRemainder (ip : J → MvPolynomial X ℤ)
    (β : ∀ u, (L u).Coord → MvPolynomial X ℤ) : J → MvPolynomial X ℤ :=
  ip + ∑ u, coordinateCopySum (L u).label (β u)

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PreparedPolynomialPullback
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators TensorProduct

namespace RankPreparationLayer

variable {X Y J : Type}

noncomputable def pullback (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    RankPreparationLayer Y J where
  Coord := L.Coord
  Column := L.Column
  Row := L.Row
  coordFinite := L.coordFinite
  columnFinite := L.columnFinite
  rowFinite := L.rowFinite
  label := L.label
  basis := L.basis
  rows := L.rows
  poly := substitute f L.poly

@[simp] theorem pullback_space (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    (L.pullback f).space = L.space := rfl

@[simp] theorem pullback_rank (L : RankPreparationLayer X J) (f : X → MvPolynomial Y ℝ) :
    (L.pullback f).rank = L.rank := rfl

end RankPreparationLayer

namespace RankPreparationFamily

variable {X Y J : Type} {m : ℕ}

noncomputable def pullback (L : RankPreparationFamily X J m) (f : X → MvPolynomial Y ℝ) :
    RankPreparationFamily Y J m := fun u => (L u).pullback f

end RankPreparationFamily
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SpatialAffineFullMass
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct
open VectorPolynomial

namespace RankPreparationFamily

variable {I J K : Type} {s : ℕ}

@[simp] theorem pullback_potential (L : RankPreparationFamily I J s)
    (f : I → MvPolynomial K ℝ) : (L.pullback f).potential = L.potential := rfl

end RankPreparationFamily

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NativeIntegerChartNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute polynomialOrbitRealChart
  weightedAdaptedRealChartHom realPolynomialSymbolHom

variable {L σ τ : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
  (Q : D.Niltest w) (v : τ → ℕ) (β : σ → MvPolynomial τ ℤ)
  (hβ : ∀ i, integerSampledRealChart β i ∈ weightedSupportLE v (w i))

theorem integerChartPullback_orbit_eq_of_orbit_eq (R : D.Niltest w)
    (hQR : Q.orbit = R.orbit) :
    (Q.integerChartPullback v β hβ).orbit = (R.integerChartPullback v β hβ).orbit := by
  simp only [integerChartPullback_orbit, hQR]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankPreparationPaddedFreezingLifts
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators TensorProduct

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

noncomputable def padCoordInclusion (hmq : m ≤ q) :
    (Σ j, (L j).Coord) → Σ j, (L.pad q j).Coord := fun a =>
  ⟨a.1.castLE hmq, cast (congrArg RankPreparationLayer.Coord
    (L.pad_apply_castLE hmq a.1).symm) a.2⟩

theorem padCoord_isLt (a : Σ j, (L.pad q j).Coord) : a.1.val < m := by
  rcases a with ⟨j, i⟩
  by_cases hj : j.val < m
  · exact hj
  · exact PEmpty.elim (cast (congrArg RankPreparationLayer.Coord
      (L.pad_apply_ge j (by omega))) i)

noncomputable def padCoordRestriction (a : Σ j, (L.pad q j).Coord) :
    Σ j, (L j).Coord :=
  ⟨⟨a.1.val, L.padCoord_isLt a⟩, cast (congrArg RankPreparationLayer.Coord
    (L.pad_apply_lt a.1 (L.padCoord_isLt a))) a.2⟩

@[simp] theorem padCoordRestriction_inclusion (hmq : m ≤ q)
    (a : Σ j, (L j).Coord) :
    L.padCoordRestriction (L.padCoordInclusion hmq a) = a := by
  rcases a with ⟨j, i⟩
  dsimp only [padCoordInclusion, padCoordRestriction]
  apply Sigma.ext
  · exact Fin.ext rfl
  exact (cast_heq _ _).trans (cast_heq _ _)

@[simp] theorem padCoordInclusion_restriction (hmq : m ≤ q)
    (a : Σ j, (L.pad q j).Coord) :
    L.padCoordInclusion hmq (L.padCoordRestriction a) = a := by
  rcases a with ⟨j, i⟩
  dsimp only [padCoordInclusion, padCoordRestriction]
  apply Sigma.ext
  · exact Fin.ext rfl
  exact (cast_heq _ _).trans (cast_heq _ _)

noncomputable def padCoordEquiv (hmq : m ≤ q) :
    (Σ j, (L.pad q j).Coord) ≃ Σ j, (L j).Coord where
  toFun := L.padCoordRestriction
  invFun := L.padCoordInclusion hmq
  left_inv := L.padCoordInclusion_restriction hmq
  right_inv := L.padCoordRestriction_inclusion hmq

@[simp] theorem padCoordEquiv_index (hmq : m ≤ q) (a : Σ j, (L.pad q j).Coord) :
    ((L.padCoordEquiv hmq a).1 : ℕ) = a.1.val := rfl

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial

variable {X J : Type} {m q : ℕ} (L : RankPreparationFamily X J m)

noncomputable def unpadCenter (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) : ∀ j, (L j).Coord → ℝ := fun j i =>
  c ((L.padCoordEquiv hmq).symm ⟨j, i⟩).1 ((L.padCoordEquiv hmq).symm ⟨j, i⟩).2

@[simp] theorem unpadCenter_equiv (hmq : m ≤ q)
    (c : ∀ j, (L.pad q j).Coord → ℝ) (a : Σ j, (L.pad q j).Coord) :
    L.unpadCenter hmq c (L.padCoordEquiv hmq a).1 (L.padCoordEquiv hmq a).2 =
      c a.1 a.2 := by
  exact congrArg (fun b : Σ j, (L.pad q j).Coord => c b.1 b.2)
    ((L.padCoordEquiv hmq).symm_apply_apply a)

end Erdos3.RankPreparationFamily

end

section

namespace Erdos3.RankPreparationFamily

open VectorPolynomial
open scoped BigOperators

variable {X J : Type} {Vars : Type*} {m q : ℕ}
    (L : RankPreparationFamily X J m)

noncomputable def unpadFreezingLifts (hmq : m ≤ q)
    (β : ∀ j, (L.pad q j).Coord → MvPolynomial Vars ℤ) :
    ∀ j, (L j).Coord → MvPolynomial Vars ℤ := fun j i =>
  β (L.padCoordInclusion hmq ⟨j, i⟩).1 (L.padCoordInclusion hmq ⟨j, i⟩).2

end Erdos3.RankPreparationFamily

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
variable {σ τ : Type*} {s d : ℕ}

theorem symbolicShearPrefixSubstitution_weighted_degree (p : τ → ℕ) (w : Fin d → ℕ) (i : Fin d)
    (v : τ ⊕ Fin d) :
    symbolicShearPrefixSubstitution i v ∈
      weightedSupportLE (weightedPatchVariableWeight p w i) (Sum.elim p w v) := by
  classical
  cases v with
  | inl a => exact weightedSupportLE_X _ (Sum.inl a)
  | inr j =>
      dsimp only [symbolicShearPrefixSubstitution, Sum.elim_inr]
      split_ifs with h
      · have hj : earlierSlot i ⟨j.val, h⟩ = j := Fin.ext rfl
        have hx := weightedSupportLE_X (R := ℝ)
          (weightedPatchVariableWeight p w i) (Sum.inr ⟨j.val, h⟩)
        change _ ∈ weightedSupportLE _ (w (earlierSlot i ⟨j.val, h⟩)) at hx
        rw [hj] at hx
        exact hx
      · exact Submodule.zero_mem _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedEarlyLateSamplerGeometry
namespace OAI

section

namespace Erdos3.RankPreparationFamily

open Module Submodule VectorPolynomial

variable {X J : Type} {m : ℕ} (L : RankPreparationFamily X J m)

theorem PreparedHeights.mono_parameter
    {pPrep pLate : ℝ} {R : ℕ} (hL : L.PreparedHeights pPrep R)
    (hpPrep : 0 ≤ pPrep) (hPrepLate : pPrep ≤ pLate) :
    L.PreparedHeights pLate R := by
  intro j
  apply (hL j).mono_height
  unfold preparationHeight
  apply Nat.floor_mono
  apply Real.exp_le_exp.mpr
  exact pow_le_pow_left₀ (by linarith : 0 ≤ pPrep + 2)
    (by linarith : pPrep + 2 ≤ pLate + 2) _

end Erdos3.RankPreparationFamily

end

end OAI
end


