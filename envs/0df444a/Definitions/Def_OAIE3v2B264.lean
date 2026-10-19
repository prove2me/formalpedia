-- Prove2me | Definitions.Def_OAIE3v2B264
-- name    : OAIE3v2B264
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:28:09.661735+00:00
-- url     : https://prove2.me/theorems/a944ee3d-7791-40b6-ae05-c7117a3e4b8e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 272 of 311
-- statement:
--   Definitions bundle 272 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B255`, `OAIE3v2B256`, `OAIE3v2B257`, `OAIE3v2B303` of this split.
--
--   Modules: `Estimates/AllocatedExternalCandidateAxisFreezingConclusion.lean`, `Estimates/AllocatedExternalCandidatePrecenterNativePartners.lean`, `Estimates/AllocatedExternalCandidateTaggedSourceEvaluation.lean`, `Estimates/NativeProductVerticalization.lean`, `Geometry/AllocatedExternalCandidateRefilteredSupportedStep.lean`, `Geometry/AllocatedExternalCandidateSpatialNativeBudget.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Linear/InducedUnitRankFamily.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/PolynomialPatchTaggedBufferedScore.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B255
import Definitions.Def_OAIE3v2B256
import Definitions.Def_OAIE3v2B257
import Definitions.Def_OAIE3v2B303

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.InducedUnitRankFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct BigOperators NNReal

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {τ K I : Type} [Fintype I] {s r N n degree : ℕ} [NeZero N]
  {b p q P Z : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
  {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
  (D : R.CommonData P) (t : ℕ)
  (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
  (f : τ → K → ZMod N → ℂ)

def HasUnitRankInducedCorrelationFamily (B C : ℝ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ (k : ℝ) ≤ Real.exp B ∧
    ∃ F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ
        ((I × I) × (I × Fin k)) C,
      ∃ (m : ℕ) (_hm : 0 < m), (m : ℝ) ≤ Real.exp B ∧
        ∃ d : ℕ, ∃ E : RationalFilteredNilmanifold
          (MarkedShiftQuotient D.coefficientFreeFiltration D.coefficientFreeGenerator
            D.coefficientWeight D.coefficientIsDependent t) (s + 1) d,
          ∃ M : E.MultidegreeStructure (mixedCorrelationDegree s),
            M.filtration = D.markedQuotientMultidegree t ∧ M.ComplexityLE B ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
               D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
               D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
                  IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             letI := E.metricSpace
             ∃ G : Fin k → E.Space → ℂ,
               (∀ j z, ‖G j z‖ ≤ 2) ∧
               (∀ j, LipschitzWith ⟨Real.exp B, Real.exp_nonneg _⟩ (G j)) ∧
               ∀ z, Nonempty (NativeVectorCorrelation degree N B
                 (fun ij : (K × Fin k) × ((I × I) × (I × Fin k)) => fun a =>
                   f z ij.1.1 a * star (G ij.1.2 (QuotientGroup.mk
                     ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
                       (correlationInput ((h z).val : ℤ) (a.val : ℤ))
                       (D.localPhaseMarkedOrbit t x y u c h₀ m)))) *
                   star (F.eval z ij.2 (fun _ => (a.val : ℤ))))))

theorem HasCommonInducedCorrelationFamily.combineLower
    (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
    {e k : ℕ} (Q : RationalFilteredNilmanifold D.DependentQuotient s e)
    [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
    [TopologicalSpace (ℝ ⊗[ℚ] D.DependentQuotient)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.DependentQuotient)]
    [T2Space (ℝ ⊗[ℚ] D.DependentQuotient)]
    {S : Subgroup A.RealGroup} {T : Subgroup Q.RealGroup}
    (V : A.UnitVerticalObservable S I Z) (U : Q.UnitVerticalObservable T (Fin k) Z)
    (hφ : A.lattice ≤ Q.lattice.comap (mapOfSteps
      (hL := A.filtration.lowerCentralSeries_eq_bot)
      (hM := Q.filtration.lowerCentralSeries_eq_bot) D.dependentQuotientMap))
    (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    {B C : ℝ} (hk : 0 < k) (hkB : (k : ℝ) ≤ Real.exp B)
    (F : NativeUnitRankFamily (fun _ : Unit => 1) s r τ ((I × I) × (I × Fin k)) C)
    (hF : ∀ z ij w, F.eval z ij w =
      (V.observable ij.1.1 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (v z))) *
        star (V.observable ij.1.2 (QuotientGroup.mk
          (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))) *
      mapDifferenceObservable V U D.dependentQuotientMap hφ ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))
    (hcommon : D.HasCommonInducedCorrelationFamily (degree := degree)
      t A Q V U hφ x y u c h₀ h a v f B) :
    D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree) t x y u c h₀ h f B C := by
  obtain ⟨m, hm, hmB, d₁, _, E₁, M, hMF, hM, hdata⟩ := hcommon
  refine ⟨k, hk, hkB, F, m, hm, hmB, d₁, E₁, M, hMF, hM, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E₁.basis
  let := E₁.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hdata
  refine ⟨G, hGn, hGL, ?_⟩
  intro z
  exact NativeVectorCorrelation.exists_combined_factor_correlation (f z)
    (fun j w => G j (QuotientGroup.mk
      ((D.markedQuotientMultidegree t).realification.polynomialOrbitEval
        (correlationInput ((h z).val : ℤ) (w.val : ℤ))
        (D.localPhaseMarkedOrbit t x y u c h₀ m))))
    (fun (ij : I × I) w => V.observable ij.1 (QuotientGroup.mk
      (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (w.val : ℤ)) (v z))) *
      star (V.observable ij.2 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
          (fun _ => (w.val : ℤ)) (a z)))))
    (fun (ij : I × Fin k) w => mapDifferenceObservable V U D.dependentQuotientMap hφ ij
      (QuotientGroup.mk (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (fun _ => (w.val : ℤ)) (a z))))
    (fun ij w => F.eval z ij (fun _ => (w.val : ℤ))) Prod.snd
    (fun ij w => hF z ij (fun _ => (w.val : ℤ))) (Classical.choice (hcorr z))

variable (A : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : A.DegreeRankStructure (r + 1))
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : A.UnitVerticalObservable (T.realSubgroup s (r + 1)) I Z)
  (a v : τ → A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))

theorem HasCoveredInducedCorrelationFamily.combineLower
    {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hcovered : D.HasCoveredInducedCorrelationFamily (degree := degree)
      t A T V x y u c h₀ h a v f B)
    {L : Type} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
    (E : RationalFilteredNilmanifold L s d) (U : E.DegreeRankStructure (r + 1))
    (hfirst : E.HasLowerRankOrbitFamily U (fun _ : Unit => 1)
      (fun z (ij : I × I) w => V.observable ij.1 (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (v z))) *
        star (V.observable ij.2 (QuotientGroup.mk
          (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w (a z))))) C) :
    D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree)
      t x y u c h₀ h f B (productNiltestBudget (C + B + 2)) := by
  obtain ⟨Λ, _, l, hl, hin, hout, _, e, _, Q, S, _, _, hφ, V₀, _, hVobs, hcoeff⟩ := hcovered
  let A₀ := A.withLattice Λ l hl hin hout
  let T₀ := T.withLattice Λ l hl hin hout
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.DependentQuotient)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.DependentQuotient) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨k, hk, hkB, U₀, hcommon, hsecond⟩ := hcoeff
  obtain ⟨F, _, hF⟩ := exists_binary_lower_rank_unit_family (p := C + B + 2) E A₀ U T₀
    (fun _ : Unit => 1) _ _ (by linarith : 2 ≤ C + B + 2)
    (hfirst.mono (show C ≤ C + B + 2 by linarith))
    (hsecond.mono (show B ≤ C + B + 2 by linarith))
  apply HasCommonInducedCorrelationFamily.combineLower D t x y u c h₀ h f
    A₀ Q V₀ U₀ hφ a v hk hkB F ?_ hcommon
  intro z ij w
  rw [hF]
  have hvalue (i : I) (o : A.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) :
      V₀.observable i (QuotientGroup.mk
        (A₀.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w o)) =
      V.observable i (QuotientGroup.mk
        (A.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) w o)) := hVobs i _
  simp only [hvalue]
  rfl

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeProductVerticalization
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff
  NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem HasUnitRankInducedCorrelationFamily.combineMixed
    {τ I : Type} [Fintype I] {s r N degree : ℕ} [NeZero N]
    {b p q P B C Q : ℝ} {W : NativeDegreeRankFamily s (r + 1) (ZMod N) b}
    {out : Fin W.outputDim} {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
    (D : R.CommonData P) (t : ℕ)
    (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
    (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
    (u c : Fin t → ℝ) (h₀ : ZMod N) (h : τ → ZMod N)
    (f : τ → ZMod N → ℂ) (χ : NativeMultidegreeNilcharacter (mixedCorrelationDegree s) Q)
    (hB : 0 ≤ B)
    (hfamily : D.HasUnitRankInducedCorrelationFamily (I := I) (degree := degree)
      t x y u c h₀ h
      (fun z i a => f z a * star (χ.evalCyclic N i (correlationInput (h z) a))) B C) :
    HasBoundedProductCorrelation (I := I) (s := s) (r := r) (degree := degree)
      h f χ.outputDim B C (productNiltestBudget (Q + B + 2 + 4)) := by
  obtain ⟨k, hk, hkB, F, m, hm, hmB, d, E, M, hMF, hM, hdata⟩ := hfamily
  let := moduleTopology ℝ (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] MarkedShiftQuotient D.coefficientFreeFiltration
    D.coefficientFreeGenerator D.coefficientWeight D.coefficientIsDependent t) :=
      IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  let := E.metricSpace
  obtain ⟨G, hGn, hGL, hcorr⟩ := hdata
  let F₀ := (D.markedQuotientMultidegree t).realification
  have hF : F₀ = M.filtration.realification := congrArg MultidegreeLieFiltration.realification hMF.symm
  let g := F₀.orbitEquivOfEq hF (D.localPhaseMarkedOrbit t x y u c h₀ m)
  obtain ⟨Ω, hΩ⟩ := χ.exists_product_with_bounded_family E M
    (mixedCorrelationDegree_sum s).symm g G hB hM hGn hGL
  refine ⟨k, hk, hkB, F, Ω, ?_⟩
  have hprod (ij : Fin χ.outputDim × Fin k) (a : Fin 2 → ℤ) :
      Ω.eval ij a = χ.eval ij.1 a * G ij.2 (QuotientGroup.mk
        (F₀.polynomialOrbitEval a (D.localPhaseMarkedOrbit t x y u c h₀ m))) / 2 :=
    (hΩ ij a).trans (congrArg (fun v : E.RealGroup => χ.eval ij.1 a * G ij.2 (QuotientGroup.mk v) / 2)
      (F₀.orbitEquivOfEq_eval hF (D.localPhaseMarkedOrbit t x y u c h₀ m) a))
  have hchi (i : Fin χ.outputDim) (z : τ) (a : ZMod N) :
      χ.evalCyclic N i (correlationInput (h z) a) =
        χ.eval i (correlationInput ((h z).val : ℤ) (a.val : ℤ)) := by
    unfold NativeMultidegreeNilcharacter.evalCyclic
    exact congrArg (χ.eval i) (map_correlationInput (fun z : ZMod N => (z.val : ℤ)) (h z) a)
  intro z
  obtain ⟨Cz⟩ := hcorr z
  obtain ⟨Dz⟩ := Cz.exists_half_signal
  refine ⟨Dz.mapCoordinates _ id ?_⟩
  intro ij a
  simp only [id_eq, hprod, hchi, star_div₀, star_mul, star_ofNat]
  ring

end NativeRankRelation.CommonData

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

theorem majorPhasePlateauSignal_integerChart_eq {m : ℕ} {X : Type} {τ : Type*}
    (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : τ → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (integerSampledLowTags J k β u i : ℝ)| ≤ 1 / 8) :
    majorPhasePlateauSignal J k poly c P (integerSampledSpatial β u) =
      (Real.fourierChar (MvPolynomial.eval (fun x => (u x : ℝ))
        (aeval (integerSampledRealChart β ∘ lowTaggedVariableEmbedding J k) P)) : ℂ) := by
  rw [majorPhasePlateauSignal_eq_phase J k poly c P
    (integerSampledSpatial β u) (integerSampledLowTags J k β u) hb]
  have he : MvPolynomial.eval (fun x => (u x : ℝ))
      (aeval (integerSampledRealChart β ∘ lowTaggedVariableEmbedding J k) P) =
      MvPolynomial.eval
        (fun i => ((Sum.elim (integerSampledSpatial β u) (integerSampledLowTags J k β u) i : ℤ) : ℝ)) P := by
    calc
      _ = MvPolynomial.eval (fun i => MvPolynomial.eval (fun x => (u x : ℝ))
          (integerSampledRealChart β (lowTaggedVariableEmbedding J k i))) P :=
        MvPolynomial.comp_aeval_apply _ (MvPolynomial.aeval (fun x => (u x : ℝ))) P
      _ = _ := by
        apply congrArg (fun z => MvPolynomial.eval z P)
        funext i
        rw [integerSampledRealChart_eval]
        cases i <;> rfl
  rw [he]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

theorem exists_bufferedSampledCurrentGrade_phase
    {m : ℕ} {X η : Type} {τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ)
    (hβ : ∀ i, integerSampledRealChart β i ∈
      weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i))
    (U : Submodule ℚ F.AssociatedGraded)
    (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U)) (j : η)
    (n : ℕ) (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ) :
    let topβ := fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i)
    let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
      (fun _ : τ => 1) topβ
      (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
    ∃ lower : MvPolynomial τ ℝ, lower.totalDegree ≤ n ∧
      ∀ u : τ → ℤ,
      (∀ i, |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
        (lowTaggedPolynomial J (n + 1) poly i) - c i -
        (integerSampledLowTags J (n + 1) β u i : ℝ)| ≤ 1 / 8) →
      majorPhasePlateauSignal J (n + 1) poly c
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1) (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) U (n + 1) (left⁻¹ * Z * right⁻¹).coord)))
        (integerSampledSpatial β u) =
      (Real.fourierChar (MvPolynomial.eval (fun x => (u x : ℝ))
        (homogeneousComponent (n + 1)
          (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) ((eQ.coord j).comp U.mkQ)
            ((pull left)⁻¹ * pull Z * (pull right)⁻¹)) + lower)) : ℂ) := by
  obtain ⟨lower, hdegree, hphase⟩ := F.exists_sampledCurrentGrade_lowTagged_lower_phase
    b ω hF J (integerSampledRealChart β) hβ U eQ j n Z left right
  refine ⟨lower, hdegree, ?_⟩
  intro u hb
  rw [majorPhasePlateauSignal_integerChart_eq J (n + 1) poly c β _ u hb, hphase]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realPolynomialSymbolLift realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom weightedAdaptedRealChartHom realChartSubstitute
  symbolPointwiseSubalgebra realificationLieSubalgebra
  PolynomialRationalGrid PolynomialSlowBound

theorem exists_controlled_terminal_globalMarkedNativeFactors (s a : ℕ) :
    ∃ Ce Cr : ℕ, 2 ≤ Ce ∧ 2 ≤ Cr ∧
    ∀ {m : ℕ} {X ι η L : Type} [Fintype X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (W : LieSubalgebra ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ W.toSubmodule)))
      (lift : (F.AssociatedGraded ⧸ W.toSubmodule) →ₗ[ℚ] F.AssociatedGraded)
      (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase budget : ℝ)
      (history : CertifiedFullChartFiniteHistory F b ω hF J W.toSubmodule basis lift
        Z Kinitial Utag poly N Bphase s),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule →
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2 budget →
    ∀ (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial (X ⊕ (Σ j, J j)) ℝ)
      (hβ : ∀ i, β i ∈ weightedSupportLE
        (fullTaggedVariableWeight (X := X) J) (fullTaggedVariableWeight (X := X) J i))
      (_hδ : ∀ i, δ i ∈ weightedSupportLE
        (fullTaggedVariableWeight (X := X) J) (fullTaggedVariableWeight (X := X) J i)),
      (∀ i, weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
        (fullTaggedVariableWeight (X := X) J i) (δ i) =
        MvPolynomial.aeval
          (fun j => weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J j) (β j))
          (normalizedRealPolynomialChart (fun i => (N i : ℝ))
            (fullTaggedMajorTopCoordinates J poly) i)) →
      (∀ t : X ⊕ (Σ j, J j) → ℝ,
        (fun i => MvPolynomial.eval t
          (weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J i) (β i))) ∈ history.K) →
    ∀ (D H : ℕ) (p : ℝ), 0 < D → 1 ≤ H → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → Real.exp budget * (D : ℝ) ^ s ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H) →
      (∀ i, realPolynomialCoefficientGrid D
        (weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
          (fullTaggedVariableWeight (X := X) J i) (β i))) →
      ∃ q n : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
        0 < n ∧ (n : ℝ) ≤ Real.exp ((p + Cr) ^ Cr) ∧ q * D ^ s ∣ n ∧
        ∀ g : (F.realification.adaptedPolynomialFiltration
          (fullTaggedVariableWeight (X := X) J)).Group,
        F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight (X := X) J) g = Z →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF
          (fullTaggedVariableWeight (X := X) J) (fullTaggedVariableWeight (X := X) J)
          (fun i => weightedHomogeneousComponent (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J i) (β i))
          (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∃ A : GlobalMarkedNativeFactors F b ω hF (fullTaggedVariableWeight (X := X) J) W
          (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight (X := X) J)
            (fullTaggedVariableWeight (X := X) J) β hβ g)
          (pull history.outer.1) (pull history.outer.2),
          F.PolynomialRationalGrid b (fullTaggedVariableWeight (X := X) J) n A.right ∧
          ∀ {τ : Type*} [Fintype τ] (v : τ → ℕ), (∀ i, 0 < v i) →
            (Fintype.card τ : ℝ) ≤ p →
            ∀ (γ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
              (hγ : ∀ i, γ i ∈ weightedSupportLE v (fullTaggedVariableWeight (X := X) J i))
              (T : τ → ℝ), (∀ i, 0 < T i) →
            ∀ B : ℝ, 1 ≤ B →
              (∀ i, realPolynomialMass (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) →
              (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
                Real.exp budget * B ^ s ≤ Real.exp ((p + 2) ^ a)) →
              F.PolynomialSlowBound b v T (Real.exp ((p + Ce) ^ Ce))
                (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight (X := X) J)
                  v γ hγ A.left) := by
  obtain ⟨Ce, Cr, hCe, hCr, hnormalize⟩ :=
    exists_chartwise_controlled_globalMarkedNativeFactors s a
  refine ⟨Ce, Cr, hCe, hCr, ?_⟩
  intro m X ι η L _ _ _ _ _ F b ω hF J _ W basis lift Z Kinitial Utag poly N
    Bphase budget history hW hcontrol β δ hβ hδ hδtop htop D H p hD hH hp
    hι hσ hHp hden hbracket hgrid
  let w := fullTaggedVariableWeight (X := X) J
  let βtop := fun i => weightedHomogeneousComponent w (w i) (β i)
  have hβtop : ∀ i, (βtop i).IsWeightedHomogeneous w (w i) :=
    fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w w βtop hβtop
  obtain ⟨q, hq, hqB, e₀, r₀, he₀, hr₀, hrGrid, hl, heSlow⟩ :=
    FullChartControlledFactors.exists_prescribed_full_lifts F b ω hF J poly N
      history.outer.1 history.outer.2 hcontrol w βtop δ hβtop hδ hδtop D hD hgrid
  have hlp : ((q * D ^ s : ℕ) : ℝ) ≤ Real.exp p := by
    calc
      ((q * D ^ s : ℕ) : ℝ) = (q : ℝ) * (D : ℝ) ^ s := by simp only [Nat.cast_mul, Nat.cast_pow]
      _ ≤ Real.exp budget * (D : ℝ) ^ s :=
        mul_le_mul_of_nonneg_right hqB (pow_nonneg (Nat.cast_nonneg _) _)
      _ ≤ Real.exp p := hden
  obtain ⟨n, hn, hnp, hln, hfactor⟩ := hnormalize F b ω hF w
    (fullTaggedVariableWeight_pos J) H (q * D ^ s) p hH hl hp hι hσ hHp hlp hbracket
  refine ⟨q, n, hq, hqB, hn, hnp, hln, ?_⟩
  intro g hZ
  change ∃ A : GlobalMarkedNativeFactors F b ω hF w W
      (F.weightedAdaptedRealChartHom w w β hβ g)
      (pull history.outer.1) (pull history.outer.2), _
  have hfast := history.globalRestriction_terminal_mem_pointwise hW β hβ g hZ htop
  change ((pull history.outer.1)⁻¹ *
    F.realPolynomialSymbolHom b ω hF w (F.weightedAdaptedRealChartHom w w β hβ g) *
    (pull history.outer.2)⁻¹).coord ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w W) at hfast
  have hresult := hfactor W
    (F.weightedAdaptedRealChartHom w w β hβ g) e₀ r₀
    (pull history.outer.1) (pull history.outer.2) he₀ hr₀ hfast hrGrid
  apply Exists.elim hresult
  intro A hA
  refine ⟨A, hA.1, ?_⟩
  intro τ _ v hv hτ γ hγ T hT B hB hmass hbudget
  apply hA.2 v hv hτ γ hγ T hT
  exact F.polynomialSlowBound_mono b v T hT hbudget _
    (heSlow v γ hγ T hT B hB hmass)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateAxisFreezingConclusion
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost shortCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)

variable (fixed : {i : C.Variables // ¬keep i.val} → ℤ)

variable (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
    (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable abbrev freezeAxes : AllocatedExternalLocalChart (E := E) A (max cost shortCost) where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := keep
  fixed := C.axisFixed keep fixed
  fixed_in_box i := by
    dsimp only [axisFixed]
    split_ifs with hi
    · exact Finset.mem_Ico.mp (C.slice.progression_inside ⟨i.val, hi⟩ (hfixed ⟨⟨i.val, hi⟩, i.property⟩))
    · exact C.fixed_in_box ⟨i.val, hi⟩
  step := C.step
  step_pos := C.step_pos
  slice := C.axisSlice keep hkeep
  dense := (C.slice.comap_isDenseCommonStrideBox C.step_pos C.dense
    (C.keptInclusion keep hkeep)).mono (le_max_left _ _)

@[simp] theorem freezeAxes_path :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).path = C.path := rfl

@[simp] theorem freezeAxes_centerLift :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).centerLift = C.centerLift := rfl

theorem freezeAxes_parameter (u : {i // keep i} → ℤ) :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).parameter u =
      C.parameter (C.axisPoint keep fixed u) := by
  funext i
  by_cases hk : keep i
  · have hc := hkeep i hk
    simp [parameter, freezeAxes, axisPoint, finiteSplitPoint, hk, hc]
  · by_cases hc : C.keep i
    · simp [parameter, axisFixed, axisPoint, finiteSplitPoint, hk, hc]
    · simp [parameter, axisFixed, finiteSplitPoint, hk, hc]

theorem freezeAxes_chartValues (u : {i // keep i} → ℤ) :
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).chartValues u =
      C.chartValues (C.axisPoint keep fixed u) := by
  funext i
  change MvPolynomial.eval u (freezePolynomial keep (C.axisFixed keep fixed) _) =
    MvPolynomial.eval (C.axisPoint keep fixed u) (freezePolynomial C.keep C.fixed _)
  rw [freezePolynomial_eval, freezePolynomial_eval]
  apply congrArg (fun x => MvPolynomial.eval x _)
  exact C.freezeAxes_parameter (shortCost := shortCost) keep hkeep fixed hfixed u

noncomputable def axisPolynomial (i : C.Variables) : MvPolynomial {i // keep i} ℝ :=
  if hi : keep i.val then MvPolynomial.X ⟨i.val, hi⟩ else MvPolynomial.C (fixed ⟨i, hi⟩ : ℝ)

theorem axisPolynomial_support (i : C.Variables) :
    C.axisPolynomial keep fixed i ∈ weightedSupportLE (fun _ => 1) 1 := by
  by_cases hi : keep i.val
  · rw [axisPolynomial, dif_pos hi]
    exact weightedSupportLE_X (R := ℝ) (fun _ : {i // keep i} => 1) ⟨i.val, hi⟩
  · rw [axisPolynomial, dif_neg hi]
    exact weightedSupportLE_C (fun _ : {i // keep i} => 1) 1 (fixed ⟨i, hi⟩ : ℝ)

theorem axisPolynomial_eval (u : {i // keep i} → ℤ) (i : C.Variables) :
    MvPolynomial.eval (fun k => (u k : ℝ)) (C.axisPolynomial keep fixed i) =
      (C.axisPoint keep fixed u i : ℝ) := by
  by_cases hi : keep i.val <;> simp [axisPolynomial, axisPoint, hi]

include hfixed in

theorem axisPoint_mem {u : {i // keep i} → ℤ}
    (hu : u ∈ (C.axisSlice keep hkeep).integerPoints) :
    C.axisPoint keep fixed u ∈ C.slice.integerPoints := by
  apply (C.slice.mem_integerPoints_iff _).mpr
  have hu' := ((C.axisSlice keep hkeep).mem_integerPoints_iff _).mp hu
  intro i
  by_cases hi : keep i.val
  · simpa only [axisPoint, dif_pos hi, axisSlice, ResidueBoxSlice.comap, keptInclusion] using hu' ⟨i.val, hi⟩
  · simpa only [axisPoint, dif_neg hi] using hfixed ⟨i, hi⟩

end AllocatedExternalLocalChart

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
    [LieRing M] [LieAlgebra ℚ M] {r d t : ℕ}
    {D : RationalFilteredNilmanifold L r d} {Fmark : NilpotentLieFiltration M t}
    {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}

namespace AllocatedExternalLocalCandidate

variable {cost shortCost : ℝ} {C : AllocatedExternalLocalChart (E := E) A cost}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable def axisOrbit : D.filtration.realification.PolynomialOrbit
    (fun _ : {i // keep i} => 1) :=
  D.filtration.polynomialOrbitRealChart (fun _ => 1) (fun _ => 1)
    (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed) candidate.orbit

theorem axisOrbit_eval (u : {i // keep i} → ℤ) :
    D.filtration.realification.polynomialOrbitEval (fun _ => 1) u
      (candidate.axisOrbit keep fixed) =
      D.filtration.realification.polynomialOrbitEval (fun _ => 1)
        (C.axisPoint keep fixed u) candidate.orbit := by
  simpa only [axisOrbit, C.axisPolynomial_eval, polynomialOrbitRealEval_integer] using
    D.filtration.polynomialOrbitRealChart_realEval (fun _ => 1) (fun _ => 1)
      (C.axisPolynomial keep fixed) (C.axisPolynomial_support keep fixed)
      candidate.orbit (fun i => (u i : ℝ))

noncomputable def freezeAxes : AllocatedExternalLocalCandidate
    (C.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed) D Fmark φ marked where
  orbit := candidate.axisOrbit keep fixed
  mark_on_slice u hu := by
    rw [candidate.axisOrbit_eval, C.freezeAxes_chartValues]
    exact candidate.mark_on_slice _ (C.axisPoint_mem keep hkeep fixed hfixed hu)

noncomputable def freezeAxesScore (observable : (X → ℤ) → D.Space → ℂ)
    (weight : (X → ℤ) → ℂ) : ℝ :=
  (candidate.freezeAxes (shortCost := shortCost) keep hkeep fixed hfixed).score observable weight

end AllocatedExternalLocalCandidate

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

attribute [local irreducible] polynomialOrbitRealChart
  integerProgressionSupport IsDenseCommonStrideBox ResidueBoxSlice.integerPoints

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalChart

variable {cost : ℝ} (C : AllocatedExternalLocalChart (E := E) A cost)
    (keep : LayerSamplerVariables G I n B → Prop)
    (hkeep : ∀ i, keep i → C.keep i)
    (fixed : {i : C.Variables // ¬keep i.val} → ℤ)
    (hfixed : ∀ i, fixed i ∈ integerProgressionSupport
      (C.slice.start i.val : ℤ) C.step (C.slice.length i.val))

noncomputable abbrev restrictAxes : AllocatedExternalLocalChart (E := E) A cost where
  path := C.path
  path_supported := C.path_supported
  centerLift := C.centerLift
  center_eq := C.center_eq
  sample := C.sample
  read := C.read
  recovered := C.recovered
  keep := keep
  fixed := C.axisFixed keep fixed
  fixed_in_box := (C.freezeAxes (shortCost := cost) keep hkeep fixed hfixed).fixed_in_box
  step := C.step
  step_pos := C.step_pos
  slice := C.axisSlice keep hkeep
  dense := C.slice.comap_isDenseCommonStrideBox C.step_pos C.dense
    (C.keptInclusion keep hkeep)

@[simp] theorem restrictAxes_path :
    (C.restrictAxes keep hkeep fixed hfixed).path = C.path := rfl

@[simp] theorem restrictAxes_centerLift :
    (C.restrictAxes keep hkeep fixed hfixed).centerLift = C.centerLift := rfl

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateRefilteredSupportedStep
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}

namespace AllocatedExternalCandidateSampler

variable (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

theorem physical_mem_integerBox (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) :
    A.physical z site ∈ integerBox N := by
  have hroot : (∑ k, |(site.val k : ℝ)|) ≤
      allocatedExternalCandidateRootBudget B U b S := by
    rw [allocatedExternalCandidateRootBudget_eq]
    exact allocatedParameterSite_sum_bound B U b S site
  exact jointIntegerPhysicalSite_mem_box site.val N (spatialTrimMargin τ N)
    (fun x => (A.trimMargin_proper x).le) A.widths
    (narrowTrimmedSpatialWidths_fit
      (allocatedExternalCandidateRootBudget_nonneg B U b S) A.trim_pos hξ1
      site.val hroot N A.size_pos) z

end AllocatedExternalCandidateSampler

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I E J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalLocalChart

variable {A} {chartCost : ℝ} (C : AllocatedExternalLocalChart (E := E) A chartCost)

theorem physical_mem_integerBox (hξ1 : ξ ≤ 1) (u : C.Variables → ℤ)
    (hu : u ∈ C.slice.integerPoints) : C.physical u ∈ integerBox N := by
  rw [C.physical_eq_sampler u (C.slice.integerPoints_subset_integerBox hu)]
  exact A.physical_mem_integerBox hξ1 C.path _

end AllocatedExternalLocalChart

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidatePrecenterNativePartners
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel NilpotentLieFiltration
open RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    (A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center)

namespace AllocatedExternalCandidateSampler

def boxedPhysical (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) : integerBox N :=
  ⟨A.physical z site, A.physical_mem_integerBox hξ1 z site⟩

@[simp] theorem boxedPhysical_val (hξ1 : ξ ≤ 1) (z : A.Path) (site : A.Site) :
    (A.boxedPhysical hξ1 z site).val = A.physical z site := rfl

end AllocatedExternalCandidateSampler

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedExternalCandidateTaggedSourceEvaluation
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel NilpotentLieFiltration NilpotentLieBCHGroup
open scoped BigOperators Classical TensorProduct

noncomputable section

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
    {I Deck J : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
    {n : Fin m → ℕ} {B : LayerSamplerAxis I n → Type*} [∀ a, Fintype (B a)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
    {hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    {A : AllocatedExternalCandidateSampler B U b S hb o hR hσ N poly hm τ ξ stride cells center}

namespace AllocatedExternalLocalCandidate

variable {cost : ℝ} {C : AllocatedExternalLocalChart (E := Deck) A cost}
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d t : ℕ} {D : RationalFilteredNilmanifold L s d}
    {Fmark : NilpotentLieFiltration M t} {φ : L →ₗ⁅ℚ⁆ M}
    {marked : Fmark.realification.PolynomialOrbit (fullTaggedVariableWeight (X := X) J)}
    (candidate : AllocatedExternalLocalCandidate C D Fmark φ marked)

@[simp] theorem siteValue_site (u : C.Variables → ℤ)
    (hu : u ∈ integerBox (fun i : C.Variables => A.sides i.val)) :
    candidate.siteValue (C.site u hu) = candidate.value u := by
  change candidate.value (C.retainedParameter (C.parameter u)) = candidate.value u
  rw [C.retainedParameter_parameter]

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {Y : Type*} {w : Y → ℕ} (reference : D.Niltest w)

@[simp] theorem withOrbit_eval (u : C.Variables → ℤ) :
    (reference.withOrbit candidate.orbit).eval u =
      reference.observable (candidate.value u) := rfl

@[simp] theorem withOrbit_eval_site (site : A.Site) :
    (reference.withOrbit candidate.orbit).eval (C.retainedParameter site.val) =
      reference.observable (candidate.siteValue site) := rfl

end AllocatedExternalLocalCandidate

end

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedExternalCandidateSpatialNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*)

theorem fullTaggedSpatialIntegerChart_support (x : X) :
    integerSampledRealChart (fullTaggedSpatialIntegerChart (X := X) J) x ∈
      weightedSupportLE (fullTaggedVariableWeight J) 1 := by
  change MvPolynomial.map (Int.castRingHom ℝ) (MvPolynomial.X (Sum.inl x)) ∈ _
  rw [MvPolynomial.map_X]
  exact weightedSupportLE_X (fullTaggedVariableWeight J) (Sum.inl x)

end Erdos3.VectorPolynomial

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}
    (Q : D.Niltest (fun _ : X => 1)) (J : Fin m → Type*)

noncomputable def fullTaggedSpatial : D.Niltest (fullTaggedVariableWeight (X := X) J) :=
  Q.integerChartPullback (fullTaggedVariableWeight J) (fullTaggedSpatialIntegerChart J)
    (fullTaggedSpatialIntegerChart_support J)

@[simp] theorem fullTaggedSpatial_eval (u : X ⊕ (Σ j, J j) → ℤ) :
    (Q.fullTaggedSpatial J).eval u = Q.eval (fun x => u (Sum.inl x)) := by
  rw [fullTaggedSpatial, integerChartPullback_eval]
  simp only [fullTaggedSpatialIntegerChart, MvPolynomial.eval_X]

@[simp] theorem fullTaggedSpatial_eval_physical
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (c : ∀ j, J j → ℝ)
    (u : X → ℤ) :
    (Q.fullTaggedSpatial J).eval (fullTaggedPhysicalIntegerPoint J poly c u) = Q.eval u := by
  rw [fullTaggedSpatial_eval]
  rfl

@[simp] theorem fullTaggedSpatial_normBound :
    (Q.fullTaggedSpatial J).normBound = Q.normBound := rfl

@[simp] theorem fullTaggedSpatial_complexity (p : ℝ) :
    (Q.fullTaggedSpatial J).ComplexityLE p ↔ Q.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

namespace Erdos3.NativeSampleModel

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

variable {m s : ℕ} {X T : Type*} {p : ℝ}
    {sample : T → X → ℤ} {f : T → ℂ}
    (Q : NativeSampleModel (fun _ : X => 1) s p sample f)
    (J : Fin m → Type*) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))

noncomputable def fullTaggedSpatial (c : ∀ j, J j → ℝ) :
    NativeSampleModel (fullTaggedVariableWeight J) s p
      (fun t => fullTaggedPhysicalIntegerPoint J poly c (sample t)) f where
  L := Q.L
  dim := Q.dim
  model := Q.model
  test := Q.test.fullTaggedSpatial J
  norm := Q.norm
  complexity := Q.complexity
  eval t := by
    rw [RationalFilteredNilmanifold.Niltest.fullTaggedSpatial_eval_physical]
    exact Q.eval t

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchTaggedBufferedScore
namespace OAI

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {τ : Type*} (p : τ → ℕ) {d s : ℕ} {w : Fin d → ℕ}
variable [Fintype (PolynomialShearIndex w)]

theorem weightedPolynomialShearOrbitSymbolicHom_degree (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).realification.PolynomialOrbit p)
    {n : ℕ} {P : MvPolynomial (τ ⊕ Fin d) ℝ}
    (hP : P ∈ weightedSupportLE (Sum.elim p w) n) :
    weightedPolynomialShearOrbitSymbolicHom p hw g P ∈
      weightedSupportLE (Sum.elim p w) n :=
  polynomialSymbolicShearExp_weighted_degree p w _
    (weightedPolynomialShearOrbitParameterCoordinates_degree s hw p g) hP

namespace PolynomialPatch
variable {σ : Type*} (A : PolynomialPatch σ s d)

noncomputable def ofWeightedShearOrbit
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : WeightedParameterPatch τ p s d := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.weightedSymbolicShearPatch p (weightedPolynomialShearOrbitSymbolicHom p A.weight_le g⁻¹)
    (weightedPolynomialShearOrbitSymbolicHom_degree p A.weight_le g⁻¹)

@[simp] theorem ofWeightedShearOrbit_weight
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : (A.ofWeightedShearOrbit p g).weight = A.weight := rfl

@[simp] theorem ofWeightedShearOrbit_kernel
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      p) : (A.ofWeightedShearOrbit p g).kernel = A.kernel := rfl

end PolynomialPatch
end Erdos3

end

section

namespace Erdos3
open _root_.MvPolynomial _root_.OAI.MvPolynomial
open VectorPolynomial

variable {X : Type*} {m n : ℕ} {J : Fin m → Type*}

namespace PolynomialPatch
variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)

noncomputable def ofTaggedWeightedShearOrbit (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    WeightedParameterPatch (X ⊕ Fin n)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1)) s d :=
  A.ofWeightedShearOrbit (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1))
    ((polynomialShearFiltration A.weight s A.weight_le).polynomialOrbitRealChart
      (fullTaggedVariableWeight J)
      (Sum.elim (fun _ => 1) (fun i => (e i).1.val + 1))
      (taggedShearOrbitReindexChart e) (taggedShearOrbitReindexChart_degree e) g)

@[simp] theorem ofTaggedWeightedShearOrbit_weight (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofTaggedWeightedShearOrbit e g).weight = A.weight := rfl

@[simp] theorem ofTaggedWeightedShearOrbit_kernel (e : Fin n ≃ Sigma J)
    (g : (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fullTaggedVariableWeight (X := X) J)) :
    (A.ofTaggedWeightedShearOrbit e g).kernel = A.kernel := rfl

end PolynomialPatch
end Erdos3

end

end OAI
end


