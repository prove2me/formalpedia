-- Prove2me | Definitions.Def_OAIE3v2B257
-- name    : OAIE3v2B257
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:44:56.838393+00:00
-- url     : https://prove2.me/theorems/bf2085ec-32cc-47c6-95c7-7307bdc0860b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 263 of 311
-- statement:
--   Definitions bundle 263 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B243`, `OAIE3v2B248`, `OAIE3v2B250`, `OAIE3v2B251` of this split.
--
--   Modules: `Estimates/AllocatedControlledFrozenPullbacks.lean`, `Estimates/FullRestrictedGradeMajorMatching.lean`, `Estimates/RealSymbolGradedCoefficientBound.lean`, `Geometry/AllocatedRecoveredChartSlow.lean`, `Geometry/CertifiedFullChartBudgetedTreeTerminal.lean`, `Geometry/CertifiedFullChartDecompositionSource.lean`, `Geometry/InhomogeneousFullChartLift.lean`, `Geometry/PreparedFullChartNativeDetection.lean`, `Linear/PreparedDeterminingMatrixBudget.lean`, `Polynomial/FullChartPrescribedPolynomialLifts.lean`, `Polynomial/MajorPhaseDetectedDecomposition.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B243
import Definitions.Def_OAIE3v2B248
import Definitions.Def_OAIE3v2B250
import Definitions.Def_OAIE3v2B251

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorPhaseDetectedDecomposition
namespace OAI

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_residue_detection (d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {m : ℕ} {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      [Fintype (WeightedBasisIndex (lowTaggedWeight J d) d)]
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (R : D.Niltest (fun _ : X => 1))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (W : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ W j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (start : X → ℤ) (q : ℕ) (_hq : 0 < q) (M : ℕ) (_hM : 0 < M)
      (a : (Σ j, J j) → ℤ)
      (_hhigh : ∀ j, d < j.val + 1 → ∀ i, a ⟨j, i⟩ = 0)
      (lengths : X → ℕ) (_hlengths : ∀ i, 0 < lengths i)
      (p : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (M : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, |(a i : ℝ)| ≤ Real.exp p) →
      (∀ i, Real.exp ((p+C)^C) ≤ (lengths i : ℝ)) →
      (∀ v ∈ integerBox lengths, ∀ i,
        |MvPolynomial.eval (fun x => (start x : ℝ) + (q : ℝ) * v x)
          (lowTaggedPolynomial J d poly i) - c i -
          (β (fun x => start x + (q : ℤ) * v x) i : ℝ)| ≤ 1/2) →
      Real.exp (-p) ≤ ‖𝔼 v ∈ integerBox lengths,
        (Real.fourierChar (MvPolynomial.eval
          (fun i => (start i : ℝ) + (q : ℝ) * v i)
          (normalizedTwistFrequencyPolynomial M a poly)) : ℂ) *
          majorPhaseSample J d poly Ψ c F β R.eval
            (fun i => start i + (q : ℤ) * v i)‖ →
      (∀ h : Fin d, HasLayerSamplingRank (h.val + 1) (fun i => (lengths i : ℝ))
        (Real.exp ((p+C)^C)) (lowTaggedRetained J d W h)
        (lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j)))) →
      ∃ (fast : LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J d) d))
        (g : Fin (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J d) d) L)) →
          weightedSubalgebra (lowTaggedWeight J d) d)
        (Slow : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
        (RatPart : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℚ)
        (qOut : ℕ),
        (finrank ℚ (PairAlgebra (weightedSubalgebra (lowTaggedWeight J d) d) L) : ℝ) ≤ (p+C)^C ∧
        Submodule.span ℚ (Set.range g) = fast.toSubmodule ∧
        BasisGradedSubmodule (weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d))
          (weightedBasisGrade (lowTaggedWeight J d) d) fast.toSubmodule ∧
        (∀ j i, rationalLogHeight
          ((weightedBasis (lowTaggedWeight J d) d (lowTaggedWeight_pos J d)).repr (g j) i) ≤ (p+C)^C) ∧
        BasisGradedSubmodule (Pi.basisFun ℝ _) (lowTaggedWeight J d)
          ((fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) ∧
        (∀ h, lowTaggedRetained J d W h ≤ (fast.toSubmodule.baseChange ℝ).map
          (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype))) ∧
        realPolynomialMass Slow ≤ Real.exp ((p+C)^C) ∧
        (∀ α, |Slow.coeff α| ≤ Real.exp ((p+C)^C)) ∧
        0 < qOut ∧ (qOut : ℝ) ≤ Real.exp ((p+C)^C) ∧
        (fun α => RatPart.coeff α) ∈ denominatorGrid qOut ∧
        (∀ α, (RatPart.coeff α).den ≤ qOut) ∧
        Slow ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d ∧
        RatPart ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d ∧
        ∀ (u : X → ℝ) (z : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ),
          z ∈ (fast.toSubmodule.baseChange ℝ).map
            (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra (lowTaggedWeight J d) d).subtype)) →
          MvPolynomial.eval (Sum.elim u z)
            (weightedHomogeneousComponent (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d
              (jointResidueAffinePolynomial q start F)) =
            MvPolynomial.eval (Sum.elim (fun i => u i / (lengths i : ℝ))
              (fun j => z j - MvPolynomial.eval u
                (majorTranslationTopCoordinates (lowTaggedWeight J d)
                  (fun i => residueAffinePolynomial q start
                    (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))) j))) Slow +
              MvPolynomial.eval₂ (algebraMap ℚ ℝ) (Sum.elim u z) RatPart := by
  obtain ⟨aC, _, hprimitive⟩ := exists_majorRationalLift_detection_budget d
  obtain ⟨bC, _, hdetect⟩ :=
    exists_reduced_majorPolynomial_degree_twisted_correlation_decomposition d hd
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseLowFourierExtraction_budget aC bC
  refine ⟨C, hC, ?_⟩
  intro m X L _ _ _ _ t e _ _ _ _ J _ _ D htd R poly hpoly W hcoeff Ψ c F hF β
    start q hq M hM a hhigh lengths hlengths p hp hR hcap hdim hMexp hΨ ha hlarge hβ hcorr hrank
  let w := lowTaggedWeight J d
  let hw := lowTaggedWeight_pos J d
  let hwd := lowTaggedWeight_le J d
  let := moduleTopology ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    realification_moduleTopology_t2 (weightedBasis w d hw)
  let A := fun i => residueAffinePolynomial q start
    (lowTaggedPolynomial J d poly i - MvPolynomial.C (c i))
  let F' := jointResidueAffinePolynomial q start F
  let R' := R.scalarAffinePullback (q : ℚ) (fun i => (start i : ℚ))
  let β' := fun (v : X → ℤ) i => β (fun x => start x + (q : ℤ) * v x) i
  let T := rationalLiftCharacterTwist M (lowTaggedFrequency J d a) c
  let K := rationalLiftCharacterTwistLip M (lowTaggedFrequency J d a)
  let p' : ℝ := (p+aC)^aC+p+1
  have hpow : 0 ≤ (p+aC)^aC := by positivity
  have hpp' : p ≤ p' := by dsimp only [p']; linarith
  have hp' : 0 ≤ p' := hp.trans hpp'
  have hprimitive' : (p+aC)^aC ≤ p' := by dsimp only [p']; linarith
  have hfinal : (p'+bC)^bC ≤ (p+C)^C := (hbudget p hp).2.1
  have hdim' : ((Fintype.card X + Fintype.card (LowTaggedIndex J d) : ℕ) : ℝ) ≤ p := by
    apply le_trans _ hdim
    exact_mod_cast Nat.add_le_add_left (lowTaggedIndex_card_le J d) _
  obtain ⟨hgeometry, hlog⟩ := hprimitive (U := X) w hw hwd M hM Ψ
    (lowTaggedFrequency J d a) p hp hdim' hMexp hΨ (lowTaggedFrequency_bound J d a _ ha)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    residueAffinePolynomial_totalDegree_le q start _ _
      ((MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i))
  have hF' : F' ∈ weightedSupportLE (Sum.elim (fun _ : X => 1) w) d :=
    jointResidueAffinePolynomial_degree w q start hF
  have hzero : translatedIntegerBox (0 : X → ℤ) lengths = integerBox lengths := by
    ext v
    simp only [mem_translatedIntegerBox, mem_integerBox, Pi.zero_apply, zero_add]
  have hβ' : ∀ v ∈ translatedIntegerBox (0 : X → ℤ) lengths, ∀ i,
      |MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ)| ≤ 1/2 := by
    rw [hzero]
    intro v hv i
    simpa only [A, β', residueAffinePolynomial_eval_real, map_sub, eval_C] using hβ v hv i
  have hcorr' : Real.exp (-p') ≤ ‖𝔼 v ∈ translatedIntegerBox (0 : X → ℤ) lengths,
      T (fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ))
          (fun i => (β' v i : ZMod M)) *
        (Ψ.value (fun i => MvPolynomial.eval (fun x => (v x : ℝ)) (A i) - (β' v i : ℝ)) : ℂ) *
        (Real.fourierChar (MvPolynomial.eval (fun j => ((Sum.elim v (β' v) j : ℤ) : ℝ)) F') : ℂ) *
        R'.eval v‖ := by
    rw [hzero]
    apply (Real.exp_le_exp.mpr (neg_le_neg hpp')).trans
    refine le_of_le_of_eq hcorr (Eq.symm ?_)
    refine congrArg (fun z => ‖z‖) ?_
    apply Finset.expect_congr rfl
    intro v _
    have hcast : (fun j => ((Sum.elim v (β' v) j : ℤ) : ℝ)) =
        Sum.elim (fun i => (v i : ℝ)) (fun i => (β' v i : ℝ)) := by
      funext j
      cases j <;> rfl
    rw [hcast]
    simpa only [T, A, β', F', R', Function.comp_def] using
      (majorPhase_affine_integrand J d poly Ψ c F β R start q M hM a hhigh v).symm
  have htop : ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
      (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i)) =
      lowTaggedTopPolynomial J d (fun j => residueAffine q start (poly j)) := by
    exact lowTaggedTopPolynomial_centered_residueAffine J d poly q start c
  have hTpos (i : X) : 0 < (lengths i : ℝ) := by exact_mod_cast hlengths i
  have hrank' (h : Fin d) : HasLayerSamplingRank (h.val+1) (fun i => (lengths i : ℝ))
      (Real.exp ((p'+bC)^bC)) (lowTaggedRetained J d W h)
      (ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
        (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i))) := by
    rw [htop]
    exact (hrank h).mono (Real.exp_le_exp.mpr hfinal) hTpos
  have hcoeff' α : coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ _)
      (fun i => weightedHomogeneousComponent (fun _ : X => 1) (w i) (A i))) α ∈
      ⨆ h, lowTaggedRetained J d W h := by
    rw [htop]
    exact lowTaggedTopPolynomial_residueAffine_coeff_mem_iSup J d poly W hcoeff q start α
  have hX : (Fintype.card X : ℝ) ≤ p' := by
    apply le_trans _ (hdim'.trans hpp')
    exact_mod_cast Nat.le_add_right (Fintype.card X) (Fintype.card (LowTaggedIndex J d))
  obtain ⟨fast, g, Slow, RatPart, qOut, hdimOut, hg, hgraded, hheight, hbasegraded,
      hret, hmass, hslow, hqOut, hqbound, hgrid, hden, hSlowW, hRatW, hidentity⟩ :=
    hdetect w hw hwd M hM D htd Ψ F' hF' A hA K T
      (fun x r => (rationalLiftCharacterTwist_norm M (lowTaggedFrequency J d a) c x r).le)
      (rationalLiftCharacterTwist_lipschitz M (lowTaggedFrequency J d a) c)
      R' p' hp' (GeometryComplexityLE.mono _ hgeometry hprimitive') (hlog.trans hprimitive')
      (hR.mono hpp') hcap 0 lengths hlengths hX
      (fun i => (Real.exp_le_exp.mpr hfinal).trans (hlarge i)) β' hβ' hcorr'
      (lowTaggedRetained J d W) hrank' hcoeff'
  exact ⟨fast, g, Slow, RatPart, qOut, hdimOut.trans hfinal, hg, hgraded,
    (fun j i => (hheight j i).trans hfinal), hbasegraded, hret,
    hmass.trans (Real.exp_le_exp.mpr hfinal),
    (fun α => (hslow α).trans (Real.exp_le_exp.mpr hfinal)), hqOut,
    hqbound.trans (Real.exp_le_exp.mpr hfinal), hgrid, hden, hSlowW, hRatW, hidentity⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial Module RationalFilteredNilmanifold PolynomialTranslationLie
open scoped TensorProduct NNReal BigOperators

theorem exists_majorPhase_detected_decomposition (m d : ℕ) (hd : 0 < d) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L : Type} [Fintype X] [DecidableEq X]
      [LieRing L] [LieAlgebra ℚ L] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold L t e) (_htd : t < d)
      (R : D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J d)))
      (c : Fin (Fintype.card (LowTaggedIndex J d)) → ℝ)
      (F : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J d))) ℝ)
      (_hF : F ∈ weightedSupportLE
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J d)) d)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J d)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J d poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → R.ComplexityLE p → (R.normBound : ℝ) ≤ 1 →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (W.modulus : ℝ) ≤ Real.exp p → (W.cover : ℝ) ≤ Real.exp p →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        W.eval N poly u * majorPhaseSample J d poly Ψ c F β R.eval u‖ →
      MajorPhaseDetectedConclusion (L := L) J d U poly c F N ((p + C) ^ C) := by
  obtain ⟨aC, _, hextract⟩ := exists_majorPhase_low_localized_correlating_frequency m d
  obtain ⟨bC, _, hdetect⟩ := exists_majorPhase_residue_detection d hd
  obtain ⟨C, hC, hbudget⟩ := exists_majorPhaseDetectedDecomposition_budget aC bC 1 m d
  refine ⟨C, hC, ?_⟩
  intro X L _ _ _ _ t e _ _ _ _ J _ periodCap coverCap Lip W D htd R N poly hpoly U hcoeff
    Ψ c F hF β hβ p Rrank hp hR hcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  let E : ℝ := (p+aC)^aC
  let Q : ℝ := E+p+1
  let G : ℝ := (Q+bC)^bC
  let B : ℝ := (p+C)^C
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hpQ : p ≤ Q := by dsimp [Q]; linarith
  have hEQ : E ≤ Q := by dsimp [Q]; linarith
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hb : E ≤ B ∧ E+(G+Q+1) ≤ B ∧ (m : ℝ)*p+(G+Q+1) ≤ B ∧
    (m : ℝ)*E+(G+Q+1) ≤ B ∧ (d : ℝ)*E+(G+Q+1) ≤ B ∧
    (d : ℝ)*p+(G+Q+1) ≤ B ∧ G+Q+1 ≤ B := by
      simpa only [E, Q, G, B, Nat.cast_one, pow_one] using hbudget p hp
  obtain ⟨hEB, hEGB, hmp, hmE, hdE, hdp, hGB⟩ := hb
  have hGle : G ≤ B := by linarith
  have hEGle : E+G ≤ B := by linarith
  have hNpos (i : X) : 0 < (N i : ℝ) := (Real.exp_pos B).trans_le (hN i)
  obtain ⟨start, lengths, a, hlengths, hlengthLower, hcomparison, hinside,
      ha, hselected, hhigh, _⟩ :=
    hextract J W D htd.le R hd N poly hpoly U hcoeff Ψ c F hF β hβ p Rrank hp hR hcap
      hdim hmod hcover hLip hΨ
      (fun i => (Real.exp_le_exp.mpr hEB).trans (hN i))
      ((Real.exp_le_exp.mpr hEB).trans hRrank) (fun j _ => hrank j) hcorr
  have hlong (i : X) : Real.exp G ≤ (lengths i : ℝ) := by
    calc
      Real.exp G = Real.exp (E+G) * Real.exp (-E) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp B * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hEGle) (Real.exp_nonneg _)
      _ ≤ (N i : ℝ) * Real.exp (-E) :=
        mul_le_mul_of_nonneg_right (hN i) (Real.exp_nonneg _)
      _ ≤ _ := hlengthLower i
  let startInt := fun i => (start i : ℤ)
  have hsliceRank := majorPhase_residue_lowTagged_rank J d poly hpoly U N lengths
    hNpos hlengths W.modulus W.modulus_pos startInt p E G B Rrank hp hE hmod hcomparison
    hGle (by linarith) (by linarith) hRrank hrank
  have hβslice : ∀ v ∈ integerBox lengths, ∀ i,
      |MvPolynomial.eval (fun x => (startInt x : ℝ) + (W.modulus : ℝ) * v x)
        (lowTaggedPolynomial J d poly i) - c i -
        (β (fun x => startInt x + (W.modulus : ℤ) * v x) i : ℝ)| ≤ 1/2 := by
    intro v hv i
    simpa only [startInt, Int.cast_add, Int.cast_mul, Int.cast_natCast] using
      hβ _ (hinside v hv) i
  have hselectedQ : Real.exp (-Q) ≤ ‖𝔼 v ∈ integerBox lengths,
      (Real.fourierChar (MvPolynomial.eval
        (fun i => (startInt i : ℝ) + (W.modulus : ℝ) * v i)
        (normalizedTwistFrequencyPolynomial W.cover a poly)) : ℂ) *
      majorPhaseSample J d poly Ψ c F β R.eval
        (fun i => startInt i + (W.modulus : ℤ) * v i)‖ := by
    simpa only [startInt, Int.cast_natCast] using
      (Real.exp_le_exp.mpr (neg_le_neg hEQ)).trans hselected
  let w := lowTaggedWeight J d
  let := weightedBasisIndex_finite w d (lowTaggedWeight_pos J d)
  let : Fintype (WeightedBasisIndex w d) := Fintype.ofFinite _
  obtain ⟨fast, g, Slow, RatPart, qOut, hcount, hgspan, hgraded, hgheight, hKgraded,
      hretained, hmass, _, hqOut, hqBound, hgrid, _, hSlow, hRat, hidentity⟩ :=
    hdetect J D htd R poly hpoly U hcoeff Ψ c F hF β startInt W.modulus W.modulus_pos
      W.cover W.cover_pos a hhigh lengths hlengths Q hQ (hR.mono hpQ) hcap
      (hdim.trans hpQ) (hcover.trans (Real.exp_le_exp.mpr hpQ))
      (hΨ.trans (Real.exp_le_exp.mpr hpQ))
      (fun i => (ha i).trans (Real.exp_le_exp.mpr hEQ)) hlong hβslice hselectedQ hsliceRank
  let K := (fast.toSubmodule.baseChange ℝ).map
    (realifyCoordinateMap (baseLinear.comp (weightedSubalgebra w d).subtype))
  let A := fun i => lowTaggedPolynomial J d poly i - MvPolynomial.C (c i)
  have hA : ∀ i, (A i).totalDegree ≤ w i := fun i =>
    (MvPolynomial.totalDegree_sub_C_le _ _).trans (lowTaggedPolynomial_degree J d poly hpoly i)
  obtain ⟨Slow', RatPart', _, _, hidentity', hmass', hSlow', hRat', _, _, hgrid'⟩ :=
    algebraic_major_weighted_affine_top_pullback_decomposition K w (lowTaggedWeight_pos J d)
      d F hF A hA Slow RatPart W.modulus W.modulus_pos startInt
      (fun i => (N i : ℝ)) (fun i => (lengths i : ℝ)) hNpos
      (fun i => Nat.cast_pos.mpr (hlengths i)) hidentity
      (Real.exp E) (Real.exp G) (Real.one_le_exp hE) hcomparison d qOut hSlow hRat hmass hgrid
  have hmassFinal : realPolynomialMass Slow' ≤ Real.exp B :=
    hmass'.trans (pow_mul_exp_le_exp_of_le_budget (Real.exp_nonneg E) le_rfl hE
      le_rfl (by linarith : (d : ℝ)*E+G ≤ B))
  have hdenFinal : ((W.modulus^d*qOut : ℕ) : ℝ) ≤ Real.exp B :=
    nat_pow_mul_le_exp_of_le_budget hmod hqBound (by linarith : (d : ℝ)*p+G ≤ B)
  have hdenPos : 0 < W.modulus^d*qOut := Nat.mul_pos (pow_pos W.modulus_pos _) hqOut
  refine ⟨fast, g, Slow', RatPart', W.modulus^d*qOut,
    hcount.trans hGle, hgspan, hgraded, (fun j i => (hgheight j i).trans hGle),
    hKgraded, hretained, hmassFinal, ?_, hdenPos, hdenFinal, hgrid', ?_,
    hSlow', hRat', hidentity'⟩
  · exact fun α => (realPolynomialMass_coeff_le Slow' α).trans hmassFinal
  · exact fun α => den_le_of_mem_denominatorGrid hdenPos hgrid' α

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FullRestrictedGradeMajorMatching
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_homogeneous_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X M : Type} {η V : Type*} [Fintype X] [DecidableEq X] [Fintype η]
      [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
      [LieRing M] [LieAlgebra ℚ M] {t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (J : Fin m → Type) [∀ j, Fintype (J j)] (basis : Basis η ℝ V)
      (pvec : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ V)
      (_hhom : ∀ α, Finsupp.weight (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) α ≠ k →
        coefficients pvec α = 0)
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom pvec) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis pvec := by
  obtain ⟨C, hC, hdetect⟩ := exists_majorPhase_detected_decomposition m k hk
  refine ⟨C, hC, ?_⟩
  intro X M η V _ _ _ _ _ _ _ _ _ t e _ _ _ _ J _ basis pvec hhom
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  have hsupport (j : η) : coordinate (basis.coord j).toAddMonoidHom pvec ∈
      weightedSupportLE (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) k := by
    have hh : (coordinate (basis.coord j).toAddMonoidHom pvec).IsWeightedHomogeneous
        (Sum.elim (fun _ : X => 1) (lowTaggedWeight J k)) k := by
      intro α hα
      by_contra hweight
      apply hα
      rw [coeff_coordinate, hhom α hweight, map_zero]
    intro α hα
    exact (hh (MvPolynomial.mem_support_iff.mp hα)).le
  have hscalar (j : η) : MajorPhaseDetectedConclusion (L := M) J k U poly c
      (coordinate (basis.coord j).toAddMonoidHom pvec) N ((p + C) ^ C) :=
    hdetect J (W j) D htk (R j) N poly hpoly U hcoeff Ψ c
      (coordinate (basis.coord j).toAddMonoidHom pvec) (hsupport j)
      β hβ p Rrank hp (hR j) (hRcap j) hdim (hmod j) (hcover j) hLip hΨ hN hRrank hrank (hcorr j)
  exact majorPhaseVectorDetectedConclusion_of_coordinates J k U poly c N ((p + C) ^ C)
    basis pvec hhom hscalar

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_restricted_grade_vector_major_detection (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (residual : F.RealPolynomialSymbol (fullTaggedVariableWeight (X := X) J))
      {periodCap coverCap : ℝ} {Lip : ℝ≥0}
      (W : η → NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (R : η → D.Niltest (fun _ : X => 1))
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (_hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
      (U : ∀ j, Submodule ℝ (J j → ℝ))
      (_hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
      (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
      (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
      (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
      (_hβ : ∀ u ∈ integerBox N, ∀ i,
        |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
          c i - (β u i : ℝ)| ≤ 1 / 2)
      (p Rrank : ℝ), 0 ≤ p → (∀ j, (R j).ComplexityLE p) →
      (∀ j, ((R j).normBound : ℝ) ≤ 1) →
      ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ p →
      (∀ j, ((W j).modulus : ℝ) ≤ Real.exp p) →
      (∀ j, ((W j).cover : ℝ) ≤ Real.exp p) →
      (Lip : ℝ) ≤ Real.exp p → (Ψ.lip : ℝ) ≤ Real.exp p →
      (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      Real.exp ((p + C) ^ C) ≤ Rrank →
      (∀ j, HasLayerSamplingRank (j.val + 1)
        (fun i => (N i : ℝ)) Rrank (U j) (poly j)) →
      (∀ j, Real.exp (-p) ≤ ‖𝔼 u ∈ integerBox N,
        (W j).eval N poly u * majorPhaseSample J k poly Ψ c
          (coordinate (basis.coord j).toAddMonoidHom
            (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
              (fullTaggedVariableWeight J) fast k residual))) β (R j).eval u‖) →
      MajorPhaseVectorDetectedConclusion (L := M) J k U poly c N ((p + C) ^ C) basis
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight J) fast k residual)) ∧
      ∀ (u : X → ℝ) (z : ∀ j, J j → ℝ),
        eval₂ (Sum.elim u (fun a : Σ j, J j => z a.1 a.2))
          (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) fast k residual) =
        eval₂ (Sum.elim u (lowTaggedCoordinates J k z))
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight J) fast k residual)) := by
  obtain ⟨C, hC, hdetect⟩ := exists_homogeneous_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis residual
    periodCap coverCap Lip W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR
    hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  constructor
  · apply hdetect J basis
      (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight J) fast k residual))
      _ W D htk R N poly hpoly U hcoeff Ψ c β hβ p Rrank hp hR hRcap hdim
      hmod hcover hLip hΨ hN hRrank hrank hcorr
    exact lowTaggedVectorRestrict_homogeneous J k _
      (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF (fullTaggedVariableWeight J) fast k residual)
  · intro u z
    apply lowTaggedVectorRestrict_eval_real J k _ _ u z
    intro α hα
    exact F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF (fullTaggedVariableWeight J)
      fast k residual α (ne_of_gt hα)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartDecompositionSource
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_certified_full_chart_decomposition_of_major_correlation
    (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L M ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s t e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (D : RationalFilteredNilmanifold M t e) (_htk : t < k)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      FullChartMajorCorrelation F b ω hF J k fast basis Z left right D N poly U p Rrank C →
      CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hdetect⟩ := exists_full_restricted_grade_vector_major_detection m k hk
  refine ⟨C, hC, ?_⟩
  intro X L M ι η _ _ _ _ _ _ _ s t e _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower D htk N poly U p Rrank hcorrelation
  obtain ⟨periodCap, coverCap, Lip, W, R, Ψ, c, β, hpoly, hcoeff, hβ,
    hp, hR, hRcap, hdim, hmod, hcover, hLip, hΨ, hN, hRrank, hrank, hcorr⟩ := hcorrelation
  have hdetected := hdetect F b ω hF J fast basis (left⁻¹ * Z * right⁻¹).coord
    W D htk R N poly hpoly U hcoeff Ψ c β hβ
    p Rrank hp hR hRcap hdim hmod hcover hLip hΨ hN hRrank hrank hcorr
  exact certifiedFullChartDetectedDecomposition_of_vector_detection F b ω hF J k fast
    basis lift Z left right K₀ U poly N ((p + C) ^ C) c hfast hsection hK₀ hlower hdetected.1

attribute [local instance] FullChartMajorCorrelationWitness.lie
  FullChartMajorCorrelationWitness.algebra FullChartMajorCorrelationWitness.topology
  FullChartMajorCorrelationWitness.topologicalAdd FullChartMajorCorrelationWitness.continuousSMul
  FullChartMajorCorrelationWitness.hausdorff

theorem exists_certified_full_chart_decomposition_of_major_correlation_witness
    (m k : ℕ) (hk : 0 < k) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
      (_hfast : BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast)
      (_hsection : ∀ y, fast.mkQ (lift y) = y)
      (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
      (_hK₀ : ∀ t ∈ K₀, ∀ r : ℚ,
        (fun i => (r : ℝ) ^ fullTaggedVariableWeight (X := X) J i * t i) ∈ K₀)
      (_hlower : ∀ t ∈ K₀, ∀ j < k,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight (X := X) J) j t
          (left⁻¹ * Z * right⁻¹).coord ∈ fast.baseChange ℝ)
      (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
      (U : ∀ j, Submodule ℝ (J j → ℝ)) (p Rrank : ℝ),
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
        Z left right N poly U p Rrank C) →
      CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
        Z left right K₀ U poly N ((p + C) ^ C) := by
  obtain ⟨C, hC, hstep⟩ := exists_certified_full_chart_decomposition_of_major_correlation m k hk
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z left right K₀ hK₀ hlower N poly U p Rrank hwitness
  obtain ⟨witness⟩ := hwitness
  exact hstep F b ω hF J fast basis lift hfast hsection Z left right K₀ hK₀ hlower
    witness.model witness.lower N poly U p Rrank witness.correlation

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolGradedCoefficientBound
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolHomogeneousPullback

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem FullChartControlledFactors.homogeneousPullback_slow
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {m : ℕ} {X : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (hcontrol : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (fullTaggedVariableWeight (X := X) J i))
    (T : τ → ℝ) (hT : ∀ i, 0 < T i) {B : ℝ} (hB : 1 ≤ B)
    (hmass : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T
      (MvPolynomial.aeval β (normalizedRealPolynomialChart (fun x => (N x : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))) ≤ B) :
    F.SymbolSlowBound b ω hF v T
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget * B ^ s)
      (F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight (X := X) J)
        v β hβ left) := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right hcontrol
  apply F.symbolSlowBound_of_gradedPolynomial b ω hF v T _
  rw [F.realGradedSymbolPolynomialHom_homogeneousPullback_of_chart b ω hF
    (fullTaggedVariableWeight (X := X) J) v β hβ left
    (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly)) E hchart]
  exact CoefficientBound.realChartSubstitute
    ((F.associatedGradedBasis b ω hF).baseChange ℝ) T hT
    (fun i => MvPolynomial.aeval β
      (normalizedRealPolynomialChart (fun x => (N x : ℝ)) (fullTaggedMajorTopCoordinates J poly) i))
    hbound (Real.exp_pos budget).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.InhomogeneousFullChartLift
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realChartSubstitute realGradedSymbolPolynomial
  realSymbolOfGradedPolynomial realSymbolHomogeneousPullback gradedPolynomialProjection

theorem FullChartControlledFactors.exists_graded_degree_bounded_chart
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
        F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
          realPolynomialChartSubstitution
            F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
            (normalizedRealPolynomialChart (fun i => (N i : ℝ))
              (fullTaggedMajorTopCoordinates J poly)) Echart ∧
        CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
          (Real.exp budget) Echart.coord ∧
        Echart.coord ∈ gradedPolynomialSubmodule
          ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
          (fullTaggedVariableWeight (X := X) J) ∧
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart.coord ∧
        DegreeLE (fun _ => 1) s Echart.coord ∧
        CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
          (F.realGradedSymbolPolynomialHom b ω hF
            (fullTaggedVariableWeight (X := X) J) right).coord := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_degree_bounded_chart F b ω hF J poly N left right h
  let w := fullTaggedVariableWeight (X := X) J
  let E' : PolynomialGroup (X ⊕ (Σ j, J j))
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
    ⟨F.gradedPolynomialProjection b ω hF w E.coord⟩
  refine ⟨q, hq, hqB, E', ?_, ?_, F.gradedPolynomialProjection_mem b ω hF w E.coord,
    F.gradedPolynomialProjection_degreeLE b ω hF w w s E.coord hweighted,
    F.gradedPolynomialProjection_degreeLE b ω hF w (fun _ => 1) s E.coord hdegree, hgrid⟩
  · apply NilpotentLieBCHGroup.ext
    have he := congrArg NilpotentLieBCHGroup.coord hchart
    rw [realPolynomialChartSubstitution_coord] at he
    change F.realGradedSymbolPolynomial b ω hF w left.coord =
      realChartSubstitute
        (normalizedRealPolynomialChart (fun i => (N i : ℝ))
          (fullTaggedMajorTopCoordinates J poly))
        (F.gradedPolynomialProjection b ω hF w E.coord)
    have hgraded := F.realGradedSymbolPolynomial_mem_gradedPolynomialSubmodule
      b ω hF w left.coord
    rw [← F.gradedPolynomialProjection_realChartSubstitute b ω hF w w _
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ))) E.coord,
      ← he]
    exact (F.gradedPolynomialProjection_eq_self b ω hF w _ hgraded).symm
  · exact F.gradedPolynomialProjection_coefficientBound b ω hF w _
      (fun _ => zero_lt_one) (Real.exp_pos budget).le E.coord hbound

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ τ : Type*} {ι L : Type} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

attribute [local irreducible] realChartSubstitute realSymbolOfGradedPolynomial
  realGradedSymbolPolynomial realSymbolHomogeneousPullback

theorem FullChartControlledFactors.exists_inhomogeneous_left_lift
    {m : ℕ} {X : Type} [Fintype X]
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup
      (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v
      (fullTaggedVariableWeight (X := X) J i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v
      (fullTaggedVariableWeight (X := X) J i))
    (htop : ∀ i, MvPolynomial.weightedHomogeneousComponent v
      (fullTaggedVariableWeight (X := X) J i) (δ i) =
      MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i)) :
    ∃ (P : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] F.AssociatedGraded))
      (e : (F.realification.adaptedPolynomialFiltration v).Group),
      CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ)
        (fun _ => 1) (Real.exp budget) P ∧
      P ∈ gradedPolynomialSubmodule ((F.associatedGradedBasis b ω hF).baseChange ℝ) ω
        (fullTaggedVariableWeight (X := X) J) ∧
      DegreeLE (fullTaggedVariableWeight (X := X) J) s P ∧
      DegreeLE (fun _ => 1) s P ∧
      e.coord.val = realChartSubstitute δ (VectorPolynomial.map
        (((F.gradedBasisSplitting b ω hF).toLinearMap.baseChange ℝ).restrictScalars ℚ) P) ∧
      F.realPolynomialSymbolHom b ω hF v e = F.realSymbolHomogeneousPullbackHom b ω hF
        (fullTaggedVariableWeight (X := X) J) v β hβ left := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hgraded, hweighted, hdegree, hgrid⟩ :=
    FullChartControlledFactors.exists_graded_degree_bounded_chart
      F b ω hF J poly N left right h
  have hc := congrArg NilpotentLieBCHGroup.coord hchart
  rw [realPolynomialChartSubstitution_coord] at hc
  obtain ⟨e, he, hsymbol⟩ := F.exists_inhomogeneous_chart_lift_algebraic b ω hF
    _ v left _ E.coord hgraded hc β δ hβ hδ htop
  exact ⟨E.coord, e, hbound, hgraded, hweighted, hdegree, he, hsymbol⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPrescribedPolynomialLifts
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct

attribute [local irreducible] realPolynomialSymbolLift realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom weightedAdaptedRealChartHom realChartSubstitute

variable {s m : ℕ} {X τ ι L : Type} [Fintype X]
  [LieRing L] [LieAlgebra ℚ L]
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]

local notation "wt" => fullTaggedVariableWeight (X := X) J

theorem FullChartControlledFactors.exists_prescribed_full_lifts
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup wt)
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget)
    (v : τ → ℕ) (β δ : (X ⊕ (Σ j, J j)) → MvPolynomial τ ℝ)
    (hβ : ∀ i, (β i).IsWeightedHomogeneous v (wt i))
    (hδ : ∀ i, δ i ∈ weightedSupportLE v (wt i))
    (htop : ∀ i, weightedHomogeneousComponent v (wt i) (δ i) =
      MvPolynomial.aeval β (normalizedRealPolynomialChart (fun i => (N i : ℝ))
        (fullTaggedMajorTopCoordinates J poly) i))
    (D : ℕ) (hD : 0 < D) (hgrid : ∀ i, realPolynomialCoefficientGrid D (β i)) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ e r : (F.realification.adaptedPolynomialFiltration v).Group,
        F.realPolynomialSymbolHom b ω hF v e =
          F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ left ∧
        F.realPolynomialSymbolHom b ω hF v r =
          F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ right ∧
        F.PolynomialRationalGrid b v (q * D ^ s) r ∧
        0 < q * D ^ s ∧
        ∀ {υ : Type*} (u : υ → ℕ) (γ : τ → MvPolynomial υ ℝ)
          (hγ : ∀ i, γ i ∈ weightedSupportLE u (v i))
          (T : υ → ℝ), (∀ i, 0 < T i) →
          ∀ B : ℝ, 1 ≤ B →
          (∀ i, realPolynomialMass (scaleMvPolynomialAxes T (MvPolynomial.aeval γ (δ i))) ≤ B) →
          F.PolynomialSlowBound b u T
            (((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s * Real.exp budget * B ^ s)
            (F.weightedAdaptedRealChartHom v u γ hγ e) := by
  obtain ⟨P, e, hbound, _, _, hdegree, he, hsymbol⟩ :=
    FullChartControlledFactors.exists_inhomogeneous_left_lift
      F b ω hF J poly N left right h v β δ hβ hδ htop
  obtain ⟨q, hq, hqB, _, _, _, hright⟩ := h
  let R := F.realSymbolHomogeneousPullbackHom b ω hF wt v β hβ right
  have hR : F.SymbolRationalGrid b ω hF v (q * D ^ s) R :=
    F.symbolRationalGrid_homogeneousPullback_rational_of_coefficientGrid b ω hF wt v
      (fullTaggedVariableWeight_pos J) β hβ q D hgrid right hright
  let r := F.realPolynomialSymbolLift b ω hF v R
  have hr : F.PolynomialRationalGrid b v (q * D ^ s) r := by
    unfold PolynomialRationalGrid
    dsimp only [r]
    rw [F.realPolynomialSymbolLift_log]
    exact F.realSymbolRepresentative_rational_coefficients b ω hF v (q * D ^ s) R hR
  refine ⟨q, hq, hqB, e, r, hsymbol, F.realPolynomialSymbolHom_lift b ω hF v R,
    hr, Nat.mul_pos hq (pow_pos hD s), ?_⟩
  intro υ u γ hγ T hT B hB hmass
  exact F.polynomialSlowBound_inhomogeneous_chart_lift b ω hF v u e δ P he γ hγ
    T hT hbound (Real.exp_pos _).le hB hdegree hmass

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedRecoveredChartSlow
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module Submodule BooleanCubeKernel _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {m : ℕ} {G : Type*} {X : Type} [Fintype G] {I E : Fin m → Type*} {J : Fin m → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)

theorem AllocatedCenteredFramedRecoveredSampleAt.integerFullChart_frozen_pulled_slow
    [Fintype X]
    {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (basis : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (basis '' {i | j ≤ ω i}))
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (hp : ∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j))
    (c : ∀ j, U j) (a : X → ℤ)
    (N : X → ℕ) (hN : ∀ x, 0 < N x)
    {budget : ℝ} (hcontrol : NilpotentLieFiltration.FullChartControlledFactors F basis ω hF J poly N left right budget)
    {τ ξ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hξ : ξ ≤ 1)
    (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hv : v ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths
        (allocatedPhysicalRootBudget B U b S (fun _ => 0)) τ ξ N) 1)
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (read : AllocatedActualCoefficientIndex G X I E n B → ℤ)
    (h : AllocatedCenteredFramedRecoveredSampleAt B U b hb o S hR hσ poly hm c a v sample read)
    (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
    (hchart : ∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm x‖ ≤ C j * ‖x‖)
    (hsmall : ∀ j, C j * (((Fintype.card (I j) : ℝ) + 1) * R j) ≤ 1)

    (keep : LayerSamplerVariables G I n B → Prop) (fixed : {i // ¬keep i} → ℤ)
    : F.SymbolSlowBound basis ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (fun i : {i // keep i} => layerSamplerBox B U b S i.val)
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
      (F.realSymbolHomogeneousPullbackHom basis ω hF (fullTaggedVariableWeight (X := X) J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun z => homogeneousComponent (fullTaggedVariableWeight J z)
          (integerSampledRealChart (fun z => freezePolynomial keep fixed
            (allocatedRecoveredIntegerFullChart B U b o poly hm c a v sample z)) z))
        (fun _ => weightedHomogeneousComponent_isWeightedHomogeneous _ _) left) := by
  apply NilpotentLieFiltration.FullChartControlledFactors.homogeneousPullback_slow
    F basis ω hF J poly N left right hcontrol
  · intro k
    exact lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U b S k.val)
  · have hdim : (1 : ℝ) ≤ ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
    have hm : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    simpa only [one_mul] using
      mul_le_mul hm (one_le_pow₀ hdim (n := m)) (by norm_num : (0 : ℝ) ≤ 1) (by positivity)
  · exact h.integerFullChart_frozen_normalized_top_mass B U b hb o S hR hσ poly hm hp c a N hN
      hτ hτ1 hξ v hv sample read hσ1 C hC hchart hsmall keep fixed

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedControlledFrozenPullbacks
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct Classical

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X]
variable {I Deck J : Fin m → Type} [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {Rad σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ U j)
variable {L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
variable (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem FullChartControlledFactors.exists_allocated_frozen_pullbacks
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (N : X → ℕ) (hN : ∀ i, 0 < N i) {budget allowance : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly N left right budget)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((m + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ m) ^ s)
        ≤ allowance) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∀ (c : ∀ j, U j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B U btag hbtag otag S hRad hσ
        poly hm c origin v sample read →
      ∀ (keep : LayerSamplerVariables G I n B → Prop)
        (fixed : {i // ¬keep i} → ℤ),
      let β := allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed
      let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
      (∀ l : ℕ, q ∣ l → F.SymbolRationalGrid b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l (pull right)) ∧
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B U btag S (fun _ => 0)) τ ξ N) 1 →
      (∀ j, σ j ≤ 1) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ Cgeo : Fin m → ℝ, (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1) →
      F.SymbolSlowBound b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => ((Sum.elim (fun _ : G => S.value)
          (allocatedPrincipalSides B U btag S) i.val : ℕ) : ℝ)) allowance (pull left) := by
  have hc := hcontrol
  obtain ⟨q, hq, hqB, Echart, hchart, hbound, hgrid⟩ := hc
  refine ⟨q, hq, hqB, ?_⟩
  intro c origin v sample read hread keep fixed
  dsimp only
  constructor
  · intro l hql
    apply F.symbolRationalGrid_mono b ω hF _ hq hql
    exact F.symbolRationalGrid_integerTopPullback_of_coefficientGrid b ω hF
      (fullTaggedVariableWeight J) (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (allocatedFrozenIntegerFullChart B U btag otag poly hm c origin v sample keep fixed)
      q right hgrid
  · intro τ ξ hτ hτ1 hξ hv hσ1 hpoly Cgeo hCgeo hgeo hsmall
    have hs := hread.integerFullChart_frozen_pulled_slow B U btag hbtag otag S hRad hσ
      poly hm F b ω hF left right hpoly c origin N hN hcontrol hτ hτ1 hξ
      v hv sample read hσ1 Cgeo hCgeo hgeo hsmall keep fixed
    have hs' := F.symbolSlowBound_mono b ω hF
      (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
      (fun i : {i // keep i} => layerSamplerBox B U btag S i.val)
      (fun i => lt_of_lt_of_le zero_lt_one (layerSamplerBox_one_le B U btag S i.val))
      hallowance _ hs
    simp_rw [allocatedParameterBox_side_eq] at hs'
    unfold allocatedFrozenIntegerFullChart
    exact hs'

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeTerminal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer

theorem exists_budgeted_reached_child_of_major_correlation_witness (m n : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
        [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
        (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
        (J : Fin m → Type) [∀ j, Fintype (J j)]
        (fast : Submodule ℚ F.AssociatedGraded)
        (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
        (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
      ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
        (U : ∀ j, Submodule ℝ (J j → ℝ))
        (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
        (Bphase pTree pPhase Rrank : ℝ) (stageBudget : ℕ → ℝ) (depth : ℕ)
        (T : BudgetedBranchTree F b ω hF J fast basis lift Z U poly N Bphase stageBudget depth pTree)
        (H : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
          Set.univ U poly N Bphase n),
      n < depth → H ∈ T.level n → (pPhase + C) ^ C ≤ stageBudget n →
      Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
        Z H.outer.1 H.outer.2 N poly U pPhase Rrank C) →
      ∃ (q : ℕ) (K : Set ((X ⊕ (Σ j, J j)) → ℝ))
        (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
          VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))),
        FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
          Z H.outer.1 H.outer.2 H.K U poly N ((pPhase + C) ^ C) q K pair ∧
        ∃ Hnext ∈ T.level (n + 1),
          AdmissibleChildAt F b ω hF J fast basis lift Z U poly N Bphase (stageBudget n) H Hnext ∧
          RepresentsCorrection F b ω hF J fast basis lift Z U poly N Bphase Hnext q K pair := by
  obtain ⟨C, hC, hsource⟩ :=
    exists_certified_full_chart_decomposition_of_major_correlation_witness m (n + 1) (by omega)
  refine ⟨C, hC, ?_⟩
  intro X L ι η _ _ _ _ _ s F b ω hF J _ fast basis lift hfast hsection
    Z U poly N Bphase pTree pPhase Rrank stageBudget depth T H hn hH hbudget hcorrelation
  have hlower : ∀ t ∈ H.K, ∀ j < n + 1,
      F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) j t
        (H.outer.1⁻¹ * Z * H.outer.2⁻¹).coord ∈ fast.baseChange ℝ := by
    intro t ht j hj
    exact H.invariant_outer t ht j (by omega)
  have hdecomposition := hsource F b ω hF J fast basis lift hfast hsection
    Z H.outer.1 H.outer.2 H.K H.dilation hlower N poly U pPhase Rrank hcorrelation
  obtain ⟨q, K, pair, hpair⟩ :=
    CertifiedFullChartDetectedDecomposition.exists_admissible_stage
      F b ω hF J (n + 1) fast basis lift Z H.outer.1 H.outer.2 H.K U poly N
      ((pPhase + C) ^ C) hdecomposition
  refine ⟨q, K, pair, hpair, ?_⟩
  have hpairB := FullChartAdmissibleStageCorrection.mono_budget hpair hbudget
  exact T.exists_representative_child hn hH q K pair hpairB

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection
  CertifiedFullChartFiniteHistory.outer

theorem exists_certified_budgeted_tree_terminal_constants (s m a : ℕ) :
    ∃ Ccontrol : ℕ, 2 ≤ Ccontrol ∧ ∃ Cphase : ℕ → ℕ,
      (∀ n, 2 ≤ Cphase n) ∧
    ∀ {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype ι] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (J : Fin m → Type) [∀ j, Fintype (J j)]
      (fast : Submodule ℚ F.AssociatedGraded)
      (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
      (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded),
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω fast →
      (∀ y, fast.mkQ (lift y) = y) →
    ∀ (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
      (Utag : ∀ j, Submodule ℝ (J j → ℝ))
      (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
      (Bphase B pTree Rrank : ℝ) (H qS : ℕ)
      (cap cumulative pControl pPhase : ℕ → ℝ)
      (T : CertifiedFullChartFiniteHistory.BudgetedBranchTree F b ω hF J fast basis lift
        Z Utag poly N Bphase cap s pTree),
      1 ≤ H → 0 < qS →
      (∀ n ≤ s, 0 ≤ pControl n) →
      (∀ n ≤ s, 0 ≤ cumulative n) →
      (∀ n < s, cumulative n ≤ cumulative (n + 1)) →
      (∀ n < s, cap n ≤ cumulative (n + 1)) →
      (∀ n ≤ s, ∀ j < n, cap j ≤ cumulative n) →
      (∀ n < s, (pPhase n + Cphase n) ^ Cphase n ≤ cap n) →
      (∀ n ≤ s, (Fintype.card ι : ℝ) ≤ pControl n) →
      (∀ n ≤ s, (Fintype.card (X ⊕ (Σ j, J j)) : ℝ) ≤ pControl n) →
      (∀ n ≤ s, (H : ℝ) ≤ Real.exp (pControl n)) →
      (∀ i j z, RationalHeightLE ((F.associatedGradedBasis b ω hF).repr
        ⁅F.associatedGradedBasis b ω hF i, F.associatedGradedBasis b ω hF j⁆ z) H) →
      (∀ n ≤ s, (qS : ℝ) * Real.exp ((s : ℝ) * (Fintype.card η : ℝ) * cumulative n) ≤
        Real.exp (pControl n)) →
      (∀ n ≤ s, (Fintype.card η : ℝ) * B * Real.exp (cumulative n) ≤
        Real.exp ((pControl n + 2) ^ a)) →
      (∀ i j, |((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i| ≤ B) →
      (∀ j, (fun i => ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr
        (lift.baseChange ℝ (basis j)) i) ∈ realDenominatorGrid qS) →
      (∀ n, n ≤ s → ∀ history ∈ T.level n,
        FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
          ((pControl n + Ccontrol) ^ Ccontrol)) ∧
      ((∀ n, n < s → ∀ history ∈ T.level n,
        Nonempty (FullChartMajorCorrelationWitness F b ω hF J (n + 1) fast basis
          Z history.outer.1 history.outer.2 N poly Utag (pPhase n) Rrank (Cphase n))) →
    ∃ history ∈ T.level s,
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl s + Ccontrol) ^ Ccontrol) ∧
      RationalTaggedConstraintCertificate J Set.univ history.K (cumulative s)
        (s * (Fintype.card η * m)) ∧
      ∀ point ∈ history.K,
        eval₂ point (F.realGradedSymbolPolynomial b ω hF (fullTaggedVariableWeight J)
          (history.outer.1⁻¹ * Z * history.outer.2⁻¹).coord) ∈ fast.baseChange ℝ) := by
  obtain ⟨Ccontrol, hCcontrol, hcontrol⟩ := exists_certified_full_chart_history_control s a
  let Cphase : ℕ → ℕ := fun n => Classical.choose
    (CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness m n)
  have hphase (n : ℕ) := Classical.choose_spec
    (CertifiedFullChartFiniteHistory.exists_budgeted_reached_child_of_major_correlation_witness m n)
  refine ⟨Ccontrol, hCcontrol, Cphase, fun n => (hphase n).1, ?_⟩
  intro X L ι η _ _ _ _ _ _ F b ω hF J _ fast basis lift hfast hsection
    Z Utag poly N Bphase B pTree Rrank H qS cap cumulative pControl pPhase T hH hqS
    hp hcumulative hmono hcap hprefix hdetect hι hσ hHp hstructure hden hcost hentry hgrid
  have hbounds := T.stage_bounds hmono hcap
  have hcontrolled (n : ℕ) (hn : n ≤ s)
      (history : CertifiedFullChartFiniteHistory F b ω hF J fast basis lift
        Z Set.univ Utag poly N Bphase n) (hmem : history ∈ T.level n) :
      FullChartControlledFactors F b ω hF J poly N history.outer.1 history.outer.2
        ((pControl n + Ccontrol) ^ Ccontrol) := by
    let hsmall := (hbounds n hn history hmem).to_budget (hprefix n hn)
    have hactual := hcontrol F b ω hF J fast basis lift Z Set.univ Utag poly N
      (cumulative n) B (pControl n) H qS n hH (hp n hn) (hcumulative n hn) hqS hn
      (hι n hn) (hσ n hn) (hHp n hn) hstructure (hden n hn) (hcost n hn)
      hentry hgrid hsmall
    dsimp only [hsmall] at hactual
    rw [(hbounds n hn history hmem).to_budget_outer (hprefix n hn)] at hactual
    exact hactual
  refine ⟨hcontrolled, ?_⟩
  intro hsource
  have hreached : ∀ n, n ≤ s → (T.level n).Nonempty := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨CertifiedFullChartFiniteHistory.univInitialHistory F b ω hF J fast basis lift
        Z Utag poly N Bphase, by
          change _ ∈ finiteGradedBranchLevel _ _ 0
          exact (finiteGradedBranchLevel_mem_zero _ _ _).mpr rfl⟩
    | succ n ih =>
      intro hn
      have hns : n < s := Nat.lt_of_succ_le hn
      obtain ⟨history, hmem⟩ := ih (Nat.le_of_succ_le hn)
      have hcorr := hsource n hns history hmem
      obtain ⟨q, K, pair, _, next, hnext, _, _⟩ := (hphase n).2
        F b ω hF J fast basis lift hfast hsection Z Utag poly N Bphase pTree
        (pPhase n) Rrank cap s T history hns hmem (hdetect n hns) hcorr
      exact ⟨next, hnext⟩
  obtain ⟨history, hmem⟩ := hreached s le_rfl
  exact ⟨history, hmem, hcontrolled s le_rfl history hmem,
    (hbounds s le_rfl history hmem).certificate, history.terminal_mem_fast hfast⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PreparedDeterminingMatrixBudget
namespace OAI

section

namespace Erdos3

open Module Submodule VectorPolynomial BohrLattice.MinkowskiSecondBox
open scoped BigOperators

namespace RankPreparationLayer

variable {X J : Type} (L : RankPreparationLayer X J)

theorem rank_le_coord_card : L.rank ≤ Fintype.card L.Coord := by
  have h := L.rank_add_orthogonal_finrank
  omega

attribute [local irreducible] rank

end RankPreparationLayer

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PreparedFullChartNativeDetection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

attribute [local instance] NativeSampleModelFamily.lie NativeSampleModelFamily.algebra
  NativeSampleModelFamily.topology NativeSampleModelFamily.topologicalAdd
  NativeSampleModelFamily.continuousSMul NativeSampleModelFamily.hausdorff

theorem exists_full_chart_major_correlation_witness_of_native_detections
    {m k t : ℕ} {X L ι η : Type} [Fintype X] [DecidableEq X] [Fintype η]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (Ψ : PatchKernel (Fintype.card (LowTaggedIndex J k)))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (β : (X → ℤ) → Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hβ : ∀ u ∈ integerBox N, ∀ i,
      |MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) -
        c i - (β u i : ℝ)| ≤ 1 / 2)
    {periodCap coverCap : ℝ} {Lip : ℝ≥0}
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hperiod : periodCap ≤ Real.exp pMajor) (hcover : coverCap ≤ Real.exp pMajor)
    (hLip : (Lip : ℝ) ≤ Real.exp pMajor) (hΨ : (Ψ.lip : ℝ) ≤ Real.exp pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (hdetected : ∀ j,
      ∃ (W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap Lip)
        (g : integerBox N → ℂ),
        Nonempty (NativeSampleModel (fun _ : X => 1) t pNative
          (fun u : integerBox N => u.val) g) ∧
        Real.exp (-pNative) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
            (fun u => majorPhaseSample J k poly Ψ c
              (coordinate (basis.coord j).toAddMonoidHom
                (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                  (fullTaggedVariableWeight (X := X) J) fast k
                    (left⁻¹ * Z * right⁻¹).coord))) β (fun _ => 1) u.val)
            (fun u => star (W.eval N poly u.val) * g u)‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  obtain ⟨W, g, common, hcorr⟩ := exists_native_major_correlation_family_of_detections
    J N hbox poly Ψ c
    (fun j => coordinate (basis.coord j).toAddMonoidHom
      (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
        (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
    β pNative hpNative hη hdetected
  refine ⟨{
    L := common.L
    step := t
    dim := common.dim
    model := common.model
    lower := htk
    correlation := ?_ }⟩
  unfold FullChartMajorCorrelation
  refine ⟨periodCap, coverCap, Lip, W, (fun j => (common.test j).conjugate),
    Ψ, c, β, hpoly, hcoeff, hβ, ?_, ?_, ?_, hdim, ?_, ?_, hLip, hΨ,
    hN, hRrank, hrank, ?_⟩
  · linarith
  · intro j
    exact ((common.test j).conjugate_complexityLE pMajor).mpr
      ((common.complexity j).mono hproduct)
  · intro j
    exact_mod_cast common.norm j
  · exact fun j => (W j).modulus_bound.trans hperiod
  · exact fun j => (W j).cover_bound.trans hcover
  · intro j
    exact (Real.exp_le_exp.mpr (neg_le_neg hNativeMajor)).trans (hcorr j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct NNReal

def SampledSliceNativeDetection
    {m : ℕ} {X Ω T : Type} [Fintype X] [DecidableEq X] [Fintype Ω] [Fintype T]
    {Tests : Ω → Type} (J : Fin m → Type) [∀ j, Fintype (J j)]
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (pathLaw : FiniteProbabilityWeights Ω) (physical : Ω → T → X → ℤ)
    (slices : ∀ z, Tests z → Finset T) (weight : ∀ z, Tests z → T → ℂ)
    (degree : ℕ) (pNative α : ℝ) : Prop :=
  ∀ signal : (X → ℤ) → ℂ,
    (∀ u, ‖signal u‖ ≤ 1) →
    (∀ u, u ∉ integerBox N → signal u = 0) →
    α ≤ sampledSliceSeminorm pathLaw physical slices weight signal →
    ∃ (W : NormalizedPolynomialTwist X (Σ j, J j)
        (Real.exp pNative) (Real.exp pNative) ⟨Real.exp pNative, Real.exp_nonneg _⟩)
      (g : integerBox N → ℂ),
      Nonempty (NativeSampleModel (fun _ : X => 1) degree pNative
        (fun u : integerBox N => u.val) g) ∧
      Real.exp (-pNative) ≤
        ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) hbox).correlation
          (fun u => signal u.val) (fun u => star (W.eval N poly u.val) * g u)‖

noncomputable def majorPhasePlateauBoxSignal
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ) :
    (X → ℤ) → ℂ :=
  (integerBox N : Set (X → ℤ)).indicator (majorPhasePlateauSignal J k poly c P)

theorem majorPhasePlateauBoxSignal_inside
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (hu : u ∈ integerBox N) :
    majorPhasePlateauBoxSignal J k N poly c P u = majorPhasePlateauSignal J k poly c P u :=
  Set.indicator_of_mem hu _

theorem majorPhasePlateauBoxSignal_outside
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) (hu : u ∉ integerBox N) :
    majorPhasePlateauBoxSignal J k N poly c P u = 0 :=
  Set.indicator_of_notMem hu _

theorem majorPhasePlateauBoxSignal_norm_le_one
    {m : ℕ} {X : Type} [Fintype X] [DecidableEq X] (J : Fin m → Type) [∀ j, Fintype (J j)]
    (k : ℕ) (N : X → ℕ) (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (P : MvPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℝ)
    (u : X → ℤ) : ‖majorPhasePlateauBoxSignal J k N poly c P u‖ ≤ 1 := by
  classical
  by_cases hu : u ∈ integerBox N
  · rw [majorPhasePlateauBoxSignal_inside J k N poly c P u hu]
    exact majorPhasePlateauSignal_norm_le_one J k poly c P u
  · rw [majorPhasePlateauBoxSignal_outside J k N poly c P u hu, norm_zero]
    exact zero_le_one

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal

theorem exists_full_chart_major_correlation_witness_of_prepared_detection
    {m k t : ℕ} {X L ι η Ω T : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype T]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    {Tests : Ω → Type} (pathLaw : FiniteProbabilityWeights Ω)
    (physical : Ω → T → X → ℤ) (slices : ∀ z, Tests z → Finset T)
    (weight : ∀ z, Tests z → T → ℂ) (α : ℝ)
    (hdirect : SampledSliceNativeDetection J N hbox poly pathLaw physical slices weight t pNative α)
    (hlarge : ∀ j, α ≤ sampledSliceSeminorm pathLaw physical slices weight
      (majorPhasePlateauBoxSignal J k N poly c
        (coordinate (basis.coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
            (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))))) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  have hNative0 : 0 ≤ pNative := by linarith
  have hseven : 7 ≤ pMajor := by
    have h := (productNiltestBudget_geometry hNative0).trans hproduct
    nlinarith
  have hkernel : ((majorPhasePlateauKernel (Fintype.card (LowTaggedIndex J k))).lip : ℝ) ≤
      Real.exp pMajor := by
    change (8 : ℝ) ≤ Real.exp pMajor
    linarith [Real.add_one_le_exp pMajor]
  have hexp := Real.exp_le_exp.mpr hNativeMajor
  apply exists_full_chart_major_correlation_witness_of_native_detections
    (Lip := ⟨Real.exp pNative, Real.exp_nonneg _⟩)
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff
    (majorPhasePlateauKernel _) c (majorPhaseNearestLift J k poly c)
    (fun u _ i => majorPhaseNearestLift_close J k poly c u i)
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim
    hexp hexp hexp hkernel hN hRrank hrank
  intro j
  let P := coordinate (basis.coord j).toAddMonoidHom
    (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
      (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))
  obtain ⟨W, g, hmodel, hcorr⟩ := hdirect (majorPhasePlateauBoxSignal J k N poly c P)
    (majorPhasePlateauBoxSignal_norm_le_one J k N poly c P)
    (majorPhasePlateauBoxSignal_outside J k N poly c P) (hlarge j)
  refine ⟨W, g, hmodel, ?_⟩
  have heq : (fun u : integerBox N => majorPhasePlateauBoxSignal J k N poly c P u.val) =
      fun u : integerBox N => majorPhasePlateauSignal J k poly c P u.val := by
    funext u
    exact majorPhasePlateauBoxSignal_inside J k N poly c P u.val u.property
  rw [heq] at hcorr
  exact hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators

theorem exists_full_chart_major_correlation_witness_of_productive_local_tests
    {m k t : ℕ} {X L ι η Ω I : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (pathLaw : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (localN : I → ℕ) (hlocalN : ∀ i, 0 < localN i)
    (cost : ℝ) (hcost : 0 ≤ cost)
    (physical : Ω → (I → ℤ) → X → ℤ)
    (hphysical : ∀ j z, z ∈ good j → ∀ x,
      x ∈ integerBox localN → physical z x ∈ integerBox N)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * pathLaw.mass (good j))
    (hdirect : ∀ chosen : Ω → Option η →
      LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : integerBox localN) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox localN) => (chosen z a).weight x.val) t pNative α)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (physical z x) * A.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  let phase := fun j => coordinate (basis.coord j).toAddMonoidHom
    (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
      (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord))
  let signal := fun j => majorPhasePlateauBoxSignal J k N poly c (phase j)
  have hlocalBox : ∀ j z, z ∈ good j →
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN cost
        (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          signal j (physical z x) * A.weight x‖ := by
    intro j z hz
    obtain ⟨A, hA⟩ := hlocal j z hz
    refine ⟨A, ?_⟩
    have heq : (𝔼 x ∈ A.slice.integerPoints, signal j (physical z x) * A.weight x) =
        𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c (phase j) (physical z x) * A.weight x := by
      apply Finset.expect_congr rfl
      intro x hx
      rw [show signal j (physical z x) =
          majorPhasePlateauSignal J k poly c (phase j) (physical z x) from
        majorPhasePlateauBoxSignal_inside J k N poly c (phase j) (physical z x)
          (hphysical j z hz x (A.slice.integerPoints_subset_integerBox hx))]
    rw [heq]
    exact hA
  obtain ⟨chosen, _, hlarge⟩ := exists_productive_localMajorSlice_coordinate_family
    (OrdinaryPolynomialPhase.nilmanifold t) pathLaw good localN hlocalN cost
    (OrdinaryPolynomialPhase.budget t) (9 / 10)
    (OrdinaryPolynomialPhase.zeroLocalMajorSlice localN hlocalN cost hcost)
    physical signal hlocalBox
  apply exists_full_chart_major_correlation_witness_of_prepared_detection
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff c
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim hN hRrank hrank
    pathLaw (fun z (x : integerBox localN) => physical z x.val)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a (x : integerBox localN) => (chosen z a).weight x.val)
    α (hdirect chosen)
  intro j
  exact (hmass j).trans (hlarge j)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped TensorProduct NNReal BigOperators Classical

theorem exists_full_chart_major_correlation_witness_of_frozen_productive_local_tests
    {m k t : ℕ} {X L ι η Ω I : Type}
    [Fintype X] [DecidableEq X] [Fintype η] [Fintype Ω] [Fintype I] [DecidableEq I]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
      OrdinaryPolynomialPhase.weight t)]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (N : X → ℕ) (hbox : (integerBox N).Nonempty)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (hcoeff : ∀ j α, α ≠ 0 → coefficients (poly j) α ∈ U j)
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (pathLaw : FiniteProbabilityWeights Ω) (good : η → Finset Ω)
    (localN : I → ℕ) (hlocalN : ∀ i, 0 < localN i)
    (keep : I → Prop) (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (localN i : ℝ) ≤ Bshort)
    (physical : Ω → (I → ℤ) → X → ℤ)
    (hphysical : ∀ j z, z ∈ good j → ∀ x,
      x ∈ integerBox localN → physical z x ∈ integerBox N)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * pathLaw.mass (good j))
    (hdirect : ∀ chosen : Ω → Option η →
      LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t) localN (max cost (Real.log Bshort))
        (OrdinaryPolynomialPhase.budget t),
      SampledSliceNativeDetection J N hbox poly pathLaw
        (fun z (x : integerBox localN) => physical z x.val)
        (fun z a => (chosen z a).slice.subtypeSites)
        (fun z a (x : integerBox localN) => (chosen z a).weight x.val) t pNative α)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < localN i.val) ∧
      ∃ A : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
        (fun i : {i // keep i} => localN i.val) cost (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (physical z (finiteSplitPoint keep x fixed)) * A.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_full_chart_major_correlation_witness_of_productive_local_tests
    F b ω hF J fast basis Z left right htk N hbox poly hpoly U hcoeff c
    pNative pMajor Rrank C hpNative hη hNativeMajor hproduct hdim hN hRrank hrank
    pathLaw good localN hlocalN (max cost (Real.log Bshort))
    (hcost.trans (le_max_left _ _)) physical hphysical α hmass hdirect
  intro j z hz
  obtain ⟨fixed, hfixed, A, hA⟩ := hlocal j z hz
  let starts := frozenShortStarts keep fixed
  have hstarts := frozenShortStarts_inside keep fixed hfixed
  refine ⟨A.freezeShort keep starts hstarts hBshort hshort, ?_⟩
  rw [A.expect_freezeShort keep starts hstarts hBshort hshort
    (fun x => majorPhasePlateauSignal J k poly c
      (coordinate (basis.coord j).toAddMonoidHom
        (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
          (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
      (physical z x))]
  simpa only [starts, frozenLongExtension_shortStarts keep fixed (fun i => (hfixed i).1)] using hA

end Erdos3.NilpotentLieFiltration

end

end OAI
end


