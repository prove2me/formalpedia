-- Prove2me | Definitions.Def_OAIE3v2B148
-- name    : OAIE3v2B148
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:20:04.039483+00:00
-- url     : https://prove2.me/theorems/1645ef4a-9a2f-4541-a5d6-d8ec97a1448b
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 150 of 311
-- statement:
--   Definitions bundle 150 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129`, `OAIE3v2B130`, `OAIE3v2B131`, `OAIE3v2B132`, `OAIE3v2B133`, `OAIE3v2B134`, `OAIE3v2B136`, `OAIE3v2B137` of this split.
--
--   Modules: `Dynamics/ActualPathCurrentGradeReset.lean`, `Dynamics/PreparedFiniteStageNativeBudget.lean`, `Dynamics/ProjectedPotentialGroupIdentity.lean`, `Dynamics/RestrictedGradePathMembership.lean`, `Dynamics/TranslationMajorDetectedPotential.lean`, `Estimates/CenteredFiniteSliceResidualEnvelope.lean`, `Estimates/FixedObservableCorrelation.lean`, `Estimates/RationalCentralCircle.lean`, `Estimates/RealTranslationEvaluationContinuity.lean`, `Estimates/RefilteredPointwiseSplitting.lean`, `Estimates/RelativePatchAmplification.lean`, `Estimates/SimultaneousSymbolSplitting.lean`, `Estimates/SymbolCommonCorrections.lean`, `Estimates/SymbolFastMembership.lean`, `Estimates/VectorRealSubstitutionBound.lean`, `Fourier/PivotAnnihilatorFrequencyCode.lean`, `Geometry/ControlledGradedBaseCoordinates.lean`, `Geometry/GlobalChartNativeFactorization.lean`, `Lattices/RealSymbolAffine.lean`, `Lattices/SourceLatticeCover.lean`, `Linear/RationalKernelInvariance.lean`, `Linear/RefilteredKernelConstantBounds.lean`, `Nilpotent/CyclicNiltestApproximation.lean`, `Nilpotent/FactorwiseBCHCovers.lean`, `Nilpotent/NiltestAffineProjection.lean`, `Nilpotent/NiltestComplement.lean`, `Nilpotent/PolynomialShearNilmanifold.lean`, `Polynomial/MajorTranslationDegreeSymbol.lean`, `Polynomial/PolynomialPatchShearOrbit.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Polynomial/QuantitativeOuterPolynomialProducts.lean`, `Polynomial/SimultaneousPolynomialSymbolSplitting.lean`, `Polynomial/TwistedBufferedTranslationPhase.lean`, `Sampling/PositiveGridFamily.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129
import Definitions.Def_OAIE3v2B130
import Definitions.Def_OAIE3v2B131
import Definitions.Def_OAIE3v2B132
import Definitions.Def_OAIE3v2B133
import Definitions.Def_OAIE3v2B134
import Definitions.Def_OAIE3v2B136
import Definitions.Def_OAIE3v2B137

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open NilpotentLieBCHGroup

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)]
  [DecidableEq α] {s : ℕ}

theorem piBCHSubgroup_le_of_factors [Finite α] (F : ∀ a, NilpotentLieFiltration (M a) s)
    (Δ : ∀ a, Subgroup (F a).Group) (Λ : Subgroup (NilpotentLieFiltration.pi F).Group)
    (h : ∀ a, Δ a ≤ Λ.comap (bchPiSingle F a)) : piBCHSubgroup F Δ ≤ Λ := by
  intro g hg
  let Λ' := Λ.comap (bchPiEquiv F).symm.toMonoidHom
  have hp : bchPiEquiv F g ∈ Λ' := by
    apply Subgroup.pi_mem_of_mulSingle_mem
    intro a
    change (bchPiEquiv F).symm (Pi.mulSingle a (bchPiEquiv F g a)) ∈ Λ
    rw [← bchPiSingle_eq_symm_mulSingle]
    exact h a ((mem_piBCHSubgroup F Δ g).mp hg a)
  simpa only [Λ', Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] using hp

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieBCHGroup

variable {α : Type*} [Fintype α] [DecidableEq α] {M : α → Type*}
  [∀ a, LieRing (M a)] [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}
  (F : ∀ a, NilpotentLieFiltration (M a) s)
  {κ : α → Type*} [∀ a, Fintype (κ a)] (f : ∀ a, Basis (κ a) ℚ (M a))

theorem exists_factorwise_bch_covers (Γ : ∀ a, Subgroup (F a).Group) (l : α → ℕ)
    (hl : ∀ a, 0 < l a)
    (hΓin : ∀ a, scaledIntegerGrid (l a) ⊆ bchSubgroupCoordinates (f a) (Γ a))
    (hΓout : ∀ a, bchSubgroupCoordinates (f a) (Γ a) ⊆ denominatorGrid (l a))
    (Λ : Subgroup (NilpotentLieFiltration.pi F).Group) (m : ℕ) (hm : 0 < m)
    (hΛ : scaledIntegerGrid m ⊆ bchSubgroupCoordinates (Pi.basis f) Λ)
    {p : ℝ} (hp : 0 ≤ p) (hd : ∀ a, (Fintype.card (κ a) : ℝ) ≤ p)
    (hlp : ∀ a, (l a : ℝ) ≤ Real.exp p) (hmp : (m : ℝ) ≤ Real.exp p) :
    ∃ (Δ : ∀ a, Subgroup (F a).Group) (N : α → ℕ),
      (∀ a, Δ a ≤ Γ a ∧ ((Δ a).subgroupOf (Γ a)).Characteristic ∧
        ((Δ a).subgroupOf (Γ a)).Normal ∧ ((Δ a).subgroupOf (Γ a)).FiniteIndex ∧
        ((Δ a).relIndex (Γ a) : ℝ) ≤ Real.exp (2 * p ^ 2) ∧
        0 < N a ∧ (N a : ℝ) ≤ Real.exp ((p + 2) ^ 2) ∧
        scaledIntegerGrid (N a) ⊆ bchSubgroupCoordinates (f a) (Δ a) ∧
        bchSubgroupCoordinates (f a) (Δ a) ⊆ denominatorGrid (N a)) ∧
      piBCHSubgroup F Δ ≤ Λ := by
  have h := fun a => (F a).exists_normal_cover_exp_quadratic (f a) (Γ a)
    (Λ.comap (bchPiSingle F a)) (l a) m (hl a) hm (hΓin a) (hΓout a)
    (bchPiSingle_comap_inner_grid F f Λ m hΛ a) hp (hd a) (hlp a) hmp
  choose Δ htarget hΔ hchar hnormal hfinite hindex N hN hNb hin hout using h
  exact ⟨Δ, N, fun a => ⟨hΔ a, hchar a, hnormal a, hfinite a, hindex a,
    hN a, hNb a, hin a, hout a⟩, piBCHSubgroup_le_of_factors F Δ Λ htarget⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbit
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

theorem polynomialShearOrderedBasis_outer_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    bchSubgroupCoordinates (polynomialShearOrderedBasis w) (polynomialShearLattice w s hw) ⊆
      denominatorGrid s.factorial :=
  bchSubgroup_outer_grid_reindex (polynomialShearBasis w) (polynomialShearIndexOrder w) _
    (polynomialShearLattice_outer_grid s hw)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.PolynomialShearNilmanifold
namespace OAI

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearNilmanifold (s : ℕ) (hw : ∀ i, w i ≤ s) :
    RationalFilteredNilmanifold (PolynomialShearLieAlgebra w ℚ) s
      (Fintype.card (PolynomialShearIndex w)) where
  filtration := polynomialShearFiltration w s hw
  basis := polynomialShearOrderedBasis w
  layerBasis i := polynomialShearLayerFinBasis w (i.val + 1)
  lattice := polynomialShearLattice w s hw
  grid := s.factorial
  grid_pos := Nat.factorial_pos s
  inner_grid := polynomialShearOrderedBasis_inner_grid w s hw
  outer_grid := polynomialShearOrderedBasis_outer_grid w s hw

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3.PolynomialPatch

open NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} {s d : ℕ} (A : PolynomialPatch σ s d)
  [Fintype (PolynomialShearIndex A.weight)]

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ)]

theorem shearObservable_lipschitz (M : ℝ≥0)
    (hA : ∀ i, realPolynomialMass (A.form.center i) ≤ M) :
    letI : MetricSpace ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) :=
      (polynomialShearNilmanifold A.weight s A.weight_le).metricSpace
    LipschitzWith (A.shearObservableLipBound M) A.shearObservable := by
  let e := (polynomialShearOrderedBasis A.weight).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra A.weight ℚ) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (polynomialShearFiltration A.weight s A.weight_le).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift (polynomialShearRealLattice s A.weight_le)
    (polynomialShearRealLattice_closed_discrete s A.weight_le).1 A.shearObservable
    (A.shearOrbitSum_lipschitz M hA)

end Erdos3.PolynomialPatch

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CyclicNiltestApproximation
namespace OAI

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace RationalFilteredNilmanifold

namespace Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem unit_interval_eval (T : D.Niltest w) (hT : T.UnitIntervalValued) (x : σ → ℤ) :
    (T.eval x).im = 0 ∧ 0 ≤ (T.eval x).re ∧ (T.eval x).re ≤ 1 := hT _

end Niltest
end RationalFilteredNilmanifold
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FixedObservableCorrelation
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_observable_correlators (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      (D : RationalFilteredNilmanifold L s d)
      (T : G → D.Niltest (fun _ : Unit => 1)) (H : Finset G), H.Nonempty →
      ∀ {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      (∀ h ∈ H, (T h).ComplexityLE p) → (∀ h ∈ H, (T h).normBound ≤ 1) →
      ∀ {N : ℕ} [NeZero N] (weight : G → ZMod N → ℂ),
      (∀ h ∈ H, ∀ x, ‖weight h x‖ ≤ 1) →
      (∀ h ∈ H, Real.exp (-p) ≤
        ‖𝔼 x, weight h x * star ((T h).evalCyclic N (fun _ => x))‖) →
      ∃ (H' : Finset G) (S : G → D.Niltest (fun _ : Unit => 1)),
        H' ⊆ H ∧ H'.Nonempty ∧ Real.exp (-((p + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
        (∀ h, (S h).orbit = (T h).orbit ∧ (S h).normBound ≤ 1 ∧
          (S h).UnitIntervalValued ∧ (S h).ComplexityLE ((p + C) ^ C)) ∧
        (∀ h k, (S h).observable = (S k).observable) ∧
        ∀ h ∈ H', Real.exp (-((p + C) ^ C)) ≤
          ‖𝔼 x, weight h x * star ((S h).evalCyclic N (fun _ => x))‖ := by
  classical
  obtain ⟨A, _, hpartition⟩ := exists_native_positive_partition s 2
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C A) ^ A + 2)
  refine ⟨C, hC, ?_⟩
  intro G L _ _ _ _ _ _ d D T H hH p hp hD hT hcap N _ weight hweight hcorr
  let q := (p + A) ^ A
  have hq : 0 ≤ q := pow_nonneg (by positivity) _
  have hcost : p + q + 2 ≤ (p + C) ^ C := by
    simpa [X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : q ≤ (p + C) ^ C := by linarith
  let rho := Real.exp (-(2 * p + 1))
  have hrho : 0 < rho := Real.exp_pos _
  have hrhoinv : 1 / rho ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ = Real.exp (2 * p + 1) := by simp only [rho, one_div, ← Real.exp_neg, neg_neg]
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  let := D.metricSpace
  obtain ⟨n, hn, hnq, K, hK, ψ, hψ, hsum, hLip, hdiam⟩ :=
    hpartition D hp hD hrho hrhoinv
  let U (h : G) (i : Fin n) : D.Niltest (fun _ : Unit => 1) :=
    D.sectionNiltest (T h).orbit (fun z (_ : Unit) => ψ i z)
      (fun z _ => hψ i z) K (fun _ => hLip i) (some ())
  have hlog : Real.log (3 + (K : ℝ)) ≤ (p + C) ^ C := by
    apply (Real.log_le_iff_le_exp (by positivity)).mpr
    have h1 : 1 ≤ Real.exp q := Real.one_le_exp hq
    have h4 : (4 : ℝ) ≤ Real.exp 2 := by
      rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp (q + 2) := by
        rw [Real.exp_add]
        nlinarith [mul_le_mul_of_nonneg_left h4 (Real.exp_nonneg q)]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hU (h : G) (i : Fin n) : (U h i).orbit = (T h).orbit ∧ (U h i).normBound ≤ 1 ∧
      (U h i).UnitIntervalValued ∧ (U h i).ComplexityLE ((p + C) ^ C) := by
    refine ⟨rfl, le_rfl, ?_, ?_⟩
    · exact D.sectionNiltest_unit_interval _ _ _ _ _ _
    · exact D.sectionNiltest_complexityLE _ _ _ _ _ _ (hD.mono D hpC) hlog
  have hchoose (h : {h // h ∈ H}) : ∃ i : Fin n,
      Real.exp (-p) / (2 * Real.exp q) ≤
        ‖𝔼 x, weight h.val x * star ((U h.val i).evalCyclic N (fun _ => x))‖ := by
    obtain ⟨c, hc, happ⟩ := exists_complex_partition_approximation ψ
      (fun i z => (hψ i z).1) hsum hdiam (T h.val).observable
      (fun z => ((T h.val).norm_le z).trans (hcap h.val h.property)) (T h.val).lipschitz
    have hprecision : ((T h.val).lipBound : ℝ) * rho ≤ Real.exp (-p) / 2 := by
      have hbudgetT := Niltest.observable_budget (hT h.val h.property)
      have hlip : ((T h.val).lipBound : ℝ) ≤ Real.exp p := by
        have hnorm := (T h.val).normBound.coe_nonneg
        linarith
      calc
        _ ≤ Real.exp p * rho := mul_le_mul_of_nonneg_right hlip hrho.le
        _ = Real.exp (-p - 1) := by
          dsimp [rho]
          rw [← Real.exp_add]
          congr 1
          ring
        _ ≤ _ := exp_sub_one_le_half_exp _
    obtain ⟨i, hi⟩ := exists_correlating_summand Finset.univ_nonempty (weight h.val)
      (fun x => (T h.val).evalCyclic N (fun _ => x))
      (fun i x => (U h.val i).evalCyclic N (fun _ => x) * c i)
      (Real.exp_pos (-p)) (Real.exp_pos q) (by simpa only [Fintype.card_fin] using hnq)
      (fun x _ => hweight h.val h.property x)
      (fun x _ => by
        rw [norm_sub_rev]
        exact (happ (D.cyclicOrbitPoint (T h.val).orbit N (fun _ => x))).trans hprecision)
      (hcorr h.val h.property)
    refine ⟨i, hi.trans ?_⟩
    have heq : finiteCorrelation Finset.univ (weight h.val)
        (fun x => (U h.val i).evalCyclic N (fun _ => x) * c i) =
        star (c i) * finiteCorrelation Finset.univ (weight h.val)
          (fun x => (U h.val i).evalCyclic N (fun _ => x)) := by
      simp only [finiteCorrelation, Finset.mul_expect]
      apply Finset.expect_congr rfl
      intro x _
      simp only [star_mul]
      ring
    rw [heq, norm_mul, norm_star]
    exact (mul_le_mul_of_nonneg_right (hc i) (norm_nonneg _)).trans_eq (one_mul _)
  choose choice hchoice using hchoose
  let code : G → Fin n := fun h => if hh : h ∈ H then choice ⟨h, hh⟩ else ⟨0, hn⟩
  obtain ⟨i, _, H', hsub, hnonempty, hconstant, hdense⟩ :=
    exists_exponential_constant_fiber H hH code Set.univ (Set.toFinite _)
      (fun _ _ => Set.mem_univ _) (by simpa only [Set.ncard_univ, Nat.card_eq_fintype_card,
        Fintype.card_fin] using hnq)
  refine ⟨H', fun h => U h i, hsub, hnonempty, ?_, fun h => hU h i, fun _ _ => rfl, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hqC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    have hcode : choice ⟨h, hsub hh⟩ = i := by
      simpa only [code, dif_pos (hsub hh)] using hconstant h hh
    have hc := hchoice ⟨h, hsub hh⟩
    rw [hcode] at hc
    apply le_trans _ hc
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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolFastMembership
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

theorem polynomialSymbolDilation_repr (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (x : F.PolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hF w).repr (F.polynomialSymbolDilation w r x) z =
      r ^ Finsupp.weight w z.val.1 * (F.polynomialSymbolBasis b ω hF w).repr x z := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolDilation_map, F.polynomialSymbolBasis_repr_map,
    F.polynomialSymbolBasis_repr_map]
  change b.repr (coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) z.val.1) z.val.2 = _
  rw [coefficients_weightedDilation, map_smul, Finsupp.smul_apply, smul_eq_mul]

theorem realPolynomialSymbolDilation_repr (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr (F.realPolynomialSymbolDilation w r x) z =
      (r : ℝ) ^ Finsupp.weight w z.val.1 * ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [F.realPolynomialSymbolDilation_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, F.polynomialSymbolDilation_repr]
    simp only [Rat.smul_def, Rat.cast_mul, Rat.cast_pow]
    ring
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]

theorem realSymbolOfPolynomial_dilation (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r p) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
  ext z
  rw [F.realPolynomialSymbolDilation_repr, F.realSymbolOfPolynomial_coordinate,
    F.realSymbolOfPolynomial_coordinate]
  simp only [coefficients_weightedDilation, map_rat_smul, Finsupp.smul_apply,
    Rat.smul_def, Rat.cast_pow]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolRationalGrid_dilation_ratio (w : σ → ℕ) (D d : ℕ) (a : ℤ) (hd : 0 < d)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w D g) :
    F.SymbolRationalGrid b ω hF w (D * d ^ s)
      (F.realPolynomialSymbolDilationHom w ((a : ℚ) / d) g) := by
  change (fun z => ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
    (F.realPolynomialSymbolDilationHom w ((a : ℚ) / d) g).coord z) ∈ _
  simp_rw [F.realPolynomialSymbolDilationHom_coord, F.realPolynomialSymbolDilation_repr,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact realDenominatorGrid_rational_power_scale (fun z : SymbolBasisIndex w ω => Finsupp.weight w z.val.1)
    D d s a hd (fun z => z.property.le.trans (F.adaptedBasis_weight_le_step b ω hF z.val.2)) _ hg

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.RestrictedGradePathMembership
namespace OAI

section

namespace Erdos3

namespace NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem reset_real_splitting (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L))
    (hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (j : ℕ) (E P R E₀ R₀ : F.realification.Group)
    (hP : P.coord ∈ U)
    (hleft : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (E₀⁻¹ * E) ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j)))
    (hright : NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (R * R₀⁻¹) ∈
      (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U).map
        (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))) :
    let A := F.truncateRealGrades b w j (E₀⁻¹ * E)
    let D := F.truncateRealGrades b w j (R * R₀⁻¹)
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      (A * P * D).coord ∈ U ∧
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (E * A⁻¹) =
        NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) E₀ ∧
      NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) (D⁻¹ * R) =
        NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j) R₀ := by
  exact reset_splitting_in_quotient
    (NilpotentLieBCHGroup.quotientHom (hnil := F.realification.lowerCentralSeries_eq_bot) (F.realification.layerIdeal j))
    (NilpotentLieBCHGroup.realLieSubgroup (hnil := F.realification.lowerCentralSeries_eq_bot) U) E P R E₀ R₀
    (F.truncateRealGrades b w j (E₀⁻¹ * E)) (F.truncateRealGrades b w j (R * R₀⁻¹)) hP
    (F.truncateRealGrades_mem_of_quotient_mem b w hlayers U hU j _ hleft)
    (F.truncateRealGrades_mem_of_quotient_mem b w hlayers U hU j _ hright)
    (F.truncateRealGrades_quotient b w hlayers j _) (F.truncateRealGrades_quotient b w hlayers j _)

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_symbol_reset_bounds (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ E E₀ R R₀ : F.RealPolynomialSymbolGroup w,
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
          F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        ∀ j : ℕ,
          let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
          let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
            F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨c₁, _, hslow₁⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨c₂, _, hslow₂⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨cr, _, hrat⟩ := exists_symbol_rational_product_bound s 2
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + (Polynomial.X + Polynomial.C c₁) ^ c₁ +
    (Polynomial.X + Polynomial.C cr) ^ cr + Polynomial.X + 2
  let B : Polynomial ℕ := (Q + Polynomial.C c₂) ^ c₂ + (Q + Polynomial.C cr) ^ cr
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  let q : ℝ := (p + 2) ^ a + (p + c₁) ^ c₁ + (p + cr) ^ cr + p + 2
  have ha0 : 0 ≤ (p + 2) ^ a := by positivity
  have hs0 : 0 ≤ (p + c₁) ^ c₁ := by positivity
  have hr0 : 0 ≤ (p + cr) ^ cr := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + 2) ^ a ≤ q + 2 := by dsimp [q]; linarith
  have hsq : (p + c₁) ^ c₁ ≤ q + 2 := by dsimp [q]; linarith
  have hrq : (p + cr) ^ cr ≤ q := by dsimp [q]; linarith
  have hboth : (q + c₂) ^ c₂ + (q + cr) ^ cr ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hbound p hp
  have hsfinal : (q + c₂) ^ c₂ ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hboth
  have hrfinal : (q + cr) ^ cr ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hboth
  obtain ⟨m₁, hm₁, hm₁p, hlm₁, hproducts₁⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  obtain ⟨m₂, hm₂, hm₂p, hm₁m₂, hproducts₂⟩ := hrat F b ω hlayers w hw H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hb m₁ hm₁
    (hm₁p.trans (Real.exp_le_exp.mpr hrq))
  refine ⟨m₂, hm₂, hm₂p.trans (Real.exp_le_exp.mpr hrfinal), hlm₁.trans hm₁m₂, ?_⟩
  intro E E₀ R R₀ hE hE₀ hR hR₀
  have hA : F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + c₁) ^ c₁)) (E₀⁻¹ * E) := by
    have hi : ∀ g ∈ [E₀⁻¹, E], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact (F.symbolSlowBound_inv_iff b ω hlayers w T _ E₀).mpr hE₀
      · exact hE
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hslow₁ F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT [E₀⁻¹, E] (by simp) hi
  have hD : F.SymbolRationalGrid b ω hlayers w m₁ (R * R₀⁻¹) := by
    have hi : ∀ g ∈ [R, R₀⁻¹], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hR
      · exact F.symbolRationalGrid_inv b ω hlayers w l hR₀
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts₁ [R, R₀⁻¹] (by simp) hi
  intro j
  dsimp only
  constructor
  · have hi : ∀ g ∈ [E, (F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E))⁻¹],
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((q + 2) ^ 1)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr (by simpa using haq)) _ hE
      · apply (F.symbolSlowBound_inv_iff b ω hlayers w T _ _).mpr
        exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr (by simpa using hsq)) _
          (F.truncateRealSymbol_slow b ω hlayers w j _ T _ hA)
    have hnew := hslow₂ F b ω hlayers w hw H q hH hq (hι.trans hpq) (hσ.trans hpq)
      (hHp.trans (Real.exp_le_exp.mpr hpq)) hb T hT
      [E, (F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E))⁻¹] (by simp) hi
    simp only [List.prod_cons, List.prod_nil, mul_one] at hnew
    exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr hsfinal) _ hnew
  · have hi : ∀ g ∈ [(F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹))⁻¹, R],
        F.SymbolRationalGrid b ω hlayers w m₁ g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact F.symbolRationalGrid_inv b ω hlayers w m₁
          (F.truncateRealSymbol_rational b ω hlayers w j _ m₁ hD)
      · exact F.symbolRationalGrid_mono b ω hlayers w hl hlm₁ _ hR
    simpa only [List.prod_cons, List.prod_nil, mul_one] using
      hproducts₂ [(F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹))⁻¹, R] (by simp) hi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

abbrev RealSymbolGradeQuotientGroup (j : ℕ) :=
  NilpotentLieBCHGroup
    (F.RealPolynomialSymbol w ⧸ (F.polynomialSymbolFiltration w).realification.layerIdeal j) s
    (lie_quotient_lowerCentralSeries_eq_bot
      (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))
      ((F.polynomialSymbolFiltration w).realification.layerIdeal j))

noncomputable def realSymbolGradeQuotientHom (j : ℕ) :
    F.RealPolynomialSymbolGroup w →* F.RealSymbolGradeQuotientGroup w j :=
  NilpotentLieBCHGroup.quotientHom ((F.polynomialSymbolFiltration w).realification.layerIdeal j)

theorem reset_real_symbol_splitting (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (hU : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) U.toSubmodule)
    (j : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hleft : F.realSymbolGradeQuotientHom w j (E₀⁻¹ * E) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j))
    (hright : F.realSymbolGradeQuotientHom w j (R * R₀⁻¹) ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j)) :
    let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
    let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
    (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
      (A * P * D).coord ∈ realificationLieSubalgebra U ∧
      F.realSymbolGradeQuotientHom w j (E * A⁻¹) = F.realSymbolGradeQuotientHom w j E₀ ∧
      F.realSymbolGradeQuotientHom w j (D⁻¹ * R) = F.realSymbolGradeQuotientHom w j R₀ := by
  have hUreal : BasisGradedSubmodule ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) (realificationLieSubalgebra U).toSubmodule :=
    hU.baseChange (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule
  exact (F.polynomialSymbolFiltration w).reset_real_splitting
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) (realificationLieSubalgebra U) hUreal
    j E P R E₀ R₀ hP hleft hright

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_controlled_symbol_reset (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ U : LieSubalgebra ℚ (F.PolynomialSymbol w),
        BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule →
        ∀ (j : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w),
        P.coord ∈ realificationLieSubalgebra U →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E₀ →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l R₀ →
        F.realSymbolGradeQuotientHom w j (E₀⁻¹ * E) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j) →
        F.realSymbolGradeQuotientHom w j (R * R₀⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w j) →
        let A := F.truncateRealSymbol b ω hlayers w j (E₀⁻¹ * E)
        let D := F.truncateRealSymbol b ω hlayers w j (R * R₀⁻¹)
        (E * A⁻¹) * (A * P * D) * (D⁻¹ * R) = E * P * R ∧
          (A * P * D).coord ∈ realificationLieSubalgebra U ∧
          F.realSymbolGradeQuotientHom w j (E * A⁻¹) = F.realSymbolGradeQuotientHom w j E₀ ∧
          F.realSymbolGradeQuotientHom w j (D⁻¹ * R) = F.realSymbolGradeQuotientHom w j R₀ ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A⁻¹) ∧
          F.SymbolRationalGrid b ω hlayers w m (D⁻¹ * R) := by
  obtain ⟨C, hC, hbound⟩ := exists_symbol_reset_bounds s a
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  obtain ⟨m, hm, hmp, hlm, hreset⟩ := hbound F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro U hU j E P R E₀ R₀ hP hE hE₀ hR hR₀ hleft hright
  obtain ⟨hprod, hmid, hEeq, hReq⟩ := F.reset_real_symbol_splitting w b ω hlayers U hU j E P R E₀ R₀ hP hleft hright
  obtain ⟨hslow, hgrid⟩ := hreset E E₀ R R₀ hE hE₀ hR hR₀ j
  exact ⟨hprod, hmid, hEeq, hReq, hslow, hgrid⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolCommonCorrections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem controlled_separation_at_layer (F : NilpotentLieFiltration L s)
    (e : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
    (U : LieSubalgebra ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ z i, RationalHeightLE (e.repr (v z) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (j : ℕ) (x y : ℝ ⊗[ℚ] L)
    (hx : ‖(e.baseChange ℝ).equivFun x‖ ≤ Real.exp (2 * p) / Real.exp (separationBudget (2 * p)))
    (hy : (e.baseChange ℝ).equivFun y ∈ realDenominatorGrid l)
    (hsum : x + y ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j) :
    x ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j ∧
      y ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔ F.realification.layer j := by
  let M : Matrix ι (κ ⊕ ι) ℚ := fun i z => e.repr (subalgebraLayerFamily e v ω j z) i
  have hM : ∀ i z, RationalHeightLE (M i z) H :=
    fun i z => subalgebraLayerFamily_height e v ω j hH hv z i
  have hcols : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hsum' : (e.baseChange ℝ).equivFun x + (e.baseChange ℝ).equivFun y ∈
      Submodule.span ℝ (Set.range (fun z i => (M i z : ℝ))) := by
    rw [← map_add]
    exact (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mp hsum
  obtain ⟨hx', hy'⟩ := controlled_small_vector_separation M hH hl hM (by linarith)
    (hι.trans (by linarith)) hcols (hHp.trans (Real.exp_le_exp.mpr (by linarith)))
    (hlp.trans (Real.exp_le_exp.mpr (by linarith))) _ _ hx hy hsum'
  exact ⟨(F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mpr hx',
    (F.real_subalgebra_layer_mem_iff_coordinates e ω hlayers U v hspan j _).mpr hy'⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem realSymbolGradeQuotient_mem_iff {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (k : ℕ) (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w k g ∈
        (NilpotentLieBCHGroup.realificationSubgroup
          (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map (F.realSymbolGradeQuotientHom w k) ↔
      g.coord ∈ (realLieSubalgebraOverRat (realificationLieSubalgebra U)).toSubmodule ⊔
        (F.polynomialSymbolFiltration w).realification.layer k :=
  NilpotentLieBCHGroup.quotient_mem_map_subgroup_iff
    ((F.polynomialSymbolFiltration w).realification.layerIdeal k)
    (realLieSubalgebraOverRat (realificationLieSubalgebra U)) g

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem symbol_current_grade_residual_mem
    {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (U : LieSubalgebra ℚ (F.PolynomialSymbol w))
    (hU : BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
      (fun z => ω z.val.2) U.toSubmodule)
    (k : ℕ) (E P R E₀ R₀ : F.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra U)
    (hE : F.realSymbolGradeQuotientHom w k E₀ = F.realSymbolGradeQuotientHom w k E)
    (hR : F.realSymbolGradeQuotientHom w k R = F.realSymbolGradeQuotientHom w k R₀) :
    let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
      (fun z => ω z.val.2) k
    π (E₀⁻¹ * (E * P * R) * R₀⁻¹).coord - π (E₀⁻¹ * E).coord - π (R * R₀⁻¹).coord ∈
      realificationLieSubalgebra U := by
  exact (F.polynomialSymbolFiltration w).realGradeProjection_normalized_residual_mem
    (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w)
    (realificationLieSubalgebra U).toSubmodule
    (hU.baseChange (F.polynomialSymbolBasis b ω hlayers w) (fun z => ω z.val.2) U.toSubmodule)
    k E P R E₀ R₀ hP hE hR

theorem exists_controlled_symbol_grade_step (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ T : σ → ℝ, (∀ i, 0 < T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {η : Type*} (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)),
        (∀ i, BasisGradedSubmodule (F.polynomialSymbolBasis b ω hlayers w)
          (fun z => ω z.val.2) (U i).toSubmodule) →
        ∀ (k : ℕ) (X E R A D : F.RealPolynomialSymbolGroup w),
        (∀ i, F.realSymbolGradeQuotientHom w k (E⁻¹ * X * R⁻¹) ∈
          (NilpotentLieBCHGroup.realificationSubgroup
            (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U i)).map
            (F.realSymbolGradeQuotientHom w k)) →
        A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k →
        D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k →
        (let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) k
         ∀ i, π (E⁻¹ * X * R⁻¹).coord - π A.coord - π D.coord ∈ realificationLieSubalgebra (U i)) →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) E →
        F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) A →
        F.SymbolRationalGrid b ω hlayers w l R → F.SymbolRationalGrid b ω hlayers w l D →
        (E * A) * (A⁻¹ * (E⁻¹ * X * R⁻¹) * D⁻¹) * (D * R) = X ∧
          F.realSymbolGradeQuotientHom w k (E * A) = F.realSymbolGradeQuotientHom w k E ∧
          F.realSymbolGradeQuotientHom w k (D * R) = F.realSymbolGradeQuotientHom w k R ∧
          (∀ i, F.realSymbolGradeQuotientHom w (k + 1) (A⁻¹ * (E⁻¹ * X * R⁻¹) * D⁻¹) ∈
            (NilpotentLieBCHGroup.realificationSubgroup
              (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) (U i)).map
              (F.realSymbolGradeQuotientHom w (k + 1))) ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) (E * A) ∧
          F.SymbolRationalGrid b ω hlayers w m (D * R) := by
  obtain ⟨cs, hcs, hslow⟩ := exists_symbol_slow_product_bound s a 2
  obtain ⟨cr, hcr, hrat⟩ := exists_symbol_rational_product_bound s 2
  refine ⟨max cs cr, hcs.trans (le_max_left _ _), ?_⟩
  intro σ ι L _ _ _ _ F b ω hlayers w hw H l p hH hl hp hι hσ hHp hlp hb T hT
  have hs : (p + cs) ^ cs ≤ (p + (max cs cr : ℕ)) ^ max cs cr :=
    shifted_power_self_mono hp (by omega) (le_max_left _ _)
  have hr : (p + cr) ^ cr ≤ (p + (max cs cr : ℕ)) ^ max cs cr :=
    shifted_power_self_mono hp (by omega) (le_max_right _ _)
  obtain ⟨m, hm, hmp, hlm, hproducts⟩ := hrat F b ω hlayers w hw H p hH hp hι hσ hHp hb l hl hlp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hr), hlm, ?_⟩
  intro η U hU k X E R A D hY hA hD hgrade hEslow hAslow hRgrid hDgrid
  let G := F.polynomialSymbolFiltration w
  let B := F.polynomialSymbolBasis b ω hlayers w
  have hUr : ∀ i, BasisGradedSubmodule (B.baseChange ℝ) (fun z => ω z.val.2)
      (realificationLieSubalgebra (U i)).toSubmodule :=
    fun i => (hU i).baseChange B (fun z => ω z.val.2) (U i).toSubmodule
  have hYr : ∀ i, (E⁻¹ * X * R⁻¹).coord ∈
      (realificationLieSubalgebra (U i)).toSubmodule ⊔ (G.realLayer k).toSubmodule :=
    fun i => (G.real_quotient_mem_subgroup_iff (realificationLieSubalgebra (U i)) k _).mp (hY i)
  obtain ⟨hprod, hEq, hRq, hnext⟩ := G.simultaneous_real_grade_correction B (fun z => ω z.val.2)
    (F.polynomialSymbolFiltration_layer b ω hlayers w) (fun i => realificationLieSubalgebra (U i))
    hUr k X E R A D hYr hA hD hgrade
  refine ⟨hprod, hEq, hRq, ?_, ?_, ?_⟩
  · intro i
    exact (G.real_quotient_mem_subgroup_iff (realificationLieSubalgebra (U i)) (k + 1) _).mpr (hnext i)
  · have hi : ∀ g ∈ [E, A], F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hEslow
      · exact hAslow
    have h := hslow F b ω hlayers w hw H p hH hp hι hσ hHp hb T hT [E, A] (by simp) hi
    simp only [List.prod_cons, List.prod_nil, mul_one] at h
    exact F.symbolSlowBound_mono b ω hlayers w T hT (Real.exp_le_exp.mpr hs) _ h
  · have hi : ∀ g ∈ [D, R], F.SymbolRationalGrid b ω hlayers w l g := by
      intro g hg
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · exact hDgrid
      · exact hRgrid
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hproducts [D, R] (by simp) hi

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

theorem exists_common_symbol_grade_corrections (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {σ ι κ η L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [Fintype η]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (U : η → LieSubalgebra ℚ (F.PolynomialSymbol w)) (v : η → κ → F.PolynomialSymbol w),
      (∀ j, Submodule.span ℚ (Set.range (v j)) = (U j).toSubmodule) →
      (∀ j, BasisBlockInvariant (F.polynomialSymbolBasis b ω hlayers w)
        (fun z => z.val.1) (U j).toSubmodule) →
      ∀ (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card κ : ℝ) ≤ p → (Fintype.card η : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ j i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr (v j i) z) H) →
      ∀ T : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ (k : ℕ) (x : F.RealPolynomialSymbol w) (E R : η → F.RealPolynomialSymbolGroup w),
        let π := basisGradeProjection ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
          (fun z => ω z.val.2) k
        (∀ j, F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + 2) ^ a)) (E j)) →
        (∀ j, F.SymbolRationalGrid b ω hlayers w l (R j)) →
        (∀ j, π x - π (E j).coord - π (R j).coord ∈ realificationLieSubalgebra (U j)) →
        ∃ A D : F.RealPolynomialSymbolGroup w,
          A.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
          D.coord ∈ (F.polynomialSymbolFiltration w).realification.layer k ∧
          F.SymbolSlowBound b ω hlayers w T (Real.exp ((p + C) ^ C)) A ∧
          F.SymbolRationalGrid b ω hlayers w m D ∧
          ∀ j, π x - π A.coord - π D.coord ∈ realificationLieSubalgebra (U j) := by
  obtain ⟨C, hC, hbound⟩ := exists_common_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro σ ι κ η L _ _ _ _ _ _ F b ω hlayers w hw U v hspan hblock H l p hH hl hp
    hι hσ hκ hη hHp hlp hv T hT
  let : Fintype (SymbolBasisIndex w ω) :=
    symbolBasisIndexFintype w ω s hw (F.adaptedBasis_weight_le_step b ω hlayers)
  let N : ℝ := (p + (s + 2)) ^ (s + 2)
  let q : ℝ := N * (p + 1) + (p + 2) ^ a + p + 2
  let t : ℝ := ((q + 2) ^ 10 + 2) ^ 4
  have hN : 0 ≤ N := by dsimp [N]; positivity
  have ha : 0 ≤ (p + 2) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hNp : 0 ≤ N * (p + 1) := mul_nonneg hN (by positivity)
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hNterm : N ≤ N * (p + 1) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (show 1 ≤ p + 1 by linarith) hN
  have hNq : N ≤ q := hNterm.trans (by dsimp [q]; linarith)
  have hNpq : N * p ≤ q :=
    (mul_le_mul_of_nonneg_left (show p ≤ p + 1 by linarith) hN).trans (by dsimp [q]; linarith)
  have haq : (p + 2) ^ a ≤ q := by dsimp [q]; linarith
  have hdim : (Fintype.card (SymbolBasisIndex w ω) : ℝ) ≤ N :=
    (Nat.cast_le.mpr (symbolBasisIndex_card_le w ω s hw
      (F.adaptedBasis_weight_le_step b ω hlayers))).trans
      (symbol_dimension_bound_le_power s (Fintype.card ι) (Fintype.card σ) hp hι hσ)
  have hcols : ((Fintype.card (SymbolBasisIndex w ω) * Fintype.card κ : ℕ) : ℝ) ≤ q := by
    rw [Nat.cast_mul]
    exact (mul_le_mul hdim hκ (Nat.cast_nonneg _) hN).trans hNpq
  have hrows : (Fintype.card (Σ _ : η, SymbolBasisIndex w ω) : ℝ) ≤ q := by
    simp only [Fintype.card_sigma, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
    exact (mul_le_mul hη hdim (Nat.cast_nonneg _) hp).trans (by simpa only [mul_comm] using hNpq)
  have hall : separationBudget t + (t + 2) ^ 36 + ((t + 2) ^ 18 + t) ≤ (p + C) ^ C := by
    exact hbound p hp
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hs : 0 ≤ separationBudget t := separationBudget_nonneg ht
  have hden0 : 0 ≤ (t + 2) ^ 36 := by positivity
  have hslow0 : 0 ≤ (t + 2) ^ 18 + t := by positivity
  have hcut : separationBudget t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right hden0).trans ((le_add_of_nonneg_right hslow0).trans hall)
  have hden : (t + 2) ^ 36 ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left hs).trans ((le_add_of_nonneg_right hslow0).trans hall)
  have hslow : (t + 2) ^ 18 + t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (add_nonneg hs hden0)).trans hall
  let e := F.polynomialSymbolBasis b ω hlayers w
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_block_subspace_corrections e (fun z => z.val.1)
    (fun j => (U j).toSubmodule) v hspan hblock hH hl hv hq (hdim.trans hNq) hcols hrows
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hden), hlm, ?_⟩
  intro k x E R
  dsimp only
  intro hE hR hres
  let π := basisGradeProjection (e.baseChange ℝ) (fun z => ω z.val.2) k
  have hπ (z : F.RealPolynomialSymbol w) : π (π z) = π z :=
    basisCoordinateProjection_idempotent (e.baseChange ℝ) {z | ω z.val.2 = k} z
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hW : ∀ α, 0 < monomialScale T α := monomialScale_pos T hTpos
  have hWmin : ∀ z : SymbolBasisIndex w ω, Real.exp (separationBudget t) ≤ monomialScale T z.val.1 :=
    fun z => le_monomialScale_of_ne_zero T (Real.one_le_exp hs)
      (fun i => (Real.exp_le_exp.mpr hcut).trans (hT i))
      (F.symbolBasisIndex_monomial_ne_zero b ω hlayers w z)
  have he : ∀ j z, |(e.baseChange ℝ).equivFun (π (E j).coord) z| ≤ Real.exp q / monomialScale T z.val.1 := by
    intro j z
    exact ((basisCoordinateProjection_abs_repr_le (e.baseChange ℝ) {z | ω z.val.2 = k} (E j).coord z).trans
      (hE j z)).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr haq) (hW _).le)
  have hr : ∀ j, (e.baseChange ℝ).equivFun (π (R j).coord) ∈ realDenominatorGrid l :=
    fun j => basisCoordinateProjection_real_grid (e.baseChange ℝ) {z | ω z.val.2 = k} l (R j).coord (hR j)
  obtain ⟨u, d, hu, hd, hcommon⟩ := hsolve (monomialScale T) hW hWmin
    (fun j => π (E j).coord) (fun j => π (R j).coord) (π x) he hr hres
  refine ⟨⟨π u⟩, ⟨π d⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer e (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hlayers w) k u
  · exact (F.polynomialSymbolFiltration w).realGradeProjection_mem_layer e (fun z => ω z.val.2)
      (F.polynomialSymbolFiltration_layer b ω hlayers w) k d
  · intro z
    exact ((basisCoordinateProjection_abs_repr_le (e.baseChange ℝ) {z | ω z.val.2 = k} u z).trans
      (hu z)).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hslow) (hW _).le)
  · exact basisCoordinateProjection_real_grid (e.baseChange ℝ) {z | ω z.val.2 = k} m d hd
  · intro j
    have hgraded : BasisGradedSubmodule e (fun z => ω z.val.2) (U j).toSubmodule := by
      have heq : (fun z : SymbolBasisIndex w ω => ω z.val.2) = (fun z => Finsupp.weight w z.val.1) :=
        funext (fun z => z.property.symm)
      rw [heq]
      exact (hblock j).graded e (fun z => z.val.1) (U j).toSubmodule (Finsupp.weight w)
    have h := hgraded.baseChange e (fun z => ω z.val.2) (U j).toSubmodule k
      (π x - u - d) (hcommon j)
    change π (π x - u - d) ∈ (U j).toSubmodule.baseChange ℝ at h
    change π x - π (π u) - π (π d) ∈ (U j).toSubmodule.baseChange ℝ
    simpa only [map_sub, hπ] using h

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SimultaneousSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem symbolSlowBound_one (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) :
    F.SymbolSlowBound b ω hlayers w T M 1 := by
  intro z
  change |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z| ≤ _
  simp only [map_zero, Finsupp.zero_apply, abs_zero]
  exact div_nonneg hM (monomialScale_pos T hT z.val.1).le

theorem symbolRationalGrid_one (l : ℕ) : F.SymbolRationalGrid b ω hlayers w l 1 := by
  change (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z) ∈ realDenominatorGrid l
  have hzero : (fun z => ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr 0 z) =
      (0 : SymbolBasisIndex w ω → ℝ) := by
    funext z
    simp only [map_zero, Finsupp.zero_apply, Pi.zero_apply]
  rw [hzero]
  exact realDenominatorGrid_zero l

theorem realSymbolGradeQuotientHom_first (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w 1 g = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (lieQuotientMap_eq_zero ((F.polynomialSymbolFiltration w).realification.layerIdeal 1) _).mpr
  change g.coord ∈ (F.polynomialSymbolFiltration w).realification.layer 1
  rw [(F.polynomialSymbolFiltration w).realification.one_eq_top]
  exact Submodule.mem_top

theorem realSymbolGradeQuotient_mem_terminal_iff
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (g : F.RealPolynomialSymbolGroup w) :
    F.realSymbolGradeQuotientHom w (s + 1) g ∈
      (NilpotentLieBCHGroup.realificationSubgroup
        (hnil := F.polynomialSymbol_lowerCentralSeries_eq_bot w) U).map
        (F.realSymbolGradeQuotientHom w (s + 1)) ↔ g.coord ∈ realificationLieSubalgebra U := by
  rw [F.realSymbolGradeQuotient_mem_iff w U (s + 1) g,
    (F.polynomialSymbolFiltration w).realification.terminal, sup_bot_eq]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SimultaneousPolynomialSymbolSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem exists_realPolynomial_symbol_factorization
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (h : E * P * R = F.realPolynomialSymbolHom b ω hlayers w g) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w E.coord ∧
      (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) = F.realSymbolRepresentative b ω hlayers w R.coord ∧
      F.realPolynomialSymbolHom b ω hlayers w p = P := by
  let e := F.realPolynomialSymbolLift b ω hlayers w E
  let r := F.realPolynomialSymbolLift b ω hlayers w R
  refine ⟨e, e⁻¹ * g * r⁻¹, r, ?_, rfl, rfl, ?_⟩
  · simp [mul_assoc]
  · rw [map_mul, map_mul, map_inv, map_inv, ← h]
    simp [e, r, mul_assoc]

theorem exists_realPolynomial_controlled_symbol_factorization
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M) (l : ℕ)
    (g : (F.realification.adaptedPolynomialFiltration w).Group)
    (E P R : F.RealPolynomialSymbolGroup w)
    (h : E * P * R = F.realPolynomialSymbolHom b ω hlayers w g)
    (hE : F.SymbolSlowBound b ω hlayers w T M E)
    (hR : F.SymbolRationalGrid b ω hlayers w l R) :
    ∃ e p r : (F.realification.adaptedPolynomialFiltration w).Group,
      e * p * r = g ∧
      F.realPolynomialSymbolHom b ω hlayers w p = P ∧
      (∀ α i, |(b.baseChange ℝ).repr
        (coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
          M / monomialScale T α) ∧
      ((fun z : (σ →₀ ℕ) × ι => (b.baseChange ℝ).repr
        (coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈
          realDenominatorGrid l) ∧
      coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
      coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
      coefficients (p.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 =
        coefficients (g.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 := by
  obtain ⟨e, p, r, hepr, he, hr, hp⟩ :=
    F.exists_realPolynomial_symbol_factorization b ω hlayers w g E P R h
  have he0 : coefficients (e.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
    rw [he]
    exact F.realSymbolRepresentative_constant b ω hlayers w E.coord
  have hr0 : coefficients (r.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 := by
    rw [hr]
    exact F.realSymbolRepresentative_constant b ω hlayers w R.coord
  refine ⟨e, p, r, hepr, hp, ?_, ?_, he0, hr0,
    F.realification.polynomial_factor_middle_constant w g e p r hepr he0 hr0⟩
  · rw [he]
    exact F.realSymbolRepresentative_slow_coefficients b ω hlayers w T hT hM E hE
  · rw [hr]
    exact F.realSymbolRepresentative_rational_coefficients b ω hlayers w l R hR

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RefilteredPointwiseSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem mem_realGradedRefiltrationSubalgebra (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realGradedRefiltrationSubalgebra U ↔ v ∈ F.realGradedRefiltrationLayer U 1 := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (U : LieSubalgebra ℚ F.AssociatedGraded)

theorem normalized_refiltration_coefficients_mem_first
    (hw : ∀ i, 0 < w i) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U 1 := by
  intro α
  by_cases hα : α = 0
  · rw [hα, hzero]
    exact (F.realGradedRefiltrationLayer U 1).zero_mem
  · exact F.realGradedRefiltrationLayer_antitone U (positive_weight_of_ne_zero w hw hα) (hp α)

theorem exists_refiltered_polynomial_of_coefficients (hw : ∀ i, 0 < w i)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (hp : ∀ α, coefficients p α ∈ F.realGradedRefiltrationLayer U (Finsupp.weight w α))
    (hzero : coefficients p 0 = 0) :
    ∃ q : VectorPolynomial σ ℚ (F.realGradedRefiltrationSubalgebra U),
      (F.realGradedRefiltration U).Adapted w q ∧
      VectorPolynomial.map (F.realGradedRefiltrationSubalgebra U).incl.toLinearMap q = p ∧
      coefficients q 0 = 0 := by
  have hfirst := F.normalized_refiltration_coefficients_mem_first w U hw p hp hzero
  have hcoeff : ∀ α, coefficients p α ∈ (F.realGradedRefiltrationSubalgebra U).toSubmodule := by
    intro α
    exact (F.mem_realGradedRefiltrationSubalgebra U _).mpr (hfirst α)
  let q := restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff
  have hq (α : σ →₀ ℕ) : (coefficients q α : ℝ ⊗[ℚ] L) = coefficients p α :=
    coefficients_restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff α
  refine ⟨q, ?_, map_restrictCoefficients (F.realGradedRefiltrationSubalgebra U).toSubmodule p hcoeff, ?_⟩
  · apply ((F.realGradedRefiltration U).adapted_iff_coefficients w q).mpr
    intro α
    rw [F.mem_realGradedRefiltration_layer, hq]
    exact hp α
  · apply Subtype.ext
    exact (hq 0).trans hzero

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalCentralCircle
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem centralRationalCircle_act_coe (v : L) (hv : v ∈ D.filtration.layer s)
    (r : ℝ) (x : D.Space) :
    let := D.metricSpace
    (D.centralRationalCircle v hv).act (r : CircleFourier.Circle) x =
      realBCHLine (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
        (D.periodicRealDirection v) r • x := by
  let := D.metricSpace
  exact centralBCHCircleAction_act_coe (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_mem_lattice v) r x

theorem centralRationalCircle_commutes (v w : L)
    (hv : v ∈ D.filtration.layer s) (hw : w ∈ D.filtration.layer s) :
    let := D.metricSpace
    (D.centralRationalCircle v hv).Commutes (D.centralRationalCircle w hw) := by
  let := D.metricSpace
  exact centralBCHCircleAction_commutes (D.basis.baseChange ℝ) D.realLattice
    D.realLattice_closed_discrete.1 (D.periodicRealDirection v) (D.periodicRealDirection w)
    (D.periodicRealDirection_central v hv) (D.periodicRealDirection_central w hw)
    (D.periodicRealDirection_mem_lattice v) (D.periodicRealDirection_mem_lattice w)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalKernelInvariance
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup CircleFourier
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem invariant_of_kernel_circles (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    (b : Basis ι ℚ K) (f : D.Space → ℂ)
    (hf : let := D.metricSpace; ∀ i t x,
      f ((D.centralRationalCircle (b i) (hK (b i).property)).act t x) = f x)
    (z : D.RealGroup) (hz : z.coord ∈ K.baseChange ℝ) (x : D.Space) :
    f (z • x) = f x := by
  let := D.metricSpace
  have hspan : Submodule.span ℝ (Set.range (fun i => D.periodicRealDirection (b i))) =
      K.baseChange ℝ :=
    (D.periodicRealDirection_span (fun i => (b i : L))).trans
      (real_span_rational_family K (fun i => (b i : L)) (span_submodule_basis K b))
  have h := central_span_character (fun i => D.periodicRealDirection (b i))
    (fun i => D.periodicRealDirection_central (b i) (hK (b i).property))
    (0 : (ℝ ⊗[ℚ] L) →ₗ[ℝ] ℝ) f (fun i r y => by
      have hi := hf i (r : CircleFourier.Circle) y
      rw [D.centralRationalCircle_act_coe] at hi
      simpa only [LinearMap.zero_apply, mul_zero, AddCircle.coe_zero, character_zero, one_mul] using hi)
    (hspan.symm ▸ hz) x
  simpa only [LinearMap.zero_apply, AddCircle.coe_zero, character_zero, one_mul] using h

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TwistedBufferedTranslationPhase
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (M : ℕ)

theorem twistedBufferedTranslationTerm_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) (β : Fin m → ℤ) :
    twistedBufferedTranslationTerm M Ψ D₀ T (g * ⟨0, C a⟩) β =
      twistedBufferedTranslationTerm M Ψ D₀ T g β * (Real.fourierChar a : ℂ) := by
  unfold twistedBufferedTranslationTerm bufferedTranslationTerm
  have hb : (g * (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m))).base = g.base := by simp
  rw [hb]
  have ha := translationPhaseArgument_mul D₀ g
    (⟨0, C a⟩ : PolynomialTranslationGroupOver ℝ (Fin m)) (fun i => (β i : ℝ))
  simp only [add_zero, eval_C] at ha
  rw [ha, Real.fourierChar.map_add_eq_mul]
  simp only [Circle.coe_mul, mul_assoc]

theorem twistedBufferedTranslationPhase_central (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (a : ℝ) :
    twistedBufferedTranslationPhase M Ψ D₀ T (g * ⟨0, C a⟩) =
      twistedBufferedTranslationPhase M Ψ D₀ T g * (Real.fourierChar a : ℂ) := by
  unfold twistedBufferedTranslationPhase
  simp_rw [twistedBufferedTranslationTerm_central]
  exact tsum_mul_right

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RealSymbolAffine
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (w : σ → ℕ)

theorem realSymbolOfPolynomial_affine (hw : ∀ i, 0 < w i) (h : σ → ℚ) (r : ℚ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hp : F.realification.Adapted w p) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r (translate h p)) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  rw [F.realSymbolOfPolynomial_dilation, F.realSymbolOfPolynomial_translate b ω hF w hw h p hp]

theorem realGradedSymbolPolynomial_dilation_coefficient (r : ℚ)
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hF w (F.realPolynomialSymbolDilation w r x)) α =
      (r : ℝ) ^ Finsupp.weight w α • coefficients (F.realGradedSymbolPolynomial b ω hF w x) α := by
  apply ((F.associatedGradedBasis b ω hF).baseChange ℝ).repr.injective
  ext i
  rw [map_smul, Finsupp.smul_apply]
  by_cases h : Finsupp.weight w α = ω i
  · rw [F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), h⟩,
      F.realGradedSymbolPolynomial_coordinate b ω hF w _ ⟨(α, i), h⟩,
      F.realPolynomialSymbolDilation_repr]
    rfl
  · rw [F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i h,
      F.realGradedSymbolPolynomial_coordinate_of_ne b ω hF w _ α i h, smul_zero]

theorem realSymbolDilation_mem_pointwise (U : LieSubalgebra ℚ F.AssociatedGraded)
    (r : ℚ) (x : F.RealPolynomialSymbol w)
    (hx : x ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U)) :
    F.realPolynomialSymbolDilation w r x ∈
      realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF w U) := by
  apply (F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w U _).mpr
  intro α
  rw [F.realGradedSymbolPolynomial_dilation_coefficient]
  exact (realificationLieSubalgebra U).smul_mem _
    ((F.mem_real_symbolPointwiseSubalgebra_iff_coefficients b ω hF w U x).mp hx α)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s dim}

theorem exists_nested_box_restriction (T : D.Niltest (fun _ : I => 1))
    (c b : I → ℤ) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (H K : I → ℕ) (hK : ∀ i, 0 < K i)
    (hsub : commonStrideBox b d K ⊆ commonStrideBox c m H) :
    ∃ U : D.Niltest (fun _ : I => 1),
      (∀ p, U.ComplexityLE p ↔ T.ComplexityLE p) ∧
      ∀ x ∈ integerBox K, U.eval x = T.eval (commonStrideIndex c m (commonStridePoint b d x)) := by
  obtain ⟨A, a, hA⟩ := exists_nested_box_affine c b hm hd H K hK hsub
  refine ⟨T.affinePullback A a, fun p => affinePullback_complexityLE T A a p, ?_⟩
  intro x hx
  rw [eval_affinePullback, (hA x hx).2, commonStrideIndex_point c hm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.QuantitativeOuterPolynomialProducts
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

section Modules

variable {σ ι κ L M : Type*} [AddCommGroup L] [Module ℚ L]
  [AddCommGroup M] [Module ℚ M]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficient_norm
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    {H K : ℕ} (hφ : ∀ i j, RationalHeightLE (LinearMap.toMatrix b c φ i j) H)
    (hS : ∀ i j, RationalHeightLE (LinearMap.toMatrix c b S i j) K)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) (T : σ → ℝ) (A B : ℝ)
    (α : σ →₀ ℕ)
    (hp : ‖(b.baseChange ℝ).equivFun (coefficients p α)‖ ≤ A / monomialScale T α)
    (hq : ‖(c.baseChange ℝ).equivFun (coefficients q α)‖ ≤ B / monomialScale T α) :
    ‖(b.baseChange ℝ).equivFun (coefficients (sectionCorrectedPolynomial φ S p q) α)‖ ≤
      (A + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        ((((Fintype.card ι : ℝ) + 1) * (H + 1)) * A + B)) / monomialScale T α := by
  rw [sectionCorrectedPolynomial_coefficients]
  apply (realified_section_correction_coordinate_norm b c φ S hφ hS
    (coefficients p α) (coefficients q α)).trans
  calc
    _ ≤ A / monomialScale T α + (((Fintype.card κ : ℝ) + 1) * (K + 1)) *
        (((Fintype.card ι : ℝ) + 1) * (H + 1) * (A / monomialScale T α) +
          B / monomialScale T α) := by
      exact add_le_add hp (mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) hq) (by positivity))
    _ = _ := by ring

theorem sectionCorrectedPolynomial_coefficient_grid
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) {l : ℕ} (hl : 0 < l) (α : σ →₀ ℕ)
    (hp : (b.baseChange ℝ).equivFun (coefficients p α) ∈ realDenominatorGrid l)
    (hq : (c.baseChange ℝ).equivFun (coefficients q α) ∈ realDenominatorGrid l) :
    (b.baseChange ℝ).equivFun (coefficients (sectionCorrectedPolynomial φ S p q) α) ∈
      realDenominatorGrid (matrixDenominator (LinearMap.toMatrix c b S) *
        matrixDenominator (LinearMap.toMatrix b c φ) * l) := by
  let D := matrixDenominator (LinearMap.toMatrix b c φ)
  let E := matrixDenominator (LinearMap.toMatrix c b S)
  have hinner : (c.baseChange ℝ).equivFun
      (φ.baseChange ℝ (coefficients p α) - coefficients q α) ∈
      realDenominatorGrid (D * l) := by
    rw [map_sub]
    exact realDenominatorGrid_sub (D * l) _ _
      (realified_linear_coordinate_grid b c φ l _ hp)
      (realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l D) hq)
  have hcorr : (b.baseChange ℝ).equivFun
      (S.baseChange ℝ (φ.baseChange ℝ (coefficients p α) - coefficients q α)) ∈
      realDenominatorGrid (E * D * l) := by
    simpa only [mul_assoc] using realified_linear_coordinate_grid c b S (D * l) _ hinner
  rw [sectionCorrectedPolynomial_coefficients, map_sub]
  exact realDenominatorGrid_sub (E * D * l) _ _
    (realDenominatorGrid_subset_of_dvd hl (dvd_mul_left l (E * D)) hp) hcorr

end Modules

section LieModules

variable {σ ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem sectionCorrectedPolynomial_coefficientGrid
    (b : Basis ι ℚ L) (c : Basis κ ℚ M) (φ : L →ₗ[ℚ] M) (S : M →ₗ[ℚ] L)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L))
    (q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] M)) {l : ℕ} (hl : 0 < l)
    (hp : CoefficientGrid (b.baseChange ℝ) l p)
    (hq : CoefficientGrid (c.baseChange ℝ) l q) :
    CoefficientGrid (b.baseChange ℝ)
      (matrixDenominator (LinearMap.toMatrix c b S) *
        matrixDenominator (LinearMap.toMatrix b c φ) * l)
      (sectionCorrectedPolynomial φ S p q) := by
  intro α
  exact sectionCorrectedPolynomial_coefficient_grid b c φ S p q hl α (hp α) (hq α)

end LieModules

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RelativePatchAmplification
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

def RelativePatchInductionRule (s n₀ stage : ℕ) (τ : ℝ)
    (cutoff cost : ℝ → ℝ) : Prop :=
  ∀ (p a Λ : ℝ) (d₀ : ℕ), 2 ≤ p → Real.exp (-p) ≤ a → a ≤ Λ → Λ ≤ 1 →
    RelativePatchAbsoluteRule s n₀ p a Λ d₀ →
    ∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X],
      (Fintype.card X : ℝ) ≤ p →
      ∀ (N : X → ℕ), (∀ i, Real.exp (cutoff p) ≤ (N i : ℝ)) →
      ∀ (f : (X → ℤ) → ℝ),
        (∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) →
        IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} (s + 2) →
        ∀ (d : ℕ) (A : PolynomialPatch X s d),
          relativePatchComplexity A ≤ p → relativePatchDistinctWeights A ≤ stage →
          Real.exp (-p) ≤ relativePatchBoxScore N f a A →
          RelativePatchSliceConclusion s N f ((1 - τ) ^ (stage + 1) * Λ)
            (d₀ + s * d) (cost p)

def RelativePatchPowerInductionRule (s n₀ stage : ℕ) (τ : ℝ) (E : ℕ) : Prop :=
  RelativePatchInductionRule s n₀ stage τ (fun p => (p + 2) ^ E) (fun p => (p + 2) ^ E)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CenteredFiniteSliceResidualEnvelope
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem productive_mass_mul_le_sampledSliceSeminorm
    {Ω T X : Type*} [Fintype Ω] [Fintype T] [Nonempty T]
    {J : Ω → Type*} (p : FiniteProbabilityWeights Ω) (good : Finset Ω)
    (physical : Ω → T → X) (slices : ∀ z, J z → Finset T)
    (weight : ∀ z, J z → T → ℂ)
    (hslices : ∀ z j, (slices z j).Nonempty)
    (hweight : ∀ z j t, ‖weight z j t‖ ≤ 1)
    (signal : X → ℂ) (δ : ℝ)
    (hcorr : ∀ z ∈ good, ∃ j : J z,
      δ ≤ ‖𝔼 t ∈ slices z j, signal (physical z t) * weight z j t‖) :
    δ * p.mass good ≤ sampledSliceSeminorm p physical slices weight signal := by
  let W := fun z j => normalizedSliceTest (slices z j) (weight z j)
  have hsize (z) (j) : (Fintype.card T : ℝ) / (slices z j).card ≤ Fintype.card T := by
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hslices z j).card_pos)).mpr
    have hcard : (1 : ℝ) ≤ (slices z j).card := by exact_mod_cast (hslices z j).card_pos
    nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card T)]
  have hW (z) (j) (t) : ‖W z j t‖ ≤ Fintype.card T :=
    normalizedSliceTest_norm_le _ _ (hsize z j) (hweight z j) t
  have hpoint (z) : (if z ∈ good then δ else 0) ≤
      (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal := by
    by_cases hz : z ∈ good
    · rw [if_pos hz]
      obtain ⟨j, hj⟩ := hcorr z hz
      rw [Seminorm.iSup_apply (sampledSingleTestSeminorm_bddAbove physical W hW z)]
      apply hj.trans
      have he : sampledSingleTestSeminorm (physical z) (W z j) signal =
          ‖𝔼 t ∈ slices z j, signal (physical z t) * weight z j t‖ := by
        change ‖𝔼 t, signal (physical z t) * W z j t‖ = _
        rw [normalizedSliceTest_mean _ (hslices z j)]
      rw [← he]
      exact le_ciSup (Seminorm.bddAbove_range_iff.mp
        (sampledSingleTestSeminorm_bddAbove physical W hW z) signal) j
    · rw [if_neg hz]
      exact apply_nonneg _ _
  calc
    δ * p.mass good = p.mean (fun z => if z ∈ good then δ else 0) := by
      rw [← p.mean_indicator good, ← p.mean_const_mul]
      apply congrArg p.mean
      funext z
      split_ifs <;> simp
    _ ≤ p.mean (fun z => (⨆ j, sampledSingleTestSeminorm (physical z) (W z j)) signal) :=
      p.mean_mono hpoint
    _ = sampledSliceSeminorm p physical slices weight signal := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationDegreeSymbol
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

theorem ofCoordinates_mem_gradedPolynomialSubmodule
    {σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
    [IsScalarTower ℚ ℝ L] (b : Basis ι ℝ L) (ω : ι → ℕ) (v : σ → ℕ)
    (P : ι → MvPolynomial σ ℝ)
    (hP : ∀ i, (P i).IsWeightedHomogeneous v (ω i)) :
    ofCoordinates (R := ℚ) b P ∈ gradedPolynomialSubmodule b ω v := by
  classical
  intro α
  change basisGradeProjection b ω (Finsupp.weight v α)
    (coefficients (ofCoordinates (R := ℚ) b P) α) = _
  apply b.repr.injective
  ext i
  have hc : b.repr (coefficients (ofCoordinates (R := ℚ) b P) α) i =
      (P i).coeff α := by
    change (b.coord i).toAddMonoidHom (coefficients (ofCoordinates (R := ℚ) b P) α) = _
    rw [← coeff_coordinate, coordinate_ofCoordinates]
  rw [basisGradeProjection_repr, hc]
  by_cases hi : ω i = Finsupp.weight v α
  · rw [if_pos hi]
  · rw [if_neg hi, (hP i).coeff_eq_zero α (Ne.symm hi)]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RefilteredKernelConstantBounds
namespace OAI

section

namespace Erdos3
open Module
open scoped TensorProduct BigOperators

theorem realification_fractional_integer_split {ι V : Type*} [Fintype ι]
    [AddCommGroup V] [Module ℚ V] (b : Basis ι ℚ V) (x : ℝ ⊗[ℚ] V) :
    ∃ (e : ℝ ⊗[ℚ] V) (r : V),
      x = e + (1 : ℝ) ⊗ₜ[ℚ] r ∧
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      ∀ i, ∃ z : ℤ, b.repr r i = z := by
  let B := b.baseChange ℝ
  let r := b.equivFun.symm (fun i => (⌊B.repr x i⌋ : ℚ))
  let e := x - (1 : ℝ) ⊗ₜ[ℚ] r
  have hr (i) : b.repr r i = (⌊B.repr x i⌋ : ℚ) := by
    change b.equivFun (b.equivFun.symm _) i = _
    rw [LinearEquiv.apply_symm_apply]
  have he (i) : B.repr e i = Int.fract (B.repr x i) := by
    change B.repr (x - (1 : ℝ) ⊗ₜ[ℚ] r) i = _
    rw [map_sub, Finsupp.sub_apply, Module.Basis.baseChange_repr_tmul (S := ℝ), hr]
    simp only [Rat.smul_def, Rat.cast_intCast, mul_one]
    rfl
  refine ⟨e, r, by dsimp [e]; abel, ?_, fun i => ⟨⌊B.repr x i⌋, hr i⟩⟩
  intro i
  change 0 ≤ B.repr e i ∧ B.repr e i < 1
  rw [he]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem exists_fractional_integer_kernel_correction
    {ι L M : Type*} [Fintype ι] [AddCommGroup L] [Module ℚ L]
    [AddCommGroup M] [Module ℚ M] (φ : L →ₗ[ℚ] M)
    (H : Submodule ℚ L) (b : Basis ι ℚ (LinearMap.ker φ))
    (x : ℝ ⊗[ℚ] L) (hx : φ.baseChange ℝ x ∈ (H.map φ).baseChange ℝ) :
    ∃ (e : ℝ ⊗[ℚ] LinearMap.ker φ) (r : LinearMap.ker φ),
      (∀ i, 0 ≤ (b.baseChange ℝ).repr e i ∧ (b.baseChange ℝ).repr e i < 1) ∧
      (∀ i, ∃ z : ℤ, b.repr r i = z) ∧
      x - (LinearMap.ker φ).subtype.baseChange ℝ e -
        (1 : ℝ) ⊗ₜ[ℚ] (r : L) ∈ H.baseChange ℝ := by
  rw [realification_map] at hx
  obtain ⟨y, hy, hxy⟩ := hx
  have hk : x - y ∈ (LinearMap.ker φ).baseChange ℝ := by
    rw [realification_ker, LinearMap.mem_ker, map_sub, hxy, sub_self]
  obtain ⟨k, hk⟩ := hk
  obtain ⟨e, r, heq, he, hr⟩ := realification_fractional_integer_split b k
  refine ⟨e, r, he, hr, ?_⟩
  have heq' := congrArg ((LinearMap.ker φ).subtype.baseChange ℝ) heq
  rw [hk, map_add, LinearMap.baseChange_tmul] at heq'
  change x - y = (LinearMap.ker φ).subtype.baseChange ℝ e + (1 : ℝ) ⊗ₜ[ℚ] (r : L) at heq'
  have hfinal : x - (LinearMap.ker φ).subtype.baseChange ℝ e -
      (1 : ℝ) ⊗ₜ[ℚ] (r : L) = y := by
    rw [show x = (x - y) + y by abel, heq']
    abel
  rwa [hfinal]

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

section Linear

variable {ι κ V L : Type*} [Fintype κ] [AddCommGroup V] [Module ℚ V]
  [AddCommGroup L] [Module ℚ L]

theorem scalarExtension_coordinate_sum (b : Basis ι ℚ L) (bk : Basis κ ℚ V)
    (f : V →ₗ[ℚ] L) (x : ℝ ⊗[ℚ] V) (i : ι) :
    (b.baseChange ℝ).repr (f.baseChange ℝ x) i =
      ∑ j, (bk.baseChange ℝ).repr x j * (b.repr (f (bk j)) i : ℝ) := by
  classical
  conv_lhs => rw [← (bk.baseChange ℝ).sum_repr x]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul, scalarExtension_basis_coordinates]

theorem scalarExtension_fractional_coordinates_bound
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (H : ℝ)
    (hentries : ∀ i j, |(b.repr (f (bk j)) i : ℝ)| ≤ H)
    (x : ℝ ⊗[ℚ] V)
    (hx : ∀ j, 0 ≤ (bk.baseChange ℝ).repr x j ∧ (bk.baseChange ℝ).repr x j < 1)
    (i : ι) :
    |(b.baseChange ℝ).repr (f.baseChange ℝ x) i| ≤ (Fintype.card κ : ℝ) * H := by
  rw [scalarExtension_coordinate_sum b bk f x i]
  calc
    _ ≤ ∑ j, |(bk.baseChange ℝ).repr x j * (b.repr (f (bk j)) i : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_nonneg (hx j).1]
      exact (mul_le_mul (hx j).2.le (hentries i j) (abs_nonneg _) (by norm_num)).trans
        (by rw [one_mul])
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem integral_basis_image_realDenominatorGrid
    (b : Basis ι ℚ L) (bk : Basis κ ℚ V) (f : V →ₗ[ℚ] L)
    (q : ℕ) (hentries : ∀ j, (fun i => b.repr (f (bk j)) i) ∈ denominatorGrid q)
    (r : V) (hr : ∀ j, ∃ z : ℤ, bk.repr r j = z) :
    (fun i => (b.baseChange ℝ).repr ((1 : ℝ) ⊗ₜ[ℚ] f r) i) ∈ realDenominatorGrid q := by
  have h := integral_basis_image_denominatorGrid b bk f q hentries r hr
  have hreal := (real_cast_mem_denominatorGrid_iff q (fun i => b.repr (f r) i)).mpr h
  simpa only [Basis.baseChange_repr_tmul (S := ℝ), Rat.smul_def, mul_one] using hreal

end Linear

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GlobalChartNativeFactorization
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ R : Type*} [CommRing R]

theorem weightedTop_aeval_monomial (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) (γ : σ →₀ ℕ) (r : R) :
    weightedHomogeneousComponent v (Finsupp.weight w γ) (aeval β (monomial γ r)) =
      aeval (fun i => weightedHomogeneousComponent v (w i) (β i)) (monomial γ r) := by
  apply weightedHomogeneousComponent_eq_of_sub_lower
  · apply weightedComparison_monomial w v (aeval β)
      (aeval (fun i => weightedHomogeneousComponent v (w i) (β i)))
    · intro i
      simpa only [aeval_X] using hβ i
    · intro i
      simpa only [aeval_X] using weightedTopPart_preserves_degree v v (w i) (hβ i)
    · intro i
      simpa only [aeval_X] using weightedTopPart_remainder_lt v (hβ i)
  · exact isWeightedHomogeneous_aeval_monomial w v _
      (fun i => weightedHomogeneousComponent_isWeightedHomogeneous _ _) γ r

theorem coeff_aeval_monomial_eq_top (w : σ → ℕ) (v : τ → ℕ)
    (β : σ → MvPolynomial τ R)
    (hβ : ∀ i, β i ∈ weightedSupportLE v (w i)) (γ : σ →₀ ℕ) (r : R)
    (α : τ →₀ ℕ) (hweight : Finsupp.weight v α = Finsupp.weight w γ) :
    (aeval β (monomial γ r)).coeff α =
      (aeval (fun i => weightedHomogeneousComponent v (w i) (β i))
        (monomial γ r)).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial τ R => polynomial.coeff α)
    (weightedTop_aeval_monomial w v β hβ γ r)
  simpa only [coeff_weightedHomogeneousComponent, if_pos hweight] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ActualPathCurrentGradeReset
namespace OAI

section

namespace Erdos3

theorem exists_actual_path_reset_budget (a cr cs ct : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let z := (p + cr) ^ cr + (p + 2) ^ a + p + 2
      (p + cr) ^ cr ≤ (p + C) ^ C ∧
        (z + cs) ^ cs ≤ (p + C) ^ C ∧
        (z + ct) ^ ct ≤ (p + C) ^ C := by
  let P : Polynomial ℕ := (Polynomial.X + Polynomial.C cr) ^ cr
  let Z : Polynomial ℕ := P + (Polynomial.X + 2) ^ a + Polynomial.X + 2
  let S : Polynomial ℕ := (Z + Polynomial.C cs) ^ cs
  let T : Polynomial ℕ := (Z + Polynomial.C ct) ^ ct
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + S + T)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hbound := hbudget p hp
  have hP := natPolynomial_eval_nonneg P hp
  have hS := natPolynomial_eval_nonneg S hp
  have hT := natPolynomial_eval_nonneg T hp
  rw [Polynomial.eval₂_add, Polynomial.eval₂_add] at hbound
  have hparts : P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      S.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C ∧
      T.eval₂ (Nat.castRingHom ℝ) p ≤ (p + C) ^ C :=
    ⟨by linarith, by linarith, by linarith⟩
  simpa only [P, Z, S, T, Polynomial.eval₂_add, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom, Nat.cast_ofNat] using hparts

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestComplement
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

universe u

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def complement (T : D.Niltest w) : D.Niltest w where
  orbit := T.orbit
  observable := fun z => 1 - T.observable z
  normBound := 1 + T.normBound
  lipBound := T.lipBound
  norm_le z := by
    exact (norm_sub_le _ _).trans (by simpa using add_le_add_left (T.norm_le z) 1)
  lipschitz := by
    let := D.metricSpace
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have he : (1 - T.observable x) - (1 - T.observable y) =
        -(T.observable x - T.observable y) := by ring
    rw [dist_eq_norm, he, norm_neg]
    simpa only [dist_eq_norm] using T.lipschitz.dist_le_mul x y

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PivotAnnihilatorFrequencyCode
namespace OAI

section

namespace Erdos3

open Module
open scoped Classical

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

theorem exists_common_frequency_kernel [FiniteDimensional ℚ V]
    {Ω : Type*} [Fintype Ω] [Fintype J]
    (law : FiniteProbabilityWeights Ω) (productive : Finset Ω)
    (P : Submodule ℚ V) (eta : J → V →ₗ[ℚ] ℚ) (js : Ω → List J) :
    ∃ (code : Fin (finrank ℚ P) → Option J) (retained : Finset Ω),
      retained ⊆ productive ∧
      law.mass productive / (Fintype.card J + 1) ^ finrank ℚ P ≤ law.mass retained ∧
      ∀ a ∈ retained, (∀ i j, code i = some j → j ∈ js a) ∧
        finiteFrequencyKernel P eta (js a) = frequencyCodeKernel P eta code := by
  choose code hmem hkernel using fun a => exists_frequency_basis_code P eta (js a)
  obtain ⟨c, hc⟩ := law.exists_code_fiber_mass productive code
  refine ⟨c, productive.filter (fun a => code a = c), Finset.filter_subset _ _, ?_, ?_⟩
  · have hcard : (Fintype.card (Fin (finrank ℚ P) → Option J) : ℝ) =
        (Fintype.card J + 1 : ℝ) ^ finrank ℚ P := by simp
    rw [hcard] at hc
    convert hc using 1; try rfl
    congr 1
    ext a
    simp only [Finset.mem_filter]
  · intro a ha
    have he := (Finset.mem_filter.mp ha).2
    rw [← he]
    exact ⟨hmem a, hkernel a⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SourceLatticeCover
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup

theorem exists_native_image_cover (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
      [LieRing M] [LieAlgebra ℚ M] {d e : ℕ}
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (φ : L →ₗ⁅ℚ⁆ M) {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p → E.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (E.basis.repr (φ (D.basis j)) i) ≤ p) →
      ∃ Λ : Subgroup E.filtration.Group,
        Λ ≤ E.lattice ∧ (Λ.subgroupOf E.lattice).Characteristic ∧
        (Λ.subgroupOf E.lattice).Normal ∧ (Λ.subgroupOf E.lattice).FiniteIndex ∧
        (Λ.relIndex E.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (N : ℕ) (hN : 0 < N)
          (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates E.basis Λ)
          (hout : bchSubgroupCoordinates E.basis Λ ⊆ denominatorGrid N),
          (E.withLattice Λ N hN hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
          Λ.map realificationHom ⊓
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ).range ≤
            (D.lattice.map realificationHom).map
              (realificationMap (hnil := D.filtration.lowerCentralSeries_eq_bot)
                (hM := E.filtration.lowerCentralSeries_eq_bot) φ) := by
  obtain ⟨c, _, hbudget⟩ := exists_image_cover_reconstruction_budget (bchIntegralDenominatorBound s) 0
  let P : Polynomial ℕ := Polynomial.X + 1 + (Polynomial.X + 1 + Polynomial.C c) ^ c
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro L M _ _ _ _ d e D E φ p hp hD hE hφ
  let t := p + 1
  have ht : 0 ≤ t := add_nonneg hp zero_le_one
  have hpt : p ≤ t := le_add_of_nonneg_right zero_le_one
  let H := ⌈Real.exp p⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp p
  have hHt : (H : ℝ) ≤ Real.exp t := ceil_exp_le_exp_add_one hp
  have hdt : (Fintype.card (Fin d) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hD.1.trans hpt
  have het : (Fintype.card (Fin e) : ℝ) ≤ t := by simpa only [Fintype.card_fin] using hE.1.trans hpt
  have hlt : (D.grid : ℝ) ≤ Real.exp t := hD.2.1.trans (Real.exp_le_exp.mpr hpt)
  have hmt : (E.grid : ℝ) ≤ Real.exp t := hE.2.1.trans (Real.exp_le_exp.mpr hpt)
  obtain ⟨A, Λ, hA, hAb, hΛ, hchar, hnormal, hfinite, hindex, hin, hout, hcover⟩ :=
    E.filtration.exists_image_lattice_cover D.basis E.basis φ D.lattice E.lattice
      D.grid E.grid H D.grid_pos E.grid_pos hH D.inner_grid E.inner_grid E.outer_grid
      (fun i j => rationalHeightLE_ceil_exp (hφ i j))
      (fun i j k => rationalHeightLE_ceil_exp (hE.2.2.1 i j k))
  let a := imageLatticeLogBudget (bchIntegralDenominatorBound s) t
  have ha : 0 ≤ a := imageLatticeLogBudget_nonneg _ ht
  have hAt : (A : ℝ) ≤ Real.exp a :=
    (Nat.cast_le.mpr hAb).trans (imageLatticeBound_le_exp _ _ _ H D.grid E.grid ht hdt het hHt hlt hmt)
  have hprod : ((E.grid * A : ℕ) : ℝ) ≤ Real.exp (t + a) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hmt hAt (Nat.cast_nonneg _) (Real.exp_pos _).le
  have hN : 0 < (E.grid * A) * E.grid := Nat.mul_pos (Nat.mul_pos E.grid_pos hA) E.grid_pos
  have hNg : (((E.grid * A) * E.grid : ℕ) : ℝ) ≤ Real.exp (2 * t + a) := by
    calc
      _ = ((E.grid * A : ℕ) : ℝ) * (E.grid : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp (t + a) * Real.exp t := mul_le_mul hprod hmt (Nat.cast_nonneg _) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  have hidx : (Λ.relIndex E.lattice : ℝ) ≤ Real.exp (t * (t + a)) := by
    apply (Nat.cast_le.mpr hindex).trans
    rw [Nat.cast_pow]
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hprod _).trans
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right het (add_nonneg ht ha)
  obtain ⟨hq, hi, _⟩ := hbudget t ht
  have hsum : t + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hfinal p hp
  have hcC : (t + c) ^ c ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have htC : t ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (add_nonneg ht (Nat.cast_nonneg _)) _)).trans hsum
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite,
    hidx.trans (Real.exp_le_exp.mpr (hi.trans hcC)), (E.grid * A) * E.grid, hN, hin, hout, ?_, hcover⟩
  exact E.withLattice_geometry Λ _ hN hin hout hE (hpt.trans htC)
    (hNg.trans (Real.exp_le_exp.mpr (hq.trans hcC)))

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PositiveGridFamily
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def PositiveGridEstimate (s : ℕ) (epsilon : ℝ) (C : ℕ) : Prop :=
  ∀ {N j : ℕ} [NeZero N] {p L g : ℝ}, 2 ≤ p → 2 ≤ L → 1 ≤ g → g ≤ Real.exp p →
    Odd N → Real.exp ((p + L + 2) ^ C) ≤ N → 1 ≤ j → j ≤ s + 1 →
    ∀ a : Fin j → ℕ, (∀ i, 1 ≤ a i ∧ (a i : ℝ) ≤ p) →
    ∀ f : PositiveGridVertex a → ZMod N → ℝ,
    (∀ b x, 0 ≤ f b x ∧ f b x ≤ Real.exp p) →
    (∀ b, CyclicNiltestUpperComparison.{0} s N ((p + L + 2) ^ C)
      (Real.exp (-((p + L + 2) ^ C))) (f b) (fun _ => g)) →
    positiveGridMean a f ≤ (g * (1 + epsilon) ^ (s + 1)) ^ positiveGridVolume a + Real.exp (-L)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

noncomputable def preparedFiniteForwardWork (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) (x : ℝ) : ℝ :=
  (preparedFiniteForwardWorkPolynomial A stageCountConstant n).eval₂ (Nat.castRingHom ℝ) x

theorem preparedFiniteForwardWork_nonneg (A : ℕ)
    (stageCountConstant : ℕ → ℕ) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ preparedFiniteForwardWork A stageCountConstant n x :=
  natPolynomial_eval_nonneg _ hx

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ProjectedPotentialGroupIdentity
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def projectedSubalgebra (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ))
    (hA : Function.Injective A) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ)) :
    LieSubalgebra ℚ (PolynomialTranslationLie τ) :=
  (U.comap (baseRange A).incl).map (projectedRestriction A hA)

theorem projected_pure_constant_zero
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0)
    (P : MvPolynomial τ ℚ)
    (hP : (⟨0,P⟩ : PolynomialTranslationLie τ) ∈ projectedSubalgebra A hA U) :
    P.coeff 0 = 0 := by
  obtain ⟨x,hx,hxP⟩ := hP
  have hb : x.val.base = 0 := by
    rw [← apply_projectedBaseCoordinates A hA x]
    have hz : projectedBaseCoordinates A hA x = 0 := congrArg PolynomialTranslationLie.base hxP
    rw [hz, map_zero]
  have hpure : (⟨0,x.val.polynomial⟩ : PolynomialTranslationLie σ) ∈ U := by
    have he : (⟨0,x.val.polynomial⟩ : PolynomialTranslationLie σ) = x.val :=
      PolynomialTranslationLie.ext hb.symm rfl
    rw [he]
    exact hx
  have hz := pure_constant_zero_of_top_frequency w d U hgraded frequency hfrequency hkill
    x.val.polynomial hpure
  have hp : polynomialLinearRestriction A x.val.polynomial = P :=
    congrArg PolynomialTranslationLie.polynomial hxP
  rw [← hp, coeff_zero_polynomialLinearRestriction, hz]

noncomputable def projectedPotentialRelation
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (hA : Function.Injective A)
    (w : σ → ℕ) (d : ℕ) (U : LieSubalgebra ℚ (PolynomialTranslationLie σ))
    (hgraded : ∀ x ∈ U, topProjection w d x ∈ U)
    (frequency : PolynomialTranslationLie σ →ₗ[ℚ] ℚ)
    (hfrequency : frequency constantDirection ≠ 0)
    (hkill : ∀ x ∈ U, x ∈ weightedLayer w d d → frequency x = 0) :
    Erdos3.PolynomialPotentialRelation τ where
  space := relationSpace (projectedSubalgebra A hA U)
  bracket_mem := by
    intro x P z Q hx hz
    exact (mem_relationSpace _ _ _).mpr (raw_lie_mem _ x z P Q
      ((mem_relationSpace _ _ _).mp hx) ((mem_relationSpace _ _ _).mp hz))
  pure_constant_zero := fun P hP => projected_pure_constant_zero A hA w d U hgraded
    frequency hfrequency hkill P ((mem_relationSpace _ _ _).mp hP)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledGradedBaseCoordinates
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {σ J : Type*} [Fintype σ]

theorem exists_controlled_basisGraded_coordinate_basis (w : σ → ℕ)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K)
    (g : J → (σ → ℚ)) (hspan : Submodule.span ℚ (Set.range g) = K)
    {H : ℕ} (hH : 1 ≤ H) (hentries : ∀ j i, RationalHeightLE (g j i) H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (b : Basis (Fin n) ℚ K),
      (∀ j, v j ∈ Set.range w) ∧
      (∀ j i, v j ≠ w i → (b j).val i = 0) ∧
      (∀ j i, RationalHeightLE ((b j).val i) H) ∧
      ∀ j, ∃ a : J, (b j).val =
        basisGradeProjection (Pi.basisFun ℚ σ) w (v j) (g a) := by
  classical
  have hgm : ∀ a, g a ∈ K := by
    intro a
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  let S : Set K := {x | ∃ a : J, ∃ j ∈ Set.range w,
    x.val = basisGradeProjection (Pi.basisFun ℚ σ) w j (g a)}
  have hspanK : Submodule.span ℚ (Set.range (fun a => (⟨g a, hgm a⟩ : K))) = ⊤ :=
    (Submodule.span_range_subtype_eq_top_iff K hgm).mpr hspan
  have hS : ⊤ ≤ Submodule.span ℚ S := by
    rw [← hspanK]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    let y (j : ℕ) : K := ⟨basisGradeProjection (Pi.basisFun ℚ σ) w j (g a),
      hK j (g a) (hgm a)⟩
    have hsum : ∑ j ∈ Finset.univ.image w, y j = (⟨g a, hgm a⟩ : K) := by
      apply Subtype.ext
      simpa only [Submodule.coe_sum] using sum_basisGradeProjection_pi w (g a)
    change (⟨g a, hgm a⟩ : K) ∈ Submodule.span ℚ S
    rw [← hsum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.subset_span
    refine ⟨a, j, ?_, rfl⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hj
    exact ⟨i, hi⟩
  let B := Basis.ofSpan hS
  let := FiniteDimensional.fintypeBasisIndex B
  let b := B.reindex (Fintype.equivFin _)
  have hb : ∀ j, b j ∈ S := by
    intro j
    dsimp only [b]
    rw [Basis.reindex_apply]
    exact Basis.ofSpan_subset hS ⟨_, rfl⟩
  choose a v hv hproj using hb
  refine ⟨_, v, b, hv, ?_, ?_, fun j => ⟨a j, hproj j⟩⟩
  · intro j i hji
    rw [hproj j, basisGradeProjection_pi_apply, if_neg (Ne.symm hji)]
  · intro j i
    rw [hproj j, basisGradeProjection_pi_apply]
    split_ifs
    · exact hentries (a j) i
    · simpa [RationalHeightLE] using hH

namespace PolynomialTranslationLie

theorem exists_controlled_graded_base_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (K : Submodule ℚ (σ → ℚ))
    (hK : BasisGradedSubmodule (Pi.basisFun ℚ σ) w K)
    (g : J → (σ → ℚ)) (hspan : Submodule.span ℚ (Set.range g) = K)
    {H : ℕ} (hH : 1 ≤ H) (hentries : ∀ j i, RationalHeightLE (g j i) H) :
    ∃ (n : ℕ) (v : Fin n → ℕ) (A : (Fin n → ℚ) →ₗ[ℚ] (σ → ℚ)),
      n ≤ Fintype.card σ ∧ (∀ j, 0 < v j) ∧ (∀ j, v j ≤ d) ∧
      Function.Injective A ∧ A.range = K ∧
      (∀ j i, v j ≠ w i → A (Pi.single j 1) i = 0) ∧
      (∀ j i, RationalHeightLE (A (Pi.single j 1) i) H) ∧
      ∀ j, ∃ a : J, A (Pi.single j 1) =
        basisGradeProjection (Pi.basisFun ℚ σ) w (v j) (g a) := by
  obtain ⟨n, v, b, hv, hcoord, hheight, hselected⟩ :=
    exists_controlled_basisGraded_coordinate_basis w K hK g hspan hH hentries
  refine ⟨n, v, submoduleBasisCoordinates K b, ?_, ?_, ?_,
    submoduleBasisCoordinates_injective K b, submoduleBasisCoordinates_range K b,
    ?_, ?_, ?_⟩
  · have hn : Module.finrank ℚ K = n := by
      simpa only [Fintype.card_fin] using Module.finrank_eq_card_basis b
    rw [← hn]
    simpa only [Module.finrank_pi] using Submodule.finrank_le K
  · intro j
    obtain ⟨i, hi⟩ := hv j
    simpa only [← hi] using hw i
  · intro j
    obtain ⟨i, hi⟩ := hv j
    simpa only [← hi] using hwd i
  · intro j i hji
    rw [submoduleBasisCoordinates_single]
    exact hcoord j i hji
  · intro j i
    rw [submoduleBasisCoordinates_single]
    exact hheight j i
  · intro j
    rw [submoduleBasisCoordinates_single]
    exact hselected j

end PolynomialTranslationLie

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.TranslationMajorDetectedPotential
namespace OAI

section

namespace Erdos3

theorem linearRestrictionLogPolynomial_eval (d : ℕ) (P Q : Polynomial ℕ) (p : ℝ) :
    (linearRestrictionLogPolynomial d P Q).eval₂ (Nat.castRingHom ℝ) p =
      (d : ℝ) * p + Q.eval₂ (Nat.castRingHom ℝ) p +
      (d : ℝ) * (p + P.eval₂ (Nat.castRingHom ℝ) p + 1) +
      (p + 1) ^ d * Q.eval₂ (Nat.castRingHom ℝ) p +
      p * p * d * P.eval₂ (Nat.castRingHom ℝ) p := by
  simp only [linearRestrictionLogPolynomial, Polynomial.eval₂_add,
    Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_one, Nat.coe_castRingHom]

theorem linearRestrictionHeight_le_exp_logPolynomial (n m d H K : ℕ)
    (P Q : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hm : (m : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp (P.eval₂ (Nat.castRingHom ℝ) p))
    (hK : (K : ℝ) ≤ Real.exp (Q.eval₂ (Nat.castRingHom ℝ) p)) :
    (linearRestrictionHeight n m d H K : ℝ) ≤
      Real.exp ((linearRestrictionLogPolynomial d P Q).eval₂ (Nat.castRingHom ℝ) p) := by
  rw [linearRestrictionLogPolynomial_eval]
  exact linearRestrictionArithmeticBudget_le_exp n m d H K hp
    (natPolynomial_eval_nonneg P hp) (natPolynomial_eval_nonneg Q hp) hn hm hH hK

theorem projectedPotentialHeight_le_exp_logPolynomial (N n d H : ℕ) {p : ℝ}
    (hp : 0 ≤ p) (hn : n ≤ N) (hN : (N : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (projectedPotentialHeight N n d H : ℝ) ≤
      Real.exp ((projectedPotentialLogPolynomial d).eval₂ (Nat.castRingHom ℝ) p) := by
  let U := linearRestrictionLogPolynomial d Polynomial.X Polynomial.X
  let V := Polynomial.X + Polynomial.X * (Polynomial.C d + U)
  have hnp : (n : ℝ) ≤ p := (Nat.cast_le.mpr hn).trans hN
  have hfirst : (linearRestrictionHeight N n d H H : ℝ) ≤
      Real.exp (U.eval₂ (Nat.castRingHom ℝ) p) := by
    exact linearRestrictionHeight_le_exp_logPolynomial N n d H H
      Polynomial.X Polynomial.X hp hN hnp (by simpa using hH) (by simpa using hH)
  have hsecond : (((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n : ℕ) : ℝ) ≤
      Real.exp (V.eval₂ (Nat.castRingHom ℝ) p) := by
    simpa only [V, Polynomial.eval₂_add, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Nat.coe_castRingHom] using
      potential_integration_height_le_exp n d (linearRestrictionHeight N n d H H)
        (natPolynomial_eval_nonneg U hp) hnp hfirst
  have hkernel : (rationalKernelHeight N H : ℝ) ≤
      Real.exp (((Polynomial.X + 2) ^ 7 : Polynomial ℕ).eval₂ (Nat.castRingHom ℝ) p) := by
    simpa only [Polynomial.eval₂_pow, Polynomial.eval₂_add, Polynomial.eval₂_X,
      Polynomial.eval₂_ofNat] using rationalKernelHeight_le_budget N H hp hN hH
  exact linearRestrictionHeight_le_exp_logPolynomial n N d (rationalKernelHeight N H)
    ((n + 1) * (d * linearRestrictionHeight N n d H H) ^ n)
    ((Polynomial.X + 2) ^ 7) V hp hnp hN hkernel hsecond

theorem exists_projectedPotential_height_budget (d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (N n H : ℕ) (p : ℝ),
      0 ≤ p → n ≤ N → (N : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (projectedPotentialHeight N n d H : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
      ((projectedPotentialHeight N n d H * (N + 1) ^ d : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) ∧
      ((projectedPotentialHeight N n d H ^ ((N + 1) ^ d) : ℕ) : ℝ) ≤
        Real.exp ((p + C) ^ C) := by
  let W := projectedPotentialLogPolynomial d
  let T := W + (W + Polynomial.C d * Polynomial.X) + (Polynomial.X + 1) ^ d * W
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget T
  refine ⟨C, hC, ?_⟩
  intro N n H p hp hn hN hH
  let w := W.eval₂ (Nat.castRingHom ℝ) p
  have hw : 0 ≤ w := natPolynomial_eval_nonneg W hp
  have hd : 0 ≤ (d : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hsw : 0 ≤ (p + 1) ^ d * w := by positivity
  have htotal : w + (w + (d : ℝ) * p) + (p + 1) ^ d * w ≤ (p + C) ^ C := by
    simpa only [T, Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_one,
      Nat.coe_castRingHom] using hbound p hp
  have hheight := projectedPotentialHeight_le_exp_logPolynomial N n d H hp hn hN hH
  have hsupport : (((N + 1) ^ d : ℕ) : ℝ) ≤ Real.exp ((d : ℝ) * p) := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity)
      ((add_le_add hN (le_refl 1)).trans (Real.add_one_le_exp p)) d
  have hsupport' : (((N + 1) ^ d : ℕ) : ℝ) ≤ (p + 1) ^ d := by
    rw [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    exact pow_le_pow_left₀ (by positivity) (add_le_add hN (le_refl 1)) d
  refine ⟨hheight.trans (Real.exp_le_exp.mpr (by change w ≤ _; linarith)), ?_, ?_⟩
  · calc
      _ ≤ Real.exp w * Real.exp ((d : ℝ) * p) := by
        rw [Nat.cast_mul]
        exact mul_le_mul hheight hsupport (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (w + (d : ℝ) * p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  · calc
      _ ≤ (Real.exp w) ^ ((N + 1) ^ d) := by
        rw [Nat.cast_pow]
        exact pow_le_pow_left₀ (Nat.cast_nonneg _) hheight _
      _ = Real.exp ((((N + 1) ^ d : ℕ) : ℝ) * w) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp ((p + 1) ^ d * w) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hsupport' hw)
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealTranslationEvaluationContinuity
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped TensorProduct

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_polynomial_eval (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group)
    (a : σ → ℝ) :
    eval a (bchRealTranslationHom w d hwd g).polynomial =
      -eval (Sum.elim a (fun _ : Unit => (0 : ℝ)))
        (polynomialShearExp (-realShearEmbedding w d g.coord) (X (Sum.inr ()))) := by
  have h := PolynomialTranslationGroupOver.action_inverse_X_inr_eval
    (bchRealTranslationHom w d hwd g) a 0
  have hi : (PolynomialTranslationGroupOver.actionMonoidHom
      (bchRealTranslationHom w d hwd g)).symm =
      PolynomialTranslationGroupOver.actionMonoidHom
        (bchRealTranslationHom w d hwd g⁻¹) := by
    rw [map_inv]
    exact (map_inv PolynomialTranslationGroupOver.actionMonoidHom _).symm
  rw [hi, bchRealTranslationHom_action] at h
  change eval (Sum.elim a (fun _ : Unit => (0 : ℝ)))
    (polynomialShearExp (realShearEmbedding w d (-g.coord)) (X (Sum.inr ()))) =
    0 - eval a (bchRealTranslationHom w d hwd g).polynomial at h
  rw [map_neg] at h
  linarith

theorem continuous_bchRealTranslationHom_polynomial_eval
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)] :
    Continuous fun z : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (σ → ℝ) =>
      eval z.2 (bchRealTranslationHom w d hwd ⟨z.1⟩).polynomial := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  have hpos : ∀ i, 0 < shearWeight w d i := by
    intro i
    cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  have hc := continuous_polynomialShearExp_eval (shearWeight w d) hpos
    (-(realShearEmbedding w d).toLinearMap) (X (Sum.inr ()))
  have he : Continuous fun z : (ℝ ⊗[ℚ] weightedSubalgebra w d) × (σ → ℝ) =>
      (z.1, Sum.elim z.2 (fun _ : Unit => (0 : ℝ))) := by
    apply continuous_fst.prodMk
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact (continuous_apply i).comp continuous_snd
    | inr _ => exact continuous_const
  convert (hc.comp he).neg using 1
  ext z
  exact bchRealTranslationHom_polynomial_eval w d hwd ⟨z.1⟩ z.2

theorem continuous_bchRealTranslationHom_base
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hd : 0 < d)
    (hwd : ∀ i, w i ≤ d)
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)] :
    Continuous fun x : ℝ ⊗[ℚ] weightedSubalgebra w d =>
      (bchRealTranslationHom w d hwd ⟨x⟩).base := by
  classical
  let := weightedBasisIndex_finite w d hw
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) :=
    ((weightedBasis w d hw).baseChange ℝ).finiteDimensional_of_finite
  have hpos : ∀ i, 0 < shearWeight w d i := by
    intro i
    cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  apply continuous_pi
  intro i
  have hc := continuous_polynomialShearExp_eval (shearWeight w d) hpos
    (realShearEmbedding w d).toLinearMap (X (Sum.inl i))
  have he := hc.comp (continuous_id.prodMk
    (continuous_const : Continuous fun _ : ℝ ⊗[ℚ] weightedSubalgebra w d =>
      (0 : σ ⊕ Unit → ℝ)))
  convert he using 1
  ext x
  have ha := bchRealTranslationHom_action w d hwd ⟨x⟩
  have hx := congrArg (fun f : MvPolynomial (σ ⊕ Unit) ℝ ≃ₐ[ℝ]
    MvPolynomial (σ ⊕ Unit) ℝ => eval 0 (f (X (Sum.inl i)))) ha
  change eval 0 (PolynomialTranslationGroupOver.actionHom
    (bchRealTranslationHom w d hwd ⟨x⟩) (X (Sum.inl i))) =
    eval 0 (polynomialShearExp (realShearEmbedding w d x) (X (Sum.inl i))) at hx
  simpa only [PolynomialTranslationGroupOver.actionHom_X_inl, map_add, eval_X,
    Pi.zero_apply, eval_C, zero_add, Function.comp_apply, id_eq, LieHom.coe_toLinearMap] using hx

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorRealSubstitutionBound
namespace OAI

section

namespace Erdos3.VectorPolynomial
open Module

variable {σ τ ι V : Type*}

theorem coordinate_realChartSubstitute
    [AddCommGroup V] [Module ℚ V] [Module ℝ V] [IsScalarTower ℚ ℝ V]
    (l : V →ₗ[ℝ] ℝ) (f : σ → MvPolynomial τ ℝ) (P : VectorPolynomial σ ℚ V) :
    coordinate l.toAddMonoidHom (Erdos3.VectorPolynomial.realChartSubstitute f P) =
      MvPolynomial.eval₂Hom MvPolynomial.C f (coordinate l.toAddMonoidHom P) := by
  apply MvPolynomial.funext
  intro x
  rw [← coordinate_eval₂ l x, eval₂_realChartSubstitute, coordinate_eval₂]
  simp only [MvPolynomial.coe_eval₂Hom, ← MvPolynomial.eval_assoc, Function.comp_def]

theorem CoefficientBound.realChartSubstitute [Fintype σ]
    [LieRing V] [LieAlgebra ℚ V] [LieAlgebra ℝ V] [IsScalarTower ℚ ℝ V]
    (b : Basis ι ℝ V) (T : τ → ℝ) (hT : ∀ i, 0 < T i)
    (f : σ → MvPolynomial τ ℝ) {A B : ℝ} {s : ℕ} {P : VectorPolynomial σ ℚ V}
    (hP : CoefficientBound b (fun _ => 1) A P) (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hdegree : DegreeLE (fun _ : σ => 1) s P)
    (hf : ∀ i, realPolynomialMass (scaleMvPolynomialAxes T (f i)) ≤ B) :
    CoefficientBound b T
      (((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * A * B ^ s)
      (Erdos3.VectorPolynomial.realChartSubstitute f P) := by
  intro α i
  let Q := coordinate (b.coord i).toAddMonoidHom P
  have hQdeg : Q.totalDegree ≤ s := (degreeLE_one_iff_basis_totalDegree b s P).mp hdegree i
  have hQcoeff (β) : |Q.coeff β| ≤ A := by
    change |b.repr (coefficients P β) i| ≤ A
    simpa [monomialScale] using hP β i
  have hcard : (Q.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le Q hQdeg
  have hbound := scaled_substitution_coeff_bound T hT f Q hB hf hQcoeff hQdeg α
  have heq := congrArg (fun q : MvPolynomial τ ℝ => q.coeff α)
    (coordinate_realChartSubstitute (b.coord i) f P)
  rw [coeff_coordinate] at heq
  change (b.coord i) (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α) = _ at heq
  change |(b.coord i) (coefficients (Erdos3.VectorPolynomial.realChartSubstitute f P) α)| ≤ _
  rw [heq]
  apply hbound.trans
  apply div_le_div_of_nonneg_right _ (monomialScale_pos T hT α).le
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcard hA)
    (pow_nonneg (zero_le_one.trans hB) s)

end Erdos3.VectorPolynomial

end

end OAI
end


