-- Prove2me | Definitions.Def_OAIE3v2B268
-- name    : OAIE3v2B268
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T06:42:52.516978+00:00
-- url     : https://prove2.me/theorems/4922c5e9-8066-4e0a-a438-63840f28b18c
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 277 of 311
-- statement:
--   Definitions bundle 277 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B304`, `OAIE3v2B264` of this split.
--
--   Modules: `Estimates/AllocatedProductiveFrozenMajorDetection.lean`, `Estimates/MarkedUnitOrbit.lean`, `Estimates/MixedPairComparison.lean`, `Lattices/CommonLocalAffineFamily.lean`, `Nilpotent/AllocatedKeptCommonCurrentGradeLocalNiltest.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B304
import Definitions.Def_OAIE3v2B264

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MarkedUnitOrbit
namespace OAI


namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (t : ℕ) (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
  (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ)
  (u c : Fin t → ℝ) (h₀ : ZMod N)

theorem localAffineMarkedLift_eval (h : ZMod N) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) =
            ∑ j : Fin s, (n : ℚ) ^ (j.val + 1) •
              ((x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
  apply (D.commonAffineMarkedLift_eval t (D.localAffineMarkedBase t x y u c h₀) y u
    (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ)) h.val n).trans
  apply Finset.sum_congr rfl
  intro j _
  apply congrArg (fun z : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra => (n : ℚ) ^ (j.val + 1) • z)
  change ((x j).val + ∑ i, (-(h₀.val : ℝ) * u i - c i) • (y j i).val) + _ = _
  rw [add_assoc, ← Finset.sum_add_distrib]
  apply congrArg ((x j).val + ·)
  apply Finset.sum_congr rfl
  intro i _
  rw [← add_smul]
  apply congrArg (fun a : ℝ => a • (y j i).val)
  simpa only [Int.cast_natCast, add_assoc] using affineCyclicTorusCarry_identity u c h₀ h i

theorem localAffineMarkedLift_eq_polynomial_eval
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (h : ZMod N) (hA : A h = positiveUnivariate (fun j =>
      (x j).val + ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val)) (n : ℤ) :
    (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
      D.coefficientWeight D.coefficientIsDependent t
        (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
          (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  rw [D.localAffineMarkedLift_eval, hA]
  simp only [positiveUnivariate, map_sum, eval_monomial, Finsupp.prod_single_index, pow_zero]

end Erdos3.NativeRankRelation.CommonData


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonLocalAffineFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_common_local_marked_family
    {t : ℕ} {B : ℝ} (hB : 0 ≤ B) (ht : (t : ℝ) ≤ B)
    (η : (Fin t → ℤ) →+ ZMod N) (radius : Fin t → ℕ)
    (hinj : Set.InjOn η {x | ∀ i, |x i| ≤ (radius i : ℤ)})
    (h₀ : ZMod N) (J : Finset (ZMod N)) (hJ : J.Nonempty)
    (hdense : Real.exp (-B) * N ≤ (J.card : ℝ))
    (v : ZMod N → Fin t → ℤ) (hv : ∀ h ∈ J, ∀ i, |v h i| ≤ (radius i : ℤ))
    (hrep : ∀ h ∈ J, h = h₀ + η (v h))
    (A : ZMod N → VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (Γ : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra))
    (hΓdeg : DegreeLE (fun _ : Unit => 1) s Γ) (hΓzero : coefficients Γ 0 = 0)
    (hΓ : ∀ j : Fin s, coefficients Γ (Finsupp.single () (j.val + 1)) ∈
      (D.coefficientFreeSpan j).baseChange ℝ)
    (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (β : Fin t → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hα : ∀ j, α j ∈ (D.dependentFreeSpan j).baseChange ℝ)
    (hβ : ∀ i j, β i j ∈ (D.dependentFreeSpan j).baseChange ℝ)
    (hA : ∀ h ∈ J, A h = Γ + positiveUnivariate (fun j => α j + ∑ i, (v h i : ℝ) • β i j)) :
    ∃ K ⊆ J, K.Nonempty ∧ Real.exp (-((B + 4) ^ 7)) * N ≤ (K.card : ℝ) ∧
      ∃ (u c : Fin t → ℝ)
        (x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ)
        (y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ),
        (∀ i, u i ∈ Set.Ico (0 : ℝ) 1) ∧
        (∀ i, ∃ k : ℤ, (N : ℝ) * u i = (k : ℝ)) ∧
        (∀ i, |c i| ≤ properCyclicCoordinateBound t (Real.exp (-B)) + 1 / 16) ∧
        ∀ h ∈ K, (∀ i, |affineCyclicTorusLocalLift u c h₀ h i| ≤ 1 / 16) ∧
          A h = positiveUnivariate (fun j => (x j).val +
            ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) ∧
          ∀ n : ℤ,
            (markedShiftEval D.coefficientFreeFiltration D.coefficientFreeGenerator
              D.coefficientWeight D.coefficientIsDependent t
                (fun i => (-affineCyclicTorusCarry u c h₀ h i : ℤ))).baseChange ℝ
                  (D.localAffineMarkedLift t x y u c h₀ h n) = eval (fun _ => (n : ℚ)) (A h) := by
  obtain ⟨K, hKJ, hK, hcard, _, _, u, c, α', β', hu, hperiod, hc, hα', hβ', hlocal⟩ :=
    exists_local_affine_polynomial_family hB ht η radius hinj h₀ J hJ hdense v hv hrep
      A Γ α β (fun j => (D.dependentFreeSpan j).baseChange ℝ) hα hβ hA
  let x : ∀ j : Fin s, (D.coefficientFreeSpan j).baseChange ℝ := fun j =>
    ⟨coefficients Γ (Finsupp.single () (j.val + 1)) + α' j,
      Submodule.add_mem _ (hΓ j) (Submodule.baseChange_mono ℝ
        (D.dependentFreeSpan_le_coefficientFreeSpan j) (hα' j))⟩
  let y : ∀ j : Fin s, Fin t → (D.dependentFreeSpan j).baseChange ℝ :=
    fun j i => ⟨β' i j, hβ' i j⟩
  refine ⟨K, hKJ, hK, hcard, u, c, x, y, hu, hperiod, hc, ?_⟩
  intro h hh
  obtain ⟨hsmall, hpoly⟩ := hlocal h hh
  have he : A h = positiveUnivariate (fun j => (x j).val +
      ∑ i, affineCyclicTorusLocalLift u c h₀ h i • (y j i).val) := by
    rw [hpoly, ← positiveUnivariate_reconstruct Γ hΓdeg hΓzero]
    simp only [x, y, positiveUnivariate, monomial, TensorProduct.tmul_add,
      Finset.sum_add_distrib, add_assoc]
  exact ⟨hsmall, he, fun n => D.localAffineMarkedLift_eq_polynomial_eval t x y u c h₀ A h he n⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CorrelatedAffineComparison.localMarkedFamily
    (hs : 2 ≤ s) (hP' : 0 ≤ P')
    (hdense : Real.exp (-P') * N ≤ (H'.card : ℝ))
    (h : D.CorrelatedAffineComparison E T hbQ hT V g hg D' hs) :
    D.CorrelatedLocalMarkedFamily E T hbQ hT V g hg D' hs := by
  classical
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let C := sharedFreeCorrelationBudget s hs P'
  let B := P' + Λ + C
  obtain ⟨J, hJH, hJ, hJcard, t, radius, η, h₀, Γ, α, β,
    ht, hinj, hΓ0, hΓ, hα, hβ, v, A, K, U, hdata,
    Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hfreq, hcorr, M, Tm, hTm, hTmc, hfamily⟩ := h
  have hΛ : 0 ≤ Λ := pow_nonneg (add_nonneg hP' (Nat.cast_nonneg _)) _
  have hC : 0 ≤ C :=
    (show 0 ≤ sharedFreeCorrelationInput s P' by
      linarith only [(sharedFreeCorrelationInput_bounds s hP' le_rfl hP').1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hP')
  have hB : 0 ≤ B := add_nonneg (add_nonneg hP' hΛ) hC
  have htB : (t : ℝ) ≤ B := ht.trans (by dsimp only [B]; linarith only [hP', hC])
  have hJB : Real.exp (-B) * N ≤ (J.card : ℝ) := by
    calc
      _ = Real.exp (-(Λ + C)) * (Real.exp (-P') * N) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        dsimp only [B]
        ring
      _ ≤ Real.exp (-(Λ + C)) * H'.card :=
        mul_le_mul_of_nonneg_left hdense (Real.exp_pos _).le
      _ ≤ _ := hJcard
  let v' (h : ZMod N) := if hh : h ∈ J then v ⟨h, hh⟩ else 0
  let A' (h : ZMod N) := if hh : h ∈ J then (A ⟨h, hh⟩).log else 0
  have hv' (h : ZMod N) (hh : h ∈ J) : ∀ i, |v' h i| ≤ (radius i : ℤ) := by
    simpa only [v', dif_pos hh] using (hdata ⟨h, hh⟩).1
  have hrep' (h : ZMod N) (hh : h ∈ J) : h = h₀ + η (v' h) := by
    simpa only [v', dif_pos hh] using (hdata ⟨h, hh⟩).2.1
  have hA' (h : ZMod N) (hh : h ∈ J) :
      A' h = Γ.log + positiveUnivariate (fun j => α j + ∑ i, (v' h i : ℝ) • β i j) := by
    simpa only [A', v', dif_pos hh] using (hdata ⟨h, hh⟩).2.2.1
  have hΓzero : coefficients Γ.log 0 = 0 := by
    have he := congrArg NilpotentLieBCHGroup.coord hΓ0
    simpa only [E.filtration.realification.polynomialOrbitEval_coord, Pi.zero_apply,
      Int.cast_zero, eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using he
  have hΓmem (j : Fin s) : coefficients Γ.log (Finsupp.single () (j.val + 1)) ∈
      (D.coefficientFreeSpan j).baseChange ℝ :=
    Submodule.baseChange_mono ℝ
      (refined_firstProjection_le_common _ _ (D.dependentFreeSpan_le_coefficientFreeSpan j) _) (hΓ j)
  obtain ⟨J₁, hJ₁J, hJ₁, hcard, u, c, x, y, hu, hperiod, hc, hlocal⟩ :=
    D.exists_common_local_marked_family hB htB η radius hinj h₀ J hJ hJB v' hv' hrep'
      A' Γ.log Γ.degreeLE hΓzero hΓmem α β (fun j => (hα j).1) (fun i j => (hβ i j).1) hA'
  let lift (h : {h // h ∈ J₁}) : {h // h ∈ J} := ⟨h.val, hJ₁J h.property⟩
  refine ⟨J₁, (fun h hh => hJH (hJ₁J hh)), hJ₁, hcard, t, ht,
    h₀, u, c, x, y, hu, hperiod, hc, (fun h => A (lift h)), (fun h => K (lift h)),
    (fun h => U (lift h)), ?_, Δ, hΔ, hchar, hnormal, hfinite, hindex,
    l, hl, hin, hout, hRank, V₁, hfreq, (fun h => hcorr (lift h)), M, Tm, hTm, hTmc, ?_⟩
  · intro h
    obtain ⟨hsmall, hpoly, heval⟩ := hlocal h.val h.property
    have hAA : A' h.val = (A (lift h)).log := by simp only [A', dif_pos (hJ₁J h.property), lift]
    rw [hAA] at hpoly heval
    obtain ⟨_, _, _, hA0, hK0, hU0, hKU⟩ := hdata (lift h)
    refine ⟨hsmall, hpoly, hA0, hK0, hU0, hKU, ?_⟩
    intro n
    exact heval n
  · exact hfamily.reindex lift

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CorrelatedLocalMarkedFamily.induce
    (B₀ : D.CoefficientBases Q) (F : FreeCoordinateFrame E.basis Q)
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hfreq : V.frequency = B₀.freeFrequency D)
    (hs : 2 ≤ s) (hP' : 0 ≤ P')
    (hlocal : D.CorrelatedLocalMarkedFamily E T hbQ hT V g hg D' hs) :
    let Z := Q + (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s +
      sharedFreeCorrelationBudget s hs P' + 2
    let C := (exists_covered_induced_correlation_family s (by omega)).choose
    D.CorrelatedLocalInducedFamily E T hbQ hT V g hg D' hs ((Z + C) ^ C) := by
  intro Z Cout
  obtain ⟨J, hJH, hJ, hJcard, t, ht, h₀, u, c, x, y, hu, hperiod, hc,
    A, K, U, hdata, Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hVfreq, hcorr, M, Tm, hTm, hTmc, hfamily⟩ := hlocal
  let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
  let Cc := sharedFreeCorrelationBudget s hs P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg W.family.dim).trans (W.family.complexity.1.1.trans hbQ)
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have hCc : 0 ≤ Cc :=
    (show 0 ≤ sharedFreeCorrelationInput s P' by
      linarith only [(sharedFreeCorrelationInput_bounds s hP' le_rfl hP').1]).trans
        (sharedFreeCorrelationInput_le_budget s hs hP')
  have hCZ : Cc ≤ Z := by
    change Cc ≤ Q + Λ + Cc + 2
    linarith
  have hQZ : Q ≤ Z := by
    change Q ≤ Q + Λ + Cc + 2
    linarith
  have hΛZ : Λ ≤ Z := by
    change Λ ≤ Q + Λ + Cc + 2
    linarith
  have hZ : 0 ≤ Z := hCc.trans hCZ
  refine ⟨J, hJH, hJ, hJcard, t, ht, h₀, u, c, x, y, hu, hperiod, hc,
    A, K, U, hdata, Δ, hΔ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
    hRank, V₁, hVfreq, hcorr, ?_, M, Tm, hTm, hTmc, hfamily⟩
  refine ⟨hCZ, ?_⟩
  apply (exists_covered_induced_correlation_family s (by omega)).choose_spec.2
    D B₀ t (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout) (V₁.mono hCZ)
    hTfil (hVfreq.trans hfreq) hZ (hRank.mono _ hCZ) (ht.trans hΛZ)
    (fun i j => (F.generator_height (by omega) i j).trans hQZ)
    (by
      simpa only [Fintype.card_fin] using
        W.family.output_bound.trans (Real.exp_le_exp.mpr (hbQ.trans hQZ)))
    x y u c h₀ (fun h : {h // h ∈ J} => h.val) A (fun h => A h * K h * U h)
    (fun h i => ((hdata h).1 i).trans (by norm_num))
    (fun h => (hdata h).2.1) (fun h => (hdata h).2.2.1)
  intro h
  exact (hcorr h).map (fun B => B.mono hCZ)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial RationalFilteredNilmanifold
open scoped BigOperators TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s (r + 1) N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure (r + 1)) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s (r + 1)) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)
  {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

theorem CorrelatedLocalInducedFamily.product (hs : 2 ≤ s) {Bound : ℝ}
    (hlocal : D.CorrelatedLocalInducedFamily E T hbQ hT V g hg D' hs Bound) :
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let C := sharedFreeCorrelationBudget s hs P'
    let B := P' + Λ + C
    let Qc := C + sharedFreeComparisonBasisBudget Q P' + 2
    0 ≤ Bound ∧ 0 ≤ nativeLowerPairModelBudget s Qc ∧
    ∃ J : Finset (ZMod N), J ⊆ H' ∧ J.Nonempty ∧
      Real.exp (-((B + 4) ^ 7)) * N ≤ (J.card : ℝ) ∧
      HasBoundedProductCorrelation (I := Fin W.family.outputDim) (s := s) (r := r) (degree := s - 1)
        (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
        W.mixed.outputDim Bound
        (productNiltestBudget (nativeLowerPairModelBudget s Qc + Bound + 2))
        (productNiltestBudget (b + Bound + 2 + 4)) := by
  intro Λ C B Qc
  obtain ⟨J, hJH, hJ, hJcard, t, _, h₀, u, c, x, y, _, _, _,
    A, K, U, _, Δ, _, _, _, _, _, l, hl, hin, hout,
    _, V₁, _, _, hcovered, M, Tm, _, _, hfirst⟩ := hlocal
  obtain ⟨hCZ, hcovered⟩ := hcovered
  have hBound : 0 ≤ Bound := by
    obtain ⟨Δ₂, _, l₂, hl₂, hin₂, hout₂, hT₂, _⟩ := hcovered
    exact (Nat.cast_nonneg _).trans hT₂.1.1
  have hFirst : 0 ≤ nativeLowerPairModelBudget s Qc := by
    obtain ⟨n₀, _, Q₀, R₀, hR₀, _⟩ := hfirst
    exact (Nat.cast_nonneg n₀).trans hR₀.1.1
  have hunit := HasCoveredInducedCorrelationFamily.combineLower
    D t x y u c h₀ (fun h : {h // h ∈ J} => h.val)
    (fun h i z => multiplicativeDerivative f h.val z *
      star (W.mixed.evalCyclic N i (correlationInput h.val z)))
    (E.withLattice Δ l hl hin hout) (T.withLattice Δ l hl hin hout)
    (V₁.mono hCZ) A (fun h => A h * K h * U h)
    hBound hFirst hcovered M Tm hfirst
  refine ⟨hBound, hFirst, J, hJH, hJ, hJcard, ?_⟩
  exact HasUnitRankInducedCorrelationFamily.combineMixed D t x y u c h₀
    (fun h : {h // h ∈ J} => h.val) (fun h z => multiplicativeDerivative f h.val z)
    W.mixed hBound hunit

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedProductiveFrozenMajorDetection
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial Submodule BooleanCubeKernel RationalFilteredNilmanifold
open scoped BigOperators Classical TensorProduct NNReal

variable {m : ℕ} {G X : Type} [Fintype G] [Fintype X] [DecidableEq X]
    {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
    {J : Fin m → Type} [∀ j, Fintype (J j)]
    {U : ∀ j, Submodule ℝ (J j → ℝ)}
    {btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
    {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U btag R σ}
    {hb : ∀ j, span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (U j))}
    {o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j))}
    {hR : ∀ j, 0 < R j} {hσ : ∀ j, 0 < σ j}
    {N : X → ℕ} {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)}
    {hm : ∀ j e, coefficients (poly j) e ∈ U j}
    {τ ξ : ℝ} {stride : X → ℕ}
    {cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride)}
    {center : CoefficientTorus (K := LayerSamplerVariables G I n B) U}
    [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
    (A : AllocatedExternalCandidateSampler B U btag S hb o hR hσ N poly hm τ ξ stride cells center)

namespace VectorPolynomial.AllocatedExternalCandidateSampler

theorem NativeDetection.localMajorSliceDetection
    {degree dim : ℕ} {L : Type} [LieRing L] [LieAlgebra ℚ L]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {pSlice pTest pNative α cost budget : ℝ}
    (hdetect : A.NativeDetection degree pSlice pTest pNative α)
    (D : RationalFilteredNilmanifold L degree dim)
    {Tests : A.Path → Type} [∀ z, Nonempty (Tests z)]
    (chosen : ∀ z, Tests z → LocalMajorSliceTest D A.sides cost budget)
    (hcost : cost ≤ pSlice) (hbudget : budget ≤ pTest) :
    SampledSliceNativeDetection J N A.integerBox_nonempty poly A.law A.physical
      (fun z a => (chosen z a).slice.subtypeSites)
      (fun z a (x : A.Site) => (chosen z a).weight x.val) degree pNative α := by
  exact hdetect (fun _ _ => D) (fun z a => (chosen z a).test)
    (fun z a => (chosen z a).slice.subtypeSites)
    (fun z a i => ((chosen z a).slice.start i : ℤ))
    (fun z a => (chosen z a).stride) (fun z a => (chosen z a).slice.length)
    (fun z a => (chosen z a).stride_pos)
    (fun z a => (chosen z a).slice.subtypeSites_image_val.trans
      (chosen z a).slice.integerPoints_eq_commonStrideBox)
    (fun z a => ((chosen z a).slice.subtypeSites_dense (chosen z a).dense).mono hcost)
    (fun z a => (chosen z a).complexity.mono hbudget)
    (fun z a => (chosen z a).norm)

end VectorPolynomial.AllocatedExternalCandidateSampler

namespace NilpotentLieFiltration

theorem exists_allocated_full_chart_major_correlation_witness_of_frozen_local_tests
    {k t : ℕ} {L ι η : Type} [Fintype η]
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
    (fast : Submodule ℚ F.AssociatedGraded)
    (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (htk : t < k)
    (hpoly : ∀ j, DegreeLE (fun _ => 1) (j.val + 1) (poly j))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)
    (pSlice pTest pNative pMajor Rrank : ℝ) (C : ℕ)
    (hpNative : 2 ≤ pNative) (hη : (Fintype.card η : ℝ) ≤ pNative)
    (hNativeMajor : pNative ≤ pMajor) (hproduct : productNiltestBudget pNative ≤ pMajor)
    (hdim : ((Fintype.card X + Fintype.card (Σ j, J j) : ℕ) : ℝ) ≤ pMajor)
    (hN : ∀ i, Real.exp ((pMajor + C) ^ C) ≤ (N i : ℝ))
    (hRrank : Real.exp ((pMajor + C) ^ C) ≤ Rrank)
    (hrank : ∀ j, HasLayerSamplingRank (j.val + 1)
      (fun i => (N i : ℝ)) Rrank (U j) (poly j))
    (good : η → Finset A.Path)
    (keep : LayerSamplerVariables G I n B → Prop)
    (cost Bshort : ℝ) (hcost : 0 ≤ cost)
    (hBshort : 1 ≤ Bshort) (hshort : ∀ i, ¬keep i → (A.sides i : ℝ) ≤ Bshort)
    (hξ : ξ ≤ 1)
    (α : ℝ) (hmass : ∀ j, α ≤ (9 / 10 : ℝ) * A.law.mass (good j))
    (hdirect : A.NativeDetection t pSlice pTest pNative α)
    (hslice : max cost (Real.log Bshort) ≤ pSlice)
    (htest : OrdinaryPolynomialPhase.budget t ≤ pTest)
    (hlocal : ∀ j z, z ∈ good j →
      ∃ fixed : {i // ¬keep i} → ℤ,
        (∀ i, 0 ≤ fixed i ∧ fixed i < A.sides i.val) ∧
      ∃ T : LocalMajorSliceTest (OrdinaryPolynomialPhase.nilmanifold t)
        (fun i : {i // keep i} => A.sides i.val) cost (OrdinaryPolynomialPhase.budget t),
        (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ T.slice.integerPoints,
          majorPhasePlateauSignal J k poly c
            (coordinate (basis.coord j).toAddMonoidHom
              (lowTaggedVectorRestrict J k (F.realSymbolGradeQuotientPolynomial b ω hF
                (fullTaggedVariableWeight (X := X) J) fast k (left⁻¹ * Z * right⁻¹).coord)))
            (jointIntegerPhysicalSite (finiteSplitPoint keep x fixed) (z.1.val, z.2.val)) * T.weight x‖) :
    Nonempty (FullChartMajorCorrelationWitness F b ω hF J k fast basis
      Z left right N poly U pMajor Rrank C) := by
  apply exists_full_chart_major_correlation_witness_of_frozen_productive_local_tests
    F b ω hF J fast basis Z left right htk N A.integerBox_nonempty poly hpoly U
    (fun j e _ => hm j e) c pNative pMajor Rrank C hpNative hη hNativeMajor hproduct
    hdim hN hRrank hrank A.law good A.sides A.sides_pos keep cost Bshort hcost hBshort hshort
    (fun z x => jointIntegerPhysicalSite x (z.1.val, z.2.val))
    (fun _ z _ x hx => by
      simpa only [mem_integerBox, AllocatedExternalCandidateSampler.physical] using
        A.physical_mem_integerBox hξ z ⟨x, hx⟩) α hmass
  · intro chosen
    exact hdirect.localMajorSliceDetection A (OrdinaryPolynomialPhase.nilmanifold t)
      chosen hslice htest
  · have hdec :
        (fun a b : {i : LayerSamplerVariables G I n B // keep i} =>
          Classical.propDecidable (a = b)) =
        (fun a b => @Subtype.instDecidableEq _ keep
          (inferInstance : DecidableEq (LayerSamplerVariables G I n B)) a b) :=
      Subsingleton.elim _ _
    rw [hdec] at hlocal
    exact hlocal

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AllocatedKeptCommonCurrentGradeLocalNiltest
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators TensorProduct

namespace NilpotentLieFiltration

variable {U ι L : Type*} [Fintype U] [DecidableEq U] [Fintype ι]
  [LieRing L] [LieAlgebra ℚ L] {s n : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]
  [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
    OrdinaryPolynomialPhase.weight n)]

theorem exists_currentGrade_localMajor_niltest_with_lower_phase
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ F.AssociatedGraded)
    (θ : F.AssociatedGraded →ₗ[ℚ] ℚ) (hθW : ∀ x ∈ W, θ x = 0)
    (E P R E₀ R₀ : F.RealPolynomialSymbolGroup (fun _ : U => 1))
    (hP : P.coord ∈ realificationLieSubalgebra
      (F.symbolPointwiseSubalgebra b ω hF (fun _ : U => 1) W))
    (hE : F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) E₀ =
      F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) E)
    (hR : F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) R =
      F.realSymbolGradeQuotientHom (fun _ : U => 1) (n + 1) R₀)
    (N : U → ℕ) (H m : ℕ) (hm : 0 < m) (M p : ℝ) (hM : 0 ≤ M)
    (hθH : ∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) H)
    (hslow : F.SymbolSlowBound b ω hF (fun _ : U => 1)
      (fun i => (N i : ℝ)) M (E₀⁻¹ * E))
    (hgrid : F.SymbolRationalGrid b ω hF (fun _ : U => 1) m (R * R₀⁻¹))
    (hp : 1 ≤ p) (hdim : (Fintype.card U : ℝ) ≤ p)
    (hMexp : (Fintype.card ι : ℝ) * H * M ≤ Real.exp p)
    (hqexp : ((H ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp p)
    (f : (U → ℤ) → ℝ) (lower : MvPolynomial U ℝ)
    (hlower : lower.totalDegree ≤ n)
    (hN : ∀ i, Real.exp ((p + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) :
    ∃ q : ℕ, 0 < q ∧ q ≤ H ^ Fintype.card ι * m ∧
      ∃ A : ResidueBoxSlice N q,
        IsDenseCommonStrideBox N ((p + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
        (𝔼 x : (∀ i, Fin (N i)), f (fun i => ((x i).val : ℤ))) ≤
          (𝔼 x ∈ A.integerPoints, f x) ∧
        ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : U => 1),
          T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
          (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
            (Real.fourierChar (eval (fun i => (x i : ℝ))
              (homogeneousComponent (n + 1)
                (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ
                  (E₀⁻¹ * (E * P * R) * R₀⁻¹)) + lower)) : ℂ) *
              star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  have hNpos : ∀ i, 0 < (N i : ℝ) := fun i => (Real.exp_pos _).trans_le (hN i)
  obtain ⟨q, hq, hqbound, hqgrid⟩ :=
    F.scalarSymbolPolynomial_exists_coefficient_grid b ω hF (fun _ : U => 1)
      θ hθH m hm (R * R₀⁻¹) hgrid
  let φ := F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ
    (E₀⁻¹ * (E * P * R) * R₀⁻¹)
  let slow := homogeneousComponent (n + 1)
    (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ (E₀⁻¹ * E))
  let rat := homogeneousComponent (n + 1)
    (F.scalarSymbolPolynomial b ω hF (fun _ : U => 1) θ (R * R₀⁻¹))
  have htop : homogeneousComponent (n + 1) (homogeneousComponent (n + 1) φ + lower) =
      slow + rat := by
    rw [map_add, homogeneousComponent_eq_self (homogeneousComponent_isHomogeneous _ _),
      homogeneousComponent_eq_zero _ lower (by omega), add_zero]
    exact F.scalarSymbolPolynomial_homogeneous_normalized_splitting b ω hF θ W hθW
      (n + 1) E P R E₀ R₀ hP hE hR
  have hcap : 0 ≤ (Fintype.card ι : ℝ) * H * M := by positivity
  have hcoeff : ∀ α, |slow.coeff α| ≤
      ((Fintype.card ι : ℝ) * H * M) / monomialScale (fun i => (N i : ℝ)) α :=
    homogeneousComponent_scaled_coeff_bound _ (n + 1) _ hNpos _ hcap
      (F.scalarSymbolPolynomial_slow_coefficients_of_height b ω hF (fun _ : U => 1)
        θ _ hNpos hM hθH (E₀⁻¹ * E) hslow)
  obtain ⟨A, hA, hscore, T, hTnorm, hTbudget, hcorr⟩ :=
    exists_localMajor_dense_slice_niltest_early N q hq
      (homogeneousComponent (n + 1) φ + lower) slow rat
      ((totalDegree_add _ _).trans (max_le
        (homogeneousComponent_isHomogeneous _ _).totalDegree_le (hlower.trans (Nat.le_succ n))))
      (homogeneousComponent_isHomogeneous _ _).totalDegree_le htop
      (realPolynomialCoefficientGrid_homogeneousComponent hqgrid (n + 1))
      ((Fintype.card ι : ℝ) * H * M) p hcap hp hdim hMexp
      ((Nat.cast_le.mpr hqbound).trans hqexp) hcoeff f hN
  exact ⟨q, hq, hqbound, A, hA, hscore, T, hTnorm, hTbudget, hcorr⟩

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem exists_actual_path_current_grade_local_niltest (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [DecidableEq τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ N : τ → ℕ, (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {n : ℕ}
          [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)], n ≤ s →
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : κ → F.PolynomialSymbol (fun _ : τ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U).toSubmodule →
        (∀ i z, RationalHeightLE
          ((F.polynomialSymbolBasis b ω hF (fun _ : τ => 1)).repr (vg i) z) H) →
        ∀ {σ : Type*} (w : σ → ℕ) (β : σ → MvPolynomial τ ℝ),
        ∀ hβ : ∀ i, β i ∈ weightedSupportLE (fun _ : τ => 1) (w i),
        ∀ K : Set (σ → ℝ),
        (∀ u : τ → ℝ,
          (fun i => MvPolynomial.eval u
            (weightedHomogeneousComponent (fun _ : τ => 1) (w i) (β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration w).Group)
          (E R : F.RealPolynomialSymbolGroup w),
        (∀ t ∈ K, ∀ j < n + 1, F.realSymbolGradeEvaluation b ω hF w j t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF w g * R⁻¹).coord ∈ realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1)
          (fun i => weightedHomogeneousComponent (fun _ : τ => 1) (w i) (β i))
          (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : τ => 1)),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
          (F.weightedAdaptedRealChartHom w (fun _ : τ => 1) β hβ g) →
        Pl.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U) →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l Rl →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l (pull R) →
        ∀ (θ : F.AssociatedGraded →ₗ[ℚ] ℚ), (∀ x ∈ U, θ x = 0) →
        ∀ (Hθ : ℕ) (pLocal : ℝ),
        (∀ i, RationalHeightLE (θ (F.associatedGradedBasis b ω hF i)) Hθ) →
        1 ≤ pLocal → (Fintype.card τ : ℝ) ≤ pLocal →
        (Fintype.card ι : ℝ) * Hθ * Real.exp ((p + C) ^ C) ≤ Real.exp pLocal →
        ((Hθ ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp pLocal →
        ∀ (score : (τ → ℤ) → ℝ) (lower : MvPolynomial τ ℝ), lower.totalDegree ≤ n →
        (∀ i, Real.exp ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * m ∧
          ∃ A : ResidueBoxSlice N q,
            IsDenseCommonStrideBox N ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
            (𝔼 x : (∀ i, Fin (N i)), score (fun i => ((x i).val : ℤ))) ≤
              (𝔼 x ∈ A.integerPoints, score x) ∧
            ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : τ => 1),
              T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
              (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
                (Real.fourierChar (eval (fun i => (x i : ℝ))
                  (homogeneousComponent (n + 1)
                    (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1) θ
                      ((pull E)⁻¹ * F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
                        (F.weightedAdaptedRealChartHom w (fun _ : τ => 1) β hβ g) *
                          (pull R)⁻¹)) + lower)) : ℂ) *
                  star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  obtain ⟨C, hC, hreset⟩ := exists_actual_path_current_grade_reset s a
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ _ F b ω hF H l p hH hl hp hι hτ hκ hHp hlp hb N hN
  obtain ⟨m, hm, hmp, hlm, hresetm⟩ := hreset F b ω hF (fun _ : τ => 1)
    (fun _ => Nat.zero_lt_one) H l p hH hl hp hι hτ hκ hHp hlp hb (fun i => (N i : ℝ)) hN
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro n _ _ _ _ hn U vg hspan hvg σ w β hβ K hK g E R hx
  dsimp only
  let pull := F.realSymbolHomogeneousPullbackHom b ω hF w (fun _ : τ => 1)
    (fun i => weightedHomogeneousComponent (fun _ : τ => 1) (w i) (β i))
    (fun _i => weightedHomogeneousComponent_isWeightedHomogeneous _ _)
  intro El Pl Rl hlocal hPl hEl hE hRl hR θ hθ Hθ pLocal hθH hpLocal hdimLocal
    hMexp hqexp score lower hlower hNLocal
  obtain ⟨E', P', R', hprod, hP', hE', hR', _, _, hslowdiff, hgriddiff⟩ :=
    hresetm U vg hspan hvg w β hβ K hK g E R (n + 1) (Nat.add_le_add_right hn 1)
      hx El Pl Rl hlocal hPl hEl hE hRl hR
  have htest := F.exists_currentGrade_localMajor_niltest_with_lower_phase b ω hF U θ hθ
    E' P' R' (pull E) (pull R) hP' hE' hR' N Hθ m hm
    (Real.exp ((p + C) ^ C)) pLocal (Real.exp_nonneg _) hθH hslowdiff hgriddiff
    hpLocal hdimLocal hMexp hqexp score lower hlower hNLocal
  rw [hprod] at htest
  exact htest

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped TensorProduct BigOperators

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

theorem exists_actual_path_buffered_localMajor_niltest (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {τ ι κ L : Type*} [Fintype τ] [DecidableEq τ] [Fintype ι] [Fintype κ]
      [LieRing L] [LieAlgebra ℚ L]
      (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
      (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
      (H l : ℕ) (p : ℝ), 1 ≤ H → 0 < l → 0 ≤ p →
      (Fintype.card ι : ℝ) ≤ p → (Fintype.card τ : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p → (l : ℝ) ≤ Real.exp p →
      (∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H) →
      ∀ N : τ → ℕ, (∀ i, Real.exp ((p + C) ^ C) ≤ (N i : ℝ)) →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
        ∀ {n : ℕ}
          [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)]
          [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra
            OrdinaryPolynomialPhase.weight n)], n ≤ s →
        ∀ (U : LieSubalgebra ℚ F.AssociatedGraded)
          (vg : κ → F.PolynomialSymbol (fun _ : τ => 1)),
        Submodule.span ℚ (Set.range vg) =
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U).toSubmodule →
        (∀ i z, RationalHeightLE
          ((F.polynomialSymbolBasis b ω hF (fun _ : τ => 1)).repr (vg i) z) H) →
        ∀ {mTag : ℕ} {X η : Type} (J : Fin mTag → Type) [∀ j, Fintype (J j)]
          (eQ : Basis η ℚ (F.AssociatedGraded ⧸ U.toSubmodule)) (j : η)
          (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
          (c : Fin (Fintype.card (LowTaggedIndex J (n + 1))) → ℝ)
          (β : X ⊕ (Σ j, J j) → MvPolynomial τ ℤ),
        ∀ hβ : ∀ i, integerSampledRealChart β i ∈
          weightedSupportLE (fun _ : τ => 1) (fullTaggedVariableWeight J i),
        ∀ K : Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ u : τ → ℝ, (fun i => MvPolynomial.eval u
          (homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))) ∈ K) →
        ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
          (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)),
        (∀ t ∈ K, ∀ d < n + 1,
          F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
            (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
              realificationLieSubalgebra U) →
        let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
          (fun _ : τ => 1)
          (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
          (fun i => sampledTopPhase_coordinate_homogeneous
            (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : τ => 1)),
        El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
          (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : τ => 1)
            (integerSampledRealChart β) hβ g) →
        Pl.coord ∈ realificationLieSubalgebra
          (F.symbolPointwiseSubalgebra b ω hF (fun _ : τ => 1) U) →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) El →
        F.SymbolSlowBound b ω hF (fun _ : τ => 1) (fun i => (N i : ℝ))
          (Real.exp ((p + 2) ^ a)) (pull E) →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l Rl →
        F.SymbolRationalGrid b ω hF (fun _ : τ => 1) l (pull R) →
        ∀ (Hθ : ℕ) (pLocal : ℝ),
        (∀ i, RationalHeightLE (((eQ.coord j).comp U.toSubmodule.mkQ)
          (F.associatedGradedBasis b ω hF i)) Hθ) →
        1 ≤ pLocal → (Fintype.card τ : ℝ) ≤ pLocal →
        (Fintype.card ι : ℝ) * Hθ * Real.exp ((p + C) ^ C) ≤ Real.exp pLocal →
        ((Hθ ^ Fintype.card ι * m : ℕ) : ℝ) ≤ Real.exp pLocal →
        ∀ score : (τ → ℤ) → ℝ,
        (∀ i, Real.exp ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) ≤ (N i : ℝ)) →
        (∀ u ∈ integerBox N, ∀ i,
          |MvPolynomial.eval (fun x => (integerSampledSpatial β u x : ℝ))
            (lowTaggedPolynomial J (n + 1) poly i) - c i -
              (integerSampledLowTags J (n + 1) β u i : ℝ)| ≤ 1 / 8) →
        ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * m ∧
          ∃ A : ResidueBoxSlice N q,
            IsDenseCommonStrideBox N ((pLocal + (n + 401 : ℕ)) ^ (n + 401)) A.integerPoints ∧
            (𝔼 x : (∀ i, Fin (N i)), score (fun i => ((x i).val : ℤ))) ≤
              (𝔼 x ∈ A.integerPoints, score x) ∧
            ∃ T : (OrdinaryPolynomialPhase.nilmanifold n).Niltest (fun _ : τ => 1),
              T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget n) ∧
              (9 / 10 : ℝ) ≤ ‖𝔼 x ∈ A.integerPoints,
                majorPhasePlateauSignal J (n + 1) poly c
                  (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                    (lowTaggedVectorRestrict J (n + 1)
                      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                        U.toSubmodule (n + 1)
                        (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                  (integerSampledSpatial β x) *
                    star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))‖ := by
  obtain ⟨C, hC, htest⟩ := exists_actual_path_current_grade_local_niltest s a
  refine ⟨C, hC, ?_⟩
  intro τ ι κ L _ _ _ _ _ _ F b ω hF H l p hH hl hp hι hτ hκ hHp hlp hb N hN
  obtain ⟨m, hm, hmp, hlm, htestm⟩ := htest F b ω hF H l p
    hH hl hp hι hτ hκ hHp hlp hb N hN
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro n _ _ _ _ hn U vg hspan hvg mTag X η J _ eQ j poly c β hβ K hK g E R hx
  dsimp only
  intro El Pl Rl hlocal hPl hEl hE hRl hR Hθ pLocal hθH hpLocal hdimLocal
    hMexp hqexp score hNLocal hbuffer
  obtain ⟨lower, hlower, hphase⟩ := F.exists_bufferedSampledCurrentGrade_phase
    b ω hF J β hβ U.toSubmodule eQ j n
    (F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g) E R poly c
  have hθ : ∀ x ∈ U, ((eQ.coord j).comp U.toSubmodule.mkQ) x = 0 :=
    fun x hx => F.quotientFunctional_kills_fast U.toSubmodule (eQ.coord j) x hx
  obtain ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, hcorr⟩ :=
    htestm hn U vg hspan hvg (fullTaggedVariableWeight J) (integerSampledRealChart β)
      hβ K hK g E R hx El Pl Rl hlocal hPl hEl hE hRl hR
      ((eQ.coord j).comp U.toSubmodule.mkQ) hθ Hθ pLocal hθH hpLocal hdimLocal
      hMexp hqexp score lower hlower hNLocal
  refine ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, ?_⟩
  have hactual := F.realPolynomialSymbolHom_weightedAdaptedRealChart b ω hF
    (fullTaggedVariableWeight J) (fun _ : τ => 1) (integerSampledRealChart β) hβ g
  have hinside (u : τ → ℤ) (hu : u ∈ A.integerPoints) : u ∈ integerBox N := by
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hu
    apply (mem_integerBox N _).mpr
    intro i
    refine ⟨Int.natCast_nonneg _, ?_⟩
    change ((A.point t i).val : ℤ) < (N i : ℤ)
    exact_mod_cast (A.point t i).isLt
  have heq : (𝔼 x ∈ A.integerPoints,
      majorPhasePlateauSignal J (n + 1) poly c
        (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
          (lowTaggedVectorRestrict J (n + 1)
            (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
              U.toSubmodule (n + 1)
              (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
        (integerSampledSpatial β x) *
          star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))) =
      (𝔼 x ∈ A.integerPoints,
        (Real.fourierChar (eval (fun i => (x i : ℝ))
          (homogeneousComponent (n + 1)
            (F.scalarSymbolPolynomial b ω hF (fun _ : τ => 1)
              ((eQ.coord j).comp U.toSubmodule.mkQ)
              ((F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
                (fun _ : τ => 1)
                (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
                (fun i => sampledTopPhase_coordinate_homogeneous
                  (fullTaggedVariableWeight J i) (integerSampledRealChart β i)) E)⁻¹ *
                F.realPolynomialSymbolHom b ω hF (fun _ : τ => 1)
                  (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J) (fun _ : τ => 1)
                    (integerSampledRealChart β) hβ g) *
                (F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
                  (fun _ : τ => 1)
                  (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
                  (fun i => sampledTopPhase_coordinate_homogeneous
                    (fullTaggedVariableWeight J i) (integerSampledRealChart β i)) R)⁻¹)) + lower)) : ℂ) *
          star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))) := by
    apply Finset.expect_congr rfl
    intro x hxA
    have h := hphase x (hbuffer x (hinside x hxA))
    rw [hactual]
    exact congrArg (fun z : ℂ => z *
      star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q x))) h
  rw [heq]
  exact hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct BigOperators Classical

attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

noncomputable def allocatedFrozenCurrentGradeResetConstant (s a : ℕ) : ℕ :=
  Classical.choose (exists_actual_path_buffered_localMajor_niltest.{0, 0, 0, 0} s a)

variable {mTag : ℕ} {G X : Type} [Fintype G] {I Deck J : Fin mTag → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin mTag → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (Utag j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
variable {Rad σ : Fin mTag → ℝ} (S : LayerSamplerScale (G := G) B Utag btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)

theorem exists_allocated_frozen_current_grade_local_niltest (s a : ℕ)
    (keep : LayerSamplerVariables G I n B → Prop)
    {ι κ L : Type} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l : ℕ) (p : ℝ) (hH : 1 ≤ H) (hl : 0 < l) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hτ : (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    (hN : ∀ i : {i : LayerSamplerVariables G I n B // keep i},
      Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ≤
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val : ℕ) : ℝ)) :
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧ l ∣ reset ∧
      ∀ {r : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)], r ≤ s →
      ∀ (fast : LieSubalgebra ℚ F.AssociatedGraded)
        (vg : κ → F.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast).toSubmodule →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
      ∀ {η : Type} (eQ : Basis η ℚ (F.AssociatedGraded ⧸ fast.toSubmodule)) (j : η)
        (c : ∀ j, Utag j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag S hRad hσ poly hm c origin v sample read →
      ∀ (fixed : {i : LayerSamplerVariables G I n B // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val) →
      (∀ j, σ j ≤ 1) →
      ∀ (Cgeo : Fin mTag → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Bstage pK M LongSide : ℝ) (blocks : ℕ),
      RationalTaggedConstraintCertificate J Set.univ K Bstage blocks →
      (∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      0 ≤ pK → Bstage ≤ pK → (∀ j, (Fintype.card (J j) : ℝ) ≤ pK) →
      0 ≤ M → (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ M) →
      1 ≤ LongSide →
      (∀ i, keep i → LongSide ≤ layerSamplerBox B Utag btag S i) →
      Real.exp ((pK + 2) ^ 9) ^ 2 * M < LongSide →
      let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed
      let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
      ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group)
        (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)),
      (∀ t ∈ K, ∀ d < r + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
            realificationLieSubalgebra fast) →
      let pull := F.realSymbolHomogeneousPullbackHom b ω hF (fullTaggedVariableWeight J)
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => homogeneousComponent (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
        (fun i => sampledTopPhase_coordinate_homogeneous (fullTaggedVariableWeight J i) (integerSampledRealChart β i))
      ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed) g) →
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast) →
      F.SymbolSlowBound b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => (N i : ℝ)) (Real.exp ((p + 2) ^ a)) El →
      F.SymbolSlowBound b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => (N i : ℝ)) (Real.exp ((p + 2) ^ a)) (pull E) →
      F.SymbolRationalGrid b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l Rl →
      F.SymbolRationalGrid b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) l (pull R) →
      ∀ (Hθ : ℕ) (pLocal : ℝ),
      (∀ i, RationalHeightLE (((eQ.coord j).comp fast.toSubmodule.mkQ)
        (F.associatedGradedBasis b ω hF i)) Hθ) →
      1 ≤ pLocal → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pLocal →
      (Fintype.card ι : ℝ) * Hθ *
        Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
          allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal →
      ((Hθ ^ Fintype.card ι * reset : ℕ) : ℝ) ≤ Real.exp pLocal →
      ∀ score : ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ,
      (∀ i, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (N i : ℝ)) →
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * reset ∧
        ∃ A : ResidueBoxSlice N q,
          IsDenseCommonStrideBox N ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) A.integerPoints ∧
          (𝔼 u : (∀ i, Fin (N i)), score (fun i => ((u i).val : ℤ))) ≤
            (𝔼 u ∈ A.integerPoints, score u) ∧
          ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest
              (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1),
            T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
            (9 / 10 : ℝ) ≤ ‖𝔼 u ∈ A.integerPoints,
              majorPhasePlateauSignal J (r + 1) poly
                (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
                (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                  (lowTaggedVectorRestrict J (r + 1)
                    (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                      fast.toSubmodule (r + 1)
                      (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (origin, v)) *
                star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q u))‖ := by
  let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
    Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
  obtain ⟨reset, hreset, hresetbound, hlreset, hlocal⟩ :=
    (Classical.choose_spec (exists_actual_path_buffered_localMajor_niltest.{0, 0, 0, 0} s a)).2
      (τ := {i : LayerSamplerVariables G I n B // keep i}) (κ := κ)
      F b ω hF H l p hH hl hp hι hτ hκ hHp hlp hbracket N hN
  refine ⟨reset, hreset, hresetbound, hlreset, ?_⟩
  intro r _ _ _ _ hr fast vg hspan hvg η eQ j c origin v sample read hread fixed hfixed
    hσ1 Cgeo hCgeo hchart hsmall hpoly K Bstage pK M LongSide blocks hcertificate
    hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
  dsimp only
  intro g E R hinvariant El Pl Rl hfactor hPl hEl hE hRl hR Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal
  have hβ := allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed
  have hrange := hread.integerFrozenFullChart_certified_top_range B Utag btag hbtag otag S hRad hσ
    poly hm hσ1 c origin v sample read K hcertificate hretained hpK hBpK hJ
    Cgeo hCgeo hchart hM hcap keep hLong hlong hthreshold fixed
  have hbuffer := hread.integerFrozenFullChart_low_residual B Utag btag hbtag otag S hRad hσ poly hm
    hσ1 Cgeo hCgeo hchart hsmall hpoly c origin v sample read keep fixed hfixed (r + 1)
  obtain ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, hcorr⟩ :=
    hlocal hr fast vg hspan hvg J eQ j poly
      (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
      (allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed)
      hβ K hrange g E R hinvariant El Pl Rl hfactor hPl hEl hE hRl hR
      Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal hbuffer
  refine ⟨q, hq, hqbound, A, hAdense, hscore, T, hTnorm, hTcomplexity, ?_⟩
  simpa only [allocatedFrozenIntegerFullChart_spatial] using hcorr

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial _root_.MvPolynomial _root_.OAI.MvPolynomial BooleanCubeKernel
open scoped TensorProduct BigOperators Classical
attribute [local irreducible] weightedAdaptedRealChartHom realPolynomialSymbolHom
  realSymbolHomogeneousPullbackHom

variable {mTag : ℕ} {G X : Type} [Fintype G] [Fintype X] {I Deck J : Fin mTag → Type}
variable [∀ j, Fintype (I j)] [∀ j, Fintype (J j)]
variable {n : Fin mTag → ℕ} (B : LayerSamplerAxis I n → Type) [∀ k, Fintype (B k)]
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (btag : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (Utag j))ᗮ)
variable (hbtag : ∀ j, Submodule.span ℤ (Set.range (btag j)) = projectedIntegerLattice (euclideanSubspace (Utag j)))
variable (otag : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (Utag j)))
variable {Rad σ : Fin mTag → ℝ} (S : LayerSamplerScale (G := G) B Utag btag Rad σ)
variable (hRad : ∀ j, 0 < Rad j) (hσ : ∀ j, 0 < σ j)
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hm : ∀ j d, coefficients (poly j) d ∈ Utag j)

theorem exists_allocated_controlled_frozen_current_grade_local_niltest (s a : ℕ)
    (keep : LayerSamplerVariables G I n B → Prop)
    {ι κ L : Type} [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H lLocal : ℕ) (p : ℝ) (hH : 1 ≤ H) (hlLocal : 0 < lLocal) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p)
    (hτ : (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p)
    (hbracket : ∀ i j z, RationalHeightLE (b.repr ⁅b i, b j⁆ z) H)
    (E R : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    (Nambient : X → ℕ) (hNambient : ∀ i, 0 < Nambient i) {budget : ℝ}
    (hcontrol : FullChartControlledFactors F b ω hF J poly Nambient E R budget)
    (hcommon : Real.exp budget * (lLocal : ℝ) ≤ Real.exp p)
    (hallowance :
      (((s : ℝ) + 1) * ((Fintype.card (X ⊕ (Σ j, J j)) : ℝ) + 1) ^ s *
        Real.exp budget *
        (((mTag + 1 : ℕ) : ℝ) * ((Fintype.card (LayerSamplerVariables G I n B) + 1 : ℕ) : ℝ) ^ mTag) ^ s)
        ≤ Real.exp ((p + 2) ^ a))
    (hN : ∀ i : {i : LayerSamplerVariables G I n B // keep i},
      Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ≤
      ((Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val : ℕ) : ℝ)) :
    ∃ qCurrent : ℕ, 0 < qCurrent ∧ (qCurrent : ℝ) ≤ Real.exp budget ∧
    ∃ reset : ℕ, 0 < reset ∧
      (reset : ℝ) ≤ Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
        allocatedFrozenCurrentGradeResetConstant s a) ∧ qCurrent * lLocal ∣ reset ∧
      ∀ {r : ℕ}
        [TopologicalSpace (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)]
        [T2Space (ℝ ⊗[ℚ] PolynomialTranslationLie.weightedSubalgebra OrdinaryPolynomialPhase.weight r)], r ≤ s →
      ∀ (fast : LieSubalgebra ℚ F.AssociatedGraded)
        (vg : κ → F.PolynomialSymbol (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      Submodule.span ℚ (Set.range vg) =
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast).toSubmodule →
      (∀ i z, RationalHeightLE ((F.polynomialSymbolBasis b ω hF
        (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)).repr (vg i) z) H) →
      ∀ {η : Type} (eQ : Basis η ℚ (F.AssociatedGraded ⧸ fast.toSubmodule)) (j : η)
        (c : ∀ j, Utag j) (origin : X → ℤ)
        (v : Option (LayerSamplerVariables G I n B) × X → ℤ)
        (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
        (read : AllocatedActualCoefficientIndex G X I Deck n B → ℤ),
      AllocatedCenteredFramedRecoveredSampleAt B Utag btag hbtag otag S hRad hσ poly hm c origin v sample read →
      ∀ {τ ξ : ℝ}, 0 < τ → τ ≤ 1 → ξ ≤ 1 →
      v ∈ rectangularWeightIndices 0
        (narrowTrimmedSpatialWidths
          (allocatedPhysicalRootBudget B Utag btag S (fun _ => 0)) τ ξ Nambient) 1 →
      ∀ (fixed : {i : LayerSamplerVariables G I n B // ¬keep i} → ℤ),
      (∀ i, 0 ≤ fixed i ∧ fixed i <
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val) →
      (∀ j, σ j ≤ 1) →
      ∀ (Cgeo : Fin mTag → ℝ), (∀ j, 0 ≤ Cgeo j) →
      (∀ j x, ‖(normalizedOrthogonalChart (euclideanSubspace (Utag j)) (btag j)).symm x‖ ≤ Cgeo j * ‖x‖) →
      (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 / 8) →
      (∀ j, DegreeLE (1 : X → ℕ) (j.val + 1) (poly j)) →
      ∀ (K : Set ((X ⊕ (Σ j, J j)) → ℝ)) (Bstage pK M LongSide : ℝ) (blocks : ℕ),
      RationalTaggedConstraintCertificate J Set.univ K Bstage blocks →
      (∀ t, (∀ j, (fun i => t (Sum.inr ⟨j, i⟩)) ∈ Utag j) → t ∈ K) →
      0 ≤ pK → Bstage ≤ pK → (∀ j, (Fintype.card (J j) : ℝ) ≤ pK) →
      0 ≤ M → (∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ M) →
      1 ≤ LongSide →
      (∀ i, keep i → LongSide ≤ layerSamplerBox B Utag btag S i) →
      Real.exp ((pK + 2) ^ 9) ^ 2 * M < LongSide →
      let β := allocatedFrozenIntegerFullChart B Utag btag otag poly hm c origin v sample keep fixed
      let N := fun i : {i : LayerSamplerVariables G I n B // keep i} =>
        Sum.elim (fun _ : G => S.value) (allocatedPrincipalSides B Utag btag S) i.val
      ∀ (g : (F.realification.adaptedPolynomialFiltration (fullTaggedVariableWeight (X := X) J)).Group),
      (∀ t ∈ K, ∀ d < r + 1,
        F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) d t
          (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord ∈
            realificationLieSubalgebra fast) →
      ∀ (El Pl Rl : F.RealPolynomialSymbolGroup (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)),
      El * Pl * Rl = F.realPolynomialSymbolHom b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (F.weightedAdaptedRealChartHom (fullTaggedVariableWeight J)
          (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
          (integerSampledRealChart β)
          (allocatedFrozenIntegerFullChart_support B Utag btag otag poly hm c origin v sample keep fixed) g) →
      Pl.coord ∈ realificationLieSubalgebra
        (F.symbolPointwiseSubalgebra b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) fast) →
      F.SymbolSlowBound b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
        (fun i => (N i : ℝ)) (Real.exp ((p + 2) ^ a)) El →
      F.SymbolRationalGrid b ω hF (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1) lLocal Rl →
      ∀ (Hθ : ℕ) (pLocal : ℝ),
      (∀ i, RationalHeightLE (((eQ.coord j).comp fast.toSubmodule.mkQ)
        (F.associatedGradedBasis b ω hF i)) Hθ) →
      1 ≤ pLocal → (Fintype.card {i : LayerSamplerVariables G I n B // keep i} : ℝ) ≤ pLocal →
      (Fintype.card ι : ℝ) * Hθ *
        Real.exp ((p + allocatedFrozenCurrentGradeResetConstant s a) ^
          allocatedFrozenCurrentGradeResetConstant s a) ≤ Real.exp pLocal →
      ((Hθ ^ Fintype.card ι * reset : ℕ) : ℝ) ≤ Real.exp pLocal →
      ∀ score : ({i : LayerSamplerVariables G I n B // keep i} → ℤ) → ℝ,
      (∀ i, Real.exp ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) ≤ (N i : ℝ)) →
      ∃ q : ℕ, 0 < q ∧ q ≤ Hθ ^ Fintype.card ι * reset ∧
        ∃ A : ResidueBoxSlice N q,
          IsDenseCommonStrideBox N ((pLocal + (r + 401 : ℕ)) ^ (r + 401)) A.integerPoints ∧
          (𝔼 u : (∀ i, Fin (N i)), score (fun i => ((u i).val : ℤ))) ≤
            (𝔼 u ∈ A.integerPoints, score u) ∧
          ∃ T : (OrdinaryPolynomialPhase.nilmanifold r).Niltest
              (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1),
            T.normBound = 1 ∧ T.ComplexityLE (OrdinaryPolynomialPhase.budget r) ∧
            (9 / 10 : ℝ) ≤ ‖𝔼 u ∈ A.integerPoints,
              majorPhasePlateauSignal J (r + 1) poly
                (fun i => (c (lowTaggedIndex J (r + 1) i).1).val (lowTaggedIndex J (r + 1) i).2)
                (coordinate ((eQ.baseChange ℝ).coord j).toAddMonoidHom
                  (lowTaggedVectorRestrict J (r + 1)
                    (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J)
                      fast.toSubmodule (r + 1)
                      (E⁻¹ * F.realPolynomialSymbolHom b ω hF (fullTaggedVariableWeight J) g * R⁻¹).coord)))
                (jointIntegerPhysicalSite (finiteSplitPoint keep u fixed) (origin, v)) *
                star (T.eval (commonStrideIndex (fun i => (A.start i : ℤ)) q u))‖ := by
  obtain ⟨qCurrent, hqCurrent, hqCurrentBound, hpulls⟩ :=
    hcontrol.exists_allocated_frozen_pullbacks B Utag btag hbtag otag S hRad hσ poly hm
      F b ω hF E R Nambient hNambient hallowance
  have hl : 0 < qCurrent * lLocal := Nat.mul_pos hqCurrent hlLocal
  have hlp : ((qCurrent * lLocal : ℕ) : ℝ) ≤ Real.exp p := by
    rw [Nat.cast_mul]
    exact (mul_le_mul_of_nonneg_right hqCurrentBound (Nat.cast_nonneg lLocal)).trans hcommon
  obtain ⟨reset, hreset, hresetbound, hlreset, hlocal⟩ :=
    exists_allocated_frozen_current_grade_local_niltest B Utag btag hbtag otag S hRad hσ poly hm
      s a keep F b ω hF H (qCurrent * lLocal) p hH hl hp hι hτ hκ hHp hlp hbracket hN
  refine ⟨qCurrent, hqCurrent, hqCurrentBound, reset, hreset, hresetbound, hlreset, ?_⟩
  intro r _ _ _ _ hr fast vg hspan hvg η eQ j c origin v sample read hread
    τ ξ hτpos hτone hξ hv fixed hfixed hσ1 Cgeo hCgeo hchart hsmall hpoly
    K Bstage pK M LongSide blocks hcertificate hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
  dsimp only
  intro g hinvariant El Pl Rl hfactor hPl hEl hRl Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal
  have hsmallOne : ∀ j, Cgeo j * (((Fintype.card (I j) : ℝ) + 1) * Rad j) ≤ 1 :=
    fun j => (hsmall j).trans (by norm_num)
  have hcurrent := hpulls c origin v sample read hread keep fixed
  have hpullR := hcurrent.1 (qCurrent * lLocal) (dvd_mul_right qCurrent lLocal)
  have hpullE := hcurrent.2 hτpos hτone hξ hv hσ1 hpoly Cgeo hCgeo hchart hsmallOne
  have hlocalR := F.symbolRationalGrid_mono b ω hF
    (fun _ : {i : LayerSamplerVariables G I n B // keep i} => 1)
    hlLocal (dvd_mul_left lLocal qCurrent) Rl hRl
  exact hlocal hr fast vg hspan hvg eQ j c origin v sample read hread fixed hfixed
    hσ1 Cgeo hCgeo hchart hsmall hpoly K Bstage pK M LongSide blocks hcertificate
    hretained hpK hBpK hJ hM hcap hLong hlong hthreshold
    g E R hinvariant El Pl Rl hfactor hPl hEl hpullE hlocalR hpullR
    Hθ pLocal hθ hpLocal hdimLocal hMexp hqexp score hNLocal

end Erdos3.NilpotentLieFiltration

end

end OAI
end


