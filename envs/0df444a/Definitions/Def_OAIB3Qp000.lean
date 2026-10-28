-- Prove2me | Definitions.Def_OAIB3Qp000
-- name    : OAIB3Qp000
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-25T15:04:37.422967+00:00
-- url     : https://prove2.me/theorems/ec32b345-dcaf-475d-bb8b-32be0bbf5674
-- title:
--   Definitions bundle OAIB3Qp000 of the split of OpenAI, Squarefree values of quartics and power-free values of polynomials
-- statement:
--   A definitions bundle of the split of OpenAI's proof of `OAI.QuarticPowerFree.allDegrees`, carved from OpenAI's openai/math development (OpenAI, *Squarefree values of quartics and power-free values of polynomials*, OpenAI Math Release, September 24, 2026, result family 20, [github.com/openai/math](https://github.com/openai/math) at commit adc7f12, Apache License 2.0) and ported to Lean 4.33.1 and Mathlib 0df444a. The declarations and their proofs are OpenAI's.
--
--   **Contents.** It holds 474 declarations of OpenAI's Lean: 231 definitions, 6 inductive types or structures, 7 instances and 230 theorems. The definitions and types are `OAI.QuarticPowerFree.ArithmeticModel`, `OAI.QuarticPowerFree.AvoidPrimes`, `OAI.QuarticPowerFree.BlockSample`, `OAI.QuarticPowerFree.ComplexValues.interpolationCramer`, `OAI.QuarticPowerFree.ComplexValues.interpolationHeight`, `OAI.QuarticPowerFree.ComplexValues.interpolationMatrix`, `OAI.QuarticPowerFree.ComplexValues.interpolationRow`, `OAI.QuarticPowerFree.ComplexValues.rationalResultantConstant`, `OAI.QuarticPowerFree.ComplexValues.rationalResultantExponent`, `OAI.QuarticPowerFree.ComplexValues.signedDivisors`, `OAI.QuarticPowerFree.DeterminedInDegree`, `OAI.QuarticPowerFree.EquationLock`, `OAI.QuarticPowerFree.FreeNormalFace`, `OAI.QuarticPowerFree.GoodPatchPiece`, `OAI.QuarticPowerFree.IdealNormal`, `OAI.QuarticPowerFree.IntegerPatch`, `OAI.QuarticPowerFree.IntegerPatch.Bounded`, `OAI.QuarticPowerFree.IntegerPatch.On`, `OAI.QuarticPowerFree.IntegerPatch.goodResidues`, `OAI.QuarticPowerFree.IntegerPatch.minor`, `OAI.QuarticPowerFree.IntegralEmbeddingChart`, `OAI.QuarticPowerFree.IntegralEmbeddingChart.A`, `OAI.QuarticPowerFree.IntegralEmbeddingChart.coord`, `OAI.QuarticPowerFree.KernelGeometry`, `OAI.QuarticPowerFree.KernelParent`, `OAI.QuarticPowerFree.NatTriple`, `OAI.QuarticPowerFree.NormBoxSystem`, `OAI.QuarticPowerFree.NormBoxSystem.a`, `OAI.QuarticPowerFree.NormBoxSystem.equation`, `OAI.QuarticPowerFree.NormBoxSystem.ideal`, `OAI.QuarticPowerFree.PairAffine`, `OAI.QuarticPowerFree.PairBasisIndex`, `OAI.QuarticPowerFree.PairCone`, `OAI.QuarticPowerFree.PairNormal`, `OAI.QuarticPowerFree.PairRing`, `OAI.QuarticPowerFree.PairSector`, `OAI.QuarticPowerFree.PatchPieceCovers`, `OAI.QuarticPowerFree.PhysicalRegular`, `OAI.QuarticPowerFree.PhysicalState`, `OAI.QuarticPowerFree.PointOn` and 197 more.
--
--   **Sources.** They come from these modules of lean/OAI/NumberTheory, in whole or in part: `PowerFree_AdaptiveFibres`, `PowerFree_AdaptiveRanks`, `PowerFree_AffineHilbert`, `PowerFree_BoundedLifts`, `PowerFree_ComplexValues`, `PowerFree_CurveAlternatives`, `PowerFree_CurveThresholds`, `PowerFree_DeformedRoots`, `PowerFree_DegreeBudgets`, `PowerFree_DegreeSchedules`, `PowerFree_EmbeddingCharts`, `PowerFree_GenericCuts`, `PowerFree_HilbertGrowth`, `PowerFree_HilbertSimplex`, `PowerFree_IntegerPatches`, `PowerFree_IntegralKernels`, `PowerFree_Jacobians`, `PowerFree_LaurentCoordinates`, `PowerFree_MediumDegree`, `PowerFree_NormBoxes`, `PowerFree_NormComponents`, `PowerFree_NormHilbert`, `PowerFree_NormalMonomials`, `PowerFree_PairAlgebras`, `PowerFree_PairBoundaries`, `PowerFree_PairCuts`, `PowerFree_PairHilbert`, `PowerFree_PairProjections`, `PowerFree_PatchBounds`, `PowerFree_PointInterpolation`, `PowerFree_PoleCoefficients`, `PowerFree_PositiveCoordinates`, `PowerFree_PrimeBlocks`, `PowerFree_PrimePools`, `PowerFree_PrincipalLifts`, `PowerFree_ProjectionDegrees`, `PowerFree_PureCuts`, `PowerFree_QuarticBoxes`, `PowerFree_QuarticComponents`, `PowerFree_QuarticPairs`, `PowerFree_RadialFibres`, `PowerFree_RegularBlocks`, `PowerFree_ResidueBounds`, `PowerFree_ResidueRelations`, `PowerFree_RootPairHilbert`, `PowerFree_SelectedPrimes`, `PowerFree_Sieve`, `PowerFree_StoppingTrees`, `PowerFree_ThreePoles`, `PowerFree_TwoPoles`, `PowerFree_UnitBalancing`, `PowerFree_WeightedFunctions`, `PowerFree_WeightedHypersurfaces`, `PowerFree_WeightedSlabs`.
--
--   **Imports.** It imports the published bundle `Def_PowerFreeValues`.
--
--   **Imported by** (directly, in this split): the statements `OAI.QuarticPowerFree.medium_degree_dyadic_tail`, `OAI.QuarticPowerFree.norm_generic_threshold_uniform`, `OAI_QuarticPowerFree_norm_indexed_count`, `OAI.QuarticPowerFree.physical_affine_count`, `OAI_QuarticPowerFree_quartic_component_alternatives`, `OAI.QuarticPowerFree.quartic_dyadic_tail`, `OAI.QuarticPowerFree.quartic_generic_threshold_uniform` and `OAI.QuarticPowerFree.quartic_surface_alternatives`; the proofs of `OAI.QuarticPowerFree.allDegrees`, `OAI.QuarticPowerFree.medium_degree_dyadic_tail`, `OAI.QuarticPowerFree.norm_generic_threshold_uniform`, `OAI_QuarticPowerFree_norm_indexed_count`, `OAI.QuarticPowerFree.physical_affine_count`, `OAI_QuarticPowerFree_quartic_component_alternatives`, `OAI.QuarticPowerFree.quartic_dyadic_tail`, `OAI.QuarticPowerFree.quartic_generic_threshold_uniform` and `OAI.QuarticPowerFree.quartic_surface_alternatives`.
-- source:
--   OpenAI, Squarefree values of quartics and power-free values of polynomials, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 20; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Squarefree-values-of-quartics-and-power-free-values-of-polynomials-September-24-2026/manuscript.pdf; Apache License 2.0); definitions carved from lean/OAI/NumberTheory at commit adc7f12

import Mathlib
import Definitions.Def_PowerFreeValues

section
-- module Solutions.OAIB3_Qpf.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
/-- Mathlib's newer `TensorProduct.inductionOn` (no `zero` case: it is the `tmul` case at
`0 ⊗ₜ 0`); ours has only `TensorProduct.induction_on`, which asks for one. Not named
`TensorProduct.inductionOn`: inside `namespace OAI` that would make `open TensorProduct` open
`OAI.TensorProduct` instead of Mathlib's. -/
@[elab_as_elim]
theorem tensorInductionOn {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
    [Module R M] [Module R N] {motive : TensorProduct R M N → Prop} (z : TensorProduct R M N)
    (tmul : ∀ x y, motive (TensorProduct.tmul R x y))
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  TensorProduct.induction_on z (by simpa using tmul 0 0) tmul add
/-- Mathlib's newer case names for `FreeGroup.induction_on` (`one`, where ours says `C1`). -/
@[elab_as_elim]
theorem freeGroupInductionOn {α : Type*} {C : FreeGroup α → Prop} (z : FreeGroup α) (one : C 1)
    (of : ∀ x, C (FreeGroup.of x)) (inv_of : ∀ x, C (FreeGroup.of x) → C (FreeGroup.of x)⁻¹)
    (mul : ∀ x y, C x → C y → C (x * y)) : C z :=
  FreeGroup.induction_on z one of inv_of mul
/-- Mathlib d13f23b's `MvPolynomial.monomial_mul_monomial`; ours is `MvPolynomial.monomial_mul`. -/
theorem _root_.MvPolynomial.monomial_mul_monomial {σ R : Type*} [CommSemiring R] {s s' : σ →₀ ℕ}
    {a b : R} : MvPolynomial.monomial s a * MvPolynomial.monomial s' b =
      MvPolynomial.monomial (s + s') (a * b) := MvPolynomial.monomial_mul
/-- For a measurable equivalence `e`, `IsProbabilityMeasure (μ.map e)` is found by instance search
(Mathlib d13f23b finds it for every map `f`: there `Measure.map` of a non-measurable map is a Dirac
mass, here it is `0`, so only the measurable case can be shimmed). -/
instance isProbabilityMeasure_map_measurableEquiv {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : MeasureTheory.Measure α} [MeasureTheory.IsProbabilityMeasure μ]
    (e : α ≃ᵐ β) : MeasureTheory.IsProbabilityMeasure (μ.map e) :=
  MeasureTheory.Measure.isProbabilityMeasure_map e.measurable.aemeasurable
end OAICompat434

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_Sieve
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Filter Asymptotics
open scoped Topology
namespace QuarticPowerFree

open Polynomial

open scoped BigOperators Count

def AvoidPrimes (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) (n : ℕ) : Prop :=
  ∀ p ∈ s, ¬(p.val : ℤ) ^ k ∣ f.eval (n : ℤ)

instance instDecidablePredNatAvoidPrimes (f : Polynomial ℤ) (k : ℕ) (s : Finset Nat.Primes) :
    DecidablePred (AvoidPrimes f k s) :=
  fun n => inferInstanceAs (Decidable (∀ p ∈ s, ¬(p.val : ℤ) ^ k ∣ f.eval (n : ℤ)))

def primesUpTo (N : ℕ) : Finset Nat.Primes := (Nat.primesLE N).subtype Nat.Prime

@[simp] theorem mem_primesUpTo {N : ℕ} {p : Nat.Primes} :
    p ∈ primesUpTo N ↔ p.val ≤ N := by
  exact (Finset.mem_subtype (p := Nat.Prime) (s := Nat.primesLE N)
    (a := ⟨p.val, p.property⟩)).trans ((Nat.mem_primesLE).trans (and_iff_left p.property))

noncomputable def natCount (f : Polynomial ℤ) (k N : ℕ) : ℕ := by
  classical
  exact Nat.count (fun n : ℕ => PowerFree k (f.eval (n : ℤ))) N

noncomputable def tailCount (f : Polynomial ℤ) (k N : ℕ) : ℕ := by
  classical
  exact Nat.count (fun n : ℕ => ∃ p : ℕ, p.Prime ∧ N < p ∧
    (p : ℤ) ^ k ∣ f.eval (n : ℤ)) N

noncomputable def dyadicTailCount (f : Polynomial ℤ) (k M : ℕ) : ℕ := by
  classical
  exact ((Finset.Ioc M (2 * M)).filter fun n : ℕ =>
    ∃ p : ℕ, p.Prime ∧ M < p ∧ (p : ℤ)^k ∣ f.eval (n : ℤ)).card

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormalMonomials
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial Finsupp MonomialOrder
open scoped MonomialOrder

variable {σ K : Type*} [Field K]

def IdealNormal (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (d : σ →₀ ℕ) : Prop :=
  ∀ p ∈ I, p ≠ 0 → ¬ m.degree p ≤ d

theorem ideal_normal_form (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) :
    ∃ r : MvPolynomial σ K, p-r ∈ I ∧
      (∀ d ∈ r.support, IdealNormal m I d) ∧ m.degree r ≼[m] m.degree p := by
  classical
  let b : {q : MvPolynomial σ K // q ∈ I ∧ q ≠ 0} → MvPolynomial σ K := Subtype.val
  have hb : ∀ i, IsUnit (m.leadingCoeff (b i)) := by
    intro i
    apply isUnit_iff_ne_zero.mpr
    exact m.leadingCoeff_ne_zero_iff.mpr i.property.2
  obtain ⟨g, r, hpr, hdeg, hr⟩ := m.div hb p
  have hg : Finsupp.linearCombination _ b g ∈ I := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ i.property.1
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [hpr, add_sub_cancel_right]; exact hg
  · intro d hd q hq hq0
    exact hr d hd ⟨q, hq, hq0⟩
  · have hlin : m.degree (Finsupp.linearCombination _ b g) ≼[m] m.degree p := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply m.degree_sum_le.trans
      apply Finset.sup_le
      intro i _
      simpa [smul_eq_mul, mul_comm] using hdeg i
    have heq : r = p - Finsupp.linearCombination _ b g := by rw [hpr]; ring
    rw [heq]
    exact (m.degree_sub_le).trans (max_le le_rfl hlin)

theorem ideal_normal_injective (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (p : MvPolynomial σ K) (hp : ∀ d ∈ p.support, IdealNormal m I d)
    (hI : p ∈ I) : p = 0 := by
  by_contra hp0
  exact hp _ (m.degree_mem_support hp0) p hI hp0 le_rfl

theorem ideal_normal_finite_obstructions [Finite σ] (m : MonomialOrder σ)
    (I : Ideal (MvPolynomial σ K)) :
    ∃ s : Finset (σ →₀ ℕ),
      (∀ d ∈ s, ∃ p ∈ I, p ≠ 0 ∧ m.degree p = d) ∧
      ∀ d, IdealNormal m I d ↔ ∀ a ∈ s, ¬ a ≤ d := by
  classical
  let D : Set (σ →₀ ℕ) := {d | ∃ p ∈ I, p ≠ 0 ∧ m.degree p = d}
  have hf : {a | Minimal (· ∈ D) a}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain _)
  refine ⟨hf.toFinset, ?_, ?_⟩
  · intro d hd
    exact (hf.mem_toFinset.mp hd).1
  · intro d
    constructor
    · intro hn a ha had
      obtain ⟨p, hp, hp0, he⟩ := (hf.mem_toFinset.mp ha).1
      exact hn p hp hp0 (he ▸ had)
    · intro hn p hp hp0 hpd
      have hpD : m.degree p ∈ D := ⟨p, hp, hp0, rfl⟩
      obtain ⟨a, hap, ha⟩ := (show D.IsPWO from Set.isPWO_of_wellQuasiOrderedLE D).exists_le_minimal hpD
      exact hn a (hf.mem_toFinset.mpr ha) (hap.trans hpd)

noncomputable def totalSpace (T : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {d | d.degree ≤ T}

@[simp] theorem mem_totalSpace {T : ℕ} {p : MvPolynomial σ K} :
    p ∈ totalSpace T ↔ p.totalDegree ≤ T := by
  simp only [totalSpace, mem_restrictSupport_iff, totalDegree, Finset.sup_le_iff]
  rfl

noncomputable def normalTotalSpace (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (T : ℕ) : Submodule K (MvPolynomial σ K) :=
  restrictSupport K {d | IdealNormal m I d ∧ d.degree ≤ T}

theorem normalTotalSpace_le (m : MonomialOrder σ) (I : Ideal (MvPolynomial σ K))
    (T : ℕ) : normalTotalSpace m I T ≤ totalSpace T := by
  intro p hp d hd
  exact (hp hd).2

theorem totalSpace_image_normal [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (T : ℕ) :
    (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap =
      (normalTotalSpace degLex I T).map (Ideal.Quotient.mkₐ K I).toLinearMap := by
  apply le_antisymm
  · rintro y ⟨p, hp, rfl⟩
    obtain ⟨r, hr, hn, hd⟩ := ideal_normal_form degLex I p
    refine ⟨r, ?_, ?_⟩
    · intro d hdr
      refine ⟨hn d hdr, ?_⟩
      exact (le_totalDegree hdr).trans
        ((degLex_totalDegree_monotone hd).trans (mem_totalSpace.mp hp))
    · apply Ideal.Quotient.eq.mpr
      simpa only [neg_sub] using I.neg_mem hr
  · exact Submodule.map_mono (normalTotalSpace_le _ _ _)

theorem coordinate_hilbert_count [LinearOrder σ] [WellFoundedGT σ]
    (I : Ideal (MvPolynomial σ K)) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
      Nat.card {d : σ →₀ ℕ // IdealNormal degLex I d ∧ d.degree ≤ T} := by
  rw [totalSpace_image_normal]
  let M := normalTotalSpace degLex I T
  let f := (Ideal.Quotient.mkₐ K I).toLinearMap.domRestrict M
  have hf : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    apply Subtype.ext
    exact ideal_normal_injective degLex I p.val (fun d hd => (p.property hd).1)
      (Ideal.Quotient.eq_zero_iff_mem.mp hp)
  have heq : LinearMap.range f = M.map (Ideal.Quotient.mkₐ K I).toLinearMap :=
    LinearMap.range_domRestrict _ _
  rw [← heq, LinearMap.finrank_range_of_inj hf]
  exact Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)

open scoped BigOperators

noncomputable def simplexTuple (h N : ℕ) : Finset (Fin h → ℕ) :=
  (Finset.range (N+1)).biUnion (Finset.Nat.antidiagonalTuple h)

@[simp] theorem mem_simplexTuple {h N : ℕ} (x : Fin h → ℕ) :
    x ∈ simplexTuple h N ↔ ∑ i, x i ≤ N := by
  classical
  simp only [simplexTuple, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro hx; exact ⟨_, by omega, rfl⟩

theorem card_antidiagonalTuple (h N : ℕ) :
    (Finset.Nat.antidiagonalTuple h N).card = h.multichoose N := by
  classical
  have hc := Finset.card_finsuppAntidiag_nat_eq_multichoose
    (s := (Finset.univ : Finset (Fin h))) N
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  apply Finset.card_bij (fun x _ => Finsupp.equivFunOnFinite.symm x)
  · intro x hx
    rw [Finset.mem_finsuppAntidiag']
    exact ⟨by simpa [Finsupp.sum_fintype] using Finset.Nat.mem_antidiagonalTuple.mp hx,
      Finset.subset_univ _⟩
  · intro x _ y _ he
    exact Finsupp.equivFunOnFinite.symm.injective he
  · intro x hx
    refine ⟨Finsupp.equivFunOnFinite x, ?_, by simp⟩
    rw [Finset.Nat.mem_antidiagonalTuple]
    simpa [Finsupp.sum_fintype] using (Finset.mem_finsuppAntidiag'.mp hx).1

theorem card_simplexTuple (h N : ℕ) :
    (simplexTuple h N).card = (N+h).choose h := by
  classical
  rw [simplexTuple, Finset.card_biUnion]
  · simp_rw [card_antidiagonalTuple]
    exact Nat.sum_range_multichoose N h
  · intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro x hi hj
    exact hij ((Finset.Nat.mem_antidiagonalTuple.mp hi).symm.trans
      (Finset.Nat.mem_antidiagonalTuple.mp hj))

noncomputable def simplexExponents (n T : ℕ) : Finset (Fin n →₀ ℕ) :=
  (simplexTuple n T).map Finsupp.equivFunOnFinite.symm.toEmbedding

@[simp] theorem mem_simplexExponents {n T : ℕ} (d : Fin n →₀ ℕ) :
    d ∈ simplexExponents n T ↔ d.degree ≤ T := by
  classical
  simp only [simplexExponents, Finset.mem_map_equiv, mem_simplexTuple]
  change (∑ i, d i) ≤ T ↔ (d.sum fun _ e => e) ≤ T
  rw [Finsupp.sum_fintype]
  intro i; rfl

@[simp] theorem card_simplexExponents (n T : ℕ) :
    (simplexExponents n T).card = (T+n).choose n := by
  rw [simplexExponents, Finset.card_map, card_simplexTuple]

noncomputable def normalExponents {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (T : ℕ) :
    Finset (Fin n →₀ ℕ) := by
  classical
  exact (simplexExponents n T).filter (fun d => ∀ a ∈ s, ¬ a ≤ d)

@[simp] theorem mem_normalExponents {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (T : ℕ)
    (d : Fin n →₀ ℕ) :
    d ∈ normalExponents s T ↔ d.degree ≤ T ∧ ∀ a ∈ s, ¬ a ≤ d := by
  classical
  simp [normalExponents]

@[simp] theorem normalExponents_empty (n T : ℕ) :
    normalExponents (∅ : Finset (Fin n →₀ ℕ)) T = simplexExponents n T := by
  classical
  ext; simp

noncomputable def colonMonomials {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) : Finset (Fin n →₀ ℕ) := by
  classical
  exact s.image (fun b => b-a)

theorem colonMonomials_card_le {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) : (colonMonomials a s).card ≤ s.card := by
  classical
  exact Finset.card_image_le

theorem finsupp_tsub_le_iff {n : ℕ} (a b d : Fin n →₀ ℕ) :
    b-a ≤ d ↔ b ≤ a+d := by
  simp only [Finsupp.le_def, Finsupp.tsub_apply, Finsupp.add_apply]
  constructor
  · intro h i; have := h i; omega
  · intro h i; have := h i; omega

theorem normalExponents_card_insert {n : ℕ} (a : Fin n →₀ ℕ)
    (s : Finset (Fin n →₀ ℕ)) (T : ℕ) (ha : a.degree ≤ T) :
    (normalExponents (insert a s) T).card +
      (normalExponents (colonMonomials a s) (T-a.degree)).card =
        (normalExponents s T).card := by
  classical
  have hs : normalExponents (insert a s) T =
      (normalExponents s T).filter (fun d => ¬ a ≤ d) := by
    ext d; simp [and_left_comm, and_comm]
  have hc : ((normalExponents s T).filter (a ≤ ·)).card =
      (normalExponents (colonMonomials a s) (T-a.degree)).card := by
    symm
    apply Finset.card_bij (fun d _ => a+d)
    · intro d hd
      obtain ⟨hdT, hdS⟩ := (mem_normalExponents _ _ d).mp hd
      apply Finset.mem_filter.mpr
      refine ⟨(mem_normalExponents _ _ _).mpr ⟨?_, ?_⟩, le_add_right le_rfl⟩
      · rw [map_add]; omega
      · intro b hb hbad
        exact hdS (b-a) (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
          ((finsupp_tsub_le_iff a b d).mpr hbad)
    · intro d _ e _ h; exact add_left_cancel h
    · intro d hd
      obtain ⟨hdS, had⟩ := Finset.mem_filter.mp hd
      obtain ⟨hdT, hdN⟩ := (mem_normalExponents _ _ d).mp hdS
      refine ⟨d-a, (mem_normalExponents _ _ _).mpr ⟨?_, ?_⟩,
        add_tsub_cancel_of_le had⟩
      · have he := congrArg Finsupp.degree (add_tsub_cancel_of_le had)
        simp only [map_add] at he
        omega
      · intro b hb hbd
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
        apply hdN c hc
        have h := (finsupp_tsub_le_iff a c (d-a)).mp hbd
        simpa only [add_tsub_cancel_of_le had] using h
  rw [hs, ← hc, add_comm]
  exact Finset.card_filter_add_card_filter_not _

theorem normalExponents_eventually_polynomial {n : ℕ} (s : Finset (Fin n →₀ ℕ)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      ((normalExponents s T).card : ℚ) = P.eval (T : ℚ) := by
  classical
  suffices H : ∀ N, ∀ s : Finset (Fin n →₀ ℕ), s.card = N →
      ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
        ((normalExponents s T).card : ℚ) = P.eval (T : ℚ) by
    exact H s.card s rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro s hs
    by_cases he : s = ∅
    · subst s
      refine ⟨Polynomial.preHilbertPoly ℚ n 0,
        (Polynomial.natDegree_preHilbertPoly _ _ _).le, 0, ?_⟩
      intro T _
      rw [normalExponents_empty, card_simplexExponents,
        Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
      simp
    · obtain ⟨a, ha⟩ := Finset.nonempty_iff_ne_empty.mpr he
      let s' := s.erase a
      have ht : s'.card < N := by rw [← hs]; exact Finset.card_erase_lt_of_mem ha
      obtain ⟨P, hP, TP, hPT⟩ := ih s'.card ht s' rfl
      obtain ⟨Q, hQ, TQ, hQT⟩ := ih (colonMonomials a s').card
        ((colonMonomials_card_le _ _).trans_lt ht) _ rfl
      refine ⟨P - Q.comp (Polynomial.X - Polynomial.C (a.degree : ℚ)), ?_,
        max TP (TQ+a.degree), ?_⟩
      · apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le hP
        rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]
        exact hQ
      · intro T hT
        have hTP : TP ≤ T := (le_max_left _ _).trans hT
        have hTQ : TQ+a.degree ≤ T := (le_max_right _ _).trans hT
        have haT : a.degree ≤ T := by omega
        have hh := normalExponents_card_insert a s' T haT
        rw [show insert a s' = s from Finset.insert_erase ha] at hh
        have hhQ : ((normalExponents s T).card : ℚ) +
            ((normalExponents (colonMonomials a s') (T-a.degree)).card : ℚ) =
              ((normalExponents s' T).card : ℚ) := by exact_mod_cast hh
        rw [hPT T hTP, hQT (T-a.degree) (by omega)] at hhQ
        rw [Polynomial.eval_sub, Polynomial.eval_comp, Polynomial.eval_sub,
          Polynomial.eval_X, Polynomial.eval_C]
        rw [Nat.cast_sub haT] at hhQ
        linarith

theorem coordinate_hilbert_eventually_polynomial {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧ ∃ T₀ : ℕ, ∀ T ≥ T₀,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ) := by
  classical
  obtain ⟨s, _, hs⟩ := ideal_normal_finite_obstructions degLex I
  have hc (T : ℕ) :
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
        (normalExponents s T).card := by
    rw [coordinate_hilbert_count, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, hs, and_comm]
  obtain ⟨P, hP, T₀, hT⟩ := normalExponents_eventually_polynomial s
  refine ⟨P, hP, T₀, ?_⟩
  intro T h
  rw [hc]
  exact hT T h

theorem idealNormal_span_singleton (m : MonomialOrder σ)
    (p : MvPolynomial σ K) (hp : p ≠ 0) (d : σ →₀ ℕ) :
    IdealNormal m (Ideal.span {p}) d ↔ ¬ m.degree p ≤ d := by
  constructor
  · intro h
    exact h p (Ideal.subset_span (Set.mem_singleton p)) hp
  · intro h q hq hq0 hqd
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton.mp hq
    have hr : r ≠ 0 := by intro he; simp [he] at hq0
    rw [m.degree_mul hp hr] at hqd
    exact h ((_root_.le_add_right le_rfl).trans hqd)

theorem hypersurface_hilbert_count {n : ℕ} (p : MvPolynomial (Fin n) K)
    (hp : p ≠ 0) (T : ℕ) (hT : p.totalDegree ≤ T) :
    Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) +
        (T-p.totalDegree+n).choose n = (T+n).choose n := by
  classical
  have hc : Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) =
      (normalExponents {degLex.degree p} T).card := by
    rw [coordinate_hilbert_count, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, idealNormal_span_singleton degLex p hp,
      Finset.mem_singleton, forall_eq, and_comm]
  rw [hc]
  have hh := normalExponents_card_insert (degLex.degree p) ∅ T
    (by simpa only [degree_degLexDegree] using hT)
  simpa [colonMonomials, degree_degLexDegree] using hh

theorem binomial_difference_sum (n e T : ℕ) (he : e ≤ T) :
    (T-e+(n+1)).choose (n+1) +
      ∑ j ∈ Finset.range e, (T-j+n).choose n =
        (T+(n+1)).choose (n+1) := by
  induction e with
  | zero => simp
  | succ e ih =>
    rw [Finset.sum_range_succ]
    have hi := ih (by omega)
    have hE : T-e+n = (T-(e+1)+(n+1)) := by omega
    have hE' : T-e+(n+1) = (T-e+n)+1 := by omega
    have hb := Nat.choose_succ_succ (T-e+n) n
    change (T-e+n+1).choose (n+1) = (T-e+n).choose n + (T-e+n).choose (n+1) at hb
    rw [← hE'] at hb
    rw [← hE]
    omega

noncomputable def hypersurfaceHilbertPolynomial (n e : ℕ) : Polynomial ℚ :=
  ∑ j ∈ Finset.range e, Polynomial.preHilbertPoly ℚ n j

theorem hypersurfaceHilbertPolynomial_coeff (n e : ℕ) :
    (hypersurfaceHilbertPolynomial n e).coeff n = (e : ℚ)/(n.factorial : ℚ) := by
  simp [hypersurfaceHilbertPolynomial, Polynomial.coeff_preHilbertPoly_self, div_eq_mul_inv]

theorem hypersurfaceHilbertPolynomial_degree (n e : ℕ) :
    (hypersurfaceHilbertPolynomial n e).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j _
  exact (Polynomial.natDegree_preHilbertPoly _ _ _).le

theorem hypersurface_hilbert_polynomial {n : ℕ} (p : MvPolynomial (Fin (n+1)) K)
    (hp : p ≠ 0) (T : ℕ) (hT : p.totalDegree ≤ T) :
    (Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) : ℚ) =
        (hypersurfaceHilbertPolynomial n p.totalDegree).eval (T : ℚ) := by
  have hh := hypersurface_hilbert_count p hp T hT
  have hb := binomial_difference_sum n p.totalDegree T hT
  have he : Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (Ideal.span {p})).toLinearMap) =
        ∑ j ∈ Finset.range p.totalDegree, (T-j+n).choose n := by omega
  rw [he, Nat.cast_sum]
  simp only [hypersurfaceHilbertPolynomial, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ ((Finset.mem_range.mp hj).le.trans hT)]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HilbertGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Polynomial Filter
open scoped Topology

theorem leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (P : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in atTop, 0 ≤ P.eval (T : ℚ)) : 0 ≤ P.leadingCoeff := by
  by_cases hd : P.natDegree = 0
  · rw [eq_C_of_natDegree_eq_zero hd] at hP ⊢
    simpa only [eval_C, leadingCoeff_C, eventually_const] using hP
  · by_contra hl
    have ht := (P.tendsto_atBot_of_leadingCoeff_nonpos
      (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd)) (le_of_not_ge hl)).comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun T : ℕ => (T : ℚ)) atTop atTop)
    have hn := ht.eventually_lt_atBot 0
    obtain ⟨T, hT, hT'⟩ := (hP.and hn).exists
    exact (not_lt_of_ge hT) hT'

theorem coeff_le_of_eventually_nat_eval_le (P Q : Polynomial ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h) (hQ : Q.natDegree ≤ h)
    (hle : ∀ᶠ T : ℕ in atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ)) :
    P.coeff h ≤ Q.coeff h := by
  have hn : 0 ≤ (Q-P).leadingCoeff :=
    leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (Q-P)
      (hle.mono (fun T hT => by simpa only [eval_sub, sub_nonneg] using hT))
  have hd : (Q-P).natDegree ≤ h := (natDegree_sub_le _ _).trans (max_le hQ hP)
  have hc : 0 ≤ (Q-P).coeff h := by
    rcases hd.eq_or_lt with he | he
    · simpa only [← he, coeff_natDegree] using hn
    · rw [coeff_eq_zero_of_natDegree_lt he]
  simpa only [coeff_sub, sub_nonneg] using hc

theorem natDegree_le_of_eventually_nat_eval_bounds (P Q : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in atTop, 0 ≤ P.eval (T : ℚ))
    (hle : ∀ᶠ T : ℕ in atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ)) :
    P.natDegree ≤ Q.natDegree := by
  by_contra hh
  have hdeg : Q.natDegree < P.natDegree := lt_of_not_ge hh
  have hP0 : P ≠ 0 := by intro he; simp [he] at hdeg
  have hl : 0 < P.leadingCoeff := lt_of_le_of_ne
    (leadingCoeff_nonneg_of_eventually_nat_eval_nonneg P hP)
    (Ne.symm (leadingCoeff_ne_zero.mpr hP0))
  have hm := leadingCoeff_nonneg_of_eventually_nat_eval_nonneg (Q-P)
    (hle.mono (fun T hT => by simpa only [eval_sub, sub_nonneg] using hT))
  rw [leadingCoeff_sub_of_degree_lt' (degree_lt_degree hdeg)] at hm
  linarith

end

open MvPolynomial Finsupp MonomialOrder
open scoped MonomialOrder BigOperators

def FreeNormalFace {n : ℕ} (s : Finset (Fin n →₀ ℕ)) (J : Finset (Fin n)) : Prop :=
  ∀ a ∈ s, ¬ a.support ⊆ J

theorem normal_of_free_face {n : ℕ} {s : Finset (Fin n →₀ ℕ)}
    {J : Finset (Fin n)} (hJ : FreeNormalFace s J)
    (d : Fin n →₀ ℕ) (hd : d.support ⊆ J) : ∀ a ∈ s, ¬ a ≤ d := by
  intro a ha had
  apply hJ a ha
  intro i hi
  apply hd
  apply Finsupp.mem_support_iff.mpr
  have hai : a i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have hh := had i
  omega

theorem large_coordinates_free {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (B : ℕ) (hB : ∀ a ∈ s, a.degree < B)
    (d : Fin n →₀ ℕ) (hd : ∀ a ∈ s, ¬ a ≤ d) :
    FreeNormalFace s (Finset.univ.filter (fun i => B ≤ d i)) := by
  classical
  intro a ha hsub
  apply hd a ha
  intro i
  by_cases hi : i ∈ a.support
  · have hh : B ≤ d i := (Finset.mem_filter.mp (hsub hi)).2
    exact ((Finsupp.le_degree i a).trans (hB a ha).le).trans hh
  · simpa only [Finsupp.notMem_support_iff.mp hi] using Nat.zero_le (d i)

theorem free_face_algebraicIndependent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ d, IdealNormal degLex I d ↔ ∀ a ∈ s, ¬ a ≤ d)
    (J : Finset (Fin n)) (hJ : FreeNormalFace s J) :
    AlgebraicIndependent K (fun j : J => Ideal.Quotient.mk I (X j.val)) := by
  classical
  let f := (Ideal.Quotient.mkₐ K I).comp (rename (fun j : J => j.val))
  have he : MvPolynomial.aeval (fun j : J => Ideal.Quotient.mk I (X j.val)) = f := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [f]
  rw [algebraicIndependent_iff_injective_aeval, he]
  intro p q hpq
  apply sub_eq_zero.mp
  apply (rename_injective (fun j : J => j.val) Subtype.val_injective)
  rw [map_zero]
  apply ideal_normal_injective degLex I
  · intro d hd
    apply (hs d).mpr
    apply normal_of_free_face hJ
    intro i hi
    have hv := support_subset_vars_of_mem_support hd hi
    have hr := vars_rename (fun j : J => j.val) (p-q) hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
    exact j.property
  · apply Ideal.Quotient.eq_zero_iff_mem.mp
    change f (p-q) = 0
    rw [map_sub, hpq, sub_self]

noncomputable def partialCoordinateBox {n : ℕ} (B T : ℕ) (J : Finset (Fin n)) :
    Finset (Fin n → ℕ) := by
  classical
  exact Fintype.piFinset (fun i => Finset.range (if i ∈ J then T+1 else B))

theorem card_partialCoordinateBox_le {n : ℕ} (B T h : ℕ) (hB : 1 ≤ B)
    (J : Finset (Fin n)) (hJ : J.card ≤ h) :
    (partialCoordinateBox B T J).card ≤ B^n * (T+1)^h := by
  classical
  rw [partialCoordinateBox, Fintype.card_piFinset]
  simp only [Finset.card_range]
  rw [Finset.prod_ite]
  have he : (Finset.univ.filter (fun i : Fin n => i ∈ J)) = J := by ext; simp
  rw [he]
  simp only [Finset.prod_const]
  have hc : (Finset.univ.filter (fun i : Fin n => i ∉ J)).card ≤ n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    (T+1)^J.card * B^(Finset.univ.filter (fun i : Fin n => i ∉ J)).card ≤
        (T+1)^h * B^n := Nat.mul_le_mul
          (Nat.pow_le_pow_right (by omega) hJ) (Nat.pow_le_pow_right hB hc)
    _ = B^n * (T+1)^h := Nat.mul_comm _ _

theorem normalExponents_card_growth {n : ℕ} (s : Finset (Fin n →₀ ℕ))
    (h : ℕ) (hh : ∀ J, FreeNormalFace s J → J.card ≤ h) (T : ℕ) :
    (normalExponents s T).card ≤
      (2^n * (s.sup Finsupp.degree + 1)^n) * (T+1)^h := by
  classical
  let B := s.sup Finsupp.degree + 1
  let faces := (Finset.univ : Finset (Fin n)).powerset.filter (fun J => J.card ≤ h)
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hBs : ∀ a ∈ s, a.degree < B := by
    intro a ha
    exact Nat.lt_succ_of_le (Finset.le_sup (f := Finsupp.degree) ha)
  have hc : (normalExponents s T).image (fun d : Fin n →₀ ℕ => (d : Fin n → ℕ)) ⊆
      faces.biUnion (partialCoordinateBox B T) := by
    intro d hd
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hd
    have ha' := mem_normalExponents s T a |>.mp ha
    let J := Finset.univ.filter (fun i => B ≤ a i)
    refine Finset.mem_biUnion.mpr ⟨J, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
        hh J (large_coordinates_free s B hBs a ha'.2)⟩
    · rw [partialCoordinateBox, Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_range]
      by_cases hi : i ∈ J
      · rw [ite_eq_left hi]
        exact Nat.lt_succ_of_le ((Finsupp.le_degree i a).trans ha'.1)
      · rw [ite_eq_right hi]
        have hh : ¬ B ≤ a i := by simpa [J] using hi
        omega
  have hf : faces.card ≤ 2^n := by
    exact (Finset.card_filter_le _ _).trans (by simp)
  calc
    (normalExponents s T).card =
      ((normalExponents s T).image (fun d : Fin n →₀ ℕ => (d : Fin n → ℕ))).card :=
        (Finset.card_image_of_injective _ (fun p q h => Finsupp.ext (fun i => congrFun h i))).symm
    _ ≤ (faces.biUnion (partialCoordinateBox B T)).card := Finset.card_le_card hc
    _ ≤ ∑ J ∈ faces, (partialCoordinateBox B T J).card := Finset.card_biUnion_le
    _ ≤ faces.card * (B^n * (T+1)^h) := by
      simpa only [nsmul_eq_mul, Nat.cast_id] using Finset.sum_le_card_nsmul faces
        (fun J => (partialCoordinateBox B T J).card) (B^n * (T+1)^h)
        (fun J hJ => card_partialCoordinateBox_le B T h hB J (Finset.mem_filter.mp hJ).2)
    _ ≤ 2^n * (B^n * (T+1)^h) := Nat.mul_le_mul_right _ hf
    _ = (2^n * (s.sup Finsupp.degree+1)^n) * (T+1)^h := by rw [Nat.mul_assoc]

theorem totalSpace_finite {n : ℕ} {K : Type*} [Field K] (T : ℕ) :
    Module.Finite K (totalSpace (σ := Fin n) (K := K) T) := by
  classical
  let e : {d : Fin n →₀ ℕ // d.degree ≤ T} ≃ {d // d ∈ simplexExponents n T} :=
    Equiv.subtypeEquivRight (fun d => (mem_simplexExponents d).symm)
  let : Finite {d : Fin n →₀ ℕ | d.degree ≤ T} :=
    Finite.of_equiv {d // d ∈ simplexExponents n T} e.symm
  exact Module.Finite.of_basis (basisRestrictSupport K {d : Fin n →₀ ℕ | d.degree ≤ T})

theorem totalSpace_finrank {n : ℕ} {K : Type*} [Field K] (T : ℕ) :
    Module.finrank K (totalSpace (σ := Fin n) (K := K) T) = (T+n).choose n := by
  change Module.finrank K (restrictSupport K {d : Fin n →₀ ℕ | d.degree ≤ T}) = _
  rw [Module.finrank_eq_nat_card_basis (basisRestrictSupport K _)]
  rw [← card_simplexExponents n T, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun d => (mem_simplexExponents d).symm)

theorem independent_coordinates_hilbert_lower {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a)))) (T : ℕ) :
    (T+h).choose h ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := totalSpace_finite (n := n) (K := K) T
  let f := (Ideal.Quotient.mkₐ K I).comp (rename j)
  have hf : Function.Injective f := by
    rw [algebraicIndependent_iff_injective_aeval] at hj
    have he : MvPolynomial.aeval (fun a => Ideal.Quotient.mk I (X (j a))) = f := by
      apply algHom_ext
      intro a
      simp [f]
    rwa [he] at hj
  let g : totalSpace (σ := Fin h) (K := K) T →ₗ[K]
      (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap :=
    (f.toLinearMap.domRestrict (totalSpace T)).codRestrict _ (by
      intro p
      exact ⟨rename j p.val,
        mem_totalSpace.mpr ((totalDegree_rename_le j p.val).trans (mem_totalSpace.mp p.property)),
        rfl⟩)
  have hg : Function.Injective g := by
    intro p q he
    exact Subtype.ext (hf (congrArg Subtype.val he))
  rw [← totalSpace_finrank (K := K) (n := h) T]
  exact LinearMap.finrank_le_finrank_of_injective hg

theorem empty_free_face_of_proper {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤)
    (s : Finset (Fin n →₀ ℕ))
    (hs : ∀ d ∈ s, ∃ p ∈ I, p ≠ 0 ∧ degLex.degree p = d) :
    FreeNormalFace s ∅ := by
  classical
  intro a ha hh
  have ha0 : a = 0 := Finsupp.support_eq_empty.mp (Finset.subset_empty.mp hh)
  obtain ⟨p, hp, hp0, hd⟩ := hs a ha
  have he := (degLex.degree_eq_zero_iff (f := p)).mp (hd.trans ha0)
  have hu : IsUnit (degLex.leadingCoeff p) := isUnit_iff_ne_zero.mpr
    (degLex.leadingCoeff_ne_zero_iff.mpr hp0)
  exact hI (I.eq_top_of_isUnit_mem hp (he ▸ hu.map C))

theorem coordinate_hilbert_degree_independent {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) :
    ∃ P : Polynomial ℚ, ∃ j : Fin P.natDegree → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) ∧
      (P.natDegree.factorial : ℚ)⁻¹ ≤ P.coeff P.natDegree ∧
      ∃ T₀ : ℕ, ∀ T ≥ T₀,
        (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
          P.eval (T : ℚ) := by
  classical
  obtain ⟨s, hsI, hs⟩ := ideal_normal_finite_obstructions degLex I
  let faces := (Finset.univ : Finset (Fin n)).powerset.filter (FreeNormalFace s)
  have hne : faces.Nonempty := by
    refine ⟨∅, Finset.mem_filter.mpr ⟨?_, empty_free_face_of_proper I hI s hsI⟩⟩
    exact Finset.mem_powerset.mpr (Finset.empty_subset _)
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image faces Finset.card hne
  have hfree : FreeNormalFace s J := (Finset.mem_filter.mp hJ).2
  have hmax' (J' : Finset (Fin n)) (hJ' : FreeNormalFace s J') : J'.card ≤ J.card :=
    hmax J' (Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hJ'⟩)
  let j : Fin J.card → Fin n := fun a => ((Finset.equivFin J).symm a).val
  have hj : Function.Injective j := Subtype.val_injective.comp (Finset.equivFin J).symm.injective
  have hind : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) :=
    (free_face_algebraicIndependent I s hs J hfree).comp _ (Finset.equivFin J).symm.injective
  obtain ⟨P, _, T₀, hT⟩ := coordinate_hilbert_eventually_polynomial I
  have hcount (T : ℕ) :
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) =
        (normalExponents s T).card := by
    rw [coordinate_hilbert_count, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro d
    simp only [mem_normalExponents, hs, and_comm]
  let c := 2^n * (s.sup Finsupp.degree+1)^n
  let Q : Polynomial ℚ := Polynomial.C (c : ℚ) *
    (Polynomial.X + Polynomial.C 1)^J.card
  have hPnonneg : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h]
    positivity
  have hPQ : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) ≤ Q.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h, hcount]
    simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_add, Polynomial.eval_X]
    exact_mod_cast normalExponents_card_growth s J.card hmax' T
  have hupper : P.natDegree ≤ J.card := by
    apply (natDegree_le_of_eventually_nat_eval_bounds P Q hPnonneg hPQ).trans
    apply Polynomial.natDegree_mul_le.trans
    simp only [Polynomial.natDegree_C, zero_add]
    exact Polynomial.natDegree_pow_le.trans (by simp only [Polynomial.natDegree_X_add_C, mul_one]; exact le_rfl)
  have hlower : ∀ᶠ T : ℕ in Filter.atTop,
      (Polynomial.preHilbertPoly ℚ J.card 0).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    apply Filter.eventually_atTop.mpr
    refine ⟨T₀, fun T h => ?_⟩
    rw [← hT T h, Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    exact_mod_cast independent_coordinates_hilbert_lower I j hind T
  have hbase : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (Polynomial.preHilbertPoly ℚ J.card 0).eval (T : ℚ) := by
    apply Filter.Eventually.of_forall
    intro T
    rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    positivity
  have hdegree : P.natDegree = J.card := by
    apply Nat.le_antisymm hupper
    simpa only [Polynomial.natDegree_preHilbertPoly] using
      natDegree_le_of_eventually_nat_eval_bounds _ P hbase hlower
  have hcoeff : (J.card.factorial : ℚ)⁻¹ ≤ P.coeff J.card := by
    have hh := coeff_le_of_eventually_nat_eval_le
      (Polynomial.preHilbertPoly ℚ J.card 0) P J.card
      (by rw [Polynomial.natDegree_preHilbertPoly]) hupper hlower
    simpa only [Polynomial.coeff_preHilbertPoly_self] using hh
  refine ⟨P, ?_⟩
  rw [hdegree]
  exact ⟨j, hj, hind, hcoeff, T₀, hT⟩

theorem projection_hilbert_le {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K))
    (J : Ideal (MvPolynomial (Fin m) K)) (j : Fin m → Fin n)
    (hker : ∀ p, Ideal.Quotient.mk I (rename j p) = 0 ↔ p ∈ J) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let := totalSpace_finite (n := n) (K := K) T
  let f₀ := (Ideal.Quotient.mkₐ K I).comp (rename j)
  let f := Ideal.Quotient.liftₐ J f₀ (fun p hp => (hker p).mpr hp)
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro y hy
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact (hker p).mp hy
  let g := (f.toLinearMap.domRestrict
    ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap)).codRestrict
      ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) (by
        rintro ⟨y, p, hp, rfl⟩
        exact ⟨rename j p,
          mem_totalSpace.mpr ((totalDegree_rename_le j p).trans (mem_totalSpace.mp hp)), rfl⟩)
  apply LinearMap.finrank_le_finrank_of_injective (f := g)
  intro y z he
  exact Subtype.ext (hf (congrArg Subtype.val he))

theorem not_independent_over_hilbert_degree {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (j : Fin (h+1) → Fin n) :
    ¬ AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) := by
  intro hj
  have hlower : ∀ᶠ T : ℕ in Filter.atTop,
      (Polynomial.preHilbertPoly ℚ (h+1) 0).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    apply hT.mono
    intro T h
    rw [← h, Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    simp only [Nat.sub_zero]
    exact_mod_cast independent_coordinates_hilbert_lower I j hj T
  have hbase : ∀ᶠ T : ℕ in Filter.atTop,
      0 ≤ (Polynomial.preHilbertPoly ℚ (h+1) 0).eval (T : ℚ) := by
    apply Filter.Eventually.of_forall
    intro T
    rw [Polynomial.preHilbertPoly_eq_choose_sub_add _ _ (Nat.zero_le _)]
    positivity
  have hh := natDegree_le_of_eventually_nat_eval_bounds _ P hbase hlower
  rw [Polynomial.natDegree_preHilbertPoly] at hh
  omega

theorem projection_equation_degree_bound {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (P : Polynomial ℚ)
    (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (j : Fin (h+1) → Fin n)
    (q : MvPolynomial (Fin (h+1)) K) (hq : q ≠ 0)
    (hker : ∀ p, Ideal.Quotient.mk I (rename j p) = 0 ↔ q ∣ p) :
    (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h := by
  have hh : ∀ᶠ T : ℕ in Filter.atTop,
      (hypersurfaceHilbertPolynomial h q.totalDegree).eval (T : ℚ) ≤ P.eval (T : ℚ) := by
    filter_upwards [hT, Filter.eventually_ge_atTop q.totalDegree] with T hT hqT
    rw [← hT, ← hypersurface_hilbert_polynomial q hq T hqT]
    exact_mod_cast projection_hilbert_le I (Ideal.span {q}) j
      (fun p => (hker p).trans Ideal.mem_span_singleton.symm) T
  have hcoeff := coeff_le_of_eventually_nat_eval_le
    (hypersurfaceHilbertPolynomial h q.totalDegree) P h
    (hypersurfaceHilbertPolynomial_degree _ _) hP hh
  rw [hypersurfaceHilbertPolynomial_coeff] at hcoeff
  have hf : (0 : ℚ) < h.factorial := by exact_mod_cast Nat.factorial_pos h
  exact (div_le_iff₀ hf).mp hcoeff |>.trans_eq (mul_comm _ _)

open Polynomial

theorem exists_irreducible_in_kernel {R S : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [CommRing S] [IsDomain S]
    (f : R →+* S) (p : R) (hp : p ≠ 0) (hfp : f p = 0) :
    ∃ g : R, Irreducible g ∧ f g = 0 := by
  induction p using WfDvdMonoid.induction_on_irreducible with
  | zero => exact (hp rfl).elim
  | unit u hu => exact (hu.map f).ne_zero hfp |>.elim
  | mul a i ha hi ih =>
    rw [map_mul, mul_eq_zero] at hfp
    rcases hfp with h | h
    · exact ⟨i, hi, h⟩
    · exact ih ha h

theorem principal_coordinate_kernel {R F L : Type*} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] [Field F] [Field L]
    [Algebra R F] [IsFractionRing R F] [Algebra F L] [Algebra R L]
    [IsScalarTower R F L]
    (x : L) (p : Polynomial R) (hp : p ≠ 0) (hpx : Polynomial.aeval x p = 0) :
    ∃ g : Polynomial R, Irreducible g ∧ g.IsPrimitive ∧ g.natDegree ≠ 0 ∧
      (∀ q : Polynomial R, Polynomial.aeval x q = 0 ↔ g ∣ q) := by
  obtain ⟨g, hg, hxg⟩ := exists_irreducible_in_kernel (Polynomial.aeval x).toRingHom p hp hpx
  change Polynomial.aeval x g = 0 at hxg
  have hinj : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R F L]
    change Function.Injective ((algebraMap F L) ∘ (algebraMap R F))
    exact (RingHom.injective (algebraMap F L)).comp (IsFractionRing.injective R F)
  have hn : g.natDegree ≠ 0 := by
    intro h
    have he := eq_C_of_natDegree_eq_zero h
    have hh := hxg
    rw [he, Polynomial.aeval_C] at hh
    have hz : g.coeff 0 = 0 := hinj (hh.trans (map_zero _).symm)
    exact hg.ne_zero (he.trans (by rw [hz, Polynomial.C_0]))
  have hprim := hg.isPrimitive hn
  have hi : Irreducible (g.map (algebraMap R F)) :=
    hprim.irreducible_iff_irreducible_map_fraction_map.mp hg
  have hx : Polynomial.aeval x (g.map (algebraMap R F)) = 0 := by
    simpa only [Polynomial.aeval_map_algebraMap] using hxg
  have ha : IsAlgebraic F x := ⟨g.map (algebraMap R F), hi.ne_zero, hx⟩
  have hass := (minpoly.irreducible ha.isIntegral).associated_of_dvd hi (minpoly.dvd F x hx)
  refine ⟨g, hg, hprim, hn, ?_⟩
  intro q
  constructor
  · intro hq
    apply (hprim.dvd_iff_fraction_map_dvd_fraction_map F).mpr
    apply hass.dvd_iff_dvd_left.mp
    exact minpoly.dvd F x (by simpa only [Polynomial.aeval_map_algebraMap] using hq)
  · rintro ⟨r, rfl⟩
    simp only [map_mul, hxg, zero_mul]

open MvPolynomial in

theorem principal_projection_relation {h : ℕ} {K L : Type*} [Field K] [Field L]
    [Algebra K L] (y : Fin h → L) (hy : AlgebraicIndependent K y) (x : L)
    (p : MvPolynomial (Fin (h+1)) K) (hp : p ≠ 0)
    (hpx : MvPolynomial.aeval (Fin.cases x y) p = 0) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, MvPolynomial.aeval (Fin.cases x y) r = 0 ↔ q ∣ r) := by
  let R := MvPolynomial (Fin h) K
  let F := FractionRing R
  let f : R →ₐ[K] L := MvPolynomial.aeval y
  have hf : Function.Injective f := algebraicIndependent_iff_injective_aeval.mp hy
  let : Algebra R L := f.toRingHom.toAlgebra
  let : Algebra F L := (IsFractionRing.lift (K := F) hf).toAlgebra
  have hcomp : algebraMap R L = (algebraMap F L).comp (algebraMap R F) := by
    apply RingHom.ext
    intro a
    exact (IsFractionRing.lift_algebraMap (K := F) (g := f.toRingHom) hf a).symm
  let : IsScalarTower R F L := IsScalarTower.of_algebraMap_eq' hcomp
  let E := finSuccEquiv K h
  have heval (r : MvPolynomial (Fin (h+1)) K) :
      Polynomial.aeval x (E r) = MvPolynomial.aeval (Fin.cases x y) r := by
    have he : (Polynomial.aeval x).toRingHom.comp E.toRingHom =
        (MvPolynomial.aeval (Fin.cases x y)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro c
        change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.C c)) = _
        rw [finSuccEquiv_apply, eval₂Hom_C, RingHom.comp_apply, Polynomial.aeval_C]
        change MvPolynomial.aeval y (MvPolynomial.C c) =
          MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.C c)
        simp only [MvPolynomial.aeval_C]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.X 0)) = _
          rw [finSuccEquiv_X_zero, Polynomial.aeval_X]
          change x = MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.X (0 : Fin (h+1)))
          simp only [MvPolynomial.aeval_X, Fin.cases_zero]
        · change Polynomial.aeval x ((finSuccEquiv K h) (MvPolynomial.X j.succ)) = _
          rw [finSuccEquiv_X_succ, Polynomial.aeval_C]
          change MvPolynomial.aeval y (MvPolynomial.X j) =
            MvPolynomial.aeval (Fin.cases x y) (MvPolynomial.X j.succ)
          simp only [MvPolynomial.aeval_X, Fin.cases_succ]
    exact congrArg (fun g : MvPolynomial (Fin (h+1)) K →+* L => g r) he
  have hep : E p ≠ 0 := by
    intro hh
    exact hp (E.injective (hh.trans (map_zero E).symm))
  obtain ⟨g, hg, _, hgn, hgker⟩ := principal_coordinate_kernel (F := F) x (E p) hep
    ((heval p).trans hpx)
  refine ⟨E.symm g, ?_, ?_, ?_⟩
  · exact (MulEquiv.irreducible_iff E.symm).mpr hg
  · simpa only [← natDegree_finSuccEquiv, E, AlgEquiv.apply_symm_apply] using hgn
  · intro r
    rw [← heval r, hgker]
    constructor
    · rintro ⟨s, hs⟩
      refine ⟨E.symm s, ?_⟩
      apply E.injective
      simpa only [map_mul, AlgEquiv.apply_symm_apply] using hs
    · rintro ⟨s, rfl⟩
      exact ⟨E s, by simp only [map_mul, AlgEquiv.apply_symm_apply]⟩

theorem quotient_aeval_rename {n m : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (j : Fin m → Fin n) :
    MvPolynomial.aeval (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) =
      (Ideal.Quotient.mkₐ K I).comp (MvPolynomial.rename j) := by
  ext a
  simp

theorem exists_principal_relation_of_dependent {h : ℕ} {K A : Type*}
    [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    (x : A) (y : Fin h → A) (hy : AlgebraicIndependent K y)
    (hxy : ¬ AlgebraicIndependent K (Fin.cases x y)) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, MvPolynomial.aeval (Fin.cases x y) r = 0 ↔ q ∣ r) := by
  let L := FractionRing A
  let e : A →ₐ[K] L := IsScalarTower.toAlgHom K A L
  have he : Function.Injective e := IsFractionRing.injective A L
  have hcase : Fin.cases (e x) (fun a => e (y a)) =
      fun a : Fin (h+1) => e (Fin.cases x y a) := by
    funext a
    exact Fin.cases rfl (fun _ => rfl) a
  have hei (r : MvPolynomial (Fin (h+1)) K) :
      MvPolynomial.aeval (Fin.cases (e x) (fun a => e (y a))) r =
        e (MvPolynomial.aeval (Fin.cases x y) r) := by
    rw [hcase, ← MvPolynomial.comp_aeval_apply]
  have hyL : AlgebraicIndependent K (fun a => e (y a)) := hy.map' he
  rw [algebraicIndependent_iff] at hxy
  push Not at hxy
  obtain ⟨p, hpx, hp⟩ := hxy
  obtain ⟨q, hq, hqdeg, hqker⟩ := principal_projection_relation
    (fun a => e (y a)) hyL (e x) p hp (by rw [hei, hpx, map_zero])
  refine ⟨q, hq, hqdeg, fun r => ?_⟩
  rw [← hqker, hei, map_eq_zero_iff e he]

theorem prime_projection_relation {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))))
    (i : Fin n)
    (hdep : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (Fin.cases i j a)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename (Fin.cases i j) r) = 0 ↔ q ∣ r) := by
  have hcase : Fin.cases (Ideal.Quotient.mk I (MvPolynomial.X i))
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) =
        fun a : Fin (h+1) => Ideal.Quotient.mk I (MvPolynomial.X (Fin.cases i j a)) := by
    funext a
    exact Fin.cases rfl (fun _ => rfl) a
  have hd : ¬ AlgebraicIndependent K
      (Fin.cases (Ideal.Quotient.mk I (MvPolynomial.X i))
        (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a)))) := by
    rwa [hcase]
  obtain ⟨q, hq, hqdeg, hqker⟩ := exists_principal_relation_of_dependent
    (Ideal.Quotient.mk I (MvPolynomial.X i))
    (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) hj hd
  refine ⟨q, hq, hqdeg, fun r => ?_⟩
  rw [← hqker, hcase, quotient_aeval_rename]
  rfl

theorem prime_projection_map {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (z : Fin (h+1) → Fin n)
    (hz : AlgebraicIndependent K
      (fun a : Fin h => Ideal.Quotient.mk I (MvPolynomial.X (z a.succ))))
    (hdep : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X (z a)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename z r) = 0 ↔ q ∣ r) := by
  have he (a : Fin (h+1)) : Fin.cases (z 0) (fun b : Fin h => z b.succ) a = z a :=
    Fin.cases rfl (fun _ => rfl) a
  have hd : ¬ AlgebraicIndependent K
      (fun a => Ideal.Quotient.mk I (MvPolynomial.X
        (Fin.cases (z 0) (fun b : Fin h => z b.succ) a))) := by
    simpa only [he] using hdep
  obtain ⟨q, hq, hqd, hker⟩ := prime_projection_relation I (fun a => z a.succ) hz (z 0) hd
  refine ⟨q, hq, hqd, fun r => ?_⟩
  have hr : MvPolynomial.rename z r =
      MvPolynomial.rename (fun a => Fin.cases (z 0) (fun b : Fin h => z b.succ) a) r :=
    congrArg (fun v : Fin (h+1) → Fin n => MvPolynomial.rename v r) (funext he).symm
  rw [hr]
  exact hker r

theorem bounded_projection_relation {n h : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) (z : Fin (h+1) → Fin n)
    (hz : AlgebraicIndependent K
      (fun a : Fin h => Ideal.Quotient.mk I (MvPolynomial.X (z a.succ)))) :
    ∃ q : MvPolynomial (Fin (h+1)) K, Irreducible q ∧ q.degreeOf 0 ≠ 0 ∧
      (q.totalDegree : ℚ) ≤ (h.factorial : ℚ) * P.coeff h ∧
      (∀ r, Ideal.Quotient.mk I (MvPolynomial.rename z r) = 0 ↔ q ∣ r) := by
  have hd := not_independent_over_hilbert_degree I P hP hT z
  obtain ⟨q, hq, hqdeg, hker⟩ := prime_projection_map I z hz hd
  exact ⟨q, hq, hqdeg,
    projection_equation_degree_bound I P hP hT z q hq.ne_zero hker, hker⟩

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_Jacobians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

namespace QuarticPowerFree

section

attribute [local instance] Classical.propDecidable

theorem pderiv_totalDegree_lt {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) (h : MvPolynomial.pderiv i p ≠ 0) :
    (MvPolynomial.pderiv i p).totalDegree < p.totalDegree := by
  classical
  have hs : ∀ m ∈ (MvPolynomial.pderiv i p).support,
      m.sum (fun _ e => e) < p.totalDegree := by
    intro m hm
    have hc := MvPolynomial.mem_support_iff.mp hm
    rw [MvPolynomial.coeff_pderiv] at hc
    have hp : m + Finsupp.single i 1 ∈ p.support :=
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul]))
    have hh := MvPolynomial.le_totalDegree hp
    rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
      Finsupp.sum_single_index (by rfl)] at hh
    exact hh
  obtain ⟨m, hm⟩ := MvPolynomial.support_nonempty.mpr h
  have hpos : 0 < p.totalDegree := (Nat.zero_le _).trans_lt (hs m hm)
  exact (Finset.sup_lt_iff hpos).mpr hs

theorem pderiv_vars_subset {σ K : Type*} [CommSemiring K]
    (i : σ) (p : MvPolynomial σ K) :
    (MvPolynomial.pderiv i p).vars ⊆ p.vars := by
  classical
  intro j hj
  obtain ⟨m, hm, hjm⟩ := (MvPolynomial.mem_vars_iff_mem_support j).mp hj
  have hc := MvPolynomial.mem_support_iff.mp hm
  rw [MvPolynomial.coeff_pderiv] at hc
  refine (MvPolynomial.mem_vars_iff_mem_support j).mpr
    ⟨m + Finsupp.single i 1,
      MvPolynomial.mem_support_iff.mpr (fun he => hc (by rw [he, zero_mul])), ?_⟩
  rw [Finsupp.mem_support_iff, Finsupp.add_apply]
  have hh := Finsupp.mem_support_iff.mp hjm
  omega

theorem pderiv_ne_zero_of_mem_vars {σ K : Type*} [CommRing K]
    [IsDomain K] [CharZero K] (i : σ) (p : MvPolynomial σ K)
    (hi : i ∈ p.vars) : MvPolynomial.pderiv i p ≠ 0 := by
  classical
  obtain ⟨m, hm, him⟩ := (MvPolynomial.mem_vars_iff_mem_support i).mp hi
  have hmi : m i ≠ 0 := Finsupp.mem_support_iff.mp him
  have hcoeff : p.coeff m ≠ 0 := MvPolynomial.mem_support_iff.mp hm
  intro h
  have hh := congrArg (fun polynomial => polynomial.coeff (m - Finsupp.single i 1)) h
  rw [MvPolynomial.coeff_pderiv, Finsupp.sub_add_single_one_cancel hmi,
    MvPolynomial.coeff_zero] at hh
  have hnat : ∀ n : ℕ, (n : K) + 1 ≠ 0 := by
    intro n
    exact_mod_cast Nat.succ_ne_zero n
  exact (mul_ne_zero hcoeff (hnat _)) hh

theorem eq_zero_of_aeval_eq_zero_of_vars_subset {σ K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val))
    (p : MvPolynomial σ K) (hp : (p.vars : Set σ) ⊆ J)
    (hz : MvPolynomial.aeval z p = 0) : p = 0 := by
  obtain ⟨q, hq⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range p
    (fun j : J => j.val) Subtype.val_injective (by simpa using hp)
  subst p
  rw [MvPolynomial.aeval_rename] at hz
  have hh : q = 0 := (algebraicIndependent_iff_injective_aeval.mp hJ)
    (hz.trans (map_zero _).symm)
  simp [hh]

theorem exists_relation_with_nonzero_pderiv {σ K F : Type*}
    [Field K] [CharZero K] [CommRing F] [Algebra K F]
    (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val))
    (i : σ) (p : MvPolynomial σ K) (hp : p ≠ 0)
    (hvars : (p.vars : Set σ) ⊆ insert i J) (hz : MvPolynomial.aeval z p = 0) :
    ∃ q : MvPolynomial σ K, q ≠ 0 ∧ (q.vars : Set σ) ⊆ insert i J ∧
      q.totalDegree ≤ p.totalDegree ∧ MvPolynomial.aeval z q = 0 ∧
      MvPolynomial.aeval z (MvPolynomial.pderiv i q) ≠ 0 := by
  classical
  let S : Set (MvPolynomial σ K) :=
    {q | q ≠ 0 ∧ (q.vars : Set σ) ⊆ insert i J ∧ MvPolynomial.aeval z q = 0}
  have hpS : p ∈ S := ⟨hp, hvars, hz⟩
  let q := Function.argminOn MvPolynomial.totalDegree S ⟨p, hpS⟩
  have hq : q ∈ S := Function.argminOn_mem _ _ _
  have hiq : i ∈ q.vars := by
    by_contra hn
    apply hq.1
    apply eq_zero_of_aeval_eq_zero_of_vars_subset z J hJ q _ hq.2.2
    intro j hj
    rcases hq.2.1 hj with he | he
    · exact False.elim (hn (he ▸ hj))
    · exact he
  have hder : MvPolynomial.pderiv i q ≠ 0 := pderiv_ne_zero_of_mem_vars i q hiq
  have hdeg := pderiv_totalDegree_lt i q hder
  refine ⟨q, hq.1, hq.2.1, ?_, hq.2.2, ?_⟩
  · exact Function.argminOn_le _ _ hpS
  · intro he
    have hdS : MvPolynomial.pderiv i q ∈ S :=
      ⟨hder, fun j hj => hq.2.1 (pderiv_vars_subset i q hj), he⟩
    exact Function.not_lt_argminOn MvPolynomial.totalDegree S hdS hdeg

theorem exists_diagonal_jacobian_relations {σ K F : Type*}
    [Fintype σ] [DecidableEq σ] [Field K] [CharZero K] [CommRing F] [IsDomain F] [Algebra K F]
    (z : σ → F) (J : Set σ)
    (hJ : AlgebraicIndependent K (fun j : J => z j.val)) (D : ℕ)
    (hrel : ∀ i : ↥(Jᶜ), ∃ p : MvPolynomial σ K, p ≠ 0 ∧
      (p.vars : Set σ) ⊆ insert i.val J ∧ p.totalDegree ≤ D ∧
      MvPolynomial.aeval z p = 0) :
    ∃ G : ↥(Jᶜ) → MvPolynomial σ K,
      (∀ i, (G i).totalDegree ≤ D) ∧
      (∀ i, MvPolynomial.aeval z (G i) = 0) ∧
      Matrix.det (fun i j : ↥(Jᶜ) => MvPolynomial.aeval z
        (MvPolynomial.pderiv j.val (G i))) ≠ 0 := by
  classical
  have hh : ∀ i : ↥(Jᶜ), ∃ q : MvPolynomial σ K,
      (q.vars : Set σ) ⊆ insert i.val J ∧ q.totalDegree ≤ D ∧
      MvPolynomial.aeval z q = 0 ∧
      MvPolynomial.aeval z (MvPolynomial.pderiv i.val q) ≠ 0 := by
    intro i
    obtain ⟨p, hp, hv, hd, he⟩ := hrel i
    obtain ⟨q, _, hvq, hdq, heq, hder⟩ :=
      exists_relation_with_nonzero_pderiv z J hJ i.val p hp hv he
    exact ⟨q, hvq, hdq.trans hd, heq, hder⟩
  choose G hvars hdeg heval hder using hh
  refine ⟨G, hdeg, heval, ?_⟩
  have hmat : (fun i j : ↥(Jᶜ) => MvPolynomial.aeval z
      (MvPolynomial.pderiv j.val (G i))) =
      Matrix.diagonal (fun i : ↥(Jᶜ) => MvPolynomial.aeval z
        (MvPolynomial.pderiv i.val (G i))) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · rw [Matrix.diagonal_apply_ne _ hij]
      rw [MvPolynomial.pderiv_eq_zero_of_notMem_vars, map_zero]
      intro hj
      rcases hvars i hj with hj | hj
      · exact hij (Subtype.ext hj.symm)
      · exact j.property hj
  rw [hmat, Matrix.det_diagonal]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => hder i)

theorem exists_nonsingular_rows_of_span_eq_top {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field F] (A : Matrix α β F)
    (hA : Submodule.span F (Set.range A) = ⊤) :
    ∃ a : β → α, Function.Injective a ∧ Matrix.det (fun i j => A (a i) j) ≠ 0 := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' F A
  let := Fintype.ofInjective a ha
  let b : Module.Basis κ F (β → F) := Module.Basis.mk hli (by rw [hspan, hA])
  have hcard : Fintype.card β = Fintype.card κ := by
    rw [← Module.finrank_fintype_fun_eq_card (R := F), Module.finrank_eq_card_basis b]
  let e : β ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, ha.comp e.injective, ?_⟩
  apply Matrix.nonsingular_iff_det_ne_zero.mp
  apply Matrix.Nonsingular.of_linearIndependent_row
  exact hli.comp e e.injective

noncomputable def genericJacobianRow {σ β K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (v : β → σ) :
    MvPolynomial σ K →ₗ[K] (β → F) :=
  LinearMap.pi (fun j => (MvPolynomial.aeval z).toLinearMap.comp
    (MvPolynomial.pderiv (v j)).toLinearMap)

theorem jacobianRow_mem_span {σ α β K F : Type*}
    [CommRing K] [CommRing F] [Algebra K F] (z : σ → F) (v : β → σ)
    (G : α → MvPolynomial σ K) (p : MvPolynomial σ K)
    (hp : p ∈ Submodule.span K (Set.range G)) :
    genericJacobianRow z v p ∈ Submodule.span F
      (Set.range (fun i => genericJacobianRow z v (G i))) := by
  let W := Submodule.span F (Set.range (fun i => genericJacobianRow z v (G i)))
  have hs : Submodule.span K (Set.range G) ≤
      (W.restrictScalars K).comap (genericJacobianRow z v) := by
    apply Submodule.span_le.mpr
    rintro q ⟨i, rfl⟩
    exact Submodule.subset_span (Set.mem_range_self i)
  exact hs hp

theorem exists_nonsingular_jacobian_of_span {σ α β K F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field K] [Field F] [Algebra K F]
    (z : σ → F) (v : β → σ) (G : α → MvPolynomial σ K)
    (P : β → MvPolynomial σ K)
    (hP : ∀ i, P i ∈ Submodule.span K (Set.range G))
    (hdet : Matrix.det (fun i j => MvPolynomial.aeval z
      (MvPolynomial.pderiv (v j) (P i))) ≠ 0) :
    ∃ a : β → α, Function.Injective a ∧
      Matrix.det (fun i j => MvPolynomial.aeval z
        (MvPolynomial.pderiv (v j) (G (a i)))) ≠ 0 := by
  classical
  let A : Matrix β β F := fun i => genericJacobianRow z v (P i)
  have hli : LinearIndependent F A := Matrix.linearIndependent_rows_of_det_ne_zero hdet
  have htop : Submodule.span F (Set.range A) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (Module.finrank_fintype_fun_eq_card (R := F)).symm
  apply exists_nonsingular_rows_of_span_eq_top (fun i => genericJacobianRow z v (G i))
  apply top_unique
  rw [← htop]
  apply Submodule.span_le.mpr
  rintro q ⟨i, rfl⟩
  exact jacobianRow_mem_span z v G (P i) (hP i)

end
open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem bounded_generic_jacobian {n h D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : (h.factorial : ℚ) * P.coeff h ≤ D)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a)))) :
    ∃ J : Set (Fin n), Nat.card J = h ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) K,
        (∀ i, (G i).totalDegree ≤ D) ∧ (∀ i, G i ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (G i)) ∉ I := by
  classical
  let z : Fin n → MvPolynomial (Fin n) K ⧸ I := fun a => Ideal.Quotient.mk I (X a)
  have hjj : Function.Injective j := by
    intro a b hab
    exact hj.injective (congrArg (fun x => Ideal.Quotient.mk I (X x)) hab)
  obtain ⟨J, hJr⟩ : ∃ J : Set (Fin n), Set.range j = J := ⟨_, rfl⟩
  have hmem (a : Fin n) : a ∈ Set.range j ↔ a ∈ J := Set.ext_iff.mp hJr a
  let e : Fin h ≃ J := (Equiv.ofInjective j hjj).trans (Equiv.setCongr hJr)
  have heval (a : Fin h) : (e a).val = j a := rfl
  have hej (a : J) : j (e.symm a) = a.val := (heval _).symm.trans (congrArg Subtype.val (e.apply_symm_apply a))
  have hJ : AlgebraicIndependent K (fun a : J => z a.val) := by
    have hh := hj.comp e.symm e.symm.injective
    simpa only [Function.comp_def, hej, z] using hh
  have hae : aeval z = Ideal.Quotient.mkₐ K I := by ext a; simp only [aeval_X]; rfl
  have hr : ∀ i : ↥(Jᶜ), ∃ p : MvPolynomial (Fin n) K, p ≠ 0 ∧
      (p.vars : Set (Fin n)) ⊆ insert i.val J ∧ p.totalDegree ≤ D ∧ aeval z p = 0 := by
    intro i
    let v : Fin (h+1) → Fin n := Fin.cases i.val j
    have hvj : AlgebraicIndependent K
        (fun a : Fin h => Ideal.Quotient.mk I (X (v a.succ))) := hj
    obtain ⟨q,hq,_,hd,hker⟩ := bounded_projection_relation I P hP hT v hvj
    have hvi : Function.Injective v := by
      intro a b hab
      cases a using Fin.cases with
      | zero =>
        cases b using Fin.cases with
        | zero => rfl
        | succ b => exact False.elim (i.property ((hmem i.val).mp (Set.mem_range.mpr ⟨b,hab.symm⟩)))
      | succ a =>
        cases b using Fin.cases with
        | zero => exact False.elim (i.property ((hmem i.val).mp (Set.mem_range.mpr ⟨a,hab⟩)))
        | succ b => exact congrArg Fin.succ (hjj hab)
    refine ⟨rename v q, (rename_injective v hvi).ne hq.ne_zero, ?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨b,_,rfl⟩ := mem_vars_rename v q ha
      cases b using Fin.cases with
      | zero => exact Set.mem_insert _ _
      | succ b => exact Set.mem_insert_of_mem _ ((hmem (j b)).mp (Set.mem_range_self b))
    · apply (totalDegree_rename_le v q).trans
      exact_mod_cast hd.trans hD
    · rw [hae]
      exact (hker q).mpr (dvd_refl q)
  obtain ⟨G,hdeg,hvan,hdet⟩ := exists_diagonal_jacobian_relations z J hJ D hr
  refine ⟨J, ?_, G,hdeg,?_,?_⟩
  · exact (Nat.card_congr e.symm).trans (Nat.card_fin h)
  · intro i
    exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa only [hae, Ideal.Quotient.mkₐ_eq_mk] using hvan i)
  · have hdet' : Matrix.det (fun i l : ↥(Jᶜ) => Ideal.Quotient.mk I (pderiv l.val (G i))) ≠ 0 := by
      simpa only [hae, Ideal.Quotient.mkₐ_eq_mk] using hdet
    intro hm
    apply hdet'
    let M : Matrix ↥(Jᶜ) ↥(Jᶜ) (MvPolynomial (Fin n) K) := fun i l => pderiv l.val (G i)
    have hm0 : Ideal.Quotient.mk I M.det = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hm
    have he : ((Ideal.Quotient.mk I).mapMatrix M).det = 0 :=
      ((Ideal.Quotient.mk I).map_det M).symm.trans hm0
    exact he

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_IntegralKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators

open Matrix
open scoped BigOperators

namespace QuarticPowerFree

def integralKernelMatrix {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) : Matrix β β R :=
  (B * B.transpose).det • 1 - B.transpose * (B * B.transpose).adjugate * B

theorem mul_integralKernelMatrix {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R) :
    B * integralKernelMatrix B = 0 := by
  unfold integralKernelMatrix
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_adjugate,
    Matrix.smul_mul, Matrix.one_mul, sub_self]

theorem integralKernelMatrix_mulVec_of_kernel {α β R : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [CommRing R] (B : Matrix α β R)
    (x : β → R) (hx : B *ᵥ x = 0) :
    integralKernelMatrix B *ᵥ x = (B * B.transpose).det • x := by
  unfold integralKernelMatrix
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero, sub_zero]

theorem gram_det_ne_zero_of_linearIndependent {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [Field F] [LinearOrder F]
    [IsStrictOrderedRing F] (B : Matrix α β F) (hB : LinearIndependent F B) :
    (B * B.transpose).det ≠ 0 := by
  intro hdet
  obtain ⟨x, hx, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hz : B.transpose *ᵥ x = 0 := by
    rw [← Matrix.mulVec_mulVec] at hker
    have hh := congrArg (fun y => dotProduct x y) hker
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      dotProduct_zero, dotProduct_self_eq_zero] at hh
    exact hh
  apply hx
  have hinj : Function.Injective (fun x => x ᵥ* B) :=
    Matrix.vecMul_injective_iff.mpr hB
  apply hinj
  simpa only [Matrix.mulVec_transpose, Matrix.zero_vecMul] using hz

theorem mulVec_eq_zero_of_row_mem_span {α β γ F : Type*}
    [Fintype β] [CommSemiring F] [Fintype γ]
    (A : Matrix α β F) (B : Matrix γ β F)
    (hspan : ∀ i, A i ∈ Submodule.span F (Set.range B))
    (x : β → F) (hx : B *ᵥ x = 0) : A *ᵥ x = 0 := by
  ext i
  change dotProduct (A i) x = 0
  have hsub : Submodule.span F (Set.range B) ≤
      LinearMap.ker ((dotProductBilin F F).flip x) := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact congrFun hx j
  exact hsub (hspan i)

theorem integralKernelMatrix_column_mem_kernel {α β γ R : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    [DecidableEq α] [DecidableEq β] [CommRing R]
    (A : Matrix γ β R) (B : Matrix α β R)
    (hspan : ∀ i, A i ∈ Submodule.span R (Set.range B)) (j : β) :
    A *ᵥ (fun i => integralKernelMatrix B i j) = 0 := by
  apply mulVec_eq_zero_of_row_mem_span A B hspan
  have hh := mul_integralKernelMatrix B
  ext i
  exact congrArg (fun M => M i j) hh

theorem mem_span_integralKernelMatrix_columns {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] [Field F]
    (B : Matrix α β F) (hdet : (B * B.transpose).det ≠ 0)
    (x : β → F) (hx : B *ᵥ x = 0) :
    x ∈ Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)) := by
  have heq := integralKernelMatrix_mulVec_of_kernel B x hx
  have hmem : integralKernelMatrix B *ᵥ x ∈
      Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)) := by
    rw [Matrix.mulVec_eq_sum]
    apply Submodule.sum_mem
    intro j _
    change (fun i => integralKernelMatrix B i j * x j) ∈ _
    have hh := Submodule.smul_mem
      (Submodule.span F (Set.range (fun j => fun i => integralKernelMatrix B i j)))
      (x j) (Submodule.subset_span (Set.mem_range_self j))
    convert hh using 1
    ext i
    exact mul_comm _ _
  rw [heq] at hmem
  exact (Submodule.smul_mem_iff _ hdet).mp hmem

theorem exists_independent_spanning_rows {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℚ) :
    ∃ r : ℕ, r ≤ Fintype.card β ∧ ∃ a : Fin r → α,
      Function.Injective a ∧ LinearIndependent ℚ (fun i => A (a i)) ∧
      Submodule.span ℚ (Set.range (fun i => A (a i))) =
        Submodule.span ℚ (Set.range A) := by
  classical
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℚ A
  let := Fintype.ofInjective a ha
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, ?_, a ∘ e.symm, ha.comp e.symm.injective, ?_, ?_⟩
  · simpa only [Module.finrank_fintype_fun_eq_card] using hli.fintype_card_le_finrank
  · exact hli.comp e.symm e.symm.injective
  · have hrange : Set.range (fun i => A (a (e.symm i))) = Set.range (A ∘ a) := by
      ext y
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨e.symm i, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨e i, congrArg (fun j => A (a j)) (e.symm_apply_apply i)⟩
    simpa only [Function.comp_def, hrange] using hspan

theorem integralKernelMatrix_map {α β R S : Type*}
    [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [CommRing R] [CommRing S] (f : R →+* S) (B : Matrix α β R) :
    (integralKernelMatrix B).map f = integralKernelMatrix (B.map f) := by
  have hadj := f.map_adjugate (B * B.transpose)
  have hdet := f.map_det (B * B.transpose)
  simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hadj hdet
  unfold integralKernelMatrix
  ext i j
  simp only [Matrix.map_apply, Matrix.sub_apply, map_sub, Matrix.smul_apply,
    smul_eq_mul, map_mul]
  rw [hdet]
  have hone : f ((1 : Matrix β β R) i j) = (1 : Matrix β β S) i j := by
    simp only [Matrix.one_apply]; split_ifs <;> simp
  rw [hone]
  change _ - ((B.transpose * (B * B.transpose).adjugate * B).map f) i j = _
  rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map, hadj]

theorem det_abs_le_row_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (B : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ B i) :
    |A.det| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
  calc
    |A.det| = |∑ σ : Equiv.Perm ι, Equiv.Perm.sign σ • ∏ i, A (σ i) i| := by
      rw [Matrix.det_apply]
    _ ≤ ∑ σ : Equiv.Perm ι, |Equiv.Perm.sign σ • ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ σ : Equiv.Perm ι, ∏ i, |A (σ i) i| := by
      apply Finset.sum_congr rfl
      intro σ _
      rw [show |Equiv.Perm.sign σ • ∏ i, A (σ i) i| = |∏ i, A (σ i) i| from
        AbsoluteValue.abs.map_units_int_smul _ _, Finset.abs_prod]
    _ ≤ ∑ σ : Equiv.Perm ι, ∏ i, B (σ i) := by
      apply Finset.sum_le_sum
      intro σ _
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
    _ = (Nat.factorial (Fintype.card ι) : ℝ) * ∏ i, B i := by
      simp_rw [Equiv.prod_comp]
      simp [Fintype.card_perm]

theorem det_abs_le_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℤ) (B : ℝ) (hA : ∀ i j, |(A i j : ℝ)| ≤ B) :
    |(A.det : ℝ)| ≤ (Nat.factorial (Fintype.card ι) : ℝ) * B ^ Fintype.card ι := by
  rw [Int.cast_det]
  simpa only [Finset.prod_const, Finset.card_univ] using
    det_abs_le_row_product (A.map fun x => (x : ℝ)) (fun _ => B) hA

theorem matrix_mul_entry_abs_le {α β γ : Type*} [Fintype β]
    (A : Matrix α β ℤ) (B : Matrix β γ ℤ) (H K : ℝ)
    (hH : 0 ≤ H) (_hK : 0 ≤ K)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) (hB : ∀ i j, |(B i j : ℝ)| ≤ K)
    (i : α) (j : γ) : |((A * B) i j : ℝ)| ≤ (Fintype.card β : ℝ) * H * K := by
  simp only [Matrix.mul_apply, Int.cast_sum, Int.cast_mul]
  calc
    |∑ k, (A i k : ℝ) * (B k j : ℝ)| ≤ ∑ k, |(A i k : ℝ) * (B k j : ℝ)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : β, H * K := by
      apply Finset.sum_le_sum
      intro k _
      rw [abs_mul]
      exact mul_le_mul (hA i k) (hB k j) (abs_nonneg _) hH
    _ = (Fintype.card β : ℝ) * H * K := by simp [mul_assoc]

def integralKernelHeight (n : ℕ) (H : ℝ) : ℝ :=
  (1 + (n : ℝ) ^ 2 * H ^ 2) * (Nat.factorial n : ℝ) *
    (1 + (n : ℝ) * H ^ 2) ^ n

theorem integralKernelMatrix_abs_le {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (B : Matrix α β ℤ) (n : ℕ)
    (hα : Fintype.card α ≤ n) (hβ : Fintype.card β ≤ n)
    (H : ℝ) (hH : 1 ≤ H) (hB : ∀ i j, |(B i j : ℝ)| ≤ H) (i j : β) :
    |((integralKernelMatrix B i j : ℤ) : ℝ)| ≤ integralKernelHeight n H := by
  let G := B * B.transpose
  let C : ℝ := 1 + (n : ℝ) * H ^ 2
  let K : ℝ := (Nat.factorial n : ℝ) * C ^ n
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hC : 1 ≤ C := by
    dsimp [C]
    linarith [mul_nonneg (Nat.cast_nonneg n) (sq_nonneg H)]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hG : ∀ u v, |(G u v : ℝ)| ≤ C := by
    intro u v
    have hh := matrix_mul_entry_abs_le B B.transpose H H hH0 hH0 hB
      (fun i j => hB j i) u v
    apply hh.trans
    have hc : (Fintype.card β : ℝ) ≤ n := by exact_mod_cast hβ
    dsimp [C]
    nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg H)]
  have hdetbound {A : Matrix α α ℤ} (hA : ∀ u v, |(A u v : ℝ)| ≤ C) :
      |(A.det : ℝ)| ≤ K := by
    apply (det_abs_le_uniform A C hA).trans
    exact mul_le_mul (by exact_mod_cast Nat.factorial_le hα)
      (pow_le_pow_right₀ hC hα) (by positivity) (by positivity)
  have hdet : |(G.det : ℝ)| ≤ K := hdetbound hG
  have hadj : ∀ u v, |(G.adjugate u v : ℝ)| ≤ K := by
    intro u v
    rw [Matrix.adjugate_apply]
    apply hdetbound
    intro a b
    by_cases hav : a = v
    · subst a
      rw [Matrix.updateRow_self]
      by_cases hbu : b = u
      · subst b
        simpa using hC
      · simp [Pi.single_eq_of_ne hbu, zero_le_one.trans hC]
    · rw [Matrix.updateRow_ne hav]
      exact hG a b
  have hb₁ : ∀ u v, |((B.transpose * G.adjugate) u v : ℝ)| ≤
      (Fintype.card α : ℝ) * H * K :=
    matrix_mul_entry_abs_le B.transpose G.adjugate H K hH0 hK
      (fun i j => hB j i) hadj
  have hb₂ := matrix_mul_entry_abs_le (B.transpose * G.adjugate) B
    ((Fintype.card α : ℝ) * H * K) H (by positivity) hH0 hb₁ hB i j
  have hdiag : |(((G.det • (1 : Matrix β β ℤ)) i j : ℤ) : ℝ)| ≤ K := by
    by_cases hij : i = j
    · subst j
      simpa using hdet
    · simpa [Matrix.one_apply, hij] using hK
  have hαr : (Fintype.card α : ℝ) ≤ n := by exact_mod_cast hα
  have hαnonneg : (0 : ℝ) ≤ Fintype.card α := Nat.cast_nonneg _
  have hsquare : (Fintype.card α : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 :=
    sq_le_sq₀ hαnonneg (Nat.cast_nonneg _) |>.mpr hαr
  unfold integralKernelMatrix
  change |(((G.det • (1 : Matrix β β ℤ)) i j -
    ((B.transpose * G.adjugate * B) i j) : ℤ) : ℝ)| ≤ _
  rw [Int.cast_sub]
  apply (abs_sub _ _).trans
  apply (add_le_add hdiag hb₂).trans
  have hsqbound := mul_le_mul_of_nonneg_right hsquare (mul_nonneg (sq_nonneg H) hK)
  dsimp [integralKernelHeight, K] at *
  nlinarith

theorem exists_bounded_integral_kernel_spanning {α β F : Type*}
    [Fintype α] [Fintype β] [DecidableEq β] [Field F] [CharZero F]
    (A : Matrix α β ℤ) (H : ℝ) (hH : 1 ≤ H)
    (hA : ∀ i j, |(A i j : ℝ)| ≤ H) :
    ∃ C : Matrix β β ℤ, A * C = 0 ∧
      (∀ i j, |(C i j : ℝ)| ≤ integralKernelHeight (Fintype.card β) H) ∧
      ∀ x : β → F, (A.map (Int.castRingHom F)) *ᵥ x = 0 →
        x ∈ Submodule.span F (Set.range
          (fun j => fun i => (C i j : F))) := by
  classical
  let AQ : Matrix α β ℚ := A.map (Int.castRingHom ℚ)
  obtain ⟨r, hr, a, _ha, hli, hspan⟩ := exists_independent_spanning_rows AQ
  let B : Matrix (Fin r) β ℤ := fun i => A (a i)
  have hliQ : LinearIndependent ℚ (B.map (Int.castRingHom ℚ)) := hli
  have hdetQ := gram_det_ne_zero_of_linearIndependent _ hliQ
  have hdetInt : (B * B.transpose).det ≠ 0 := by
    intro heq
    apply hdetQ
    have hh := (Int.castRingHom ℚ).map_det (B * B.transpose)
    simpa only [heq, map_zero, RingHom.mapMatrix_apply,
      Matrix.map_mul, Matrix.transpose_map] using hh.symm
  have hdetF : ((B.map (Int.castRingHom F)) *
      (B.map (Int.castRingHom F)).transpose).det ≠ 0 := by
    have hh := (Int.castRingHom F).map_det (B * B.transpose)
    simp only [RingHom.mapMatrix_apply, Matrix.map_mul, Matrix.transpose_map] at hh
    rw [← hh]
    exact Int.cast_ne_zero.mpr hdetInt
  let C := integralKernelMatrix B
  refine ⟨C, ?_, ?_, ?_⟩
  · have hmulQ : AQ * integralKernelMatrix (B.map (Int.castRingHom ℚ)) = 0 := by
      ext i j
      have hh := integralKernelMatrix_column_mem_kernel AQ (B.map (Int.castRingHom ℚ))
        (fun i => by
          change AQ i ∈ Submodule.span ℚ (Set.range (fun t => AQ (a t)))
          rw [hspan]
          exact Submodule.subset_span (Set.mem_range_self i)) j
      exact congrFun hh i
    ext i j
    apply Int.cast_injective (α := ℚ)
    change ((A * C).map (Int.castRingHom ℚ)) i j = 0
    rw [Matrix.map_mul]
    change (AQ * (integralKernelMatrix B).map (Int.castRingHom ℚ)) i j = 0
    rw [integralKernelMatrix_map, hmulQ]
    rfl
  · intro i j
    exact integralKernelMatrix_abs_le B (Fintype.card β) (by simpa using hr)
      le_rfl H hH (fun i j => hA (a i) j) i j
  · intro x hx
    have hxB : (B.map (Int.castRingHom F)) *ᵥ x = 0 := by
      ext i
      exact congrFun hx (a i)
    have hmem := mem_span_integralKernelMatrix_columns _ hdetF x hxB
    rw [← integralKernelMatrix_map (Int.castRingHom F) B] at hmem
    exact hmem

def monomialOrder {ι : Type*} (a : ι →₀ ℕ) : ℕ := a.sum (fun _ e => e)

noncomputable def monomialsUpTo (ι : Type*) [Fintype ι] (t : ℕ) : Finset (ι →₀ ℕ) := by
  classical
  exact (Finset.range (t + 1)).biUnion (fun n => Finset.univ.finsuppAntidiag n)

theorem mem_monomialsUpTo {ι : Type*} [Fintype ι] {a : ι →₀ ℕ} {t : ℕ} :
    a ∈ monomialsUpTo ι t ↔ monomialOrder a ≤ t := by
  classical
  simp only [monomialsUpTo, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag', Finset.subset_univ, and_true, monomialOrder]
  exact ⟨fun ⟨n, hn, heq⟩ => heq ▸ Nat.le_of_lt_succ hn,
    fun h => ⟨a.sum (fun _ e => e), Nat.lt_succ_of_le h, rfl⟩⟩

theorem card_monomialsUpTo (ι : Type*) [Fintype ι] (t : ℕ) :
    (monomialsUpTo ι t).card = (t + Fintype.card ι).choose (Fintype.card ι) := by
  classical
  rw [monomialsUpTo, Finset.card_biUnion]
  · simp_rw [Finset.card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ]
    exact Nat.sum_range_multichoose t (Fintype.card ι)
  intro i _ j _ hij
  apply Finset.disjoint_left.mpr
  intro a hi hj
  apply hij
  rw [Finset.mem_finsuppAntidiag'] at hi hj
  exact hi.1.symm.trans hj.1

noncomputable def polynomialFromCoefficients {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) : (M → R) →ₗ[R] MvPolynomial σ R where
  toFun c := ∑ m : M, MvPolynomial.monomial m.val (c m)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' r c := by
    change (∑ m : M, MvPolynomial.monomial m.val (r • c m)) =
      r • ∑ m : M, MvPolynomial.monomial m.val (c m)
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl (fun m _ => map_smul (MvPolynomial.monomial m.val) r (c m))

theorem polynomialFromCoefficients_coeff {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (m : M) :
    (polynomialFromCoefficients M c).coeff m.val = c m := by
  classical
  change (∑ t : M, MvPolynomial.monomial t.val (c t)).coeff m.val = _
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, ← Subtype.ext_iff, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem polynomialFromCoefficients_coeff_of_not_mem {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (m : σ →₀ ℕ) (hm : m ∉ M) :
    (polynomialFromCoefficients M c).coeff m = 0 := by
  classical
  change (∑ t : M, MvPolynomial.monomial t.val (c t)).coeff m = _
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_eq_zero
  intro t _
  rw [MvPolynomial.coeff_monomial, ite_eq_right]
  intro h
  exact hm (h ▸ t.property)

theorem polynomialFromCoefficients_support {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) :
    (polynomialFromCoefficients M c).support ⊆ M := by
  intro m hm
  by_contra h
  exact MvPolynomial.mem_support_iff.mp hm
    (polynomialFromCoefficients_coeff_of_not_mem M c m h)

theorem polynomialFromCoefficients_coefficients {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (p : MvPolynomial σ R) (hp : p.support ⊆ M) :
    polynomialFromCoefficients M (fun m => p.coeff m.val) = p := by
  classical
  ext m
  by_cases hm : m ∈ M
  · exact polynomialFromCoefficients_coeff M _ ⟨m, hm⟩
  · rw [polynomialFromCoefficients_coeff_of_not_mem M _ m hm]
    symm
    by_contra hn
    exact hm (hp (MvPolynomial.mem_support_iff.mpr hn))

theorem polynomialFromCoefficients_map {σ R S : Type*} [CommSemiring R]
    [CommSemiring S] (f : R →+* S) (M : Finset (σ →₀ ℕ)) (c : M → R) :
    MvPolynomial.map f (polynomialFromCoefficients M c) =
      polynomialFromCoefficients M (fun m => f (c m)) := by
  change MvPolynomial.map f (∑ m : M, MvPolynomial.monomial m.val (c m)) = _
  simp [map_sum, MvPolynomial.map_monomial, polynomialFromCoefficients]

theorem eval_polynomialFromCoefficients {σ R : Type*} [CommSemiring R]
    (M : Finset (σ →₀ ℕ)) (c : M → R) (z : σ → R) :
    MvPolynomial.eval z (polynomialFromCoefficients M c) =
      dotProduct (fun m : M => m.val.prod (fun i e => z i ^ e)) c := by
  change MvPolynomial.eval z (∑ m : M, MvPolynomial.monomial m.val (c m)) = _
  simp [MvPolynomial.eval_monomial, dotProduct, mul_comm]

theorem exists_bounded_polynomial_kernel {σ ι F : Type*}
    [Fintype ι] [Field F] [CharZero F]
    (M : Finset (σ →₀ ℕ)) (z : ι → σ → ℤ) (H : ℝ) (hH : 1 ≤ H)
    (heval : ∀ i (m : M), |((m.val.prod (fun l e => z i l ^ e) : ℤ) : ℝ)| ≤ H) :
    ∃ G : M → MvPolynomial σ ℤ,
      (∀ j, (G j).support ⊆ M) ∧
      (∀ j m, |(((G j).coeff m : ℤ) : ℝ)| ≤ integralKernelHeight M.card H) ∧
      (∀ j i, MvPolynomial.eval (z i) (G j) = 0) ∧
      ∀ p : MvPolynomial σ F, p.support ⊆ M →
        (∀ i, MvPolynomial.eval (fun l => (z i l : F)) p = 0) →
        p ∈ Submodule.span F (Set.range (fun j => MvPolynomial.map (Int.castRingHom F) (G j))) := by
  classical
  let A : Matrix ι M ℤ := fun i m => m.val.prod (fun l e => z i l ^ e)
  obtain ⟨C, hAC, hC, hspan⟩ := exists_bounded_integral_kernel_spanning (F := F) A H hH heval
  let G : M → MvPolynomial σ ℤ := fun j => polynomialFromCoefficients M (fun m => C m j)
  refine ⟨G, (fun j => polynomialFromCoefficients_support M _), ?_, ?_, ?_⟩
  · intro j m
    by_cases hm : m ∈ M
    · change |(((polynomialFromCoefficients M (fun t => C t j)).coeff m : ℤ) : ℝ)| ≤ _
      rw [polynomialFromCoefficients_coeff M _ ⟨m, hm⟩]
      simpa only [Fintype.card_coe] using hC ⟨m, hm⟩ j
    · rw [show (G j).coeff m = 0 from polynomialFromCoefficients_coeff_of_not_mem M _ m hm]
      simp only [Int.cast_zero, abs_zero]
      dsimp [integralKernelHeight]
      positivity
  · intro j i
    rw [show G j = polynomialFromCoefficients M (fun m => C m j) from rfl,
      eval_polynomialFromCoefficients]
    exact congrArg (fun B => B i j) hAC
  · intro p hp hpz
    have hcast : A.map (Int.castRingHom F) =
        (fun i m => m.val.prod (fun l e => (z i l : F) ^ e) : Matrix ι M F) := by
      ext i m
      change ((m.val.prod (fun l e => z i l ^ e) : ℤ) : F) = _
      simp only [Finsupp.prod, Int.cast_prod, Int.cast_pow]
    have hker : (A.map (Int.castRingHom F)) *ᵥ (fun m => p.coeff m.val) = 0 := by
      rw [hcast]
      ext i
      change dotProduct (fun m : M => m.val.prod (fun l e => (z i l : F) ^ e))
        (fun m => p.coeff m.val) = 0
      rw [← eval_polynomialFromCoefficients, polynomialFromCoefficients_coefficients M p hp]
      exact hpz i
    have hh := Submodule.apply_mem_span_image_of_mem_span
      (polynomialFromCoefficients (R := F) M) (hspan _ hker)
    rw [polynomialFromCoefficients_coefficients M p hp] at hh
    have hG : (fun j => polynomialFromCoefficients (R := F) M (fun i => (C i j : F))) =
        (fun j => MvPolynomial.map (Int.castRingHom F) (G j)) := by
      funext j
      exact (polynomialFromCoefficients_map (Int.castRingHom F) M (fun i => C i j)).symm
    rw [← Set.range_comp] at hh
    change p ∈ Submodule.span F (Set.range (fun j =>
      polynomialFromCoefficients (R := F) M (fun i => (C i j : F)))) at hh
    rwa [hG] at hh

theorem monomial_eval_abs_le {σ : Type*} (z : σ → ℤ) (m : σ →₀ ℕ)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i, |(z i : ℝ)| ≤ H) (D : ℕ)
    (hD : monomialOrder m ≤ D) :
    |((m.prod (fun i e => z i ^ e) : ℤ) : ℝ)| ≤ H ^ D := by
  classical
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  rw [Finsupp.prod, Int.cast_prod, Finset.abs_prod]
  simp only [Int.cast_pow, abs_pow]
  calc
    (∏ i ∈ m.support, |(z i : ℝ)| ^ m i) ≤ ∏ i ∈ m.support, H ^ m i :=
      Finset.prod_le_prod (fun i _ => by positivity)
        (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hz i) _)
    _ = H ^ monomialOrder m := by simp [monomialOrder, Finsupp.sum, Finset.prod_pow_eq_pow_sum]
    _ ≤ H ^ D := pow_le_pow_right₀ hH hD

theorem exists_bounded_degree_vanishing_polynomials {σ ι F : Type*}
    [Fintype σ] [Fintype ι] [Field F] [CharZero F]
    (z : ι → σ → ℤ) (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H)
    (D : ℕ) :
    ∃ G : monomialsUpTo σ D → MvPolynomial σ ℤ,
      (∀ j, (G j).totalDegree ≤ D) ∧
      (∀ j m, |(((G j).coeff m : ℤ) : ℝ)| ≤
        integralKernelHeight ((D + Fintype.card σ).choose (Fintype.card σ)) (H ^ D)) ∧
      (∀ j i, MvPolynomial.eval (z i) (G j) = 0) ∧
      ∀ p : MvPolynomial σ F, p.totalDegree ≤ D →
        (∀ i, MvPolynomial.eval (fun l => (z i l : F)) p = 0) →
        p ∈ Submodule.span F (Set.range (fun j => MvPolynomial.map (Int.castRingHom F) (G j))) := by
  classical
  obtain ⟨G, hs, hc, he, hspan⟩ := exists_bounded_polynomial_kernel
    (F := F) (monomialsUpTo σ D) z (H ^ D) (one_le_pow₀ hH)
    (fun i m => monomial_eval_abs_le (z i) m.val H hH (hz i) D
      (mem_monomialsUpTo.mp m.property))
  refine ⟨G, ?_, ?_, he, ?_⟩
  · intro j
    rw [MvPolynomial.totalDegree, Finset.sup_le_iff]
    exact fun m hm => mem_monomialsUpTo.mp (hs j hm)
  · simpa only [card_monomialsUpTo] using hc
  · intro p hp heval
    apply hspan p _ heval
    intro m hm
    exact mem_monomialsUpTo.mpr ((MvPolynomial.le_totalDegree hm).trans hp)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_GenericCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
attribute [local instance] Classical.propDecidable

noncomputable def genericPoint {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    Fin n → FractionRing (MvPolynomial (Fin n) K ⧸ I) :=
  fun i => algebraMap _ _ (Ideal.Quotient.mk I (X i))

theorem aeval_genericPoint {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    aeval (genericPoint I) =
      (IsScalarTower.toAlgHom K (MvPolynomial (Fin n) K ⧸ I)
        (FractionRing (MvPolynomial (Fin n) K ⧸ I))).comp (Ideal.Quotient.mkₐ K I) := by
  ext i
  simp only [aeval_X, AlgHom.comp_apply]
  rfl

theorem aeval_genericPoint_eq_zero_iff {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) :
    aeval (genericPoint I) p = 0 ↔ p ∈ I := by
  rw [aeval_genericPoint]
  change algebraMap (MvPolynomial (Fin n) K ⧸ I)
    (FractionRing (MvPolynomial (Fin n) K ⧸ I)) (Ideal.Quotient.mk I p) = 0 ↔ _
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]

theorem aeval_jacobian_det {σ β K F : Type*} [Fintype β] [DecidableEq β]
    [CommRing K] [CommRing F] [Algebra K F]
    (z : σ → F) (v : β → σ) (G : β → MvPolynomial σ K) :
    aeval z (Matrix.det (fun i j => pderiv (v j) (G i))) =
      Matrix.det (fun i j => aeval z (pderiv (v j) (G i))) := by
  exact (aeval z).toRingHom.map_det (fun i j => pderiv (v j) (G i))

theorem bounded_patch_or_cut {n h D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ) (hP : P.natDegree ≤ h)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : (h.factorial : ℚ) * P.coeff h ≤ D)
    (j : Fin h → Fin n)
    (hj : AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))))
    (z : ι → Fin n → ℤ) (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    (∃ G : MvPolynomial (Fin n) ℤ,
      G.totalDegree ≤ D ∧
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤ integralKernelHeight ((D+n).choose n) (H^D)) ∧
      (∀ i, eval (z i) G = 0) ∧ MvPolynomial.map (Int.castRingHom K) G ∉ I) ∨
    (∃ J : Set (Fin n), Nat.card J = h ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) ℤ,
        (∀ i, (G i).totalDegree ≤ D) ∧
        (∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ integralKernelHeight ((D+n).choose n) (H^D)) ∧
        (∀ i, MvPolynomial.map (Int.castRingHom K) (G i) ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (MvPolynomial.map (Int.castRingHom K) (G i))) ∉ I) := by
  classical
  obtain ⟨G,hGdeg,hGheight,hGvan,hGspan⟩ :=
    exists_bounded_degree_vanishing_polynomials (F := K) z H hH hz D
  simp only [Fintype.card_fin] at hGheight
  by_cases hGI : ∀ a, MvPolynomial.map (Int.castRingHom K) (G a) ∈ I
  · right
    obtain ⟨J,hJ,P₁,hPdeg,hPI,hPdet⟩ := bounded_generic_jacobian I P hP hT hD j hj
    have hspan (i : ↥(Jᶜ)) : P₁ i ∈ Submodule.span K
        (Set.range (fun a => MvPolynomial.map (Int.castRingHom K) (G a))) :=
      hGspan (P₁ i) (hPdeg i) (hzI (P₁ i) (hPI i))
    have hdet : Matrix.det (fun i l : ↥(Jᶜ) =>
        aeval (genericPoint I) (pderiv l.val (P₁ i))) ≠ 0 := by
      rw [← aeval_jacobian_det]
      exact mt (aeval_genericPoint_eq_zero_iff I _).mp hPdet
    obtain ⟨a,_,ha⟩ := exists_nonsingular_jacobian_of_span
      (genericPoint I) (fun l : ↥(Jᶜ) => l.val)
      (fun a => MvPolynomial.map (Int.castRingHom K) (G a)) P₁ hspan hdet
    refine ⟨J,hJ,(fun i => G (a i)),(fun i => hGdeg (a i)),
      (fun i => hGheight (a i)),(fun i => hGI (a i)),?_⟩
    intro hm
    apply ha
    rw [← aeval_jacobian_det]
    exact (aeval_genericPoint_eq_zero_iff I _).mpr hm
  · left
    obtain ⟨a,ha⟩ := not_forall.mp hGI
    exact ⟨G a,hGdeg a,hGheight a,hGvan a,ha⟩

end

open MvPolynomial

theorem pderiv_degree_le_sub_one {σ R : Type*} [CommSemiring R]
    (p : MvPolynomial σ R) (D : ℕ) (hp : p.totalDegree ≤ D) (i : σ) :
    (pderiv i p).totalDegree ≤ D-1 := by
  by_cases he : pderiv i p = 0
  · simp [he]
  · have hd := pderiv_totalDegree_lt i p he
    omega

theorem jacobian_minor_degree {σ β R : Type*} [Fintype β] [DecidableEq β]
    [CommRing R] (G : β → MvPolynomial σ R) (v : β → σ)
    (D : ℕ) (hG : ∀ i, (G i).totalDegree ≤ D) :
    (Matrix.det (fun i j => pderiv (v j) (G i))).totalDegree ≤
      Fintype.card β * (D-1) := by
  classical
  let M : Matrix β β (MvPolynomial σ R) := fun i j => pderiv (v j) (G i)
  change M.det.totalDegree ≤ _
  rw [Matrix.det_apply]
  apply (totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro e _
  apply (totalDegree_smul_le _ _).trans
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i : β, (pderiv (v i) (G (e i))).totalDegree ≤ ∑ _i : β, (D-1) :=
      Finset.sum_le_sum (fun i _ => pderiv_degree_le_sub_one _ D (hG _) _)
    _ = Fintype.card β * (D-1) := by simp

theorem coordinate_transcendence_basis {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] :
    ∃ m : ℕ, ∃ j : Fin m → Fin n,
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (MvPolynomial.X (j a))) ∧
      Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) = m := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let x : Fin n → A := fun i => Ideal.Quotient.mk I (MvPolynomial.X i)
  have hx : MvPolynomial.aeval x = Ideal.Quotient.mkₐ K I := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [MvPolynomial.aeval_X]
    rfl
  have hg : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [Algebra.adjoin_range_eq_range_aeval, hx]
    exact (AlgHom.range_eq_top _).mpr Ideal.Quotient.mk_surjective
  have : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range x)) A := by
    rw [hg]
    constructor
    intro a
    exact isAlgebraic_algebraMap (R := (⊤ : Subalgebra K A)) ⟨a, trivial⟩
  obtain ⟨t, ht, htb⟩ := exists_isTranscendenceBasis_subset (R := K) (A := A) (Set.range x)
  have htfin : t.Finite := (Set.finite_range x).subset ht
  let : Fintype t := htfin.fintype
  let e : Fin (Fintype.card t) ≃ t := (Fintype.equivFin t).symm
  choose j hj using fun a : Fin (Fintype.card t) => ht (e a).property
  refine ⟨Fintype.card t, j, ?_, ?_⟩
  · have hi := htb.1.comp e e.injective
    simpa only [Function.comp_def, ← hj] using hi
  · rw [← htb.cardinalMk_eq_trdeg, Cardinal.mk_fintype]

theorem hilbert_natDegree_eq_trdeg {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (P : Polynomial ℚ)
    (hT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ)) : (P.natDegree : Cardinal) = Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) := by
  obtain ⟨Q,j,_,hj,_,T₀,hQ⟩ := coordinate_hilbert_degree_independent I Ideal.IsPrime.ne_top'
  have hQN : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        Q.eval (T : ℚ) := Filter.eventually_atTop.mpr ⟨T₀,hQ⟩
  have hPN : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ P.eval (T : ℚ) := hT.mono (fun T ht => by
    rw [← ht]; positivity)
  have hQNN : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Q.eval (T : ℚ) := hQN.mono (fun T ht => by
    rw [← ht]; positivity)
  have heval : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) = Q.eval (T : ℚ) := by
    filter_upwards [hT,hQN] with T hp hq
    exact hp.symm.trans hq
  have hPQ : P.natDegree = Q.natDegree := le_antisymm
    (natDegree_le_of_eventually_nat_eval_bounds P Q hPN (heval.mono fun _ ht => ht.le))
    (natDegree_le_of_eventually_nat_eval_bounds Q P hQNN (heval.mono fun _ ht => ht.ge))
  obtain ⟨m, z, hz, hm⟩ := coordinate_transcendence_basis I
  have h1 : (P.natDegree : Cardinal) ≤ Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ I) := by
    rw [hPQ]
    simpa using hj.lift_cardinalMk_le_trdeg
  have h2 : m ≤ P.natDegree := by
    by_contra hh
    have hm' : P.natDegree+1 ≤ m := by omega
    let v : Fin (P.natDegree+1) → Fin n := fun a => z (Fin.castLE hm' a)
    exact not_independent_over_hilbert_degree I P le_rfl hT v
      (hz.comp (Fin.castLE hm') (Fin.castLE_injective hm'))
  rw [hm] at h1 ⊢
  exact le_antisymm h1 (by exact_mod_cast h2)

theorem proper_cut_hilbert_inequality {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (T : ℕ) (hT : p.totalDegree ≤ T) :
    Module.finrank K ((totalSpace T).map
      (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) +
      Module.finrank K ((totalSpace (T-p.totalDegree)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  classical
  let A := MvPolynomial (Fin n) K ⧸ I
  let J := I ⊔ Ideal.span {p}
  let F := (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let G := (totalSpace (T-p.totalDegree)).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let := totalSpace_finite (n := n) (K := K) T
  let := totalSpace_finite (n := n) (K := K) (T-p.totalDegree)
  let f := (Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left)).toLinearMap.domRestrict F
  let g : G →ₗ[K] F :=
    { toFun := fun x => ⟨Ideal.Quotient.mk I p * x.val, by
        obtain ⟨q, hq, hqx⟩ := x.property
        refine ⟨p*q, ?_, ?_⟩
        · apply mem_totalSpace.mpr
          exact (totalDegree_mul p q).trans ((Nat.add_le_add_left (mem_totalSpace.mp hq) _).trans
            (by omega))
        · change Ideal.Quotient.mk I (p*q) = _
          rw [map_mul]
          exact congrArg (fun y => Ideal.Quotient.mk I p * y) hqx⟩
      map_add' := by intros; ext; simp [mul_add]
      map_smul' := by intros; ext; simp }
  have hpn : Ideal.Quotient.mk I p ≠ 0 := by
    exact fun h => hp (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hg : Function.Injective g := by
    intro x y h
    exact Subtype.ext (mul_left_cancel₀ hpn (congrArg Subtype.val h))
  have hgle : LinearMap.range g ≤ LinearMap.ker f := by
    rintro x ⟨y, rfl⟩
    change (Ideal.Quotient.factorₐ K (show I ≤ J from le_sup_left))
      (Ideal.Quotient.mk I p * y.val) = 0
    rw [map_mul]
    have hpJ : Ideal.Quotient.mk J p = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      exact (le_sup_right : Ideal.span {p} ≤ J) (Ideal.subset_span (Set.mem_singleton p))
    change Ideal.Quotient.mk J p * _ = 0
    rw [hpJ, zero_mul]
  have hk : Module.finrank K G ≤ Module.finrank K (LinearMap.ker f) := by
    rw [← LinearMap.finrank_range_of_inj hg]
    exact Submodule.finrank_mono hgle
  have hdim := f.finrank_range_add_finrank_ker
  have hr : LinearMap.range f = (totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext z
    constructor
    · rintro ⟨⟨y, q, hq, rfl⟩, rfl⟩
      exact ⟨q, hq, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      refine ⟨⟨Ideal.Quotient.mk I q, ⟨q, hq, rfl⟩⟩, rfl⟩
  rw [hr] at hdim
  exact (Nat.add_le_add_left hk _).trans_eq hdim

theorem coeff_taylor_high (P : Polynomial ℚ) (a : ℚ) (n : ℕ)
    (hn : P.natDegree ≤ n) : (Polynomial.taylor a P).coeff n = P.coeff n := by
  obtain h | rfl := lt_or_eq_of_le hn
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (p := Polynomial.taylor a P) (by simpa using h),
      Polynomial.coeff_eq_zero_of_natDegree_lt h]
  · rw [Polynomial.coeff_taylor_natDegree, Polynomial.coeff_natDegree]

theorem hilbert_difference_degree (P : Polynomial ℚ) (a : ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h+1) : (P - Polynomial.taylor a P).natDegree ≤ h := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [Polynomial.coeff_sub, coeff_taylor_high P a n (by omega), sub_self]

theorem hilbert_difference_coeff (P : Polynomial ℚ) (a : ℚ) (h : ℕ)
    (hP : P.natDegree ≤ h+1) :
    (P - Polynomial.taylor (-a) P).coeff h = a * (h+1) * P.coeff (h+1) := by
  have hn : (Polynomial.hasseDeriv h P).natDegree ≤ 1 :=
    (Polynomial.natDegree_hasseDeriv_le P h).trans (by omega)
  rw [Polynomial.coeff_sub, Polynomial.taylor_coeff,
    Polynomial.eq_X_add_C_of_natDegree_le_one hn]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.hasseDeriv_coeff, zero_add, Nat.choose_self,
    Nat.cast_one, one_mul]
  rw [Nat.add_comm 1 h, Nat.choose_succ_self_right]
  push_cast
  ring

theorem proper_cut_hilbert_polynomial {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (P Q : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) =
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap))
    (hQ : ∀ᶠ T : ℕ in Filter.atTop, Q.eval (T : ℚ) =
      Module.finrank K ((totalSpace T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap))
    (h : ℕ) (hdeg : P.natDegree ≤ h+1) :
    Q.natDegree ≤ h ∧ Q.coeff h ≤ (p.totalDegree : ℚ) * (h+1) * P.coeff (h+1) := by
  let D := P - Polynomial.taylor (-(p.totalDegree : ℚ)) P
  have hD : D.natDegree ≤ h := hilbert_difference_degree P _ h hdeg
  have hn : ∀ᶠ T : ℕ in Filter.atTop, 0 ≤ Q.eval (T : ℚ) := hQ.mono (fun T hT => by
    rw [hT]; positivity)
  have hl : ∀ᶠ T : ℕ in Filter.atTop, Q.eval (T : ℚ) ≤ D.eval (T : ℚ) := by
    have hs := (Filter.tendsto_sub_atTop_nat p.totalDegree).eventually hP
    filter_upwards [hP, hQ, hs, Filter.eventually_ge_atTop p.totalDegree] with T hPT hQT hPS hT
    have hi := proper_cut_hilbert_inequality I p hp T hT
    have hie : (Module.finrank K ((totalSpace T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) +
      Module.finrank K ((totalSpace (T-p.totalDegree)).map
        (Ideal.Quotient.mkₐ K I).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
      exact_mod_cast hi
    dsimp [D]
    rw [Polynomial.eval_sub, Polynomial.taylor_eval, ← sub_eq_add_neg,
      ← Nat.cast_sub hT, hPT, hQT, hPS]
    exact le_sub_iff_add_le.mpr hie
  have hdQ := (natDegree_le_of_eventually_nat_eval_bounds Q D hn hl).trans hD
  refine ⟨hdQ, ?_⟩
  have hc := coeff_le_of_eventually_nat_eval_le Q D h hdQ hD hl
  exact hc.trans_eq (hilbert_difference_coeff P (p.totalDegree : ℚ) h hdeg)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PureCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree

section
open Algebra

theorem prime_height_le_of_goingDown {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.HasGoingDown R S]
    (p : Ideal R) [p.IsPrime] [p.FiniteHeight]
    (P : Ideal S) [P.IsPrime] [P.LiesOver p] : p.height ≤ P.height := by
  obtain ⟨l, hl, hn⟩ := p.exists_ltSeries_length_eq_height
  have hlp : l.last.asIdeal = p := congrArg PrimeSpectrum.asIdeal hl
  have : P.LiesOver l.last.asIdeal := hlp.symm ▸ (inferInstance : P.LiesOver p)
  obtain ⟨L, hL, hlast, _⟩ := Ideal.exists_ltSeries_of_hasGoingDown l P
  have hlength : (L.length : ℕ∞) ≤ Order.height L.last := Order.length_le_height (show L.last ≤ L.last from le_rfl)
  have hh : Order.height L.last = P.height :=
    (congrArg Order.height hlast).trans (PrimeSpectrum.height_eq_orderHeight _).symm
  calc
    p.height = (l.length : ℕ∞) := hn.symm
    _ = (L.length : ℕ∞) := congrArg Nat.cast hL.symm
    _ ≤ P.height := hlength.trans_eq hh

theorem mvPolynomial_maximal_height {K : Type*} [Field K]
    (n : ℕ) (P : Ideal (MvPolynomial (Fin n) K)) [P.IsMaximal] : P.height = n := by
  induction n with
  | zero =>
    have hdim := MvPolynomial.ringKrullDim_of_isNoetherianRing (ι := Fin 0) (R := K)
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := P) Ideal.IsPrime.ne_top'
    simp only [ENat.card_eq_coe_fintype_card, Nat.card_eq_fintype_card, Fintype.card_fin, zero_add, Nat.cast_zero,
      ringKrullDim_eq_zero_of_field] at hdim
    rw [hdim] at h
    exact le_antisymm (by exact_mod_cast h) (zero_le)
  | succ n ih =>
    let e := (MvPolynomial.finSuccEquiv K n).toRingEquiv
    let Q := P.map e
    have : Q.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q : Ideal (MvPolynomial (Fin n) K) := Q.comap Polynomial.C
    have : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing Q
    have he : Q.height = P.height := e.height_map P
    have hq : Q.LiesOver q := ⟨rfl⟩
    rw [← he, Polynomial.height_eq_height_add_one q Q, ih q, Nat.cast_add, Nat.cast_one]

theorem normalization_size_le_maximal_height {K A : Type*} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective g) (hi : g.IsIntegral)
    (P : Ideal A) [P.IsMaximal] : (s : ℕ∞) ≤ P.height := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have : Algebra.IsIntegral R A := ⟨hi⟩
  let p : Ideal R := P.under R
  have : p.IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := R) (S := A) P
  rw [← mvPolynomial_maximal_height s p]
  exact prime_height_le_of_goingDown p P

theorem normalization_trdeg {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] (s : ℕ) (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective g) (hi : g.IsIntegral) : trdeg K A = s := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  have : Algebra.IsIntegral R A := ⟨hi⟩
  have : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (g.commutes x).symm)
  have h := trdeg_add_eq K R (A := A)
  have hz : trdeg R A = 0 := trdeg_eq_zero_iff.mpr inferInstance
  rw [hz, add_zero] at h
  rw [← h, MvPolynomial.trdeg_of_isDomain]
  simp

theorem finite_type_trdeg_le_maximal_height {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (P : Ideal A) [P.IsMaximal] :
    ∃ s : ℕ, trdeg K A = s ∧ (s : ℕ∞) ≤ P.height := by
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K A
  exact ⟨s, normalization_trdeg s g hg hi,
    normalization_size_le_maximal_height s g hg hi P⟩

theorem trdeg_le_one_of_principal_maximal {K A : Type u} [Field K] [CommRing A]
    [IsDomain A] [Algebra K A] [Algebra.FiniteType K A]
    (p : A) (P : Ideal A) [P.IsMaximal]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) : trdeg K A ≤ 1 := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing K A
  obtain ⟨s, hs, hheight⟩ := finite_type_trdeg_le_maximal_height (K := K) P
  have hle := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) P hP
  rw [hs]
  have hn : s ≤ 1 := by exact_mod_cast hheight.trans hle
  exact_mod_cast hn

open scoped nonZeroDivisors

theorem localized_algebraic_prime_isMaximal
    {R A F B : Type u} [CommRing R] [IsDomain R] [CommRing A] [IsDomain A]
    [Field F] [CommRing B] [Algebra R A] [Algebra R F] [IsFractionRing R F]
    [Algebra A B] [Algebra R B] [Algebra F B]
    [IsScalarTower R A B] [IsScalarTower R F B]
    [IsLocalization (Algebra.algebraMapSubmonoid A R⁰) B]
    (P : Ideal A) [P.IsPrime]
    [FaithfulSMul R (A ⧸ P)] [Algebra.IsAlgebraic R (A ⧸ P)] :
    (P.map (algebraMap A B)).IsMaximal := by
  let M := Algebra.algebraMapSubmonoid A R⁰
  have hdis : Disjoint (M : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨r, hr, rfl⟩ ha
    have hzero : algebraMap R (A ⧸ P) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    have hr0 : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    exact hr0 ((FaithfulSMul.algebraMap_injective R (A ⧸ P))
      (hzero.trans (map_zero _).symm))
  let Q := P.map (algebraMap A B)
  have : Q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M B P inferInstance hdis
  let C := B ⧸ Q
  let f : A →ₐ[R] C := (Ideal.Quotient.mkₐ R Q).comp (IsScalarTower.toAlgHom R A B)
  let g : (A ⧸ P) →ₐ[R] C := Ideal.Quotient.liftₐ P f (by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha))
  have hnum (a : A) : IsAlgebraic F (f a) := by
    have hr := IsAlgebraic.algHom g (Algebra.IsAlgebraic.isAlgebraic (R := R) (Ideal.Quotient.mk P a))
    exact hr.extendScalars (FaithfulSMul.algebraMap_injective R F)
  have h_alg : Algebra.IsAlgebraic F C := by
    constructor
    intro c
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨⟨a,s⟩, hs⟩ := IsLocalization.surj M b
    obtain ⟨r, hr, hsr⟩ := s.property
    have hrn : r ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hr
    have hrF : algebraMap R F r ≠ 0 := by simpa using (IsFractionRing.injective R F).ne hrn
    have hrel : Ideal.Quotient.mk Q b * algebraMap F C (algebraMap R F r) = f a := by
      change Ideal.Quotient.mk Q b * Ideal.Quotient.mk Q (algebraMap F B (algebraMap R F r)) = _
      rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R A B, hsr,
        ← map_mul, hs]
      rfl
    have hc : Ideal.Quotient.mk Q b = f a * algebraMap F C (algebraMap R F r)⁻¹ := by
      rw [← hrel, mul_assoc, ← map_mul, mul_inv_cancel₀ hrF, map_one, mul_one]
    rw [hc]
    exact (hnum a).mul (isAlgebraic_algebraMap _)
  have : Algebra.IsIntegral F C := Algebra.IsAlgebraic.isIntegral
  exact Ideal.Quotient.maximal_of_isField Q (isField_of_isIntegral_of_isField' (Field.toIsField F))

open scoped TensorProduct nonZeroDivisors

theorem principal_minimal_trdeg_bound_of_normalization
    {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : A) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) (s : ℕ)
    (g : MvPolynomial (Fin s) K →ₐ[K] A)
    (hg : Function.Injective ((Ideal.Quotient.mkₐ K P).comp g))
    (hi : ((Ideal.Quotient.mkₐ K P).comp g).IsIntegral) :
    Algebra.trdeg K A ≤ (s : Cardinal) + 1 := by
  let R := MvPolynomial (Fin s) K
  let : Algebra R A := g.toRingHom.toAlgebra
  have hga : Function.Injective g := Function.Injective.of_comp hg
  have : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hga
  have : FaithfulSMul R (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective R (A ⧸ P)).mpr hg
  have : Algebra.IsIntegral R (A ⧸ P) := ⟨hi⟩
  have : IsScalarTower K R A := IsScalarTower.of_algebraMap_eq' (by
    ext x
    exact (g.commutes x).symm)
  have : Algebra.FiniteType R A := Algebra.FiniteType.of_restrictScalars_finiteType K R A
  let F := FractionRing R
  let B := F ⊗[R] A
  let : Algebra A B := Algebra.TensorProduct.rightAlgebra
  let M := Algebra.algebraMapSubmonoid A R⁰
  have hM : M ≤ A⁰ := by
    rintro a ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    simpa using (FaithfulSMul.algebraMap_injective R A).ne (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  have : IsDomain B := IsLocalization.isDomain_of_le_nonZeroDivisors B hM
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).mpr
    (IsLocalization.injective B hM)
  let Q := P.map (algebraMap A B)
  have : Q.IsMaximal := localized_algebraic_prime_isMaximal (R := R) (F := F) P
  have hdis : Disjoint (M : Set A) (P : Set A) := by
    rw [Set.disjoint_left]
    rintro a ⟨r, hr, rfl⟩ ha
    have hz : algebraMap R (A ⧸ P) r = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (mem_nonZeroDivisors_iff_ne_zero.mp hr)
      ((FaithfulSMul.algebraMap_injective R (A ⧸ P)) (hz.trans (map_zero _).symm))
  have hQP : Q.under A = P :=
    IsLocalization.under_map_of_isPrime_disjoint M B inferInstance hdis
  have hm : Q ∈ (Ideal.span {algebraMap A B p}).minimalPrimes := by
    rw [← Set.image_singleton, ← Ideal.map_span, IsLocalization.minimalPrimes_map M B]
    simpa only [Set.mem_preimage, hQP] using hP
  have hFB : Algebra.trdeg F B ≤ 1 := trdeg_le_one_of_principal_maximal
    (algebraMap A B p) Q hm
  have : IsScalarTower K A B := IsScalarTower.of_algebraMap_eq (fun k => by
    rw [IsScalarTower.algebraMap_apply K R B, IsScalarTower.algebraMap_apply K R A,
      IsScalarTower.algebraMap_apply R A B])
  have : Algebra.IsAlgebraic A B := IsLocalization.isAlgebraic B M
  have hAB := trdeg_add_eq K A (A := B)
  rw [trdeg_eq_zero (R := A) (A := B), add_zero] at hAB
  have : Algebra.IsAlgebraic R F := IsLocalization.isAlgebraic F R⁰
  have hRF := trdeg_add_eq K R (A := F)
  rw [trdeg_eq_zero (R := R) (A := F), add_zero, MvPolynomial.trdeg_of_isDomain] at hRF
  have hRF' : Algebra.trdeg K F = (s : Cardinal) := by simpa using hRF.symm
  have : FaithfulSMul F B := (faithfulSMul_iff_algebraMap_injective F B).mpr
    (algebraMap F B).injective
  have hBF := trdeg_add_eq K F (A := B)
  rw [hRF'] at hBF
  rw [hAB, ← hBF]
  exact add_le_add_right hFB _

theorem principal_minimal_trdeg_bound
    {K A : Type u} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    [Algebra.FiniteType K A] (p : A) (P : Ideal A) [P.IsPrime]
    (hP : P ∈ (Ideal.span {p}).minimalPrimes) :
    Algebra.trdeg K A ≤ Algebra.trdeg K (A ⧸ P) + 1 := by
  classical
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K (A ⧸ P)
  choose x hx using fun i : Fin s => Ideal.Quotient.mk_surjective (g (MvPolynomial.X i))
  let G : MvPolynomial (Fin s) K →ₐ[K] A := MvPolynomial.aeval x
  have he : (Ideal.Quotient.mkₐ K P).comp G = g := by
    apply MvPolynomial.algHom_ext
    intro i
    simpa only [G, AlgHom.comp_apply, MvPolynomial.aeval_X, Ideal.Quotient.mkₐ_eq_mk] using hx i
  have hG : Function.Injective ((Ideal.Quotient.mkₐ K P).comp G) := he.symm ▸ hg
  have hI : ((Ideal.Quotient.mkₐ K P).comp G).IsIntegral := he.symm ▸ hi
  rw [normalization_trdeg s g hg hi]
  exact principal_minimal_trdeg_bound_of_normalization p P hP s G hG hI

end
open MvPolynomial

theorem quotient_hilbert_le {n : ℕ} {K : Type*} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) (hIJ : I ≤ J) (T : ℕ) :
    Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) ≤
      Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) := by
  let F := (totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap
  let := totalSpace_finite (n := n) (K := K) T
  let f := (Ideal.Quotient.factorₐ K hIJ).toLinearMap.domRestrict F
  have hr : LinearMap.range f = (totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap := by
    ext z
    constructor
    · rintro ⟨⟨y,q,hq,rfl⟩,rfl⟩
      exact ⟨q,hq,rfl⟩
    · rintro ⟨q,hq,rfl⟩
      exact ⟨⟨Ideal.Quotient.mk I q,⟨q,hq,rfl⟩⟩,rfl⟩
  rw [← hr]
  exact LinearMap.finrank_range_le f

theorem cut_minimal_hilbert_codim_le_one {n : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes)
    (P S : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
        P.eval (T : ℚ))
    (hS : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) : ℚ) =
        S.eval (T : ℚ)) : P.natDegree ≤ S.natDegree + 1 := by
  let A := MvPolynomial (Fin n) K ⧸ I
  let q := Q.map (Ideal.Quotient.mk I)
  have hIQ : I ≤ Q := le_sup_left.trans hQ.le
  have hq : q ∈ (Ideal.span {Ideal.Quotient.mk I p}).minimalPrimes := by
    rw [← Set.image_singleton, ← Ideal.map_span,
      Ideal.minimalPrimes_map_of_surjective Ideal.Quotient.mk_surjective, Ideal.mk_ker,
      sup_comm]
    exact ⟨Q,hQ,rfl⟩
  have : q.IsPrime := hq.isPrime
  have hi := principal_minimal_trdeg_bound (K := K) (Ideal.Quotient.mk I p) q hq
  let e : (A ⧸ q) ≃ₐ[K] (MvPolynomial (Fin n) K ⧸ Q) :=
    DoubleQuot.quotQuotEquivQuotOfLEₐ K hIQ
  have he : Algebra.trdeg K (A ⧸ q) = Algebra.trdeg K (MvPolynomial (Fin n) K ⧸ Q) :=
    AlgEquiv.trdeg_eq e
  rw [he, ← hilbert_natDegree_eq_trdeg I P hP, ← hilbert_natDegree_eq_trdeg Q S hS] at hi
  exact_mod_cast hi

theorem proper_cut_hilbert_purity {n h : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes)
    (P D S : Polynomial ℚ)
    (hP : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) = P.eval (T : ℚ))
    (hD : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map
        (Ideal.Quotient.mkₐ K (I ⊔ Ideal.span {p})).toLinearMap) : ℚ) = D.eval (T : ℚ))
    (hS : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) : ℚ) = S.eval (T : ℚ))
    (hdeg : P.natDegree = h+1) : S.natDegree = h := by
  have hd := (proper_cut_hilbert_polynomial I p hp P D (hP.mono fun _ ht => ht.symm)
    (hD.mono fun _ ht => ht.symm) h hdeg.le).1
  have hs : S.natDegree ≤ D.natDegree := by
    apply natDegree_le_of_eventually_nat_eval_bounds S D
    · exact hS.mono fun T ht => ht ▸ (show (0 : ℚ) ≤ Module.finrank K
        ((totalSpace T).map (Ideal.Quotient.mkₐ K Q).toLinearMap) from Nat.cast_nonneg _)
    · filter_upwards [hS,hD] with T ht hd
      rw [← ht,← hd]
      exact_mod_cast quotient_hilbert_le (I ⊔ Ideal.span {p}) Q hQ.le T
  have hl := cut_minimal_hilbert_codim_le_one I Q p hQ P S hP hS
  omega

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_DegreeBudgets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

theorem minimal_prime_separators {R ι : Type*} [CommRing R] [Fintype ι]
    (J : Ideal R) (P : ι → Ideal R) (hP : ∀ i, P i ∈ J.minimalPrimes)
    (hPi : Function.Injective P) :
    ∃ b : ι → R, (∀ i, b i ∉ P i) ∧ (∀ i j, i ≠ j → b i ∈ P j) := by
  classical
  have hex : ∀ i j : ι, i ≠ j → ∃ a : R, a ∈ P j ∧ a ∉ P i := by
    intro i j hij
    by_contra hh
    have hji : P j ≤ P i := by
      intro a ha
      by_contra hn
      exact hh ⟨a,ha,hn⟩
    have he : P i = P j := le_antisymm ((hP i).2 (hP j).1 hji) hji
    exact hij (hPi he)
  choose a ha using hex
  let b : ι → R := fun i => ∏ j : {j : ι // i ≠ j}, a i j j.property
  refine ⟨b,?_,?_⟩
  · intro i
    have : (P i).IsPrime := (hP i).isPrime
    simp only [b, Ideal.IsPrime.prod_mem_iff, Finset.mem_univ, true_and, not_exists]
    intro j
    exact (ha i j j.property).2
  · intro i j hij
    have : (P j).IsPrime := (hP j).isPrime
    exact Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨j,hij⟩,Finset.mem_univ _,(ha i j hij).1⟩

theorem component_hilbert_sum_le_shift {n : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (J : Ideal (MvPolynomial (Fin n) K))
    (P : ι → Ideal (MvPolynomial (Fin n) K)) (hPr : ∀ i, (P i).IsPrime)
    (hJP : ∀ i, J ≤ P i) (b : ι → MvPolynomial (Fin n) K)
    (hb : ∀ i, b i ∉ P i) (hsep : ∀ i j, i ≠ j → b i ∈ P j)
    (B T : ℕ) (hB : ∀ i, (b i).totalDegree ≤ B) :
    (∑ i, Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap)) ≤
      Module.finrank K ((totalSpace (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap) := by
  classical
  let V := fun i => (totalSpace T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap
  let W := (totalSpace (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap
  let f : ∀ i, totalSpace (σ := Fin n) (K := K) T →ₗ[K] V i := fun i =>
    { toFun := fun x => ⟨Ideal.Quotient.mk (P i) x.val, ⟨x.val,x.property,rfl⟩⟩
      map_add' := by intros; ext; simp
      map_smul' := by
        intro c x
        apply Subtype.ext
        exact (Ideal.Quotient.mkₐ K (P i)).toLinearMap.map_smul c x.val }
  have hf : ∀ i, LinearMap.range (f i) = ⊤ := by
    intro i
    apply LinearMap.range_eq_top.mpr
    rintro ⟨y,p,hp,hpy⟩
    exact ⟨⟨p,hp⟩,Subtype.ext hpy⟩
  let (i : ι) : Module.Free K (V i) := Module.Free.of_divisionRing K (V i)
  let (i : ι) : Module.Projective K (V i) := Module.Projective.of_free
  choose l hl using fun i => (f i).exists_rightInverse_of_surjective (hf i)
  have hli : ∀ i (x : V i), Ideal.Quotient.mk (P i) (l i x).val = x.val := by
    intro i x
    exact congrArg Subtype.val (LinearMap.congr_fun (hl i) x)
  let L : (∀ i, V i) →ₗ[K] W :=
    { toFun := fun x => ⟨Ideal.Quotient.mk J (∑ i, b i * (l i (x i)).val), by
        refine ⟨∑ i, b i * (l i (x i)).val, ?_, rfl⟩
        apply Submodule.sum_mem
        intro i _
        apply mem_totalSpace.mpr
        exact (totalDegree_mul _ _).trans ((Nat.add_le_add (hB i)
          (mem_totalSpace.mp (l i (x i)).property)).trans_eq (Nat.add_comm B T))⟩
      map_add' := by
        intro x y
        apply Subtype.ext
        simp only [Pi.add_apply, map_add, AddMemClass.coe_add, mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c x
        apply Subtype.ext
        simp only [Pi.smul_apply, map_smul, SetLike.val_smul, mul_smul_comm,
          ← Finset.smul_sum]
        exact (Ideal.Quotient.mkₐ K J).toLinearMap.map_smul c _ }
  have hL : Function.Injective L := by
    intro x y hxy
    funext i
    have : (P i).IsPrime := hPr i
    apply Subtype.ext
    have hh := congrArg (fun z : W => Ideal.Quotient.factor (hJP i) z.val) hxy
    change Ideal.Quotient.mk (P i) (∑ j, b j * (l j (x j)).val) =
      Ideal.Quotient.mk (P i) (∑ j, b j * (l j (y j)).val) at hh
    have hs (z : ∀ j, V j) : Ideal.Quotient.mk (P i) (∑ j, b j * (l j (z j)).val) =
        Ideal.Quotient.mk (P i) (b i) * (z i).val := by
      rw [map_sum, Finset.sum_eq_single i, map_mul, hli]
      · intro j _ hji
        rw [map_mul, Ideal.Quotient.eq_zero_iff_mem.mpr (hsep j i hji),zero_mul]
      · simp
    rw [hs, hs] at hh
    exact mul_left_cancel₀ (fun hz => hb i (Ideal.Quotient.eq_zero_iff_mem.mp hz)) hh
  let := totalSpace_finite (n := n) (K := K) T
  let := totalSpace_finite (n := n) (K := K) (T+B)
  simpa only [Module.finrank_pi_fintype] using LinearMap.finrank_le_finrank_of_injective hL

theorem component_hilbert_coeff_sum_le {n h : ℕ} {K ι : Type*} [Field K] [Fintype ι]
    (J : Ideal (MvPolynomial (Fin n) K))
    (P : ι → Ideal (MvPolynomial (Fin n) K)) (hPr : ∀ i, P i ∈ J.minimalPrimes)
    (hPi : Function.Injective P) (D : Polynomial ℚ) (S : ι → Polynomial ℚ)
    (hD : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K J).toLinearMap) : ℚ) = D.eval (T : ℚ))
    (hS : ∀ i, ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K (P i)).toLinearMap) : ℚ) = (S i).eval (T : ℚ))
    (hdD : D.natDegree ≤ h) (hdS : ∀ i, (S i).natDegree ≤ h) :
    ∑ i, (S i).coeff h ≤ D.coeff h := by
  classical
  obtain ⟨b,hb,hsep⟩ := minimal_prime_separators J P hPr hPi
  let B := Finset.univ.sup (fun i => (b i).totalDegree)
  have hB : ∀ i, (b i).totalDegree ≤ B := fun i => Finset.le_sup (f := fun i => (b i).totalDegree) (Finset.mem_univ i)
  have hsum : (∑ i, S i).natDegree ≤ h :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i _ => hdS i)
  have hshift : (Polynomial.taylor (B : ℚ) D).natDegree ≤ h := by simpa using hdD
  have hDT : ∀ᶠ T : ℕ in Filter.atTop,
      (Module.finrank K ((totalSpace (T+B)).map (Ideal.Quotient.mkₐ K J).toLinearMap) : ℚ) =
        D.eval ((T+B : ℕ) : ℚ) := by
    obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hD
    exact Filter.eventually_atTop.mpr ⟨N,fun T hT => hN (T+B) (by omega)⟩
  have hle : ∀ᶠ T : ℕ in Filter.atTop,
      (∑ i, S i).eval (T : ℚ) ≤ (Polynomial.taylor (B : ℚ) D).eval (T : ℚ) := by
    filter_upwards [Filter.eventually_all.mpr hS,hDT] with T hs hd
    rw [Polynomial.eval_finsetSum,Polynomial.taylor_eval,← Nat.cast_add,← hd]
    simp_rw [← hs]
    exact_mod_cast component_hilbert_sum_le_shift J P (fun i => (hPr i).isPrime)
      (fun i => (hPr i).le) b hb hsep B T hB
  have hc := coeff_le_of_eventually_nat_eval_le (∑ i, S i) (Polynomial.taylor (B : ℚ) D)
    h hsum hshift hle
  rw [coeff_taylor_high D (B : ℚ) h hdD] at hc
  simpa only [Polynomial.finsetSum_coeff] using hc

theorem polynomial_eq_of_eventually_nat_eval_eq (P Q : Polynomial ℚ)
    (he : ∀ᶠ T : ℕ in Filter.atTop, P.eval (T : ℚ) = Q.eval (T : ℚ)) : P = Q := by
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp he
  apply Polynomial.eq_of_infinite_eval_eq
  apply ((Set.Ici_infinite N).image (Nat.cast_injective (R := ℚ)).injOn).mono
  rintro _ ⟨T,hT,rfl⟩
  exact hN T hT

noncomputable def coordinateHilbert {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : Polynomial ℚ :=
  (coordinate_hilbert_eventually_polynomial I).choose

noncomputable def affineDimension {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ℕ := (coordinateHilbert I).natDegree

noncomputable def affineDegree {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ℚ :=
  ((affineDimension I).factorial : ℚ) * (coordinateHilbert I).coeff (affineDimension I)

theorem coordinateHilbert_eventually {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) : ∀ᶠ T : ℕ in Filter.atTop,
    (Module.finrank K ((totalSpace T).map (Ideal.Quotient.mkₐ K I).toLinearMap) : ℚ) =
      (coordinateHilbert I).eval (T : ℚ) := by
  obtain ⟨N,hN⟩ := (coordinate_hilbert_eventually_polynomial I).choose_spec.2
  exact Filter.eventually_atTop.mpr ⟨N,hN⟩

theorem one_le_affineDegree {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) : 1 ≤ affineDegree I := by
  obtain ⟨P,_,_,_,hc,N,hN⟩ := coordinate_hilbert_degree_independent I hI
  have he : P = coordinateHilbert I := by
    apply polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Filter.eventually_atTop.mpr ⟨N,hN⟩,coordinateHilbert_eventually I] with T hp hq
    exact hp.symm.trans hq
  rw [he] at hc
  have hf : (0 : ℚ) < ((affineDimension I).factorial : ℚ) := by exact_mod_cast Nat.factorial_pos _
  calc
    1 = ((affineDimension I).factorial : ℚ) * ((affineDimension I).factorial : ℚ)⁻¹ :=
      (mul_inv_cancel₀ hf.ne').symm
    _ ≤ affineDegree I := mul_le_mul_of_nonneg_left hc hf.le

theorem proper_cut_component_dimension {n h : ℕ} {K : Type u} [Field K]
    (I Q : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [Q.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I)
    (hQ : Q ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hd : affineDimension I = h+1) :
    affineDimension Q = h :=
  proper_cut_hilbert_purity I Q p hp hQ _ _ _ (coordinateHilbert_eventually I)
    (coordinateHilbert_eventually _) (coordinateHilbert_eventually Q) hd

theorem proper_cut_sum_affineDegree_le {n h : ℕ} {K : Type u} {ι : Type*}
    [Field K] [Fintype ι] (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (p : MvPolynomial (Fin n) K) (hp : p ∉ I) (hd : affineDimension I = h+1)
    (Q : ι → Ideal (MvPolynomial (Fin n) K))
    (hQ : ∀ i, Q i ∈ (I ⊔ Ideal.span {p}).minimalPrimes) (hQi : Function.Injective Q) :
    ∑ i, affineDegree (Q i) ≤ (p.totalDegree : ℚ) * affineDegree I := by
  classical
  let J := I ⊔ Ideal.span {p}
  have hdim : ∀ i, affineDimension (Q i) = h := by
    intro i
    let := (hQ i).isPrime
    exact proper_cut_component_dimension I (Q i) p hp (hQ i) hd
  have hj := proper_cut_hilbert_polynomial I p hp (coordinateHilbert I) (coordinateHilbert J)
    ((coordinateHilbert_eventually I).mono (fun _ ht => ht.symm))
    ((coordinateHilbert_eventually J).mono (fun _ ht => ht.symm)) h hd.le
  have hc := component_hilbert_coeff_sum_le J Q hQ hQi (coordinateHilbert J)
    (fun i => coordinateHilbert (Q i)) (coordinateHilbert_eventually J)
    (fun i => coordinateHilbert_eventually (Q i)) hj.1 (fun i => (hdim i).le)
  have hf : (0 : ℚ) ≤ (h.factorial : ℚ) := Nat.cast_nonneg _
  calc
    ∑ i, affineDegree (Q i) = (h.factorial : ℚ) * ∑ i, (coordinateHilbert (Q i)).coeff h := by
      simp only [affineDegree, hdim, Finset.mul_sum]
    _ ≤ (h.factorial : ℚ) * (coordinateHilbert J).coeff h := mul_le_mul_of_nonneg_left hc hf
    _ ≤ (h.factorial : ℚ) * ((p.totalDegree : ℚ) * (h+1) * (coordinateHilbert I).coeff (h+1)) :=
      mul_le_mul_of_nonneg_left hj.2 hf
    _ = (p.totalDegree : ℚ) * affineDegree I := by
      rw [affineDegree, hd, Nat.factorial_succ]
      push_cast
      ring

end

open MvPolynomial

def DeterminedInDegree {σ ι K : Type*} [Field K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ) (D : ℕ) : Prop :=
  ∀ p : MvPolynomial σ K, p.totalDegree ≤ D →
    ((∀ i, eval (fun l => (z i l : K)) p = 0) ↔ p ∈ I)

theorem bounded_cut_or_determined {σ ι K : Type*}
    [Fintype σ] [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial σ K)) (z : ι → σ → ℤ)
    (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (D : ℕ) (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    (∃ G : MvPolynomial σ ℤ,
      G.totalDegree ≤ D ∧
      (∀ m, |((G.coeff m : ℤ) : ℝ)| ≤
        integralKernelHeight ((D + Fintype.card σ).choose (Fintype.card σ)) (H^D)) ∧
      (∀ i, eval (z i) G = 0) ∧ MvPolynomial.map (Int.castRingHom K) G ∉ I) ∨
    DeterminedInDegree I z D := by
  classical
  obtain ⟨G,hdeg,hheight,hvan,hspan⟩ :=
    exists_bounded_degree_vanishing_polynomials (F := K) z H hH hz D
  by_cases hGI : ∀ a, MvPolynomial.map (Int.castRingHom K) (G a) ∈ I
  · right
    intro p hp
    constructor
    · intro hvanp
      exact (Submodule.span_le.mpr (by rintro _ ⟨a,rfl⟩; exact hGI a) :
        Submodule.span K (Set.range (fun a => MvPolynomial.map (Int.castRingHom K) (G a))) ≤
          I.restrictScalars K) (hspan p hp hvanp)
    · exact hzI p
  · left
    obtain ⟨a,ha⟩ := not_forall.mp hGI
    exact ⟨G a,hdeg a,hheight a,hvan a,ha⟩

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PointInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem affineDimension_independent_coordinates {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (hI : I ≠ ⊤) :
    ∃ j : Fin (affineDimension I) → Fin n,
      Function.Injective j ∧
      AlgebraicIndependent K (fun a => Ideal.Quotient.mk I (X (j a))) := by
  obtain ⟨P,j,hj,hi,_,N,hN⟩ := coordinate_hilbert_degree_independent I hI
  have he : P = coordinateHilbert I := by
    apply polynomial_eq_of_eventually_nat_eval_eq
    filter_upwards [Filter.eventually_atTop.mpr ⟨N,hN⟩,coordinateHilbert_eventually I] with T hp hq
    exact hp.symm.trans hq
  subst P
  exact ⟨j,hj,hi⟩

theorem determined_bounded_patch {n D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hD : affineDegree I ≤ D) (z : ι → Fin n → ℤ)
    (hdet : DeterminedInDegree I z D)
    (hzI : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    ∃ J : Set (Fin n), Nat.card J = affineDimension I ∧
      ∃ G : ↥(Jᶜ) → MvPolynomial (Fin n) ℤ,
        (∀ i, (G i).totalDegree ≤ D) ∧
        (∀ i m, |(((G i).coeff m : ℤ) : ℝ)| ≤ integralKernelHeight ((D+n).choose n) (H^D)) ∧
        (∀ i, MvPolynomial.map (Int.castRingHom K) (G i) ∈ I) ∧
        Matrix.det (fun i l : ↥(Jᶜ) => pderiv l.val (MvPolynomial.map (Int.castRingHom K) (G i))) ∉ I := by
  obtain ⟨j,_,hj⟩ := affineDimension_independent_coordinates I (Ideal.IsPrime.ne_top inferInstance)
  obtain hc | hp := bounded_patch_or_cut I (coordinateHilbert I) le_rfl
    (coordinateHilbert_eventually I) hD j hj z hzI H hH hz
  · obtain ⟨G,hG,_,hvan,hnot⟩ := hc
    have hd : (MvPolynomial.map (Int.castRingHom K) G).totalDegree ≤ D := by
      simpa only [totalDegree, support_map_of_injective G (f := Int.castRingHom K) (Int.cast_injective (α := K))] using hG
    have hv : ∀ i, eval (fun l => (z i l : K)) (MvPolynomial.map (Int.castRingHom K) G) = 0 := by
      intro i
      have he := map_eval (Int.castRingHom K) (z i) G
      rw [hvan i, map_zero] at he
      exact he.symm
    exact (hnot ((hdet _ hd).mp hv)).elim
  · exact hp

theorem point_on_minimal_component {n : ℕ} {K : Type*} [Field K]
    (J : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → K)
    (hz : ∀ p ∈ J, eval z p = 0) :
    ∃ Q ∈ J.minimalPrimes, ∀ p ∈ Q, eval z p = 0 := by
  let P := RingHom.ker (eval z)
  have hP : P.IsPrime := RingHom.ker_isPrime _
  obtain ⟨Q,hQ,hQP⟩ := Ideal.exists_minimalPrimes_le (show J ≤ P from hz)
  exact ⟨Q,hQ,fun p hp => hQP hp⟩

end
open MvPolynomial

theorem zeroDim_isMaximal {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I = 0) : I.IsMaximal := by
  have ht := hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I)
  change (affineDimension I : Cardinal) = _ at ht
  rw [hd, Nat.cast_zero] at ht
  let : Algebra.IsAlgebraic K (MvPolynomial (Fin n) K ⧸ I) := trdeg_eq_zero_iff.mp ht.symm
  exact Ideal.Quotient.maximal_of_isField I (isField_of_isIntegral_of_isField' (R := K)
    (S := MvPolynomial (Fin n) K ⧸ I) (Field.toIsField K))

theorem zeroDim_eq_point {n : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I = 0) (z : Fin n → K)
    (hz : ∀ p ∈ I, eval z p = 0) : I = RingHom.ker (eval z) := by
  apply (zeroDim_isMaximal I hd).eq_of_le (RingHom.ker_isPrime _).ne_top
  exact hz

theorem zeroDim_determined {n D : ℕ} {ι K : Type*} [Nonempty ι] [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I = 0) (z : ι → Fin n → ℤ)
    (hz : ∀ p ∈ I, ∀ i, eval (fun l => (z i l : K)) p = 0) : DeterminedInDegree I z D := by
  intro p _
  constructor
  · intro hp
    obtain ⟨i⟩ := ‹Nonempty ι›
    rw [zeroDim_eq_point I hd (fun l => (z i l : K)) (fun q hq => hz q hq i)]
    exact hp i
  · exact hz p

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

structure IntegerPatch (n : ℕ) where
  free : Set (Fin n)
  equations : ↥(freeᶜ) → MvPolynomial (Fin n) ℤ

noncomputable def IntegerPatch.minor {n : ℕ} (P : IntegerPatch n) : MvPolynomial (Fin n) ℤ :=
  Matrix.det (fun i j : ↥(P.freeᶜ) => pderiv j.val (P.equations i))

def IntegerPatch.On {n : ℕ} {K : Type*} [Field K]
    (P : IntegerPatch n) (I : Ideal (MvPolynomial (Fin n) K)) : Prop :=
  Nat.card P.free = affineDimension I ∧
  (∀ i, MvPolynomial.map (Int.castRingHom K) (P.equations i) ∈ I) ∧
  MvPolynomial.map (Int.castRingHom K) P.minor ∉ I

def IntegerPatch.Bounded {n : ℕ} (P : IntegerPatch n) (D : ℕ) (H : ℝ) : Prop :=
  ∃ d ≤ D, (∀ i, (P.equations i).totalDegree ≤ d) ∧
    ∀ i m, |(((P.equations i).coeff m : ℤ) : ℝ)| ≤
      integralKernelHeight ((d+n).choose n) (H^d)

def PointOn {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) : Prop :=
  ∀ p ∈ I, eval (fun l => (z l : K)) p = 0

theorem IntegerPatch.Bounded.mono {n D E : ℕ} {P : IntegerPatch n} {H : ℝ}
    (h : P.Bounded D H) (hDE : D ≤ E) : P.Bounded E H := by
  obtain ⟨d,hd,hdeg,hheight⟩ := h
  exact ⟨d,hd.trans hDE,hdeg,hheight⟩

theorem map_integer_minor {n : ℕ} {K : Type*} [Field K] (P : IntegerPatch n) :
    MvPolynomial.map (Int.castRingHom K) P.minor =
      Matrix.det (fun i j : ↥(P.freeᶜ) => pderiv j.val
        (MvPolynomial.map (Int.castRingHom K) (P.equations i))) := by
  let M : Matrix ↥(P.freeᶜ) ↥(P.freeᶜ) (MvPolynomial (Fin n) ℤ) :=
    fun i j => pderiv j.val (P.equations i)
  have he := (MvPolynomial.map (Int.castRingHom K)).map_det M
  calc
    MvPolynomial.map (Int.castRingHom K) P.minor =
      Matrix.det (fun i j => MvPolynomial.map (Int.castRingHom K) (M i j)) := he
    _ = _ := by congr 1; funext i j; exact pderiv_map.symm

theorem determined_integer_patch {n D : ℕ} {ι K : Type*}
    [Fintype ι] [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hD : affineDegree I ≤ D) (z : ι → Fin n → ℤ)
    (hdet : DeterminedInDegree I z D)
    (hzI : ∀ i, PointOn I (z i))
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ i l, |(z i l : ℝ)| ≤ H) :
    ∃ P : IntegerPatch n, P.On I ∧ P.Bounded D H := by
  obtain ⟨J,hJ,G,hdeg,hheight,hGI,hminor⟩ := determined_bounded_patch I hD z hdet
    (fun p hp i => hzI i p hp) H hH hz
  let P : IntegerPatch n := ⟨J,G⟩
  refine ⟨P,⟨hJ,hGI,?_⟩,D,le_rfl,hdeg,hheight⟩
  simpa only [map_integer_minor] using hminor

theorem IntegerPatch.minor_degree_le {n D : ℕ} {P : IntegerPatch n} {H : ℝ}
    (h : P.Bounded D H) : P.minor.totalDegree ≤ n * D := by
  obtain ⟨d,hd,hdeg,_⟩ := h
  apply (jacobian_minor_degree P.equations Subtype.val d hdeg).trans
  apply Nat.mul_le_mul
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun x : Fin n => x ∈ P.freeᶜ)
  · exact (Nat.sub_le _ _).trans hd

theorem bounded_cut_components {n h e D : ℕ} {K : Type u} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (he : affineDegree I ≤ e) (p : MvPolynomial (Fin n) K)
    (hp : p ∉ I) (hpD : p.totalDegree ≤ D) (hd : affineDimension I = h+1) :
    ∃ Q : Finset (Ideal (MvPolynomial (Fin n) K)),
      Q.card ≤ D*e ∧
      (∀ J ∈ Q, J.IsPrime ∧ I ≤ J ∧ affineDimension J = h ∧ affineDegree J ≤ D*e) ∧
      (∀ z : Fin n → K, (∀ F ∈ I, eval z F = 0) → eval z p = 0 →
        ∃ J ∈ Q, ∀ F ∈ J, eval z F = 0) := by
  classical
  let J := I ⊔ Ideal.span {p}
  let Q := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin n) K) J).toFinset
  have hQ : ∀ q : Q, q.val ∈ J.minimalPrimes := fun q =>
    (Set.Finite.mem_toFinset _).mp q.property
  have hsum : ∑ q ∈ Q, affineDegree q ≤ (D*e : ℕ) := by
    calc
      ∑ q ∈ Q, affineDegree q ≤ (p.totalDegree : ℚ) * affineDegree I := by
        simpa only [Finset.univ_eq_attach, Finset.sum_attach] using
          proper_cut_sum_affineDegree_le I p hp hd (fun q : Q => q.val) hQ Subtype.val_injective
      _ ≤ (D : ℚ) * e := mul_le_mul (by exact_mod_cast hpD) he
        ((one_le_affineDegree I Ideal.IsPrime.ne_top').trans' zero_le_one) (Nat.cast_nonneg _)
      _ = (D*e : ℕ) := by norm_cast
  have hnonneg : ∀ q ∈ Q, (0 : ℚ) ≤ affineDegree q := fun q hq =>
    zero_le_one.trans (one_le_affineDegree q (hQ ⟨q,hq⟩).isPrime.ne_top)
  refine ⟨Q,?_,?_,?_⟩
  · have hc : (Q.card : ℚ) ≤ ∑ q ∈ Q, affineDegree q := by
      calc
        (Q.card : ℚ) = ∑ _q ∈ Q, (1 : ℚ) := by simp
        _ ≤ _ := Finset.sum_le_sum fun q hq => one_le_affineDegree q (hQ ⟨q,hq⟩).isPrime.ne_top
    exact_mod_cast hc.trans hsum
  · intro q hq
    have hm := hQ ⟨q,hq⟩
    let := hm.isPrime
    refine ⟨hm.isPrime,?_,proper_cut_component_dimension I q p hp hm hd,?_⟩
    · exact le_sup_left.trans hm.1.2
    · simpa only [Nat.cast_mul] using (Finset.single_le_sum hnonneg hq).trans hsum
  · intro z hz hpz
    obtain ⟨q,hq,hzq⟩ := point_on_minimal_component J z (show J ≤ RingHom.ker (eval z) from
      sup_le hz (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hpz)))
    exact ⟨q,(Set.Finite.mem_toFinset _).mpr hq,hzq⟩

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_IntegerPatches
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
attribute [local instance] Classical.propDecidable

theorem totalDegree_int_map {n : ℕ} {K : Type*} [Field K] [CharZero K]
    (p : MvPolynomial (Fin n) ℤ) :
    (MvPolynomial.map (Int.castRingHom K) p).totalDegree = p.totalDegree := by
  simp only [totalDegree, support_map_of_injective p (f := Int.castRingHom K)
    (Int.cast_injective (α := K))]

theorem eval_int_map {n : ℕ} {K : Type*} [Field K]
    (p : MvPolynomial (Fin n) ℤ) (z : Fin n → ℤ) :
    eval (fun l => (z l : K)) (MvPolynomial.map (Int.castRingHom K) p) = (eval z p : K) :=
  (map_eval (Int.castRingHom K) z p).symm

theorem integer_patch_step {n D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (hD : affineDegree I ≤ D)
    (S : Finset (Fin n → ℤ)) (hSI : ∀ z ∈ S, PointOn I z)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ p : MvPolynomial (Fin n) K, p ∉ I ∧ p.totalDegree ≤ (n+1)*D ∧
      ∃ L : List (IntegerPatch n), L.length ≤ 1 ∧
        (∀ P ∈ L, P.On I ∧ P.Bounded D H ∧
          DeterminedInDegree I (fun z : S => z.val) D) ∧
        ∀ z ∈ S, eval (fun l => (z l : K)) p = 0 ∨
          ∃ P ∈ L, eval z P.minor ≠ 0 := by
  obtain hc | hd := bounded_cut_or_determined I (fun z : S => z.val)
    (fun p hp z => hSI z.val z.property p hp) D H hH (fun z => hz z.val z.property)
  · obtain ⟨G,hG,_,hvan,hnot⟩ := hc
    refine ⟨MvPolynomial.map (Int.castRingHom K) G,hnot,?_,[],by simp,by simp,?_⟩
    · rw [totalDegree_int_map]
      exact hG.trans (Nat.le_mul_of_pos_left D (Nat.succ_pos n))
    · intro z hzs
      left
      rw [eval_int_map, hvan ⟨z,hzs⟩, Int.cast_zero]
  · obtain ⟨P,hPI,hP⟩ := determined_integer_patch I hD (fun z : S => z.val) hd
      (fun z => hSI z.val z.property) H hH (fun z => hz z.val z.property)
    refine ⟨MvPolynomial.map (Int.castRingHom K) P.minor,hPI.2.2,?_,[P],by simp,?_,?_⟩
    · rw [totalDegree_int_map]
      exact (P.minor_degree_le hP).trans (Nat.mul_le_mul_right D (Nat.le_succ n))
    · simpa using And.intro hPI (And.intro hP hd)
    · intro z _
      by_cases h : eval z P.minor = 0
      · left
        rw [eval_int_map,h,Int.cast_zero]
      · exact Or.inr ⟨P,by simp,h⟩

end
section
open MvPolynomial
attribute [local instance] Classical.propDecidable

def EquationLock {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ)) (D : ℕ) : Prop :=
  ∀ p : MvPolynomial (Fin n) K, p.totalDegree ≤ D →
    ((∀ z ∈ S, PointOn I z → eval (fun l => (z l : K)) p = 0) ↔ p ∈ I)

theorem PointOn.mono {n : ℕ} {K : Type*} [Field K]
    {I J : Ideal (MvPolynomial (Fin n) K)} (hIJ : I ≤ J) {z : Fin n → ℤ}
    (hz : PointOn J z) : PointOn I z := fun p hp => hz p (hIJ hp)

theorem equationLock_of_determined {n D E : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ))
    (hS : ∀ z ∈ S, PointOn I z) (h : DeterminedInDegree I (fun z : S => z.val) D)
    (hED : E ≤ D) : EquationLock I S E := by
  intro p hp
  rw [← h p (hp.trans hED)]
  constructor
  · intro he z
    exact he z.val z.property (hS z.val z.property)
  · intro he z hz _
    exact he ⟨z,hz⟩

theorem EquationLock.of_filter {n D : ℕ} {K : Type*} [Field K]
    {I J : Ideal (MvPolynomial (Fin n) K)} (hIJ : I ≤ J)
    (S : Finset (Fin n → ℤ)) (h : EquationLock J (S.filter (PointOn I)) D) :
    EquationLock J S D := by
  intro p hp
  rw [← h p hp]
  constructor
  · intro he z hz hj
    exact he z (Finset.mem_filter.mp hz).1 hj
  · intro he z hz hj
    exact he z (Finset.mem_filter.mpr ⟨hz,hj.mono hIJ⟩) hj

def patchNextDegree (n D e : ℕ) : ℕ := ((n+1)*max e D)*e

def patchDegreeBudget (n D : ℕ) : ℕ → ℕ → ℕ
  | 0,e => max e D
  | h+1,e => max (max e D) (patchDegreeBudget n D h (patchNextDegree n D e))

def patchCountBudget (n D : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 1
  | h+1,e => 1+patchNextDegree n D e * patchCountBudget n D h (patchNextDegree n D e)

theorem le_patchDegreeBudget (n D h e : ℕ) : max e D ≤ patchDegreeBudget n D h e := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact Nat.le_max_left _ _

theorem one_le_patchCountBudget (n D h e : ℕ) : 1 ≤ patchCountBudget n D h e := by
  cases h <;> simp only [patchCountBudget] <;> omega

def GoodPatchPiece {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (S : Finset (Fin n → ℤ))
    (D h B : ℕ) (H : ℝ) (C : Ideal (MvPolynomial (Fin n) K) × IntegerPatch n) : Prop :=
  C.1.IsPrime ∧ I ≤ C.1 ∧ affineDimension C.1 ≤ h ∧ affineDegree C.1 ≤ B ∧
    C.2.On C.1 ∧ C.2.Bounded B H ∧ EquationLock C.1 S D

def PatchPieceCovers {n : ℕ} {K : Type*} [Field K]
    (C : Ideal (MvPolynomial (Fin n) K) × IntegerPatch n) (z : Fin n → ℤ) : Prop :=
  PointOn C.1 z ∧ eval z C.2.minor ≠ 0

theorem zeroDim_patch_cover {n D : ℕ} {K : Type*} [Field K] [CharZero K]
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] (hd : affineDimension I = 0)
    (hD : affineDegree I ≤ D) (S : Finset (Fin n → ℤ)) (hS : S.Nonempty)
    (hSI : ∀ z ∈ S, PointOn I z) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ P : IntegerPatch n, P.On I ∧ P.Bounded D H ∧
      EquationLock I S D ∧ ∀ z ∈ S, PatchPieceCovers (I,P) z := by
  let : Nonempty S := hS.to_subtype
  have hdet : DeterminedInDegree I (fun z : S => z.val) D :=
    zeroDim_determined I hd _ (fun p hp z => hSI z.val z.property p hp)
  obtain ⟨P,hPI,hP⟩ := determined_integer_patch I hD (fun z : S => z.val) hdet
    (fun z => hSI z.val z.property) H hH (fun z => hz z.val z.property)
  refine ⟨P,hPI,hP,equationLock_of_determined I S hSI hdet le_rfl,?_⟩
  intro z hzs
  refine ⟨hSI z hzs,?_⟩
  intro hzero
  apply hPI.2.2
  rw [zeroDim_eq_point I hd (fun l => (z l : K)) (hSI z hzs)]
  change eval (fun l => (z l : K)) (MvPolynomial.map (Int.castRingHom K) P.minor) = 0
  rw [eval_int_map,hzero,Int.cast_zero]

theorem list_flatMap_length_le {α β : Type*} (l : List α) (f : α → List β) (B : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ B) : (l.flatMap f).length ≤ l.length*B := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem bounded_integer_patch_cover {n : ℕ} {K : Type u} [Field K] [CharZero K]
    (D h e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hdim : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (S : Finset (Fin n → ℤ)) (hSI : ∀ z ∈ S, PointOn I z)
    (H : ℝ) (hH : 1 ≤ H) (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ patchCountBudget n D h e ∧
      (∀ C ∈ L, GoodPatchPiece I S D h (patchDegreeBudget n D h e) H C) ∧
      ∀ z ∈ S, ∃ C ∈ L, PatchPieceCovers C z := by
  classical
  induction h generalizing e I S with
  | zero =>
    by_cases hS : S.Nonempty
    · have hd : affineDimension I = 0 := Nat.eq_zero_of_le_zero hdim
      obtain ⟨P,hPI,hP,hl,hcov⟩ := zeroDim_patch_cover I hd
        (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hS hSI H hH hz
      refine ⟨[(I,P)],by simp [patchCountBudget],?_,?_⟩
      · intro C hC
        have hC : C = (I,P) := by simpa using hC
        subst C
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP,?_⟩
        · exact he.trans (by exact_mod_cast Nat.le_max_left e D)
        · intro p hp
          exact hl p (hp.trans (Nat.le_max_right _ _))
      · intro z hzs
        exact ⟨(I,P),by simp,hcov z hzs⟩
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hzs
      exact (hS ⟨z,hzs⟩).elim
  | succ h ih =>
    by_cases hS : S.Nonempty
    swap
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hzs
      exact (hS ⟨z,hzs⟩).elim
    by_cases hd : affineDimension I = 0
    · obtain ⟨P,hPI,hP,hl,hcov⟩ := zeroDim_patch_cover I hd
        (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hS hSI H hH hz
      have hB := le_patchDegreeBudget n D (h+1) e
      refine ⟨[(I,P)],?_,?_,?_⟩
      · simpa using one_le_patchCountBudget n D (h+1) e
      · intro C hC
        have hC : C = (I,P) := by simpa using hC
        subst C
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP.mono hB,?_⟩
        · exact he.trans (by exact_mod_cast (Nat.le_max_left e D).trans hB)
        · intro p hp
          exact hl p (hp.trans (Nat.le_max_right _ _))
      · intro z hzs
        exact ⟨(I,P),by simp,hcov z hzs⟩
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hd
    have hkh : k ≤ h := by omega
    obtain ⟨p,hp,hpD,L₀,hL₀,hgood₀,hcover₀⟩ := integer_patch_step I
      (he.trans (by exact_mod_cast Nat.le_max_left e D)) S hSI H hH hz
    let E := patchNextDegree n D e
    obtain ⟨Q,hcard,hQ,hcoverQ⟩ := bounded_cut_components I he p hp hpD hk
    let S' := fun q : Q => S.filter (PointOn q.val)
    have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
        L.length ≤ patchCountBudget n D h E ∧
        (∀ C ∈ L, GoodPatchPiece q.val (S' q) D h (patchDegreeBudget n D h E) H C) ∧
        ∀ z ∈ S' q, ∃ C ∈ L, PatchPieceCovers C z := by
      intro q
      have hq := hQ q.val q.property
      let := hq.1
      apply ih E q.val (hq.2.2.1.le.trans hkh)
        (by simpa only [E,patchNextDegree,Nat.cast_mul] using hq.2.2.2) (S' q)
      · intro z hzs
        exact (Finset.mem_filter.mp hzs).2
      · intro z hzs
        exact hz z (Finset.mem_filter.mp hzs).1
    choose L hlen hgood hcover using hc
    let R := Q.attach.toList.flatMap L
    have hRlen : R.length ≤ Q.card * patchCountBudget n D h E := by
      simpa [R] using list_flatMap_length_le Q.attach.toList L (patchCountBudget n D h E)
        (fun q _ => hlen q)
    refine ⟨L₀.map (fun P => (I,P)) ++ R,?_,?_,?_⟩
    · simp only [List.length_append,List.length_map]
      exact (Nat.add_le_add hL₀ hRlen).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hcard) 1)
    · intro C hC
      rcases List.mem_append.mp hC with hC | hC
      · obtain ⟨P,hPL,rfl⟩ := List.mem_map.mp hC
        obtain ⟨hPI,hP,hdet⟩ := hgood₀ P hPL
        have hB := le_patchDegreeBudget n D (h+1) e
        refine ⟨inferInstance,le_rfl,hdim,?_,hPI,hP.mono hB,?_⟩
        · exact he.trans (by exact_mod_cast (Nat.le_max_left e D).trans hB)
        · exact equationLock_of_determined I S hSI hdet (Nat.le_max_right _ _)
      · obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
        obtain ⟨hpq,hIq,hdq,heq,hOn,hBound,hLock⟩ := hgood q C hCL
        have hB : patchDegreeBudget n D h E ≤ patchDegreeBudget n D (h+1) e := Nat.le_max_right _ _
        refine ⟨hpq,(hQ q.val q.property).2.1.trans hIq,hdq.trans (Nat.le_succ _),?_,
          hOn,hBound.mono hB,?_⟩
        · exact heq.trans (by exact_mod_cast hB)
        · exact hLock.of_filter hIq S
    · intro z hzs
      rcases hcover₀ z hzs with hpz | ⟨P,hPL,hPz⟩
      · obtain ⟨q,hq,hzq⟩ := hcoverQ (fun l => (z l : K)) (hSI z hzs) hpz
        obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hzs,hzq⟩)
        refine ⟨C,List.mem_append_right _ ?_,hCz⟩
        exact List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hCL⟩
      · exact ⟨(I,P),List.mem_append_left _ (List.mem_map.mpr ⟨P,hPL,rfl⟩),hSI z hzs,hPz⟩

end
open MvPolynomial
attribute [local instance] Classical.propDecidable

def evaluationSpace {n : ℕ} (S : Finset (Fin n → ℤ)) (D : ℕ) :
    Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) D) where
  carrier := {p | ∀ z ∈ S, eval (fun l => (z l : ℂ)) p.val = 0}
  zero_mem' := by simp
  add_mem' := by intro p q hp hq z hz; simpa using congrArg₂ (· + ·) (hp z hz) (hq z hz)
  smul_mem' := by intro a p hp z hz; simp [hp z hz]

noncomputable def evaluationCell {n : ℕ} {K : Type*} [Field K]
    (S : Finset (Fin n → ℤ)) (I : Ideal (MvPolynomial (Fin n) K))
    (z : Fin n → ℤ) (Q : Finset ℕ) : Finset (Fin n → ℤ) :=
  S.filter fun w => PointOn I w ∧ ∀ p ∈ Q, ∀ l, (p : ℤ) ∣ w l-z l

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PatchBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree
open MvPolynomial

def kernelDegreeBudget (D : ℕ) : ℕ → ℕ → ℕ
  | 0, e => e
  | h+1, e => max e (kernelDegreeBudget D h (D*e))

def kernelCountBudget (D : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | h+1, e => 1+(D*e)*kernelCountBudget D h (D*e)

theorem le_kernelDegreeBudget (D h e : ℕ) : e ≤ kernelDegreeBudget D h e := by
  cases h with
  | zero => exact le_rfl
  | succ h => exact Nat.le_max_left _ _

theorem one_le_kernelCountBudget (D h e : ℕ) : 1 ≤ kernelCountBudget D h e := by
  cases h <;> simp only [kernelCountBudget] <;> omega

theorem bounded_kernel_components {n D : ℕ} {K : Type u} [Field K]
    (F : Set (MvPolynomial (Fin n) K))
    (hF : ∀ p ∈ F, p.totalDegree ≤ D) (h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K)),
      L.length ≤ kernelCountBudget D h e ∧
      (∀ J ∈ L, J.IsPrime ∧ I ≤ J ∧ affineDimension J ≤ affineDimension I ∧
        affineDegree J ≤ kernelDegreeBudget D h e ∧ F ⊆ J ∧
        (¬ F ⊆ I → affineDimension J < affineDimension I)) ∧
      (∀ z : Fin n → K, (∀ p ∈ I, eval z p = 0) →
        (∀ p ∈ F, eval z p = 0) → ∃ J ∈ L, ∀ p ∈ J, eval z p = 0) := by
  classical
  induction h generalizing e I with
  | zero =>
    by_cases hFI : F ⊆ I
    · refine ⟨[I],le_rfl,?_,?_⟩
      · intro J hJ
        have hj : J = I := by simpa using hJ
        subst J
        exact ⟨inferInstance,le_rfl,le_rfl,he,hFI,fun hn => (hn hFI).elim⟩
      · intro z hz _
        exact ⟨I,by simp,hz⟩
    · refine ⟨[],by simp [kernelCountBudget],by simp,?_⟩
      intro z hz hFz
      exfalso
      apply hFI
      rw [zeroDim_eq_point I (Nat.eq_zero_of_le_zero hd) z hz]
      exact hFz
  | succ h ih =>
    by_cases hFI : F ⊆ I
    · refine ⟨[I],one_le_kernelCountBudget D (h+1) e,?_,?_⟩
      · intro J hJ
        have hj : J = I := by simpa using hJ
        subst J
        refine ⟨inferInstance,le_rfl,le_rfl,?_,hFI,fun hn => (hn hFI).elim⟩
        exact he.trans (by exact_mod_cast le_kernelDegreeBudget D (h+1) e)
      · intro z hz _
        exact ⟨I,by simp,hz⟩
    by_cases hd0 : affineDimension I = 0
    · refine ⟨[],by simp,by simp,?_⟩
      intro z hz hFz
      exfalso
      apply hFI
      rw [zeroDim_eq_point I hd0 z hz]
      exact hFz
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hd0
    have hkh : k ≤ h := by omega
    obtain ⟨p,hpF,hpI⟩ : ∃ p ∈ F, p ∉ I := by
      exact Set.not_subset.mp hFI
    obtain ⟨Q,hQcard,hQ,hQcov⟩ := bounded_cut_components I he p hpI (hF p hpF) hk
    have hc : ∀ q : Q, ∃ L : List (Ideal (MvPolynomial (Fin n) K)),
        L.length ≤ kernelCountBudget D h (D*e) ∧
        (∀ J ∈ L, J.IsPrime ∧ q.val ≤ J ∧ affineDimension J ≤ affineDimension q.val ∧
          affineDegree J ≤ kernelDegreeBudget D h (D*e) ∧ F ⊆ J ∧
          (¬ F ⊆ q.val → affineDimension J < affineDimension q.val)) ∧
        (∀ z : Fin n → K, (∀ p ∈ q.val, eval z p = 0) →
          (∀ p ∈ F, eval z p = 0) → ∃ J ∈ L, ∀ p ∈ J, eval z p = 0) := by
      intro q
      obtain ⟨hprime,_,hdq,heq⟩ := hQ q.val q.property
      let := hprime
      exact ih (D*e) q.val (hdq.le.trans hkh) (by simpa only [Nat.cast_mul] using heq)
    choose L hlen hgood hcover using hc
    let R := Q.attach.toList.flatMap L
    refine ⟨R,?_,?_,?_⟩
    · have hh : R.length ≤ Q.card * kernelCountBudget D h (D*e) := by
        simpa only [R,Finset.length_toList,Finset.card_attach] using
          list_flatMap_length_le Q.attach.toList L (kernelCountBudget D h (D*e))
            (fun q _ => hlen q)
      exact (hh.trans (Nat.mul_le_mul_right _ hQcard)).trans
        (Nat.le_add_left _ _)
    · intro J hJ
      obtain ⟨q,_,hJL⟩ := List.mem_flatMap.mp hJ
      obtain ⟨hpJ,hqJ,hdJ,heJ,hFJ,_⟩ := hgood q J hJL
      have hend : affineDimension J < affineDimension I := by
        have hdq := (hQ q.val q.property).2.2.1
        omega
      refine ⟨hpJ,(hQ q.val q.property).2.1.trans hqJ,hend.le,?_,hFJ,fun _ => hend⟩
      exact heJ.trans (by exact_mod_cast Nat.le_max_right e (kernelDegreeBudget D h (D*e)))
    · intro z hz hFz
      obtain ⟨q,hq,hzq⟩ := hQcov z hz (hFz p hpF)
      obtain ⟨J,hJL,hzJ⟩ := hcover ⟨q,hq⟩ z hzq hFz
      exact ⟨J,List.mem_flatMap.mpr ⟨⟨q,hq⟩,by simp,hJL⟩,hzJ⟩

theorem affineDimension_antitone {n : ℕ} {K : Type u} [Field K]
    (I J : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime] [J.IsPrime]
    (hIJ : I ≤ J) : affineDimension J ≤ affineDimension I := by
  have ht := trdeg_le_of_surjective (Ideal.Quotient.factorₐ K hIJ)
    (Ideal.Quotient.factor_surjective hIJ)
  rw [← hilbert_natDegree_eq_trdeg I (coordinateHilbert I) (coordinateHilbert_eventually I),
    ← hilbert_natDegree_eq_trdeg J (coordinateHilbert J) (coordinateHilbert_eventually J)] at ht
  exact_mod_cast ht

theorem bounded_kernel_patch_cover {n D A h e : ℕ} {K : Type u} [Field K] [CharZero K]
    (F : Set (MvPolynomial (Fin n) K)) (hF : ∀ p ∈ F, p.totalDegree ≤ D)
    (I : Ideal (MvPolynomial (Fin n) K)) [I.IsPrime]
    (hd : affineDimension I ≤ h) (he : affineDegree I ≤ e)
    (S : Finset (Fin n → ℤ)) (H : ℝ) (hH : 1 ≤ H)
    (hz : ∀ z ∈ S, ∀ l, |(z l : ℝ)| ≤ H) :
    ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ kernelCountBudget D h e * patchCountBudget n A h (kernelDegreeBudget D h e) ∧
      (∀ C ∈ L,
        GoodPatchPiece I S A h (patchDegreeBudget n A h (kernelDegreeBudget D h e)) H C ∧
        F ⊆ C.1 ∧ affineDimension C.1 ≤ affineDimension I ∧
        (¬ F ⊆ I → affineDimension C.1 < affineDimension I)) ∧
      ∀ z ∈ S, PointOn I z → (∀ p ∈ F, eval (fun l => (z l : K)) p = 0) →
        ∃ C ∈ L, PatchPieceCovers C z := by
  classical
  obtain ⟨Q,hQlen,hQ,hQcov⟩ := bounded_kernel_components F hF h e I hd he
  let S' := fun q : {q // q ∈ Q} => S.filter (PointOn q.val)
  have hc : ∀ q : {q // q ∈ Q}, ∃ L : List (Ideal (MvPolynomial (Fin n) K) × IntegerPatch n),
      L.length ≤ patchCountBudget n A h (kernelDegreeBudget D h e) ∧
      (∀ C ∈ L, GoodPatchPiece q.val (S' q) A h
        (patchDegreeBudget n A h (kernelDegreeBudget D h e)) H C) ∧
      ∀ z ∈ S' q, ∃ C ∈ L, PatchPieceCovers C z := by
    intro q
    obtain ⟨hprime,_,hdq,heq,_⟩ := hQ q.val q.property
    let := hprime
    apply bounded_integer_patch_cover A h (kernelDegreeBudget D h e) q.val (hdq.trans hd) heq
      (S' q)
    · intro z hz; exact (Finset.mem_filter.mp hz).2
    · exact hH
    · intro z hzs; exact hz z (Finset.mem_filter.mp hzs).1
  choose L hlen hgood hcover using hc
  let R := Q.attach.flatMap L
  refine ⟨R,?_,?_,?_⟩
  · have hh : R.length ≤ Q.length * patchCountBudget n A h (kernelDegreeBudget D h e) := by
      simpa only [R,List.length_attach] using list_flatMap_length_le Q.attach L
        (patchCountBudget n A h (kernelDegreeBudget D h e)) (fun q _ => hlen q)
    exact hh.trans (Nat.mul_le_mul_right _ hQlen)
  · intro C hC
    obtain ⟨q,_,hCL⟩ := List.mem_flatMap.mp hC
    obtain ⟨hpq,hIq,hdq,heq,hFq,hstrict⟩ := hQ q.val q.property
    obtain ⟨hpC,hqC,hdC,heC,hOn,hBound,hLock⟩ := hgood q C hCL
    let := hpq
    let := hpC
    have hdim := affineDimension_antitone q.val C.1 hqC
    refine ⟨⟨hpC,hIq.trans hqC,hdC,heC,hOn,hBound,hLock.of_filter hqC S⟩,
      hFq.trans hqC,hdim.trans hdq,?_⟩
    exact fun hn => hdim.trans_lt (hstrict hn)
  · intro z hz hIz hFz
    obtain ⟨q,hq,hzq⟩ := hQcov (fun l => (z l : K)) hIz hFz
    obtain ⟨C,hCL,hCz⟩ := hcover ⟨q,hq⟩ z (Finset.mem_filter.mpr ⟨hz,hzq⟩)
    refine ⟨C,List.mem_flatMap.mpr ⟨⟨q,hq⟩,?_,hCL⟩,hCz⟩
    exact List.mem_attach Q ⟨q,hq⟩

noncomputable def stagedEvaluationSpace {n : ℕ} (S : Finset (Fin n → ℤ)) (d E : ℕ) :
    Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E) :=
  (totalSpace d).comap (totalSpace E).subtype ⊓ evaluationSpace S E

def stagedKernelPolynomials {n : ℕ} (d E : ℕ)
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E)) :
    Set (MvPolynomial (Fin n) ℂ) :=
  {p | ∃ v ∈ W, (v : MvPolynomial (Fin n) ℂ) = p ∧ p.totalDegree ≤ d}

theorem stagedKernelPolynomials_degree {n d E : ℕ}
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E))
    (p : MvPolynomial (Fin n) ℂ) (hp : p ∈ stagedKernelPolynomials d E W) :
    p.totalDegree ≤ d := hp.choose_spec.2.2

structure KernelGeometry (n : ℕ) where
  points : Finset (Fin n → ℤ)
  height : ℝ
  one_le_height : 1 ≤ height
  bounded : ∀ z ∈ points, ∀ l, |(z l : ℝ)| ≤ height

def KernelParent {n : ℕ} (h e : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) : Prop :=
  I.IsPrime ∧ affineDimension I ≤ h ∧ affineDegree I ≤ e

noncomputable def kernelChildList {n E : ℕ} (G : KernelGeometry n) (d A h e : ℕ)
    (I : Ideal (MvPolynomial (Fin n) ℂ))
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E)) :
    List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n) := by
  classical
  exact if hi : KernelParent h e I then
    letI := hi.1
    (bounded_kernel_patch_cover (A := A) (stagedKernelPolynomials d E W)
      (stagedKernelPolynomials_degree W) I hi.2.1 hi.2.2 G.points G.height
      G.one_le_height G.bounded).choose
  else []

noncomputable def firstCoveringChild {n : ℕ} (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (L : List (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)) :
    Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n := by
  classical
  exact (L.find? (fun C => decide (PatchPieceCovers C z))).getD s

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def kernelHeightConstant (m : ℕ) : ℝ :=
  (1+(m:ℝ)^2) * m.factorial * (1+(m:ℝ))^m

def minorSizeConstant (n d m : ℕ) : ℝ :=
  m.factorial * ((((d+n).choose n : ℝ)*(d:ℝ)*kernelHeightConstant ((d+n).choose n))^m)

def minorSizeExponent (n d m : ℕ) : ℕ :=
  (2*d*((d+n).choose n+1)+d)*m

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_AdaptiveRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators

namespace QuarticPowerFree

noncomputable def equationRank {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : Submodule K V) : ℕ := Module.finrank K (V ⧸ W)

variable {K V σ α : Type*} [Field K] [AddCommGroup V] [Module K V]
variable (W : ℕ → σ → α → Submodule K V)
variable (next : ℕ → σ → Submodule K V → σ)

noncomputable def adaptiveCode : ℕ → ℕ → σ → α → ℕ
  | 0, _, _, _ => 0
  | n+1, i, s, a => equationRank (W i s a) * (Module.finrank K V + 1)^n +
      adaptiveCode n (i+1) (next i s (W i s a)) a

noncomputable def adaptiveStates : ℕ → ℕ → σ → α → List σ
  | 0, _, s, _ => [s]
  | n+1, i, s, a => s :: adaptiveStates n (i+1) (next i s (W i s a)) a

end QuarticPowerFree

open scoped BigOperators

namespace QuarticPowerFree

noncomputable def subsetMean {α : Type*} (P : Finset α) (t : ℕ)
    (f : Finset α → ℝ) : ℝ :=
  (∑ S ∈ P.powersetCard t, f S) / (P.powersetCard t).card

noncomputable def badFraction {α : Type*} [DecidableEq α]
    (P : Finset α) (t : ℕ) (bad : Finset α → Finset α) : ℝ :=
  (∑ S ∈ P.powersetCard t, ∑ q ∈ S, if q ∈ bad S then (1 : ℝ) else 0) /
    ((t : ℝ) * (P.powersetCard t).card)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrimeBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

open scoped BigOperators

def BlockSample (P : Finset ℕ) (ell T : ℕ) :=
  Σ j : Fin T, (P.powersetCard (ell+j.val+1))

noncomputable instance instFintypeBlockSample (P : Finset ℕ) (ell T : ℕ) : Fintype (BlockSample P ell T) :=
  inferInstanceAs (Fintype (Σ j : Fin T, (P.powersetCard (ell+j.val+1))))

noncomputable def blockWeight (P : Finset ℕ) (ell T : ℕ)
    (a : BlockSample P ell T) : ℝ :=
  ((T : ℝ) * ((P.powersetCard (ell+a.1.val+1)).card : ℝ))⁻¹

def blockSet {P : Finset ℕ} {ell T : ℕ} (a : BlockSample P ell T) : Finset ℕ :=
  a.2.val

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RegularBlocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

noncomputable def selectedBlocks {r T : ℕ} {P : Fin r → Finset ℕ}
    {ell : Fin r → ℕ} (a : ∀ i, BlockSample (P i) (ell i) T) : Fin r → Finset ℕ :=
  fun i => blockSet (a i)

open MvPolynomial

noncomputable def cumulativeBlockPrimes {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun j => j.val ≤ i).biUnion B

def pathDegreeBudget (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ) : ℕ → ℕ
  | 0 => e
  | i+1 => patchDegreeBudget n A h (kernelDegreeBudget (d i) h (pathDegreeBudget n d A h e i))

noncomputable def physicalKernel {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (z : Fin n → ℤ) (i : ℕ) (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E) :=
  stagedEvaluationSpace (evaluationCell G.points s.1 z (cumulativeBlockPrimes B i)) (d i) E

noncomputable def physicalNext {n E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (z : Fin n → ℤ) (i : ℕ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (W : Submodule ℂ (totalSpace (σ := Fin n) (K := ℂ) E)) :
    Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n :=
  firstCoveringChild z s (kernelChildList G (d i) A h (pathDegreeBudget n d A h e i) s.1 W)

def PhysicalState {n : ℕ} (G : KernelGeometry n) (h e : ℕ) (z : Fin n → ℤ)
    (s : Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n) : Prop :=
  KernelParent h e s.1 ∧ s.2.On s.1 ∧ s.2.Bounded e G.height ∧ PatchPieceCovers s z

open MvPolynomial
open scoped BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_DeformedRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open MvPolynomial
open scoped Matrix

noncomputable def implicitApprox {ι κ R : Type*} [CommRing R]
    (Φ : κ → MvPolynomial (ι ⊕ κ) R) : ℕ → κ → MvPolynomial ι R
  | 0, _ => 0
  | n + 1, j => eval₂ C (Sum.elim X (implicitApprox Φ n)) (Φ j)

noncomputable def implicitJacobian {ι κ R : Type*} [CommRing R]
    (G : κ → MvPolynomial (ι ⊕ κ) R) : Matrix κ κ R :=
  Matrix.of (fun j a => eval (fun _ => 0) (pderiv (Sum.inr a) (G j)))

noncomputable def normalizedImplicitMap {ι κ R : Type*} [Fintype κ]
    [DecidableEq κ] [CommRing R] (G : κ → MvPolynomial (ι ⊕ κ) R)
    (j : κ) : MvPolynomial (ι ⊕ κ) R :=
  X (Sum.inr j) - ∑ a, C ((implicitJacobian G)⁻¹ j a) * G a

noncomputable def shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) : MvPolynomial κ R →+* MvPolynomial (Unit ⊕ κ) R :=
  eval₂Hom C (fun i => X (Sum.inr i) + C (a i))

@[simp] theorem eval_shiftedParameterPolynomial {κ R : Type*} [CommRing R]
    (a : κ → R) (p : MvPolynomial κ R) (z : Unit ⊕ κ → R) :
    eval z (shiftedParameterPolynomial a p) = eval (fun i => z (Sum.inr i) + a i) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [shiftedParameterPolynomial]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [shiftedParameterPolynomial]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ResidueBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial

noncomputable def partialEval {ι κ K : Type*} [CommSemiring K] (x : ι → K) :
    MvPolynomial (ι ⊕ κ) K →+* MvPolynomial κ K :=
  eval₂Hom C (Sum.elim (fun i => C (x i)) X)

@[simp] theorem eval_partialEval {ι κ K : Type*} [CommSemiring K]
    (x : ι → K) (y : κ → K) (p : MvPolynomial (ι ⊕ κ) K) :
    eval y (partialEval x p) = eval (Sum.elim x y) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [partialEval]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p a hp =>
    simp only [map_mul, hp]
    congr 1
    cases a <;> simp [partialEval]

end

open scoped BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_StoppingTrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

open scoped BigOperators

open MvPolynomial
open scoped BigOperators

noncomputable def IntegerPatch.goodResidues {n : ℕ} (P : IntegerPatch n)
    (K : Type*) [Field K] [Fintype K] : Finset (Fin n → K) := by
  classical
  exact Finset.univ.filter fun x =>
    (∀ i, eval x (MvPolynomial.map (Int.castRingHom K) (P.equations i)) = 0) ∧
    eval x (MvPolynomial.map (Int.castRingHom K) P.minor) ≠ 0

attribute [local instance] Classical.propDecidable

def residueTuple {n : ℕ} (Q : Finset ℕ) (z : Fin n → ℤ) :
    ∀ p : Q, Fin n → ZMod p.val := fun p i => (z i : ZMod p.val)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_AdaptiveFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def adaptiveStateAt {K V σ α : Type*} [Field K] [AddCommGroup V]
    [Module K V] (W : ℕ → σ → α → Submodule K V)
    (next : ℕ → σ → Submodule K V → σ) : ℕ → ℕ → σ → α → σ
  | 0, _, s, _ => s
  | m+1, i, s, a =>
    let t := adaptiveStateAt W next m i s a
    next (i+m) t (W (i+m) t a)

noncomputable def physicalStateAt {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n :=
  adaptiveStateAt (physicalKernel (E := E) G d z.val) (physicalNext G d A h e z.val) i 0 (start z) B

@[simp] theorem physicalStateAt_zero {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (z : G.points) : physicalStateAt (E := E) G d A h e start B 0 z = start z := rfl

noncomputable def pastBlockPrimes {r : ℕ} (B : Fin r → Finset ℕ) (i : ℕ) : Finset ℕ :=
  (Finset.univ.filter fun j => j.val < i).biUnion B

@[simp] theorem pastBlockPrimes_zero {r : ℕ} (B : Fin r → Finset ℕ) :
    pastBlockPrimes B 0 = ∅ := by simp [pastBlockPrimes]

noncomputable def physicalNode {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (i : ℕ) (z : G.points) :
    (Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n) ×
      (∀ p : pastBlockPrimes B i, Fin n → ZMod p.val) :=
  (physicalStateAt (E := E) G d A h e start B i z, residueTuple (pastBlockPrimes B i) z.val)

end

open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def activePoints {α : Type*} (S : Finset α) (stop : α → ℕ) (i : ℕ) : Finset α :=
  S.filter fun z => i ≤ stop z

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ResidueRelations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def physicalBranchAllowance {r : ℕ} (n : ℕ) (d : ℕ → ℕ) (A h e : ℕ)
    (B : Fin r → Finset ℕ) (M b q : Fin r → ℕ) (i : Fin r) : ℕ :=
  (2^(B i).card * ((pathDegreeBudget n d A h e i.val+1)^n)^(B i).card *
    M i ^ (q i*(B i).card+n*b i)) *
  (kernelCountBudget (d i.val) h (pathDegreeBudget n d A h e i.val) *
    patchCountBudget n A h (kernelDegreeBudget (d i.val) h (pathDegreeBudget n d A h e i.val)))

end

open MvPolynomial
open scoped BigOperators

noncomputable def shiftVariables {σ R : Type*} [CommRing R]
    (z : σ → R) (P : MvPolynomial σ R) : MvPolynomial σ R :=
  eval₂ C (fun i => X i + C (z i)) P

open Matrix

open Matrix

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_HilbertSimplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open scoped BigOperators

open scoped BigOperators
open MvPolynomial

noncomputable def monomialWeight {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (a : σ →₀ ℕ) : ℝ := ∑ i, ω i*(a i : ℝ)

noncomputable def weightedExponentBound {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : σ →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun i => ⌊T/ω i⌋₊)

noncomputable def weightedMonomials {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : Finset (σ →₀ ℕ) := by
  classical
  exact (Finset.Iic (weightedExponentBound ω T)).filter fun a => monomialWeight ω a ≤ T

noncomputable def weightedDegreeBound {σ : Type*} [Fintype σ]
    (ω : σ → ℝ) (T : ℝ) : ℕ := ∑ i, ⌊T/ω i⌋₊

noncomputable def weightedFunctions {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) :
    Submodule K (MvPolynomial σ K ⧸ I) :=
  Submodule.span K ((fun a => Ideal.Quotient.mk I (monomial a (1:K))) ''
    (weightedMonomials ω T : Set (σ →₀ ℕ)))

instance weightedFunctions_finite {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) :
    Module.Finite K (weightedFunctions I ω T) := by
  classical
  exact Module.Finite.span_of_finite K ((weightedMonomials ω T).finite_toSet.image _)

noncomputable def weightedHilbert {σ K : Type*} [Fintype σ] [Field K]
    (I : Ideal (MvPolynomial σ K)) (ω : σ → ℝ) (T : ℝ) : ℕ :=
  Module.finrank K (weightedFunctions I ω T)

end

open scoped BigOperators
open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrimePools
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def physicalPathProduct {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (z : G.points) : ℤ :=
  ((adaptiveStates (physicalKernel (E := E) G d z.val) (physicalNext G d A h e z.val)
    m 0 (start z) B).map (fun t => eval z.val t.2.minor)).prod

def PhysicalRegular {n r E : ℕ} (G : KernelGeometry n) (d : ℕ → ℕ)
    (A h e m : ℕ) (start : G.points → Ideal (MvPolynomial (Fin n) ℂ) × IntegerPatch n)
    (B : Fin r → Finset ℕ) (ξ : ℝ) (z : G.points) : Prop :=
  ∀ j, ((∑ p ∈ B j, if (p : ℤ) ∣ physicalPathProduct (E := E) G d A h e m start B z
    then (1 : ℝ) else 0) / (B j).card) ≤ ξ

end

section
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open scoped Classical

noncomputable def firstStop (r : ℕ) (P : ℕ → Prop) : ℕ :=
  Nat.find (show ∃ i, i = r ∨ P i from ⟨r,Or.inl rfl⟩)

end

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_DegreeSchedules
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators
open Matrix
open scoped BigOperators
open scoped BigOperators
namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

def physicalDegreeRecord (n A h : ℕ) (chooseDegree : ℕ → ℕ → ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | i+1 => patchDegreeBudget n A h
      (kernelDegreeBudget (chooseDegree i (physicalDegreeRecord n A h chooseDegree e i)) h
        (physicalDegreeRecord n A h chooseDegree e i))

end

open MvPolynomial
open scoped BigOperators Classical
attribute [local instance] Classical.propDecidable

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedSlabs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

def simplexPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (N+1)).biUnion Finset.HasAntidiagonal.antidiagonal

@[simp] theorem mem_simplexPairs (x : ℕ × ℕ) (N : ℕ) :
    x ∈ simplexPairs N ↔ x.1+x.2 ≤ N := by
  simp only [simplexPairs, Finset.mem_biUnion, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro h; exact ⟨_, by omega, rfl⟩

def weightedPairs (a b T : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (T+1)) ×ˢ (Finset.range (T+1))).filter
    (fun x => a*x.1+b*x.2 ≤ T)

end

abbrev NatTriple := ℕ × ℕ × ℕ

def tripleWeight (a b c : ℕ) (x : NatTriple) : ℕ := a*x.1+b*x.2.1+c*x.2.2

def weightedTriples (a b c T : ℕ) : Finset NatTriple :=
  ((Finset.range (T+1)) ×ˢ (Finset.range (T+1)) ×ˢ (Finset.range (T+1))).filter
    (fun x => tripleWeight a b c x ≤ T)

def tripleDivides (m x : NatTriple) : Prop := m.1 ≤ x.1 ∧ m.2.1 ≤ x.2.1 ∧ m.2.2 ≤ x.2.2

instance instDecidableTripleDivides (m x : NatTriple) : Decidable (tripleDivides m x) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def weightedNormal (a b c : ℕ) (m : NatTriple) (T : ℕ) : Finset NatTriple :=
  (weightedTriples a b c T).filter (fun x => ¬ tripleDivides m x)

def tripleShift (m : NatTriple) : NatTriple ↪ NatTriple where
  toFun x := (m.1+x.1,m.2.1+x.2.1,m.2.2+x.2.2)
  inj' := by
    intro x y h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg (fun x : NatTriple => x.2.1) h
    have h3 := congrArg (fun x : NatTriple => x.2.2) h
    simp only [Nat.add_left_cancel_iff] at h1 h2 h3
    exact Prod.ext h1 (Prod.ext h2 h3)

def firstSlab (i : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (i,x)
  inj' := by intro x y h; exact congrArg Prod.snd h

def secondSlab (u j : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (u+x.1,j,x.2)
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
      (congrArg (fun z : NatTriple => z.2.2) h)

def thirdSlab (u v k : ℕ) : (ℕ × ℕ) ↪ NatTriple where
  toFun x := (u+x.1,v+x.2,k)
  inj' := by
    intro x y h
    exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst h))
      (Nat.add_left_cancel (congrArg (fun z : NatTriple => z.2.1) h))

def firstSlabs (a b c u T : ℕ) : Finset NatTriple :=
  (Finset.range u).biUnion fun i => (weightedPairs b c (T-a*i)).map (firstSlab i)

def secondSlabs (a b c u v T : ℕ) : Finset NatTriple :=
  (Finset.range v).biUnion fun j => (weightedPairs a c (T-(a*u+b*j))).map (secondSlab u j)

def thirdSlabs (a b c u v w T : ℕ) : Finset NatTriple :=
  (Finset.range w).biUnion fun k => (weightedPairs a b (T-(a*u+b*v+c*k))).map (thirdSlab u v k)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedHypersurfaces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

@[simp] theorem firstSlab_apply (i : ℕ) (x : ℕ × ℕ) : firstSlab i x = (i,x) := rfl
@[simp] theorem secondSlab_apply (u j : ℕ) (x : ℕ × ℕ) : secondSlab u j x = (u+x.1,j,x.2) := rfl
@[simp] theorem thirdSlab_apply (u v k : ℕ) (x : ℕ × ℕ) : thirdSlab u v k x = (u+x.1,v+x.2,k) := rfl

noncomputable def normalErrorConst (a b c : ℕ) (m : NatTriple) : ℝ :=
  (m.1:ℝ)*((tripleWeight a b c m:ℝ)+2+4*(b*c : ℕ)) +
  (m.2.1:ℝ)*((tripleWeight a b c m:ℝ)+2+4*(a*c : ℕ)) +
  (m.2.2:ℝ)*((tripleWeight a b c m:ℝ)+2+4*(a*b : ℕ))

end

open MvPolynomial
open scoped BigOperators

noncomputable def weightedLift {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i => Polynomial.C (X i) * Polynomial.X ^ w i)

noncomputable def weightedSpace {σ K : Type*} [CommSemiring K] (w : σ → ℕ) (T : ℕ) :
    Submodule K (MvPolynomial σ K) :=
  restrictSupport K {m | Finsupp.weight w m ≤ T}

theorem mem_weightedSpace {σ K : Type*} [CommSemiring K] (w : σ → ℕ)
    (T : ℕ) (p : MvPolynomial σ K) :
    p ∈ weightedSpace w T ↔ weightedTotalDegree w p ≤ T := by
  classical
  simp only [weightedSpace, mem_restrictSupport_iff, weightedTotalDegree,
    Finset.sup_le_iff, Set.subset_def, Finset.mem_coe, Set.mem_ofPred_eq]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ComplexValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI


namespace QuarticPowerFree
open MvPolynomial

noncomputable def tripleFinsuppEquiv : (Fin 3 →₀ ℕ) ≃ NatTriple :=
  Finsupp.equivFunOnFinite.trans
    { toFun := fun f => (f 0, f 1, f 2)
      invFun := fun x => ![x.1, x.2.1, x.2.2]
      left_inv := by intro f; funext i; fin_cases i <;> rfl
      right_inv := by rintro ⟨x,y,z⟩; rfl }

def tripleWeights (a b c : ℕ) : Fin 3 → ℕ := ![a,b,c]

end QuarticPowerFree


open Polynomial Matrix
open scoped BigOperators

namespace QuarticPowerFree.ComplexValues

def signedDivisors (r : ℤ) : Finset ℤ :=
  (r.natAbs.divisors.image (fun n : ℕ => (n : ℤ))) ∪
    (r.natAbs.divisors.image (fun n : ℕ => -(n : ℤ)))

def interpolationRow {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (i : Option ι) : Fin (a + 1) ⊕ Fin (b + 1) → R :=
  match i with
  | none => Pi.single (Sum.inr ⟨b, Nat.lt_succ_self b⟩) 1
  | some t => Sum.elim (fun j => s t ^ j.val) (fun j => -(v t * s t ^ j.val))

def interpolationMatrix {R ι : Type*} [CommRing R] {a b : ℕ}
    (s v : ι → R) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    Matrix (Fin (a + 1) ⊕ Fin (b + 1)) (Fin (a + 1) ⊕ Fin (b + 1)) R :=
  Matrix.of (fun j => interpolationRow s v (e j))

noncomputable def interpolationCramer {ι : Type*} [Fintype ι] {a b : ℕ}
    (s v : ι → ℤ) (e : (Fin (a + 1) ⊕ Fin (b + 1)) ≃ Option ι) :
    Fin (a + 1) ⊕ Fin (b + 1) → ℤ := by
  classical
  exact (interpolationMatrix s v e).cramer (fun j => if e j = none then 1 else 0)

def interpolationHeight (D : ℕ) (H : ℝ) : ℝ :=
  (Nat.factorial (2 * D + 2) : ℝ) * H ^ ((D + 1) * (2 * D + 2))

def rationalResultantConstant (D : ℕ) : ℝ :=
  (Nat.factorial (2 * D) : ℝ) * (Nat.factorial (2 * D + 2) : ℝ) ^ (2 * D)

def rationalResultantExponent (D : ℕ) : ℕ := 2 * D * ((D + 1) * (2 * D + 2))

open Filter

end QuarticPowerFree.ComplexValues

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_CurveAlternatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial
open scoped BigOperators Classical

noncomputable def binaryPolynomialEquiv (K : Type*) [CommSemiring K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (finSuccEquiv K 1).trans (Polynomial.mapAlgEquiv (uniqueAlgEquiv K (Fin 1)))

@[simp] theorem binaryPolynomialEquiv_natDegree {K : Type*} [CommSemiring K]
    (q : MvPolynomial (Fin 2) K) : (binaryPolynomialEquiv K q).natDegree = q.degreeOf 0 := by
  rw [binaryPolynomialEquiv,AlgEquiv.trans_apply,Polynomial.coe_mapAlgEquiv,
    Polynomial.natDegree_map_eq_of_injective (uniqueAlgEquiv K (Fin 1)).injective,
    natDegree_finSuccEquiv]

noncomputable def binaryStripExponent {M : ℕ} (i : Fin 2 × Fin (M+1)) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 i.1.val + Finsupp.single 1 i.2.val

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_SelectedPrimes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial
open scoped BigOperators Classical

noncomputable def pointEvaluation {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) :
    (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] K :=
  Ideal.Quotient.liftₐ I (MvPolynomial.aeval (fun j => (z j : K))) (by
    intro p hp
    exact hz p hp)

@[simp] theorem pointEvaluation_X {n : ℕ} {K : Type*} [Field K]
    (I : Ideal (MvPolynomial (Fin n) K)) (z : Fin n → ℤ) (hz : PointOn I z) (j : Fin n) :
    pointEvaluation I z hz (Ideal.Quotient.mk I (X j)) = (z j:K) := by
  change MvPolynomial.aeval (fun i => (z i:K)) (X j) = _
  simp

noncomputable def directSurface {K : Type*} [CommRing K] (f : Polynomial K) (k : ℕ) :
    MvPolynomial (Fin 3) K := Polynomial.eval₂ C (X 0) f - X 1*(X 2)^k

noncomputable def directSurfaceEquiv (K : Type*) [CommRing K] :
    MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
  (renameEquiv K (Equiv.swap 0 1)).trans (finSuccEquiv K 2)

@[simp] theorem directSurfaceEquiv_X0 {K : Type*} [CommRing K] :
    directSurfaceEquiv K (X 0) = Polynomial.C (X 0) := by
  simp [directSurfaceEquiv,finSuccEquiv_apply]
  rfl

@[simp] theorem directSurfaceEquiv_X1 {K : Type*} [CommRing K] :
    directSurfaceEquiv K (X 1) = Polynomial.X := by
  simp [directSurfaceEquiv,finSuccEquiv_apply]

@[simp] theorem directSurfaceEquiv_X2 {K : Type*} [CommRing K] :
    directSurfaceEquiv K (X 2) = Polynomial.C (X 1) := by
  simp [directSurfaceEquiv,Equiv.swap_apply_of_ne_of_ne,finSuccEquiv_apply]
  rfl

@[simp] theorem directSurfaceEquiv_C {K : Type*} [CommRing K] (c : K) :
    directSurfaceEquiv K (C c) = Polynomial.C (C c) := by
  simp [directSurfaceEquiv,finSuccEquiv_apply]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairAlgebras
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open MvPolynomial MonomialOrder
open scoped MonomialOrder

noncomputable def pairRelation {n : ℕ} {R : Type*} [CommRing R] (k : ℕ) (q : Fin n → R)
    (i : Fin n) : MvPolynomial (Fin n ⊕ Fin n) R :=
  X (Sum.inl i) ^ k * X (Sum.inr i) - C (q i)

def PairNormal {n : ℕ} (k : ℕ) (m : (Fin n ⊕ Fin n) →₀ ℕ) : Prop :=
  ∀ i, m (Sum.inl i) < k ∨ m (Sum.inr i) = 0

theorem pair_normal_form {n : ℕ} {R : Type*} [CommRing R] [Nontrivial R]
    (k : ℕ) (q : Fin n → R) (p : MvPolynomial (Fin n ⊕ Fin n) R) :
    ∃ (g : Fin n →₀ MvPolynomial (Fin n ⊕ Fin n) R)
      (r : MvPolynomial (Fin n ⊕ Fin n) R),
      p = Finsupp.linearCombination _ (pairRelation k q) g + r ∧
      ∀ m ∈ r.support, PairNormal k m := by
  classical
  let o : LinearOrder (Fin n ⊕ Fin n) :=
    LinearOrder.lift' (Fintype.equivFin _) (Fintype.equivFin _).injective
  have : @WellFoundedGT (Fin n ⊕ Fin n) o.toLT := ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
  let e : Fin n → ((Fin n ⊕ Fin n) →₀ ℕ) := fun i =>
    Finsupp.single (Sum.inl i) k + Finsupp.single (Sum.inr i) 1
  have he (i) : X (Sum.inl i) ^ k * X (Sum.inr i) = monomial (e i) (1 : R) := by
    rw [X_pow_eq_monomial, X, monomial_mul_monomial, one_mul]
  have hlt (i) : degLex.degree (C (q i)) ≺[degLex]
      degLex.degree (monomial (e i) (1 : R)) := by
    apply lt_of_not_ge
    intro h
    have ht := MvPolynomial.degLex_totalDegree_monotone h
    rw [totalDegree_C, totalDegree_monomial _ one_ne_zero] at ht
    have hp : 1 ≤ (e i).sum (fun _ a => a) := by
      exact (show 1 ≤ (e i) (Sum.inr i) by simp [e]).trans
        (by simpa using Finsupp.single_le_sum (g := fun _ a => a) (e i) (fun _ _ => Nat.zero_le _) (Sum.inr i))
    omega
  have hd (i) : degLex.degree (pairRelation k q i) = e i := by
    rw [pairRelation, he, degLex.degree_sub_of_lt (hlt i),
      degLex.degree_monomial, ite_eq_right one_ne_zero]
  have hu (i) : IsUnit (degLex.leadingCoeff (pairRelation k q i)) := by
    rw [pairRelation, he, degLex.leadingCoeff_sub_of_lt (hlt i),
      degLex.leadingCoeff_monomial]
    exact isUnit_one
  obtain ⟨g, r, h, _, hr⟩ := MonomialOrder.div hu p
  refine ⟨g, r, h, ?_⟩
  intro m hm i
  have hnd := hr m hm i
  rw [hd] at hnd
  by_contra! hn
  apply hnd
  intro a
  cases a with
  | inl j => by_cases h : j = i <;> simp [e, h, hn.1]
  | inr j =>
    by_cases h : j = i
    · simp [e, h]; omega
    · simp [e, h]

def pairExponent {n : ℕ} (k : ℕ) (m : (Fin n ⊕ Fin n) →₀ ℕ) : Fin n → ℤ :=
  fun i => (m (Sum.inl i) : ℤ) - (k : ℤ) * m (Sum.inr i)

theorem pairExponent_injective_normal {n k : ℕ} {m m' : (Fin n ⊕ Fin n) →₀ ℕ}
    (hm : PairNormal k m) (hm' : PairNormal k m')
    (h : pairExponent k m = pairExponent k m') : m = m' := by
  have hc (i) : m (Sum.inl i) = m' (Sum.inl i) ∧
      m (Sum.inr i) = m' (Sum.inr i) := by
    have he := congrFun h i
    dsimp [pairExponent] at he
    have hN : (0 : ℤ) ≤ m (Sum.inl i) := Int.natCast_nonneg _
    have hN' : (0 : ℤ) ≤ m' (Sum.inl i) := Int.natCast_nonneg _
    have hK : (0 : ℤ) ≤ k := Int.natCast_nonneg _
    have hM : (m (Sum.inl i) : ℤ) < k ∨ (m (Sum.inr i) : ℤ) = 0 := by
      exact_mod_cast hm i
    have hM' : (m' (Sum.inl i) : ℤ) < k ∨ (m' (Sum.inr i) : ℤ) = 0 := by
      exact_mod_cast hm' i
    have hs : (m (Sum.inr i) : ℤ) = m' (Sum.inr i) := by
      rcases hM with ha | hb <;> rcases hM' with ha' | hb'
      · by_contra hs
        rcases lt_or_gt_of_ne hs with hs | hs
        · have ht := mul_le_mul_of_nonneg_left (show
            (m (Sum.inr i) : ℤ) + 1 ≤ m' (Sum.inr i) by omega) hK
          nlinarith
        · have ht := mul_le_mul_of_nonneg_left (show
            (m' (Sum.inr i) : ℤ) + 1 ≤ m (Sum.inr i) by omega) hK
          nlinarith
      · by_contra hs
        have ht := mul_le_mul_of_nonneg_left
          (show (1 : ℤ) ≤ m (Sum.inr i) by omega) hK
        rw [hb', mul_zero] at he
        nlinarith
      · by_contra hs
        have ht := mul_le_mul_of_nonneg_left
          (show (1 : ℤ) ≤ m' (Sum.inr i) by omega) hK
        rw [hb, mul_zero] at he
        nlinarith
      · omega
    rw [hs] at he
    constructor <;> omega
  ext a
  cases a with
  | inl i => exact (hc i).1
  | inr i => exact (hc i).2

noncomputable def pairLaurentMap {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) :
    MvPolynomial (Fin n ⊕ Fin n) R →+* AddMonoidAlgebra R (Fin n → ℤ) :=
  eval₂Hom AddMonoidAlgebra.singleZeroRingHom
    (Sum.elim (fun i => AddMonoidAlgebra.single (Pi.single i 1) 1)
      (fun i => AddMonoidAlgebra.single (Pi.single i (-(k : ℤ))) (q i)))

theorem pairLaurentMap_monomial {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (m : (Fin n ⊕ Fin n) →₀ ℕ) (c : R) :
    pairLaurentMap k q (monomial m c) =
      AddMonoidAlgebra.single (pairExponent k m)
        (c * ∏ i, q i ^ m (Sum.inr i)) := by
  classical
  rw [pairLaurentMap, eval₂Hom_monomial]
  rw [Finsupp.prod_fintype _ _ (by simp)]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.prod_single,
    Finset.prod_const_one, AddMonoidAlgebra.single_mul_single, one_mul]
  change AddMonoidAlgebra.single 0 c *
      AddMonoidAlgebra.single _ (∏ i, q i ^ m (Sum.inr i)) = _
  rw [AddMonoidAlgebra.single_mul_single, zero_add]
  congr 1
  ext i
  simp [pairExponent, Finset.sum_apply, Pi.single_apply, mul_comm, sub_eq_add_neg]

theorem pairLaurentMap_relation {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    pairLaurentMap k q (pairRelation k q i) = 0 := by
  classical
  simp only [pairRelation, map_sub, map_mul, map_pow]
  simp only [pairLaurentMap, eval₂Hom_X', eval₂Hom_C, Sum.elim_inl, Sum.elim_inr,
    AddMonoidAlgebra.single_pow, one_pow, AddMonoidAlgebra.single_mul_single, one_mul]
  have he : k • Pi.single i (1 : ℤ) + Pi.single i (-(k : ℤ)) = (0 : Fin n → ℤ) := by
    ext j
    by_cases h : j = i <;> simp [h]
  rw [he]
  exact sub_self _

theorem pairLaurentMap_normal_injective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0)
    (r : MvPolynomial (Fin n ⊕ Fin n) R)
    (hr : ∀ m ∈ r.support, PairNormal k m) (he : pairLaurentMap k q r = 0) :
    r = 0 := by
  classical
  ext m
  by_cases hm : m ∈ r.support
  · have hc : (pairLaurentMap k q r).coeff (pairExponent k m) =
        r.coeff m * ∏ i, q i ^ m (Sum.inr i) := by
      conv_lhs => rw [r.as_sum, map_sum]
      rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
        Finset.sum_eq_single_of_mem m hm]
      · simp [pairLaurentMap_monomial, AddMonoidAlgebra.coeff_single]
      · intro m' hm' hne
        have hE : pairExponent k m' ≠ pairExponent k m :=
          fun hh => hne (pairExponent_injective_normal (hr m' hm') (hr m hm) hh)
        simp [pairLaurentMap_monomial, AddMonoidAlgebra.coeff_single, hE]
    rw [he] at hc
    have hp : (∏ i, q i ^ m (Sum.inr i)) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hq i))
    have hc0 : r.coeff m = 0 := (mul_eq_zero.mp hc.symm).resolve_right hp
    simpa using hc0
  · simpa using notMem_support_iff.mp hm

theorem pair_ideal_eq_ker {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Ideal.span (Set.range (pairRelation k q)) = RingHom.ker (pairLaurentMap k q) := by
  classical
  have hle : Ideal.span (Set.range (pairRelation k q)) ≤
      RingHom.ker (pairLaurentMap k q) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact pairLaurentMap_relation k q i
  apply le_antisymm hle
  intro p hp
  obtain ⟨g, r, hpr, hr⟩ := pair_normal_form k q p
  have hg : Finsupp.linearCombination _ (pairRelation k q) g ∈
      Ideal.span (Set.range (pairRelation k q)) := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum]
    apply Ideal.sum_mem
    intro i _
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
  have her : pairLaurentMap k q r = 0 := by
    have he := congrArg (pairLaurentMap k q) hpr
    rw [map_add, show pairLaurentMap k q p = 0 from hp,
      show pairLaurentMap k q (Finsupp.linearCombination _ (pairRelation k q) g) = 0
        from hle hg, zero_add] at he
    exact he.symm
  rw [pairLaurentMap_normal_injective k q hq r hr her, add_zero] at hpr
  exact hpr ▸ hg

theorem pair_normal_quotient_bijective {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Function.Bijective
      (((Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))).toLinearMap).comp
        (restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}).subtype) := by
  classical
  let I := Ideal.span (Set.range (pairRelation k q))
  let M := restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}
  let f := ((Ideal.Quotient.mkₐ R I).toLinearMap).comp M.subtype
  change Function.Bijective f
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro p hp
    apply Subtype.ext
    apply pairLaurentMap_normal_injective k q hq p.val (fun m hm => p.property hm)
    have hmem : p.val ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hp
    change p.val ∈ RingHom.ker (pairLaurentMap k q)
    rwa [← pair_ideal_eq_ker k q hq]
  · intro y
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨g, r, hpr, hr⟩ := pair_normal_form k q p
    refine ⟨⟨r, fun m hm => hr m hm⟩, ?_⟩
    have hg : Finsupp.linearCombination _ (pairRelation k q) g ∈ I := by
      rw [Finsupp.linearCombination_apply, Finsupp.sum]
      apply Ideal.sum_mem
      intro i _
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
    change (Ideal.Quotient.mk I) r = (Ideal.Quotient.mk I) p
    rw [hpr, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hg, zero_add]

noncomputable def pairNormalEquiv {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m} ≃ₗ[R]
      MvPolynomial (Fin n ⊕ Fin n) R ⧸ Ideal.span (Set.range (pairRelation k q)) :=
  LinearEquiv.ofBijective
    (((Ideal.Quotient.mkₐ R (Ideal.span (Set.range (pairRelation k q)))).toLinearMap).comp
      (restrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}).subtype)
    (pair_normal_quotient_bijective k q hq)

noncomputable def pairNormalBasis {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]
    (k : ℕ) (q : Fin n → R) (hq : ∀ i, q i ≠ 0) :
    Module.Basis {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m} R
      (MvPolynomial (Fin n ⊕ Fin n) R ⧸ Ideal.span (Set.range (pairRelation k q))) :=
  (basisRestrictSupport R {m : (Fin n ⊕ Fin n) →₀ ℕ | PairNormal k m}).map (pairNormalEquiv k q hq)

abbrev PairRing {n : ℕ} {R : Type*} [CommRing R] (k : ℕ) (q : Fin n → R) :=
  MvPolynomial (Fin n ⊕ Fin n) R ⧸ Ideal.span (Set.range (pairRelation k q))

noncomputable def pairCoeffs {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k : ℕ) (q : Fin n → R) : R →ₐ[K] PairRing k q :=
  (Ideal.Quotient.mkₐ K _).comp (IsScalarTower.toAlgHom K R _)

noncomputable def pairScalePre {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R) :
    MvPolynomial (Fin n ⊕ Fin n) R →ₐ[K] Polynomial (PairRing k q) :=
  MvPolynomial.aevalTower ((Polynomial.mapAlgHom (pairCoeffs (K := K) k q)).comp L)
    (fun i : Fin n ⊕ Fin n => Polynomial.monomial (Sum.elim (fun _ => A) (fun _ => B) i)
      (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))) (X i)))

theorem pairScalePre_relation {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) (i : Fin n) :
    pairScalePre k A B q L (pairRelation k q i) = 0 := by
  have hr : (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))))
      (X (Sum.inl i)^k * X (Sum.inr i)) = pairCoeffs (K := K) k q (q i) := by
    have hh : Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q)))
        (pairRelation k q i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
    simpa [pairRelation, pairCoeffs, sub_eq_zero] using hh
  simp only [pairRelation, map_sub, map_mul, map_pow, pairScalePre,
    MvPolynomial.aevalTower_X, Sum.elim_inl, Sum.elim_inr,
    MvPolynomial.aevalTower_C, AlgHom.comp_apply, hq,
    Polynomial.mapAlgHom_monomial,
    Polynomial.monomial_pow, Polynomial.monomial_mul_monomial, Nat.mul_comm A k]
  rw [← map_pow, ← map_mul, hr, sub_self]

noncomputable def pairScale {n : ℕ} {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (k A B : ℕ) (q : Fin n → R) (L : R →ₐ[K] Polynomial R)
    (hq : ∀ i, L (q i) = Polynomial.monomial (k*A+B) (q i)) :
    PairRing k q →ₐ[K] Polynomial (PairRing k q) :=
  Ideal.Quotient.liftₐ _ (pairScalePre k A B q L) (by
    have hh : Ideal.span (Set.range (pairRelation k q)) ≤
        RingHom.ker (pairScalePre k A B q L).toRingHom := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      exact pairScalePre_relation k A B q L hq i
    exact fun x hx => hh hx)

noncomputable def normPair_weightedLift {σ R : Type*} [CommSemiring R] (w : σ → ℕ) :
    MvPolynomial σ R →+* Polynomial (MvPolynomial σ R) :=
  eval₂Hom (Polynomial.C.comp C)
    (fun i => Polynomial.C (X i) * Polynomial.X ^ w i)

noncomputable def weightedScale {σ K : Type*} [Field K] (w : σ → ℕ) :
    MvPolynomial σ K →ₐ[K] Polynomial (MvPolynomial σ K) where
  toRingHom := normPair_weightedLift w
  commutes' := by
    intro r
    simp [normPair_weightedLift, MvPolynomial.algebraMap_eq, Polynomial.algebraMap_apply]

theorem weightedScale_X {σ K : Type*} [Field K] (w : σ → ℕ) (i : σ) :
    weightedScale (K := K) w (X i) = Polynomial.monomial (w i) (X i) := by
  simp [weightedScale, normPair_weightedLift, Polynomial.C_mul_X_pow_eq_monomial]

theorem weightedScale_C {σ K : Type*} [Field K] (w : σ → ℕ) (r : K) :
    weightedScale w (MvPolynomial.C r) = Polynomial.monomial 0 (MvPolynomial.C r) := by
  simp [weightedScale, normPair_weightedLift]

def triplePairWeights (A B : ℕ) : Fin 3 → ℕ := ![A,B,1]

noncomputable def pairConeQ {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin n) : MvPolynomial (Fin 3) K :=
  X 0 ^ k * X 1 + C (θ i) * X 2 ^ (k*A+B)

theorem pairConeQ_ne_zero {n : ℕ} {K : Type*} [Field K] (k A B : ℕ)
    (hB : 0 < B) (θ : Fin n → K) (i : Fin n) : pairConeQ k A B θ i ≠ 0 := by
  have hQ : k*A+B ≠ 0 := by omega
  intro hz
  have hh := congrArg (MvPolynomial.eval (fun i : Fin 3 => if i = 2 then (0:K) else 1)) hz
  simp only [pairConeQ, map_add, map_mul, map_pow, MvPolynomial.eval_X,
    MvPolynomial.eval_C, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, ite_false, ite_true, one_pow, one_mul,
    zero_pow hQ, mul_zero, add_zero, map_zero] at hh
  exact one_ne_zero hh

theorem pairConeQ_homogeneous {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin n) :
    weightedScale (triplePairWeights A B) (pairConeQ k A B θ i) =
      Polynomial.monomial (k*A+B) (pairConeQ k A B θ i) := by
  simp only [pairConeQ, map_add, map_mul, map_pow, weightedScale_X, weightedScale_C,
    triplePairWeights, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Polynomial.monomial_pow, Polynomial.monomial_mul_monomial,
    Nat.one_mul, Nat.zero_add, Nat.mul_comm A k]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

noncomputable def homogeneousSpace {K R : Type*} [Field K] [CommRing R] [Algebra K R]
    (L : R →ₐ[K] Polynomial R) (T : ℕ) : Submodule K R where
  carrier := {x | L x = Polynomial.monomial T x}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change L (x+y) = Polynomial.monomial T (x+y)
    change L x = Polynomial.monomial T x at hx
    change L y = Polynomial.monomial T y at hy
    rw [map_add, hx, hy, map_add]
  smul_mem' := by
    intro c x hx
    change L (c • x) = Polynomial.monomial T (c • x)
    change L x = Polynomial.monomial T x at hx
    rw [map_smul, hx, Polynomial.smul_monomial]

open scoped BigOperators

open scoped BigOperators

noncomputable def normPair_simplexTuple (h N : ℕ) : Finset (Fin h → ℕ) :=
  (Finset.range (N+1)).biUnion (Finset.Nat.antidiagonalTuple h)

@[simp] theorem normPair_mem_simplexTuple {h N : ℕ} (x : Fin h → ℕ) :
    x ∈ normPair_simplexTuple h N ↔ ∑ i, x i ≤ N := by
  classical
  simp only [normPair_simplexTuple, Finset.mem_biUnion, Finset.mem_range,
    Finset.Nat.mem_antidiagonalTuple]
  constructor
  · rintro ⟨n, hn, he⟩; omega
  · intro hx; exact ⟨_, by omega, rfl⟩

def weightedTuple {h : ℕ} (w : Fin h → ℕ) (T : ℕ) : Finset (Fin h → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (T+1))).filter
    (fun x => ∑ i, w i*x i ≤ T)

def tupleQuot {h : ℕ} (m : Fin h → ℕ) (x : Fin h → ℕ) : Fin h → ℕ := fun i => x i / m i

def tupleRem {h : ℕ} (m : Fin h → ℕ) (x : Fin h → ℕ) : Fin h → ℕ := fun i => x i % m i

noncomputable def shiftedTupleCount {h : ℕ} (w : Fin h → ℕ) (e T : ℕ) : ℕ :=
  if e ≤ T then (weightedTuple w (T-e)).card else 0

def PairSector (u v : ℕ) := Fin u ⊕ Fin v

instance instFintypePairSector (u v : ℕ) : Fintype (PairSector u v) := inferInstanceAs (Fintype (Fin u ⊕ Fin v))
instance instDecidableEqPairSector (u v : ℕ) : DecidableEq (PairSector u v) := inferInstanceAs (DecidableEq (Fin u ⊕ Fin v))

def sectorPoint {u v : ℕ} (c : PairSector u v) (x : ℕ) : ℕ × ℕ :=
  match c with
  | Sum.inl r => (r, x)
  | Sum.inr r => (u+x, r)

def sectorWeight (A B : ℕ) {u v : ℕ} (c : PairSector u v) : ℕ :=
  match c with
  | Sum.inl _ => B
  | Sum.inr _ => A

def sectorShift (A B : ℕ) {u v : ℕ} (c : PairSector u v) : ℕ :=
  match c with
  | Sum.inl r => A*r
  | Sum.inr r => A*u+B*r

def normalPairTuples {h : ℕ} (A B : ℕ) (u v : Fin h → ℕ) (T : ℕ) :
    Finset (Fin h → ℕ × ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (T+1) ×ˢ Finset.range (T+1))).filter
    (fun p => (∀ i, (p i).1 < u i ∨ (p i).2 < v i) ∧
      ∑ i, (A*(p i).1+B*(p i).2) ≤ T)

noncomputable def sectorTuples {h : ℕ} (A B : ℕ) (u v : Fin h → ℕ) (T : ℕ) :
    Finset (Σ _c : (i : Fin h) → PairSector (u i) (v i), Fin h → ℕ) :=
  Finset.univ.sigma (fun c =>
    if ∑ i, sectorShift A B (c i) ≤ T then
      weightedTuple (fun i => sectorWeight A B (c i)) (T-∑ i, sectorShift A B (c i))
    else ∅)

def ambientPairTuples (h A B k T : ℕ) : Finset (Fin (h+1) → ℕ × ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (T+1) ×ˢ Finset.range (T+1))).filter
    (fun p => (∀ i : Fin h, (p i.succ).1 < k ∨ (p i.succ).2 = 0) ∧
      ∑ i, (A*(p i).1+B*(p i).2) ≤ T)

theorem mem_ambientPairTuples {h A B k T : ℕ} (hA : 0 < A) (hB : 0 < B)
    (p : Fin (h+1) → ℕ × ℕ) :
    p ∈ ambientPairTuples h A B k T ↔
      (∀ i : Fin h, (p i.succ).1 < k ∨ (p i.succ).2 = 0) ∧
        ∑ i, (A*(p i).1+B*(p i).2) ≤ T := by
  classical
  simp only [ambientPairTuples, Finset.mem_filter, Fintype.mem_piFinset,
    Finset.mem_product, Finset.mem_range]
  constructor
  · exact fun h => h.2
  · intro hp
    refine ⟨fun i => ?_, hp⟩
    have hi := Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Nat.zero_le (A*(p j).1+B*(p j).2)) (Finset.mem_univ i)
    have ha : (p i).1 ≤ A*(p i).1 := by nlinarith
    have hb : (p i).2 ≤ B*(p i).2 := by nlinarith
    constructor <;> omega

def pairTranslate {h : ℕ} (u v : ℕ) (p : Fin (h+1) → ℕ × ℕ) :
    Fin (h+1) → ℕ × ℕ :=
  Fin.cons ((p 0).1+u, (p 0).2+v) (fun i => p i.succ)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree
open scoped BigOperators
abbrev PairBasisIndex (n k : ℕ) :=
  (Fin 3 →₀ ℕ) × {m : (Fin n ⊕ Fin n) →₀ ℕ // PairNormal k m}

def pairIndexToTuple {n k : ℕ} (i : PairBasisIndex n k) : Fin (n+1) → ℕ × ℕ :=
  Fin.cons (i.1 0, i.1 1) (fun j => (i.2.val (Sum.inl j), i.2.val (Sum.inr j)))

noncomputable def tupleBasisIndex {n k : ℕ} (p : Fin (n+1) → ℕ × ℕ) (t : ℕ)
    (hp : ∀ i : Fin n, (p i.succ).1 < k ∨ (p i.succ).2 = 0) : PairBasisIndex n k :=
  (Finsupp.equivFunOnFinite.symm ![(p 0).1, (p 0).2, t],
   ⟨Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (p i.succ).1) (fun i => (p i.succ).2)),
    by simpa [PairNormal] using hp⟩)

noncomputable def pairBasisWeight {n k : ℕ} (A B : ℕ) (i : PairBasisIndex n k) : ℕ :=
  Finsupp.weight (triplePairWeights A B) i.1 +
  Finsupp.weight (Sum.elim (fun _ => A) (fun _ => B)) i.2.val

theorem pairIndexToTuple_normal {n k : ℕ} (i : PairBasisIndex n k) :
    ∀ j : Fin n, (pairIndexToTuple i j.succ).1 < k ∨
      (pairIndexToTuple i j.succ).2 = 0 := by
  simpa [pairIndexToTuple, PairNormal] using i.2.property

theorem pairBasisWeight_eq {n k : ℕ} (A B : ℕ) (i : PairBasisIndex n k) :
    pairBasisWeight A B i = i.1 2 + ∑ j, (A*(pairIndexToTuple i j).1+B*(pairIndexToTuple i j).2) := by
  simp only [pairBasisWeight, Finsupp.weight_eq_sum, smul_eq_mul,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  have h3 : (∑ j : Fin 3, i.1 j * triplePairWeights A B j) =
      i.1 0 * A + i.1 1 * B + i.1 2 := by
    simp [Fin.sum_univ_succ, triplePairWeights, add_assoc]
  rw [h3, Fin.sum_univ_succ]
  simp only [pairIndexToTuple, Fin.cons_zero, Fin.cons_succ,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

theorem pairIndexToTuple_tupleBasisIndex {n k : ℕ} (p : Fin (n+1) → ℕ × ℕ)
    (t : ℕ) (hp : ∀ i : Fin n, (p i.succ).1 < k ∨ (p i.succ).2 = 0) :
    pairIndexToTuple (tupleBasisIndex p t hp) = p := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairIndexToTuple, tupleBasisIndex]
  · simp [pairIndexToTuple, tupleBasisIndex]

theorem tupleBasisIndex_pairIndexToTuple {n k : ℕ} (i : PairBasisIndex n k) :
    tupleBasisIndex (pairIndexToTuple i) (i.1 2) (pairIndexToTuple_normal i) = i := by
  apply Prod.ext
  · ext j
    fin_cases j <;> simp [tupleBasisIndex, pairIndexToTuple]
  · apply Subtype.ext
    ext j
    cases j <;> simp [tupleBasisIndex, pairIndexToTuple]

noncomputable def pairBasisWeightEquiv {n k A B : ℕ} (hA : 0 < A) (hB : 0 < B) (T : ℕ) :
    {i : PairBasisIndex n k // pairBasisWeight A B i = T} ≃
      {p // p ∈ ambientPairTuples n A B k T} where
  toFun i := ⟨pairIndexToTuple i.val, (mem_ambientPairTuples hA hB _).mpr
    ⟨pairIndexToTuple_normal i.val, by
      have hi := i.property
      rw [pairBasisWeight_eq] at hi
      omega⟩⟩
  invFun p := ⟨tupleBasisIndex p.val (T-∑ j, (A*(p.val j).1+B*(p.val j).2))
    ((mem_ambientPairTuples hA hB p.val).mp p.property).1, by
      rw [pairBasisWeight_eq, pairIndexToTuple_tupleBasisIndex]
      change (T - ∑ j, (A*(p.val j).1+B*(p.val j).2)) +
        (∑ j, (A*(p.val j).1+B*(p.val j).2)) = T
      exact Nat.sub_add_cancel ((mem_ambientPairTuples hA hB p.val).mp p.property).2⟩
  left_inv i := by
    apply Subtype.ext
    have hi := i.property
    rw [pairBasisWeight_eq] at hi
    have ht : T - ∑ j, (A*(pairIndexToTuple i.val j).1+B*(pairIndexToTuple i.val j).2) = i.val.1 2 := by omega
    dsimp only
    rw [ht]
    exact tupleBasisIndex_pairIndexToTuple i.val
  right_inv p := by
    apply Subtype.ext
    dsimp only
    exact pairIndexToTuple_tupleBasisIndex p.val _ _

abbrev PairCone {n : ℕ} {K : Type*} [Field K] (k A B : ℕ) (θ : Fin n → K) :=
  PairRing k (pairConeQ k A B θ)

noncomputable def pairConeScale {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    PairCone k A B θ →ₐ[K] Polynomial (PairCone k A B θ) :=
  pairScale k A B (pairConeQ k A B θ) (weightedScale (triplePairWeights A B))
    (pairConeQ_homogeneous k A B θ)

noncomputable def pairConeBasis {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) :
    Module.Basis (PairBasisIndex n k) K (PairCone k A B θ) :=
  (MvPolynomial.basisMonomials (Fin 3) K).smulTower
    (pairNormalBasis k (pairConeQ k A B θ) (pairConeQ_ne_zero k A B hB θ))

open MvPolynomial

noncomputable def pairMap {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (f : R →+* S) :
    PairRing k q →+* PairRing k (fun i => f (q i)) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (MvPolynomial.map f)) (by
    have h : Ideal.span (Set.range (pairRelation k q)) ≤
        RingHom.ker ((Ideal.Quotient.mk (Ideal.span
          (Set.range (pairRelation k (fun i => f (q i)))))).comp (MvPolynomial.map f)) := by
      apply Ideal.span_le.mpr
      rintro _ ⟨i,rfl⟩
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      have hm : MvPolynomial.map f (pairRelation k q i) =
          pairRelation k (fun i => f (q i)) i := by simp [pairRelation]
      change MvPolynomial.map f (pairRelation k q i) ∈ _
      rw [hm]
      exact Ideal.subset_span ⟨i,rfl⟩
    exact fun p hp => h hp)

@[simp] theorem pairMap_mk {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (f : R →+* S) (p : MvPolynomial (Fin n ⊕ Fin n) R) :
    pairMap k q f (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

noncomputable def pairCoeffMap {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) : R →+* PairRing k q :=
  (Ideal.Quotient.mk _).comp MvPolynomial.C

open Classical

noncomputable def eraseVariable {σ R : Type*} [CommRing R] (i : σ) :
    MvPolynomial σ R →+* MvPolynomial σ R := by
  classical
  exact eval₂Hom C (fun j => if j = i then 0 else X j)

@[simp] theorem eraseVariable_X {σ R : Type*} [CommRing R] (i j : σ) :
    eraseVariable (R := R) i (X j) = if j = i then 0 else X j := by
  classical
  simp [eraseVariable]

@[simp] theorem eraseVariable_C {σ R : Type*} [CommRing R] (i : σ) (r : R) :
    eraseVariable i (C r) = C r := by simp [eraseVariable]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_BoundedLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section

open scoped BigOperators

noncomputable def pairAExponent {n k : ℕ} (i : PairBasisIndex n k) : Fin (n+1) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j => (pairIndexToTuple i j).1)

noncomputable def pairConeA {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) : Fin (n+1) → PairCone k A B θ :=
  Fin.cons (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 0))
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inl j)))

end

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_QuarticPairs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

noncomputable def pairConeB {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) : Fin (n+1) → PairCone k A B θ :=
  Fin.cons (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 1))
    (fun j => Ideal.Quotient.mk _ (MvPolynomial.X (Sum.inr j)))

noncomputable def pairABExponent {n k : ℕ} (i : PairBasisIndex n k) :
    (Fin (n+1) ⊕ Fin (n+1)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim
    (fun j => (pairIndexToTuple i j).1) (fun j => (pairIndexToTuple i j).2))

noncomputable def pairConePolynomial {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (hB : 0 < B) (θ : Fin n → K) (c : PairCone k A B θ) :
    MvPolynomial (Fin (n+1) ⊕ Fin (n+1)) K :=
  ((pairConeBasis k A B hB θ).repr c).sum fun i r =>
    MvPolynomial.monomial (pairABExponent i) r

open scoped BigOperators
open MvPolynomial

end

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairBoundaries
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

lemma pairCone_mapped_equation {n : ℕ} {K S : Type*} [Field K] [CommRing S] [Algebra K S]
    (k A B : ℕ) (θ : Fin n → K) (φ : PairCone k A B θ →ₐ[K] S)
    (ht : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.X 2)) = 1)
    (j : Fin n) :
    φ (pairConeA k A B θ j.succ)^k * φ (pairConeB k A B θ j.succ) =
      φ (pairConeA k A B θ 0)^k * φ (pairConeB k A B θ 0) + algebraMap K S (θ j) := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k (pairConeQ k A B θ))))
      (pairRelation k (pairConeQ k A B θ) j) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_range_self j))
  have he := congrArg φ h
  simp only [pairRelation,map_sub,map_mul,map_pow,map_zero,sub_eq_zero] at he
  change φ (pairConeA k A B θ j.succ)^k * φ (pairConeB k A B θ j.succ) =
    φ (pairCoeffMap k (pairConeQ k A B θ) (pairConeQ k A B θ j)) at he
  rw [he]
  have hcoef (r : K) : φ (pairCoeffMap k (pairConeQ k A B θ) (MvPolynomial.C r)) =
      algebraMap K S r := φ.commutes r
  simp only [pairConeQ,map_add,map_mul,map_pow,hcoef,ht,one_pow,mul_one]
  rfl

end

open MvPolynomial
open scoped Classical

def pairBoundaryExponent {n : ℕ} (k : ℕ) (i : Fin n)
    (m : (Fin n ⊕ Fin n) →₀ ℕ) : (Fin n → ℤ) × ℕ :=
  (fun j => if j = i then 0 else pairExponent k m j, m (Sum.inr i))

noncomputable def pairBoundaryMap {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]
    (k : ℕ) (q : Fin n → R) (φ : R →+* S) (i : Fin n) :
    MvPolynomial (Fin n ⊕ Fin n) R →+* AddMonoidAlgebra S ((Fin n → ℤ) × ℕ) :=
  eval₂Hom ((AddMonoidAlgebra.singleZeroRingHom).comp φ)
    (Sum.elim
      (fun j => AddMonoidAlgebra.single ((if j=i then 0 else Pi.single j 1), 0)
        (if j=i then 0 else 1))
      (fun j => AddMonoidAlgebra.single ((if j=i then 0 else Pi.single j (-(k:ℤ))),
        if j=i then 1 else 0) (if j=i then 1 else φ (q j))))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_LaurentCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

noncomputable def pairToLaurent {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) : PairRing k q →+* AddMonoidAlgebra R (Fin n → ℤ) :=
  Ideal.Quotient.lift _ (pairLaurentMap k q) (by
    change Ideal.span (Set.range (pairRelation k q)) ≤ RingHom.ker (pairLaurentMap k q)
    apply Ideal.span_le.mpr
    rintro p ⟨i,rfl⟩
    exact pairLaurentMap_relation k q i)

noncomputable def pairCoordinate {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) : PairRing k q :=
  Ideal.Quotient.mk _ (X (Sum.inl i))

@[simp] theorem pairToLaurent_coordinate {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    pairToLaurent k q (pairCoordinate k q i) =
      AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  simp [pairToLaurent,pairCoordinate,pairLaurentMap]

@[simp] theorem pairToLaurent_C {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (r : R) :
    pairToLaurent k q (Ideal.Quotient.mk _ (C r)) =
      AddMonoidAlgebra.single 0 r := by
  simp [pairToLaurent,pairLaurentMap]

end

open MvPolynomial

open MvPolynomial

noncomputable def pairEvaluation {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) : PairRing k q →ₐ[K] S :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aevalTower f (Sum.elim a b)) (by
    change Ideal.span _ ≤ RingHom.ker (MvPolynomial.aevalTower f (Sum.elim a b)).toRingHom
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change MvPolynomial.aevalTower f (Sum.elim a b) (pairRelation k q i) = 0
    simp only [pairRelation,map_sub,map_mul,map_pow,MvPolynomial.aevalTower_X,
      MvPolynomial.aevalTower_C,Sum.elim_inl,Sum.elim_inr,h,sub_self])

@[simp] theorem pairEvaluation_mk {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (p : MvPolynomial (Fin n ⊕ Fin n) R) :
    pairEvaluation k q f a b h (Ideal.Quotient.mk _ p) =
      MvPolynomial.aevalTower f (Sum.elim a b) p := rfl

@[simp] theorem pairEvaluation_coeff {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (r : R) :
    pairEvaluation k q f a b h (pairCoeffMap k q r) = f r := by
  change MvPolynomial.aevalTower f (Sum.elim a b) (MvPolynomial.C r) = f r
  exact MvPolynomial.aevalTower_C _ _ _

theorem pairEvaluation_ext {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f g : PairRing k q →ₐ[K] S)
    (hC : ∀ r, f (pairCoeffMap k q r) = g (pairCoeffMap k q r))
    (ha : ∀ i, f (Ideal.Quotient.mk _ (X (Sum.inl i))) =
      g (Ideal.Quotient.mk _ (X (Sum.inl i))))
    (hb : ∀ i, f (Ideal.Quotient.mk _ (X (Sum.inr i))) =
      g (Ideal.Quotient.mk _ (X (Sum.inr i)))) : f = g := by
  apply AlgHom.ext
  intro r
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective r
  induction p using MvPolynomial.induction_on with
  | C c => exact hC c
  | add p q hp hq => simp only [map_add,hp,hq]
  | mul_X p i hp =>
    simp only [map_mul,hp]
    cases i with
    | inl j => rw [ha]
    | inr j => rw [hb]

theorem pairCoordinate_equation {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    (Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q))) (X (Sum.inl i)))^k *
      Ideal.Quotient.mk _ (X (Sum.inr i)) = pairCoeffMap k q (q i) := by
  have h : Ideal.Quotient.mk (Ideal.span (Set.range (pairRelation k q)))
      (pairRelation k q i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  simpa only [pairRelation,map_sub,map_mul,map_pow,sub_eq_zero,pairCoeffMap,RingHom.comp_apply] using h

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PrincipalLifts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

noncomputable def pairLeft {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) : PairRing k q :=
  Ideal.Quotient.mk _ (X (Sum.inl i))

noncomputable def pairRight {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) : PairRing k q :=
  Ideal.Quotient.mk _ (X (Sum.inr i))

@[simp] theorem pairEvaluation_left {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (i : Fin n) :
    pairEvaluation k q f a b h (pairLeft k q i) = a i := by
  simp [pairLeft]

@[simp] theorem pairEvaluation_right {n : ℕ} {K R S : Type*} [Field K]
    [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (k : ℕ) (q : Fin n → R) (f : R →ₐ[K] S) (a b : Fin n → S)
    (h : ∀ i, a i ^ k * b i = f (q i)) (i : Fin n) :
    pairEvaluation k q f a b h (pairRight k q i) = b i := by
  simp [pairRight]

@[simp] theorem pairCoeffMap_scalar {n : ℕ} {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (k : ℕ) (q : Fin n → R) (r : K) :
    pairCoeffMap k q (algebraMap K R r) = algebraMap K (PairRing k q) r := rfl

noncomputable def rootPairQ {n : ℕ} {K : Type*} [Field K]
    (θ : Fin n → K) (i : Fin n) : Polynomial K :=
  Polynomial.X - Polynomial.C (θ i)

abbrev RootPair {n : ℕ} {K : Type*} [Field K] (k : ℕ) (θ : Fin n → K) :=
  PairRing k (rootPairQ θ)

noncomputable def coneDifference {n : ℕ} {K : Type*} [Field K]
    (θ : Fin (n+1) → K) (j : Fin n) : K := θ 0 - θ j.succ

abbrev PairAffine {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :=
  PairCone k A B θ ⧸ Ideal.span {pairCoeffMap k (pairConeQ k A B θ) (X 2) - 1}

noncomputable def pairAffineMk {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) : PairCone k A B θ →ₐ[K] PairAffine k A B θ :=
  Ideal.Quotient.mkₐ K _

@[simp] theorem pairAffineMk_t {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) :
    pairAffineMk k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2)) = 1 := by
  have h : pairAffineMk k A B θ (pairCoeffMap k (pairConeQ k A B θ) (X 2) - 1) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  simpa only [map_sub,map_one,sub_eq_zero] using h

noncomputable def pairAffineLeft {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) : PairAffine k A B θ :=
  pairAffineMk k A B θ (pairConeA k A B θ i)

noncomputable def pairAffineRight {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (i : Fin (n+1)) : PairAffine k A B θ :=
  pairAffineMk k A B θ (pairConeB k A B θ i)

lemma pairAffine_equation {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin n → K) (j : Fin n) :
    pairAffineLeft k A B θ j.succ ^ k * pairAffineRight k A B θ j.succ =
      pairAffineLeft k A B θ 0 ^ k * pairAffineRight k A B θ 0 +
        @algebraMap K (PairAffine k A B θ) inferInstance inferInstance inferInstance (θ j) := by
  exact pairCone_mapped_equation (S := PairAffine k A B θ)
    k A B θ (pairAffineMk k A B θ) (pairAffineMk_t k A B θ) j

lemma rootPair_equation {n : ℕ} {K : Type*} [Field K]
    (k : ℕ) (θ : Fin n → K) (i : Fin n) :
    pairLeft k (rootPairQ θ) i ^ k * pairRight k (rootPairQ θ) i =
      pairCoeffMap k (rootPairQ θ) Polynomial.X - algebraMap K (RootPair k θ) (θ i) := by
  have h := pairCoordinate_equation k (rootPairQ θ) i
  change pairLeft k (rootPairQ θ) i ^ k * pairRight k (rootPairQ θ) i = _ at h
  simpa only [rootPairQ,map_sub,Polynomial.C_eq_algebraMap,pairCoeffMap_scalar] using h

noncomputable def rootPairToAffine {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RootPair k θ →ₐ[K] PairAffine k A B (coneDifference θ) :=
  pairEvaluation (K := K) (S := PairAffine k A B (coneDifference θ)) k (rootPairQ θ)
    (Polynomial.aeval (pairAffineLeft k A B (coneDifference θ) 0 ^ k *
      pairAffineRight k A B (coneDifference θ) 0 + algebraMap K _ (θ 0)))
    (pairAffineLeft k A B (coneDifference θ))
    (pairAffineRight k A B (coneDifference θ)) (by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [rootPairQ,map_sub,Polynomial.aeval_X,Polynomial.aeval_C]
        ring
      · rw [pairAffine_equation]
        simp only [rootPairQ,map_sub,Polynomial.aeval_X,Polynomial.aeval_C,coneDifference,map_sub]
        ring)

noncomputable def pairConeToRoot {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    PairCone k A B (coneDifference θ) →ₐ[K] RootPair k θ :=
  pairEvaluation k (pairConeQ k A B (coneDifference θ))
    (MvPolynomial.aeval ![pairLeft k (rootPairQ θ) 0,pairRight k (rootPairQ θ) 0,1])
    (fun j => pairLeft k (rootPairQ θ) j.succ)
    (fun j => pairRight k (rootPairQ θ) j.succ) (by
      intro i
      simp only [pairConeQ,map_add,map_mul,map_pow,MvPolynomial.aeval_X,
        MvPolynomial.aeval_C,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,one_pow,mul_one]
      rw [rootPair_equation,rootPair_equation]
      simp [coneDifference,sub_eq_add_neg,add_assoc])

@[simp] theorem pairConeToRoot_t {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    pairConeToRoot k A B θ (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2)) = 1 := by
  simp [pairConeToRoot]

@[simp] theorem pairConeToRoot_left {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairConeToRoot k A B θ (pairConeA k A B (coneDifference θ) i) =
      pairLeft k (rootPairQ θ) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeA,pairConeToRoot]
  · change pairEvaluation _ _ _ _ _ _ (pairLeft _ _ j) = _
    simp

@[simp] theorem pairConeToRoot_right {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairConeToRoot k A B θ (pairConeB k A B (coneDifference θ) i) =
      pairRight k (rootPairQ θ) i := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairConeB,pairConeToRoot]
  · change pairEvaluation _ _ _ _ _ _ (pairRight _ _ j) = _
    simp

noncomputable def pairAffineToRoot {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    PairAffine k A B (coneDifference θ) →ₐ[K] RootPair k θ :=
  Ideal.Quotient.liftₐ _ (pairConeToRoot k A B θ) (by
    change Ideal.span _ ≤ RingHom.ker (pairConeToRoot k A B θ).toRingHom
    rw [Ideal.span_singleton_le_iff_mem]
    change pairConeToRoot k A B θ (_ - 1) = 0
    simp)

@[simp] theorem pairAffineToRoot_mk {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (p : PairCone k A B (coneDifference θ)) :
    pairAffineToRoot k A B θ (pairAffineMk k A B (coneDifference θ) p) =
      pairConeToRoot k A B θ p := rfl

noncomputable def pairCoeffHom {n : ℕ} {K R : Type*} [Field K]
    [CommRing R] [Algebra K R] (k : ℕ) (q : Fin n → R) : R →ₐ[K] PairRing k q where
  toRingHom := pairCoeffMap k q
  commutes' := pairCoeffMap_scalar k q

@[simp] theorem rootPairToAffine_left {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    rootPairToAffine k A B θ (pairLeft k (rootPairQ θ) i) =
      pairAffineLeft k A B (coneDifference θ) i := by
  simp [rootPairToAffine]

@[simp] theorem rootPairToAffine_right {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    rootPairToAffine k A B θ (pairRight k (rootPairQ θ) i) =
      pairAffineRight k A B (coneDifference θ) i := by
  simp [rootPairToAffine]

@[simp] theorem pairAffineToRoot_left {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairAffineToRoot k A B θ (pairAffineLeft k A B (coneDifference θ) i) =
      pairLeft k (rootPairQ θ) i := by
  simp [pairAffineLeft]

@[simp] theorem pairAffineToRoot_right {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) (i : Fin (n+1)) :
    pairAffineToRoot k A B θ (pairAffineRight k A B (coneDifference θ) i) =
      pairRight k (rootPairQ θ) i := by
  simp [pairAffineRight]

theorem pairAffineToRoot_leftInverse {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    Function.LeftInverse (pairAffineToRoot k A B θ) (rootPairToAffine k A B θ) := by
  have h : (pairAffineToRoot k A B θ).comp (rootPairToAffine k A B θ) =
      AlgHom.id K (RootPair k θ) := by
    apply pairEvaluation_ext (K := K) k (rootPairQ θ)
    · have hc : ((pairAffineToRoot k A B θ).comp (rootPairToAffine k A B θ)).comp
            (pairCoeffHom (K := K) k (rootPairQ θ)) =
          (AlgHom.id K (RootPair k θ)).comp (pairCoeffHom (K := K) k (rootPairQ θ)) := by
        apply Polynomial.algHom_ext
        change pairAffineToRoot k A B θ
          (rootPairToAffine k A B θ (pairCoeffMap k (rootPairQ θ) Polynomial.X)) =
          pairCoeffMap k (rootPairQ θ) Polynomial.X
        simp only [rootPairToAffine,pairEvaluation_coeff,Polynomial.aeval_X,map_add,
          map_mul,map_pow,pairAffineToRoot_left,pairAffineToRoot_right,AlgHom.commutes,
          rootPair_equation,sub_add_cancel]
      intro r
      exact AlgHom.congr_fun hc r
    · intro i
      change pairAffineToRoot k A B θ (rootPairToAffine k A B θ (pairLeft _ _ i)) = _
      simp only [rootPairToAffine_left,pairAffineToRoot_left]
      rfl
    · intro i
      change pairAffineToRoot k A B θ (rootPairToAffine k A B θ (pairRight _ _ i)) = _
      simp only [rootPairToAffine_right,pairAffineToRoot_right]
      rfl
  intro x
  exact AlgHom.congr_fun h x

theorem rootPairToAffine_comp_cone {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    (rootPairToAffine k A B θ).comp (pairConeToRoot k A B θ) =
      pairAffineMk k A B (coneDifference θ) := by
  apply pairEvaluation_ext (K := K) (S := PairAffine k A B (coneDifference θ)) k (pairConeQ k A B (coneDifference θ))
  · have hc : ((rootPairToAffine k A B θ).comp (pairConeToRoot k A B θ)).comp
          (pairCoeffHom (K := K) k (pairConeQ k A B (coneDifference θ))) =
        (pairAffineMk k A B (coneDifference θ)).comp
          (pairCoeffHom (K := K) k (pairConeQ k A B (coneDifference θ))) := by
      apply MvPolynomial.algHom_ext
      intro i
      fin_cases i
      · change rootPairToAffine k A B θ (pairConeToRoot k A B θ
            (pairConeA k A B (coneDifference θ) 0)) = _
        simp only [pairConeToRoot_left,rootPairToAffine_left,pairAffineLeft]
        rfl
      · change rootPairToAffine k A B θ (pairConeToRoot k A B θ
            (pairConeB k A B (coneDifference θ) 0)) = _
        simp only [pairConeToRoot_right,rootPairToAffine_right,pairAffineRight]
        rfl
      · change rootPairToAffine k A B θ (pairConeToRoot k A B θ
            (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2))) = _
        simp only [pairConeToRoot_t,map_one]
        exact (pairAffineMk_t k A B (coneDifference θ)).symm
    intro r
    exact AlgHom.congr_fun hc r
  · intro i
    change rootPairToAffine k A B θ (pairConeToRoot k A B θ
      (pairConeA k A B (coneDifference θ) i.succ)) = _
    simp only [pairConeToRoot_left,rootPairToAffine_left,pairAffineLeft]
    rfl
  · intro i
    change rootPairToAffine k A B θ (pairConeToRoot k A B θ
      (pairConeB k A B (coneDifference θ) i.succ)) = _
    simp only [pairConeToRoot_right,rootPairToAffine_right,pairAffineRight]
    rfl

theorem pairAffineToRoot_rightInverse {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    Function.RightInverse (pairAffineToRoot k A B θ) (rootPairToAffine k A B θ) := by
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun (rootPairToAffine_comp_cone k A B θ) p

noncomputable def rootPairAffineEquiv {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    RootPair k θ ≃ₐ[K] PairAffine k A B (coneDifference θ) :=
  { rootPairToAffine k A B θ with
    invFun := pairAffineToRoot k A B θ
    left_inv := pairAffineToRoot_leftInverse k A B θ
    right_inv := pairAffineToRoot_rightInverse k A B θ }

end

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PositiveCoordinates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped BigOperators

def positiveExponent {n : ℕ} : (Fin n →₀ ℕ) →+ (Fin n → ℤ) where
  toFun e i := e i
  map_zero' := by ext i; simp
  map_add' e f := by ext i; simp

noncomputable def positiveLaurentMap {n : ℕ} {R : Type*} [CommRing R] :
    MvPolynomial (Fin n) R →+* AddMonoidAlgebra R (Fin n → ℤ) :=
  AddMonoidAlgebra.mapDomainRingHom R positiveExponent

@[simp] theorem positiveLaurentMap_monomial {n : ℕ} {R : Type*} [CommRing R]
    (e : Fin n →₀ ℕ) (r : R) :
    positiveLaurentMap (monomial e r) = AddMonoidAlgebra.single (fun i => (e i : ℤ)) r := by
  exact AddMonoidAlgebra.mapDomain_single

@[simp] theorem positiveLaurentMap_C {n : ℕ} {R : Type*} [CommRing R] (r : R) :
    positiveLaurentMap (C r : MvPolynomial (Fin n) R) = AddMonoidAlgebra.single 0 r := by
  change positiveLaurentMap (monomial 0 r) = AddMonoidAlgebra.single (fun _ => (0 : ℤ)) r
  exact positiveLaurentMap_monomial 0 r

@[simp] theorem positiveLaurentMap_X {n : ℕ} {R : Type*} [CommRing R] (i : Fin n) :
    positiveLaurentMap (X i : MvPolynomial (Fin n) R) =
      AddMonoidAlgebra.single (Pi.single i 1) 1 := by
  classical
  rw [X,positiveLaurentMap_monomial]
  congr 1
  ext j
  simp [Finsupp.single_apply,Pi.single_apply,eq_comm]

end
open MvPolynomial

noncomputable def positiveToPair {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) : MvPolynomial (Fin n) R →+* PairRing k q :=
  MvPolynomial.eval₂Hom (pairCoeffMap k q) (pairCoordinate k q)

@[simp] theorem positiveToPair_C {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (r : R) :
    positiveToPair k q (C r) = pairCoeffMap k q r := by
  simp [positiveToPair]

@[simp] theorem positiveToPair_X {n : ℕ} {R : Type*} [CommRing R]
    (k : ℕ) (q : Fin n → R) (i : Fin n) :
    positiveToPair k q (X i) = pairCoordinate k q i := by
  simp [positiveToPair]

open MvPolynomial
open scoped BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PairProjections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section

section
open MvPolynomial

noncomputable def positiveToPairHom {n : ℕ} {K R : Type*} [Field K] [CommRing R]
    [Algebra K R] (k : ℕ) (q : Fin n → R) : MvPolynomial (Fin n) R →ₐ[K] PairRing k q :=
  MvPolynomial.aevalTower (pairCoeffHom (K := K) k q) (pairCoordinate k q)

noncomputable def pairConeN {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) : PairCone k A B (coneDifference θ) :=
  pairConeA k A B (coneDifference θ) 0 ^ k * pairConeB k A B (coneDifference θ) 0 +
    algebraMap K _ (θ 0) * (pairCoeffMap k (pairConeQ k A B (coneDifference θ)) (X 2))^(k*A+B)

@[simp] theorem pairConeToRoot_N {n : ℕ} {K : Type*} [Field K]
    (k A B : ℕ) (θ : Fin (n+1) → K) :
    pairConeToRoot k A B θ (pairConeN k A B θ) = pairCoeffMap k (rootPairQ θ) Polynomial.X := by
  simp only [pairConeN,map_add,map_mul,map_pow,pairConeToRoot_left,pairConeToRoot_right,
    pairConeToRoot_t,one_pow,mul_one,AlgHom.commutes,rootPair_equation,sub_add_cancel]

end
open scoped BigOperators

end

open MvPolynomial
open scoped BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ProjectionDegrees
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial

def pairProjectionIndex (m : ℕ) : Fin (m+2) ≃ Option (Fin (m+1)) :=
  (Equiv.swap 0 1).trans (finSuccEquiv (m+1))

@[simp] theorem pairProjectionIndex_zero (m : ℕ) : pairProjectionIndex m 0 = some 0 := by
  simp [pairProjectionIndex]

@[simp] theorem pairProjectionIndex_one (m : ℕ) : pairProjectionIndex m 1 = none := by
  simp [pairProjectionIndex]

@[simp] theorem pairProjectionIndex_succ_succ (m : ℕ) (i : Fin m) :
    pairProjectionIndex m i.succ.succ = some i.succ := by
  have hi0 : i.succ.succ ≠ (0 : Fin (m+2)) := Fin.succ_ne_zero _
  have hi1 : i.succ.succ ≠ (1 : Fin (m+2)) := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_succ,Fin.val_one] at this
    omega
  simp [pairProjectionIndex,Equiv.swap_apply_of_ne_of_ne hi0 hi1]

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RootPairHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

noncomputable def rootPairEvaluation {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) :
    RootPair k θ →ₐ[K] S :=
  pairEvaluation k (rootPairQ θ) (Polynomial.aeval x) a b (by
    intro i
    simpa only [rootPairQ,map_sub,Polynomial.aeval_X,Polynomial.aeval_C] using hab i)

@[simp] theorem rootPairEvaluation_left {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) (i : Fin d) :
    rootPairEvaluation k θ a b x hab (pairLeft k (rootPairQ θ) i) = a i := by
  simp [rootPairEvaluation]

@[simp] theorem rootPairEvaluation_right {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) (i : Fin d) :
    rootPairEvaluation k θ a b x hab (pairRight k (rootPairQ θ) i) = b i := by
  simp [rootPairEvaluation]

@[simp] theorem rootPairEvaluation_number {d : ℕ} {K S : Type*}
    [Field K] [CommRing S] [Algebra K S]
    (k : ℕ) (θ : Fin d → K) (a b : Fin d → S) (x : S)
    (hab : ∀ i, a i ^ k * b i = x - algebraMap K S (θ i)) :
    rootPairEvaluation k θ a b x hab (pairCoeffMap k (rootPairQ θ) Polynomial.X) = x := by
  simp [rootPairEvaluation]

end
open MvPolynomial

universe u

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace QuarticPowerFree

section
open scoped BigOperators Classical

def pairSplitFirst {h : ℕ} (p : Fin (h+1) → ℕ × ℕ) : Fin (h+2) → ℕ × ℕ :=
  Fin.cons ((p 0).1,0) (Fin.cons (0,(p 0).2) (fun i => p i.succ))

end

open MvPolynomial

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_WeightedFunctions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open scoped BigOperators Classical

noncomputable def conjugateLinePolynomial {d : ℕ} {K : Type*} [Field K]
    (v : Fin d → K) (σ : K →+* ℂ) (P : Fin d → Polynomial ℂ) : Polynomial ℂ :=
  ∑ j, Polynomial.C (σ (v j))*P j

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_CurveThresholds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial
open scoped Classical BigOperators

noncomputable def coordinateLinearForm {n d : ℕ} {K : Type*} [Field K]
    (x : Fin d → Fin n) (c : Fin d → K) : MvPolynomial (Fin n) K :=
  ∑ j, C (c j)*X (x j)

end

open scoped BigOperators

noncomputable def normBoxEnvelope (d h : ℕ) : ℝ :=
  if d = 5 then if h ≤ 2 then 196/1000 else if h = 3 then 154/1000 else 150/1000
  else if d = 6 then if h ≤ 2 then 176/1000 else if h = 3 then 134/1000 else 121/1000
  else if d = 7 then if h = 1 then 167/1000 else if h = 2 then 161/1000 else if h = 3 then 119/1000 else if h = 4 then 102/1000 else 100/1000
  else if h = 1 then 167/1000 else if h = 2 then 150/1000 else if h = 3 then 108/1000 else if h = 4 then 92/1000 else 85/1000

noncomputable def normBoxStage (d : ℕ) (i : Fin (d+1)) : ℝ := normBoxEnvelope d (d+1-i.val)
noncomputable def normBoxIncrement (d : ℕ) (i : Fin (d+1)) : ℝ :=
  if i.val = 0 then normBoxStage d i else normBoxStage d i - normBoxEnvelope d (d+2-i.val)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open MvPolynomial

open MvPolynomial
open scoped BigOperators Classical

structure NormBoxSystem (n d D : ℕ) (ω : Fin n → ℝ) (w : Fin n → ℕ) where
  Carrier : Type
  [field : Field Carrier]
  [charZero : CharZero Carrier]
  v : Fin d → Carrier
  independent : LinearIndependent ℚ v
  σ : Fin d → Carrier →+* ℂ
  θ : Fin d → ℂ
  distinct : Function.Injective θ
  x : Fin d → Fin n
  xweight : ∀ i, ω (x i) = 1/3
  b : Fin d → MvPolynomial (Fin n) ℂ
  q : MvPolynomial (Fin n) ℂ
  generates : Algebra.adjoin ℂ
    (Set.range (fun i => coordinateLinearForm x (σ i ∘ v)) ∪ Set.range b) = ⊤
  leftDegree : ∀ i, (coordinateLinearForm x (σ i ∘ v)).totalDegree ≤ D
  qDegree : q.totalDegree ≤ D
  leftWeight : ∀ i, coordinateLinearForm x (σ i ∘ v) ∈ weightedSpace w 5
  rightWeight : ∀ i, b i ∈ weightedSpace w 6

attribute [instance] NormBoxSystem.field NormBoxSystem.charZero

noncomputable def NormBoxSystem.a {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  coordinateLinearForm M.x (M.σ i ∘ M.v)

noncomputable def NormBoxSystem.equation {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) (i : Fin d) : MvPolynomial (Fin n) ℂ :=
  M.a i^(d-2)*M.b i-M.q+C (M.θ i)

noncomputable def NormBoxSystem.ideal {n d D : ℕ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : NormBoxSystem n d D ω w) : Ideal (MvPolynomial (Fin n) ℂ) :=
  Ideal.span (Set.range M.equation)

end
open MvPolynomial
open scoped BigOperators Classical

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_NormBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Polynomial NumberField

theorem scaleRoots_irreducible {K : Type*} [Field K] (f : Polynomial K)
    (hf : Irreducible f) (r : K) (hr : r ≠ 0) :
    Irreducible (f.scaleRoots r) := by
  have hu (g : Polynomial K) : IsUnit (g.scaleRoots r) ↔ IsUnit g := by
    rw [Polynomial.isUnit_iff_degree_eq_zero,Polynomial.isUnit_iff_degree_eq_zero,
      Polynomial.degree_scaleRoots]
  refine ⟨fun h => hf.not_isUnit (hu f |>.mp h),?_⟩
  intro a b he
  have hback : f = a.scaleRoots r⁻¹ * b.scaleRoots r⁻¹ := by
    rw [← mul_scaleRoots_of_noZeroDivisors,← he,← scaleRoots_mul, mul_inv_cancel₀ hr,
      scaleRoots_one]
  rcases hf.isUnit_or_isUnit hback with ha | hb
  · left
    simpa only [Polynomial.isUnit_iff_degree_eq_zero,degree_scaleRoots] using ha
  · right
    simpa only [Polynomial.isUnit_iff_degree_eq_zero,degree_scaleRoots] using hb

theorem integralNormalization_irreducible (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) :
    Irreducible (f.integralNormalization.map (Int.castRingHom ℚ)) := by
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by simp [h])
  have hc : (f.leadingCoeff : ℚ) ≠ 0 := by exact_mod_cast leadingCoeff_ne_zero.mpr hf0
  have hs := scaleRoots_irreducible (f.map (Int.castRingHom ℚ)) hf (f.leadingCoeff : ℚ) hc
  have he := congrArg (Polynomial.map (Int.castRingHom ℚ))
    (integralNormalization_mul_C_leadingCoeff f)
  rw [Polynomial.map_mul,Polynomial.map_C,map_scaleRoots f f.leadingCoeff _ hc] at he
  change f.integralNormalization.map (Int.castRingHom ℚ) * C (f.leadingCoeff : ℚ) =
    (f.map (Int.castRingHom ℚ)).scaleRoots (f.leadingCoeff : ℚ) at he
  rw [← he] at hs
  exact (irreducible_mul_isUnit (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hc))).mp hs

open Polynomial NumberField
open scoped nonZeroDivisors

end

open Polynomial NumberField

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_UnitBalancing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace QuarticPowerFree

open Polynomial NumberField

structure ArithmeticModel (f : Polynomial ℤ) where
  Carrier : Type
  [field : Field Carrier]
  [numberField : NumberField Carrier]
  root : Carrier
  root_eq : f.aeval root = 0
  integralRoot : 𝓞 Carrier
  integralRoot_eq : (integralRoot : Carrier) = (f.leadingCoeff : Carrier) * root
  powerBasis : PowerBasis ℚ Carrier
  powerBasis_gen : powerBasis.gen = (integralRoot : Carrier)
  degree_eq : Module.finrank ℚ Carrier = f.natDegree

attribute [instance] ArithmeticModel.field ArithmeticModel.numberField

noncomputable def arithmeticModel (f : Polynomial ℤ)
    (hf : Irreducible (f.map (Int.castRingHom ℚ))) (hd : 1 ≤ f.natDegree) :
    ArithmeticModel f := by
  let F := f.integralNormalization
  let G := F.map (Int.castRingHom ℚ)
  have hG : Irreducible G := integralNormalization_irreducible f hf
  letI : Fact (Irreducible G) := ⟨hG⟩
  let K := AdjoinRoot G
  let pb : PowerBasis ℚ K := AdjoinRoot.powerBasis hG.ne_zero
  letI : Module.Finite ℚ K := pb.finite
  letI : NumberField K := NumberField.of_module_finite ℚ K
  let r : K := AdjoinRoot.root G
  have hr : G.aeval r = 0 := AdjoinRoot.eval₂_root G
  have hrF : F.aeval r = 0 := by
    change (F.map (algebraMap ℤ ℚ)).aeval r = 0 at hr
    rw [aeval_map_algebraMap] at hr
    exact hr
  have hf0 : f ≠ 0 := fun h => hf.ne_zero (by simp [h])
  have hFmon : F.Monic := monic_integralNormalization hf0
  let t : 𝓞 K := ⟨r,⟨F,hFmon,hrF⟩⟩
  let θ : K := r / (f.leadingCoeff : K)
  have hc : (f.leadingCoeff : K) ≠ 0 := by
    exact_mod_cast leadingCoeff_ne_zero.mpr hf0
  have ht : (f.leadingCoeff : K) * θ = r := by
    dsimp only [θ]
    rw [← mul_div_assoc, mul_comm (f.leadingCoeff : K) r, mul_div_cancel_right₀ r hc]
  have hθ : f.aeval θ = 0 := by
    have he := integralNormalization_eval₂_leadingCoeff_mul hd (algebraMap ℤ K) θ
    change F.aeval ((f.leadingCoeff : K) * θ) =
      (f.leadingCoeff : K) ^ (f.natDegree - 1) * f.aeval θ at he
    rw [ht,hrF] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (pow_ne_zero _ hc)
  refine ⟨K,θ,hθ,t,ht.symm,pb,?_,?_⟩
  · rfl
  · rw [pb.finrank]
    change G.natDegree = f.natDegree
    rw [natDegree_map_eq_of_injective Int.cast_injective]
    exact natDegree_integralNormalization

end QuarticPowerFree
end

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_EmbeddingCharts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

structure IntegralEmbeddingChart (K : Type*) [Field K] [NumberField K] (d : ℕ) where
  σ : Fin d ≃ (K →+* ℂ)
  B : Basis (Fin d) ℤ (𝓞 K)
  V : Basis (Fin d) ℚ K
  compatible : ∀ j, V j = (B j:K)
  det_ne_zero : (Matrix.of (fun i j => σ i (V j))).det ≠ 0

noncomputable def integralEmbeddingChart (K : Type*) [Field K] [NumberField K]
    (d : ℕ) (hd : Module.finrank ℚ K = d) : IntegralEmbeddingChart K d := by
  classical
  let e : Fin d ≃ (K →+* ℂ) := (Fintype.equivFinOfCardEq ((NumberField.Embeddings.card K ℂ).trans hd)).symm
  let r := (equivReindex K).symm.trans e.symm
  let B := (RingOfIntegers.basis K).reindex r
  let V := (integralBasis K).reindex r
  refine ⟨e,B,V,?_,?_⟩
  · intro j
    simp [V,B,Basis.reindex_apply,integralBasis_apply]
  · have hm : Matrix.of (fun i j => e i (V j)) =
        ((basisMatrix K).transpose).reindex e.symm e.symm := by
      ext i j
      simp [V,r,Matrix.reindex_apply,Matrix.submatrix_apply,basisMatrix,
        canonicalEmbedding.latticeBasis_apply]
    rw [hm,Matrix.det_reindex_self,Matrix.det_transpose]
    exact det_of_basisMatrix_non_zero K

noncomputable def IntegralEmbeddingChart.A {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) : Matrix (Fin d) (Fin d) ℂ :=
  fun i j => T.σ i (T.V j)

noncomputable def IntegralEmbeddingChart.coord {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α : 𝓞 K) : Fin d → ℤ := T.B.repr α

end

section
open MvPolynomial
open scoped Classical BigOperators

theorem coordinateLinearForm_inverse {n d : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (hA : A.det ≠ 0) (x : Fin d → Fin n) (j : Fin d) :
    ∑ i, C (A⁻¹ j i)*coordinateLinearForm x (A i) = X (x j) := by
  simp only [coordinateLinearForm,Finset.mul_sum,←mul_assoc,←map_mul]
  rw [Finset.sum_comm]
  simp only [←Finset.sum_mul,←map_sum]
  have he (l : Fin d) : ∑ i, A⁻¹ j i*A i l = if j=l then 1 else 0 := by
    have hh := congrArg (fun M : Matrix (Fin d) (Fin d) K => M j l)
      (Matrix.nonsing_inv_mul A (Ne.isUnit hA))
    simpa only [Matrix.mul_apply,Matrix.one_apply] using hh
  simp only [he]
  simp

theorem coordinateLinearForm_mem_adjoin {n d : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (hA : A.det ≠ 0) (x : Fin d → Fin n)
    (S : Subalgebra K (MvPolynomial (Fin n) K))
    (h : ∀ i, coordinateLinearForm x (A i) ∈ S) (j : Fin d) : X (x j) ∈ S := by
  rw [←coordinateLinearForm_inverse A hA x j]
  exact S.sum_mem (fun i _ => S.mul_mem (S.algebraMap_mem _) (h i))

theorem coordinateLinearForm_totalDegree {n d : ℕ} {K : Type*} [Field K]
    (x : Fin d → Fin n) (c : Fin d → K) : (coordinateLinearForm x c).totalDegree ≤ 1 := by
  apply totalDegree_finsetSum_le
  intro i _
  exact (totalDegree_mul _ _).trans (by simp)

theorem coordinateLinearForm_weightedSpace {n d : ℕ} {K : Type*} [Field K]
    (w : Fin n → ℕ) (x : Fin d → Fin n) (c : Fin d → K) (W : ℕ)
    (hx : ∀ i, w (x i) ≤ W) : coordinateLinearForm x c ∈ weightedSpace w W := by
  apply Submodule.sum_mem
  intro i _
  rw [←smul_eq_C_mul]
  apply Submodule.smul_mem
  rw [mem_weightedSpace]
  simpa [weightedTotalDegree,MvPolynomial.X,Finsupp.weight_single] using hx i

noncomputable def normBoxWeight (d : ℕ) : Fin (d+d) → ℝ := Fin.addCases (fun _ => 1/3) (fun _ => 2/5)
noncomputable def normBoxNatWeight (d : ℕ) : Fin (d+d) → ℕ := Fin.addCases (fun _ => 5) (fun _ => 6)

theorem pairedLinearForms_generate {d : ℕ} {K : Type*} [Field K]
    (A : Matrix (Fin d) (Fin d) K) (hA : A.det ≠ 0) (s : K) (hs : s ≠ 0) :
    Algebra.adjoin K (Set.range (fun i => coordinateLinearForm (Fin.castAdd d) (A i)) ∪
      Set.range (fun i => C s*coordinateLinearForm (Fin.natAdd d) (A i))) = ⊤ := by
  let S := Algebra.adjoin K (Set.range (fun i => coordinateLinearForm (Fin.castAdd d) (A i)) ∪
      Set.range (fun i => C s*coordinateLinearForm (Fin.natAdd d) (A i)))
  have hleft (i) : coordinateLinearForm (Fin.castAdd d) (A i) ∈ S :=
    Algebra.subset_adjoin (Or.inl ⟨i,rfl⟩)
  have hright (i) : coordinateLinearForm (Fin.natAdd d) (A i) ∈ S := by
    have hh : C s*coordinateLinearForm (Fin.natAdd d) (A i) ∈ S := Algebra.subset_adjoin (Or.inr ⟨i,rfl⟩)
    have he : C s⁻¹*(C s*coordinateLinearForm (Fin.natAdd d) (A i)) = coordinateLinearForm (Fin.natAdd d) (A i) := by
      rw [←mul_assoc,←map_mul,inv_mul_cancel₀ hs,map_one,one_mul]
    rw [←he]
    exact S.mul_mem (S.algebraMap_mem _) hh
  have hx (j : Fin (d+d)) : X j ∈ S := by
    induction j using Fin.addCases with
    | left j => exact coordinateLinearForm_mem_adjoin A hA _ S hleft j
    | right j => exact coordinateLinearForm_mem_adjoin A hA _ S hright j
  apply top_unique
  rw [←adjoin_range_X (R := K) (σ := Fin (d+d))]
  exact Algebra.adjoin_le (by rintro _ ⟨j,rfl⟩; exact hx j)

end

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

noncomputable def normBoxOfChart {K : Type} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) (hd : 0 < d) :
    NormBoxSystem (d+d) d (d+1) (normBoxWeight d) (normBoxNatWeight d) := by
  let a : Fin d → MvPolynomial (Fin (d+d)) ℂ := fun i => coordinateLinearForm (Fin.castAdd d) (T.A i)
  let b : Fin d → MvPolynomial (Fin (d+d)) ℂ := fun i => C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd d) (T.A i)
  let i₀ : Fin d := ⟨0,hd⟩
  have hb (i) : (b i).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using coordinateLinearForm_totalDegree (Fin.natAdd d) (T.A i))
  refine ⟨K,T.V,T.V.linearIndependent,T.σ,fun i => T.σ i θ,hθ,Fin.castAdd d,
    ?_,b,a i₀^(d-2)*b i₀+C (T.σ i₀ θ),?_,?_,?_,?_,?_⟩
  · intro i; simp only [normBoxWeight,Fin.addCases_left]
  · exact pairedLinearForms_generate T.A T.det_ne_zero (μ:ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast hμ.ne'))
  · intro i; exact (coordinateLinearForm_totalDegree _ _).trans (by omega)
  · apply (totalDegree_add _ _).trans
    rw [max_le_iff]
    refine ⟨(totalDegree_mul _ _).trans ?_,by simp⟩
    have ha : (a i₀).totalDegree ≤ 1 := coordinateLinearForm_totalDegree _ _
    have hp := (totalDegree_pow (a i₀) (d-2)).trans (Nat.mul_le_mul_left (d-2) ha)
    have hh := hb i₀
    omega
  · intro i
    exact coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [normBoxNatWeight,Fin.addCases_left,le_refl])
  · intro i
    change C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd d) (T.A i) ∈ _
    rw [←smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [normBoxNatWeight,Fin.addCases_right,le_refl]))

noncomputable def normIntegralPoint {K : Type*} [Field K] [NumberField K] {d : ℕ}
    (T : IntegralEmbeddingChart K d) (α β : 𝓞 K) : Fin (d+d) → ℤ :=
  Fin.addCases (T.coord α) (T.coord β)

end

open NumberField
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_MediumDegree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open MvPolynomial
open scoped Classical BigOperators

structure QuarticBoxSystem (n D A B : ℕ) (U : ℝ) (ω : Fin n → ℝ) (w : Fin n → ℕ) where
  Carrier : Type
  [field : Field Carrier]
  [charZero : CharZero Carrier]
  v : Fin 4 → Carrier
  independent : LinearIndependent ℚ v
  σ : Fin 4 → Carrier →+* ℂ
  θ : Fin 4 → ℂ
  distinct : Function.Injective θ
  x : Fin 4 → Fin n
  xweight : ∀ i, ω (x i) = U
  b : Fin 4 → MvPolynomial (Fin n) ℂ
  q : MvPolynomial (Fin n) ℂ
  generates : Algebra.adjoin ℂ
    (Set.range (fun i => coordinateLinearForm x (σ i ∘ v)) ∪ Set.range b) = ⊤
  leftDegree : ∀ i, (coordinateLinearForm x (σ i ∘ v)).totalDegree ≤ D
  qDegree : q.totalDegree ≤ D
  leftWeight : ∀ i, coordinateLinearForm x (σ i ∘ v) ∈ weightedSpace w A
  rightWeight : ∀ i, b i ∈ weightedSpace w B
attribute [instance] QuarticBoxSystem.field QuarticBoxSystem.charZero

noncomputable def QuarticBoxSystem.a {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (i : Fin 4) : MvPolynomial (Fin n) ℂ :=
  coordinateLinearForm M.x (M.σ i ∘ M.v)
noncomputable def QuarticBoxSystem.equation {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) (i : Fin 4) : MvPolynomial (Fin n) ℂ := M.a i^2*M.b i-M.q+C (M.θ i)
noncomputable def QuarticBoxSystem.ideal {n D A B : ℕ} {U : ℝ} {ω : Fin n → ℝ} {w : Fin n → ℕ}
    (M : QuarticBoxSystem n D A B U ω w) : Ideal (MvPolynomial (Fin n) ℂ) := Ideal.span (Set.range M.equation)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_AffineHilbert
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section

section
open scoped BigOperators Classical
open MvPolynomial

noncomputable def affineExponent {σ : Type*} : Option σ → σ →₀ ℕ :=
  fun o => o.elim 0 (fun i => Finsupp.single i 1)

end
universe u v
open scoped BigOperators

end

open MvPolynomial
open scoped BigOperators Classical

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_PoleCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u

namespace QuarticPowerFree

open Polynomial
open scoped BigOperators Classical

noncomputable def rootCoeffLinear {K : Type*} [Field K] (r : K) (n : ℕ) :
    Polynomial K →ₗ[K] K :=
  (Polynomial.lcoeff K n).comp ((Polynomial.aeval (Polynomial.X+Polynomial.C r)).toLinearMap)

noncomputable def threePoleNumerator {K : Type*} [Field K] (r₀ : K) (r : Fin 2 → K)
    (m : ℕ) (i : Fin 2 × Fin m × Fin 2) : Polynomial K :=
  (X-C (r i.1))^(2*(m-(i.2.1.val+1))+i.2.2.val) *
    ((X-C r₀)^(2*(i.2.1.val+1)) * (X-C (r (1-i.1)))^(2*m))

noncomputable def threePoleBase {K : Type*} [Field K] (r : Fin 2 → K) (m : ℕ) : Polynomial K :=
  (X-C (r 0))^(2*m)*(X-C (r 1))^(2*m)

noncomputable def twoPoleNumerator {K : Type*} [Field K] (r₀ r₁ : K)
    (m l : ℕ) (i : (Fin m × Fin 2) ⊕ (Fin l × Fin 2)) : Polynomial K :=
  i.elim (fun j => (X-C r₁)^(2*(m-(j.1.val+1))+j.2.val)*
      ((X-C r₀)^(2*l+2*(j.1.val+1))))
    (fun j => (X-C r₀)^(2*(l-(j.1.val+1))+j.2.val)*(X-C r₁)^(2*m))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_ThreePoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open Polynomial
open scoped BigOperators Classical

noncomputable def threePoleClearing {K : Type*} [Field K] (r₀ : K) (r : Fin 2 → K)
    (M m : ℕ) : Polynomial K :=
  (X-C r₀)^(2*(M-m))*(X-C (r 0))^(2*(M-m))*(X-C (r 1))^(2*(M-m))

noncomputable def threePolePolynomial {K : Type*} [Field K]
    (r₀ θ₀ : K) (r θ : Fin 2 → K) (M m N : ℕ)
    (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) : Polynomial (Polynomial K) :=
  i.elim
    (fun a => C (threePoleClearing r₀ r M m * (X^a.val*threePoleBase r m)) * (X-C (C θ₀))^m)
    (fun j => C (threePoleClearing r₀ r M m * threePoleNumerator r₀ r m j) *
      ((X-C (C θ₀))^(m-(j.2.1.val+1))*(X-C (C (θ j.1)))^(j.2.1.val+1)))

noncomputable def bivarEvaluation {K L : Type*} [Field K] [CommRing L] [Algebra K L]
    (t q : L) : Polynomial (Polynomial K) →ₐ[K] L :=
  Polynomial.aevalTower (Polynomial.aeval t) q

end

open Polynomial
open scoped BigOperators Classical

noncomputable def threePoleFunction {L : Type*} [CommRing L]
    (t b₀ : L) (a b : Fin 2 → L) (m N : ℕ)
    (i : (Fin N) ⊕ (Fin 2 × Fin m × Fin 2)) : L :=
  i.elim (fun j => t^j.val*b₀^m)
    (fun j => b₀^(m-(j.2.1.val+1))*b j.1^(j.2.1.val+1)*a j.1^j.2.2.val)

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_TwoPoles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

open Polynomial
open scoped BigOperators Classical

noncomputable def twoPolePolynomial {K : Type*} [Field K]
    (r₀ r₁ θ₀ θ₁ : K) (M m N : ℕ)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) : Polynomial (Polynomial K) :=
  let H := (X-C r₁)^(2*(M-m))
  i.elim
    (fun a => C (H*(X^a.val*((X-C r₀)^(2*(M-m))*(X-C r₁)^(2*m))))*(X-C (C θ₀))^m)
    (fun j => C (H*twoPoleNumerator r₀ r₁ m (M-m) j)*
      j.elim (fun e => (X-C (C θ₀))^(m-(e.1.val+1))*(X-C (C θ₁))^(e.1.val+1))
        (fun _ => (X-C (C θ₀))^m))

noncomputable def twoPoleFunction {L : Type*} [CommRing L]
    (t a₀ a₁ b₀ b₁ u₀ : L) (M m N : ℕ)
    (i : Fin N ⊕ ((Fin m × Fin 2) ⊕ (Fin (M-m) × Fin 2))) : L :=
  i.elim (fun j => t^j.val*b₀^m)
    (Sum.elim (fun j => b₀^(m-(j.1.val+1))*b₁^(j.1.val+1)*a₁^j.2.val)
      (fun j => b₀^m*u₀^(j.1.val+1)*a₀^j.2.val))

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_QuarticComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped BigOperators

def quarticA (j : Fin 100) : ℕ := 101+j.val
def quarticB (j : Fin 100) : ℕ := 200-2*j.val
def quarticNumerator (j : Fin 100) (h : ℕ) : ℕ :=
  if j.val < 60 then if h ≤ 2 then 206 else if h=3 then 200 else 191
  else if h=1 then 252 else if h=2 then 206 else 175
noncomputable def quarticEnvelope (j : Fin 100) (h : ℕ) : ℝ := quarticNumerator j h/1000
noncomputable def quarticU (j : Fin 100) : ℝ := quarticA j/400
noncomputable def quarticV (j : Fin 100) : ℝ := quarticB j/400
noncomputable def quarticStage (j : Fin 100) (i : Fin 5) : ℝ := quarticEnvelope j (5-i.val)
noncomputable def quarticIncrement (j : Fin 100) (i : Fin 5) : ℝ :=
  if i.val=0 then quarticStage j i else quarticStage j i-quarticEnvelope j (6-i.val)

end

open MvPolynomial

open MvPolynomial
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_QuarticBoxes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open NumberField Module MvPolynomial
open scoped Classical BigOperators

noncomputable def quarticBoxWeight (j : Fin 100) : Fin (4+4) → ℝ :=
  Fin.addCases (m := 4) (n := 4) (fun _ : Fin 4 => quarticU j) (fun _ : Fin 4 => quarticV j)
def quarticBoxNatWeight (j : Fin 100) : Fin (4+4) → ℕ :=
  Fin.addCases (m := 4) (n := 4) (fun _ : Fin 4 => quarticA j) (fun _ : Fin 4 => quarticB j)

noncomputable def quarticBoxOfChart {K : Type} [Field K] [NumberField K] (j : Fin 100)
    (T : IntegralEmbeddingChart K 4) (θ : K) (hθ : Function.Injective (fun i => T.σ i θ))
    (μ : ℕ) (hμ : 0 < μ) :
    QuarticBoxSystem 8 5 (quarticA j) (quarticB j) (quarticU j) (quarticBoxWeight j) (quarticBoxNatWeight j) := by
  let a : Fin 4 → MvPolynomial (Fin (4+4)) ℂ := fun i => coordinateLinearForm (Fin.castAdd 4) (T.A i)
  let b : Fin 4 → MvPolynomial (Fin (4+4)) ℂ := fun i => C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd 4) (T.A i)
  let i₀ : Fin 4 := 0
  have hb (i) : (b i).totalDegree ≤ 1 := by
    exact (totalDegree_mul _ _).trans (by simpa only [totalDegree_C,zero_add] using coordinateLinearForm_totalDegree (Fin.natAdd 4) (T.A i))
  refine ⟨K,T.V,T.V.linearIndependent,T.σ,fun i => T.σ i θ,hθ,Fin.castAdd 4,
    ?_,b,a i₀^2*b i₀+C (T.σ i₀ θ),?_,?_,?_,?_,?_⟩
  · intro i; simp only [quarticBoxWeight,Fin.addCases_left]
  · exact pairedLinearForms_generate T.A T.det_ne_zero (μ:ℂ)⁻¹ (inv_ne_zero (by exact_mod_cast hμ.ne'))
  · intro i; exact (coordinateLinearForm_totalDegree _ _).trans (by omega)
  · apply (totalDegree_add _ _).trans
    rw [max_le_iff]
    refine ⟨(totalDegree_mul _ _).trans ?_,by simp⟩
    have ha : (a i₀).totalDegree ≤ 1 := coordinateLinearForm_totalDegree _ _
    have hp := (totalDegree_pow (a i₀) 2).trans (Nat.mul_le_mul_left 2 ha)
    have hh := hb i₀
    omega
  · intro i
    exact coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [quarticBoxNatWeight,Fin.addCases_left,le_refl])
  · intro i
    change C (μ:ℂ)⁻¹*coordinateLinearForm (Fin.natAdd 4) (T.A i) ∈ _
    rw [←smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (coordinateLinearForm_weightedSpace _ _ _ _ (fun j => by simp only [quarticBoxNatWeight,Fin.addCases_right,le_refl]))

end

open NumberField Module
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end

section
-- module Solutions.OAIB3_Qpf.PowerFree_RadialFibres
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace QuarticPowerFree

section
open scoped Classical

noncomputable def quarticLowerEta (j : Fin 100) : ℝ := 1+(j.val:ℝ)/100
noncomputable def quarticUpperEta (j : Fin 100) : ℝ := 1+((j.val:ℝ)+1)/100

end

open NumberField Module
open scoped Classical BigOperators

end QuarticPowerFree

end OAI
end


