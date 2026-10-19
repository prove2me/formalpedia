-- Prove2me | Definitions.Def_OAIE3v2B140
-- name    : OAIE3v2B140
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:49:39.107583+00:00
-- url     : https://prove2.me/theorems/5a1bac45-fc43-401b-b3ea-83bb7bf589ee
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 142 of 311
-- statement:
--   Definitions bundle 142 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B128`, `OAIE3v2B129` of this split.
--
--   Modules: `Estimates/BufferedTranslationIncrement.lean`, `Estimates/ControlledComparisonModel.lean`, `Estimates/MajorTranslationPureFactorValues.lean`, `Estimates/SquarefreeQuotientAction.lean`, `Estimates/SquarefreeRealAction.lean`, `Estimates/WeightedTranslationCentralTop.lean`, `Estimates/WeightedTranslationRealPureFactors.lean`, `Estimates/WeightedTranslationStructureConstants.lean`, `Estimates/WeightedTwistedTranslationLipschitz.lean`, `Fourier/BohrNiltestBudget.lean`, `Fourier/WeightedTranslationBufferedCentralFrequency.lean`, `Geometry/WeightedTranslationBufferedCoordinates.lean`, `Lattices/NativeSquarefreeLattice.lean`, `Lattices/WeightedTranslationCentralLattice.lean`, `Lattices/WeightedTranslationLattice.lean`, `Lattices/WeightedTranslationResidueLattice.lean`, `Linear/ComparisonChosenLayerBasis.lean`, `Linear/WeightedTranslationOrderedBasis.lean`, `Nilpotent/LocalMajorDenseSliceNiltest.lean`, `Nilpotent/WeightedTranslationResidueNilmanifold.lean`, `Nilpotent/WeightedTranslationTwistedNiltest.lean`, `Polynomial/PolynomialTranslationIntegralAction.lean`, `Polynomial/TwistedBufferedTranslationPhase.lean`, `Polynomial/WeightedTranslationResiduePhase.lean`, `Sampling/NativeSquarefreeGrids.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B128
import Definitions.Def_OAIE3v2B129

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationIntegralAction
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem bchTranslation_integral_comap (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    PolynomialTranslationGroup.integralGroup.comap (bchTranslationHom w d hw hwd) =
      (integerWeightedLoweringSubgroup (shearWeight w d)).comap (weightedShearGroupHom w d hwd) := by
  ext g
  exact bchTranslationHom_mem_integralGroup_iff w d hw hwd g

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationLattice
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem weightedTranslationLattice_eq_integral_preimage (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) :
    weightedTranslationLattice w d hwd =
      PolynomialTranslationGroup.integralGroup.comap (bchTranslationHom w d hw hwd) :=
  (bchTranslation_integral_comap w d hw hwd).symm

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationStructureConstants
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def weightedBasisBracketCoefficient (w : σ → ℕ) (d : ℕ) :
    WeightedBasisIndex w d → WeightedBasisIndex w d → WeightedBasisIndex w d → ℤ := by
  classical
  exact fun a b c => match a, b, c with
    | Sum.inl i, Sum.inr a, Sum.inr c =>
        if a.val - Finsupp.single i 1 = c.val then (a.val i : ℤ) else 0
    | Sum.inr a, Sum.inl i, Sum.inr c =>
        -(if a.val - Finsupp.single i 1 = c.val then (a.val i : ℤ) else 0)
    | _, _, _ => 0

variable [Fintype σ]

theorem weightedBasis_structureConstants (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (a b c : WeightedBasisIndex w d) :
    lieStructureConstants (weightedBasis w d hw) a b c =
      (weightedBasisBracketCoefficient w d a b c : ℚ) := by
  classical
  unfold lieStructureConstants
  cases c with
  | inl c =>
      rw [weightedBasis_repr_inl]
      cases a <;> cases b <;> rfl
  | inr c =>
      rw [weightedBasis_repr_inr]
      change (scalarDirectionalDerivative (weightedBasis w d hw a).val.base
        (weightedBasis w d hw b).val.polynomial -
        scalarDirectionalDerivative (weightedBasis w d hw b).val.base
          (weightedBasis w d hw a).val.polynomial).coeff c.val = _
      cases a with
      | inl i =>
          cases b with
          | inl j => simp [weightedBasisBracketCoefficient]
          | inr a =>
              simp [weightedBasisBracketCoefficient, scalarDirectionalDerivative_apply,
                Pi.single_apply, pderiv_monomial, coeff_monomial]
      | inr a =>
          cases b with
          | inl i =>
              simp [weightedBasisBracketCoefficient, scalarDirectionalDerivative_apply,
                Pi.single_apply, pderiv_monomial, coeff_monomial]
          | inr b => simp [weightedBasisBracketCoefficient]

omit [Fintype σ] in
theorem weightedBasisBracketCoefficient_natAbs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    (weightedBasisBracketCoefficient w d a b c).natAbs ≤ d := by
  classical
  have hb : ∀ (i : σ) (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}), a.val i ≤ d := by
    intro i a
    exact (Finsupp.le_weight w (hw i).ne' a.val).trans (Nat.le_of_lt a.property)
  cases a <;> cases b <;> cases c <;>
    simp only [weightedBasisBracketCoefficient, Int.natAbs_neg] <;>
    (try split_ifs) <;>
    simp only [Int.natAbs_zero, Int.natAbs_natCast, Nat.zero_le] <;> exact hb _ _

theorem weightedBasis_structure_height_succ (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    RationalHeightLE (lieStructureConstants (weightedBasis w d hw) a b c) (d + 1) := by
  rw [weightedBasis_structureConstants]
  constructor
  · simpa using (weightedBasisBracketCoefficient_natAbs_le w d hw a b c).trans (Nat.le_succ d)
  · simp

theorem weightedBasis_structure_height (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a b c : WeightedBasisIndex w d) :
    RationalHeightLE (lieStructureConstants (weightedBasis w d hw) a b c) (2 * d + 1) :=
  (weightedBasis_structure_height_succ w d hw a b c).mono (by omega)

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.WeightedTranslationOrderedBasis
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ)
  (hw : ∀ i, 0 < w i) [Fintype (WeightedBasisIndex w d)]

theorem weightedOrderedBasis_structure_height (a b c) :
    RationalHeightLE (lieStructureConstants (weightedOrderedBasis w d hw) a b c) (2 * d + 1) := by
  rw [weightedOrderedBasis, lieStructureConstants_reindex]
  exact weightedBasis_structure_height w d hw _ _ _

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationResidueLattice
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

noncomputable def weightedTranslationResidueLattice (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    Subgroup (weightedFiltration w d hwd).Group :=
  ((integerTranslationResidueSubgroup (B := σ) M).map PolynomialTranslationGroup.fromInteger).comap
    (bchTranslationHom w d hw hwd)

theorem weightedTranslationResidueLattice_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    weightedTranslationResidueLattice w d hw hwd M ≤ weightedTranslationLattice w d hwd := by
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd]
  rintro g ⟨z, _, hz⟩
  exact ⟨z, hz⟩

omit [Fintype σ] in
theorem integerTranslation_base_pow
    (γ : PolynomialTranslationGroupOver ℤ σ) (n : ℕ) (i : σ) :
    (γ ^ n).base i = (n : ℤ) * γ.base i := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, PolynomialTranslationGroupOver.base_mul, Pi.add_apply, ih,
        Nat.cast_add, Nat.cast_one, add_mul, one_mul]

theorem weightedTranslationResidueLattice_contains_power_cover
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    subgroupPowerCover (weightedTranslationLattice w d hwd) M ≤
      weightedTranslationResidueLattice w d hw hwd M := by
  apply (subgroupPowerCover_le_iff _ _ M).mpr
  intro g hg
  rw [weightedTranslationLattice_eq_integral_preimage w d hw hwd] at hg
  obtain ⟨γ, hγ⟩ := hg
  refine ⟨γ ^ M, ?_, ?_⟩
  · intro i
    rw [integerTranslation_base_pow]
    simp
  · rw [map_pow, map_pow, hγ]

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

theorem weightedTranslationResidueLattice_inner_grid (M : ℕ) :
    scaledIntegerGrid (d.factorial * M) ⊆
      bchSubgroupCoordinates (weightedOrderedBasis w d hw)
        (weightedTranslationResidueLattice w d hw hwd M) := by
  have hinner := subgroupPowerCover_inner_grid (weightedOrderedBasis w d hw)
    (weightedTranslationLattice w d hwd) d.factorial M (weightedOrderedBasis_inner_grid w d hw hwd)
  intro x hx
  apply weightedTranslationResidueLattice_contains_power_cover w d hw hwd M
  apply hinner
  simpa only [Nat.mul_comm] using hx

theorem weightedTranslationResidueLattice_outer_grid (M : ℕ) :
    bchSubgroupCoordinates (weightedOrderedBasis w d hw)
      (weightedTranslationResidueLattice w d hw hwd M) ⊆
        denominatorGrid (d.factorial * M) := by
  intro x hx
  have h0 := weightedOrderedBasis_outer_grid w d hw hwd
    (weightedTranslationResidueLattice_le w d hw hwd M hx)
  simpa only [Nat.mul_comm] using denominator_grid_subset_mul d.factorial M h0

end Erdos3.PolynomialTranslationLie

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

variable {m : ℕ}

theorem bufferedTranslationTerm_nonzero_iff (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) :
    bufferedTranslationTerm Ψ D₀ g β ≠ 0 ↔
      Ψ.value (fun i => g.base i - (β i : ℝ)) ≠ 0 := by
  simp only [bufferedTranslationTerm, ne_eq, mul_eq_zero, Complex.ofReal_eq_zero,
    Circle.coe_ne_zero, or_false]

theorem bufferedTranslationTerm_unique (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β γ : Fin m → ℤ)
    (hβ : bufferedTranslationTerm Ψ D₀ g β ≠ 0)
    (hγ : bufferedTranslationTerm Ψ D₀ g γ ≠ 0) : β = γ := by
  have hβ' := (bufferedTranslationTerm_nonzero_iff Ψ D₀ g β).mp hβ
  have hγ' := (bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hγ
  exact (Ψ.buffered_lift_unique g.base β γ
    (fun i => (Ψ.support _ hβ' i).trans (by norm_num)) hγ').symm

theorem bufferedTranslationPhase_eq_chart (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : ∀ i, |g.base i - (β i : ℝ)| ≤ 1 / 2) :
    bufferedTranslationPhase Ψ D₀ g = bufferedTranslationTerm Ψ D₀ g β := by
  classical
  apply tsum_eq_single β
  intro γ hγ
  by_contra hn
  exact hγ (Ψ.buffered_lift_unique g.base β γ hβ
    ((bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hn))

theorem bufferedTranslationPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    ‖bufferedTranslationPhase Ψ D₀ g‖ ≤ 1 := by
  rw [bufferedTranslationPhase_eq_chart Ψ D₀ g (nearestIntegerLift g.base)
    (nearestIntegerLift_close g.base)]
  simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
  exact Ψ.le_one _

theorem bufferedTranslationQuotientPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationSubgroup) :
    ‖bufferedTranslationQuotientPhase Ψ D₀ g‖ ≤ 1 := by
  refine Quotient.inductionOn g ?_
  exact bufferedTranslationPhase_norm_le_one Ψ D₀

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {m : ℕ} (M : ℕ)

theorem twistedBufferedTranslationTerm_unique (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β γ : Fin m → ℤ)
    (hβ : twistedBufferedTranslationTerm M Ψ D₀ T g β ≠ 0)
    (hγ : twistedBufferedTranslationTerm M Ψ D₀ T g γ ≠ 0) : β = γ :=
  bufferedTranslationTerm_unique Ψ D₀ g β γ
    (mul_ne_zero_iff.mp hβ).2 (mul_ne_zero_iff.mp hγ).2

theorem twistedBufferedTranslationPhase_eq_chart (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    (hβ : ∀ i, |g.base i - (β i : ℝ)| ≤ 1 / 2) :
    twistedBufferedTranslationPhase M Ψ D₀ T g = twistedBufferedTranslationTerm M Ψ D₀ T g β := by
  classical
  apply tsum_eq_single β
  intro γ hγ
  by_contra hn
  have hb := (mul_ne_zero_iff.mp hn).2
  exact hγ (Ψ.buffered_lift_unique g.base β γ hβ
    ((bufferedTranslationTerm_nonzero_iff Ψ D₀ g γ).mp hb))

theorem twistedBufferedTranslationTerm_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ) :
    ‖twistedBufferedTranslationTerm M Ψ D₀ T g β‖ ≤ 1 := by
  have hb : ‖bufferedTranslationTerm Ψ D₀ g β‖ ≤ 1 := by
    simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
    exact Ψ.le_one _
  rw [twistedBufferedTranslationTerm, norm_mul]
  exact (mul_le_mul (hT _ _) hb (norm_nonneg _) (by norm_num)).trans (by norm_num)

theorem twistedBufferedTranslationPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m)) :
    ‖twistedBufferedTranslationPhase M Ψ D₀ T g‖ ≤ 1 := by
  rw [twistedBufferedTranslationPhase_eq_chart M Ψ D₀ T g (nearestIntegerLift g.base)
    (nearestIntegerLift_close g.base)]
  exact twistedBufferedTranslationTerm_norm_le_one M Ψ D₀ T hT g _

theorem twistedBufferedTranslationQuotientPhase_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) (hT : ∀ x r, ‖T x r‖ ≤ 1)
    (g : PolynomialTranslationGroupOver ℝ (Fin m) ⧸ integerPolynomialTranslationResidueCover M) :
    ‖twistedBufferedTranslationQuotientPhase M Ψ D₀ T g‖ ≤ 1 := by
  refine Quotient.inductionOn g ?_
  exact twistedBufferedTranslationPhase_norm_le_one M Ψ D₀ T hT

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BufferedTranslationIncrement
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {m : ℕ}

theorem translation_cutoff_increment_bound (Ψ : PatchKernel m)
    (z g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    {ε : ℝ} (hε : 0 ≤ ε) (hbase : ∀ i, |z.base i| ≤ ε) :
    |Ψ.value (fun i => (z * g).base i - (β i : ℝ)) -
      Ψ.value (fun i => g.base i - (β i : ℝ))| ≤ Ψ.lip * ε := by
  have hdist : dist (fun i => (z * g).base i - (β i : ℝ))
      (fun i => g.base i - (β i : ℝ)) ≤ ε := by
    apply (dist_pi_le_iff hε).mpr
    intro i
    simp only [Real.dist_eq, PolynomialTranslationGroupOver.base_mul, Pi.add_apply]
    rw [show z.base i + g.base i - (β i : ℝ) - (g.base i - (β i : ℝ)) = z.base i by ring]
    exact hbase i
  exact (Ψ.lipschitz.dist_le_mul _ _).trans
    (mul_le_mul_of_nonneg_left hdist Ψ.lip.coe_nonneg)

theorem bufferedTranslationTerm_increment_bound (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (z g : PolynomialTranslationGroupOver ℝ (Fin m)) (β : Fin m → ℤ)
    {d : ℕ} {M ε : ℝ} (hε : 0 ≤ ε) (hεsmall : ε ≤ 1 / 4)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (hbase : ∀ i, |z.base i| ≤ ε)
    (heval : ∀ x : Fin m → ℝ, (∀ i, |x i| ≤ 1) → |eval x z.polynomial| ≤ ε) :
    ‖bufferedTranslationTerm Ψ D₀ (z * g) β - bufferedTranslationTerm Ψ D₀ g β‖ ≤
      (Ψ.lip + (2 * Real.pi) * (1 + M * m * d)) * ε := by
  let a := Ψ.value (fun i => (z * g).base i - (β i : ℝ))
  let b := Ψ.value (fun i => g.base i - (β i : ℝ))
  let v : ℂ := Real.fourierChar (translationPhaseArgument D₀ (z * g) (fun i => (β i : ℝ)))
  let u : ℂ := Real.fourierChar (translationPhaseArgument D₀ g (fun i => (β i : ℝ)))
  have hv : ‖v‖ = 1 := Circle.norm_coe _
  have hdiff : |a - b| ≤ Ψ.lip * ε := translation_cutoff_increment_bound Ψ z g β hε hbase
  have hM : 0 ≤ M := (realPolynomialMass_nonneg D₀).trans hD
  change ‖(a : ℂ) * v - (b : ℂ) * u‖ ≤ _
  by_cases hb : b = 0
  · rw [hb, Complex.ofReal_zero, zero_mul, sub_zero, norm_mul, hv, mul_one,
      Complex.norm_real, Real.norm_eq_abs]
    have ha : |a| ≤ Ψ.lip * ε := by simpa only [hb, sub_zero] using hdiff
    apply ha.trans
    have hn : 0 ≤ (2 * Real.pi) * (1 + M * m * d) := by positivity
    nlinarith
  · have hres (i : Fin m) : |(β i : ℝ) - g.base i| ≤ 1 / 4 := by
      rw [abs_sub_comm]
      exact Ψ.support _ hb i
    have he : |eval ((fun i => (β i : ℝ)) - g.base) z.polynomial| ≤ ε :=
      heval _ (fun i => (hres i).trans (by norm_num))
    have hc : ‖v - u‖ ≤ (2 * Real.pi) * (1 + M * m * d) * ε := by
      simpa only [Fintype.card_fin] using
        translationPhaseCharacter_left_increment_quarter_point_bound D₀ z g
          (fun i => (β i : ℝ)) hε hεsmall hdegree hD hres hbase he
    have hid : (a : ℂ) * v - (b : ℂ) * u = ((a - b : ℝ) : ℂ) * v + (b : ℂ) * (v - u) := by
      push_cast
      ring
    rw [hid]
    have h1 : ‖((a - b : ℝ) : ℂ) * v‖ ≤ Ψ.lip * ε := by
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, hv, mul_one] using hdiff
    have h2 : ‖(b : ℂ) * (v - u)‖ ≤ (2 * Real.pi) * (1 + M * m * d) * ε := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
      exact (mul_le_mul_of_nonneg_right (Ψ.le_one _) (norm_nonneg _)).trans
        (by simpa only [one_mul] using hc)
    exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by ring))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ComparisonChosenLayerBasis
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeBasis_permute (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (j : M.SquarefreeBasisIndex) :
    ∃ k, M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he
      (M.squarefreeBasis p j) = M.squarefreeBasis p k := by
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  exact M.filtration.squarefreeBasis_permute (fun j : ReplicatedIndex bound => j.1)
    (chosenBoundedSubmoduleBasis D.basis ⌈Real.exp p⌉₊) e he j

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.NativeSquarefreeGrids
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeGrid_permute (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (B : ℕ)
    {x : M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)}
    (hx : x ∈ coordinateGridModule (M.squarefreeBasis p) B) :
    M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x ∈
      coordinateGridModule (M.squarefreeBasis p) B :=
  coordinateGridModule_map_of_basis (M.squarefreeBasis p) (M.squarefreeBasis p)
    (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he).toLinearEquiv.toLinearMap
    (M.squarefreeBasis_permute p e he) B hx

theorem squarefreeGrid_permute_iff (p : ℝ) (e : Equiv.Perm (ReplicatedIndex bound))
    (he : ∀ j, (e j).1 = j.1) (B : ℕ)
    (x : M.filtration.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x ∈
      coordinateGridModule (M.squarefreeBasis p) B ↔ x ∈ coordinateGridModule (M.squarefreeBasis p) B := by
  constructor
  · intro hx
    have h := M.squarefreeGrid_permute p e.symm
      (MultidegreeLieFiltration.blockPermutation_symm _ e he) B hx
    have heq : M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e.symm
        (MultidegreeLieFiltration.blockPermutation_symm _ e he)
        (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he x) = x :=
      Subtype.ext (squarefreePermute_symm_apply e x.val)
    rwa [heq] at h
  · exact M.squarefreeGrid_permute p e he B

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NativeSquarefreeLattice
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem squarefreeLattice_permute (p : ℝ) (B : ℕ) (hstable : M.SquarefreeGridStable p B)
    (e : Equiv.Perm (ReplicatedIndex bound)) (he : ∀ j, (e j).1 = j.1)
    (g : (M.filtration.squarefreeOrdinaryFiltration (fun j : ReplicatedIndex bound => j.1)).Group) :
    NilpotentLieBCHGroup.map
        (M.filtration.squarefreeBlockPermute (fun j : ReplicatedIndex bound => j.1) e he).toLieHom g ∈
        M.squarefreeLattice p B hstable ↔ g ∈ M.squarefreeLattice p B hstable :=
  M.squarefreeGrid_permute_iff p e he B g.coord

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeRealAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

theorem squarefreeRealPermute_one (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeRealPermute p B hB hstable 1 g = g := by
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_eq_self _ M.filtration.replicatedLiePermute_one g.coord

theorem squarefreeRealPermute_lattice (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).realLattice ≤
      (M.squarefreeModel p B hB hstable).realLattice.comap
        (M.squarefreeRealPermute p B hB hstable e) := by
  apply realificationMap_subgroup
  intro g hg
  exact (M.squarefreeLattice_permute p B hstable (replicatedPermutation bound e)
    (replicatedPermutation_block bound e) g).mpr hg

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedTranslationBufferedCoordinates
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

theorem weightedShearEmbedding_coordinate_row (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : PolynomialShearIndex (shearWeight w d)) :
    (∀ x, (polynomialShearBasis (R := ℚ) (shearWeight w d)).repr
      (weightedShearEmbedding w d x) a = 0) ∨
    ∃ i : WeightedBasisIndex w d, ∀ x,
      (polynomialShearBasis (R := ℚ) (shearWeight w d)).repr
        (weightedShearEmbedding w d x) a = (weightedBasis w d hw).repr x i := by
  classical
  rcases a with ⟨i, a, ha⟩
  cases i with
  | inl i =>
      by_cases ha0 : a = 0
      · right
        refine ⟨Sum.inl i, fun x => ?_⟩
        rw [polynomialShearBasis_repr, weightedBasis_repr_inl]
        change (shearDerivation x.val (X (Sum.inl i))).coeff a = _
        rw [shearDerivation_X_inl, ha0]
        simp
      · left
        intro x
        rw [polynomialShearBasis_repr]
        change (shearDerivation x.val (X (Sum.inl i))).coeff a = 0
        rw [shearDerivation_X_inl]
        simp [MvPolynomial.coeff_C, Ne.symm ha0]
  | inr u =>
      by_cases hb : ∃ b : σ →₀ ℕ, b.mapDomain Sum.inl = a
      · obtain ⟨b, rfl⟩ := hb
        have hweight : Finsupp.weight (shearWeight w d) (b.mapDomain Sum.inl) =
            Finsupp.weight w b := by
          change Finsupp.linearCombination ℕ (shearWeight w d) (b.mapDomain Sum.inl) =
            Finsupp.linearCombination ℕ w b
          rw [Finsupp.linearCombination_mapDomain]
          rfl
        have hb : Finsupp.weight w b < d := by
          change Finsupp.weight (shearWeight w d) (b.mapDomain Sum.inl) + 1 ≤ d at ha
          rw [hweight] at ha
          omega
        right
        refine ⟨Sum.inr ⟨b, hb⟩, fun x => ?_⟩
        rw [polynomialShearBasis_repr, weightedBasis_repr_inr]
        change (shearDerivation x.val (X (Sum.inr u))).coeff (b.mapDomain Sum.inl) = _
        rw [shearDerivation_X_inr, coeff_rename_mapDomain Sum.inl Sum.inl_injective]
      · left
        intro x
        rw [polynomialShearBasis_repr]
        change (shearDerivation x.val (X (Sum.inr u))).coeff a = 0
        rw [shearDerivation_X_inr]
        apply coeff_rename_eq_zero
        intro b hba
        exact (hb ⟨b, hba⟩).elim

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

open Module
open scoped TensorProduct

namespace PolynomialTranslationLie

variable {σ : Type*} [Fintype σ]

theorem realShearEmbedding_repr (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (a : PolynomialShearIndex (shearWeight w d)) :
    (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a =
      ((polynomialShearBasis (R := ℚ) (shearWeight w d)).baseChange ℝ).repr
        (realificationLieHom (weightedShearEmbedding w d) x) a := by
  exact congrArg (fun c => c a) (polynomialShearRealificationEquiv_repr (shearWeight w d)
    (realificationLieHom (weightedShearEmbedding w d) x))

theorem realShearEmbedding_coordinate_row (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (a : PolynomialShearIndex (shearWeight w d)) :
    (∀ x, (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d x) a = 0) ∨
    ∃ i : WeightedBasisIndex w d, ∀ x,
      (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
        (realShearEmbedding w d x) a = ((weightedBasis w d hw).baseChange ℝ).repr x i := by
  rcases weightedShearEmbedding_coordinate_row w d hw a with hzero | ⟨i, hi⟩
  · left
    intro x
    rw [realShearEmbedding_repr]
    exact realificationLieHom_repr_zero (polynomialShearBasis (shearWeight w d))
      (weightedShearEmbedding w d) a hzero x
  · right
    refine ⟨i, fun x => ?_⟩
    rw [realShearEmbedding_repr]
    exact realificationLieHom_repr_coordinate (weightedBasis w d hw)
      (polynomialShearBasis (shearWeight w d)) (weightedShearEmbedding w d) a i hi x

theorem realShearEmbedding_coordinate_abs_le (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hx : ∀ i, |((weightedBasis w d hw).baseChange ℝ).repr x i| ≤ δ)
    (a : PolynomialShearIndex (shearWeight w d)) :
    |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a| ≤
      δ := by
  rcases realShearEmbedding_coordinate_row w d hw a with hzero | ⟨i, hi⟩
  · simpa only [hzero x, abs_zero] using hδ
  · rw [hi x]
    exact hx i

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ]

theorem bchRealTranslation_inverse_action_X (w : σ → ℕ) (d : ℕ)
    (hwd : ∀ i, w i ≤ d) (g : (weightedFiltration w d hwd).realification.Group)
    (i : σ ⊕ Unit) :
    (PolynomialTranslationGroupOver.actionMonoidHom (bchRealTranslationHom w d hwd g)).symm (X i) =
      polynomialShearExp (-(realShearEmbedding w d g.coord)) (X i) := by
  calc
    _ = PolynomialTranslationGroupOver.actionMonoidHom
        (bchRealTranslationHom w d hwd g⁻¹) (X i) := by
      rw [map_inv, map_inv]
      rfl
    _ = (weightedShearRealGroupHom w d hwd g⁻¹).val (X i) := by
      rw [bchRealTranslationHom_action]
    _ = _ := by
      change polynomialShearExp (realShearEmbedding w d g⁻¹.coord) (X i) = _
      rw [coord_inv, map_neg]

theorem bchRealTranslation_bounds_of_shear_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group)
    {δ : ℝ} (hδ : 0 ≤ δ) (hδone : δ ≤ 1)
    (hg : ∀ a, |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (realShearEmbedding w d g.coord) a| ≤ δ) :
    let K := polynomialShearDisplacementBound d (Fintype.card (σ ⊕ Unit)) 1
    (∀ i, |(bchRealTranslationHom w d hwd g).base i| ≤ (K : ℝ) * δ) ∧
      ∀ x : σ → ℝ, (∀ i, |x i| ≤ 1) →
        |eval x (bchRealTranslationHom w d hwd g).polynomial| ≤ (K : ℝ) * δ := by
  let K := polynomialShearDisplacementBound d (Fintype.card (σ ⊕ Unit)) 1
  have hpos : ∀ i, 1 ≤ shearWeight w d i := by
    intro i; cases i with
    | inl i => exact hw i
    | inr _ => exact hd
  have hgn (a) : |(polynomialShearBasis (R := ℝ) (shearWeight w d)).repr
      (-(realShearEmbedding w d g.coord)) a| ≤ δ := by
    simpa only [map_neg, Finsupp.neg_apply, abs_neg] using hg a
  have hpoint (x : σ → ℝ) (hx : ∀ i, |x i| ≤ 1) (i : σ ⊕ Unit) :
      |eval (Sum.elim x (fun _ : Unit => (0 : ℝ)))
        ((PolynomialTranslationGroupOver.actionMonoidHom
          (bchRealTranslationHom w d hwd g)).symm (X i)) -
        Sum.elim x (fun _ : Unit => (0 : ℝ)) i| ≤ (K : ℝ) * δ := by
    rw [bchRealTranslation_inverse_action_X]
    have hh := polynomialShearExp_X_displacement (-(realShearEmbedding w d g.coord))
      hpos (shearWeight_le w d hwd) hδ hδone le_rfl hgn
      (Sum.elim x (fun _ : Unit => (0 : ℝ))) (by
        intro j; cases j with
        | inl j => exact hx j
        | inr _ => simp) i
    convert hh using 1
    · simp only [aeval_eq_eval]
    · simp [K, polynomialShearDisplacementBound, mul_assoc, mul_left_comm, mul_comm]
  constructor
  · intro i
    have hh := hpoint 0 (by simp) (Sum.inl i)
    rw [PolynomialTranslationGroupOver.action_inverse_X_inl_eval] at hh
    simpa [K] using hh
  · intro x hx
    have hh := hpoint x hx (Sum.inr ())
    rw [PolynomialTranslationGroupOver.action_inverse_X_inr_eval] at hh
    simpa [K] using hh

section Metric

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedBasis_real_log_coordinates_bound (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    let C := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
    (C : ℝ) * dist 1 g < 1 →
      ∀ a, |((weightedBasis w d hw).baseChange ℝ).repr g.coord a| ≤ (C : ℝ) * dist 1 g := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
  dsimp only
  intro hnear a
  have hlog : ‖basisHomeomorph ((weightedOrderedBasis w d hw).baseChange ℝ) g‖ ≤
      (C : ℝ) * dist 1 g := by
    have hh := norm_coordinates_le_of_near_one
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
      (lieStructureConstants (weightedOrderedBasis w d hw))
      (fun i j k => (realLieBasis_structure (weightedOrderedBasis w d hw) i j k).symm)
      (weightedOrderedBasis_structure_height w d hw) 1 le_rfl g
    simp only [Fintype.card_fin, NNReal.coe_one] at hh
    exact hh hnear
  have hh := (norm_le_pi_norm
    (basisHomeomorph ((weightedOrderedBasis w d hw).baseChange ℝ) g)
    (weightedIndexOrder w d a)).trans hlog
  have he : (weightedOrderedBasis w d hw).baseChange ℝ =
      ((weightedBasis w d hw).baseChange ℝ).reindex (weightedIndexOrder w d) := by
    ext j
    simp only [weightedOrderedBasis, Basis.baseChange_apply, Basis.reindex_apply]
  simpa only [basisHomeomorph_apply, Basis.equivFun_apply, Real.norm_eq_abs,
    he, Basis.repr_reindex_apply, Equiv.symm_apply_apply] using hh

theorem bchRealTranslation_bounds_near_one (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (g : (weightedFiltration w d hwd).realification.Group) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    let C := weightedTranslationDisplacementConstant d (Fintype.card σ)
      (Fintype.card (WeightedBasisIndex w d))
    dist 1 g ≤ 1 / C →
      (∀ i, |(bchRealTranslationHom w d hwd g).base i| ≤ C * dist 1 g) ∧
      ∀ x : σ → ℝ, (∀ i, |x i| ≤ 1) →
        |eval x (bchRealTranslationHom w d hwd g).polynomial| ≤ C * dist 1 g := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let K : ℝ := polynomialShearDisplacementBound d (Fintype.card σ + 1) 1
  let L : ℝ := bchLogMetricConstant d (Fintype.card (WeightedBasisIndex w d)) (2*d+1) 1
  let C := weightedTranslationDisplacementConstant d (Fintype.card σ)
    (Fintype.card (WeightedBasisIndex w d))
  have hK : 0 ≤ K := NNReal.coe_nonneg _
  have hL : 0 ≤ L := NNReal.coe_nonneg _
  have hC : 0 < C := weightedTranslationDisplacementConstant_pos _ _ _
  have hCeq : C = 2 * (K+1) * (L+1) := rfl
  have hLC : 2 * L ≤ C := by nlinarith [mul_nonneg hK hL]
  have hKC : K * L ≤ C := by nlinarith [mul_nonneg hK hL]
  dsimp only
  intro hnear
  have hdist : 0 ≤ dist 1 g := dist_nonneg
  have hCd : C * dist 1 g ≤ 1 := by
    have hh := (le_div_iff₀ hC).mp hnear
    simpa only [mul_comm] using hh
  have hlognear : L * dist 1 g < 1 := by
    have hh := mul_le_mul_of_nonneg_right hLC hdist
    nlinarith
  have hcoords := weightedBasis_real_log_coordinates_bound w d hw hwd g hlognear
  have hshear := realShearEmbedding_coordinate_abs_le w d hw g.coord
    (mul_nonneg hL hdist) hcoords
  have hbounds := bchRealTranslation_bounds_of_shear_coordinates w d hw hd hwd g
    (mul_nonneg hL hdist) hlognear.le hshear
  have hprod : K * (L * dist 1 g) ≤ C * dist 1 g := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hKC hdist
  constructor
  · intro i
    apply le_trans ?_ hprod
    simpa [K] using hbounds.1 i
  · intro x hx
    apply le_trans ?_ hprod
    simpa [K] using hbounds.2 x hx

end Metric

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTwistedTranslationLipschitz
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
  [Fintype (WeightedBasisIndex w d)]
  [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
  [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem bufferedTranslationTerm_lipschitz
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (β : Fin m → ℤ) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (bufferedTranslationTermLip w d Ψ M)
      (fun g => bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  let C := translationDisplacementNN w d
  let L : ℝ≥0 := (Ψ.lip + ⟨2 * Real.pi, by positivity⟩ * (1 + M * m * d)) * C
  have hC : 0 < (C : ℝ) := weightedTranslationDisplacementConstant_pos _ _ _
  have heq : bufferedTranslationTermLip w d Ψ M = max (2 * (4 * C)) L := by
    dsimp [bufferedTranslationTermLip, L]
    congr 1
    ring
  rw [heq]
  apply lipschitzWith_of_complex_unit_near _ (4 * C) L
  · intro g
    simp only [bufferedTranslationTerm, norm_mul, Circle.norm_coe, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Ψ.nonneg _)]
    exact Ψ.le_one _
  · intro x y hnear
    let z := x * y⁻¹
    have hz : z * y = x := by dsimp [z]; group
    have hdist : dist 1 z = dist x y := by
      have hh := (rightMetricSpace_isometry_mul_right
        ((weightedOrderedBasis w d hw).baseChange ℝ) y⁻¹).dist_eq y x
      simpa only [z, mul_inv_cancel, dist_comm y x] using hh
    have hsmall : (C : ℝ) * dist x y ≤ 1 / 4 := by
      simp only [NNReal.coe_mul, NNReal.coe_ofNat] at hnear
      linarith
    have hnearz : dist 1 z ≤ 1 / (C : ℝ) := by
      rw [hdist, le_div_iff₀ hC]
      nlinarith
    have hnearz' : dist 1 z ≤ 1 / weightedTranslationDisplacementConstant d m
        (Fintype.card (WeightedBasisIndex w d)) := hnearz
    have hb := bchRealTranslation_bounds_near_one w d hw hd hwd z
      (by simpa only [Fintype.card_fin] using hnearz')
    simp only [Fintype.card_fin] at hb
    change (∀ i, |(bchRealTranslationHom w d hwd z).base i| ≤ (C : ℝ) * dist 1 z) ∧
      ∀ a : Fin m → ℝ, (∀ i, |a i| ≤ 1) →
        |eval a (bchRealTranslationHom w d hwd z).polynomial| ≤ (C : ℝ) * dist 1 z at hb
    rw [hdist] at hb
    have h := bufferedTranslationTerm_increment_bound Ψ D₀
      (bchRealTranslationHom w d hwd z) (bchRealTranslationHom w d hwd y) β
      (mul_nonneg hC.le dist_nonneg) hsmall hdegree hD hb.1 hb.2
    rw [← map_mul, hz] at h
    change _ ≤ ((Ψ.lip : ℝ) + 2 * Real.pi * (1 + (M : ℝ) * m * d)) *
      (C : ℝ) * dist x y
    simpa only [mul_assoc] using h

theorem bufferedTranslationPhase_lipschitz
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d)
    (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M) :
    letI := rightMetricSpace
      (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
      ((weightedOrderedBasis w d hw).baseChange ℝ)
    LipschitzWith (2 * bufferedTranslationTermLip w d Ψ M)
      (fun g => bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd g)) := by
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot)
    ((weightedOrderedBasis w d hw).baseChange ℝ)
  exact separated_complex_tsum_lipschitz
    (fun β g => bufferedTranslationTerm Ψ D₀ (bchRealTranslationHom w d hwd g) β)
    (fun β => bufferedTranslationTerm_lipschitz w d hw hd hwd Ψ D₀ M hdegree hD β)
    (fun g β γ => bufferedTranslationTerm_unique Ψ D₀ (bchRealTranslationHom w d hwd g) β γ)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3

namespace PolynomialTranslationLie

open _root_.MvPolynomial NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    [Fintype (WeightedBasisIndex w d)]
    [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

noncomputable def twistedBufferedTranslationTermLip (Ψ : PatchKernel m) (A K : ℝ≥0) : ℝ≥0 :=
  max (2 * translationDisplacementNN w d)
    (bufferedTranslationTermLip w d Ψ A + K * translationDisplacementNN w d)

end PolynomialTranslationLie

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeQuotientAction
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound) (p : ℝ) (B : ℕ) (hB : 0 < B)
  (hstable : M.SquarefreeGridStable p B)

noncomputable def squarefreeSpacePermute (e : ReplicatedPermutation bound) :
    (M.squarefreeModel p B hB hstable).Space → (M.squarefreeModel p B hB hstable).Space :=
  cosetMap _ _ (M.squarefreeRealPermute p B hB hstable e)
    (M.squarefreeRealPermute_lattice p B hB hstable e)

theorem squarefreeSpacePermute_mk (e : ReplicatedPermutation bound)
    (g : (M.squarefreeModel p B hB hstable).RealGroup) :
    M.squarefreeSpacePermute p B hB hstable e (QuotientGroup.mk g) =
      QuotientGroup.mk (M.squarefreeRealPermute p B hB hstable e g) := rfl

theorem squarefreeSpacePermute_one (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable 1 x = x := by
  induction x using Quotient.inductionOn with
  | h g => rw [M.squarefreeSpacePermute_mk, M.squarefreeRealPermute_one]

theorem squarefreeSpacePermute_mul (e f : ReplicatedPermutation bound)
    (x : (M.squarefreeModel p B hB hstable).Space) :
    M.squarefreeSpacePermute p B hB hstable (e * f) x =
      M.squarefreeSpacePermute p B hB hstable e (M.squarefreeSpacePermute p B hB hstable f x) := by
  induction x using Quotient.inductionOn with
  | h g =>
    rw [M.squarefreeSpacePermute_mk, M.squarefreeSpacePermute_mk,
      M.squarefreeSpacePermute_mk, M.squarefreeRealPermute_mul]

@[instance_reducible]
noncomputable def squarefreeSpaceAction :
    MulAction (ReplicatedPermutation bound) (M.squarefreeModel p B hB hstable).Space where
  smul := M.squarefreeSpacePermute p B hB hstable
  one_smul := M.squarefreeSpacePermute_one p B hB hstable
  mul_smul := M.squarefreeSpacePermute_mul p B hB hstable

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.BohrNiltestBudget
namespace OAI

section

namespace Erdos3.RationalTorus

open Module

def filtration (d : ℕ) : NilpotentLieFiltration (Algebra d) 1 where
  layer j := if j ≤ 1 then ⊤ else ⊥
  antitone := by
    intro i j hij
    by_cases hj : j ≤ 1
    · have hi := hij.trans hj
      simp only [hi, hj, ite_true, le_refl]
    · simp only [hj, ite_false, bot_le]
  one_eq_top := by simp
  lie_mem := by
    intro i j a b _ _
    rw [lie_eq_zero]
    exact Submodule.zero_mem _
  terminal := by simp

theorem basis_layers (d j : ℕ) :
    (filtration d).layer j = Submodule.span ℚ ((basis d) '' {_i : Fin d | j ≤ (1 : ℕ)}) := by
  by_cases hj : j ≤ 1
  · simpa only [filtration, hj, ite_true, Set.ofPred_true, Set.image_univ] using (basis d).span_eq.symm
  · simp only [filtration, hj, ite_false, Set.ofPred_false, Set.image_empty, Submodule.span_empty]

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open Module

noncomputable def lattice (d : ℕ) : Subgroup (filtration d).Group where
  carrier := {g | IntegralVector g.coord}
  one_mem' := ⟨0, fun _ => rfl⟩
  mul_mem' := by
    intro a b ha hb
    obtain ⟨z, hz⟩ := ha
    obtain ⟨w, hw⟩ := hb
    refine ⟨z + w, ?_⟩
    intro i
    rw [(filtration d).stepOne_coord_mul]
    change a.coord i + b.coord i = ((z + w) i : ℚ)
    simp only [Pi.add_apply, Int.cast_add, hz, hw]
  inv_mem' := by
    intro a ha
    obtain ⟨z, hz⟩ := ha
    refine ⟨-z, ?_⟩
    intro i
    change -(a.coord i) = ((-z) i : ℚ)
    simp only [Pi.neg_apply, Int.cast_neg, hz]

theorem lattice_coordinates (d : ℕ) :
    bchSubgroupCoordinates (basis d) (lattice d) = {x | IntegralVector x} := by
  ext x
  change IntegralVector ((basis d).equivFun.symm x) ↔ IntegralVector x
  rw [basis_equivFun_symm]

theorem lattice_inner_grid (d : ℕ) :
    scaledIntegerGrid 1 ⊆ bchSubgroupCoordinates (basis d) (lattice d) := by
  rw [lattice_coordinates]
  rintro x ⟨z, rfl⟩
  exact ⟨z, fun i => by simp⟩

theorem lattice_outer_grid (d : ℕ) :
    bchSubgroupCoordinates (basis d) (lattice d) ⊆ denominatorGrid 1 := by
  rw [lattice_coordinates]
  intro x hx
  simpa only [denominatorGrid, Set.mem_ofPred_eq, Nat.cast_one, one_smul] using hx

noncomputable def nilmanifold (d : ℕ) : RationalFilteredNilmanifold (Algebra d) 1 d :=
  (filtration d).ofAdaptedBasis (basis d) (fun _ => 1) (basis_layers d)
    (lattice d) 1 (by decide) (lattice_inner_grid d) (lattice_outer_grid d)

end Erdos3.RationalTorus

end

section

namespace Erdos3.RationalTorus

open scoped TensorProduct

noncomputable def phaseCoordinates (d : ℕ) (g : (nilmanifold d).RealGroup) :
    Fin d → CircleFourier.Circle :=
  fun i => (((basis d).baseChange ℝ).repr g.coord i : CircleFourier.Circle)

theorem phaseCoordinates_mul (d : ℕ) (g h : (nilmanifold d).RealGroup) :
    phaseCoordinates d (g * h) = phaseCoordinates d g + phaseCoordinates d h := by
  ext i
  simp only [phaseCoordinates, (nilmanifold d).filtration.realification.stepOne_coord_mul,
    map_add, Finsupp.add_apply, AddCircle.coe_add, Pi.add_apply]

theorem phaseCoordinates_inv (d : ℕ) (g : (nilmanifold d).RealGroup) :
    phaseCoordinates d g⁻¹ = -phaseCoordinates d g := by
  ext i
  simp [phaseCoordinates]

theorem phaseCoordinates_lattice (d : ℕ) (g : (nilmanifold d).RealGroup)
    (hg : g ∈ (nilmanifold d).realLattice) : phaseCoordinates d g = 0 := by
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨z, hz⟩ : IntegralVector a.coord := ha
  ext i
  change ((((basis d).baseChange ℝ).equivFun
    (NilpotentLieBCHGroup.realificationHom a).coord) i : CircleFourier.Circle) = 0
  rw [NilpotentLieBCHGroup.realificationHom_coordinates]
  dsimp only
  rw [basis_repr, hz]
  apply (AddCircle.coe_eq_zero_iff (1 : ℝ)).mpr
  refine ⟨z i, ?_⟩
  simp

noncomputable def phaseProjection (d : ℕ) :
    (nilmanifold d).Space → (Fin d → CircleFourier.Circle) :=
  Quotient.lift (phaseCoordinates d) (fun a b hab => by
    have h := phaseCoordinates_lattice d (a⁻¹ * b) (QuotientGroup.leftRel_apply.mp hab)
    apply Eq.symm
    apply sub_eq_zero.mp
    simpa only [phaseCoordinates_mul, phaseCoordinates_inv, sub_eq_add_neg, add_comm] using h)

@[simp] theorem phaseProjection_mk (d : ℕ) (g : (nilmanifold d).RealGroup) :
    phaseProjection d (QuotientGroup.mk g) = phaseCoordinates d g := rfl

end Erdos3.RationalTorus

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MajorTranslationPureFactorValues
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped TensorProduct

namespace PolynomialTranslationLie

variable {B : Type*} [Fintype B]

theorem bchRealTranslationHom_pure_polynomial_of_shape
    (w : B → ℕ) (d : ℕ) (hwd : ∀ i, w i ≤ d)
    (v : ℝ ⊗[ℚ] weightedSubalgebra w d) (P : MvPolynomial B ℝ)
    (hb : ∀ i, (realShearEmbedding w d v).val (X (Sum.inl i)) = 0)
    (hP : (realShearEmbedding w d v).val (X (Sum.inr ())) = rename Sum.inl P) :
    bchRealTranslationHom w d hwd ⟨v⟩ = ⟨0, P⟩ := by
  apply PolynomialTranslationGroupOver.actionMonoidHom_injective
  rw [bchRealTranslationHom_action]
  change (polynomialShearExpAut (realShearEmbedding w d v)).val = _
  have hsq : ((realShearEmbedding w d v).val.toLinearMap ^ 2) (X (Sum.inr ())) = 0 := by
    change (realShearEmbedding w d v).val ((realShearEmbedding w d v).val (X (Sum.inr ()))) = 0
    rw [hP]
    exact translationShear_derivation_rename_eq_zero _ hb P
  have h := PolynomialTranslationGroupOver.action_eq_of_shape
    (polynomialShearExpAut (realShearEmbedding w d v)).val 0 P
    (fun i => polynomialShearExp_X_of_derivation_eq_C _ _ _
      (by simpa only [Pi.zero_apply, map_zero] using hb i))
    (by change polynomialShearExp _ _ = _
        rw [polynomialShearExp_eq_add_of_sq_eq_zero _ hsq, hP])
  simpa only [PolynomialTranslationGroupOver.actionElement, neg_zero,
    polynomialTranslate_zero_ring] using h.symm

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationRealPureFactors
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

theorem realShearEmbedding_base_coeff (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (i : σ) :
    ((realShearEmbedding w d x).val (X (Sum.inl i))).coeff 0 =
      ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inl i) := by
  let a : PolynomialShearIndex (shearWeight w d) := ⟨Sum.inl i, 0, by
    change Finsupp.weight (shearWeight w d) 0 + 1 ≤ w i
    simpa using Nat.succ_le_of_lt (hw i)⟩
  change (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) a = _
  rw [realShearEmbedding_repr]
  apply realificationLieHom_repr_coordinate (weightedBasis w d hw) _ _ a (Sum.inl i) _ x
  intro y
  rw [polynomialShearBasis_repr, weightedBasis_repr_inl]
  change (shearDerivation y.val (X (Sum.inl i))).coeff 0 = _
  rw [shearDerivation_X_inl]
  simp

theorem realShearEmbedding_extra_coeff (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    (a : {a : σ →₀ ℕ | Finsupp.weight w a < d}) :
    ((realShearEmbedding w d x).val (X (Sum.inr ()))).coeff (a.val.mapDomain Sum.inl) =
      ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inr a) := by
  have hweight : Finsupp.weight (shearWeight w d) (a.val.mapDomain Sum.inl) =
      Finsupp.weight w a.val := by
    change Finsupp.linearCombination ℕ (shearWeight w d) (a.val.mapDomain Sum.inl) = _
    rw [Finsupp.linearCombination_mapDomain]
    rfl
  let j : PolynomialShearIndex (shearWeight w d) := ⟨Sum.inr (), a.val.mapDomain Sum.inl, by
    change Finsupp.weight (shearWeight w d) (a.val.mapDomain Sum.inl) + 1 ≤ d
    rw [hweight]
    exact a.property⟩
  change (polynomialShearBasis (R := ℝ) (shearWeight w d)).repr (realShearEmbedding w d x) j = _
  rw [realShearEmbedding_repr]
  apply realificationLieHom_repr_coordinate (weightedBasis w d hw) _ _ j (Sum.inr a) _ x
  intro y
  rw [polynomialShearBasis_repr, weightedBasis_repr_inr]
  change (shearDerivation y.val (X (Sum.inr ()))).coeff (a.val.mapDomain Sum.inl) = _
  rw [shearDerivation_X_inr, coeff_rename_mapDomain Sum.inl Sum.inl_injective]

theorem realShearEmbedding_polynomial_mem (w : σ → ℕ) (d : ℕ)
    (x : ℝ ⊗[ℚ] weightedSubalgebra w d) (P : MvPolynomial σ ℝ)
    (hP : (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P) :
    P ∈ weightedSupportLT w d := by
  intro a ha
  have hcoeff : ((realShearEmbedding w d x).val (X (Sum.inr ()))).coeff
      (a.mapDomain Sum.inl) ≠ 0 := by
    rw [hP, coeff_rename_mapDomain Sum.inl Sum.inl_injective]
    exact MvPolynomial.mem_support_iff.mp ha
  have h := (realShearEmbedding w d x).property (Sum.inr ())
    (MvPolynomial.mem_support_iff.mpr hcoeff)
  change Finsupp.weight (shearWeight w d) (a.mapDomain Sum.inl) + 1 ≤ d at h
  change Finsupp.weight w a < d
  change Finsupp.linearCombination ℕ (shearWeight w d) (a.mapDomain Sum.inl) + 1 ≤ d at h
  rw [Finsupp.linearCombination_mapDomain] at h
  exact h

theorem realShearEmbedding_shape_of_coordinates (w : σ → ℕ) (d : ℕ)
    (hw : ∀ i, 0 < w i) (x : ℝ ⊗[ℚ] weightedSubalgebra w d)
    (b : σ → ℝ) (P : weightedSupportLT (R := ℝ) w d)
    (hb : ∀ i, ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inl i) = b i)
    (hP : ∀ a, ((weightedBasis w d hw).baseChange ℝ).repr x (Sum.inr a) = P.val.coeff a.val) :
    (∀ i, (realShearEmbedding w d x).val (X (Sum.inl i)) = C (b i)) ∧
      (realShearEmbedding w d x).val (X (Sum.inr ())) = rename Sum.inl P.val := by
  classical
  obtain ⟨b', P', hb', hP'⟩ := realShearEmbedding_shape w d x
  have hbq (i : σ) : b' i = b i := by
    have h := realShearEmbedding_base_coeff w d hw x i
    rw [hb', hb] at h
    simpa using h
  have hPq : P' = P.val := by
    have hmem := realShearEmbedding_polynomial_mem w d x P' hP'
    apply MvPolynomial.ext
    intro a
    by_cases ha : Finsupp.weight w a < d
    · have h := realShearEmbedding_extra_coeff w d hw x ⟨a, ha⟩
      rw [hP', coeff_rename_mapDomain Sum.inl Sum.inl_injective, hP] at h
      exact h
    · have hz (Q : MvPolynomial σ ℝ) (hQ : Q ∈ weightedSupportLT w d) : Q.coeff a = 0 := by
        by_contra hc
        exact ha (hQ (MvPolynomial.mem_support_iff.mpr hc))
      rw [hz P' hmem, hz P.val P.property]
  exact ⟨fun i => (hb' i).trans (congrArg C (hbq i)), hP'.trans (congrArg (rename Sum.inl) hPq)⟩

theorem polynomialRealElement_shear_base (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) (i : σ) :
    (realShearEmbedding w d (polynomialRealElement w d hw P)).val (X (Sum.inl i)) = 0 := by
  simpa using (realShearEmbedding_shape_of_coordinates w d hw
    (polynomialRealElement w d hw P) 0 P (by simp) (by simp)).1 i

theorem polynomialRealElement_shear_extra (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (P : weightedSupportLT (R := ℝ) w d) :
    (realShearEmbedding w d (polynomialRealElement w d hw P)).val (X (Sum.inr ())) =
      rename Sum.inl P.val :=
  (realShearEmbedding_shape_of_coordinates w d hw _ 0 P (by simp) (by simp)).2

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LocalMajorDenseSliceNiltest
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct Manifold ContDiff

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def evalReal (T : D.Niltest w) (x : σ → ℝ) : ℂ :=
  T.observable (QuotientGroup.mk (D.filtration.realification.polynomialOrbitRealEval w x T.orbit))

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedTranslationBufferedObservable (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ) :
    (weightedTranslationNilmanifold w d hw hwd).Space → ℂ :=
  bufferedTranslationQuotientPhase Ψ D₀ ∘ weightedTranslationPhaseQuotientMap w d hw hwd

@[simp] theorem weightedTranslationBufferedObservable_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationBufferedObservable w d hw hwd Ψ D₀ (QuotientGroup.mk g) =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd g) := rfl

theorem weightedTranslationBufferedObservable_norm_le_one (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (g : (weightedTranslationNilmanifold w d hw hwd).Space) :
    ‖weightedTranslationBufferedObservable w d hw hwd Ψ D₀ g‖ ≤ 1 :=
  bufferedTranslationQuotientPhase_norm_le_one Ψ D₀ _

variable [TopologicalSpace (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [IsTopologicalAddGroup (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d)]
    [T2Space (ℝ ⊗[ℚ] weightedSubalgebra w d)]

theorem weightedTranslationBufferedObservable_lipschitz
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M) :
    letI := (weightedTranslationNilmanifold w d hw hwd).metricSpace
    LipschitzWith (2 * bufferedTranslationTermLip w d Ψ M)
      (weightedTranslationBufferedObservable w d hw hwd Ψ D₀) := by
  let e := (weightedOrderedBasis w d hw).baseChange ℝ
  let : FiniteDimensional ℝ (ℝ ⊗[ℚ] weightedSubalgebra w d) := e.finiteDimensional_of_finite
  let := rightMetricSpace
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  let := rightMetricSpace_isIsometricSMul
    (hnil := (weightedFiltration w d hwd).realification.lowerCentralSeries_eq_bot) e
  exact rightCosetMetricSpace_lipschitz_lift
    (weightedTranslationNilmanifold w d hw hwd).realLattice
    (weightedTranslationNilmanifold w d hw hwd).realLattice_closed_discrete.1
    (weightedTranslationBufferedObservable w d hw hwd Ψ D₀)
    (bufferedTranslationPhase_lipschitz w d hw hd hwd Ψ D₀ M hdegree hD)

noncomputable def weightedTranslationBufferedNiltest {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) :
    (weightedTranslationNilmanifold w d hw hwd).Niltest ω where
  orbit := q
  observable := weightedTranslationBufferedObservable w d hw hwd Ψ D₀
  normBound := 1
  lipBound := 2 * bufferedTranslationTermLip w d Ψ M
  norm_le := weightedTranslationBufferedObservable_norm_le_one w d hw hwd Ψ D₀
  lipschitz := weightedTranslationBufferedObservable_lipschitz w d hw hwd hd Ψ D₀ M hdegree hD

@[simp] theorem weightedTranslationBufferedNiltest_eval {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℤ) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).eval t =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitEval ω t q)) := rfl

@[simp] theorem weightedTranslationBufferedNiltest_evalReal {U : Type*} (ω : U → ℕ)
    (hd : 0 < d) (Ψ : PatchKernel m) (D₀ : MvPolynomial (Fin m) ℝ) (M : ℝ≥0)
    (hdegree : D₀.totalDegree ≤ d) (hD : realPolynomialMass D₀ ≤ M)
    (q : (weightedFiltration w d hwd).realification.PolynomialOrbit ω) (t : U → ℝ) :
    (weightedTranslationBufferedNiltest w d hw hwd ω hd Ψ D₀ M hdegree hD q).evalReal t =
      bufferedTranslationPhase Ψ D₀ (bchRealTranslationHom w d hwd
        ((weightedFiltration w d hwd).realification.polynomialOrbitRealEval ω t q)) := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledComparisonModel
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

@[simp] theorem pairToPi_zero (x : L × L) : pairToPi x 0 = x.1 := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedTranslationBufferedCentralFrequency
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

noncomputable def centralRealLine (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    (weightedFiltration w d hwd).realification.Group :=
  ⟨polynomialRealElement w d hw (centralConstantPolynomial w d hd t)⟩

@[simp] theorem centralRealLine_map (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    bchRealTranslationHom w d hwd (centralRealLine w d hw hd hwd t) = ⟨0, C t⟩ :=
  bchRealTranslationHom_pure_polynomial_of_shape w d hwd _ _
    (polynomialRealElement_shear_base w d hw _)
    (polynomialRealElement_shear_extra w d hw _)

@[simp] theorem centralRealLine_zero (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) :
    centralRealLine w d hw hd hwd 0 = 1 := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [centralRealLine_map, map_one, map_zero]
  rfl

@[simp] theorem centralRealLine_add (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t u : ℝ) :
    centralRealLine w d hw hd hwd (t + u) =
      centralRealLine w d hw hd hwd t * centralRealLine w d hw hd hwd u := by
  apply bchRealTranslationHom_injective w d hwd
  simp only [map_mul, centralRealLine_map]
  apply PolynomialTranslationGroupOver.ext <;> simp

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.WeightedTranslationCentralLattice
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

noncomputable def centralRationalElement (w : σ → ℕ) (d : ℕ) (hd : 0 < d)
    (q : ℚ) : weightedSubalgebra w d :=
  ⟨⟨0, C q⟩, ⟨by simp, (monomial_mem_restrictSupport ℚ).mpr
    (Or.inl (by simpa using hd))⟩⟩

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationCentralTop
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie
open _root_.MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

@[simp] theorem centralRealLine_coord (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hd : 0 < d) (hwd : ∀ i, w i ≤ d) (t : ℝ) :
    (centralRealLine w d hw hd hwd t).coord =
      t ⊗ₜ[ℚ] centralRationalElement w d hd 1 := by
  classical
  apply ((weightedBasis w d hw).baseChange ℝ).repr.injective
  ext a
  change ((weightedBasis w d hw).baseChange ℝ).repr
    (polynomialRealElement w d hw (centralConstantPolynomial w d hd t)) a = _
  rw [polynomialRealElement_repr, Basis.baseChange_repr_tmul]
  cases a with
  | inl i => simp [weightedBasis_repr_inl, centralRationalElement]
  | inr a =>
    simp only [Sum.elim_inr, centralConstantPolynomial, weightedBasis_repr_inr,
      centralRationalElement, coeff_C]
    split_ifs <;> simp

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationResidueNilmanifold
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)]

noncomputable def weightedTranslationResidueNilmanifold (M : ℕ) (hM : 0 < M) :
    RationalFilteredNilmanifold (weightedSubalgebra w d) d (Fintype.card (WeightedBasisIndex w d)) where
  filtration := weightedFiltration w d hwd
  basis := weightedOrderedBasis w d hw
  layerBasis i := weightedLayerFinBasis w d hw hwd (i.val+1)
  lattice := weightedTranslationResidueLattice w d hw hwd M
  grid := d.factorial * M
  grid_pos := Nat.mul_pos (Nat.factorial_pos d) hM
  inner_grid := weightedTranslationResidueLattice_inner_grid w d hw hwd M
  outer_grid := weightedTranslationResidueLattice_outer_grid w d hw hwd M

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedTranslationResiduePhase
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
variable {σ : Type*} [Fintype σ]

theorem bchRealTranslationHom_rational_residue
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) (r : (weightedFiltration w d hwd).Group)
    (hr : bchTranslationHom w d hw hwd r ∈
      (integerTranslationResidueSubgroup M).map PolynomialTranslationGroup.fromInteger) :
    bchRealTranslationHom w d hwd (NilpotentLieBCHGroup.realificationHom r) ∈
      integerPolynomialTranslationResidueCover M := by
  obtain ⟨z, hz, he⟩ := hr
  refine ⟨z, hz, ?_⟩
  rw [bchRealTranslationHom_rational w d hw hwd, ← he]
  apply PolynomialTranslationGroupOver.ext
  · funext i
    change (z.base i : ℝ) = ((z.base i : ℚ) : ℝ)
    simp
  · change MvPolynomial.map (Int.castRingHom ℝ) z.polynomial =
      MvPolynomial.map (algebraMap ℚ ℝ) (MvPolynomial.map (Int.castRingHom ℚ) z.polynomial)
    rw [MvPolynomial.map_map]
    congr 1

theorem realResidueLattice_translation_residue_map
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    (M : ℕ) {g : (weightedFiltration w d hwd).realification.Group}
    (hg : g ∈ (weightedTranslationResidueLattice w d hw hwd M).map
      NilpotentLieBCHGroup.realificationHom) :
    bchRealTranslationHom w d hwd g ∈ integerPolynomialTranslationResidueCover M := by
  obtain ⟨r, hr, rfl⟩ := hg
  exact bchRealTranslationHom_rational_residue w d hw hwd M r hr

noncomputable def weightedTranslationResidueQuotientMap
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ) :
    ((weightedFiltration w d hwd).realification.Group ⧸
      (weightedTranslationResidueLattice w d hw hwd M).map NilpotentLieBCHGroup.realificationHom) →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationResidueCover M) :=
  Quotient.map (bchRealTranslationHom w d hwd) (by
    intro a b hab
    apply QuotientGroup.leftRel_apply.mpr
    have h := realResidueLattice_translation_residue_map w d hw hwd M
      (QuotientGroup.leftRel_apply.mp hab)
    simpa only [map_mul, map_inv] using h)

@[simp] theorem weightedTranslationResidueQuotientMap_mk
    (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d) (M : ℕ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationResidueQuotientMap w d hw hwd M (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

section Nilmanifold

variable (w : σ → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i) (hwd : ∀ i, w i ≤ d)
    [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

noncomputable def weightedTranslationResiduePhaseQuotientMap :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space →
      (PolynomialTranslationGroupOver ℝ σ ⧸ integerPolynomialTranslationResidueCover M) :=
  weightedTranslationResidueQuotientMap w d hw hwd M

@[simp] theorem weightedTranslationResiduePhaseQuotientMap_mk
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationResiduePhaseQuotientMap w d hw hwd M hM (QuotientGroup.mk g) =
      QuotientGroup.mk (bchRealTranslationHom w d hwd g) := rfl

end Nilmanifold

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.WeightedTranslationTwistedNiltest
namespace OAI

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial Module NilpotentLieBCHGroup
open scoped NNReal TensorProduct

variable {m : ℕ} (w : Fin m → ℕ) (d : ℕ) (hw : ∀ i, 0 < w i)
    (hwd : ∀ i, w i ≤ d) [Fintype (WeightedBasisIndex w d)] (M : ℕ) (hM : 0 < M)

noncomputable def weightedTranslationTwistedObservable (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ) :
    (weightedTranslationResidueNilmanifold w d hw hwd M hM).Space → ℂ :=
  twistedBufferedTranslationQuotientPhase M Ψ D₀ T ∘
    weightedTranslationResiduePhaseQuotientMap w d hw hwd M hM

@[simp] theorem weightedTranslationTwistedObservable_mk (Ψ : PatchKernel m)
    (D₀ : MvPolynomial (Fin m) ℝ)
    (T : (Fin m → ℝ) → (Fin m → ZMod M) → ℂ)
    (g : (weightedFiltration w d hwd).realification.Group) :
    weightedTranslationTwistedObservable w d hw hwd M hM Ψ D₀ T (QuotientGroup.mk g) =
      twistedBufferedTranslationPhase M Ψ D₀ T (bchRealTranslationHom w d hwd g) := rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end


