-- Prove2me | solution 1 for ApproxDegComp.theorem_23
-- status  : ACCEPTED   (prove)
-- author  : @Abhishek Anand
-- created : 2026-11-13T04:15:14.976426+00:00
-- url     : https://prove2.me/submissions/b32b895c-0299-4cab-a71c-c771c2b36708

import Definitions.Def_ApproxDegCompV1_CompositionEstimates
import Definitions.Def_ApproxDegComp_approxDeg
import Definitions.Def_OAI_Combinatorics_Sensitivity_Composition

-- CompositionTheorem.lean
section
/-!
# Approximate degree under Boolean block composition: elementary operator proof

The new Fourier bound is proved by directed crossings, selection of one
block diagonal, and elementary spectral binning. The former phase extraction
and Bernstein Fourier-level estimate are not used.

The outer function is total. The inner function may have any finite Boolean
promise domain, represented by injective Boolean coordinates. Approximation is
required only on that domain, and composition uses its full product.
-/

namespace ElementaryComposition.CompositionTheorem

open ApproxDegree

open CompositionDefinitions

noncomputable section

variable {Y σ ι : Type*} [Fintype Y] [DecidableEq Y]
  [Fintype σ] [Fintype ι] [DecidableEq ι]

/-- An actual inner witness and raw composite approximant force an outer
polynomial below every admissible factorial-tail cutoff. -/
theorem outer_degree_lt_cutoff (coords : Y → σ → Bool)
    (f : (ι → Bool) → Bool) (g : Y → Bool)
    (w : ConstructedExtraction.InnerData (BooleanApproxDegree.realCoords coords)
      g (bitDegree coords g) (2 / 3))
    (p : MvPolynomial (ι × σ) ℝ) (D : ℕ) (hdeg : p.totalDegree ≤ D)
    (herr : ∀ x : ι → Y,
      |BooleanApproxDegree.bitValue (blockCompose f g x) -
        MvPolynomial.eval (BooleanApproxDegree.realCoords (productCoords coords) x) p| ≤ 1 / 3)
    (r : ℕ) (hr : 1 ≤ r)
    (hcut : 8 * Real.exp 1 *
      (63 * (D : ℝ) / ‖DegreeScaleWitness.witnessStrip w.psi
        (BooleanApproxDegree.realCoords coords) g (bitDegree coords g)‖) ≤ (r : ℝ)) :
    bitDegree (id : (ι → Bool) → ι → Bool) f < r := by
  let κ := ‖DegreeScaleWitness.witnessStrip w.psi
    (BooleanApproxDegree.realCoords coords) g (bitDegree coords g)‖
  let a : ℝ := 63 * (D : ℝ) / κ
  let P := ErrorReduction.bitAmplifierPolynomial p
  let pval : (ι → Y) → ℝ := fun x =>
    MvPolynomial.eval (BooleanApproxDegree.realCoords (productCoords coords) x) P
  have hraw : ApproxDegree.RawPolynomialBound.rawEval (BooleanApproxDegree.realCoords coords) P =
      (fun x => (pval x : ℂ)) := rfl
  obtain ⟨hPdeg, hP⟩ := amplified_composite_bounds coords f g p hdeg herr
  have ha : 0 ≤ a := by dsimp [a, κ]; positivity
  have hnorm : ∀ x : ι → Y,
      |MvPolynomial.eval (ApproxDegree.RawPolynomialBound.productCoords
        (BooleanApproxDegree.realCoords coords) x) P| ≤ 1 := fun x => (hP x).1
  have hlevel : ∀ (b : TensorPhase.Bits ι) (k : ℕ), 1 ≤ k →
      ‖TensorPhase.fourierLevel k
        (WalshReconstruction.coefficient (FiberChannel.channelQ w.u (fun x => (pval x : ℂ))))
        (fun i => TensorPhase.bitSign (b i))‖ ≤ a ^ k / (2 * (k.factorial : ℝ)) := by
    intro b k hk
    have hz : ∀ i, TensorPhase.bitSign (b i) * TensorPhase.bitSign (b i) = 1 := by
      intro i
      cases b i <;> norm_num [TensorPhase.bitSign]
    have hb := ElementaryComposition.RawPolynomialBound.fourier_level_bound w P (9 * D) hPdeg 1
      (by norm_num) hnorm (by omega : 0 < k) (fun i => TensorPhase.bitSign (b i)) hz
    have hscale : (((7 * (9 * D) : ℕ) : ℝ) / κ) = a := by
      dsimp [a]
      push_cast
      ring
    change _ ≤ 1 / (2 * (k.factorial : ℝ)) *
      (((7 * (9 * D) : ℕ) : ℝ) / κ) ^ k at hb
    rw [hscale] at hb
    rw [hraw] at hb
    simpa only [one_div_mul_eq_div] using hb
  obtain ⟨q, hqdeg, hq⟩ := ChannelApproximation.exists_outer_approximant_from_channel
    g w.u w.support w.normalized pval (outerSign f) (3 / 5)
    (fun x => (hP x).2.le) ha r hr hcut hlevel
  obtain ⟨hbitdeg, hbit⟩ := AffineApproximation.positiveSignToBit_approximation f q
    (by intro b; have h := hq b; norm_num [outerSign] at h ⊢; exact h)
  have houter : bitDegree (id : (ι → Bool) → ι → Bool) f ≤
      (AffineApproximation.positiveSignToBit q).totalDegree :=
    BooleanApproxDegree.approximateDegree_le
      ⟨AffineApproximation.positiveSignToBit q, le_rfl, fun b => (hbit b).le⟩
  exact houter.trans_lt (hbitdeg.trans_lt hqdeg)

omit [DecidableEq Y] [DecidableEq ι] in
/-- Constant-factor composition lower bound at bit error `1/3`.

The outer function is arbitrary and total. The inner function is arbitrary on
its finite Boolean promise domain. The only coordinate condition is injectivity;
there are no off-promise bounds, witness assumptions, or analytic premises. -/
theorem approximateDegree_comp_lower (coords : Y → σ → Bool)
    (hinj : Function.Injective coords) (f : (ι → Bool) → Bool) (g : Y → Bool) :
    (bitDegree (id : (ι → Bool) → ι → Bool) f : ℝ) * (bitDegree coords g : ℝ) /
      (1512 * Real.exp 1) ≤
        (bitDegree (productCoords coords) (blockCompose f g) : ℝ) := by
  classical
  by_cases hgz : bitDegree coords g = 0
  · simp only [hgz, Nat.cast_zero, mul_zero, zero_div]
    positivity
  by_cases hfz : bitDegree (id : (ι → Bool) → ι → Bool) f = 0
  · simp only [hfz, Nat.cast_zero, zero_mul, zero_div]
    positivity
  have hg : 0 < bitDegree coords g := Nat.pos_of_ne_zero hgz
  have hf : 0 < bitDegree (id : (ι → Bool) → ι → Bool) f := Nat.pos_of_ne_zero hfz
  have hno := AffineApproximation.inner_sign_nonapproximation
    (BooleanApproxDegree.realCoords coords) g hg
  obtain ⟨w⟩ := ConstructedExtraction.exists_innerData
    (BooleanApproxDegree.realCoords coords) g (bitDegree coords g) hg (2 / 3)
    (by norm_num) hno
  obtain ⟨p, hpdeg, hperr⟩ := exists_minimal_composite_polynomial coords hinj f g
  let D := bitDegree (productCoords coords) (blockCompose f g)
  let κ := ‖DegreeScaleWitness.witnessStrip w.psi
    (BooleanApproxDegree.realCoords coords) g (bitDegree coords g)‖
  have hκ : (bitDegree coords g : ℝ) / 3 < κ := by
    have h := w.scale_lower
    change (2 / 3 : ℝ) * (bitDegree coords g : ℝ) / 2 < κ at h
    linarith
  apply CompositionArithmetic.product_le_of_lt_cutoff hf hg hκ
  exact outer_degree_lt_cutoff coords f g w p D hpdeg hperr
    (CompositionArithmetic.cutoff D κ) (CompositionArithmetic.one_le_cutoff D κ)
    (CompositionArithmetic.threshold_le_cutoff D κ)

omit [Fintype Y] [DecidableEq Y] [DecidableEq ι] in
/-- The usual total-Boolean-function instance of the composition lower bound. -/
theorem total_approximateDegree_comp_lower
    (f : (ι → Bool) → Bool) (g : (σ → Bool) → Bool) :
    (bitDegree (id : (ι → Bool) → ι → Bool) f : ℝ) *
      (bitDegree (id : (σ → Bool) → σ → Bool) g : ℝ) / (1512 * Real.exp 1) ≤
        (bitDegree (productCoords (id : (σ → Bool) → σ → Bool))
          (blockCompose f g) : ℝ) := by
  classical
  exact approximateDegree_comp_lower id Function.injective_id f g

end

end ElementaryComposition.CompositionTheorem
end

/-!
Theorem 23 as stated on Prove2Me, using the elementary composition proof above.
-/

open ApproxDegree

namespace ApproxDegComp

private theorem approxDeg_eq_bitDegree {ι : Type} [Fintype ι]
    (f : (ι → Bool) → Bool) :
    approxDeg f = CompositionDefinitions.bitDegree id f := by
  unfold approxDeg approxDegEps CompositionDefinitions.bitDegree
    BooleanApproxDegree.approximateDegree
  congr 1
  ext d
  change (∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ _) ↔
    (∃ p : MvPolynomial ι ℝ, p.totalDegree ≤ d ∧ _)
  constructor <;> rintro ⟨p, hp, h⟩ <;> refine ⟨p, hp, fun x => ?_⟩
  · rw [abs_sub_comm]
    exact h x
  · rw [abs_sub_comm]
    exact h x

private theorem compose_bitDegree_eq {ι σ : Type} [Fintype ι] [Fintype σ]
    (f : (ι → Bool) → Bool) (g : (σ → Bool) → Bool) :
    CompositionDefinitions.bitDegree
        (CompositionDefinitions.productCoords (id : (σ → Bool) → σ → Bool))
        (CompositionDefinitions.blockCompose f g) =
      CompositionDefinitions.bitDegree id (OAI.Paper320.compose f g) := by
  unfold CompositionDefinitions.bitDegree BooleanApproxDegree.approximateDegree
  congr 1
  ext d
  change (∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ d ∧ _) ↔
    (∃ p : MvPolynomial (ι × σ) ℝ, p.totalDegree ≤ d ∧ _)
  constructor
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, fun x => h (fun i j => x (i, j))⟩
  · rintro ⟨p, hp, h⟩
    exact ⟨p, hp, fun x => h (fun ij => x ij.1 ij.2)⟩

end ApproxDegComp

open ApproxDegComp in
theorem solution :
    ∃ c : ℝ, 0 < c ∧
      ∀ (n m : ℕ) (f : (Fin n → Bool) → Bool) (g : (Fin m → Bool) → Bool),
        c * (approxDeg f : ℝ) * (approxDeg g : ℝ) ≤
          (approxDeg (OAI.Paper320.compose f g) : ℝ) := by
  refine ⟨1 / (1512 * Real.exp 1), by positivity, ?_⟩
  intro n m f g
  have h := ElementaryComposition.CompositionTheorem.total_approximateDegree_comp_lower f g
  rw [ApproxDegComp.compose_bitDegree_eq] at h
  rw [ApproxDegComp.approxDeg_eq_bitDegree f, ApproxDegComp.approxDeg_eq_bitDegree g,
    ApproxDegComp.approxDeg_eq_bitDegree (OAI.Paper320.compose f g)]
  convert h using 1
  ring

