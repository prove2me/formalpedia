-- Prove2me | Definitions.Def_OAIErdos3B003
-- name    : OAIErdos3B003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T07:24:57.962643+00:00
-- url     : https://prove2.me/theorems/137f6e7d-f62e-4259-8b61-2eae8c0edcb8
-- title:
--   OpenAI Erdős-3 split, definitions bundle 4 of 132
-- statement:
--   Definitions bundle 4 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B002`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 4 available.
--
--   Modules: `Estimates.BooleanCubeModeWitness`, `Linear.BooleanCubeCoordinateFrame`, `Polynomial.BoundedRealPolynomialBasis`, `Lattices.IntegerAffineResidues`, `Estimates.RealBooleanInterpolation`, `Linear.MatrixSupInverse`, `Linear.RealKernelJetInverse`, `Lattices.NormalizedIntegerDual`, `Lattices.IntegralAffineModeRemoval`, `Estimates.NormalizedIntervalWindow`, `Linear.KernelMixtureControl`, `Estimates.FiniteReciprocalTenthTail`, `Estimates.CompactIntervalIntegral`, `Geometry.FiniteSupportTranslation`, `Estimates.LocalAverageAmplitude`, `Lattices.IntegerFiberCount`, `Estimates.PartialComplexScaledQuadrature`, `Lattices.CompactLatticeApproximation`, `Probability.BinaryDensity`, `Probability.SampledWeightCellLaw`, `Geometry.BoxWindowAveraging`, `Lattices.AffineBoxTest`, `Estimates.SmoothedImageTest`, `Geometry.BoxImageComparison`, `Geometry.ProductEuclideanCoordinates`, `Estimates.ProperSubspaceCount`, `Lattices.IntegerAbsInterval`, `Lattices.DenseIntegerSpan`, `Estimates.EuclideanBisectorNull`, `Linear.SpanSubsetBasis`, `Linear.ZSpanRounding`, `Lattices.LatticeVoronoiPacking`, `Linear.ShortVectorProjection`, `Sampling.DerivativeGridPoints`, `Lattices.EuclideanDerivativeLattice`, `Probability.DiagonalDensityTransport`, `Geometry.TwoBoxSmoothingComplex`, `Estimates.InverseSqrtMoment`, `Geometry.UnitBoxAmplitude`, `Probability.PairedProductDensity`, `Probability.DiagonalImageDensity`, `Estimates.SmoothSublevelCutoff`, `Geometry.ChartCutoff`, `Geometry.BoxChartCutoff`, `Geometry.SigmaAxisCoordinates`, `Geometry.PivotCoordinateChange`, `Probability.TranslatedMixtureL1`, `Estimates.PivotJacobianBound`, `Linear.PivotNormalizedMatrix`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B002

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def booleanCoefficient {α R : Type*} [DecidableEq α] [CommRing R]
    (f : Finset α → R) (s : Finset α) : R :=
  ∑ t ∈ s.powerset, (-1 : R) ^ (s \ t).card * f t

theorem sum_powerset_neg_one_pow_card_ring {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) : (∑ t ∈ s.powerset, (-1 : R) ^ t.card) = if s = ∅ then 1 else 0 := by
  have h := congrArg (Int.castRingHom R) (Finset.sum_powerset_neg_one_pow_card (x := s))
  simpa only [map_sum, map_pow, map_neg, map_one, map_zero, apply_ite] using h

theorem boolean_interval_alternating_sum {α R : Type*} [DecidableEq α] [CommRing R]
    (s r : Finset α) (hrs : r ⊆ s) :
    (∑ t ∈ s.powerset with r ⊆ t, (-1 : R) ^ (s \ t).card) = if s = r then 1 else 0 := by
  classical
  have hsum : (∑ t ∈ s.powerset with r ⊆ t, (-1 : R) ^ (s \ t).card) =
      ∑ u ∈ (s \ r).powerset, (-1 : R) ^ u.card := by
    refine Finset.sum_bij (fun t _ => s \ t) ?_ ?_ ?_ ?_
    · intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hts, hrt⟩
      rw [Finset.mem_powerset]
      intro a ha
      rcases Finset.mem_sdiff.mp ha with ⟨has, hat⟩
      exact Finset.mem_sdiff.mpr ⟨has, fun har => hat (hrt har)⟩
    · intro t ht u hu heq
      have ht' := Finset.mem_powerset.mp (Finset.mem_filter.mp ht).1
      have hu' := Finset.mem_powerset.mp (Finset.mem_filter.mp hu).1
      have h := congrArg (fun v => s \ v) heq
      simpa only [Finset.sdiff_sdiff_eq_self ht', Finset.sdiff_sdiff_eq_self hu'] using h
    · intro u hu
      have hu' := Finset.mem_powerset.mp hu
      refine ⟨s \ u, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
        intro a har
        apply Finset.mem_sdiff.mpr
        refine ⟨hrs har, ?_⟩
        intro hau
        exact (Finset.mem_sdiff.mp (hu' hau)).2 har
      · exact Finset.sdiff_sdiff_eq_self (hu'.trans Finset.sdiff_subset)
    · intro t _
      rfl
  rw [hsum, sum_powerset_neg_one_pow_card_ring]
  by_cases h : s = r
  · subst s
    simp
  · have hne : s \ r ≠ ∅ := by
      intro hempty
      exact h ((Finset.sdiff_eq_empty_iff_subset.mp hempty).antisymm hrs)
    simp only [hne, h, ite_false]

theorem booleanCoefficient_monomial {α R : Type*} [DecidableEq α] [CommRing R]
    (r s : Finset α) :
    booleanCoefficient (fun t => if r ⊆ t then (1 : R) else 0) s = if s = r then 1 else 0 := by
  classical
  unfold booleanCoefficient
  simp only [mul_ite, mul_one, mul_zero, ← Finset.sum_filter]
  by_cases hrs : r ⊆ s
  · exact boolean_interval_alternating_sum (R := R) s r hrs
  · have hfilter : {t ∈ s.powerset | r ⊆ t} = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro t ht
      rcases Finset.mem_filter.mp ht with ⟨hts, hrt⟩
      exact hrs (hrt.trans (Finset.mem_powerset.mp hts))
    have hne : s ≠ r := fun h => hrs (h.symm ▸ Finset.Subset.refl r)
    simp only [hfilter, Finset.sum_empty, hne, ite_false]

theorem booleanCoefficient_sum {α R B : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (b : Finset B) (f : B → Finset α → R) :
    booleanCoefficient (fun t => ∑ i ∈ b, f i t) s =
      ∑ i ∈ b, booleanCoefficient (f i) s := by
  simp only [booleanCoefficient, Finset.mul_sum]
  exact Finset.sum_comm

theorem booleanCoefficient_const_mul {α R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) (c : R) (f : Finset α → R) :
    booleanCoefficient (fun t => c * f t) s = c * booleanCoefficient f s := by
  simp only [booleanCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem booleanCoefficient_add {α R : Type*} [DecidableEq α] [CommRing R]
    (f g : Finset α → R) (s : Finset α) :
    booleanCoefficient (fun t => f t + g t) s = booleanCoefficient f s + booleanCoefficient g s := by
  simp only [booleanCoefficient, mul_add, Finset.sum_add_distrib]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators

abbrev Variable (α β : Type*) := Option (α ⊕ β)

inductive Form (α β : Type*) where
  | coordinate : Variable α β → Form α β
  | difference : α → Form α β

noncomputable def site {α β R : Type*} [DecidableEq α] [CommRing R]
    (s : Finset α) : Variable α β → R
  | none => 1
  | some (.inl i) => if i ∈ s then 1 else 0
  | some (.inr _) => 0

noncomputable def formPolynomial {α β R : Type*} [CommRing R] :
    Form α β → MvPolynomial (Variable α β) R
  | .coordinate v => X v
  | .difference i => X (some (.inl i)) - X none

noncomputable def formProduct {α β R : Type*} [CommRing R]
    (l : List (Form α β)) : MvPolynomial (Variable α β) R :=
  (l.map formPolynomial).prod

theorem formProduct_nil {α β R : Type*} [CommRing R] :
    formProduct (R := R) ([] : List (Form α β)) = 1 := rfl

theorem formProduct_cons {α β R : Type*} [CommRing R]
    (f : Form α β) (l : List (Form α β)) :
    formProduct (R := R) (f :: l) = formPolynomial f * formProduct l := rfl

noncomputable def vanishingSpan {α β R : Type*} [DecidableEq α] [CommRing R]
    (h : ℕ) : Submodule R (MvPolynomial (Variable α β) R) :=
  Submodule.span R {P | ∃ l : List (Form α β), l.length = h ∧
    (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧ P = formProduct l}

theorem formProduct_mem_vanishingSpan {α β R : Type*} [DecidableEq α] [CommRing R]
    (l : List (Form α β)) (hz : ∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) :
    formProduct (R := R) l ∈ vanishingSpan l.length :=
  Submodule.subset_span ⟨l, rfl, hz, rfl⟩

theorem vanishingSpan_eval_zero {α β R : Type*} [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) (s : Finset α) :
    eval (site s) P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP => obtain ⟨l, _, hz, rfl⟩ := hP; exact hz s
  | zero => simp
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P _ hP => simp only [smul_eq_C_mul, map_mul, eval_C, hP, mul_zero]

theorem vanishingSpan_mul_form {α β R : Type*} [DecidableEq α] [CommRing R]
    {h : ℕ} {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) (f : Form α β) :
    formPolynomial f * P ∈ vanishingSpan (h + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, hz, rfl⟩ := hP
    have he : (f :: l).length = h + 1 := by simp [hl]
    rw [← formProduct_cons, ← he]
    apply formProduct_mem_vanishingSpan
    intro s
    rw [formProduct_cons, map_mul, hz, mul_zero]
  | zero => simpa only [mul_zero] using (vanishingSpan (h + 1)).zero_mem
  | add P Q _ _ hP hQ =>
    simpa only [mul_add] using (vanishingSpan (h + 1)).add_mem hP hQ
  | smul a P _ hP =>
    simpa only [mul_smul_comm] using (vanishingSpan (h + 1)).smul_mem a hP

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open scoped BigOperators NNReal

noncomputable def booleanSiteJets {D α : Type*} [DecidableEq α]
    {O : D → Type*} (sets : ∀ d, O d → Finset α) (x : Finset α → D → ℝ) : (Σ d, O d) → ℝ :=
  fun o => booleanCoefficient (fun s => x s o.1) (sets o.1 o.2)

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

noncomputable def normalMonomial (h : ℕ) (s : Finset α) : MvPolynomial (Variable α β) R :=
  X none ^ (h - s.card) * ∏ i ∈ s, X (some (.inl i))

noncomputable def normalWord (h : ℕ) (s : Finset α) : List (Form α β) :=
  List.replicate (h - s.card) (.coordinate none) ++ s.toList.map (fun i => .coordinate (some (.inl i)))

omit [DecidableEq α] in
theorem normalWord_length (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    (normalWord (β := β) h s).length = h := by
  simp only [normalWord, List.length_append, List.length_replicate, List.length_map,
    Finset.length_toList, Nat.sub_add_cancel hs]

omit [DecidableEq α] in
theorem normalWord_product (h : ℕ) (s : Finset α) :
    formProduct (R := R) (normalWord (β := β) h s) = normalMonomial h s := by
  simp only [normalWord, formProduct, List.map_append, List.prod_append,
    List.map_replicate, List.prod_replicate, List.map_map]
  rw [Finset.prod_map_toList]
  rfl

theorem normalMonomial_eval (h : ℕ) (s t : Finset α) :
    eval (site (β := β) t) (normalMonomial (R := R) h s) = if s ⊆ t then 1 else 0 := by
  simp only [normalMonomial, map_mul, map_pow, eval_X, site, one_pow, one_mul, map_prod]
  by_cases hst : s ⊆ t
  · rw [if_pos hst]
    exact Finset.prod_eq_one (fun i hi => by simp [hst hi])
  · rw [if_neg hst]
    obtain ⟨i, his, hit⟩ := Finset.not_subset.mp hst
    exact Finset.prod_eq_zero his (by simp [hit])

theorem normalMonomial_jet (h : ℕ) (s t : Finset α) :
    booleanCoefficient (fun u => eval (site (β := β) u) (normalMonomial (R := R) h s)) t =
      if t = s then 1 else 0 := by
  simp_rw [normalMonomial_eval]
  exact booleanCoefficient_monomial s t

noncomputable def normalSpan (h : ℕ) : Submodule R (MvPolynomial (Variable α β) R) :=
  Submodule.span R {P | ∃ s : Finset α, s.card ≤ h ∧ P = normalMonomial h s}

omit [DecidableEq α] in
theorem normalMonomial_mem (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    normalMonomial (β := β) (R := R) h s ∈ normalSpan h :=
  Submodule.subset_span ⟨s, hs, rfl⟩

omit [DecidableEq α] in
theorem normalMonomial_mul_root (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    X none * normalMonomial (β := β) (R := R) h s = normalMonomial (h + 1) s := by
  have he : h + 1 - s.card = (h - s.card) + 1 := by omega
  simp only [normalMonomial, he, pow_succ]
  ring

theorem normalMonomial_mul_new (h : ℕ) (s : Finset α) (i : α) (hi : i ∉ s) :
    X (some (.inl i)) * normalMonomial (β := β) (R := R) h s =
      normalMonomial (h + 1) (insert i s) := by
  simp only [normalMonomial, Finset.card_insert_of_notMem hi, Nat.add_sub_add_right,
    Finset.prod_insert hi]
  ring

theorem normalMonomial_mul_coordinate (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (v : Variable α β) :
    X v * normalMonomial (R := R) h s ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  cases v with
  | none =>
    rw [normalMonomial_mul_root h s hs]
    exact Submodule.mem_sup_right (normalMonomial_mem _ _ (by omega))
  | some v =>
    cases v with
    | inl i =>
      by_cases hi : i ∈ s
      · have hz : (X (some (.inl i)) - X none) * normalMonomial (β := β) (R := R) h s ∈
            vanishingSpan (h + 1) := by
          have he : (Form.difference i :: normalWord (β := β) h s).length = h + 1 := by
            simp only [List.length_cons, normalWord_length h s hs]
          rw [← he, ← normalWord_product h s]
          change formProduct (R := R) (Form.difference i :: normalWord h s) ∈ _
          apply formProduct_mem_vanishingSpan
          intro t
          rw [formProduct_cons, normalWord_product, map_mul, normalMonomial_eval]
          by_cases hst : s ⊆ t
          · simp [formPolynomial, site, hst, hst hi]
          · simp [hst]
        have hn := normalMonomial_mem (β := β) (R := R) (h + 1) s (by omega)
        rw [← normalMonomial_mul_root h s hs] at hn
        have he : X (some (.inl i)) * normalMonomial (β := β) (R := R) h s =
            (X (some (.inl i)) - X none) * normalMonomial h s +
              X none * normalMonomial h s := by ring
        rw [he]
        exact Submodule.add_mem_sup hz hn
      · rw [normalMonomial_mul_new h s i hi]
        exact Submodule.mem_sup_right (normalMonomial_mem _ _ (by
          rw [Finset.card_insert_of_notMem hi]; omega))
    | inr j =>
      apply Submodule.mem_sup_left
      have he : (Form.coordinate (some (.inr j)) :: normalWord (β := β) h s).length = h + 1 := by
        simp only [List.length_cons, normalWord_length h s hs]
      rw [← he, ← normalWord_product h s]
      change formProduct (R := R) (Form.coordinate (some (.inr j)) :: normalWord h s) ∈ _
      apply formProduct_mem_vanishingSpan
      intro t
      simp only [formProduct_cons, map_mul, formPolynomial, eval_X, site, zero_mul]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3

open MvPolynomial
open scoped BigOperators Classical

noncomputable def polynomialLinearRow {σ R : Type*} [CommRing R]
    (P : MvPolynomial σ R) (i : σ) : R := P.coeff (Finsupp.single i 1)

noncomputable def rowPolynomial {σ R : Type*} [Fintype σ] [CommRing R]
    (a : σ → R) : MvPolynomial σ R := ∑ i, C (a i) * X i

theorem homogeneous_eq_rowPolynomial {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) :
    P = rowPolynomial (polynomialLinearRow P) := by
  have hp : P ∈ Submodule.span R (Set.range (X : σ → MvPolynomial σ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hP
  clear hP
  induction hp using Submodule.span_induction with
  | mem P hp =>
    obtain ⟨v, rfl⟩ := hp
    have hs (i : σ) : (Finsupp.single v 1 : σ →₀ ℕ) = Finsupp.single i 1 ↔ v = i :=
      (Finsupp.single_left_injective (by decide : (1 : ℕ) ≠ 0)).eq_iff
    simp only [rowPolynomial, polynomialLinearRow, coeff_X, hs, apply_ite, map_one,
      map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  | zero => simp [rowPolynomial, polynomialLinearRow]
  | add P Q _ _ hP hQ =>
    simpa only [rowPolynomial, polynomialLinearRow, MvPolynomial.coeff_add,
      Finsupp.add_apply, map_add, add_mul,
      Finset.sum_add_distrib] using congrArg₂ (fun a b => a + b) hP hQ
  | smul a P _ hP =>
    simpa only [rowPolynomial, polynomialLinearRow, coeff_smul, coeff_C_mul, smul_eq_mul, map_mul,
      smul_eq_C_mul, Finset.mul_sum, mul_assoc] using congrArg (fun Q => a • Q) hP

theorem rowPolynomial_eval {σ R : Type*} [Fintype σ] [CommRing R] (a x : σ → R) :
    eval x (rowPolynomial a) = ∑ i, a i * x i := by
  simp only [rowPolynomial, map_sum, map_mul, eval_C, eval_X]

theorem homogeneous_eval_eq_row {σ R : Type*} [Fintype σ] [CommRing R]
    (P : MvPolynomial σ R) (hP : P.IsHomogeneous 1) (x : σ → R) :
    eval x P = ∑ i, polynomialLinearRow P i * x i := by
  conv_lhs => rw [homogeneous_eq_rowPolynomial P hP]
  rw [rowPolynomial_eval]

end Erdos3

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

variable {α β R : Type*} [DecidableEq α] [CommRing R]

theorem normalSpan_mul_coordinate {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) (v : Variable α β) :
    X v * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, hs, rfl⟩ := hP
    exact normalMonomial_mul_coordinate h s hs v
  | zero => simp only [mul_zero]; exact Submodule.zero_mem _
  | add P Q _ _ hP hQ =>
    rw [mul_add]
    exact Submodule.add_mem _ hP hQ
  | smul a P _ hP =>
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ a hP

theorem reductionSpace_mul_coordinate {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ vanishingSpan h ⊔ normalSpan h) (v : Variable α β) :
    X v * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  obtain ⟨A, hA, B, hB, rfl⟩ := Submodule.mem_sup.mp hP
  rw [mul_add]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (vanishingSpan_mul_form hA (.coordinate v)))
    (normalSpan_mul_coordinate hB v)

theorem reductionSpace_mul_linear {h : ℕ} {P L : MvPolynomial (Variable α β) R}
    (hP : P ∈ vanishingSpan h ⊔ normalSpan h) (hL : L.IsHomogeneous 1) :
    L * P ∈ vanishingSpan (h + 1) ⊔ normalSpan (h + 1) := by
  have hL' : L ∈ Submodule.span R (Set.range (X : Variable α β → MvPolynomial _ R)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hL
  clear hL
  induction hL' using Submodule.span_induction with
  | mem L hL =>
    obtain ⟨v, rfl⟩ := hL
    exact reductionSpace_mul_coordinate hP v
  | zero => simp only [zero_mul]; exact Submodule.zero_mem _
  | add A B _ _ hA hB =>
    rw [add_mul]
    exact Submodule.add_mem _ hA hB
  | smul a L _ hL =>
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ a hL

theorem homogeneous_mem_reductionSpace {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) : P ∈ vanishingSpan h ⊔ normalSpan h := by
  induction h generalizing P with
  | zero =>
    have hp : P ∈ (1 : Submodule R (MvPolynomial (Variable α β) R)) := by
      rw [← homogeneousSubmodule_zero]
      exact hP
    obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hp
    apply Submodule.mem_sup_right
    have hone := normalMonomial_mem (β := β) (R := R) 0 (∅ : Finset α) (by simp)
    have hc := (normalSpan (α := α) (β := β) (R := R) 0).smul_mem a hone
    simpa only [normalMonomial, Finset.card_empty, Nat.sub_self, pow_zero, Finset.prod_empty,
      mul_one, smul_eq_C_mul, algebraMap_eq] using hc
  | succ h ih =>
    have hp : P ∈ homogeneousSubmodule (Variable α β) R 1 *
        homogeneousSubmodule (Variable α β) R h := by
      rw [← homogeneousSubmodule_one_pow (σ := Variable α β) R h, ← pow_succ',
        homogeneousSubmodule_one_pow (σ := Variable α β) R (h + 1)]
      exact hP
    refine Submodule.mul_induction_on hp ?_ ?_
    · intro L hL Q hQ
      exact reductionSpace_mul_linear (ih hQ) hL
    · intro A B hA hB
      exact Submodule.add_mem _ hA hB

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α β R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def siteEvaluation :
    MvPolynomial (Variable α β) R →ₗ[R] (Finset α → R) where
  toFun P s := eval (site s) P
  map_add' P Q := by ext s; exact map_add _ _ _
  map_smul' a P := by ext s; exact smul_eval _ _ _

noncomputable def coefficientLinear (s : Finset α) : (Finset α → R) →ₗ[R] R where
  toFun f := booleanCoefficient f s
  map_add' f g := booleanCoefficient_add f g s
  map_smul' a f := booleanCoefficient_const_mul s a f

noncomputable def interpolation (h : ℕ) : (Finset α → R) →ₗ[R] MvPolynomial (Variable α β) R :=
  ∑ s : Finset α, if s.card ≤ h then (coefficientLinear s).smulRight (normalMonomial h s) else 0

theorem interpolation_apply (h : ℕ) (f : Finset α → R) :
    interpolation (β := β) h f =
      ∑ s : Finset α, if s.card ≤ h then booleanCoefficient f s • normalMonomial h s else 0 := by
  simp only [interpolation, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro s _
  by_cases hs : s.card ≤ h
  · simp only [hs, ite_true, LinearMap.smulRight_apply]
    rfl
  · simp only [hs, ite_false, LinearMap.zero_apply]

theorem interpolation_normalMonomial (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    interpolation (β := β) h (siteEvaluation (normalMonomial (β := β) (R := R) h s)) =
      normalMonomial h s := by
  rw [interpolation_apply]
  change (∑ t : Finset α, if t.card ≤ h then
    booleanCoefficient (fun u => eval (site u) (normalMonomial (β := β) (R := R) h s)) t •
      normalMonomial h t else 0) = _
  simp_rw [normalMonomial_jet]
  rw [Finset.sum_eq_single s]
  · simp only [hs, ite_true, one_smul]
  · intro t _ ht
    simp only [ht, ite_false, zero_smul, ite_self]
  · simp

theorem interpolation_eq_of_mem_normalSpan {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P ∈ normalSpan h) : interpolation h (siteEvaluation P) = P := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨s, hs, rfl⟩ := hP
    exact interpolation_normalMonomial h s hs
  | zero => simp only [map_zero]
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ]
  | smul a P _ hP => simp only [map_smul, hP]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

variable {α β R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

theorem remainder_mem_vanishingSpan {h : ℕ} {P : MvPolynomial (Variable α β) R}
    (hP : P.IsHomogeneous h) : P - interpolation h (siteEvaluation P) ∈ vanishingSpan h := by
  obtain ⟨A, hA, B, hB, he⟩ := Submodule.mem_sup.mp (homogeneous_mem_reductionSpace hP)
  have hEA : siteEvaluation A = 0 := by ext s; exact vanishingSpan_eval_zero hA s
  rw [← he, map_add, hEA, zero_add, interpolation_eq_of_mem_normalSpan hB, add_sub_cancel_right]
  exact hA

omit [Fintype α] in
theorem map_vanishingSpan_eq_zero (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) {h : ℕ}
    (hkill : ∀ l : List (Form α β), l.length = h →
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) → Λ (formProduct l) = 0)
    {P : MvPolynomial (Variable α β) R} (hP : P ∈ vanishingSpan h) : Λ P = 0 := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨l, hl, hz, rfl⟩ := hP
    exact hkill l hl hz
  | zero => exact map_zero Λ
  | add P Q _ _ hP hQ => simp only [map_add, hP, hQ, add_zero]
  | smul a P _ hP => simp only [map_smul, hP, smul_zero]

theorem factor_through_sites_of_kills_products
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) (h : ℕ)
    (hkill : ∀ l : List (Form α β), l.length = h →
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) → Λ (formProduct l) = 0)
    {P : MvPolynomial (Variable α β) R} (hP : P.IsHomogeneous h) :
    Λ P = (Λ.comp (interpolation h)) (siteEvaluation P) := by
  have hz := map_vanishingSpan_eq_zero Λ hkill (remainder_mem_vanishingSpan hP)
  rw [map_sub, sub_eq_zero] at hz
  exact hz

theorem exists_vanishing_product_of_nonfactor
    (Λ : MvPolynomial (Variable α β) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (siteEvaluation P)) :
    ∃ l : List (Form α β), l.length = h ∧
      (∀ s : Finset α, eval (site s) (formProduct (R := R) l) = 0) ∧ Λ (formProduct l) ≠ 0 := by
  by_contra hnone
  apply hnonfactor
  refine ⟨Λ.comp (interpolation h), fun P hP => factor_through_sites_of_kills_products Λ h ?_ hP⟩
  intro l hl hz
  by_contra hne
  exact hnone ⟨l, hl, hz, hne⟩

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CompactIntervalIntegral
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem compactInterval_integrable (f : ℝ → ℝ) (hf : Continuous f) (R : ℝ)
    (hsupport : ∀ x, R < |x| → f x = 0) : Integrable f := by
  apply hf.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := -R) (b := R))
  intro x hx
  apply abs_le.mp
  by_contra! h
  exact hx (hsupport x h)

theorem integral_norm_le_interval (f : ℝ → ℝ) {u v C : ℝ} (huv : u ≤ v)
    (hzero : ∀ x, x ∉ Set.Icc u v → f x = 0)
    (hbound : ∀ x ∈ Set.Icc u v, ‖f x‖ ≤ C) :
    (∫ x, ‖f x‖) ≤ C * (v - u) := by
  have hi : Integrable ((Set.Icc u v).indicator (fun _ : ℝ => C)) :=
    (integrableOn_const (by simp : volume (Set.Icc u v) ≠ ⊤)).integrable_indicator measurableSet_Icc
  have hb : ∀ x, ‖f x‖ ≤ (Set.Icc u v).indicator (fun _ : ℝ => C) x := by
    intro x
    by_cases hx : x ∈ Set.Icc u v
    · simpa only [Set.indicator_of_mem hx] using hbound x hx
    · simp only [hzero x hx, norm_zero, Set.indicator_of_notMem hx, le_refl]
  calc
    _ ≤ ∫ x, (Set.Icc u v).indicator (fun _ : ℝ => C) x :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => norm_nonneg (f x))) hi
        (Filter.Eventually.of_forall hb)
    _ = C * (v - u) := by
      rw [integral_indicator_const C measurableSet_Icc, Real.volume_real_Icc_of_le huv, smul_eq_mul]
      ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanBisectorNull
namespace OAI

section

namespace Erdos3

open MeasureTheory

theorem linear_levelset_measure_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (f : E →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) : μ {x : E | f x = c} = 0 := by
  let S : AffineSubspace ℝ E := (affineSpan ℝ ({c} : Set ℝ)).comap f.toAffineMap
  have hS : (S : Set E) = {x : E | f x = c} := by
    ext x
    simp [S]
  have hproper : S ≠ ⊤ := by
    intro he
    have hall : ∀ x : E, f x = c := by
      intro x
      have hx : x ∈ S := by rw [he]; trivial
      change x ∈ (S : Set E) at hx
      simpa only [hS, Set.mem_ofPred_eq] using hx
    have hc : c = 0 := by simpa using (hall 0).symm
    apply hf
    ext x
    simpa only [hc, LinearMap.zero_apply] using hall x
  rw [← hS]
  exact μ.addHaar_affineSubspace S hproper

theorem euclidean_bisector_measure_zero {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ] (a b : E) (hab : a ≠ b) :
    μ {x : E | ‖x - a‖ = ‖x - b‖} = 0 := by
  let f : E →ₗ[ℝ] ℝ := (innerSL ℝ (b - a)).toLinearMap
  have hf : f ≠ 0 := by
    intro he
    have hz : inner ℝ (b - a) (b - a) = 0 := by
      simpa only [f, ContinuousLinearMap.coe_coe, innerSL_apply_apply,
        LinearMap.zero_apply] using LinearMap.congr_fun he (b - a)
    exact hab (sub_eq_zero.mp ((inner_self_eq_zero).mp hz)).symm
  apply measure_mono_null (t := {x : E | f x = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2})
  · intro x hx
    change inner ℝ (b - a) x = (‖b‖ ^ 2 - ‖a‖ ^ 2) / 2
    rw [inner_sub_left, real_inner_comm x b, real_inner_comm x a]
    have he : ‖x - a‖ ^ 2 = ‖x - b‖ ^ 2 := congrArg (fun t : ℝ => t ^ 2) hx
    rw [norm_sub_sq_real, norm_sub_sq_real] at he
    linarith
  · exact linear_levelset_measure_zero μ f hf _

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteReciprocalTenthTail
namespace OAI

section

namespace Erdos3

theorem one_sub_sum_le_positive_prod {ι : Type*} (S : Finset ι) (f e : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) (he : ∀ i ∈ S, e i ∈ Set.Icc (0 : ℝ) 1)
    (hlower : ∀ i ∈ S, 1 - e i ≤ f i) :
    1 - ∑ i ∈ S, e i ≤ ∏ i ∈ S, f i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have heS := fun i hi => he i (Finset.mem_insert_of_mem hi)
    have hlS := fun i hi => hlower i (Finset.mem_insert_of_mem hi)
    have hea := he a (Finset.mem_insert_self _ _)
    have hs := Finset.sum_nonneg (fun i hi => (heS i hi).1)
    have h₁ := mul_le_mul_of_nonneg_left (ih hfS heS hlS) (sub_nonneg.mpr hea.2)
    have h₂ := mul_le_mul_of_nonneg_right (hlower a (Finset.mem_insert_self _ _))
      (Finset.prod_nonneg hfS)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    nlinarith [mul_nonneg hea.1 hs]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedIntervalWindow
namespace OAI

section

namespace Erdos3

open MeasureTheory Set

noncomputable def intervalWindow (a b : ℝ) : ℝ → ℝ :=
  (Ioc a b).indicator (fun _ => 1)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def normalizedIntervalWindow (ℓ x t : ℝ) : ℝ :=
  intervalWindow x (x + ℓ) t / ℓ

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelMixtureControl
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def kernelAverage {X T : Type*} [MeasurableSpace T]
    (μ : Measure T) (K : X → T → ℝ) (g : T → ℝ) (x : X) : ℝ := ∫ t, K x t * g t ∂μ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FiniteSupportTranslation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem translation_difference_zero_off {G : Type*} [AddCommGroup G] [DecidableEq G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (v x : G)
    (hx : x ∉ S ∪ S.image (fun y => y + v)) : w (x - v) - w x = 0 := by
  have hxS : x ∉ S := fun h => hx (Finset.mem_union_left _ h)
  have hyS : x - v ∉ S := by
    intro h
    apply hx
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x - v, h, sub_add_cancel x v⟩)
  rw [hw _ hyS, hw _ hxS, sub_self]

theorem finiteSupport_translation_l1_bound {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (v : G)
    {B : ℝ} (hB : 0 ≤ B) (hstep : ∀ x, |w (x - v) - w x| ≤ B) :
    (∑' x, |w (x - v) - w x|) ≤ 2 * (S.card : ℝ) * B := by
  classical
  let U := S ∪ S.image (fun y => y + v)
  have hz (x : G) (hx : x ∉ U) : |w (x - v) - w x| = 0 := by
    rw [translation_difference_zero_off w S hw v x hx, abs_zero]
  have hc : (U.card : ℝ) ≤ 2 * (S.card : ℝ) := by
    have hn : U.card ≤ S.card + S.card :=
      (Finset.card_union_le S (S.image (fun y => y + v))).trans
        (Nat.add_le_add_left Finset.card_image_le _)
    exact_mod_cast (show U.card ≤ 2 * S.card by omega)
  calc
    (∑' x, |w (x - v) - w x|) = ∑ x ∈ U, |w (x - v) - w x| :=
      (hasSum_sum_of_ne_finset_zero hz).tsum_eq
    _ ≤ ∑ _x ∈ U, B := Finset.sum_le_sum (fun x _ => hstep x)
    _ = (U.card : ℝ) * B := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hB

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LocalAverageAmplitude
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem finite_weighted_test_summable {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (f : X → ℂ) : Summable (fun x => (w x : ℂ) * f x) := by
  apply (hasSum_sum_of_ne_finset_zero (s := S) _).summable
  intro x hx
  simp only [hw x hx, Complex.ofReal_zero, zero_mul]

theorem finite_weighted_test_norm_le {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) (f : X → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ ∑' x, |w x| := by
  have hs : Summable (fun x => |w x|) :=
    (hasSum_sum_of_ne_finset_zero (s := S) (fun x hx => by rw [hw x hx, abs_zero])).summable
  apply tsum_of_norm_bounded hs.hasSum
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (hf x) (abs_nonneg _)).trans_eq (mul_one _)

theorem finite_weighted_translation_test_le {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : G) :
    ‖(∑' x, (w x : ℂ) * f (x + v)) - ∑' x, (w x : ℂ) * f x‖ ≤
      ∑' x, |w (x - v) - w x| := by
  classical
  have hshift (x : G) (hx : x ∉ S.image (fun y => y + v)) : w (x - v) = 0 := by
    apply hw
    intro hy
    exact hx (Finset.mem_image.mpr ⟨x - v, hy, sub_add_cancel x v⟩)
  have hleft : (∑' x, (w x : ℂ) * f (x + v)) = ∑' x, (w (x - v) : ℂ) * f x := by
    simpa using (Equiv.addRight v).tsum_eq (fun x => (w (x - v) : ℂ) * f x)
  have he : (∑' x, (w x : ℂ) * f (x + v)) - ∑' x, (w x : ℂ) * f x =
      ∑' x, ((w (x - v) - w x : ℝ) : ℂ) * f x := by
    rw [hleft, ← (finite_weighted_test_summable _ _ hshift f).tsum_sub
      (finite_weighted_test_summable w S hw f)]
    apply tsum_congr
    intro x
    rw [Complex.ofReal_sub, sub_mul]
  rw [he]
  exact finite_weighted_test_norm_le _ (S ∪ S.image (fun y => y + v))
    (translation_difference_zero_off w S hw v) f hf

theorem normalized_finite_translation_test_le {G : Type*} [AddCommGroup G]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (f : G → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1) (v : G) {Z : ℝ} (hZ : 0 < Z) :
    ‖(∑' x, ((w x / Z : ℝ) : ℂ) * f (x + v)) -
      ∑' x, ((w x / Z : ℝ) : ℂ) * f x‖ ≤ (∑' x, |w (x - v) - w x|) / Z := by
  have h := finite_weighted_translation_test_le (fun x => w x / Z) S
    (fun x hx => by rw [hw x hx, zero_div]) f hf v
  simpa only [← sub_div, abs_div, abs_of_pos hZ, tsum_div_const] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem finite_weighted_expect_comm {G X : Type*} [Fintype X]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0) (F : X → G → ℂ) :
    (𝔼 u, ∑' x, (w x : ℂ) * F u x) = ∑' x, (w x : ℂ) * (𝔼 u, F u x) := by
  have ht (f : G → ℂ) : (∑' x, (w x : ℂ) * f x) = ∑ x ∈ S, (w x : ℂ) * f x := by
    apply (hasSum_sum_of_ne_finset_zero (s := S) _).tsum_eq
    intro x hx
    simp only [hw x hx, Complex.ofReal_zero, zero_mul]
  simp_rw [ht]
  rw [Finset.expect_sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  exact (Finset.mul_expect _ _ _).symm

theorem finite_probability_test_norm_le {G : Type*}
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∑' x, w x) = 1)
    (f : G → ℂ) {B : ℝ} (hf : ∀ x, ‖f x‖ ≤ B) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ B := by
  have hs : Summable w := (hasSum_sum_of_ne_finset_zero hw).summable
  have hm : HasSum (fun x => w x * B) B := by
    simpa only [hmass, one_mul] using hs.hasSum.mul_right B
  apply tsum_of_norm_bounded hm
  intro x
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw0 x)]
  exact mul_le_mul_of_nonneg_left (hf x) (hw0 x)

theorem finite_probability_shift_transfer {G X : Type*} [AddCommGroup G]
    [Fintype X] [Nonempty X]
    (w : G → ℝ) (S : Finset G) (hw : ∀ x ∉ S, w x = 0)
    (hw0 : ∀ x, 0 ≤ w x) (hmass : (∑' x, w x) = 1)
    (shift : X → G) (f : G → ℂ) {ε B : ℝ}
    (hmove : ∀ u, ‖(∑' x, (w x : ℂ) * f (x + shift u)) -
      ∑' x, (w x : ℂ) * f x‖ ≤ ε)
    (hlocal : ∀ x, ‖𝔼 u, f (x + shift u)‖ ≤ B) :
    ‖∑' x, (w x : ℂ) * f x‖ ≤ ε + B := by
  let base := ∑' x, (w x : ℂ) * f x
  let mean := 𝔼 u, ∑' x, (w x : ℂ) * f (x + shift u)
  have he : mean - base = 𝔼 u, ((∑' x, (w x : ℂ) * f (x + shift u)) - base) := by
    rw [Finset.expect_sub_distrib, Fintype.expect_const]
  have hdiff : ‖mean - base‖ ≤ ε := by
    rw [he]
    apply (RCLike.norm_expect_le (K := ℂ)).trans
    exact (Finset.expect_le_expect (fun u _ => hmove u)).trans_eq (Fintype.expect_const ε)
  have hmean : ‖mean‖ ≤ B := by
    dsimp only [mean]
    rw [finite_weighted_expect_comm w S hw]
    exact finite_probability_test_norm_le w S hw hw0 hmass _ hlocal
  calc
    ‖base‖ = ‖(base - mean) + mean‖ := by rw [sub_add_cancel]
    _ ≤ ‖base - mean‖ + ‖mean‖ := norm_add_le _ _
    _ ≤ ε + B := add_le_add (by simpa only [norm_sub_rev] using hdiff) hmean

end Erdos3

end

section

namespace Erdos3
open scoped BigOperators

theorem norm_local_average_amplitude_le {G X : Type*} [Fintype X] [Nonempty X]
    (point : X → G) (f amplitude : G → ℂ) (base : G)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hamp : ‖amplitude base‖ ≤ 1)
    {η β : ℝ} (hvariation : ∀ u, ‖amplitude (point u) - amplitude base‖ ≤ η)
    (hlocal : ‖𝔼 u, f (point u)‖ ≤ β) :
    ‖𝔼 u, amplitude (point u) * f (point u)‖ ≤ η + β := by
  have he : (𝔼 u, amplitude (point u) * f (point u)) =
      (𝔼 u, (amplitude (point u) - amplitude base) * f (point u)) +
        amplitude base * (𝔼 u, f (point u)) := by
    rw [Finset.mul_expect, ← Finset.expect_add_distrib]
    apply Finset.expect_congr rfl
    intro u _
    ring
  rw [he]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · apply (RCLike.norm_expect_le (K := ℂ)).trans
    apply (Finset.expect_le_expect (fun u _ => ?_)).trans_eq (Fintype.expect_const η)
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_left (hf _) (norm_nonneg _)).trans (by simpa using hvariation u)
  · rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hamp (norm_nonneg _)).trans (by simpa using hlocal)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerFiberCount
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem card_integer_set_le_diameter_add_one (A : Finset ℤ) {L : ℝ} (hL : 0 ≤ L)
    (hdiam : ∀ x ∈ A, ∀ y ∈ A, |(x : ℝ) - y| ≤ L) :
    (A.card : ℝ) ≤ L + 1 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp only [Finset.card_empty, Nat.cast_zero]
    linarith
  have hsub : A ⊆ Finset.Icc (A.min' hA) (A.max' hA) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨A.min'_le x hx, A.le_max' x hx⟩
  have hcard : (A.card : ℝ) ≤ (A.max' hA : ℝ) + 1 - A.min' hA := by
    have hc := Finset.card_le_card hsub
    have hi := Int.card_Icc_of_le (A.min' hA) (A.max' hA)
      (le_trans (A.min'_le_max' hA) (by omega))
    have hc' : (A.card : ℤ) ≤ A.max' hA + 1 - A.min' hA := by
      exact_mod_cast hi ▸ (show (A.card : ℤ) ≤ (Finset.Icc (A.min' hA) (A.max' hA)).card by
        exact_mod_cast hc)
    exact_mod_cast hc'
  have hd := (abs_le.mp (hdiam _ (A.max'_mem hA) _ (A.min'_mem hA))).2
  linarith

theorem count_integer_phase_fibers (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η : ℝ} (hH : 0 ≤ H) (hθ : 0 < θ) (hη : 0 ≤ η)
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    (D.card : ℝ) ≤ (2 * H * θ + 2 * η + 1) * (2 * η / θ + 1) := by
  have hm (h : ℤ) (hh : h ∈ D) : |(m h : ℝ)| ≤ H * θ + η := by
    have ha := abs_le.mp (hD h hh)
    have he := abs_le.mp (hclose h hh)
    have hlo := mul_le_mul_of_nonneg_right ha.1 hθ.le
    have hhi := mul_le_mul_of_nonneg_right ha.2 hθ.le
    rw [abs_le]
    constructor <;> nlinarith only [hlo, hhi, he.1, he.2]
  have himage : ((D.image m).card : ℝ) ≤ 2 * H * θ + 2 * η + 1 := by
    apply card_integer_set_le_diameter_add_one _ (by positivity)
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have hx' := abs_le.mp (hm x hx)
    have hy' := abs_le.mp (hm y hy)
    rw [abs_le]
    constructor <;> linarith
  have hfiber (a : ℤ) : ((D.filter (fun h => m h = a)).card : ℝ) ≤ 2 * η / θ + 1 := by
    apply card_integer_set_le_diameter_add_one _ (by positivity)
    intro x hx y hy
    obtain ⟨hx, hmx⟩ := Finset.mem_filter.mp hx
    obtain ⟨hy, hmy⟩ := Finset.mem_filter.mp hy
    have he₁ := abs_le.mp (hclose x hx)
    have he₂ := abs_le.mp (hclose y hy)
    rw [hmx] at he₁
    rw [hmy] at he₂
    apply (le_div_iff₀ hθ).mpr
    rw [← abs_of_pos hθ, ← abs_mul, abs_le]
    constructor <;> nlinarith only [he₁.1, he₁.2, he₂.1, he₂.2]
  calc
    (D.card : ℝ) = ∑ a ∈ D.image m, ((D.filter (fun h => m h = a)).card : ℝ) := by
      exact_mod_cast Finset.card_eq_sum_card_fiberwise (fun x hx => Finset.mem_image.mpr ⟨x, hx, rfl⟩)
    _ ≤ ∑ _a ∈ D.image m, (2 * η / θ + 1) := Finset.sum_le_sum (fun a _ => hfiber a)
    _ = ((D.image m).card : ℝ) * (2 * η / θ + 1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 * H * θ + 2 * η + 1) * (2 * η / θ + 1) :=
      mul_le_mul_of_nonneg_right himage (by positivity)

theorem count_integer_phase_fibers_abs (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η : ℝ} (hH : 0 ≤ H) (hθ : θ ≠ 0) (hη : 0 ≤ η)
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    (D.card : ℝ) ≤ (2 * H * |θ| + 2 * η + 1) * (2 * η / |θ| + 1) := by
  rcases lt_or_gt_of_ne hθ with ht | ht
  · have he : ∀ h ∈ D, |(h : ℝ) * (-θ) - ((-m h : ℤ) : ℝ)| ≤ η := by
      intro h hh
      simpa only [Int.cast_neg, mul_neg, neg_sub_neg, abs_sub_comm] using hclose h hh
    simpa only [abs_of_neg ht] using count_integer_phase_fibers D (fun h => -m h)
      hH (neg_pos.mpr ht) hη hD he
  · simpa only [abs_of_pos ht] using count_integer_phase_fibers D m hH ht hη hD hclose

theorem small_linear_phase_of_many_near_integers (D : Finset ℤ) (m : ℤ → ℤ)
    {H θ η ρ : ℝ} (hH : 0 < H) (hρ : 0 < ρ) (hη : 0 ≤ η) (hηone : η ≤ 1)
    (hsmall : 16 * η ≤ ρ) (hθsmall : |θ| ≤ 2 * η)
    (hsize : ρ * H ≤ (D.card : ℝ))
    (hD : ∀ h ∈ D, |(h : ℝ)| ≤ H)
    (hclose : ∀ h ∈ D, |(h : ℝ) * θ - m h| ≤ η) :
    |θ| ≤ 24 * η / (ρ * H) := by
  by_cases ht : θ = 0
  · rw [ht, abs_zero]
    positivity
  have hθ : 0 < |θ| := abs_pos.mpr ht
  have hc := count_integer_phase_fibers_abs D m hH.le ht hη hD hclose
  have hc' : ρ * H ≤ (2 * H * |θ| + 3) * (2 * η / |θ| + 1) := by
    apply hsize.trans (hc.trans _)
    apply mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have hp := mul_le_mul_of_nonneg_right hc' hθ.le
  have hid : ((2 * H * |θ| + 3) * (2 * η / |θ| + 1)) * |θ| =
      4 * H * |θ| * η + 2 * H * |θ| ^ 2 + 6 * η + 3 * |θ| := by
    field_simp
    ring
  rw [hid] at hp
  have hsquare := mul_le_mul_of_nonneg_left hθsmall
    (show 0 ≤ 2 * H * |θ| by positivity)
  have hcost := mul_le_mul_of_nonneg_right hsmall
    (show 0 ≤ H * |θ| by positivity)
  apply (le_div_iff₀ (mul_pos hρ hH)).mpr
  nlinarith only [hp, hsquare, hcost, hθsmall]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PartialComplexScaledQuadrature
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def sampledWeightIndices (a S R : ℝ) : Finset ℤ :=
  Finset.Icc ⌈a - S * R⌉ ⌊a + S * R⌋

noncomputable def sampledWeight (ψ : ℝ → ℝ) (a S : ℝ) (k : ℤ) : ℝ :=
  ψ (((k : ℝ) - a) / S)

noncomputable def sampledWeightSum (ψ : ℝ → ℝ) (a S R : ℝ) : ℝ :=
  ∑ k ∈ sampledWeightIndices a S R, sampledWeight ψ a S k

noncomputable def sampledWeightHistogram (ψ : ℝ → ℝ) (a S R : ℝ) : ℝ → ℝ :=
  finiteLatticeHistogram (sampledWeightIndices a S R) (sampledWeight ψ a S) a S

theorem sampledWeight_zero_off_indices (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (k : ℤ)
    (hk : k ∉ sampledWeightIndices a S R) : sampledWeight ψ a S k = 0 := by
  by_contra hn
  have hb : |((k : ℝ) - a) / S| ≤ R := by
    by_contra! hb
    exact hn (hsupport _ hb)
  obtain ⟨hlo, hhi⟩ := abs_le.mp hb
  have hlo' := (le_div_iff₀ hS).mp hlo
  have hhi' := (div_le_iff₀ hS).mp hhi
  apply hk
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem sampledWeightSum_eq_tsum (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) :
    sampledWeightSum ψ a S R = ∑' k : ℤ, ψ (((k : ℝ) - a) / S) :=
  (hasSum_sum_of_ne_finset_zero (sampledWeight_zero_off_indices ψ hS hsupport)).tsum_eq.symm

theorem sampledWeightHistogram_eq (ψ : ℝ → ℝ) {a S R : ℝ} (hS : 0 < S)
    (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    sampledWeightHistogram ψ a S R x = ψ (latticeSample a S x) :=
  finiteLatticeHistogram_eq_floor _ _ (sampledWeight_zero_off_indices ψ hS hsupport) a hS x

theorem sampledWeightHistogram_integrable (ψ : ℝ → ℝ) (a S R : ℝ) :
    Integrable (sampledWeightHistogram ψ a S R) := finiteLatticeHistogram_integrable _ _ _ _

theorem sampledWeightHistogram_integral (ψ : ℝ → ℝ) (a : ℝ) {S : ℝ} (hS : 0 < S) (R : ℝ) :
    (∫ x, sampledWeightHistogram ψ a S R x) = sampledWeightSum ψ a S R / S :=
  finiteLatticeHistogram_integral _ _ a hS

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def finiteRectangularHistogram (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S x : J → ℝ) : ℝ :=
  ∑ k ∈ s, (rectangularLatticeCell a S k).indicator (fun _ => w k) x

theorem rectangularLatticeCell_indicator_integrable (a S : J → ℝ) (k : J → ℤ) (v : ℝ) :
    Integrable ((rectangularLatticeCell a S k).indicator (fun _ => v)) :=
  (integrableOn_const (rectangularLatticeCell_volume_ne_top a S k)).integrable_indicator
    (rectangularLatticeCell_measurable a S k)

theorem finiteRectangularHistogram_integrable (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S : J → ℝ) : Integrable (finiteRectangularHistogram s w a S) := by
  apply integrable_finsetSum
  intro k _
  exact rectangularLatticeCell_indicator_integrable a S k (w k)

theorem finiteRectangularHistogram_integral (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (a S : J → ℝ) (hS : ∀ j, 0 < S j) :
    (∫ x, finiteRectangularHistogram s w a S x) = (∑ k ∈ s, w k) / (∏ j, S j) := by
  unfold finiteRectangularHistogram
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ (rectangularLatticeCell_measurable a S _),
      rectangularLatticeCell_volume a S hS, smul_eq_mul]
    rw [← Finset.mul_sum]
    ring
  · intro k _
    exact rectangularLatticeCell_indicator_integrable a S k (w k)

omit [Fintype J] in
theorem finiteRectangularHistogram_eq_round (s : Finset (J → ℤ)) (w : (J → ℤ) → ℝ)
    (hw : ∀ k, k ∉ s → w k = 0) (a S : J → ℝ) (hS : ∀ j, 0 < S j) (x : J → ℝ) :
    finiteRectangularHistogram s w a S x = w (rectangularLatticeRound a S x) := by
  classical
  unfold finiteRectangularHistogram
  rw [Finset.sum_eq_single (rectangularLatticeRound a S x)]
  · exact Set.indicator_of_mem ((rectangularLatticeCell_iff a S hS x _).mpr rfl) _
  · intro k _ hne
    apply Set.indicator_of_notMem
    intro hk
    exact hne ((rectangularLatticeCell_iff a S hS x k).mp hk).symm
  · intro hn
    rw [hw _ hn]
    simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularWeightIndices (a S : J → ℝ) (R : ℝ) : Finset (J → ℤ) := by
  classical
  exact Fintype.piFinset fun j => sampledWeightIndices (a j) (S j) R

noncomputable def rectangularWeight (f : (J → ℝ) → ℝ) (a S : J → ℝ) (k : J → ℤ) : ℝ :=
  f (rectangularLatticePoint a S k)

noncomputable def rectangularWeightSum (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) : ℝ :=
  ∑ k ∈ rectangularWeightIndices a S R, rectangularWeight f a S k

noncomputable def rectangularWeightHistogram (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) :
    (J → ℝ) → ℝ :=
  finiteRectangularHistogram (rectangularWeightIndices a S R) (rectangularWeight f a S) a S

theorem rectangularWeight_zero_off_indices (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0)
    (k : J → ℤ) (hk : k ∉ rectangularWeightIndices a S R) : rectangularWeight f a S k = 0 := by
  classical
  by_contra hn
  have hb : ‖rectangularLatticePoint a S k‖ ≤ R := by
    by_contra! h
    exact hn (hsupport _ h)
  apply hk
  apply Fintype.mem_piFinset.mpr
  intro j
  have hj : |((k j : ℝ) - a j) / S j| ≤ R :=
    (norm_le_pi_norm (rectangularLatticePoint a S k) j).trans hb
  obtain ⟨hlo, hhi⟩ := abs_le.mp hj
  have hlo' := (le_div_iff₀ (hS j)).mp hlo
  have hhi' := (div_le_iff₀ (hS j)).mp hhi
  apply Finset.mem_Icc.mpr
  exact ⟨Int.ceil_le.mpr (by nlinarith), Int.le_floor.mpr (by nlinarith)⟩

theorem rectangularWeight_summable (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (rectangularWeight f a S) :=
  (hasSum_sum_of_ne_finset_zero (rectangularWeight_zero_off_indices f a S hS hsupport)).summable

theorem rectangularWeightSum_eq_tsum (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    rectangularWeightSum f a S R = ∑' k : J → ℤ, f (rectangularLatticePoint a S k) :=
  (hasSum_sum_of_ne_finset_zero (rectangularWeight_zero_off_indices f a S hS hsupport)).tsum_eq.symm

theorem rectangularWeightHistogram_eq (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) :
    rectangularWeightHistogram f a S R x = f (rectangularLatticeSample a S x) :=
  finiteRectangularHistogram_eq_round _ _ (rectangularWeight_zero_off_indices f a S hS hsupport)
    a S hS x

theorem rectangularWeightHistogram_integrable (f : (J → ℝ) → ℝ) (a S : J → ℝ) (R : ℝ) :
    Integrable (rectangularWeightHistogram f a S R) := finiteRectangularHistogram_integrable _ _ a S

theorem rectangularWeightHistogram_integral (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) (R : ℝ) :
    (∫ x, rectangularWeightHistogram f a S R x) = rectangularWeightSum f a S R / (∏ j, S j) :=
  finiteRectangularHistogram_integral _ _ a S hS

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

theorem rectangularWeightHistogram_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hδ : 0 ≤ δ) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) :
    ‖rectangularWeightHistogram f a S R x - f x‖ ≤ (L : ℝ) * δ := by
  rw [rectangularWeightHistogram_eq f a S hS hsupport]
  exact (hLip.norm_sub_le _ _).trans
    (mul_le_mul_of_nonneg_left (rectangularLatticeSample_error a S hS hδ hmesh x) L.coe_nonneg)

theorem rectangularWeightHistogram_zero_outside (f : (J → ℝ) → ℝ) (a S : J → ℝ)
    (hS : ∀ j, 0 < S j) (hmesh : ∀ j, 1 / S j ≤ 1) {R : ℝ}
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (x : J → ℝ) (hx : R + 1 < ‖x‖) :
    rectangularWeightHistogram f a S R x = 0 := by
  have he := rectangularLatticeSample_error a S hS zero_le_one hmesh x
  have ht : ‖x‖ ≤ ‖rectangularLatticeSample a S x‖ + ‖rectangularLatticeSample a S x - x‖ := by
    calc
      ‖x‖ = ‖rectangularLatticeSample a S x + (x - rectangularLatticeSample a S x)‖ := by
        congr 1
        abel
      _ ≤ ‖rectangularLatticeSample a S x‖ + ‖x - rectangularLatticeSample a S x‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev x (rectangularLatticeSample a S x)]
  rw [rectangularWeightHistogram_eq f a S hS hsupport]
  exact hsupport _ (by linarith)

theorem rectangularWeightHistogram_l1_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    (∫ x, ‖rectangularWeightHistogram f a S R x - f x‖) ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  have hz : ∀ x, R + 1 < ‖x‖ → rectangularWeightHistogram f a S R x - f x = 0 := by
    intro x hx
    rw [rectangularWeightHistogram_zero_outside f a S hS (fun j => (hmesh j).trans hδ1)
      hsupport x hx, hsupport x (by linarith), sub_self]
  have he := integral_norm_le_box (fun x => rectangularWeightHistogram f a S R x - f x)
    (R := R + 1) (C := (L : ℝ) * δ) (by linarith) hz
    (fun x _ => rectangularWeightHistogram_error f hLip a S hS hδ hmesh hsupport x)
  exact he.trans_eq (by rw [mul_add, mul_one]; ring)

theorem rectangularWeightSum_error (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |rectangularWeightSum f a S R / (∏ j, S j) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  rw [← rectangularWeightHistogram_integral f a S hS R,
    ← integral_sub (rectangularWeightHistogram_integrable f a S R)
      (compactBox_integrable f hLip.continuous R hsupport)]
  exact (norm_integral_le_integral_norm _).trans
    (rectangularWeightHistogram_l1_error f hLip a S hS hR hδ hδ1 hmesh hsupport)

theorem rectangularLattice_quadrature (f : (J → ℝ) → ℝ) {L : ℝ≥0}
    (hLip : LipschitzWith L f) (a S : J → ℝ) (hS : ∀ j, 0 < S j)
    {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) (hmesh : ∀ j, 1 / S j ≤ δ)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    |(∑' k : J → ℤ, f (rectangularLatticePoint a S k)) / (∏ j, S j) - ∫ x, f x| ≤
      (2 * R + 2) ^ Fintype.card J * (L : ℝ) * δ := by
  rw [← rectangularWeightSum_eq_tsum f a S hS hsupport]
  exact rectangularWeightSum_error f hLip a S hS hR hδ hδ1 hmesh hsupport

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem sampledWeightIndices_mem_bound {a S R : ℝ} {k : ℤ}
    (hk : k ∈ sampledWeightIndices a S R) : |(k : ℝ) - a| ≤ S * R := by
  obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
  have hl := Int.ceil_le.mp hlo
  have hh := Int.le_floor.mp hhi
  rw [abs_le]
  constructor <;> linarith

theorem sampledWeightIndices_card_le (a S R : ℝ) (hS : 0 ≤ S) (hR : 0 ≤ R) :
    ((sampledWeightIndices a S R).card : ℝ) ≤ 2 * S * R + 1 := by
  apply card_integer_set_le_diameter_add_one _ (by positivity)
  intro x hx y hy
  have h := (abs_sub_le (x : ℝ) a y).trans
    (add_le_add (sampledWeightIndices_mem_bound hx)
      (by simpa only [abs_sub_comm] using sampledWeightIndices_mem_bound hy))
  linarith

theorem rectangularWeightIndices_card_le {I : Type*} [Fintype I]
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R) :
    ((rectangularWeightIndices a S R).card : ℝ) ≤
      (2 * R + 1) ^ Fintype.card I * ∏ i, S i := by
  have hi (i : I) : ((sampledWeightIndices (a i) (S i) R).card : ℝ) ≤ (2 * R + 1) * S i := by
    apply (sampledWeightIndices_card_le _ _ _ (zero_le_one.trans (hS i)) hR).trans
    nlinarith [hS i]
  calc
    ((rectangularWeightIndices a S R).card : ℝ) =
        ∏ i, ((sampledWeightIndices (a i) (S i) R).card : ℝ) := by
      simp [rectangularWeightIndices]
    _ ≤ ∏ i, ((2 * R + 1) * S i) :=
      Finset.prod_le_prod (fun i _ => Nat.cast_nonneg _) (fun i _ => hi i)
    _ = _ := by simp [Finset.prod_mul_distrib]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

omit [Fintype J] in
theorem rectangularLatticePoint_scaled (c T : J → ℝ) {m : ℝ} (hm : m ≠ 0) (z : J → ℤ) :
    rectangularLatticePoint (fun j => -c j / m) (fun j => T j / m) z =
      fun j => (c j + m * z j) / T j := by
  funext j
  unfold rectangularLatticePoint
  field_simp
  ring

theorem scaledRectangularWeight_summable (f : (J → ℝ) → ℝ) (c T : J → ℝ)
    {m : ℝ} (hm : 0 < m) (hT : ∀ j, 0 < T j)
    {R : ℝ} (hsupport : ∀ x, R < ‖x‖ → f x = 0) :
    Summable (fun z : J → ℤ => f (fun j => (c j + m * z j) / T j)) := by
  have h := rectangularWeight_summable f (fun j => -c j / m) (fun j => T j / m)
    (fun j => div_pos (hT j) hm) hsupport
  unfold rectangularWeight at h
  simpa only [rectangularLatticePoint_scaled c T hm.ne'] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem rectangularLatticePoint_zero_origin {I : Type*} [Fintype I]
    (S : I → ℝ) (k : I → ℤ) :
    rectangularLatticePoint 0 S k = fun i => (k i : ℝ) / S i := by
  funext i
  simp [rectangularLatticePoint]

theorem rectangularLatticePoint_sub_displacement {I : Type*} [Fintype I]
    (a S : I → ℝ) (k v : I → ℤ) :
    rectangularLatticePoint a S (k - v) - rectangularLatticePoint a S k =
      -rectangularLatticePoint 0 S v := by
  funext i
  simp only [rectangularLatticePoint, Pi.sub_apply, Pi.neg_apply, Pi.zero_apply, Int.cast_sub]
  ring

theorem rectangularWeight_translation_pointwise {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (v k : I → ℤ) :
    |rectangularWeight f a S (k - v) - rectangularWeight f a S k| ≤
      L * ‖rectangularLatticePoint 0 S v‖ := by
  have h := hf.norm_sub_le (rectangularLatticePoint a S (k - v)) (rectangularLatticePoint a S k)
  rw [rectangularLatticePoint_sub_displacement, norm_neg] at h
  exact h

theorem rectangularWeight_translation_l1 {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) (v : I → ℤ) :
    (∑' k, |rectangularWeight f a S (k - v) - rectangularWeight f a S k|) ≤
      2 * ((2 * R + 1) ^ Fintype.card I * ∏ i, S i) *
        (L * ‖rectangularLatticePoint 0 S v‖) := by
  have h := finiteSupport_translation_l1_bound (rectangularWeight f a S)
    (rectangularWeightIndices a S R)
    (rectangularWeight_zero_off_indices f a S (fun i => zero_lt_one.trans_le (hS i)) hsupport)
    v (mul_nonneg L.coe_nonneg (norm_nonneg _)) (rectangularWeight_translation_pointwise f hf a S v)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (rectangularWeightIndices_card_le a S hS hR) (by norm_num))
    (mul_nonneg L.coe_nonneg (norm_nonneg _)))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal BigOperators

variable {J : Type*} [Fintype J]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalized_rectangular_translation_test_le {I : Type*} [Fintype I]
    (f : (I → ℝ) → ℝ) {L : ℝ≥0} (hf : LipschitzWith L f)
    (a S : I → ℝ) (hS : ∀ i, 1 ≤ S i) {R : ℝ} (hR : 0 ≤ R)
    (hsupport : ∀ x, R < ‖x‖ → f x = 0) {Z : ℝ}
    (hmass : (∏ i, S i) / 2 ≤ Z) (φ : (I → ℤ) → ℂ) (hφ : ∀ x, ‖φ x‖ ≤ 1)
    (v : I → ℤ) :
    ‖(∑' x, ((rectangularWeight f a S x / Z : ℝ) : ℂ) * φ (x + v)) -
      ∑' x, ((rectangularWeight f a S x / Z : ℝ) : ℂ) * φ x‖ ≤
        4 * (2 * R + 1) ^ Fintype.card I * (L * ‖rectangularLatticePoint 0 S v‖) := by
  have hprod : 0 < ∏ i, S i := Finset.prod_pos (fun i _ => zero_lt_one.trans_le (hS i))
  have hZ : 0 < Z := (div_pos hprod (by norm_num)).trans_le hmass
  have hratio : (∏ i, S i) / Z ≤ 2 := (div_le_iff₀ hZ).mpr (by linarith)
  apply (normalized_finite_translation_test_le (rectangularWeight f a S)
    (rectangularWeightIndices a S R)
    (rectangularWeight_zero_off_indices f a S (fun i => zero_lt_one.trans_le (hS i)) hsupport)
    φ hφ v hZ).trans
  apply (div_le_div_of_nonneg_right (rectangularWeight_translation_l1 f hf a S hS hR hsupport v) hZ.le).trans
  calc
    (2 * ((2 * R + 1) ^ Fintype.card I * ∏ i, S i) *
        (L * ‖rectangularLatticePoint 0 S v‖)) / Z =
      (2 * (2 * R + 1) ^ Fintype.card I) * ((∏ i, S i) / Z) *
        (L * ‖rectangularLatticePoint 0 S v‖) := by ring
    _ ≤ (2 * (2 * R + 1) ^ Fintype.card I) * 2 *
        (L * ‖rectangularLatticePoint 0 S v‖) := by
      apply mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hratio (by positivity)) (by positivity)
    _ = _ := by ring

end Erdos3

end

section

namespace Erdos3
open MeasureTheory
open scoped NNReal BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CompactLatticeApproximation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem sampledWeightHistogram_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hS : 0 < S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) :
    ‖sampledWeightHistogram ψ a S R x - ψ x‖ ≤ (L : ℝ) / S := by
  rw [sampledWeightHistogram_eq ψ hS hsupport]
  calc
    _ ≤ (L : ℝ) * ‖latticeSample a S x - x‖ := hLip.norm_sub_le _ _
    _ ≤ (L : ℝ) * (1 / S) :=
      mul_le_mul_of_nonneg_left (latticeSample_error hS x) L.coe_nonneg
    _ = _ := by ring

theorem sampledWeightHistogram_zero_outside (ψ : ℝ → ℝ) {a S R : ℝ}
    (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) (x : ℝ) (hx : R + 1 < |x|) :
    sampledWeightHistogram ψ a S R x = 0 := by
  have hSp : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have he : |latticeSample a S x - x| ≤ 1 :=
    (latticeSample_error hSp x).trans ((div_le_one hSp).mpr hS)
  have ht : |x| ≤ |latticeSample a S x| + |latticeSample a S x - x| := by
    have h := abs_sub_le x (latticeSample a S x) 0
    simpa only [sub_zero, abs_sub_comm x (latticeSample a S x), add_comm] using h
  rw [sampledWeightHistogram_eq ψ hSp hsupport]
  exact hsupport _ (by linarith)

theorem sampledWeightHistogram_l1_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) :
    (∫ x, ‖sampledWeightHistogram ψ a S R x - ψ x‖) ≤ (2 * R + 2) * (L : ℝ) / S := by
  have hz : ∀ x, x ∉ Set.Icc (-(R + 1)) (R + 1) →
      sampledWeightHistogram ψ a S R x - ψ x = 0 := by
    intro x hx
    have hx' : R + 1 < |x| := lt_of_not_ge (fun h => hx (abs_le.mp h))
    rw [sampledWeightHistogram_zero_outside ψ hS hsupport x hx', hsupport x (by linarith), sub_self]
  have he := integral_norm_le_interval (fun x => sampledWeightHistogram ψ a S R x - ψ x)
    (u := -(R + 1)) (v := R + 1) (C := (L : ℝ) / S) (by linarith)
    hz (fun x _ => sampledWeightHistogram_error ψ hLip
      (lt_of_lt_of_le zero_lt_one hS) hsupport x)
  exact he.trans_eq (by ring)

theorem sampledWeightSum_error (ψ : ℝ → ℝ) {L : ℝ≥0} (hLip : LipschitzWith L ψ)
    {a S R : ℝ} (hR : 0 ≤ R) (hS : 1 ≤ S) (hsupport : ∀ x, R < |x| → ψ x = 0) :
    |sampledWeightSum ψ a S R / S - ∫ x, ψ x| ≤ (2 * R + 2) * (L : ℝ) / S := by
  rw [← sampledWeightHistogram_integral ψ a (lt_of_lt_of_le zero_lt_one hS) R,
    ← integral_sub (sampledWeightHistogram_integrable ψ a S R)
      (compactInterval_integrable ψ hLip.continuous R hsupport)]
  exact (norm_integral_le_integral_norm _).trans
    (sampledWeightHistogram_l1_error ψ hLip hR hS hsupport)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.BinaryDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def binaryDensity {X Y : Type*} (f : X → ℝ) (g : Y → ℝ) (p : X × Y) : ℝ :=
  f p.1 * g p.2

theorem binaryDensity_measurable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → ℝ} {g : Y → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (binaryDensity f g) := (hf.comp measurable_fst).mul (hg.comp measurable_snd)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.SampledWeightCellLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def independentCoordinateDensity (f : ι → ℝ → ℝ) (x : ι → ℝ) : ℝ :=
  ∏ i, f i (x i)

theorem independentCoordinateDensity_integrable (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) :
    Integrable (independentCoordinateDensity f) := Integrable.fintype_prod hf

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def realDensityMeasure {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) : Measure X := μ.withDensity (fun x => ENNReal.ofReal (f x))

theorem realDensityMeasure_apply {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) {s : Set X} (hs : MeasurableSet s) :
    realDensityMeasure μ f s = ENNReal.ofReal (∫ x in s, f x ∂μ) := by
  rw [realDensityMeasure, withDensity_apply _ hs]
  exact (ofReal_integral_eq_lintegral_ofReal hf.integrableOn (Filter.Eventually.of_forall hf0)).symm

theorem realDensityMeasure_probability {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    IsProbabilityMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ, Measure.restrict_univ,
    hmass, ENNReal.ofReal_one]

theorem binaryDensity_measure {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : X → ℝ) (g : Y → ℝ) (hf : Measurable f) (hg : Measurable g) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure μ f).prod (realDensityMeasure ν g) =
      realDensityMeasure (μ.prod ν) (binaryDensity f g) := by
  unfold realDensityMeasure
  rw [prod_withDensity hf.ennreal_ofReal hg.ennreal_ofReal]
  congr 1
  funext p
  exact (ENNReal.ofReal_mul (hf0 p.1)).symm

theorem independentCoordinateDensity_measure {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℝ) (hf : ∀ i, Integrable (f i)) (hf0 : ∀ i x, 0 ≤ f i x)
    (hmass : ∀ i, (∫ x, f i x) = 1) :
    Measure.pi (fun i => realDensityMeasure volume (f i)) =
      realDensityMeasure volume (independentCoordinateDensity f) := by
  let : ∀ i, IsProbabilityMeasure (realDensityMeasure volume (f i)) :=
    fun i => realDensityMeasure_probability volume (f i) (hf i) (hf0 i) (hmass i)
  apply Measure.pi_eq
  intro s hs
  have hprod0 (x : ι → ℝ) : 0 ≤ independentCoordinateDensity f x :=
    Finset.prod_nonneg (fun i _ => hf0 i (x i))
  rw [realDensityMeasure_apply volume _ (independentCoordinateDensity_integrable f hf) hprod0
    (MeasurableSet.univ_pi hs)]
  have hint : (∫ x in Set.univ.pi s, independentCoordinateDensity f x) =
      ∏ i, ∫ x in s i, f i x := by
    change (∫ x, (∏ i, f i (x i)) ∂(Measure.pi (fun _ : ι => (volume : Measure ℝ))).restrict
      (Set.univ.pi s)) = _
    rw [Measure.restrict_pi_pi]
    exact integral_fintype_prod_eq_prod (fun i x => f i x)
  rw [hint, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hf0 i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (realDensityMeasure_apply volume (f i) (hf i) (hf0 i) (hs i)).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ENNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxWindowAveraging
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def boxProbabilityWindow (ℓ x t : ι → ℝ) : ℝ :=
  ∏ i, normalizedIntervalWindow (ℓ i) (x i) (t i)

noncomputable def boxWindowTranslationBound (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i) : ℝ≥0 :=
  ⟨∑ i, 2 / ℓ i, Finset.sum_nonneg (fun i _ => div_nonneg (by norm_num) (hℓ i).le)⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InverseSqrtMoment
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def unitInverseSqrt (x : ℝ) : ℝ :=
  (Set.Ioc (0 : ℝ) 1).indicator (fun x => (Real.sqrt x)⁻¹) x

variable {ι : Type*} [Fintype ι]

noncomputable def unitBoxInverseSqrt (x : ι → ℝ) : ℝ := ∏ i, unitInverseSqrt (x i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MatrixSupInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_det_abs_le_row_bounds (A : Matrix ι ι ℝ) (H : ι → ℝ)
    (hA : ∀ i j, |A i j| ≤ H i) :
    |A.det| ≤ (Fintype.card ι).factorial * ∏ i, H i := by
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm ι, |((Equiv.Perm.sign σ : ℤ) : ℝ) * ∏ i, A (σ i) i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _σ : Equiv.Perm ι, ∏ i, H i := by
      apply Finset.sum_le_sum
      intro σ _
      have hsign : |((Equiv.Perm.sign σ : ℤ) : ℝ)| = 1 := by
        rw [← Int.cast_abs, Equiv.Perm.sign_abs, Int.cast_one]
      rw [abs_mul, hsign, one_mul, Finset.abs_prod]
      calc
        _ ≤ ∏ i, H (σ i) :=
          Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => hA (σ i) i)
        _ = ∏ i, H i := Equiv.prod_comp σ H
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, nsmul_eq_mul]

theorem matrix_det_abs_le_uniform_bound (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) :
    |A.det| ≤ (Fintype.card ι).factorial * H ^ Fintype.card ι := by
  simpa only [Finset.prod_const, Finset.card_univ] using
    matrix_det_abs_le_row_bounds A (fun _ => H) hA

theorem matrix_adjugate_entry_abs_le (A : Matrix ι ι ℝ) {H : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (i j : ι) :
    |A.adjugate i j| ≤ (Fintype.card ι).factorial * H ^ (Fintype.card ι - 1) := by
  rw [Matrix.adjugate_apply]
  let K : ι → ℝ := fun k => if k = j then 1 else H
  have hentry : ∀ k l, |(A.updateRow j (Pi.single i 1)) k l| ≤ K k := by
    intro k l
    by_cases hk : k = j
    · subst k
      simp only [Matrix.updateRow_self, K, ite_true, Pi.single_apply]
      split_ifs <;> norm_num
    · simpa only [Matrix.updateRow_ne hk, K, hk, ite_false] using hA k l
  have hprod : (∏ k, K k) = H ^ (Fintype.card ι - 1) := by
    rw [← Finset.mul_prod_erase Finset.univ K (Finset.mem_univ j)]
    have hj : K j = 1 := by simp [K]
    rw [hj, one_mul]
    calc
      (∏ k ∈ Finset.univ.erase j, K k) = ∏ _k ∈ Finset.univ.erase j, H := by
        apply Finset.prod_congr rfl
        intro k hk
        simp only [K, Finset.ne_of_mem_erase hk, ite_false]
      _ = _ := by simp
  simpa only [hprod] using matrix_det_abs_le_row_bounds _ K hentry

theorem matrix_inverse_entry_abs_le (A : Matrix ι ι ℝ) {H κ : ℝ}
    (hA : ∀ i j, |A i j| ≤ H) (hκ : 0 < κ) (hdet : κ ≤ |A.det|)
    (i j : ι) :
    |A⁻¹ i j| ≤ ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_inv]
  have hcof := matrix_adjugate_entry_abs_le A hA i j
  have hinv : |A.det|⁻¹ ≤ κ⁻¹ := inv_anti₀ hκ hdet
  calc
    _ ≤ κ⁻¹ * ((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) :=
      mul_le_mul hinv hcof (abs_nonneg _) (inv_nonneg.mpr hκ.le)
    _ = _ := by rw [div_eq_mul_inv]; ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def matrixSupCLM {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) : (κ → ℝ) →L[ℝ] (ι → ℝ) :=
  A.mulVecLin.toContinuousLinearMap

theorem matrixSupCLM_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℝ) {H : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H) :
    ‖matrixSupCLM A‖ ≤ Fintype.card κ * H := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  change ‖∑ j, A i j * x j‖ ≤ _
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ j, |A i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, H * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hx : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
      exact mul_le_mul (hA i j) hx (abs_nonneg _) hH
    _ = _ := by simp [mul_assoc]

theorem matrixSupCLM_mul {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixSupCLM (A * B) = (matrixSupCLM A).comp (matrixSupCLM B) := by
  ext x i
  change ((A * B).mulVec x) i = (A.mulVec (B.mulVec x)) i
  rw [Matrix.mulVec_mulVec]

theorem matrixSupCLM_one {ι : Type*} [Fintype ι] [DecidableEq ι] :
    matrixSupCLM (1 : Matrix ι ι ℝ) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  ext x i
  change ((1 : Matrix ι ι ℝ).mulVec x) i = x i
  simp

theorem matrixSupCLM_inverse_spec {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (hA : A.det ≠ 0) :
    (matrixSupCLM A).IsInvertible ∧ (matrixSupCLM A).inverse = matrixSupCLM A⁻¹ := by
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr hA
  have hright : (matrixSupCLM A).comp (matrixSupCLM A⁻¹) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← matrixSupCLM_mul, A.mul_nonsing_inv hunit, matrixSupCLM_one]
  have hleft : (matrixSupCLM A⁻¹).comp (matrixSupCLM A) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    rw [← matrixSupCLM_mul, A.nonsing_inv_mul hunit, matrixSupCLM_one]
  exact ⟨ContinuousLinearMap.IsInvertible.of_inverse hright hleft,
    ContinuousLinearMap.inverse_eq hright hleft⟩

theorem matrixSupCLM_inverse_norm_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {H κ : ℝ} (hH : 0 ≤ H) (hA : ∀ i j, |A i j| ≤ H)
    (hκ : 0 < κ) (hdet : κ ≤ |A.det|) :
    (matrixSupCLM A).IsInvertible ∧
      ‖(matrixSupCLM A).inverse‖ ≤
        Fintype.card ι * (((Fintype.card ι).factorial * H ^ (Fintype.card ι - 1)) / κ) := by
  have hne : A.det ≠ 0 := abs_pos.mp (hκ.trans_le hdet)
  obtain ⟨hinv, heq⟩ := matrixSupCLM_inverse_spec A hne
  refine ⟨hinv, ?_⟩
  rw [heq]
  exact matrixSupCLM_norm_le A⁻¹ (by positivity) (matrix_inverse_entry_abs_le A hA hκ hdet)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBoxTest
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def affineBoxAverage (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∫ u, boxProbabilityWindow ℓ 0 u * g (x + A u)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

noncomputable def affineBoxIntegrand (ℓ : ι → ℝ) (A : (ι → ℝ) →L[ℝ] (ι → ℝ))
    (g : (ι → ℝ) → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  boxProbabilityWindow ℓ 0 p.2 * g (p.1 + A p.2)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ProductEuclideanCoordinates
namespace OAI

section

namespace Erdos3

theorem euclidean_norm_le_sum_abs {ι : Type*} [Fintype ι] (x : EuclideanSpace ℝ ι) :
    ‖x‖ ≤ ∑ i, |x i| := by
  have hsq := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := Finset.univ) (f := fun i => ‖x i‖) (fun i _ => norm_nonneg (x i))
  have he := PiLp.norm_sq_eq_of_L2 (fun _ : ι => ℝ) x
  have hn := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => norm_nonneg (x i))
  have h : ‖x‖ ≤ ∑ i, ‖x i‖ := by nlinarith [norm_nonneg x]
  simpa only [Real.norm_eq_abs] using h

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def productEuclideanEquiv :
    ((σ → ℝ) × (κ → ℝ)) ≃ₗ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) :=
  (LinearEquiv.sumArrowLequivProdArrow σ κ ℝ ℝ).symm.trans
    (EuclideanSpace.equiv (σ ⊕ κ) ℝ).symm.toLinearEquiv

omit [Fintype σ] [Fintype κ] in
@[simp] theorem productEuclideanEquiv_apply_inl (x : (σ → ℝ) × (κ → ℝ)) (i : σ) :
    productEuclideanEquiv x (Sum.inl i) = x.1 i := rfl

omit [Fintype σ] [Fintype κ] in
@[simp] theorem productEuclideanEquiv_apply_inr (x : (σ → ℝ) × (κ → ℝ)) (j : κ) :
    productEuclideanEquiv x (Sum.inr j) = x.2 j := rfl

theorem productEuclideanEquiv_norm_le (x : (σ → ℝ) × (κ → ℝ)) :
    ‖productEuclideanEquiv x‖ ≤ ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * ‖x‖ := by
  calc
    _ ≤ ∑ i : σ ⊕ κ, |productEuclideanEquiv x i| := euclidean_norm_le_sum_abs _
    _ ≤ ∑ _i : σ ⊕ κ, ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      cases i with
      | inl i =>
        simpa only [productEuclideanEquiv_apply_inl, ← Real.norm_eq_abs] using
          (norm_le_pi_norm x.1 i).trans (norm_fst_le x)
      | inr j =>
        simpa only [productEuclideanEquiv_apply_inr, ← Real.norm_eq_abs] using
          (norm_le_pi_norm x.2 j).trans (norm_snd_le x)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_sum, nsmul_eq_mul]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProperSubspaceCount
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι]

theorem exists_coordinate_injective_of_ne_top
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤) :
    ∃ j : ι, ∀ x ∈ U, ∀ y ∈ U, (∀ i, i ≠ j → x i = y i) → x = y := by
  classical
  obtain ⟨f, hf, hzero⟩ := U.exists_dual_map_eq_bot_of_lt_top hU.lt_top inferInstance
  have hfzero : ∀ x ∈ U, f x = 0 := by
    intro x hx
    have hm : f x ∈ U.map f := ⟨x, hx, rfl⟩
    simpa only [hzero, Submodule.mem_bot] using hm
  have hcoord : ∃ j : ι, f (fun i => if j = i then 1 else 0) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf
    apply LinearMap.ext
    intro x
    change f x = 0
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp only [h, smul_zero, Finset.sum_const_zero]
  obtain ⟨j, hj⟩ := hcoord
  refine ⟨j, ?_⟩
  intro x hx y hy hxy
  have he : f (x - y) = (x j - y j) * f (fun i => if j = i then 1 else 0) := by
    rw [LinearMap.pi_apply_eq_sum_univ]
    apply Finset.sum_eq_single j
    · intro i _ hij
      simp only [Pi.sub_apply, hxy i hij, sub_self, zero_smul]
    · simp
  have hjxy : x j = y j := by
    rw [map_sub, hfzero x hx, hfzero y hy, sub_self] at he
    exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hj)
  funext i
  by_cases hij : i = j
  · simpa only [hij] using hjxy
  · exact hxy i hij

theorem integer_points_card_le_of_proper_subspace [DecidableEq ι]
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤)
    (H : Finset (ι → ℤ)) (S : ι → Finset ℤ)
    (hmem : ∀ h ∈ H, (fun i => (h i : ℝ)) ∈ U)
    (hbound : ∀ h ∈ H, ∀ i, h i ∈ S i) :
    ∃ j : ι, H.card ≤ ∏ i : {i : ι // i ≠ j}, (S i.val).card := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_injective_of_ne_top U hU
  refine ⟨j, ?_⟩
  let restrict : (ι → ℤ) → ({i : ι // i ≠ j} → ℤ) := fun h i => h i.val
  have hcard : H.card ≤ (Fintype.piFinset (fun i : {i : ι // i ≠ j} => S i.val)).card := by
    apply Finset.card_le_card_of_injOn restrict
    · intro h hh
      exact Fintype.mem_piFinset.mpr (fun i => hbound h hh i.val)
    · intro h hh k hk heq
      have he : (fun i => (h i : ℝ)) = (fun i => (k i : ℝ)) := by
        apply hj _ (hmem h hh) _ (hmem k hk)
        intro i hi
        exact_mod_cast congrFun heq ⟨i, hi⟩
      funext i
      exact_mod_cast congrFun he i
  simpa only [Fintype.card_piFinset] using hcard

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAbsInterval
namespace OAI

section

namespace Erdos3

noncomputable def integerAbsInterval (B : ℝ) : Finset ℤ :=
  Finset.Icc (-⌊B⌋) ⌊B⌋

theorem mem_integerAbsInterval (B : ℝ) (z : ℤ) :
    z ∈ integerAbsInterval B ↔ |(z : ℝ)| ≤ B := by
  rw [integerAbsInterval, Finset.mem_Icc, abs_le]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hn : -z ≤ ⌊B⌋ := by omega
    have hn' := Int.le_floor.mp hn
    have hp := Int.le_floor.mp hhi
    push_cast at hn'
    exact ⟨by linarith, hp⟩
  · rintro ⟨hlo, hhi⟩
    have hn : (-z : ℤ) ≤ ⌊B⌋ := Int.le_floor.mpr (by push_cast; linarith)
    exact ⟨by omega, Int.le_floor.mpr hhi⟩

theorem integerAbsInterval_card_le (B : ℝ) (hB : 0 ≤ B) :
    ((integerAbsInterval B).card : ℝ) ≤ 2 * B + 1 := by
  have hf : (0 : ℤ) ≤ ⌊B⌋ := Int.floor_nonneg.mpr hB
  have hc : ((integerAbsInterval B).card : ℤ) = 2 * ⌊B⌋ + 1 := by
    rw [integerAbsInterval, Int.card_Icc]
    omega
  have hc' : ((integerAbsInterval B).card : ℝ) = 2 * (⌊B⌋ : ℝ) + 1 := by
    exact_mod_cast hc
  rw [hc']
  linarith [Int.floor_le B]

theorem integerAbsInterval_card_le_three (B : ℝ) (hB : 1 ≤ B) :
    ((integerAbsInterval B).card : ℝ) ≤ 3 * B :=
  (integerAbsInterval_card_le B (by linarith)).trans (by linarith)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.DenseIntegerSpan
namespace OAI

section

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem bounded_integer_points_card_le_of_proper_subspace
    (U : Submodule ℝ (ι → ℝ)) (hU : U ≠ ⊤)
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hmem : ∀ h ∈ H, (fun i => (h i : ℝ)) ∈ U)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i) :
    ∃ j : ι, (H.card : ℝ) ≤
      (3 * R) ^ (Fintype.card ι - 1) * ∏ i : {i : ι // i ≠ j}, T i.val := by
  classical
  obtain ⟨j, hj⟩ := integer_points_card_le_of_proper_subspace U hU H
    (fun i => integerAbsInterval (R * T i)) hmem
    (fun h hh i => (mem_integerAbsInterval _ _).mpr (hbound h hh i))
  refine ⟨j, ?_⟩
  have hnum : Fintype.card {i : ι // i ≠ j} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype_compl]
    simp
  calc
    (H.card : ℝ) ≤ ∏ i : {i : ι // i ≠ j}, ((integerAbsInterval (R * T i.val)).card : ℝ) := by
      exact_mod_cast hj
    _ ≤ ∏ i : {i : ι // i ≠ j}, (3 * R) * T i.val := by
      apply Finset.prod_le_prod
      · intro i _
        positivity
      · intro i _
        have hRT : 1 ≤ R * T i.val := by
          simpa only [mul_one] using mul_le_mul hR (hT i.val)
            (show (0 : ℝ) ≤ 1 by norm_num) (show 0 ≤ R by linarith)
        simpa only [mul_assoc] using integerAbsInterval_card_le_three (R * T i.val)
          hRT
    _ = _ := by rw [Finset.prod_mul_distrib]; simp only [Finset.prod_const,
        Finset.card_univ, hnum]

theorem integer_points_span_eq_top_of_density
    (H : Finset (ι → ℤ)) (T : ι → ℝ) (R δ : ℝ)
    (hT : ∀ i, 1 ≤ T i) (hR : 1 ≤ R)
    (hbound : ∀ h ∈ H, ∀ i, |(h i : ℝ)| ≤ R * T i)
    (hdense : δ * ∏ i, T i ≤ (H.card : ℝ))
    (hlarge : ∀ i, (3 * R) ^ (Fintype.card ι - 1) < δ * T i) :
    Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨j, hj⟩ := bounded_integer_points_card_le_of_proper_subspace _ hspan H T R hT hR
    (fun h hh => Submodule.subset_span ⟨h, hh, rfl⟩) hbound
  have hp : 0 < ∏ i : {i : ι // i ≠ j}, T i.val :=
    Finset.prod_pos (fun i _ => lt_of_lt_of_le zero_lt_one (hT i.val))
  have hprod : T j * (∏ i : {i : ι // i ≠ j}, T i.val) = ∏ i, T i := by
    have he : (∏ i ∈ Finset.univ.erase j, T i) = ∏ i : {i : ι // i ≠ j}, T i.val :=
      Finset.prod_subtype _ (by simp) T
    rw [← he]
    exact Finset.mul_prod_erase Finset.univ T (Finset.mem_univ j)
  have hstrict := mul_lt_mul_of_pos_right (hlarge j) hp
  have hidentity : δ * T j * (∏ i : {i : ι // i ≠ j}, T i.val) = δ * ∏ i, T i := by
    rw [mul_assoc, hprod]
  rw [hidentity] at hstrict
  exact (hstrict.trans_le hdense).not_ge hj

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanSubsetBasis
namespace OAI

section

namespace Erdos3

open Module

theorem exists_basis_of_span_subset {E : Type*} [AddCommGroup E] [Module ℝ E]
    [FiniteDimensional ℝ E] (S : Set E) :
    ∃ d : ℕ, ∃ b : Basis (Fin d) ℝ (Submodule.span ℝ S),
      d = finrank ℝ (Submodule.span ℝ S) ∧ ∀ i, (b i).val ∈ S := by
  classical
  obtain ⟨s, hs, hspan, hli⟩ := exists_linearIndependent ℝ S
  let : Fintype s := hli.setFinite.fintype
  have he : Submodule.span ℝ (Set.range ((↑) : s → E)) = Submodule.span ℝ S := by
    simpa only [Subtype.range_coe_subtype, Set.ofPred_mem_eq] using hspan
  let b₀ : Basis s ℝ (Submodule.span ℝ S) := (Basis.span hli).map (LinearEquiv.ofEq _ _ he)
  let b := b₀.reindex (Fintype.equivFin s)
  refine ⟨Fintype.card s, b, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using (finrank_eq_card_basis b).symm
  intro i
  have hb : (b i).val = ((Fintype.equivFin s).symm i).val := by
    simp only [b, Basis.reindex_apply, b₀, Basis.map_apply]
    exact Basis.coe_span_apply hli _
  rw [hb]
  exact hs ((Fintype.equivFin s).symm i).property

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ZSpanRounding
namespace OAI

section

namespace Erdos3

open Module

theorem exists_zspan_near_of_basis_bound {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (b : Basis ι ℝ E) (R : ℝ) (hb : ∀ i, ‖b i‖ ≤ R) (x : E) :
    ∃ z ∈ Submodule.span ℤ (Set.range b), ‖x - z‖ ≤ (Fintype.card ι : ℝ) * R / 2 := by
  classical
  let a : ι → ℤ := fun i => round (b.repr x i)
  let z : E := ∑ i, (a i : ℝ) • b i
  have hz : z ∈ Submodule.span ℤ (Set.range b) := by
    apply Submodule.sum_mem
    intro i _
    rw [Int.cast_smul_eq_zsmul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have he : x - z = ∑ i, (b.repr x i - (a i : ℝ)) • b i := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [b.sum_repr]
  refine ⟨z, hz, ?_⟩
  rw [he]
  calc
    _ ≤ ∑ i, ‖(b.repr x i - (a i : ℝ)) • b i‖ := norm_sum_le _ _
    _ = ∑ i, |b.repr x i - (a i : ℝ)| * ‖b i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ _i : ι, (1 / 2 : ℝ) * R := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul (abs_sub_round (b.repr x i)) (hb i) (norm_nonneg _) (by norm_num)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeVoronoiPacking
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E)

def latticeVoronoi : Set E := {x : E | ∀ z : Λ, ‖x‖ ≤ ‖x - z.val‖}

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeVoronoi_closed : IsClosed (latticeVoronoi Λ) := by
  change IsClosed {x : E | ∀ z : Λ, ‖x‖ ≤ ‖x - z.val‖}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun z => isClosed_le continuous_norm ((continuous_id.sub continuous_const).norm))

theorem exists_sub_mem_latticeVoronoi [DiscreteTopology Λ] (x : E) :
    ∃ z : Λ, x - z.val ∈ latticeVoronoi Λ := by
  have hclosed : IsClosed (Λ : Set E) :=
    (AddSubgroup.isClosed_of_discrete : IsClosed (Λ.toAddSubgroup : Set E))
  obtain ⟨z, hz, he⟩ := hclosed.exists_infDist_eq_dist ⟨0, Λ.zero_mem⟩ x
  refine ⟨⟨z, hz⟩, ?_⟩
  intro w
  have hnear := Metric.infDist_le_dist_of_mem (x := x) (Λ.add_mem hz w.property)
  rw [he, dist_eq_norm, dist_eq_norm] at hnear
  simpa only [sub_add_eq_sub_sub] using hnear

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem latticeVoronoi_subset_closedBall (B : ℝ)
    (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B) :
    latticeVoronoi Λ ⊆ Metric.closedBall 0 B := by
  intro x hx
  obtain ⟨z, hz⟩ := hcover x
  exact mem_closedBall_zero_iff.mpr ((hx z).trans hz)

theorem latticeVoronoi_isAddFundamentalDomain [DiscreteTopology Λ]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [Measure.IsAddHaarMeasure μ] :
    IsAddFundamentalDomain Λ (latticeVoronoi Λ) μ where
  nullMeasurableSet := (latticeVoronoi_closed Λ).measurableSet.nullMeasurableSet
  ae_covers := Filter.Eventually.of_forall fun x => by
    obtain ⟨z, hz⟩ := exists_sub_mem_latticeVoronoi Λ x
    refine ⟨-z, ?_⟩
    simpa only [Submodule.vadd_def, vadd_eq_add, Submodule.coe_neg, neg_add_eq_sub] using hz
  aedisjoint := by
    intro a b hab
    apply measure_mono_null (t := {x : E | ‖x - a.val‖ = ‖x - b.val‖})
    · intro x hx
      obtain ⟨y, hy, hya⟩ := hx.1
      obtain ⟨z, hz, hzb⟩ := hx.2
      have hay : a.val + y = x := hya
      have hbz : b.val + z = x := hzb
      have hyx : y = x - a.val := by rw [← hay]; abel
      have hzx : z = x - b.val := by rw [← hbz]; abel
      have h₁ := hy (b - a)
      have h₂ := hz (a - b)
      change ‖y‖ ≤ ‖y - (b.val - a.val)‖ at h₁
      change ‖z‖ ≤ ‖z - (a.val - b.val)‖ at h₂
      rw [hyx] at h₁
      rw [hzx] at h₂
      have hsub₁ : x - a.val - (b.val - a.val) = x - b.val := by abel
      have hsub₂ : x - b.val - (a.val - b.val) = x - a.val := by abel
      rw [hsub₁] at h₁
      rw [hsub₂] at h₂
      exact le_antisymm h₁ h₂
    · exact euclidean_bisector_measure_zero μ a.val b.val (fun he => hab (Subtype.ext he))

end Erdos3

end

section

namespace Erdos3

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] (Λ : Submodule ℤ E) (R : ℝ)

def shortVectorSpan : Submodule ℝ E :=
  Submodule.span ℝ {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}

noncomputable def shortVectorLattice : Submodule ℤ (shortVectorSpan Λ R) :=
  ZLattice.comap ℝ Λ (shortVectorSpan Λ R).subtype

omit [FiniteDimensional ℝ E] in
theorem mem_shortVectorSpan {x : E} (hx : x ∈ Λ) (hR : ‖x‖ ≤ R) :
    x ∈ shortVectorSpan Λ R := Submodule.subset_span ⟨hx, hR⟩

theorem exists_shortVectorSpan_basis :
    ∃ d : ℕ, ∃ b : Basis (Fin d) ℝ (shortVectorSpan Λ R),
      d = finrank ℝ (shortVectorSpan Λ R) ∧
      ∀ i, b i ∈ shortVectorLattice Λ R ∧ ‖b i‖ ≤ R := by
  obtain ⟨d, b, hd, hb⟩ := exists_basis_of_span_subset {x : E | x ∈ Λ ∧ ‖x‖ ≤ R}
  exact ⟨d, b, hd, hb⟩

instance shortVectorLattice_discrete [DiscreteTopology Λ] :
    DiscreteTopology (shortVectorLattice Λ R) :=
  ZLattice.comap_discreteTopology ℝ Λ continuous_subtype_val Subtype.val_injective

instance shortVectorLattice_full [DiscreteTopology Λ] : IsZLattice ℝ (shortVectorLattice Λ R) := by
  obtain ⟨d, b, _, hb⟩ := exists_shortVectorSpan_basis Λ R
  constructor
  apply top_unique
  calc
    ⊤ = Submodule.span ℝ (Set.range b) := b.span_eq.symm
    _ ≤ Submodule.span ℝ (shortVectorLattice Λ R : Set (shortVectorSpan Λ R)) := by
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact (hb i).1

theorem shortVectorLattice_covering (x : shortVectorSpan Λ R) :
    ∃ z : shortVectorLattice Λ R,
      ‖x - z.val‖ ≤ (finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2 := by
  obtain ⟨d, b, hd, hb⟩ := exists_shortVectorSpan_basis Λ R
  obtain ⟨z, hz, hnear⟩ := exists_zspan_near_of_basis_bound b R (fun i => (hb i).2) x
  have hsub : Submodule.span ℤ (Set.range b) ≤ shortVectorLattice Λ R := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact (hb i).1
  refine ⟨⟨z, hsub hz⟩, ?_⟩
  simpa only [Fintype.card_fin, hd] using hnear

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module
open scoped Pointwise

theorem lattice_points_mul_covolume_le_closedBall
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (μ : Measure E) [Measure.IsAddHaarMeasure μ]
    (B R : ℝ) (hcover : ∀ x : E, ∃ z : Λ, ‖x - z.val‖ ≤ B)
    (P : Finset Λ) (hP : ∀ p ∈ P, ‖(p : E)‖ ≤ R) :
    (P.card : ℝ) * ZLattice.covolume Λ μ ≤ μ.real (Metric.closedBall 0 (R + B)) := by
  have : MeasurableVAdd Λ E := (inferInstance : MeasurableVAdd Λ.toAddSubgroup E)
  have : VAddInvariantMeasure Λ E μ := (inferInstance : VAddInvariantMeasure Λ.toAddSubgroup E μ)
  let F := latticeVoronoi Λ
  have hfd := latticeVoronoi_isAddFundamentalDomain Λ μ
  have hF : F ⊆ Metric.closedBall 0 B := latticeVoronoi_subset_closedBall Λ B hcover
  have hfinite : μ F ≠ ⊤ := measure_ne_top_of_subset hF measure_closedBall_lt_top.ne
  have hbound : (⋃ p ∈ P, p +ᵥ F) ⊆ Metric.closedBall 0 (R + B) := by
    intro x hx
    obtain ⟨p, hpUnion⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hpmem, hxTranslate⟩ := Set.mem_iUnion.mp hpUnion
    obtain ⟨y, hy, rfl⟩ := hxTranslate
    apply mem_closedBall_zero_iff.mpr
    change ‖(p : E) + y‖ ≤ R + B
    exact (norm_add_le _ _).trans
      (add_le_add (hP p hpmem) (mem_closedBall_zero_iff.mp (hF hy)))
  have hvol : μ.real (⋃ p ∈ P, p +ᵥ F) = (P.card : ℝ) * μ.real F := by
    rw [measureReal_biUnion_finset₀
      (fun p _ q _ hpq => hfd.aedisjoint hpq)
      (fun p _ => hfd.nullMeasurableSet.vadd p)
      (fun p _ => by rw [measure_vadd]; exact hfinite)]
    simp only [F, measureReal_def, measure_vadd, Finset.sum_const, nsmul_eq_mul]
  rw [ZLattice.covolume_eq_measure_fundamentalDomain Λ μ hfd, ← hvol]
  exact measureReal_mono hbound measure_closedBall_lt_top.ne

theorem shortVectorLattice_covolume_packing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] (R : ℝ)
    (P : Finset (shortVectorLattice Λ R))
    (hP : ∀ p ∈ P, ‖(p : shortVectorSpan Λ R)‖ ≤ R) :
    (P.card : ℝ) * ZLattice.covolume (shortVectorLattice Λ R) ≤
      volume.real (Metric.closedBall (0 : shortVectorSpan Λ R)
        (R + (finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2)) := by
  exact lattice_points_mul_covolume_le_closedBall (shortVectorLattice Λ R) volume
    ((finrank ℝ (shortVectorSpan Λ R) : ℝ) * R / 2) R
    (shortVectorLattice_covering Λ R) P hP

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.ShortVectorProjection
namespace OAI

section

namespace Erdos3

theorem shortVectorSpan_map_eq_top_of_spanning_integer_images
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Λ : Submodule ℤ E) (π : E →ₗ[ℝ] (ι → ℝ)) (H : Finset (ι → ℤ)) (R : ℝ)
    (hspan : Submodule.span ℝ {x : ι → ℝ | ∃ h ∈ H, x = fun i => (h i : ℝ)} = ⊤)
    (hlift : ∀ h ∈ H, ∃ v ∈ Λ, ‖v‖ ≤ R ∧ π v = fun i => (h i : ℝ)) :
    (shortVectorSpan Λ R).map π = ⊤ := by
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro x ⟨h, hh, rfl⟩
  obtain ⟨v, hv, hnorm, hπ⟩ := hlift h hh
  exact ⟨v, mem_shortVectorSpan Λ R hv hnorm, hπ⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DerivativeGridPoints
namespace OAI

section

namespace Erdos3

open scoped Matrix

variable {σ κ : Type*} [Fintype κ]

noncomputable def derivativeGridPoint (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r : κ → ℝ) : (σ → ℝ) × (κ → ℝ) :=
  (fun i => (h i : ℝ) / T i, fun j => scale j * (Y (fun i => (h i : ℝ)) - M *ᵥ r) j)

def derivativeGridPoints (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ) :
    Set ((σ → ℝ) × (κ → ℝ)) :=
  {v | ∃ h : σ → ℤ, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
    v = derivativeGridPoint T scale Y M h r}

theorem derivativeGridPoint_mem (T : σ → ℝ) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ)
    (h : σ → ℤ) (r : κ → ℝ) (hr : r ∈ realDenominatorGrid l) :
    derivativeGridPoint T scale Y M h r ∈ derivativeGridPoints T scale Y M l :=
  ⟨h, r, hr, rfl⟩

theorem derivativeGridPoint_bound [Fintype σ] (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (scale : κ → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r e : κ → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hh : ∀ i, |(h i : ℝ)| ≤ A * T i)
    (heq : Y (fun i => (h i : ℝ)) = e + M *ᵥ r)
    (he : ∀ j, |e j| ≤ B / scale j) :
    ‖derivativeGridPoint T scale Y M h r‖ ≤ max A B := by
  have hv : Y (fun i => (h i : ℝ)) - M *ᵥ r = e := by rw [heq, add_sub_cancel_right]
  rw [Prod.norm_def]
  apply max_le
  · apply (pi_norm_le_iff_of_nonneg (hA.trans (le_max_left _ _))).mpr
    intro i
    change ‖(h i : ℝ) / T i‖ ≤ max A B
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hT i)]
    exact ((div_le_iff₀ (hT i)).mpr (hh i)).trans (le_max_left _ _)
  · apply (pi_norm_le_iff_of_nonneg (hB.trans (le_max_right _ _))).mpr
    intro j
    change ‖scale j * (Y (fun i => (h i : ℝ)) - M *ᵥ r) j‖ ≤ max A B
    rw [hv, Real.norm_eq_abs, abs_mul, abs_of_pos (hscale j)]
    have hj : scale j * |e j| ≤ B := by
      simpa only [mul_comm] using (le_div_iff₀ (hscale j)).mp (he j)
    exact hj.trans (le_max_right _ _)

theorem derivativeGridPoint_eq_imp_shift_eq (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : κ → ℝ) (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h k : σ → ℤ) (r t : κ → ℝ)
    (heq : derivativeGridPoint T scale Y M h r = derivativeGridPoint T scale Y M k t) : h = k := by
  funext i
  have hi := congrArg (fun v : (σ → ℝ) × (κ → ℝ) => v.1 i * T i) heq
  simp only [derivativeGridPoint, div_mul_cancel₀ _ (hT i)] at hi
  exact_mod_cast hi

theorem exists_bounded_derivativeGridPoint_family [Fintype σ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ) (l : ℕ)
    (H : Finset (σ → ℤ)) (h₀ : σ → ℤ) (R : ℝ)
    (hexists : ∀ h ∈ H, ∃ r : κ → ℝ, r ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y M (h - h₀) r‖ ≤ R) :
    ∃ P : Finset ((σ → ℝ) × (κ → ℝ)), P.card = H.card ∧
      ∀ v ∈ P, v ∈ derivativeGridPoints T scale Y M l ∧ ‖v‖ ≤ R := by
  classical
  let r : (σ → ℤ) → κ → ℝ := fun h => if hh : h ∈ H then (hexists h hh).choose else 0
  have hr (h : σ → ℤ) (hh : h ∈ H) : r h ∈ realDenominatorGrid l ∧
      ‖derivativeGridPoint T scale Y M (h - h₀) (r h)‖ ≤ R := by
    simpa only [r, dif_pos hh] using (hexists h hh).choose_spec
  refine ⟨H.image (fun h => derivativeGridPoint T scale Y M (h - h₀) (r h)), ?_, ?_⟩
  · apply Finset.card_image_iff.mpr
    intro h _ k _ heq
    have hd := derivativeGridPoint_eq_imp_shift_eq T hT scale Y M (h - h₀) (k - h₀) (r h) (r k) heq
    simpa only [sub_add_cancel] using congrArg (fun z => z + h₀) hd
  · intro v hv
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hv
    exact ⟨derivativeGridPoint_mem T scale Y M l (h - h₀) (r h) (hr h hh).1, (hr h hh).2⟩

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.EuclideanDerivativeLattice
namespace OAI

section

namespace Erdos3

noncomputable def coordinateScaleEquiv {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0) :
    (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ) where
  toFun x i := d i * x i
  invFun x i := x i / d i
  left_inv x := by funext i; exact mul_div_cancel_left₀ (x i) (hd i)
  right_inv x := by funext i; exact mul_div_cancel₀ (x i) (hd i)
  map_add' x y := by funext i; exact mul_add _ _ _
  map_smul' c x := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

@[simp] theorem coordinateScaleEquiv_apply {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (x : ι → ℝ) (i : ι) : coordinateScaleEquiv d hd x i = d i * x i := rfl

@[simp] theorem coordinateScaleEquiv_symm_apply {ι : Type*} (d : ι → ℝ) (hd : ∀ i, d i ≠ 0)
    (x : ι → ℝ) (i : ι) : (coordinateScaleEquiv d hd).symm x i = x i / d i := rfl

noncomputable def derivativeShearEquiv {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (Y : E →ₗ[ℝ] F) (A : F ≃ₗ[ℝ] F) :
    (E × F) ≃ₗ[ℝ] (E × F) where
  toFun x := (x.1, Y x.1 - A x.2)
  invFun x := (x.1, A.symm (Y x.1 - x.2))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by
    refine Prod.ext ?_ ?_
    · rfl
    · change Y (x.1 + y.1) - A (x.2 + y.2) = (Y x.1 - A x.2) + (Y y.1 - A y.2)
      rw [map_add, map_add]
      abel
  map_smul' c x := by
    refine Prod.ext ?_ ?_
    · rfl
    · change Y (c • x.1) - A (c • x.2) = c • (Y x.1 - A x.2)
      rw [map_smul, map_smul, smul_sub]

@[simp] theorem derivativeShearEquiv_apply {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (Y : E →ₗ[ℝ] F) (A : F ≃ₗ[ℝ] F) (x : E × F) :
    derivativeShearEquiv Y A x = (x.1, Y x.1 - A x.2) := rfl

noncomputable def derivativeLatticeEquiv {σ κ : Type*}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) :
    ((σ → ℝ) × (κ → ℝ)) ≃ₗ[ℝ] ((σ → ℝ) × (κ → ℝ)) :=
  ((LinearEquiv.refl ℝ (σ → ℝ)).prodCongr
    (coordinateScaleEquiv (fun _ : κ => (l : ℝ)⁻¹) (fun _ => inv_ne_zero (by exact_mod_cast hl.ne')))).trans
    ((derivativeShearEquiv Y A).trans
      ((coordinateScaleEquiv (fun i => (T i)⁻¹) (fun i => inv_ne_zero (hT i))).prodCongr
        (coordinateScaleEquiv scale hscale)))

theorem derivativeLatticeEquiv_apply {σ κ : Type*}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (x : (σ → ℝ) × (κ → ℝ)) :
    derivativeLatticeEquiv T hT scale hscale Y A l hl x =
      (fun i => x.1 i / T i, fun j => scale j * (Y x.1 - A (fun k => x.2 k / l)) j) := by
  simp only [derivativeLatticeEquiv, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
    LinearEquiv.refl_apply, derivativeShearEquiv_apply]
  refine Prod.ext ?_ ?_
  · funext i
    simp only [coordinateScaleEquiv_apply, div_eq_mul_inv, mul_comm]
  · funext j
    have he : coordinateScaleEquiv (fun _ : κ => (l : ℝ)⁻¹)
        (fun _ => inv_ne_zero (by exact_mod_cast hl.ne')) x.2 = (fun k => x.2 k / l) := by
      funext k
      simp only [coordinateScaleEquiv_apply, div_eq_mul_inv, mul_comm]
    exact congrArg (fun v : κ → ℝ => scale j * (Y x.1 - A v) j) he

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

noncomputable def standardProductBasis :
    Basis (σ ⊕ κ) ℝ ((σ → ℝ) × (κ → ℝ)) :=
  (Pi.basisFun ℝ σ).prod (Pi.basisFun ℝ κ)

theorem standardProductBasis_mem_iff (x : (σ → ℝ) × (κ → ℝ)) :
    x ∈ Submodule.span ℤ (Set.range (standardProductBasis (σ := σ) (κ := κ))) ↔
      x.1 ∈ realIntegerGrid ∧ x.2 ∈ realIntegerGrid := by
  rw [(standardProductBasis (σ := σ) (κ := κ)).mem_span_iff_repr_mem ℤ x]
  constructor
  · intro h
    have h₁ : ∀ i : σ, ∃ n : ℤ, (n : ℝ) = x.1 i := by
      intro i
      simpa [standardProductBasis] using h (Sum.inl i)
    have h₂ : ∀ i : κ, ∃ n : ℤ, (n : ℝ) = x.2 i := by
      intro i
      simpa [standardProductBasis] using h (Sum.inr i)
    choose a ha using h₁
    choose b hb using h₂
    exact ⟨⟨a, funext ha⟩, ⟨b, funext hb⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ i
    cases i with
    | inl i => exact ⟨a i, by simpa [standardProductBasis] using congrFun ha i⟩
    | inr i => exact ⟨b i, by simpa [standardProductBasis] using congrFun hb i⟩

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

noncomputable def derivativeLatticeBasis : Basis (σ ⊕ κ) ℝ ((σ → ℝ) × (κ → ℝ)) :=
  standardProductBasis.map (derivativeLatticeEquiv T hT scale hscale Y A l hl)

noncomputable def derivativeLattice : Submodule ℤ ((σ → ℝ) × (κ → ℝ)) :=
  Submodule.span ℤ (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))

instance derivativeLattice_discrete : DiscreteTopology (derivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))))

instance derivativeLattice_full : IsZLattice ℝ (derivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (derivativeLatticeBasis T hT scale hscale Y A l hl))))

theorem derivativeLattice_mem_iff (v : (σ → ℝ) × (κ → ℝ)) :
    v ∈ derivativeLattice T hT scale hscale Y A l hl ↔
      ∃ h : σ → ℤ, ∃ z : κ → ℤ,
        v = derivativeLatticeEquiv T hT scale hscale Y A l hl
          (fun i => (h i : ℝ), fun j => (z j : ℝ)) := by
  change v ∈ Submodule.span ℤ (Set.range
    (standardProductBasis.map (derivativeLatticeEquiv T hT scale hscale Y A l hl))) ↔ _
  rw [← ZSpan.map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    obtain ⟨⟨h, hh⟩, ⟨z, hz⟩⟩ := (standardProductBasis_mem_iff x).mp hx
    have he : x = ((fun i => (h i : ℝ)), (fun j => (z j : ℝ))) := Prod.ext hh.symm hz.symm
    exact ⟨h, z, hxv.symm.trans (congrArg (derivativeLatticeEquiv T hT scale hscale Y A l hl) he)⟩
  · rintro ⟨h, z, rfl⟩
    refine ⟨((fun i => (h i : ℝ)), (fun j => (z j : ℝ))), ?_, rfl⟩
    exact (standardProductBasis_mem_iff _).mpr ⟨⟨h, rfl⟩, ⟨z, rfl⟩⟩

theorem derivativeLattice_carrier [DecidableEq κ] :
    (derivativeLattice T hT scale hscale Y A l hl : Set ((σ → ℝ) × (κ → ℝ))) =
      derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l := by
  ext v
  change (v ∈ derivativeLattice T hT scale hscale Y A l hl) ↔ _
  rw [derivativeLattice_mem_iff]
  have hlr : (l : ℝ) ≠ 0 := by exact_mod_cast hl.ne'
  constructor
  · rintro ⟨h, z, rfl⟩
    refine ⟨h, (fun j => (z j : ℝ) / l), ⟨z, ?_⟩, ?_⟩
    · funext j
      change (z j : ℝ) = (l : ℝ) * ((z j : ℝ) / l)
      field_simp
    · simp only [derivativeLatticeEquiv_apply, derivativeGridPoint, LinearMap.toMatrix'_mulVec,
        LinearEquiv.coe_coe]
  · rintro ⟨h, r, ⟨z, hz⟩, hv⟩
    have hdiv : (fun j => (z j : ℝ) / l) = r := by
      funext j
      have hj : (z j : ℝ) = (l : ℝ) * r j := congrFun hz j
      rw [hj]
      field_simp
    refine ⟨h, z, hv.trans ?_⟩
    simp only [derivativeLatticeEquiv_apply, derivativeGridPoint, LinearMap.toMatrix'_mulVec, hdiv,
      LinearEquiv.coe_coe]

end Erdos3

end

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq σ] [DecidableEq κ]

omit [DecidableEq σ] [DecidableEq κ] in
theorem derivativeGridPoint_shift_bound
    (T : σ → ℝ) (hT : ∀ i, 0 < T i) (scale : κ → ℝ)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (M : Matrix κ κ ℝ)
    (h : σ → ℤ) (r : κ → ℝ) (R : ℝ)
    (hR : ‖derivativeGridPoint T scale Y M h r‖ ≤ R) :
    ∀ i, |(h i : ℝ)| ≤ R * T i := by
  intro i
  have hi := (norm_le_pi_norm (derivativeGridPoint T scale Y M h r).1 i).trans
    ((norm_fst_le _).trans hR)
  change ‖(h i : ℝ) / T i‖ ≤ R at hi
  rw [Real.norm_eq_abs, abs_div, abs_of_pos (hT i)] at hi
  exact (div_le_iff₀ (hT i)).mp hi

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ κ : Type*} [Fintype σ] [Fintype κ]
  (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

noncomputable def euclideanDerivativeLatticeBasis :
    Basis (σ ⊕ κ) ℝ (EuclideanSpace ℝ (σ ⊕ κ)) :=
  (derivativeLatticeBasis T hT scale hscale Y A l hl).map productEuclideanEquiv

noncomputable def euclideanDerivativeLattice : Submodule ℤ (EuclideanSpace ℝ (σ ⊕ κ)) :=
  Submodule.span ℤ (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))

instance euclideanDerivativeLattice_discrete :
    DiscreteTopology (euclideanDerivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ
    (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))))

instance euclideanDerivativeLattice_full :
    IsZLattice ℝ (euclideanDerivativeLattice T hT scale hscale Y A l hl) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ
    (Set.range (euclideanDerivativeLatticeBasis T hT scale hscale Y A l hl))))

theorem euclideanDerivativeLattice_mem_iff (v : EuclideanSpace ℝ (σ ⊕ κ)) :
    v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ↔
      productEuclideanEquiv.symm v ∈ derivativeLattice T hT scale hscale Y A l hl := by
  change v ∈ Submodule.span ℤ (Set.range
    ((derivativeLatticeBasis T hT scale hscale Y A l hl).map productEuclideanEquiv)) ↔ _
  rw [← ZSpan.map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    change productEuclideanEquiv x = v at hxv
    rw [← hxv, LinearEquiv.symm_apply_apply]
    exact hx
  · intro hv
    exact ⟨productEuclideanEquiv.symm v, hv, productEuclideanEquiv.apply_symm_apply v⟩

theorem productEuclideanEquiv_mem_derivativeLattice (v : (σ → ℝ) × (κ → ℝ)) :
    productEuclideanEquiv v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ↔
      v ∈ derivativeLattice T hT scale hscale Y A l hl := by
  rw [euclideanDerivativeLattice_mem_iff, LinearEquiv.symm_apply_apply]

theorem exists_bounded_euclideanDerivativeLattice_family [DecidableEq κ]
    (R : ℝ) (P : Finset ((σ → ℝ) × (κ → ℝ)))
    (hP : ∀ v ∈ P,
      v ∈ derivativeGridPoints T scale Y (LinearMap.toMatrix' A.toLinearMap) l ∧ ‖v‖ ≤ R) :
    ∃ Q : Finset (EuclideanSpace ℝ (σ ⊕ κ)), Q.card = P.card ∧
      ∀ v ∈ Q, v ∈ euclideanDerivativeLattice T hT scale hscale Y A l hl ∧
        ‖v‖ ≤ ((Fintype.card σ + Fintype.card κ : ℕ) : ℝ) * R := by
  classical
  refine ⟨P.image productEuclideanEquiv, Finset.card_image_of_injective _
    productEuclideanEquiv.injective, ?_⟩
  intro v hv
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
  constructor
  · apply (productEuclideanEquiv_mem_derivativeLattice T hT scale hscale Y A l hl w).mpr
    rw [← SetLike.mem_coe, derivativeLattice_carrier]
    exact (hP w hw).1
  · exact (productEuclideanEquiv_norm_le w).trans
      (mul_le_mul_of_nonneg_left (hP w hw).2 (Nat.cast_nonneg _))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalDensityTransport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*}

noncomputable def inverseJacobian (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : ℝ :=
  |LinearMap.det A.symm.toLinearEquiv.toLinearMap|

theorem inverseJacobian_pos (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : 0 < inverseJacobian A :=
  abs_pos.mpr A.symm.toLinearEquiv.isUnit_det'.ne_zero

theorem inverseJacobian_eq (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    inverseJacobian A = |LinearMap.det A.toLinearEquiv.toLinearMap|⁻¹ := by
  unfold inverseJacobian
  rw [show A.symm.toLinearEquiv = A.toLinearEquiv.symm from rfl,
    LinearEquiv.det_coe_symm, abs_inv]

variable [Fintype ι]

noncomputable def linearDensityPullback (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ))
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := inverseJacobian A * f (A.symm x)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def linearBoxDensity (ℓ : ι → ℝ) (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) :
    (ι → ℝ) → ℝ := linearDensityPullback A (boxProbabilityWindow ℓ 0)

noncomputable def linearBoxDensityCap (ℓ : ι → ℝ) (hℓ : ∀ i, 0 < ℓ i)
    (A : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : ℝ≥0 :=
  ⟨inverseJacobian A * ∏ i, 1 / ℓ i,
    mul_nonneg (inverseJacobian_pos A).le
      (Finset.prod_nonneg (fun i _ => div_nonneg zero_le_one (hℓ i).le))⟩

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι] (a : ι → ℝ) (ha : ∀ i, a i ≠ 0)

noncomputable def diagonalDensityTransport (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  linearDensityPullback (coordinateScaleEquiv a ha).toContinuousLinearEquiv f

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PivotCoordinateChange
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ENNReal

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotCoordinateChange (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) :
    ((J → ℝ) × (I → ℝ)) ≃ₜ ((J → ℝ) × (I → ℝ)) where
  toFun p := (p.1, A p.2 + B p.1)
  invFun p := (p.1, A.symm (p.2 - B p.1))
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def pivotDensityPullback (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (p : (J → ℝ) × (I → ℝ)) : ℝ :=
  inverseJacobian A * f ((pivotCoordinateChange A B).symm p)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.UnitBoxAmplitude
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def positiveUnitBox (ι : Type*) := Set.univ.pi (fun _ : ι => Set.Ioc (0 : ℝ) 1)

noncomputable def unitBoxMeasure (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  volume.restrict (positiveUnitBox ι)

instance unitBoxMeasure_probability : IsProbabilityMeasure (unitBoxMeasure ι) := by
  constructor
  simp only [unitBoxMeasure, Measure.restrict_apply_univ, positiveUnitBox, Real.volume_pi_Ioc,
    sub_zero, ENNReal.ofReal_one, Finset.prod_const_one]

noncomputable def pairedAmplitude (p : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  max (∏ i, p.1 i) (∏ i, p.2 i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PairedProductDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

noncomputable def densityMixture {T X : Type*} [MeasurableSpace T]
    (μ : Measure T) (F : T → X → ℝ) (x : X) : ℝ := ∫ t, F t x ∂μ

theorem densityMixture_joint_integrable {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [SFinite ν]
    (F : T → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ν ∧ (∫ x, F t x ∂ν) = 1) :
    Integrable (Function.uncurry F) (μ.prod ν) := by
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  refine ⟨hF.mono (fun _ ht => ht.2.1), ?_⟩
  apply (integrable_const (1 : ℝ)).congr
  filter_upwards [hF] with t ht
  simp only [Function.uncurry_apply_pair, Real.norm_of_nonneg (ht.1 _)]
  exact ht.2.2.symm

theorem densityMixture_probability_density {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [IsProbabilityMeasure μ] [SFinite ν]
    (F : T → X → ℝ) (hm : Measurable (Function.uncurry F))
    (hF : ∀ᵐ t ∂μ, (∀ x, 0 ≤ F t x) ∧ Integrable (F t) ν ∧ (∫ x, F t x ∂ν) = 1) :
    (∀ x, 0 ≤ densityMixture μ F x) ∧ Integrable (densityMixture μ F) ν ∧
      (∫ x, densityMixture μ F x ∂ν) = 1 := by
  have hi := densityMixture_joint_integrable μ ν F hm hF
  refine ⟨fun x => integral_nonneg_of_ae (hF.mono (fun _ ht => ht.1 x)),
    hi.integral_prod_right, ?_⟩
  change (∫ x, ∫ t, F t x ∂μ ∂ν) = 1
  rw [← integral_integral_swap hi]
  calc
    (∫ t, ∫ x, F t x ∂ν ∂μ) = ∫ _, (1 : ℝ) ∂μ :=
      integral_congr_ae (hF.mono (fun _ ht => ht.2.2))
    _ = 1 := by simp

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def randomIntervalDensity {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (ℓ s : T → ℝ) : ℝ → ℝ :=
  densityMixture μ (fun t => normalizedIntervalWindow (ℓ t) (s t))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem densityMixture_test_integral {T X : Type*} [MeasurableSpace T] [MeasurableSpace X]
    (μ : Measure T) (ν : Measure X) [SFinite μ] [SFinite ν]
    (F : T → X → ℝ) (hF : Integrable (Function.uncurry F) (μ.prod ν))
    (φ : X → ℝ) (hφ : Measurable φ) {C : ℝ} (hbound : ∀ x, ‖φ x‖ ≤ C) :
    (∫ x, densityMixture μ F x * φ x ∂ν) = ∫ t, ∫ x, F t x * φ x ∂ν ∂μ := by
  have hi : Integrable (Function.uncurry (fun t x => F t x * φ x)) (μ.prod ν) :=
    hF.mul_bdd (hφ.comp measurable_snd).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun p => hbound p.2))
  calc
    (∫ x, densityMixture μ F x * φ x ∂ν) = ∫ x, ∫ t, F t x * φ x ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact (integral_mul_const (φ x) _).symm
    _ = ∫ t, ∫ x, F t x * φ x ∂ν ∂μ := (integral_integral_swap hi).symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def unitScalarMeasure : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)

instance unitScalarMeasure_probability : IsProbabilityMeasure unitScalarMeasure := by
  constructor
  simp [unitScalarMeasure]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def haarShiftDensity {T G : Type*} [MeasurableSpace T] [Sub G]
    (ν : Measure T) (z : T → G) (f : G → ℝ) (y : G) : ℝ :=
  densityMixture ν (fun t x => f (x - z t)) y

variable {T G : Type*} [MeasurableSpace T] [AddCommGroup G]
  [MeasurableSpace G] [MeasurableAdd₂ G] [MeasurableNeg G]

theorem haarShiftDensity_probability (μ : Measure G) [μ.IsAddLeftInvariant]
    (ν : Measure T) [IsProbabilityMeasure ν]
    {z : T → G} {f : G → ℝ} (hz : Measurable z) (hf : Measurable f)
    [SFinite μ] (hfi : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) (hmass : (∫ x, f x ∂μ) = 1) :
    (∀ x, 0 ≤ haarShiftDensity ν z f x) ∧ Integrable (haarShiftDensity ν z f) μ ∧
      (∫ x, haarShiftDensity ν z f x ∂μ) = 1 := by
  apply densityMixture_probability_density ν μ _
  · exact hf.comp (measurable_snd.sub (hz.comp measurable_fst))
  · exact ae_of_all ν (fun t => ⟨fun x => hf0 _, hfi.comp_sub_right (z t),
      (integral_sub_right_eq_self f (z t)).trans hmass⟩)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {T : Type*} [MeasurableSpace T]

noncomputable def independentShiftDensity (μ : Measure T) (z : T → ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  densityMixture μ (fun t x => f (x - z t))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def pairedProductParameterMeasure (ι : Type*) [Fintype ι] :
    Measure (((ι → ℝ) × (ι → ℝ)) × ℝ) :=
  ((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod unitScalarMeasure

instance pairedProductParameterMeasure_probability :
    IsProbabilityMeasure (pairedProductParameterMeasure ι) :=
  inferInstanceAs (IsProbabilityMeasure (((unitBoxMeasure ι).prod (unitBoxMeasure ι)).prod unitScalarMeasure))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.TranslatedMixtureL1
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotOutputDensity (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (v : I → ℝ) : ℝ := ∫ y, pivotDensityPullback A B f (y, v)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {I J : Type*} [Fintype I] [Fintype J]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PivotJacobianBound
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {I J : Type*} [Fintype I] [Fintype J]

noncomputable def pivotSliceProfile (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) (f : (J → ℝ) × (I → ℝ) → ℝ)
    (v : I → ℝ) (y : J → ℝ) : ℝ := f (y, A.symm (v - B y))

noncomputable def pivotGraphLipschitz (A : (I → ℝ) ≃L[ℝ] (I → ℝ))
    (B : (J → ℝ) →L[ℝ] (I → ℝ)) : ℝ≥0 :=
  max 1 (‖A.symm.toContinuousLinearMap‖₊ * ‖B‖₊)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BoundedRealPolynomialBasis
namespace OAI

section

namespace Erdos3

noncomputable def paddedExponentWord {K : Type*} (m : K →₀ ℕ) (h : ℕ)
    (hm : m.sum (fun _ n => n) ≤ h) : List.Vector (Option K) h :=
  ⟨(m.toMultiset.map some + Multiset.replicate (h - m.sum (fun _ n => n)) none).toList, by
    rw [Multiset.length_toList, Multiset.card_add, Multiset.card_map, Multiset.card_replicate,
      Finsupp.card_toMultiset]
    exact Nat.add_sub_of_le hm⟩

theorem paddedExponentWord_count {K : Type*} [DecidableEq K] (m : K →₀ ℕ) (h : ℕ)
    (hm : m.sum (fun _ n => n) ≤ h) (k : K) :
    ((paddedExponentWord m h hm).val : Multiset (Option K)).count (some k) = m k := by
  change Multiset.count (some k)
    ((m.toMultiset.map some + Multiset.replicate (h - m.sum (fun _ n => n)) none).toList :
      Multiset (Option K)) = m k
  rw [Multiset.coe_toList, Multiset.count_add,
    Multiset.count_map_eq_count' _ _ (Option.some_injective _)]
  simp [Multiset.mem_replicate]

theorem boundedExponentSet_card_le {K : Type*} [Fintype K] (s : Finset (K →₀ ℕ)) (h : ℕ)
    (hs : ∀ m ∈ s, m.sum (fun _ n => n) ≤ h) : s.card ≤ (Fintype.card K + 1) ^ h := by
  classical
  let f : s → List.Vector (Option K) h := fun m => paddedExponentWord m.val h (hs m.val m.property)
  have hf : Function.Injective f := by
    intro m n he
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg (fun v : List.Vector (Option K) h => (v.val : Multiset (Option K)).count (some k)) he
    simpa only [f, paddedExponentWord_count] using hc
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, card_vector, Fintype.card_option] using hc

theorem monomialArray_card_le {K T : Type*} [Fintype K] (s : Finset T)
    (exponent : T → K →₀ ℕ) (hinj : Set.InjOn exponent s) (h : ℕ)
    (hs : ∀ t ∈ s, (exponent t).sum (fun _ n => n) ≤ h) : s.card ≤ (Fintype.card K + 1) ^ h := by
  classical
  rw [← Finset.card_image_of_injOn hinj]
  apply boundedExponentSet_card_le
  intro m hm
  rcases Finset.mem_image.mp hm with ⟨t, ht, rfl⟩
  exact hs t ht

theorem mvPolynomial_support_card_le_totalDegree {K : Type*} [Fintype K]
    (p : MvPolynomial K ℝ) {h : ℕ} (hp : p.totalDegree ≤ h) :
    p.support.card ≤ (Fintype.card K + 1) ^ h :=
  boundedExponentSet_card_le p.support h (fun _ hm => (MvPolynomial.le_totalDegree hm).trans hp)

open scoped BigOperators

theorem monomialArray_abs_sum_le {K T : Type*} [Fintype K] (s : Finset T)
    (exponent : T → K →₀ ℕ) (hinj : Set.InjOn exponent s) (h : ℕ)
    (hs : ∀ t ∈ s, (exponent t).sum (fun _ n => n) ≤ h)
    (weight : T → ℝ) {M : ℝ} (hM : 0 ≤ M) (hw : ∀ t ∈ s, |weight t| ≤ M) :
    (∑ t ∈ s, |weight t|) ≤ ((Fintype.card K : ℝ) + 1) ^ h * M := by
  have hc : (s.card : ℝ) ≤ ((Fintype.card K : ℝ) + 1) ^ h := by
    exact_mod_cast monomialArray_card_le s exponent hinj h hs
  calc
    _ ≤ ∑ _t ∈ s, M := Finset.sum_le_sum hw
    _ = (s.card : ℝ) * M := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc hM

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev BoundedIntegerExponent (K : Type*) (h : ℕ) :=
  {e : K →₀ ℕ // e.sum (fun _ n => n) ≤ h}

noncomputable instance boundedIntegerExponentFintype (K : Type*) [Fintype K] (h : ℕ) :
    Fintype (BoundedIntegerExponent K h) := by
  classical
  let f : BoundedIntegerExponent K h → List.Vector (Option K) h :=
    fun e => paddedExponentWord e.val h e.property
  apply Fintype.ofInjective f
  intro e d hed
  apply Subtype.ext
  apply Finsupp.ext
  intro k
  have hc := congrArg (fun v : List.Vector (Option K) h =>
    (v.val : Multiset (Option K)).count (some k)) hed
  simpa only [f, paddedExponentWord_count] using hc

theorem boundedIntegerPolynomial_expansion {K : Type*} [Fintype K]
    (p : MvPolynomial K ℤ) (h : ℕ) (hp : p.totalDegree ≤ h) :
    (∑ e : BoundedIntegerExponent K h,
      MvPolynomial.C (p.coeff e.val) * MvPolynomial.monomial e.val 1) = p := by
  classical
  simp only [MvPolynomial.C_mul_monomial, mul_one]
  ext m
  rw [MvPolynomial.coeff_sum]
  by_cases hm : m.sum (fun _ n => n) ≤ h
  · let e : BoundedIntegerExponent K h := ⟨m, hm⟩
    rw [Finset.sum_eq_single e]
    · simp [e, MvPolynomial.coeff_monomial]
    · intro d _ hde
      have hdm : d.val ≠ m := fun heq => hde (Subtype.ext heq)
      simp [MvPolynomial.coeff_monomial, hdm]
    · simp
  · have hzero : p.coeff m = 0 := by
      apply MvPolynomial.notMem_support_iff.mp
      intro hmem
      exact hm ((MvPolynomial.le_totalDegree hmem).trans hp)
    rw [hzero]
    apply Finset.sum_eq_zero
    intro e _
    have hem : e.val ≠ m := fun heq => hm (heq ▸ e.property)
    simp [MvPolynomial.coeff_monomial, hem]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

instance boundedIntegerExponentInhabited (K : Type*) (h : ℕ) :
    Inhabited (BoundedIntegerExponent K h) := ⟨⟨0, by simp⟩⟩

theorem boundedIntegerExponent_card_le (K : Type*) [Fintype K] (h : ℕ) :
    Fintype.card (BoundedIntegerExponent K h) ≤ (Fintype.card K + 1) ^ h := by
  classical
  let f : BoundedIntegerExponent K h → List.Vector (Option K) h :=
    fun e => paddedExponentWord e.val h e.property
  have hf : Function.Injective f := by
    intro e d hed
    apply Subtype.ext
    apply Finsupp.ext
    intro k
    have hc := congrArg (fun v : List.Vector (Option K) h =>
      (v.val : Multiset (Option K)).count (some k)) hed
    simpa only [f, paddedExponentWord_count] using hc
  simpa using Fintype.card_le_of_injective f hf

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineResidues
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def integerJetMatrix {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℤ) (vertices : Finset α → K → ℤ)
    (rows : O → Finset α) : Matrix O J ℤ :=
  fun o j => booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (basis j)) (rows o)

theorem integerJetMatrix_apply_coefficients {α K O J : Type*} [DecidableEq α] [Fintype J]
    (basis : J → MvPolynomial K ℤ) (vertices : Finset α → K → ℤ)
    (rows : O → Finset α) (c : J → ℤ) (o : O) :
    (integerJetMatrix basis vertices rows *ᵥ c) o =
      booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
        (∑ j, MvPolynomial.C (c j) * basis j)) (rows o) := by
  simp only [map_sum, map_mul, MvPolynomial.eval_C,
    booleanCoefficient_sum, booleanCoefficient_const_mul]
  change (∑ j, integerJetMatrix basis vertices rows o j * c j) = _
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def integerBooleanInterpolant {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) : MvPolynomial K ℤ :=
  MvPolynomial.C (a ^ (h - s.card)) * ∏ r ∈ s, q r

theorem integerBooleanInterpolant_eval {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (vertices : Finset α → K → ℤ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then a else 0)
    (t : Finset α) :
    MvPolynomial.eval (vertices t) (integerBooleanInterpolant q a h s) =
      a ^ h * if s ⊆ t then 1 else 0 := by
  have hprod : (∏ r ∈ s, MvPolynomial.eval (vertices t) (q r)) =
      if s ⊆ t then a ^ s.card else 0 := by
    by_cases hst : s ⊆ t
    · rw [if_pos hst]
      calc
        _ = ∏ _r ∈ s, a := Finset.prod_congr rfl (fun r hr => by rw [hq r t, if_pos (hst hr)])
        _ = _ := by simp
    · rw [if_neg hst]
      obtain ⟨r, hrs, hrt⟩ := Finset.not_subset.mp hst
      exact Finset.prod_eq_zero hrs (by rw [hq r t, if_neg hrt])
  rw [integerBooleanInterpolant, map_mul, MvPolynomial.eval_C, map_prod, hprod]
  by_cases hst : s ⊆ t
  · simp only [if_pos hst, mul_one]
    rw [← pow_add, Nat.sub_add_cancel hs]
  · simp only [if_neg hst, mul_zero]

theorem integerBooleanInterpolant_jet {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (vertices : Finset α → K → ℤ)
    (hq : ∀ r t, MvPolynomial.eval (vertices t) (q r) = if r ∈ t then a else 0)
    (row : Finset α) :
    booleanCoefficient (fun t => MvPolynomial.eval (vertices t)
      (integerBooleanInterpolant q a h s)) row = if row = s then a ^ h else 0 := by
  simp_rw [integerBooleanInterpolant_eval q a h s hs vertices hq]
  rw [booleanCoefficient_const_mul, booleanCoefficient_monomial]
  split_ifs <;> simp

theorem integerBooleanInterpolant_degree {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℤ) (a : ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h)
    (hq : ∀ r ∈ s, (q r).totalDegree ≤ 1) :
    (integerBooleanInterpolant q a h s).totalDegree ≤ h := by
  unfold integerBooleanInterpolant
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  apply (MvPolynomial.totalDegree_finsetProd s q).trans
  calc
    _ ≤ ∑ _r ∈ s, 1 := Finset.sum_le_sum hq
    _ = s.card := by simp
    _ ≤ h := hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerAffineCube {α K : Type*} (root : K → ℤ) (difference : α → K → ℤ)
    (t : Finset α) : K → ℤ := fun k => root k + ∑ r ∈ t, difference r k

noncomputable def integerAffineNumerator {K : Type*} [Fintype K]
    (root n : K → ℤ) : MvPolynomial K ℤ :=
  ∑ k, MvPolynomial.C (n k) * (MvPolynomial.X k - MvPolynomial.C (root k))

theorem integerAffineNumerator_eval {α K : Type*} [Fintype K]
    (root n : K → ℤ) (difference : α → K → ℤ) (t : Finset α) :
    MvPolynomial.eval (integerAffineCube root difference t) (integerAffineNumerator root n) =
      ∑ r ∈ t, ∑ k, n k * difference r k := by
  simp only [integerAffineNumerator, map_sum, map_mul, map_sub,
    MvPolynomial.eval_C, MvPolynomial.eval_X, integerAffineCube, add_sub_cancel_left,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem integerAffineNumerator_boolean {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (difference : α → K → ℤ) (n : α → K → ℤ) (a : ℤ)
    (hdual : ∀ r s, (∑ k, n r k * difference s k) = if r = s then a else 0)
    (r : α) (t : Finset α) :
    MvPolynomial.eval (integerAffineCube root difference t) (integerAffineNumerator root (n r)) =
      if r ∈ t then a else 0 := by
  rw [integerAffineNumerator_eval]
  simp only [hdual, Finset.sum_ite_eq]

theorem integerAffineNumerator_degree {K : Type*} [Fintype K] (root n : K → ℤ) :
    (integerAffineNumerator root n).totalDegree ≤ 1 := by
  unfold integerAffineNumerator
  apply MvPolynomial.totalDegree_finsetSum_le
  intro k _
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C, zero_add]
  exact (MvPolynomial.totalDegree_sub_C_le _ _).trans (by simp)

theorem integerAffine_interpolation {α K : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (difference : α → K → ℤ) (n : α → K → ℤ) (a : ℤ)
    (hdual : ∀ r s, (∑ k, n r k * difference s k) = if r = s then a else 0)
    (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    ∃ p : MvPolynomial K ℤ, p.totalDegree ≤ h ∧ ∀ row : Finset α,
      booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root difference t) p) row =
        if row = s then a ^ h else 0 := by
  let q := fun r => integerAffineNumerator root (n r)
  refine ⟨integerBooleanInterpolant q a h s,
    integerBooleanInterpolant_degree q a h s hs (fun r _ => integerAffineNumerator_degree root (n r)), ?_⟩
  exact integerBooleanInterpolant_jet q a h s hs (integerAffineCube root difference)
    (integerAffineNumerator_boolean root difference n a hdual)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

theorem exists_integer_kernel_dual {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    (D : Matrix α K ℤ) (a : ℤ) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range) :
    ∃ n : α → K → ℤ, ∀ r s, (∑ k, n r k * D s k) = if r = s then a else 0 := by
  have hex (r : α) : ∃ n : K → ℤ, D *ᵥ n = a • Pi.single r 1 :=
    hperiod ((integerScalarLattice_mem a _).mpr ⟨Pi.single r 1, rfl⟩)
  choose n hn using hex
  refine ⟨n, fun r s => ?_⟩
  calc
    _ = (D *ᵥ n r) s := by simp [Matrix.mulVec, dotProduct, mul_comm]
    _ = (a • (Pi.single r 1 : α → ℤ)) s := congrFun (hn r) s
    _ = _ := by
      by_cases hrs : r = s
      · subst s; simp
      · simp [hrs, Ne.symm hrs]

theorem integerKernel_interpolation {α K : Type*} [Fintype α] [DecidableEq α] [Fintype K]
    (D : Matrix α K ℤ) (a : ℤ) (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (root : K → ℤ) (h : ℕ) (s : Finset α) (hs : s.card ≤ h) :
    ∃ p : MvPolynomial K ℤ, p.totalDegree ≤ h ∧ ∀ row : Finset α,
      booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root D t) p) row =
        if row = s then a ^ h else 0 := by
  obtain ⟨n, hn⟩ := exists_integer_kernel_dual D a hperiod
  exact integerAffine_interpolation root D n a hn h s hs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def realAffineCube {α K : Type*} (root : K → ℝ) (difference : α → K → ℝ)
    (t : Finset α) : K → ℝ := fun k => root k + ∑ r ∈ t, difference r k

noncomputable def realAffineDualPolynomial {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) : MvPolynomial K ℝ :=
  ∑ j, MvPolynomial.C (n j) *
    (MvPolynomial.X (selection j) - MvPolynomial.C (root (selection j)))

theorem realPolynomialMass_neg {K : Type*} (p : MvPolynomial K ℝ) :
    realPolynomialMass (-p) = realPolynomialMass p := by
  classical
  simp [realPolynomialMass]

theorem realPolynomialMass_sub_le {K : Type*} (p q : MvPolynomial K ℝ) :
    realPolynomialMass (p - q) ≤ realPolynomialMass p + realPolynomialMass q := by
  simpa only [sub_eq_add_neg, realPolynomialMass_neg] using realPolynomialMass_add_le p (-q)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def boundedDegreeIntegerJetMatrix {α K O : Type*} [DecidableEq α] [Fintype K]
    (root : K → ℤ) (D : Matrix α K ℤ) (h : ℕ) (rows : O → Finset α) :
    Matrix O (BoundedIntegerExponent K h) ℤ :=
  integerJetMatrix (fun e => MvPolynomial.monomial e.val 1) (integerAffineCube root D) rows

theorem boundedDegreeIntegerJetMatrix_period {α K O : Type*}
    [Fintype α] [DecidableEq α] [Fintype K] [Fintype O]
    (root : K → ℤ) (D : Matrix α K ℤ) (a : ℤ)
    (hperiod : integerScalarLattice α a ≤ D.mulVecLin.range)
    (h : ℕ) (rows : O → Finset α) (hinj : Function.Injective rows)
    (hdegree : ∀ o, (rows o).card ≤ h) :
    integerScalarLattice O (a ^ h) ≤ (boundedDegreeIntegerJetMatrix root D h rows).mulVecLin.range := by
  classical
  have hex (o : O) := integerKernel_interpolation D a hperiod root h (rows o) (hdegree o)
  choose p hp hjet using hex
  let E := boundedDegreeIntegerJetMatrix root D h rows
  have hunit (o : O) : a ^ h • Pi.single o 1 ∈ E.mulVecLin.range := by
    let c : BoundedIntegerExponent K h → ℤ := fun e => (p o).coeff e.val
    refine ⟨c, ?_⟩
    ext r
    change (integerJetMatrix (fun e : BoundedIntegerExponent K h => MvPolynomial.monomial e.val 1)
      (integerAffineCube root D) rows *ᵥ c) r = _
    rw [integerJetMatrix_apply_coefficients]
    change booleanCoefficient (fun t => MvPolynomial.eval (integerAffineCube root D t)
      (∑ e : BoundedIntegerExponent K h, MvPolynomial.C ((p o).coeff e.val) *
        MvPolynomial.monomial e.val 1)) (rows r) = _
    rw [boundedIntegerPolynomial_expansion (p o) h (hp o), hjet o]
    by_cases hro : r = o
    · subst r; simp
    · simp [hinj.eq_iff, hro]
  rintro y ⟨z, rfl⟩
  change a ^ h • z ∈ E.mulVecLin.range
  have hs : (∑ o, z o • (a ^ h • Pi.single o 1)) ∈ E.mulVecLin.range :=
    E.mulVecLin.range.sum_mem (fun o _ => E.mulVecLin.range.smul_mem (z o) (hunit o))
  convert hs using 1
  ext r
  simp [Pi.single_apply, mul_comm]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealBooleanInterpolation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def realBooleanInterpolant {α K : Type*} [DecidableEq α]
    (q : α → MvPolynomial K ℝ) (s : Finset α) : MvPolynomial K ℝ := ∏ r ∈ s, q r

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothSublevelCutoff
namespace OAI

section

namespace Erdos3

open scoped ContDiff NNReal

theorem exists_smooth_scalar_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ χ : ℝ → ℝ,
      ContDiff ℝ ∞ χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x, |x| ≤ 1 / 2 → χ x = 1) ∧
      (∀ x, 3 / 4 ≤ |x| → χ x = 0) ∧ LipschitzWith A χ := by
  let f : ContDiffBump (0 : ℝ) := ⟨1 / 2, 3 / 4, by norm_num, by norm_num⟩
  have hsmooth : ContDiff ℝ 1 f := f.contDiff
  obtain ⟨A, hA⟩ := ContDiff.lipschitzWith_of_hasCompactSupport f.hasCompactSupport hsmooth one_ne_zero
  refine ⟨A + 1, by simp, f, f.contDiff, fun x => ⟨f.nonneg, f.le_one⟩, ?_, ?_, ?_⟩
  · intro x hx
    apply f.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero] using hx
  · intro x hx
    apply f.zero_of_le_dist
    simpa only [Real.dist_eq, sub_zero] using hx
  · exact hA.weaken (by simp)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal ContDiff

theorem exists_smooth_sublevel_cutoff :
    ∃ A : ℝ≥0, 1 ≤ A ∧ ∃ ψ : ℝ → ℝ,
      ContDiff ℝ ∞ ψ ∧ (∀ t, ψ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t, |t| ≤ 1 → ψ t = 0) ∧
      (∀ t, 2 ≤ |t| → ψ t = 1) ∧ LipschitzWith A ψ := by
  obtain ⟨A, hA, χ, hs, hrange, hone, hzero, hLip⟩ := exists_smooth_scalar_cutoff
  refine ⟨A, hA, fun t => 1 - χ (t / 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (hs.comp (contDiff_id.div_const 2))
  · intro t
    exact ⟨sub_nonneg.mpr (hrange _).2, by linarith [(hrange (t / 2)).1]⟩
  · intro t ht
    have ht' : |t / 2| ≤ 1 / 2 := by rw [abs_div]; norm_num; linarith
    simp only [hone (t / 2) ht', sub_self]
  · intro t ht
    have ht' : 3 / 4 ≤ |t / 2| := by rw [abs_div]; norm_num; linarith
    simp only [hzero (t / 2) ht', sub_zero]
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hLip.dist_le_mul (x / 2) (y / 2)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    rw [Real.dist_eq, Real.dist_eq]
    have heq : (1 - χ (x / 2)) - (1 - χ (y / 2)) = -(χ (x / 2) - χ (y / 2)) := by ring
    rw [heq, abs_neg]
    exact h.trans (by nlinarith [A.coe_nonneg, abs_nonneg (x - y)])

noncomputable def sublevelCutoff {E : Type*} (ψ : ℝ → ℝ) (r : ℝ) (d : E → ℝ) (x : E) : ℝ :=
  ψ (d x / r)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SmoothedImageTest
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def mappedTest {Ω X : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (U : Ω → X) (φ : X → ℝ) : ℝ := ∫ a, φ (U a) ∂μ

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ChartCutoff
namespace OAI

section

namespace Erdos3

open Set
open scoped NNReal

noncomputable def chartCutoff {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (x : X) : ℝ := by
  classical
  exact if x ∈ e.target then ψ (e.symm x) else 0

theorem chartCutoff_range {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (hψ : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (x : X) :
    0 ≤ chartCutoff e ψ x ∧ chartCutoff e ψ x ≤ 1 := by
  classical
  by_cases hx : x ∈ e.target
  · simpa only [chartCutoff, if_pos hx] using hψ (e.symm x)
  · simp only [chartCutoff, if_neg hx, le_refl, zero_le_one, and_self]

theorem lipschitz_chartCutoff {E X : Type*} [MetricSpace E] [MetricSpace X]
    (e : OpenPartialHomeomorph E X) (ψ : E → ℝ) (A K δ : ℝ≥0) (hδ : 0 < δ)
    (hψ : ∀ v, 0 ≤ ψ v ∧ ψ v ≤ 1) (hLip : LipschitzWith A ψ)
    (hInv : LipschitzOnWith K e.symm e.target)
    (hgap : ∀ x ∈ e.target, ψ (e.symm x) ≠ 0 → ∀ y ∉ e.target, (δ : ℝ) ≤ dist x y) :
    LipschitzWith (A * K + 1 / δ) (chartCutoff e ψ) := by
  classical
  have hδ' : (0 : ℝ) < δ := hδ
  have hcross (x) (hx : x ∈ e.target) (y) (hy : y ∉ e.target) :
      dist (ψ (e.symm x)) 0 ≤ ((A * K + 1 / δ : ℝ≥0) : ℝ) * dist x y := by
    by_cases hz : ψ (e.symm x) = 0
    · rw [hz, dist_self]
      positivity
    · have hd := hgap x hx hz y hy
      calc
        _ = ψ (e.symm x) := by rw [Real.dist_eq, sub_zero, abs_of_nonneg (hψ _).1]
        _ ≤ 1 := (hψ _).2
        _ ≤ (1 / (δ : ℝ)) * dist x y := by
          have hd' := (div_le_div_iff_of_pos_right hδ').mpr hd
          simpa only [div_self (ne_of_gt hδ'), one_div_mul_eq_div] using hd'
        _ ≤ _ := by
          apply mul_le_mul_of_nonneg_right ?_ dist_nonneg
          simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one]
          exact le_add_of_nonneg_left (mul_nonneg A.coe_nonneg K.coe_nonneg)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : x ∈ e.target <;> by_cases hy : y ∈ e.target
  · simp only [chartCutoff, if_pos hx, if_pos hy]
    calc
      _ ≤ (A : ℝ) * dist (e.symm x) (e.symm y) := hLip.dist_le_mul _ _
      _ ≤ (A : ℝ) * ((K : ℝ) * dist x y) :=
        mul_le_mul_of_nonneg_left (hInv.dist_le_mul x hx y hy) A.coe_nonneg
      _ ≤ _ := by
        simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_one]
        nlinarith [mul_nonneg (one_div_nonneg.mpr δ.coe_nonneg) (dist_nonneg (x := x) (y := y))]
  · simpa only [chartCutoff, if_pos hx, if_neg hy] using hcross x hx y hy
  · simpa only [chartCutoff, if_neg hx, if_pos hy, dist_comm] using hcross y hy x hx
  · simp only [chartCutoff, if_neg hx, if_neg hy, dist_self]
    positivity

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxChartCutoff
namespace OAI

section

namespace Erdos3

open scoped NNReal ContDiff

noncomputable def coordinateBoxCutoff {ι : Type*} [Fintype ι]
    (χ : ℝ → ℝ) (r : ℝ) (v : ι → ℝ) : ℝ := ∏ i, χ (v i / r)

theorem coordinateBoxCutoff_range {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (r : ℝ) (v : ι → ℝ) :
    0 ≤ coordinateBoxCutoff χ r v ∧ coordinateBoxCutoff χ r v ≤ 1 := by
  exact ⟨Finset.prod_nonneg (fun i _ => (hχ _).1),
    Finset.prod_le_one (fun index _ => (hχ _).1) (fun index _ => (hχ _).2)⟩

theorem coordinateBoxCutoff_eq_one {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, |x| ≤ 1 / 2 → χ x = 1) {r : ℝ} (hr : 0 < r)
    (v : ι → ℝ) (hv : ∀ i, |v i| ≤ r / 2) : coordinateBoxCutoff χ r v = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply hχ
  rw [abs_div, abs_of_pos hr]
  apply (div_le_iff₀ hr).mpr
  linarith [hv i]

theorem coordinateBoxCutoff_eq_zero {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 3 / 4 ≤ |x| → χ x = 0) {r : ℝ} (hr : 0 < r)
    (v : ι → ℝ) (hv : ∃ i, 3 * r / 4 ≤ |v i|) : coordinateBoxCutoff χ r v = 0 := by
  classical
  obtain ⟨i, hi⟩ := hv
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply hχ
  rw [abs_div, abs_of_pos hr]
  apply (le_div_iff₀ hr).mpr
  linarith

theorem contDiff_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (r : ℝ) : ContDiff ℝ ∞ (coordinateBoxCutoff (ι := ι) χ r) := by
  unfold coordinateBoxCutoff
  apply contDiff_prod
  intro i _
  exact hχ.comp ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).contDiff.div_const r)

theorem hasCompactSupport_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ)
    (hχ : ∀ x, 3 / 4 ≤ |x| → χ x = 0) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (coordinateBoxCutoff (ι := ι) χ r) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : ι → ℝ) (3 * r / 4))
  intro v hv
  rw [Metric.mem_closedBall, dist_zero_right]
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 3 * r / 4)).mpr
  intro i
  rw [Real.norm_eq_abs]
  by_contra! hi
  exact hv (coordinateBoxCutoff_eq_zero χ hχ hr v ⟨i, hi.le⟩)

theorem lipschitz_coordinateBoxCutoff {ι : Type*} [Fintype ι] (χ : ℝ → ℝ) (A r : ℝ≥0)
    (hr : 0 < r) (hχ : ∀ x, 0 ≤ χ x ∧ χ x ≤ 1) (hLip : LipschitzWith A χ) :
    LipschitzWith (Fintype.card ι * A / r) (coordinateBoxCutoff (ι := ι) χ r) := by
  apply LipschitzWith.of_dist_le_mul
  intro v w
  have hr' : (0 : ℝ) < r := hr
  have hcoord (i) : |v i - w i| ≤ dist v w := by
    simpa only [Real.dist_eq] using dist_le_pi_dist v w i
  have hd (i) : |χ (v i / r) - χ (w i / r)| ≤ ((A : ℝ) / r) * dist v w := by
    have h := hLip.dist_le_mul (v i / r) (w i / r)
    rw [Real.dist_eq, Real.dist_eq, ← sub_div, abs_div, abs_of_pos hr'] at h
    apply h.trans
    calc
      (A : ℝ) * (|v i - w i| / r) = ((A : ℝ) / r) * |v i - w i| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcoord i) (by positivity)
  have hprod := abs_finset_prod_sub_prod_le Finset.univ (fun i => χ (v i / r))
    (fun i => χ (w i / r)) (B := 1) (δ := ((A : ℝ) / r) * dist v w) le_rfl (by positivity)
    (fun i _ => by rw [abs_of_nonneg (hχ _).1]; exact (hχ _).2)
    (fun i _ => by rw [abs_of_nonneg (hχ _).1]; exact (hχ _).2) (fun i _ => hd i)
  rw [Real.dist_eq]
  apply hprod.trans_eq
  simp only [Finset.card_univ, one_pow, mul_one, NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast]
  ring

end Erdos3

end

section

namespace Erdos3

open Set

theorem closedBox_subset_chart_source {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (φ : OpenPartialHomeomorph (ι → ℝ) X) {r : ℝ} (hr : 0 < r)
    (hsource : φ.source = {v | ∀ i, |v i| < r}) :
    Metric.closedBall 0 (3 * r / 4) ⊆ φ.source := by
  intro v hv
  rw [hsource]
  intro i
  rw [Metric.mem_closedBall, dist_zero_right] at hv
  have hi := (norm_le_pi_norm v i).trans hv
  rw [Real.norm_eq_abs] at hi
  linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxImageComparison
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]

def ImageTranslationBound (μ : Measure Ω) (U : Ω → (ι → ℝ)) (H : ℝ≥0) : Prop :=
  ∀ (φ : (ι → ℝ) → ℝ), Measurable φ → (∀ x, ‖φ x‖ ≤ 1) → ∀ z,
    |mappedTest μ U (fun x => φ (x + z)) - mappedTest μ U φ| ≤ H * dist z 0

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.SigmaAxisCoordinates
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {D : Type*} [Fintype D] (I : D → Type*) [∀ d, Fintype (I d)]

noncomputable def sigmaAxisCoordinates : ((Σ d, I d) → ℝ) ≃L[ℝ] (∀ d, I d → ℝ) where
  toLinearEquiv :=
    { toFun := fun x d i => x ⟨d, i⟩
      invFun := fun x s => x s.1 s.2
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

noncomputable def sigmaAxisProjection (d : D) : ((Σ d, I d) → ℝ) →L[ℝ] (I d → ℝ) :=
  ContinuousLinearMap.pi (fun i => ContinuousLinearMap.proj ⟨d, i⟩)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TwoBoxSmoothingComplex
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def twoBoxDifferenceDensity (ℓ r : ι → ℝ)
    (A B : (ι → ℝ) ≃L[ℝ] (ι → ℝ)) : (ι → ℝ) → ℝ :=
  affineBoxAverage ℓ A.toContinuousLinearMap (linearBoxDensity r B)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

variable {ι : Type*} [Fintype ι]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

variable {ι : Type*} [Fintype ι]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BooleanCubeCoordinateFrame
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α K R : Type*} [Fintype α] [DecidableEq α] [CommRing R]

noncomputable def affineSite (root : K → R) (difference : α → K → R)
    (s : Finset α) : Option K → R
  | none => 1
  | some k => root k + ∑ i ∈ s, difference i k

noncomputable def frameCoordinate (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) : Variable α K → MvPolynomial (Option K) R
  | none => X none
  | some (.inl i) => q i
  | some (.inr k) => X (some k) - C (root k) * X none - ∑ i, C (difference i k) * q i

noncomputable def liftCoordinate (root : K → R) (difference : α → K → R) :
    Option K → MvPolynomial (Variable α K) R
  | none => X none
  | some k => C (root k) * X none + ∑ i, C (difference i k) * X (some (.inl i)) + X (some (.inr k))

noncomputable def frameProjection (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) :
    MvPolynomial (Variable α K) R →ₐ[R] MvPolynomial (Option K) R :=
  aeval (frameCoordinate root difference q)

noncomputable def frameLift (root : K → R) (difference : α → K → R) :
    MvPolynomial (Option K) R →ₐ[R] MvPolynomial (Variable α K) R :=
  aeval (liftCoordinate root difference)

omit [DecidableEq α] in
theorem frameProjection_lift (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R) (P : MvPolynomial (Option K) R) :
    frameProjection root difference q (frameLift root difference P) = P := by
  have he : (frameProjection root difference q).comp (frameLift root difference) = AlgHom.id R _ := by
    apply algHom_ext
    intro v
    cases v with
    | none => simp [frameProjection, frameLift, liftCoordinate, frameCoordinate]
    | some k =>
      simp only [AlgHom.comp_apply, frameLift, aeval_X, liftCoordinate, frameProjection,
        map_add, map_sum, map_mul, aeval_C, algebraMap_eq, aeval_X, frameCoordinate, AlgHom.id_apply]
      ring
  exact AlgHom.congr_fun he P

omit [DecidableEq α] in
theorem liftCoordinate_homogeneous (root : K → R) (difference : α → K → R) (v : Option K) :
    (liftCoordinate root difference v).IsHomogeneous 1 := by
  cases v with
  | none => exact isHomogeneous_X R _
  | some k =>
    have hs : (∑ i, C (difference i k) * X (some (.inl i)) :
        MvPolynomial (Variable α K) R).IsHomogeneous 1 :=
      IsHomogeneous.sum _ _ _ (fun i _ => (isHomogeneous_X R _).C_mul (difference i k))
    exact (((isHomogeneous_X R _).C_mul (root k)).add hs).add (isHomogeneous_X R _)

omit [DecidableEq α] in
theorem frameLift_homogeneous (root : K → R) (difference : α → K → R)
    {P : MvPolynomial (Option K) R} {h : ℕ} (hP : P.IsHomogeneous h) :
    (frameLift root difference P).IsHomogeneous h := by
  simpa only [frameLift, Nat.one_mul] using
    hP.aeval (liftCoordinate root difference) (liftCoordinate_homogeneous root difference)

theorem frameCoordinate_eval (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (s : Finset α) (v : Variable α K) :
    eval (affineSite root difference s) (frameCoordinate root difference q v) = site s v := by
  cases v with
  | none => simp [frameCoordinate, affineSite, site]
  | some v =>
    cases v with
    | inl i => exact hq i s
    | inr k =>
      simp only [frameCoordinate, map_sub, map_mul, map_sum, eval_X, eval_C, affineSite,
        hq, mul_one, mul_ite, mul_zero, site]
      simp

theorem frameProjection_eval (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (s : Finset α) (P : MvPolynomial (Variable α K) R) :
    eval (affineSite root difference s) (frameProjection root difference q P) = eval (site s) P := by
  have he : (aeval (affineSite root difference s)).comp (frameProjection root difference q) =
      aeval (site (β := K) s) := by
    apply algHom_ext
    intro v
    simpa only [AlgHom.comp_apply, frameProjection, aeval_X, aeval_eq_eval] using
      frameCoordinate_eval root difference q hq s v
  exact AlgHom.congr_fun he P

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealKernelJetInverse
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

noncomputable def realJetMatrix {α K O J : Type*} [DecidableEq α]
    (basis : J → MvPolynomial K ℝ) (vertices : Finset α → K → ℝ)
    (rows : O → Finset α) : Matrix O J ℝ :=
  fun o j => booleanCoefficient (fun t => MvPolynomial.eval (vertices t) (basis j)) (rows o)

noncomputable def boundedDegreeRealJetMatrix {α K O : Type*} [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (h : ℕ)
    (rows : O → Finset α) : Matrix O (BoundedIntegerExponent K h) ℝ :=
  realJetMatrix (fun e => MvPolynomial.monomial e.val 1)
    (realAffineCube root difference) rows

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def realDifferencePivot {α K : Type*} (difference : α → K → ℝ)
    (selection : α → K) : Matrix α α ℝ := fun i j => difference i (selection j)

noncomputable def realKernelInterpolant {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (s : Finset α) : MvPolynomial K ℝ :=
  realBooleanInterpolant (fun r => realAffineDualPolynomial root selection
    (fun j => (realDifferencePivot difference selection)⁻¹ j r)) s

end Erdos3

end

section

namespace Erdos3

noncomputable def realKernelJetRightInverse {α K O : Type*}
    [Fintype α] [DecidableEq α]
    (root : K → ℝ) (difference : α → K → ℝ) (selection : α → K)
    (h : ℕ) (rows : O → Finset α) : Matrix (BoundedIntegerExponent K h) O ℝ :=
  fun e o => (realKernelInterpolant root difference selection (rows o)).coeff e.val

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.NormalizedIntegerDual
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

variable {α K R V : Type*} [Fintype α] [DecidableEq α] [CommRing R]
  [AddCommGroup V] [Module R V]

theorem frameLift_siteEvaluation (root : K → R) (difference : α → K → R)
    (q : α → MvPolynomial (Option K) R)
    (hq : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (P : MvPolynomial (Option K) R) :
    siteEvaluation (frameLift root difference P) = fun s => eval (affineSite root difference s) P := by
  funext s
  change eval (site s) (frameLift root difference P) = _
  rw [← frameProjection_eval root difference q hq, frameProjection_lift]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators

noncomputable def homogeneousDual {I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (selection : I → K) (n : I → R) : MvPolynomial (Option K) R :=
  ∑ j, C (n j) * (X (some (selection j)) - C (root (selection j)) * X none)

theorem homogeneousDual_homogeneous {I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (selection : I → K) (n : I → R) :
    (homogeneousDual root selection n).IsHomogeneous 1 := by
  exact IsHomogeneous.sum _ _ _ (fun j _ =>
    ((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root (selection j)))).C_mul (n j))

theorem homogeneousDual_eval {α I K R : Type*} [Fintype I] [CommRing R]
    (root : K → R) (difference : α → K → R) (selection : I → K) (n : I → R)
    (s : Finset α) :
    eval (affineSite root difference s) (homogeneousDual root selection n) =
      ∑ i ∈ s, ∑ j, n j * difference i (selection j) := by
  simp only [homogeneousDual, map_sum, map_mul, map_sub, eval_C, eval_X,
    affineSite, mul_one, add_sub_cancel_left, Finset.mul_sum]
  exact Finset.sum_comm

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

theorem homogeneousDual_mass {I K : Type*} [Fintype I]
    (root : K → ℝ) (selection : I → K) (n : I → ℝ) {H N : ℝ}
    (hN : 0 ≤ N) (hroot : ∀ j, |root (selection j)| ≤ H) (hn : ∀ j, |n j| ≤ N) :
    realPolynomialMass (homogeneousDual root selection n) ≤ (Fintype.card I : ℝ) * (N * (1 + H)) := by
  apply (realPolynomialMass_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : I, N * (1 + H) := by
      apply Finset.sum_le_sum
      intro j _
      have hr : realPolynomialMass (C (root (selection j)) * X (none : Option K)) ≤ H := by
        exact (realPolynomialMass_C_mul_le (root (selection j)) (X (none : Option K))).trans
            (by simpa only [realPolynomialMass_X, mul_one] using hroot j)
      have hs : realPolynomialMass (X (some (selection j)) - C (root (selection j)) * X none) ≤ 1 + H := by
        exact (realPolynomialMass_sub_le _ _).trans (by rw [realPolynomialMass_X]; linarith)
      exact (realPolynomialMass_C_mul_le _ _).trans
        (mul_le_mul (hn j) hs (realPolynomialMass_nonneg _) hN)
    _ = _ := by simp

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

noncomputable def scaledFrameForm {α K R : Type*} [Fintype α] [CommRing R]
    (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) : Form α K → MvPolynomial (Option K) R
  | .coordinate none => C a * X none
  | .coordinate (some (.inl i)) => numerator i
  | .coordinate (some (.inr k)) =>
      C a * (X (some k) - C (root k) * X none) - ∑ i, C (difference i k) * numerator i
  | .difference i => numerator i - C a * X none

theorem scaledFrameForm_homogeneous {α K R : Type*} [Fintype α] [CommRing R]
    (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R)
    (hn : ∀ i, (numerator i).IsHomogeneous 1) (f : Form α K) :
    (scaledFrameForm root difference a numerator f).IsHomogeneous 1 := by
  cases f with
  | coordinate v =>
    cases v with
    | none => exact (isHomogeneous_X R _).C_mul a
    | some v =>
      cases v with
      | inl i => exact hn i
      | inr k =>
        apply (((isHomogeneous_X R _).sub ((isHomogeneous_X R _).C_mul (root k))).C_mul a).sub
        exact IsHomogeneous.sum _ _ _ (fun i _ => (hn i).C_mul (difference i k))
  | difference i => exact (hn i).sub ((isHomogeneous_X R _).C_mul a)

theorem scaledFrameForm_map {α K R S : Type*} [Fintype α] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) (q : α → MvPolynomial (Option K) S)
    (hn : ∀ i, map ρ (numerator i) = C (ρ a) * q i) (f : Form α K) :
    map ρ (scaledFrameForm root difference a numerator f) =
      C (ρ a) * frameProjection (fun k => ρ (root k)) (fun i k => ρ (difference i k)) q (formPolynomial f) := by
  cases f with
  | coordinate v =>
    cases v with
    | none => simp [scaledFrameForm, frameProjection, formPolynomial, frameCoordinate]
    | some v =>
      cases v with
      | inl i => simpa only [scaledFrameForm, frameProjection, formPolynomial, aeval_X, frameCoordinate] using hn i
      | inr k =>
        have hs : (∑ i, C (ρ (difference i k)) * (C (ρ a) * q i)) =
            C (ρ a) * ∑ i, C (ρ (difference i k)) * q i := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        simp only [scaledFrameForm, map_sub, map_mul, map_sum, map_C, map_X, hn,
          frameProjection, formPolynomial, aeval_X, frameCoordinate]
        rw [hs]
        ring
  | difference i =>
    simp only [scaledFrameForm, map_sub, map_mul, map_C, map_X, hn,
      frameProjection, formPolynomial, aeval_X, frameCoordinate]
    ring

theorem affineSite_map {α K R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (s : Finset α) :
    affineSite (fun k => ρ (root k)) (fun i k => ρ (difference i k)) s = ρ ∘ affineSite root difference s := by
  funext v
  cases v <;> simp [affineSite]

theorem affineSite_eval_map {α K R S : Type*} [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (s : Finset α)
    (P : MvPolynomial (Option K) R) :
    eval (affineSite (fun k => ρ (root k)) (fun i k => ρ (difference i k)) s) (map ρ P) =
      ρ (eval (affineSite root difference s) P) := by
  rw [affineSite_map]
  exact (map_eval ρ _ P).symm

theorem scaledFrameProduct_map {α K R S : Type*} [Fintype α] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (difference : α → K → R) (a : R)
    (numerator : α → MvPolynomial (Option K) R) (q : α → MvPolynomial (Option K) S)
    (hn : ∀ i, map ρ (numerator i) = C (ρ a) * q i) (l : List (Form α K)) :
    map ρ ((l.map (scaledFrameForm root difference a numerator)).prod) =
      C ((ρ a) ^ l.length) *
        frameProjection (fun k => ρ (root k)) (fun i k => ρ (difference i k)) q (formProduct l) := by
  induction l with
  | nil => simp [formProduct_nil]
  | cons f l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, scaledFrameForm_map ρ root difference a numerator q hn,
      ih, List.length_cons, pow_succ, map_mul, formProduct_cons]
    ring

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

variable {α K V : Type*} [Fintype α] [DecidableEq α]
  [AddCommGroup V] [Module ℝ V]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators

def integerDifferencePivot {α K : Type*} (difference : α → K → ℤ) (selection : α → K) :
    Matrix α α ℤ := fun i j => difference i (selection j)

theorem integerDifferencePivot_adjugate_dual {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) (i s : α) :
    (∑ j, (integerDifferencePivot difference selection).adjugate j i * difference s (selection j)) =
      if i = s then (integerDifferencePivot difference selection).det else 0 := by
  have he := congrFun (congrFun (Matrix.mul_adjugate (integerDifferencePivot difference selection)) s) i
  simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply,
    mul_ite, ite_mul, mul_one, one_mul, mul_zero, zero_mul, integerDifferencePivot, mul_comm, eq_comm] using he

noncomputable def integerPivotNumerator {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) :
    MvPolynomial (Option K) ℤ :=
  homogeneousDual root selection (fun j => (integerDifferencePivot difference selection).adjugate j i)

theorem integerPivotNumerator_homogeneous {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) :
    (integerPivotNumerator root difference selection i).IsHomogeneous 1 :=
  homogeneousDual_homogeneous root selection _

theorem integerPivotNumerator_eval {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) (i : α) (s : Finset α) :
    eval (affineSite root difference s) (integerPivotNumerator root difference selection i) =
      if i ∈ s then (integerDifferencePivot difference selection).det else 0 := by
  rw [integerPivotNumerator, homogeneousDual_eval]
  simp only [integerDifferencePivot_adjugate_dual, Finset.sum_ite_eq]

theorem integerDifferencePivot_det_cast {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) :
    ((integerDifferencePivot difference selection).det : ℝ) =
      (realDifferencePivot (fun i k => (difference i k : ℝ)) selection).det :=
  (Int.castRingHom ℝ).map_det _

theorem integerDifferencePivot_adjugate_cast {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) (i j : α) :
    ((integerDifferencePivot difference selection).adjugate i j : ℝ) =
      (realDifferencePivot (fun i k => (difference i k : ℝ)) selection).adjugate i j := by
  exact congrFun (congrFun ((Int.castRingHom ℝ).map_adjugate (integerDifferencePivot difference selection)) i) j

theorem integerDifferencePivot_det_bound {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) {D : ℝ}
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) :
    |((integerDifferencePivot difference selection).det : ℝ)| ≤
      (Fintype.card α).factorial * D ^ Fintype.card α := by
  rw [integerDifferencePivot_det_cast]
  exact matrix_det_abs_le_uniform_bound _ hdiff

theorem integerDifferencePivot_adjugate_bound {α K : Type*} [Fintype α] [DecidableEq α]
    (difference : α → K → ℤ) (selection : α → K) {D : ℝ}
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) (i j : α) :
    |((integerDifferencePivot difference selection).adjugate i j : ℝ)| ≤
      (Fintype.card α).factorial * D ^ (Fintype.card α - 1) := by
  rw [integerDifferencePivot_adjugate_cast]
  exact matrix_adjugate_entry_abs_le _ hdiff i j

theorem homogeneousDual_map {I K R S : Type*} [Fintype I] [CommRing R] [CommRing S]
    (ρ : R →+* S) (root : K → R) (selection : I → K) (n : I → R) :
    map ρ (homogeneousDual root selection n) =
      homogeneousDual (fun k => ρ (root k)) selection (fun i => ρ (n i)) := by
  simp only [homogeneousDual, map_sum, map_mul, map_sub, map_C, map_X]

theorem integerPivotNumerator_mass {α K : Type*} [Fintype α] [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K) {H D : ℝ} (hD : 0 ≤ D)
    (hroot : ∀ j, |(root (selection j) : ℝ)| ≤ H)
    (hdiff : ∀ i j, |(difference i (selection j) : ℝ)| ≤ D) (i : α) :
    realPolynomialMass (map (Int.castRingHom ℝ) (integerPivotNumerator root difference selection i)) ≤
      (Fintype.card α : ℝ) *
        (((Fintype.card α).factorial * D ^ (Fintype.card α - 1)) * (1 + H)) := by
  rw [integerPivotNumerator, homogeneousDual_map]
  apply homogeneousDual_mass _ selection _ (by positivity) hroot
  intro j
  exact integerDifferencePivot_adjugate_bound difference selection hdiff j i

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

noncomputable def normalizedIntegerDual {α K : Type*} (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ) (i : α) : MvPolynomial (Option K) ℝ :=
  (a : ℝ)⁻¹ • map (Int.castRingHom ℝ) (numerator i)

theorem normalizedIntegerDual_clear {α K : Type*} (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ) (i : α) :
    map (Int.castRingHom ℝ) (numerator i) = C (a : ℝ) * normalizedIntegerDual a numerator i := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  rw [← smul_eq_C_mul, normalizedIntegerDual, smul_smul, mul_inv_cancel₀ ha', one_smul]

theorem normalizedIntegerDual_boolean {α K : Type*} [DecidableEq α]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hn : ∀ i s, eval (affineSite root difference s) (numerator i) = if i ∈ s then a else 0)
    (i : α) (s : Finset α) :
    eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s)
      (normalizedIntegerDual a numerator i) = if i ∈ s then 1 else 0 := by
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have he := affineSite_eval_map (Int.castRingHom ℝ) root difference s (numerator i)
  simp only [Int.coe_castRingHom] at he
  rw [normalizedIntegerDual, smul_eval, he, hn]
  by_cases hi : i ∈ s <;> simp [hi, ha']

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegralAffineModeRemoval
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped BigOperators Classical

def integerFormMassBound (n : ℕ) (H D A B : ℝ) : ℝ := A * (2 + H) + ((n : ℝ) * D + 1) * B

theorem scaledFrameForm_mass {α K : Type*} [Fintype α]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ)
    (numerator : α → MvPolynomial (Option K) ℤ) {H D A B : ℝ}
    (hH : 0 ≤ H) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (ha : |(a : ℝ)| ≤ A) (hn : ∀ i, realPolynomialMass (map (Int.castRingHom ℝ) (numerator i)) ≤ B)
    (f : Form α K) :
    realPolynomialMass (map (Int.castRingHom ℝ) (scaledFrameForm root difference a numerator f)) ≤
      integerFormMassBound (Fintype.card α) H D A B := by
  have hcross : 0 ≤ (Fintype.card α : ℝ) * D * B := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hD) hB
  have hax : realPolynomialMass (C (a : ℝ) * X (none : Option K)) ≤ A := by
    exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using ha)
  have hbase (k : K) : realPolynomialMass (X (some k) - C (root k : ℝ) * X (none : Option K)) ≤ 1 + H := by
    have hr : realPolynomialMass (C (root k : ℝ) * X (none : Option K)) ≤ H := by
      exact (realPolynomialMass_C_mul_le _ _).trans (by simpa only [realPolynomialMass_X, mul_one] using hroot k)
    exact (realPolynomialMass_sub_le _ _).trans (by rw [realPolynomialMass_X]; linarith)
  cases f with
  | coordinate v =>
    cases v with
    | none =>
      simp only [scaledFrameForm, map_mul, map_C, map_X, Int.coe_castRingHom]
      exact hax.trans (by unfold integerFormMassBound; nlinarith)
    | some v =>
      cases v with
      | inl i =>
        exact (hn i).trans (by unfold integerFormMassBound; nlinarith)
      | inr k =>
        have hp : realPolynomialMass (C (a : ℝ) * (X (some k) - C (root k : ℝ) * X none)) ≤ A * (1 + H) :=
          (realPolynomialMass_C_mul_le _ _).trans
            (mul_le_mul ha (hbase k) (realPolynomialMass_nonneg _) hA)
        have hs : realPolynomialMass (∑ i, C (difference i k : ℝ) * map (Int.castRingHom ℝ) (numerator i)) ≤
            (Fintype.card α : ℝ) * (D * B) := by
          apply (realPolynomialMass_sum_le _ _).trans
          calc
            _ ≤ ∑ _i : α, D * B := by
              apply Finset.sum_le_sum
              intro i _
              exact (realPolynomialMass_C_mul_le _ _).trans
                (mul_le_mul (hdiff i k) (hn i) (realPolynomialMass_nonneg _) hD)
            _ = _ := by simp
        simp only [scaledFrameForm, map_sub, map_mul, map_sum, map_C, map_X, Int.coe_castRingHom]
        apply (realPolynomialMass_sub_le _ _).trans
        unfold integerFormMassBound
        nlinarith
  | difference i =>
    simp only [scaledFrameForm, map_sub, map_mul, map_C, map_X, Int.coe_castRingHom]
    apply (realPolynomialMass_sub_le _ _).trans
    have hi := hn i
    unfold integerFormMassBound
    nlinarith

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

theorem exists_affine_vanishing_labels {α K R V : Type*} [Fintype α] [DecidableEq α]
    [CommRing R] [AddCommGroup V] [Module R V]
    (root : K → R) (difference : α → K → R) (q : α → MvPolynomial (Option K) R)
    (hdual : ∀ i s, eval (affineSite root difference s) (q i) = if i ∈ s then 1 else 0)
    (Λ : MvPolynomial (Option K) R →ₗ[R] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ P = L (fun s => eval (affineSite root difference s) P)) :
    ∃ l : List (Form α K), l.length = h ∧
      (∀ s, eval (affineSite root difference s) (frameProjection root difference q (formProduct l)) = 0) ∧
      Λ (frameProjection root difference q (formProduct l)) ≠ 0 := by
  let E := frameProjection root difference q
  let Λ' := Λ.comp E.toLinearMap
  have hn : ¬ ∃ L : (Finset α → R) →ₗ[R] V,
      ∀ P, P.IsHomogeneous h → Λ' P = L (siteEvaluation P) := by
    rintro ⟨L, hL⟩
    apply hnonfactor
    refine ⟨L, ?_⟩
    intro P hP
    have he := hL (frameLift root difference P) (frameLift_homogeneous root difference hP)
    change Λ (frameProjection root difference q (frameLift root difference P)) = _ at he
    rw [frameProjection_lift, frameLift_siteEvaluation root difference q hdual] at he
    exact he
  obtain ⟨l, hl, hz, hΛ⟩ := exists_vanishing_product_of_nonfactor Λ' h hn
  refine ⟨l, hl, ?_, hΛ⟩
  intro s
  exact (frameProjection_eval root difference q hdual s (formProduct l)).trans (hz s)

theorem exists_integer_vanishing_product {α K V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V]
    (root : K → ℤ) (difference : α → K → ℤ) (a : ℤ) (ha : a ≠ 0)
    (numerator : α → MvPolynomial (Option K) ℤ)
    (hlinear : ∀ i, (numerator i).IsHomogeneous 1)
    (hdual : ∀ i s, eval (affineSite root difference s) (numerator i) = if i ∈ s then a else 0)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P =
        L (fun s => eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) P)) :
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧ ∃ f : Form α K, P = scaledFrameForm root difference a numerator f) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      Λ (map (Int.castRingHom ℝ) forms.prod) ≠ 0 := by
  let q := normalizedIntegerDual a numerator
  obtain ⟨l, hl, hz, hΛ⟩ := exists_affine_vanishing_labels
    (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) q
    (normalizedIntegerDual_boolean root difference a ha numerator hdual) Λ h hnonfactor
  have hm := scaledFrameProduct_map (Int.castRingHom ℝ) root difference a numerator q
    (normalizedIntegerDual_clear a ha numerator) l
  simp only [Int.coe_castRingHom] at hm
  let forms := l.map (scaledFrameForm root difference a numerator)
  have hzero (s : Finset α) : eval (affineSite root difference s) forms.prod = 0 := by
    have he := affineSite_eval_map (Int.castRingHom ℝ) root difference s forms.prod
    simp only [Int.coe_castRingHom] at he
    have hc : ((eval (affineSite root difference s) forms.prod : ℤ) : ℝ) = 0 := by
      rw [← he]
      change eval _ (map (Int.castRingHom ℝ) ((l.map (scaledFrameForm root difference a numerator)).prod)) = 0
      rw [hm, map_mul, eval_C, hz, mul_zero]
    exact_mod_cast hc
  refine ⟨forms, ?_, ?_, ?_, ?_⟩
  · simpa only [forms, List.length_map] using hl
  · intro P hP
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hP
    exact ⟨scaledFrameForm_homogeneous root difference a numerator hlinear f, f, rfl⟩
  · intro s
    have hp : (forms.map (fun P => eval (affineSite root difference s) P)).prod = 0 := by
      simpa only [map_list_prod] using hzero s
    exact List.mem_map.mp (List.prod_eq_zero_iff.mp hp)
  · change Λ (map (Int.castRingHom ℝ) ((l.map (scaledFrameForm root difference a numerator)).prod)) ≠ 0
    rw [hm, ← smul_eq_C_mul, map_smul]
    have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    exact smul_ne_zero (pow_ne_zero _ ha') hΛ

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open MvPolynomial
open scoped Classical

theorem exists_bounded_integer_vanishing_product {α K V : Type*} [Fintype α] [DecidableEq α]
    [AddCommGroup V] [Module ℝ V]
    (root : K → ℤ) (difference : α → K → ℤ) (selection : α → K)
    (hdet : (integerDifferencePivot difference selection).det ≠ 0)
    {H D : ℝ} (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hroot : ∀ k, |(root k : ℝ)| ≤ H) (hdiff : ∀ i k, |(difference i k : ℝ)| ≤ D)
    (Λ : MvPolynomial (Option K) ℝ →ₗ[ℝ] V) (h : ℕ)
    (hnonfactor : ¬ ∃ L : (Finset α → ℝ) →ₗ[ℝ] V,
      ∀ P, P.IsHomogeneous h → Λ P =
        L (fun s => eval (affineSite (fun k => (root k : ℝ)) (fun i k => (difference i k : ℝ)) s) P)) :
    let A := ((Fintype.card α).factorial : ℝ) * D ^ Fintype.card α
    let B := (Fintype.card α : ℝ) *
      ((((Fintype.card α).factorial : ℝ) * D ^ (Fintype.card α - 1)) * (1 + H))
    ∃ forms : List (MvPolynomial (Option K) ℤ), forms.length = h ∧
      (∀ P ∈ forms, P.IsHomogeneous 1 ∧
        realPolynomialMass (map (Int.castRingHom ℝ) P) ≤ integerFormMassBound (Fintype.card α) H D A B) ∧
      (∀ s : Finset α, ∃ P ∈ forms, eval (affineSite root difference s) P = 0) ∧
      Λ (map (Int.castRingHom ℝ) forms.prod) ≠ 0 := by
  intro A B
  let a := (integerDifferencePivot difference selection).det
  let numerator := integerPivotNumerator root difference selection
  obtain ⟨forms, hlen, hforms, hz, hΛ⟩ := exists_integer_vanishing_product root difference a hdet numerator
    (integerPivotNumerator_homogeneous root difference selection)
    (integerPivotNumerator_eval root difference selection) Λ h hnonfactor
  refine ⟨forms, hlen, ?_, hz, hΛ⟩
  intro P hP
  obtain ⟨hhom, f, rfl⟩ := hforms P hP
  refine ⟨hhom, scaledFrameForm_mass root difference a numerator hH hD
    (show 0 ≤ A by dsimp [A]; positivity) (show 0 ≤ B by dsimp [B]; positivity) hroot hdiff ?_ ?_ f⟩
  · exact integerDifferencePivot_det_bound difference selection (fun i j => hdiff i (selection j))
  · intro i
    exact integerPivotNumerator_mass root difference selection hD
      (fun j => hroot (selection j)) (fun i j => hdiff i (selection j)) i

end Erdos3.BooleanCubeKernel

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.PivotNormalizedMatrix
namespace OAI

section

namespace Erdos3

open scoped Matrix BigOperators

variable {I : Type*} [Fintype I] [DecidableEq I]

noncomputable def normalizedIntegerPivot (A : Matrix I I ℤ) (S P : I → ℝ) : Matrix I I ℝ :=
  Matrix.diagonal (fun i => (P i)⁻¹) * A.map (Int.castRingHom ℝ) * Matrix.diagonal S

theorem normalizedIntegerPivot_abs_det (A : Matrix I I ℤ) (S P : I → ℝ)
    (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    |(normalizedIntegerPivot A S P).det| =
      (A.det.natAbs : ℝ) * (∏ i, S i) / (∏ i, P i) := by
  have hprodS : 0 < ∏ i, S i := Finset.prod_pos fun i _ => hS i
  have hprodP : 0 < ∏ i, P i := Finset.prod_pos fun i _ => hP i
  have hd : (A.map (Int.castRingHom ℝ)).det = (A.det : ℝ) :=
    (RingHom.map_det (Int.castRingHom ℝ) A).symm
  simp only [normalizedIntegerPivot, Matrix.det_mul, Matrix.det_diagonal,
    hd, Finset.prod_inv_distrib, abs_mul, abs_inv, abs_of_pos hprodS, abs_of_pos hprodP,
    Nat.cast_natAbs, Int.cast_abs, div_eq_mul_inv]
  ring

theorem normalizedIntegerPivot_det_ne_zero (A : Matrix I I ℤ) (hA : A.det ≠ 0)
    (S P : I → ℝ) (hS : ∀ i, 0 < S i) (hP : ∀ i, 0 < P i) :
    (normalizedIntegerPivot A S P).det ≠ 0 := by
  apply abs_pos.mp
  rw [normalizedIntegerPivot_abs_det A S P hS hP]
  have hq : (0 : ℝ) < A.det.natAbs := by exact_mod_cast Int.natAbs_pos.mpr hA
  exact div_pos (mul_pos hq (Finset.prod_pos fun i _ => hS i))
    (Finset.prod_pos fun i _ => hP i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DiagonalImageDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem realDensityMeasure_integral {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) (φ : X → ℝ) :
    (∫ x, φ x ∂realDensityMeasure μ f) = ∫ x, f x * φ x ∂μ := by
  unfold realDensityMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hf.ennreal_ofReal
    (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hf0 _), smul_eq_mul]

theorem realDensityMeasure_finite {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    IsFiniteMeasure (realDensityMeasure μ f) := by
  constructor
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ]
  exact ENNReal.ofReal_lt_top

theorem realDensityMeasure_real_univ {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (f : X → ℝ) (hf : Integrable f μ) (hf0 : ∀ x, 0 ≤ f x) :
    (realDensityMeasure μ f).real Set.univ = ∫ x, f x ∂μ := by
  change (realDensityMeasure μ f Set.univ).toReal = _
  rw [realDensityMeasure_apply μ f hf hf0 MeasurableSet.univ, Measure.restrict_univ,
    ENNReal.toReal_ofReal (integral_nonneg hf0)]

theorem mappedTest_eq_density {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (μ : Measure Ω) (ν : Measure X) (U : Ω → X) (hU : Measurable U)
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x)
    (hmap : Measure.map U μ = realDensityMeasure ν f)
    (φ : X → ℝ) (hφ : Measurable φ) : mappedTest μ U φ = ∫ x, f x * φ x ∂ν := by
  change (∫ a, φ (U a) ∂μ) = _
  rw [← integral_map hU.aemeasurable hφ.aestronglyMeasurable, hmap,
    realDensityMeasure_integral ν f hf hf0]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal Classical

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

noncomputable def fixedSpatialBlockDensity
    (μ : Measure T) (center : X → ℝ) (rest : T → X → ℝ)
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : (X → ℝ) → ℝ :=
  haarShiftDensity μ (fun t => center + rest t)
    (twoBoxDifferenceDensity (fun _ => 1) (fun _ => 1)
      (A.trans (ContinuousLinearEquiv.neg ℝ)) B)

noncomputable def fixedSpatialBlockDensityCap
    (B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : ℝ≥0 :=
  linearBoxDensityCap (fun _ => 1) (fun _ => zero_lt_one) B

noncomputable def fixedSpatialBlockDensityLipschitz
    (A B : (X → ℝ) ≃L[ℝ] (X → ℝ)) : ℝ≥0 :=
  (fixedSpatialBlockDensityCap B *
    boxWindowTranslationBound (fun _ : X => 1) (fun _ => zero_lt_one)) *
    ‖(A.trans (ContinuousLinearEquiv.neg ℝ)).symm.toContinuousLinearMap‖₊

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

theorem boundedDensity_mass {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (f : X → ℝ) (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {B : ℝ} (hB : ∀ x, f x ≤ B)
    [IsProbabilityMeasure (realDensityMeasure μ f)] : Integrable f μ ∧ (∫ x, f x ∂μ) = 1 := by
  have hi : Integrable f μ := (integrable_const B).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
      exact hB x))
  refine ⟨hi, ?_⟩
  have he := realDensityMeasure_real_univ μ f hi hf0
  change ((realDensityMeasure μ f) Set.univ).toReal = _ at he
  rw [measure_univ, ENNReal.toReal_one] at he
  exact he.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

variable {X : Type*} [Fintype X]

variable [DecidableEq X]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators Classical ENNReal

variable {X T : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace T]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {ι : Type*} [Fintype ι]

noncomputable def diagonalImageDensity (d : ι → ℝ)
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  (∏ i, |d i|)⁻¹ * f (fun i => x i / d i)

end Erdos3

end

end OAI

end


