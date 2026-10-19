-- Prove2me | Definitions.Def_OAIE3v2B215
-- name    : OAIE3v2B215
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:18:04.28559+00:00
-- url     : https://prove2.me/theorems/b6416d4b-2903-4a76-942a-b99d2aa14431
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 219 of 311
-- statement:
--   Definitions bundle 219 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B179`, `OAIE3v2B181`, `OAIE3v2B185`, `OAIE3v2B188`, `OAIE3v2B193`, `OAIE3v2B195` of this split.
--
--   Modules: `Estimates/AxisCompression.lean`, `Estimates/DiagonalRowTransfer.lean`, `Estimates/NativeCommonModelQuadruples.lean`, `Estimates/NativeOrbitFreezing.lean`, `Estimates/NativeOrbitOuterControl.lean`, `Lattices/LatticeNormalizedRefiltering.lean`, `Lattices/PositivePartitionIntegerExpansion.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B179
import Definitions.Def_OAIE3v2B181
import Definitions.Def_OAIE3v2B185
import Definitions.Def_OAIE3v2B188
import Definitions.Def_OAIE3v2B193
import Definitions.Def_OAIE3v2B195

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.LatticeNormalizedRefiltering
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration VectorPolynomial
open scoped TensorProduct

theorem exists_lattice_normalized_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J L : Type*} [Fintype σ] [Fintype J]
      [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L s d) (w : Fin d → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ w i}))
      (eta : J → L →ₗ[ℚ] ℚ) (p : ℝ), 0 ≤ p → D.GeometryComplexityLE p →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      ∀ A : σ → ℝ, (∀ i, Real.exp ((p + C) ^ C) ≤ A i) →
      ∀ g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group,
      (∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
        (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g) p) →
      ∃ (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (v : Fin d → D.filtration.AssociatedGraded) (m : ℕ) (κ : D.RealGroup)
        (E b R : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis w hF) w W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis w hF).repr (v i) k) ≤
          (p + C) ^ C) ∧
        (∀ j x, x ∈ D.filtration.realGradedRefiltrationLayer W s → realifyFunctional (eta j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ D.realLattice ∧
        E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
        (∀ α i, |(D.basis.baseChange ℝ).repr
          (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale A α) ∧
        ((fun z : (σ →₀ ℕ) × Fin d => (D.basis.baseChange ℝ).repr
          (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) z.1) z.2) ∈ realDenominatorGrid m) ∧
        coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) 0 = 0 ∧
        (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) α ∈
          D.filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
        (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) ∈
          realificationLieSubalgebra (D.filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, _, hnormalize⟩ := exists_native_polynomial_normalization s
  obtain ⟨k, _, hcommon⟩ := exists_common_refiltered_factorization s
  obtain ⟨l, _, hleft⟩ := exists_native_slow_left_constant_bound s
  let N : Polynomial ℕ := (Polynomial.X + Polynomial.C c) ^ c
  let F : Polynomial ℕ := (Polynomial.X + 2) ^ k
  let H : Polynomial ℕ := ((Polynomial.X + 2) ^ 2 + 2) ^ 63 + 1
  let Q : Polynomial ℕ := Polynomial.X + N + F
  let P : Polynomial ℕ := F + H + (Q + Polynomial.C l) ^ l
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ J L _ _ _ _ d _ _ _ D w hF eta p hp hD hσ hJ A hA g hfactor
  let q := p + (p + c) ^ c + (p + 2) ^ k
  have hn0 : 0 ≤ (p + c) ^ c := by positivity
  have hf0 : 0 ≤ (p + 2) ^ k := by positivity
  have hh0 : 0 ≤ ((p + 2) ^ 2 + 2) ^ 63 + 1 := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hnq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hfq : (p + 2) ^ k ≤ q := by dsimp [q]; linarith
  have hb : (p + 2) ^ k + (((p + 2) ^ 2 + 2) ^ 63 + 1) + (q + l) ^ l ≤ (p + C) ^ C := by
    simpa [P, Q, N, F, H, q, Polynomial.eval₂_pow] using hbudget p hp
  have hl0 : 0 ≤ (q + l) ^ l := by positivity
  have hfC : (p + 2) ^ k ≤ (p + C) ^ C := by linarith
  have hhC : ((p + 2) ^ 2 + 2) ^ 63 + 1 ≤ (p + C) ^ C := by linarith
  have hlC : (q + l) ^ l ≤ (p + C) ^ C := by linarith
  have hApos : ∀ i, 0 < A i := fun i => (Real.exp_pos _).trans_le (hA i)
  obtain ⟨a, κ, g₀, ha, hκ, hnormalizeEq, hg₀zero, hsymbol⟩ :=
    hnormalize D w hF (fun _ : σ => 1) p hp hD g
  have hfactor₀ : ∀ j, D.filtration.ControlledSymbolFactorization D.basis w hF (eta j) A
      (D.filtration.realPolynomialSymbolHom D.basis w hF (fun _ => 1) g₀) p := by
    intro j
    rw [hsymbol]
    exact hfactor j
  obtain ⟨W, v, m, e₀, b, R, hv, hW, hheight, hfreq, hm, hmp, hebr,
      hmid, he, hR, _, hR0, hb0, hvalues⟩ :=
    hcommon D.filtration D.basis w hF eta p hp
      (by simpa only [Fintype.card_fin] using hD.1) hσ hJ (fun i j k => hD.2.2.1 i j k)
      A (fun i => (Real.exp_le_exp.mpr hfC).trans (hA i)) g₀ hfactor₀
  let E := D.filtration.realification.adaptedConstantGroupHom (fun _ : σ => 1) a * e₀
  have hE : D.filtration.PolynomialSlowBound D.basis (fun _ : σ => 1) A
      (Real.exp ((p + C) ^ C)) E := by
    have hsmall := hleft D w hF q hq (RationalFilteredNilmanifold.GeometryComplexityLE.mono D hD hpq)
      (hσ.trans hpq) A hApos a (fun i => (ha i).trans (Real.exp_le_exp.mpr hnq)) e₀
      (D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos (Real.exp_le_exp.mpr hfq) e₀ he)
    exact D.filtration.polynomialSlowBound_mono D.basis (fun _ => 1) A hApos
      (Real.exp_le_exp.mpr hlC) E hsmall
  have hprod : E * b * R * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g := by
    calc
      _ = D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) a *
          (e₀ * b * R) * D.filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ := by
        simp only [E, mul_assoc]
      _ = g := by rw [hebr]; exact hnormalizeEq
  let e := Fintype.equivFin (Fin d)
  have hrange : Set.range (fun i => v (e i)) = Set.range v := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      obtain ⟨j, hj⟩ := e.surjective i
      exact ⟨j, congrArg v hj⟩
  have hv' : Submodule.span ℚ (Set.range (fun i => v (e i))) = W.toSubmodule := by
    rw [hrange]
    exact hv
  refine ⟨W, (fun i => v (e i)), m, κ, E, b, R, hv', hW,
    (fun i j => (hheight (e i) j).trans hhC), hfreq, hm,
    hmp.trans (Real.exp_le_exp.mpr hfC), hκ, hprod, hE, hR,
    hb0.trans hg₀zero, hR0, ?_, hvalues hg₀zero⟩
  exact (D.filtration.real_symbol_values_iff_refiltration_coefficients D.basis w hF
    (fun _ => 1) W b.coord).mp hmid

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitOuterControl
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold

theorem exists_native_orbit_outer_control (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (∀ i, 0 < A i) → Fintype.card σ ≤ k →
      R.HasOuterValueControl ((p + C) ^ C) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  let K := (s + 1) * (k + 1) ^ s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + Polynomial.C K)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ d D g eta A p R hp hD hA hk
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := hcoeff R hp hD hA
  have htotal : (p + a) ^ a + (K : ℝ) ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hcost : (p + a) ^ a ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (Nat.cast_nonneg K)).trans htotal
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hcost), ?_, ?_⟩
  · intro x
    exact D.filtration.polynomialRationalGrid_value D.basis (fun _ : σ => 1) m R.rational hrat x
  · intro x hx i
    have hs := D.filtration.polynomialSlowBound_value D.basis (fun _ : σ => 1)
      (fun _ => Nat.zero_lt_one) A hA (Real.exp_nonneg _) R.slow hslow
      (fun j => (x j : ℝ)) hx i
    have hcard : (Fintype.card σ : ℝ) ≤ k := by exact_mod_cast hk
    have hK : ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s ≤ K := by
      dsimp [K]
      push_cast
      gcongr
    have hKexp : (K : ℝ) ≤ Real.exp K := by linarith [Real.add_one_le_exp (K : ℝ)]
    apply hs.trans
    calc
      _ ≤ (K : ℝ) * Real.exp ((p + a) ^ a) :=
        mul_le_mul_of_nonneg_right hK (Real.exp_nonneg _)
      _ ≤ Real.exp K * Real.exp ((p + a) ^ a) :=
        mul_le_mul_of_nonneg_right hKexp (Real.exp_nonneg _)
      _ = Real.exp ((K : ℝ) + (p + a) ^ a) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr (by linarith)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeOrbitFreezing
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_native_orbit_local_control (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {d : ℕ}
      {D : RationalFilteredNilmanifold L s d}
      {g : (D.filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group}
      {eta : L →ₗ[ℚ] ℚ} {A : σ → ℝ} {p : ℝ}
      (R : NativePolynomialOrbitFactors D g eta A p),
      0 ≤ p → D.GeometryComplexityLE p → (Fintype.card σ : ℝ) ≤ p → (∀ i, 0 < A i) →
      ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        (∀ x y : σ → ℤ, (∀ i, (P : ℤ) ∣ x i - y i) →
          ((QuotientGroup.mk (R.rationalValue x) : D.Space) = QuotientGroup.mk (R.rationalValue y)) ∧
          ((QuotientGroup.mk (R.rationalValue x)⁻¹ : D.Space) = QuotientGroup.mk (R.rationalValue y)⁻¹)) ∧
        (letI := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
          (D.basis.baseChange ℝ)
         ∀ (x y : σ → ℤ) (δ : ℝ), 0 ≤ δ →
           (∀ i, |(x i : ℝ)| ≤ A i) → (∀ i, |(y i : ℝ)| ≤ A i) →
           (∀ i, |(x i : ℝ) - (y i : ℝ)| ≤ A i * δ) →
           dist (R.slowValue x) (R.slowValue y) ≤ Real.exp ((p + C) ^ C) * δ) := by
  obtain ⟨a, _, hcoeff⟩ := exists_native_orbit_coefficient_control
  obtain ⟨b, _, hperiod⟩ := exists_native_rational_period s
  obtain ⟨c, _, hmetric⟩ := exists_polynomialSlowBound_dist_exp s 1
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + (X + Polynomial.C a) ^ a + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((Q + Polynomial.C b) ^ b + (Q + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ _ _ _ _ _ d D g eta A p R hp hD hσ hA
  obtain ⟨m, hm, hmb, hgrid, hslow⟩ := hcoeff R hp hD hA
  let q := p + (p + a) ^ a + 2
  have hpow : 0 ≤ (p + a) ^ a := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith
  have hsum : (q + b) ^ b + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [Q, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hbC : (q + b) ^ b ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (by positivity)).trans hsum
  have hcC : (q + c) ^ c ≤ (p + C) ^ C :=
    (le_add_of_nonneg_left (by positivity)).trans hsum
  obtain ⟨P, hP, hPb, hcosets⟩ := hperiod D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    q hq (hD.mono D hpq) (hσ.trans hpq) m hm (hmb.trans (Real.exp_le_exp.mpr haq))
  refine ⟨P, hP, hPb.trans (Real.exp_le_exp.mpr hbC), hcosets R.rational hgrid, ?_⟩
  let := rightMetricSpace (hnil := D.filtration.realification.lowerCentralSeries_eq_bot)
    (D.basis.baseChange ℝ)
  intro x y δ hδ hx hy hxy
  have hs := D.filtration.polynomialSlowBound_mono D.basis (fun _ : σ => 1) A hA
    (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith : (p + a) ^ a ≤ (q + 2) ^ 1))
    R.slow hslow
  have hd := hmetric D (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) q hq (hD.mono D hpq)
    (hσ.trans hpq) A hA R.slow hs (fun i => (x i : ℝ)) (fun i => (y i : ℝ)) δ hδ hx hy hxy
  exact hd.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hcC) hδ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PositivePartitionIntegerExpansion
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_weighted_integer_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} [Fintype σ] {s N : ℕ} [NeZero N]
      {p : ℝ} {f : (σ → ℤ) → ℂ}
      (_E : NativeIntegerExpansion (fun _ : σ => 1) s p f),
      0 ≤ p → (Fintype.card σ : ℝ) ≤ p → ∀ w : σ → ZMod N → ℝ,
      (∀ i, PositiveCyclicNiltest.{0} s N p (w i)) →
      ∃ g : (σ → ℤ) → ℂ,
        Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) g) ∧
        ∀ x : σ → ZMod N, g (fun i => ((x i).val : ℤ)) =
          (∏ i, (w i (x i) : ℂ)) * f (fun i => ((x i).val : ℤ)) := by
  obtain ⟨A, _, hprod⟩ := exists_productNiltestBudget_bound
  obtain ⟨B, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let Y := X + (X + 2) ^ 2 + 3
  let Q := (Y + Polynomial.C A) ^ A + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((Q + Polynomial.C B) ^ B)
  refine ⟨C, hC, ?_⟩
  intro σ _ s N _ p f E hp hσ w hw
  have hp' : 0 ≤ raisedNiltestBudget p := hp.trans (le_raisedNiltestBudget p)
  let q := (raisedNiltestBudget p + A) ^ A + p + 2
  have hpower : 0 ≤ (raisedNiltestBudget p + A) ^ A := by positivity
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hpq : p ≤ q := by dsimp only [q]; linarith only [hpower]
  have hweight : productNiltestBudget (raisedNiltestBudget p) ≤ q :=
    (hprod _ hp').trans (by dsimp only [q]; linarith only [hp])
  have hqC : (q + B) ^ B ≤ (p + C) ^ C := by
    simpa [Q, Y, X, q, raisedNiltestBudget, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨g, ⟨W⟩, he⟩ := exists_positive_coordinate_product hp hσ hw
  obtain ⟨G⟩ := hmul hq (W.mono hweight) (E.mono hpq)
  refine ⟨fun x => g x * f x, ⟨G.mono hqC⟩, ?_⟩
  intro x
  exact congrArg (fun z : ℂ => z * f (fun i => ((x i).val : ℤ))) (he x)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exists_positive_partition_integer_expansion :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type} {I J : Type*} [Fintype σ] [Fintype I]
      {s N : ℕ} [NeZero N] {p : ℝ}, 0 ≤ p → (Fintype.card σ : ℝ) ≤ p →
      (Fintype.card I : ℝ) ≤ Real.exp p →
      ∀ (w : I → σ → ZMod N → ℝ) (v : I → J → (σ → ℤ) → ℂ),
        (∀ i k, PositiveCyclicNiltest.{0} s N p (w i k)) →
        (∀ i j, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s p (v i j))) →
        ∃ F : J → (σ → ℤ) → ℂ,
          (∀ j, Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + C) ^ C) (F j))) ∧
          ∀ j (x : σ → ZMod N), F j (fun k => ((x k).val : ℤ)) =
            ∑ i, ((∏ k, w i k (x k) : ℝ) : ℂ) * v i j (fun k => ((x k).val : ℤ)) := by
  obtain ⟨A, _, hweighted⟩ := exists_positive_weighted_integer_expansion
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C A) ^ A + X)
  refine ⟨C, hC, ?_⟩
  intro σ I J _ _ s N _ p hp hσ hI w v hw hv
  classical
  have hfamily (i : I) (j : J) : ∃ g : (σ → ℤ) → ℂ,
      Nonempty (NativeIntegerExpansion (fun _ : σ => 1) s ((p + A) ^ A) g) ∧
      ∀ x : σ → ZMod N, g (fun k => ((x k).val : ℤ)) =
        ((∏ k, w i k (x k) : ℝ) : ℂ) * v i j (fun k => ((x k).val : ℤ)) := by
    obtain ⟨g, hg, he⟩ := hweighted (Classical.choice (hv i j)) hp hσ (w i) (hw i)
    exact ⟨g, hg, fun x => by simpa only [Complex.ofReal_prod] using he x⟩
  choose g hg he using hfamily
  let F := fun (j : J) (x : σ → ℤ) => ∑ i, g i j x
  have hcost : (p + A) ^ A + p ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  refine ⟨F, ?_, ?_⟩
  · intro j
    have hc : (∑ _i : I, ‖(1 : ℂ)‖) ≤ Real.exp p := by simpa using hI
    exact ⟨by simpa only [F, one_mul] using
      ((NativeIntegerExpansion.weightedSum (fun i => Classical.choice (hg i j))
        (fun _ => 1) hp hI hc).mono hcost)⟩
  · intro j x
    exact Finset.sum_congr rfl (fun i _ => he i j x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

attribute [local instance] NativeCommonDerivativeModels.lie NativeCommonDerivativeModels.algebra
  NativeCommonDerivativeModels.topology NativeCommonDerivativeModels.topologicalAdd
  NativeCommonDerivativeModels.continuousSMul NativeCommonDerivativeModels.hausdorff

theorem exists_normalized_native_common_models (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ},
      0 ≤ p → (∀ x, ‖f x‖ ≤ 1) → (B : NativeCommonDerivativeModels s N p f) →
      ∃ R : NativeCommonDerivativeModels s N ((p + C) ^ C) f,
        ∀ h, R.model.filtration.realification.polynomialOrbitEval (fun _ => 1) 0
          (R.test h).orbit = 1 := by
  obtain ⟨a, _, hnormalize⟩ := RationalFilteredNilmanifold.exists_normalized_common_correlators s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (X + (X + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro N _ p f hp hf B
  have hq : 0 ≤ (p + a) ^ a := by positivity
  have hcost : p + (p + a) ^ a ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have hqC : (p + a) ^ a ≤ (p + C) ^ C := by linarith
  obtain ⟨H, S, _, hH, hdense, hS, hsame, hcorr⟩ :=
    hnormalize B.model B.test B.shifts B.nonempty hp B.geometry B.complexity
      (fun h _ => B.norm h) (fun h x => multiplicativeDerivative f h x)
      (fun h _ x => multiplicativeDerivative_norm_le_one f hf h x) B.correlation
  have hfinaldensity : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(p + (p + a) ^ a)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcost)) (Nat.cast_nonneg _)
      _ = Real.exp (-((p + a) ^ a)) * (Real.exp (-p) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-((p + a) ^ a)) * B.shifts.card :=
        mul_le_mul_of_nonneg_left B.density (Real.exp_nonneg _)
      _ ≤ _ := hdense
  let R : NativeCommonDerivativeModels s N ((p + C) ^ C) f := {
    L := B.L
    dim := B.dim
    model := B.model
    geometry := B.geometry.mono B.model hpC
    shifts := H
    nonempty := hH
    density := hfinaldensity
    test := S
    norm := fun h => (hS h).1
    complexity := fun h => (hS h).2.2.1.mono hqC
    common_observable := hsame
    correlation := fun h hh => (Real.exp_le_exp.mpr (neg_le_neg hqC)).trans (hcorr h hh) }
  exact ⟨R, fun h => (hS h).2.2.2⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DiagonalRowTransfer
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem exists_native_common_factor_products :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ J K : Type*} [Fintype K] {w : σ → ℕ} {s : ℕ} {p : ℝ},
      0 ≤ p → (Fintype.card K : ℝ) ≤ Real.exp p →
      ∀ (F : J → K → (σ → ℤ) → ℂ) (U : K → (σ → ℤ) → ℂ),
        (∀ j k, Nonempty (NativeIntegerExpansion w s p (F j k))) →
        (∀ a b, Nonempty (NativeIntegerExpansion w s p
          (fun x => U a x * star (U b x)))) →
        ∀ i j, Nonempty (NativeIntegerExpansion w s ((p + C) ^ C)
          (fun x => (∑ a, F i a x * U a x) * star (∑ b, F j b x * U b x))) := by
  obtain ⟨A, _, hmul⟩ := NativeIntegerExpansion.exists_mul_budget
  let X : Polynomial ℕ := Polynomial.X
  let R := X + (X + Polynomial.C A) ^ A + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((R + Polynomial.C A) ^ A + 2 * X)
  refine ⟨C, hC, ?_⟩
  intro σ J K _ w s p hp hK F U hF hU i j
  classical
  let r := p + (p + A) ^ A + 2
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hpr : p ≤ r := by
    have : 0 ≤ (p + A) ^ A := by positivity
    dsimp [r]
    linarith
  have har : (p + A) ^ A ≤ r := by dsimp [r]; linarith
  have hcost : (r + A) ^ A + 2 * p ≤ (p + C) ^ C := by
    simpa [X, R, r, Polynomial.eval₂_pow] using hbudget p hp
  have hterm (a b : K) : Nonempty (NativeIntegerExpansion w s ((r + A) ^ A)
      (fun x => (F i a x * star (F j b x)) * (U a x * star (U b x)))) := by
    obtain ⟨E⟩ := hmul hp (Classical.choice (hF i a)) (Classical.choice (hF j b)).conjugate
    exact hmul hr (E.mono har) ((Classical.choice (hU a b)).mono hpr)
  have hcount : (Fintype.card (K × K) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Fintype.card_prod, Nat.cast_mul, two_mul, Real.exp_add]
    exact mul_le_mul hK hK (Nat.cast_nonneg _) (Real.exp_nonneg _)
  have hcoeff : (∑ _ : K × K, ‖(1 : ℂ)‖) ≤ Real.exp (2 * p) := by simpa using hcount
  let E := (NativeIntegerExpansion.weightedSum
    (fun ab : K × K => Classical.choice (hterm ab.1 ab.2)) (fun _ => (1 : ℂ))
    (by positivity : 0 ≤ 2 * p) hcount hcoeff).mono hcost
  have heq : (fun x => ∑ ab : K × K,
      (1 : ℂ) * ((F i ab.1 x * star (F j ab.2 x)) * (U ab.1 x * star (U ab.2 x)))) =
      (fun x => (∑ a, F i a x * U a x) * star (∑ b, F j b x * U b x)) := by
    funext x
    simp only [one_mul, Fintype.sum_prod_type, star_sum, star_mul]
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  exact ⟨heq ▸ E⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AxisCompression
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem exists_native_cyclic_small_modulus_correlation (s : ℕ) (hs : 1 ≤ s)
    {N : ℕ} [NeZero N] {p q : ℝ}
    (hN : (N : ℝ) ≤ Real.exp q) (f : ZMod N → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1)
    (hGowers : Real.exp (-p) ≤ gowersNorm (s + 1) f) :
    ∃ g ∈ nativeCyclicFunctions s N 211,
      Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤ ‖𝔼 n, f n * star (g n)‖ := by
  have hmass : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) ≤
      ∑ χ : AddChar (ZMod N) ℂ, ‖finiteFourierCoeff f χ‖ := by
    calc
      _ = Real.exp (-p) ^ (2 ^ (s + 1)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      _ ≤ gowersNorm (s + 1) f ^ (2 ^ (s + 1)) :=
        pow_le_pow_left₀ (Real.exp_nonneg _) hGowers _
      _ ≤ 𝔼 n, ‖f n‖ := gowersNorm_pow_le_mean_norm s f hf
      _ ≤ _ := mean_norm_le_fourier_sum f
  obtain ⟨χ, hχ⟩ := exists_large_nonnegative_weighted_term
    (fun _ : AddChar (ZMod N) ℂ => (1 : ℝ)) (fun χ => ‖finiteFourierCoeff f χ‖)
    (fun _ => by norm_num) (fun _ => norm_nonneg _) (Real.exp_pos _) (Real.exp_pos q)
    (by simpa using hN) (by simpa only [one_mul] using hmass)
  have hcorr : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) ≤
      ‖finiteFourierCoeff f χ‖ := by
    have heq : Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p)) / Real.exp q =
        Real.exp (-(((2 ^ (s + 1) : ℕ) : ℝ) * p + q)) := by
      rw [← Real.exp_sub]
      congr 1
      ring
    rwa [heq] at hχ
  obtain ⟨T, hTnorm, hT, hTeval⟩ := exists_cyclic_character_niltest χ
  refine ⟨fun n => χ n, ⟨{
    L := RationalTorus.Algebra 1
    dim := 1
    model := (RationalTorus.nilmanifold 1).raiseStep hs
    test := T.raiseStep hs
    norm := hTnorm
    complexity := ?_
    eval := ?_ }⟩, hcorr⟩
  · have hh := T.raiseStep_complexity hs (by norm_num) hT
    convert hh using 1
    norm_num [raisedNiltestBudget]
  · intro n
    rw [RationalFilteredNilmanifold.Niltest.raiseStep_evalCyclic]
    exact (hTeval n).symm

end Erdos3

end

end OAI
end


