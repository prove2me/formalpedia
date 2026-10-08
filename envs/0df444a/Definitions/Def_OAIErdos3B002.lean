-- Prove2me | Definitions.Def_OAIErdos3B002
-- name    : OAIErdos3B002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-08T07:20:49.496057+00:00
-- url     : https://prove2.me/theorems/b5e63c6b-d50a-4100-9543-340ed1873762
-- title:
--   OpenAI Erdős-3 split, definitions bundle 3 of 132
-- statement:
--   Definitions bundle 3 of 132 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B001`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 3 available.
--
--   Modules: `Linear.SpanKernelGenerators`, `Estimates.RationalSubspaces`, `Linear.RationalKernelBudget`, `Estimates.RationalImageIntersections`, `Sampling.RationalSpanGrid`, `Sampling.RealGridSeparation`, `Linear.RationalMatrixSeparation`, `Polynomial.IntegerPolynomialCongruence`, `Polynomial.PolynomialTermCount`, `Polynomial.PolynomialIntegerInputs`, `Polynomial.LieCoordinatePolynomials`, `Geometry.LieStructureTransport`, `Estimates.TruncatedSeriesFiltration`, `Geometry.LieCoordinateHeight`, `Polynomial.PolynomialDensityBudget`, `Polynomial.RationalPolynomialGrid`, `Sampling.ConjugationGridBudget`, `Nilpotent.BCHDenominatorBudget`, `Geometry.LieCoordinateScalarExtension`, `Nilpotent.BCHNonlinearRemainder`, `Estimates.RationalLieSubalgebra`, `Nilpotent.BCHSubgroupGridExistence`, `Estimates.SquarefreeExponents`, `Estimates.SquarefreeCoefficients`, `Estimates.ProductPMFMap`, `Estimates.RealWeightPMF`, `Geometry.IndependentProductTransport`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B001

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def independentProductPMF {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) : PMF (D → X) :=
  (Measure.pi (fun d => (p d).toMeasure)).toPMF

theorem independentProductPMF_apply {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) (x : D → X) :
    independentProductPMF p x = ∏ d, p d (x d) := by
  simp only [independentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

theorem independentProductPMF_toReal {D X : Type*} [Fintype D] [Countable X]
    [MeasurableSpace X] [MeasurableSingletonClass X] (p : D → PMF X) (x : D → X) :
    (independentProductPMF p x).toReal = ∏ d, (p d (x d)).toReal := by
  rw [independentProductPMF_apply, ENNReal.toReal_prod]

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def dependentProductPMF {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) : PMF (∀ d, X d) :=
  (Measure.pi (fun d => (p d).toMeasure)).toPMF

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SpanKernelGenerators
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem range_kernel_projection (A : Matrix ι κ ℚ) (S : Matrix κ ι ℚ)
    (hS : A * S = 1) :
    LinearMap.range (1 - S * A).mulVecLin = LinearMap.ker A.mulVecLin := by
  have hzero : A * (1 - S * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hS, Matrix.one_mul, sub_self]
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change A *ᵥ ((1 - S * A) *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]
  · intro hy
    change A *ᵥ y = 0 at hy
    refine ⟨y, ?_⟩
    change (1 - S * A) *ᵥ y = y
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      hy, Matrix.mulVec_zero, sub_zero]

def rationalKernelHeight (r H : ℕ) : ℕ :=
  2 * (r + 1) * (rationalSolveHeight r H * H) ^ r

omit [DecidableEq ι] in
theorem exists_bounded_kernel_projection (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧ ∃ P : Matrix κ κ ℚ,
      LinearMap.range P.mulVecLin = LinearMap.ker A.mulVecLin ∧
      ∀ i j, RationalHeightLE (P i j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, rows, _, hsurj, hker⟩ := exists_independent_defining_rows A
  let R := A.submatrix rows id
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section R hsurj hH
    (fun i j => hA (rows i) j)
  refine ⟨r, hr, 1 - S * R, (range_kernel_projection R S hS).trans hker, ?_⟩
  intro i j
  have hI : RationalHeightLE ((1 : Matrix κ κ ℚ) i j) 1 := by
    by_cases hij : i = j
    · simpa [Matrix.one_apply, hij] using rationalHeightLE_one (by decide : 1 ≤ 1)
    · simpa [Matrix.one_apply, hij] using rationalHeightLE_zero (by decide : 1 ≤ 1)
  have hprod := rationalHeightLE_matrix_mul S R hSH (fun i j => hA (rows i) j) i j
  have hout := hI.sub hprod
  simpa only [Matrix.sub_apply, Fintype.card_fin, rationalKernelHeight, mul_one,
    mul_assoc] using hout

omit [DecidableEq ι] in

theorem exists_bounded_rational_kernel_family (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ v : Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)) → (κ → ℚ),
        LinearIndependent ℚ v ∧ Submodule.span ℚ (Set.range v) = LinearMap.ker A.mulVecLin ∧
        ∀ i j, RationalHeightLE (v i j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, P, hP, hPH⟩ := exists_bounded_kernel_projection A hH hA
  have hspan : Submodule.span ℚ (Set.range P.col) = LinearMap.ker A.mulVecLin := by
    rw [← Matrix.range_mulVecLin, hP]
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range P.col)
  rw [hspan] at hex
  obtain ⟨v, hv, hvspan, hli⟩ := hex
  refine ⟨r, hr, v, hli, hvspan, ?_⟩
  intro i j
  obtain ⟨k, hk⟩ := hv i
  rw [← hk]
  exact hPH j k

omit [DecidableEq ι] in

theorem exists_bounded_rational_kernel_basis (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ r : ℕ, r ≤ Fintype.card ι ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ (LinearMap.ker A.mulVecLin)))
        ℚ (LinearMap.ker A.mulVecLin),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  obtain ⟨r, hr, v, hli, hspan, hv⟩ := exists_bounded_rational_kernel_family A hH hA
  refine ⟨r, hr, (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hspan), ?_⟩
  intro i j
  simpa only [Module.Basis.map_apply, LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply] using hv i j

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {K V W κ : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W] [Fintype κ]

noncomputable def finiteCombination (v : κ → V) : (κ → K) →ₗ[K] V :=
  (Pi.basisFun K κ).constr K v

theorem finiteCombination_apply (v : κ → V) (x : κ → K) :
    finiteCombination v x = ∑ i, x i • v i := by
  classical
  rw [finiteCombination, Basis.constr_apply_fintype]
  rfl

theorem finiteCombination_basis (v : κ → V) (i : κ) :
    finiteCombination v (Pi.basisFun K κ i) = v i :=
  Basis.constr_basis (Pi.basisFun K κ) K v i

theorem finiteCombination_range (v : κ → V) :
    LinearMap.range (finiteCombination (K := K) v) = Submodule.span K (Set.range v) :=
  Basis.constr_range (Pi.basisFun K κ) K

theorem finiteCombination_kernel_image (v : κ → V) (P : V →ₗ[K] W) :
    (LinearMap.ker (P.comp (finiteCombination v))).map (finiteCombination v) =
      Submodule.span K (Set.range v) ⊓ LinearMap.ker P := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(finiteCombination_range v).le ⟨x, rfl⟩, hx⟩
  · rintro ⟨hy, hP⟩
    obtain ⟨x, rfl⟩ := (finiteCombination_range v).ge hy
    exact ⟨x, hP, rfl⟩

section Rational

variable {V W ι η κ : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [Fintype κ] [Fintype η]

theorem finiteCombination_constraint_kernel (f : Basis η ℚ W) (P : V →ₗ[ℚ] W)
    (v : κ → V) :
    LinearMap.ker (Matrix.mulVecLin (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i)) =
      LinearMap.ker (P.comp (finiteCombination v)) := by
  classical
  ext x
  have he : (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i) *ᵥ x =
      f.equivFun (P (finiteCombination v x)) := by
    ext i
    simp only [finiteCombination_apply, map_sum, map_smul, Basis.equivFun_apply,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _
  change (show Matrix η κ ℚ from fun i j => f.repr (P (v j)) i) *ᵥ x = 0 ↔
    P (finiteCombination v x) = 0
  rw [he, LinearEquiv.map_eq_zero_iff]

theorem exists_bounded_span_kernel_generators (e : Basis ι ℚ V) (f : Basis η ℚ W)
    (P : V →ₗ[ℚ] W) (v : κ → V) {H B : ℕ} (hB : 1 ≤ B)
    (hv : ∀ i j, RationalHeightLE (e.repr (v i) j) H)
    (hPv : ∀ i j, RationalHeightLE (f.repr (P (v i)) j) B) :
    ∃ r : ℕ, r ≤ Fintype.card η ∧ ∃ z : κ → V,
      Submodule.span ℚ (Set.range z) = Submodule.span ℚ (Set.range v) ⊓ LinearMap.ker P ∧
      ∀ i j, RationalHeightLE (e.repr (z i) j)
        ((Fintype.card κ + 1) * (rationalKernelHeight r B * H) ^ Fintype.card κ) := by
  classical
  let A : Matrix η κ ℚ := fun i j => f.repr (P (v j)) i
  obtain ⟨r, hr, Q, hQ, hQH⟩ := exists_bounded_kernel_projection A hB (fun i j => hPv j i)
  refine ⟨r, hr, fun i => finiteCombination v (Q.col i), ?_, ?_⟩
  · rw [← finiteCombination_kernel_image v P, ← finiteCombination_constraint_kernel f P v,
      ← hQ, Matrix.range_mulVecLin, Submodule.map_span, ← Set.range_comp]
    rfl
  · intro i j
    exact linearMap_coordinate_height (Pi.basisFun ℚ κ) e (finiteCombination v)
      (by intro a b; rw [finiteCombination_basis]; exact hv a b)
      (Q.col i) (fun a => hQH a i) j

end Rational
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalSubspaces
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

section Intersection

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

def jointMatrix (A : ∀ i, Matrix (ρ i) κ ℚ) : Matrix (Σ i, ρ i) κ ℚ :=
  fun ij k => A ij.1 ij.2 k

omit [Fintype η] [∀ i, Fintype (ρ i)] [DecidableEq κ] in
theorem jointMatrix_ker (A : ∀ i, Matrix (ρ i) κ ℚ) :
    LinearMap.ker (jointMatrix A).mulVecLin = ⨅ i, LinearMap.ker (A i).mulVecLin := by
  ext x
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, Matrix.mulVecLin_apply,
    funext_iff, Pi.zero_apply]
  exact ⟨fun h i j => h ⟨i, j⟩, fun h ij => h ij.1 ij.2⟩

theorem exists_bounded_rational_intersection_basis (A : ∀ i, Matrix (ρ i) κ ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ ∑ i, Fintype.card (ρ i) ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.ker (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j) (rationalKernelHeight r H) := by
  have h := exists_bounded_rational_kernel_basis (jointMatrix A) hH
    (fun ij k => hA ij.1 ij.2 k)
  rw [← jointMatrix_ker A]
  simpa only [Fintype.card_sigma] using h

end Intersection

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalKernelBudget
namespace OAI

section

namespace Erdos3

theorem rationalKernelHeight_le_budget (r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalKernelHeight r H : ℝ) ≤ Real.exp ((p + 2) ^ 7) := by
  have hsolve := rationalSolveHeight_le_budget r H hp hr hH
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hfront : (2 : ℝ) * (r + 1) ≤ Real.exp (1 + (r : ℝ)) := by
    rw [Real.exp_add]
    exact mul_le_mul htwo (Real.add_one_le_exp r) (by positivity) (by positivity)
  have hbase : (rationalSolveHeight r H : ℝ) * H ≤
      Real.exp ((p + 2) ^ 5 + p) := by
    rw [Real.exp_add]
    exact mul_le_mul hsolve hH (Nat.cast_nonneg _) (by positivity)
  have hpower := pow_le_pow_left₀ (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    hbase r
  rw [← Real.exp_nat_mul] at hpower
  have hbound : (rationalKernelHeight r H : ℝ) ≤
      Real.exp (1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p)) := by
    unfold rationalKernelHeight
    push_cast
    rw [Real.exp_add]
    exact mul_le_mul hfront hpower (by positivity) (by positivity)
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  calc
    1 + (r : ℝ) + (r : ℝ) * ((p + 2) ^ 5 + p) ≤
        1 + p + p * ((p + 2) ^ 5 + p) := by gcongr
    _ ≤ (p + 2) ^ 7 := by
      have h : 0 ≤ p ^ 7 + 13 * p ^ 6 + 74 * p ^ 5 + 240 * p ^ 4 +
          480 * p ^ 3 + 591 * p ^ 2 + 415 * p + 127 := by positivity
      nlinarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalImageIntersections
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in

theorem kernel_equations_of_transpose_kernel (A : Matrix ι κ ℚ)
    (v : Fin (Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin)) → (ι → ℚ))
    (hli : LinearIndependent ℚ v)
    (hspan : Submodule.span ℚ (Set.range v) = LinearMap.ker Aᵀ.mulVecLin) :
    Function.Surjective (Matrix.mulVec v) ∧
      LinearMap.ker (Matrix.mulVecLin v) = LinearMap.range A.mulVecLin := by
  let D : Matrix (Fin (Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin))) ι ℚ := v
  have hrows : LinearIndependent ℚ D.row := hli
  have hDA : D * A = 0 := by
    ext i j
    have hi : v i ∈ LinearMap.ker Aᵀ.mulVecLin := by
      rw [← hspan]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hj := congrFun hi j
    change (∑ k, A k j * v i k) = 0 at hj
    change (∑ k, v i k * A k j) = 0
    simpa only [mul_comm] using hj
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.ker D.mulVecLin := by
    rintro y ⟨x, rfl⟩
    change D *ᵥ (A *ᵥ x) = 0
    rw [Matrix.mulVec_mulVec, hDA, Matrix.zero_mulVec]
  have hdimD := LinearMap.finrank_range_add_finrank_ker D.mulVecLin
  have hdimA := LinearMap.finrank_range_add_finrank_ker Aᵀ.mulVecLin
  change D.rank + Module.finrank ℚ (LinearMap.ker D.mulVecLin) =
    Module.finrank ℚ (ι → ℚ) at hdimD
  change Aᵀ.rank + Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin) =
    Module.finrank ℚ (ι → ℚ) at hdimA
  rw [hrows.rank_matrix, Fintype.card_fin] at hdimD
  rw [Matrix.rank_transpose] at hdimA
  have heq : Module.finrank ℚ (LinearMap.range A.mulVecLin) =
      Module.finrank ℚ (LinearMap.ker D.mulVecLin) := by
    change A.rank = _
    omega
  exact ⟨mulVec_surjective_of_independent_rows D hrows,
    (Submodule.eq_of_le_of_finrank_eq hle heq).symm⟩

theorem exists_bounded_image_equations (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, Function.Surjective D.mulVec ∧
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧
        ∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H) := by
  obtain ⟨t, ht, v, hli, hspan, hv⟩ := exists_bounded_rational_kernel_family Aᵀ hH
    (fun i j => hA j i)
  have hD := kernel_equations_of_transpose_kernel A v hli hspan
  refine ⟨t, ht, Module.finrank ℚ (LinearMap.ker Aᵀ.mulVecLin), ?_, v, hD.1, hD.2, hv⟩
  simpa only [Module.finrank_pi] using (LinearMap.ker Aᵀ.mulVecLin).finrank_le

theorem rationalKernelHeight_pos (t : ℕ) {H : ℕ} (hH : 1 ≤ H) :
    0 < rationalKernelHeight t H := by
  have hsolve := rationalSolveHeight_pos t hH
  have hHpos : 0 < H := Nat.zero_lt_one.trans_le hH
  unfold rationalKernelHeight
  positivity

theorem exists_bounded_quotient_presentation (A : Matrix ι κ ℚ) {H : ℕ}
    (hH : 1 ≤ H) (hA : ∀ i j, RationalHeightLE (A i j) H) :
    ∃ t : ℕ, t ≤ Fintype.card κ ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.ker D.mulVecLin = LinearMap.range A.mulVecLin ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H)) := by
  obtain ⟨t, ht, d, hd, D, hsurj, hker, hD⟩ := exists_bounded_image_equations A hH hA
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section D hsurj
    (rationalKernelHeight_pos t hH) hD
  exact ⟨t, ht, d, hd, D, S, hker, hS, hD, by simpa only [Fintype.card_fin] using hSH⟩

section Coordinates

variable [DecidableEq κ]

noncomputable def rationalQuotientEquiv (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) :
    ((κ → ℚ) ⧸ K) ≃ₗ[ℚ] (ι → ℚ) :=
  (Submodule.quotEquivOfEq K (LinearMap.ker D.mulVecLin) hker.symm).trans
    (D.mulVecLin.quotKerEquivOfSurjective hsurj)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem rationalQuotientEquiv_apply_mk (D : Matrix ι κ ℚ)
    (K : Submodule ℚ (κ → ℚ)) (hker : LinearMap.ker D.mulVecLin = K)
    (hsurj : Function.Surjective D.mulVec) (x : κ → ℚ) :
    rationalQuotientEquiv D K hker hsurj (Submodule.Quotient.mk x) = D *ᵥ x := by
  simp only [rationalQuotientEquiv, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk]
  exact D.mulVecLin.quotKerEquivOfSurjective_apply_mk hsurj x

end Coordinates

end Erdos3

end

section

namespace Erdos3

theorem rationalSolveHeight_mono {r s H : ℕ} (hH : 1 ≤ H) (hrs : r ≤ s) :
    rationalSolveHeight r H ≤ rationalSolveHeight s H := by
  unfold rationalSolveHeight
  apply Nat.mul_le_mul (Nat.factorial_le hrs)
  have he : r * r + r ≤ s * s + s := Nat.add_le_add (Nat.mul_le_mul hrs hrs) hrs
  have hbase := pow_le_pow_right₀ hH he
  calc
    _ ≤ (H ^ (s * s + s)) ^ r := pow_le_pow_left₀ (Nat.zero_le _) hbase r
    _ ≤ _ := pow_le_pow_right₀ (one_le_pow₀ hH) hrs

theorem rationalKernelHeight_mono {r s H : ℕ} (hH : 1 ≤ H) (hrs : r ≤ s) :
    rationalKernelHeight r H ≤ rationalKernelHeight s H := by
  unfold rationalKernelHeight
  apply Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.succ_le_succ hrs))
  have hbase := Nat.mul_le_mul_right H (rationalSolveHeight_mono hH hrs)
  have hpos : 1 ≤ rationalSolveHeight s H * H :=
    Nat.mul_pos (rationalSolveHeight_pos s hH) (Nat.zero_lt_one.trans_le hH)
  calc
    _ ≤ (rationalSolveHeight s H * H) ^ r := pow_le_pow_left₀ (Nat.zero_le _) hbase r
    _ ≤ _ := pow_le_pow_right₀ hpos hrs

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

variable {η κ : Type*} [Fintype η] [Fintype κ] [DecidableEq κ]
variable {ρ : η → Type*} [∀ i, Fintype (ρ i)]

theorem exists_bounded_image_intersection_basis (A : ∀ i, Matrix κ (ρ i) ℚ)
    {H : ℕ} (hH : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H) :
    ∃ r : ℕ, r ≤ Fintype.card η * Fintype.card κ ∧
      ∃ b : Module.Basis (Fin (Module.finrank ℚ
          (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
        ℚ (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ)),
        ∀ i j, RationalHeightLE ((b i : κ → ℚ) j)
          (rationalKernelHeight r (rationalKernelHeight (∑ i, Fintype.card (ρ i)) H)) := by
  classical
  choose t ht d hd D hsurj hker hD using
    (fun i => exists_bounded_image_equations (A i) hH (hA i))
  let M := ∑ i, Fintype.card (ρ i)
  let K := rationalKernelHeight M H
  have htM : ∀ i, t i ≤ M := by
    intro i
    exact (ht i).trans (Finset.single_le_sum (fun j _ => Nat.zero_le (Fintype.card (ρ j)))
      (Finset.mem_univ i))
  have hDK : ∀ i j k, RationalHeightLE (D i j k) K := by
    intro i j k
    exact (hD i j k).mono (rationalKernelHeight_mono hH (htM i))
  have hsub : (⨅ i, LinearMap.ker (D i).mulVecLin : Submodule ℚ (κ → ℚ)) =
      ⨅ i, LinearMap.range (A i).mulVecLin := iInf_congr hker
  rw [← hsub]
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_rational_intersection_basis D
    (rationalKernelHeight_pos M hH) hDK
  refine ⟨r, ?_, b, hb⟩
  calc
    r ≤ ∑ i, d i := by simpa only [Fintype.card_fin] using hr
    _ ≤ ∑ _ : η, Fintype.card κ := Finset.sum_le_sum fun i _ => hd i
    _ = _ := by simp

theorem exists_image_intersection_basis_exp_height (A : ∀ i, Matrix κ (ρ i) ℚ)
    {H : ℕ} (hHpos : 1 ≤ H) (hA : ∀ i j k, RationalHeightLE (A i j k) H)
    {p : ℝ} (hp : 0 ≤ p) (hcount : (Fintype.card η : ℝ) ≤ p)
    (hdim : (Fintype.card κ : ℝ) ≤ p)
    (hcols : ((∑ i, Fintype.card (ρ i) : ℕ) : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) :
    ∃ b : Module.Basis (Fin (Module.finrank ℚ
        (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ))))
      ℚ (⨅ i, LinearMap.range (A i).mulVecLin : Submodule ℚ (κ → ℚ)), ∀ i j,
        ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤ Real.exp ((p + 2) ^ 63) ∧
        ((((b i : κ → ℚ) j).den) : ℝ) ≤ Real.exp ((p + 2) ^ 63) := by
  obtain ⟨r, hr, b, hb⟩ := exists_bounded_image_intersection_basis A hHpos hA
  let M := ∑ i, Fintype.card (ρ i)
  have hK := rationalKernelHeight_le_budget M H hp hcols hH
  have hrp : (r : ℝ) ≤ (p + 2) ^ 7 := by
    calc
      (r : ℝ) ≤ (Fintype.card η : ℝ) * Fintype.card κ := by exact_mod_cast hr
      _ ≤ (p + 2) ^ 2 := by nlinarith [mul_le_mul hcount hdim (Nat.cast_nonneg _) hp]
      _ ≤ (p + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by decide)
  have hbudget : (rationalKernelHeight r (rationalKernelHeight M H) : ℝ) ≤
      Real.exp ((p + 2) ^ 63) := by
    have h := rationalKernelHeight_le_budget r (rationalKernelHeight M H)
      (by positivity : 0 ≤ (p + 2) ^ 7) hrp hK
    exact exponential_budget_comp hp (by positivity) 7 7 le_rfl h
  refine ⟨b, fun i j => ?_⟩
  constructor
  · exact (show ((((b i : κ → ℚ) j).num.natAbs) : ℝ) ≤
      rationalKernelHeight r (rationalKernelHeight M H) from
      by exact_mod_cast (hb i j).1).trans hbudget
  · exact (show ((((b i : κ → ℚ) j).den) : ℝ) ≤
      rationalKernelHeight r (rationalKernelHeight M H) from
      by exact_mod_cast (hb i j).2).trans hbudget

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalSpanGrid
namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

variable {ι κ : Type*}

def IntegralVector (x : ι → ℚ) : Prop := ∃ z : ι → ℤ, ∀ i, x i = (z i : ℚ)

theorem IntegralVector.nat_smul {x : ι → ℚ} (hx : IntegralVector x) (n : ℕ) :
    IntegralVector ((n : ℚ) • x) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨fun i => (n : ℤ) * z i, fun i => ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul, hz, Int.cast_mul, Int.cast_natCast]

def scaledIntegerGrid (L : ℕ) : Set (ι → ℚ) :=
  {x | ∃ z : ι → ℤ, x = (L : ℚ) • (fun i => (z i : ℚ))}

def denominatorGrid (L : ℕ) : Set (ι → ℚ) :=
  {x | IntegralVector ((L : ℚ) • x)}

theorem mem_denominatorGrid_iff (L : ℕ) (hL : 0 < L) (x : ι → ℚ) :
    x ∈ denominatorGrid L ↔ ∃ z : ι → ℤ, ∀ i, x i = (z i : ℚ) / L := by
  have hLq : (L : ℚ) ≠ 0 := by exact_mod_cast hL.ne'
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    apply (eq_div_iff hLq).mpr
    simpa only [Pi.smul_apply, smul_eq_mul, mul_comm] using hz i
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    change (L : ℚ) * x i = (z i : ℚ)
    rw [hz i, mul_div_cancel₀ _ hLq]

variable [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def matrixDenominator (A : Matrix ι κ ℚ) : ℕ :=
  arrayDenominator (fun ij : ι × κ => A ij.1 ij.2)

def clearedMatrix (A : Matrix ι κ ℚ) : Matrix ι κ ℤ :=
  fun i j => clearedArray (fun ij : ι × κ => A ij.1 ij.2) (i, j)

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixDenominator_pos (A : Matrix ι κ ℚ) : 0 < matrixDenominator A :=
  arrayDenominator_pos _

omit [DecidableEq ι] [DecidableEq κ] in
theorem matrixDenominator_le (A : Matrix ι κ ℚ) {H : ℕ}
    (hA : ∀ i j, RationalHeightLE (A i j) H) :
    matrixDenominator A ≤ H ^ (Fintype.card ι * Fintype.card κ) := by
  simpa only [matrixDenominator, Fintype.card_prod] using
    arrayDenominator_le (fun ij : ι × κ => A ij.1 ij.2) (fun ij => (hA ij.1 ij.2).2)

theorem clearedMatrix_cast (A : Matrix ι κ ℚ) :
    (clearedMatrix A).map (Int.castRingHom ℚ) = (matrixDenominator A : ℚ) • A := by
  ext i j
  exact clearedArray_cast (fun ij : ι × κ => A ij.1 ij.2) (i, j)

theorem integralVector_denominator_mulVec (A : Matrix ι κ ℚ) (x : κ → ℚ)
    (hx : IntegralVector x) :
    IntegralVector ((matrixDenominator A : ℚ) • (A *ᵥ x)) := by
  obtain ⟨z, hz⟩ := hx
  have hx_eq : x = fun i => (z i : ℚ) := funext hz
  refine ⟨(clearedMatrix A) *ᵥ z, fun i => ?_⟩
  rw [← Matrix.smul_mulVec, ← clearedMatrix_cast, hx_eq]
  exact ((Int.castRingHom ℚ).map_mulVec (clearedMatrix A) z i).symm

theorem exists_bounded_rational_left_inverse (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H : ℕ} (hH : 1 ≤ H)
    (hB : ∀ i j, RationalHeightLE (B i j) H) :
    ∃ C : Matrix κ ι ℚ, C * B = 1 ∧
      ∀ i j, RationalHeightLE (C i j) (rationalSolveHeight (Fintype.card κ) H) := by
  have hsurj : Function.Surjective Bᵀ.mulVec :=
    mulVec_surjective_of_independent_rows Bᵀ hli
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section Bᵀ hsurj hH (fun i j => hB j i)
  refine ⟨Sᵀ, ?_, fun i j => hSH j i⟩
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using
    congrArg Matrix.transpose hS

theorem rational_embedding_grid_bounds (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ)
    (hCB : C * B = 1) :
    scaledIntegerGrid (matrixDenominator B * matrixDenominator C) ⊆
      {x | IntegralVector (B *ᵥ x)} ∧
    {x | IntegralVector (B *ᵥ x)} ⊆
      denominatorGrid (matrixDenominator B * matrixDenominator C) := by
  constructor
  · rintro x ⟨z, rfl⟩
    have hz : IntegralVector (fun i => (z i : ℚ)) := ⟨z, fun _ => rfl⟩
    have h := (integralVector_denominator_mulVec B _ hz).nat_smul (matrixDenominator C)
    simpa only [Set.mem_ofPred_eq, Matrix.mulVec_smul, smul_smul, Nat.cast_mul, mul_comm] using h
  · intro x hx
    have h := (integralVector_denominator_mulVec C (B *ᵥ x) hx).nat_smul (matrixDenominator B)
    rw [Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul] using h

end Erdos3

end

section

namespace Erdos3

theorem rational_grid_height_le_exp (n d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hn : (n : ℝ) ≤ p) (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    ((H ^ (n * d) * rationalSolveHeight d H ^ (d * n) : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
  have hsolve := rationalSolveHeight_le_budget d H hp hd hH
  have hA := pow_le_pow_left₀ (Nat.cast_nonneg H) hH (n * d)
  have hC := pow_le_pow_left₀ (Nat.cast_nonneg (rationalSolveHeight d H)) hsolve (d * n)
  rw [← Real.exp_nat_mul] at hA hC
  have hlog : p + (p + 2) ^ 5 ≤ (p + 2) ^ 6 := by
    have hp5 := le_power_budget hp (by decide : 1 ≤ 5)
    calc
      _ ≤ 2 * (p + 2) ^ 5 := by linarith
      _ ≤ (p + 2) * (p + 2) ^ 5 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by ring
  push_cast
  calc
    _ ≤ Real.exp ((n * d : ℕ) * p) * Real.exp ((d * n : ℕ) * (p + 2) ^ 5) :=
      mul_le_mul hA hC (by positivity) (by positivity)
    _ = Real.exp ((n : ℝ) * d * (p + (p + 2) ^ 5)) := by
      rw [← Real.exp_add]; congr 1; push_cast; ring
    _ ≤ Real.exp ((p + 2) ^ 2 * (p + 2) ^ 6) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul _ hlog (by positivity) (by positivity)
      calc
        (n : ℝ) * d ≤ (p + 2) * (p + 2) := by gcongr <;> linarith
        _ = (p + 2) ^ 2 := by ring
    _ = _ := by rw [← pow_add]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem scaledIntegerGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (h : l ∣ m) :
    (scaledIntegerGrid m : Set (ι → ℚ)) ⊆ scaledIntegerGrid l := by
  obtain ⟨k, rfl⟩ := h
  rintro x ⟨z, rfl⟩
  refine ⟨fun i => (k : ℤ) * z i, ?_⟩
  ext i
  simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  ring

theorem denominatorGrid_subset_of_dvd {ι : Type*} {l m : ℕ} (h : l ∣ m) :
    (denominatorGrid l : Set (ι → ℚ)) ⊆ denominatorGrid m := by
  obtain ⟨k, rfl⟩ := h
  intro x hx
  have hmul := IntegralVector.nat_smul hx k
  change IntegralVector (((l * k : ℕ) : ℚ) • x)
  simpa only [smul_smul, Nat.cast_mul, mul_comm] using hmul

end Erdos3

end

section

namespace Erdos3

open Topology

variable {ι : Type*}

def realIntegerGrid : Set (ι → ℝ) := Set.range (fun z : ι → ℤ => fun i => (z i : ℝ))

def realDenominatorGrid (l : ℕ) : Set (ι → ℝ) :=
  (fun x : ι → ℝ => (l : ℝ) • x) ⁻¹' realIntegerGrid

theorem isClosedEmbedding_integerVectors :
    IsClosedEmbedding (fun z : ι → ℤ => fun i => (z i : ℝ)) :=
  IsClosedEmbedding.piMap (fun _ => Real.isClosedEmbedding_intCast)

theorem isClosed_realIntegerGrid : IsClosed (realIntegerGrid : Set (ι → ℝ)) :=
  isClosedEmbedding_integerVectors.isClosed_range

theorem isClosed_realDenominatorGrid (l : ℕ) :
    IsClosed (realDenominatorGrid l : Set (ι → ℝ)) :=
  isClosed_realIntegerGrid.preimage (continuous_const_smul (l : ℝ))

theorem real_cast_mem_denominatorGrid_iff (l : ℕ) (x : ι → ℚ) :
    (fun i => (x i : ℝ)) ∈ realDenominatorGrid l ↔ x ∈ denominatorGrid l := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z, fun i => ?_⟩
    have hi := (congrFun hz i).symm
    change (l : ℝ) * (x i : ℝ) = (z i : ℝ) at hi
    change (l : ℚ) * x i = (z i : ℚ)
    exact_mod_cast hi
  · rintro ⟨z, hz⟩
    refine ⟨z, funext (fun i => ?_)⟩
    have hi := hz i
    change (l : ℚ) * x i = (z i : ℚ) at hi
    change (z i : ℝ) = (l : ℝ) * (x i : ℝ)
    exact_mod_cast hi.symm

variable [Finite ι]

theorem isDiscrete_realIntegerGrid : IsDiscrete (realIntegerGrid : Set (ι → ℝ)) :=
  isClosedEmbedding_integerVectors.isEmbedding.isInducing.isDiscrete_range

theorem isDiscrete_realDenominatorGrid (l : ℕ) (hl : 0 < l) :
    IsDiscrete (realDenominatorGrid l : Set (ι → ℝ)) := by
  apply isDiscrete_realIntegerGrid.preimage (continuous_const_smul (l : ℝ)).continuousOn
  exact (Homeomorph.smulOfNeZero (α := ι → ℝ) (l : ℝ) (by exact_mod_cast hl.ne')).injective

end Erdos3

end

section

namespace Erdos3

open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem scaled_grid_mulVec (B : Matrix ι κ ℚ) (l : ℕ) (x : κ → ℚ)
    (hx : IntegralVector (B *ᵥ x)) : B *ᵥ ((l : ℚ) • x) ∈ scaledIntegerGrid l := by
  obtain ⟨z, hz⟩ := hx
  exact ⟨z, by rw [Matrix.mulVec_smul, funext hz]⟩

theorem rational_preimage_grid_transport (B : Matrix ι κ ℚ) (C : Matrix κ ι ℚ)
    (hCB : C * B = 1) (l : ℕ) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l) :
    scaledIntegerGrid (l * (matrixDenominator B * matrixDenominator C)) ⊆ B.mulVec ⁻¹' Γ ∧
      B.mulVec ⁻¹' Γ ⊆ denominatorGrid (l * (matrixDenominator B * matrixDenominator C)) := by
  constructor
  · rintro x ⟨z, rfl⟩
    apply hinner
    have hz : ((matrixDenominator B * matrixDenominator C : ℕ) : ℚ) •
        (fun i => (z i : ℚ)) ∈ scaledIntegerGrid (matrixDenominator B * matrixDenominator C) :=
      ⟨z, rfl⟩
    have h := scaled_grid_mulVec B l _ ((rational_embedding_grid_bounds B C hCB).1 hz)
    simpa only [smul_smul, Nat.cast_mul] using h
  · intro x hx
    have h := (integralVector_denominator_mulVec C ((l : ℚ) • (B *ᵥ x)) (houter hx)).nat_smul
      (matrixDenominator B)
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hCB, Matrix.one_mulVec] at h
    simpa only [denominatorGrid, Set.mem_ofPred_eq, smul_smul, Nat.cast_mul,
      mul_assoc, mul_left_comm, mul_comm] using h

theorem grid_allowance_mul_le_exp {p : ℝ} (hp : 0 ≤ p) {l K : ℕ}
    (hl : (l : ℝ) ≤ Real.exp p) (hK : (K : ℝ) ≤ Real.exp ((p + 2) ^ 8)) :
    ((l * K : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ 9) := by
  calc
    _ ≤ Real.exp p * Real.exp ((p + 2) ^ 8) := by
      rw [Nat.cast_mul]
      exact mul_le_mul hl hK (Nat.cast_nonneg _) (by positivity)
    _ = Real.exp (p + (p + 2) ^ 8) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((p + 2) ^ 9) := by
      apply Real.exp_le_exp.mpr
      have hp8 := le_power_budget hp (by decide : 1 ≤ 8)
      calc
        _ ≤ 2 * (p + 2) ^ 8 := by linarith
        _ ≤ (p + 2) * (p + 2) ^ 8 :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = _ := by ring

theorem exists_preimage_grid_exp_bound (B : Matrix ι κ ℚ)
    (hli : LinearIndependent ℚ B.col) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (B i j) H) (Γ : Set (ι → ℚ))
    (hinner : scaledIntegerGrid l ⊆ Γ) (houter : Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hn : (Fintype.card ι : ℝ) ≤ p)
    (hd : (Fintype.card κ : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ L : ℕ, 0 < L ∧ (L : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid L ⊆ B.mulVec ⁻¹' Γ ∧ B.mulVec ⁻¹' Γ ⊆ denominatorGrid L := by
  obtain ⟨C, hCB, hC⟩ := exists_bounded_rational_left_inverse B hli hHpos hB
  have hK : ((matrixDenominator B * matrixDenominator C : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ 8) := by
    have hc := Nat.mul_le_mul (matrixDenominator_le B hB) (matrixDenominator_le C hC)
    exact (show ((matrixDenominator B * matrixDenominator C : ℕ) : ℝ) ≤
      ((H ^ (Fintype.card ι * Fintype.card κ) *
        rationalSolveHeight (Fintype.card κ) H ^ (Fintype.card κ * Fintype.card ι) : ℕ) : ℝ) from
      by exact_mod_cast hc).trans (rational_grid_height_le_exp _ _ _ hp hn hd hH)
  exact ⟨l * (matrixDenominator B * matrixDenominator C),
    Nat.mul_pos hlpos (Nat.mul_pos (matrixDenominator_pos B) (matrixDenominator_pos C)),
    grid_allowance_mul_le_exp hp hl hK, rational_preimage_grid_transport B C hCB l Γ hinner houter⟩

end Erdos3

end

section

namespace Erdos3

theorem grid_box_count_le_exp (C d l : ℕ) (hC : 2 ≤ C) {p : ℝ}
    (hp : 0 ≤ p) (hd : (d : ℝ) ≤ p) (hl : (l : ℝ) ≤ Real.exp p) :
    (((2 * ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ + 1) ^ d : ℕ) : ℝ) ≤
      Real.exp ((p + (C + 5)) ^ (C + 5)) := by
  let t := p + (C + 5 : ℕ)
  have ht : 5 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have ht1 : 1 ≤ t := by linarith
  have hpt : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) C]
  have hshift : p + C ≤ t := by dsimp [t]; push_cast; linarith
  have hpT : p ≤ t ^ C := by
    apply hpt.trans
    simpa only [pow_one] using pow_le_pow_right₀ ht1 (show 1 ≤ C by omega)
  have hprod : (l : ℝ) * Real.exp ((p + C) ^ C) ≤ Real.exp (t ^ (C + 1)) := by
    calc
      _ ≤ Real.exp (t ^ C) * Real.exp (t ^ C) :=
        mul_le_mul (hl.trans (Real.exp_le_exp.mpr hpT))
          (Real.exp_le_exp.mpr (pow_le_pow_left₀ (by positivity) hshift C))
          (by positivity) (by positivity)
      _ = Real.exp (2 * t ^ C) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [pow_succ]
        nlinarith [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ C)]
  have hceil := (Nat.ceil_lt_add_one
    (show 0 ≤ (l : ℝ) * Real.exp ((p + C) ^ C) by positivity)).le
  have hone : 1 ≤ Real.exp (t ^ (C + 1)) := Real.one_le_exp (by positivity)
  have hcount : ((2 * ⌈(l : ℝ) * Real.exp ((p + C) ^ C)⌉₊ + 1 : ℕ) : ℝ) ≤
      Real.exp (t ^ (C + 2)) := by
    have hfive : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
    calc
      _ ≤ 5 * Real.exp (t ^ (C + 1)) := by push_cast; linarith
      _ ≤ Real.exp 4 * Real.exp (t ^ (C + 1)) :=
        mul_le_mul_of_nonneg_right hfive (by positivity)
      _ = Real.exp (4 + t ^ (C + 1)) := (Real.exp_add _ _).symm
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show C + 2 = (C + 1) + 1 by omega, pow_succ t (C + 1)]
        have hpow : 1 ≤ t ^ (C + 1) := one_le_pow₀ ht1
        nlinarith [mul_le_mul_of_nonneg_right ht (by positivity : 0 ≤ t ^ (C + 1))]
  rw [Nat.cast_pow]
  calc
    _ ≤ (Real.exp (t ^ (C + 2))) ^ d := pow_le_pow_left₀ (Nat.cast_nonneg _) hcount d
    _ = Real.exp ((d : ℝ) * t ^ (C + 2)) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (t ^ (C + 3)) := by
      apply Real.exp_le_exp.mpr
      rw [show C + 3 = (C + 2) + 1 by omega, pow_succ' t (C + 2)]
      exact mul_le_mul_of_nonneg_right (hd.trans hpt) (by positivity)
    _ ≤ Real.exp (t ^ (C + 5)) := Real.exp_le_exp.mpr (pow_le_pow_right₀ ht1 (by omega))
    _ = _ := by simp [t]

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

theorem grid_det_integer_multiple {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (l : ℕ)
    (hA : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l) :
    ∃ z : ℤ, (l : ℝ) ^ Fintype.card ι * A.det = (z : ℝ) := by
  choose z hz using hA
  let B : Matrix ι ι ℤ := fun i j => z j i
  have he : B.map (Int.castRingHom ℝ) = (l : ℝ) • A := by
    ext i j
    exact congrFun (hz j) i
  refine ⟨B.det, ?_⟩
  rw [← Matrix.det_smul, ← he]
  exact ((Int.castRingHom ℝ).map_det B).symm

theorem one_div_pow_le_abs_grid_det {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (l : ℕ) (hl : 0 < l)
    (hA : ∀ j, (fun i => A i j) ∈ realDenominatorGrid l) (hne : A.det ≠ 0) :
    1 / (l : ℝ) ^ Fintype.card ι ≤ |A.det| := by
  have hlpos : (0 : ℝ) < l := by exact_mod_cast hl
  obtain ⟨z, hz⟩ := grid_det_integer_multiple A l hA
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0, Int.cast_zero] at hz
    exact (mul_ne_zero (pow_ne_zero _ hlpos.ne') hne) hz
  have habs : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast Int.one_le_abs hz0
  rw [← hz, abs_mul, abs_of_pos (pow_pos hlpos _)] at habs
  exact (div_le_iff₀ (pow_pos hlpos _)).mpr (by simpa only [mul_comm] using habs)

end Erdos3

end

section

namespace Erdos3

theorem realDenominatorGrid_nat_smul_iff {ι : Type*} (l m : ℕ) (x : ι → ℝ) :
    (l : ℝ) • x ∈ realDenominatorGrid m ↔ x ∈ realDenominatorGrid (m * l) := by
  change (m : ℝ) • ((l : ℝ) • x) ∈ realIntegerGrid ↔ ((m * l : ℕ) : ℝ) • x ∈ realIntegerGrid
  rw [Nat.cast_mul, mul_smul]

theorem linearMap_grid_of_integer {ι κ V : Type*} [AddCommGroup V] [Module ℝ V]
    (c : V →ₗ[ℝ] (ι → ℝ)) (f : V →ₗ[ℝ] (κ → ℝ)) (δ : ℕ)
    (hf : ∀ x, c x ∈ realDenominatorGrid 1 → f x ∈ realDenominatorGrid δ)
    (l : ℕ) (x : V) (hx : c x ∈ realDenominatorGrid l) :
    f x ∈ realDenominatorGrid (δ * l) := by
  have hc : c ((l : ℝ) • x) ∈ realDenominatorGrid 1 := by
    rw [map_smul, realDenominatorGrid_nat_smul_iff, one_mul]
    exact hx
  have h := hf ((l : ℝ) • x) hc
  rw [map_smul, realDenominatorGrid_nat_smul_iff] at h
  exact h

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ V : Type*} [Fintype ι] [Fintype κ] [AddCommGroup V] [Module ℚ V]

noncomputable def spanningCoordinateMatrix (e : Basis ι ℚ V) (v : κ → V) : Matrix ι κ ℚ :=
  fun i j => e.repr (v j) i

theorem spanningCoordinateMatrix_mulVec (e : Basis ι ℚ V) (v : κ → V) (t : κ → ℚ) :
    e.equivFun (∑ j, t j • v j) = spanningCoordinateMatrix e v *ᵥ t := by
  ext i
  simp [spanningCoordinateMatrix, Matrix.mulVec, dotProduct, mul_comm]

noncomputable def rationalSpanGridStep (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) : ℕ :=
  l * matrixDenominator (spanningCoordinateMatrix e v)

theorem rationalSpanGridStep_pos (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) (hl : 0 < l) :
    0 < rationalSpanGridStep e v l :=
  Nat.mul_pos hl (matrixDenominator_pos _)

theorem rationalSpanGridStep_le (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H) :
    rationalSpanGridStep e v l ≤ l * H ^ (Fintype.card ι * Fintype.card κ) :=
  Nat.mul_le_mul_left l (matrixDenominator_le _ hv)

theorem rationalSpanGridStep_combination (e : Basis ι ℚ V) (v : κ → V) (l : ℕ) (z : κ → ℤ) :
    e.equivFun (∑ j, ((z j : ℚ) * (rationalSpanGridStep e v l : ℚ)) • v j) ∈ scaledIntegerGrid l := by
  classical
  let B := spanningCoordinateMatrix e v
  have hz : IntegralVector (fun j => (z j : ℚ)) := ⟨z, fun _ => rfl⟩
  have hB : IntegralVector (B *ᵥ ((matrixDenominator B : ℚ) • (fun j => (z j : ℚ)))) := by
    rw [Matrix.mulVec_smul]
    exact integralVector_denominator_mulVec B _ hz
  have heq : (fun j => (z j : ℚ) * (rationalSpanGridStep e v l : ℚ)) =
      (l : ℚ) • ((matrixDenominator B : ℚ) • (fun j => (z j : ℚ))) := by
    ext j
    simp only [rationalSpanGridStep, Nat.cast_mul, Pi.smul_apply, smul_eq_mul, B]
    ring
  rw [spanningCoordinateMatrix_mulVec, heq]
  exact scaled_grid_mulVec B l _ hB

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RealGridSeparation
namespace OAI

section

namespace Erdos3

theorem eq_zero_of_mem_realDenominatorGrid_of_abs_lt {ι : Type*} {l : ℕ}
    (hl : 0 < l) {v : ι → ℝ} (hv : v ∈ realDenominatorGrid l)
    (hsmall : ∀ i, |v i| < 1 / (l : ℝ)) : v = 0 := by
  obtain ⟨z, hz⟩ := hv
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  funext i
  have hzi : (z i : ℝ) = (l : ℝ) * v i := congrFun hz i
  have habs : |(z i : ℝ)| < 1 := by
    rw [hzi, abs_mul, abs_of_pos hl']
    simpa only [mul_comm] using (lt_div_iff₀ hl').mp (hsmall i)
  have hz0 : z i = 0 := by
    have h : |z i| < (1 : ℤ) := by exact_mod_cast habs
    have := abs_lt.mp h
    omega
  have hv0 : (l : ℝ) * v i = 0 := by simpa only [hz0, Int.cast_zero] using hzi.symm
  exact (mul_eq_zero.mp hv0).resolve_left hl'.ne'

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RationalMatrixSeparation
namespace OAI

section

namespace Erdos3

theorem rational_abs_real_le_numerator (q : ℚ) :
    |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have hdenabs : |(q.den : ℝ)| = (q.den : ℝ) := abs_of_nonneg (Nat.cast_nonneg _)
  rw [Rat.cast_def, abs_div, hdenabs]
  have hden : (1 : ℝ) ≤ q.den := by exact_mod_cast q.den_pos
  simpa only [Nat.cast_natAbs, Int.cast_abs] using div_le_self (abs_nonneg (q.num : ℝ)) hden

theorem RationalHeightLE.abs_real_le {q : ℚ} {H : ℕ} (hq : RationalHeightLE q H) :
    |(q : ℝ)| ≤ H :=
  (rational_abs_real_le_numerator q).trans (Nat.cast_le.mpr hq.1)

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

theorem boundedSpanCell_linear_bound (v : ι → V) (f : V →ₗ[ℝ] ℝ) {c H : ℝ}
    (hc : 0 ≤ c) (hv : ∀ i, |f (v i)| ≤ H) {x : V} (hx : x ∈ boundedSpanCell v c) :
    |f x| ≤ Fintype.card ι * c * H := by
  classical
  obtain ⟨t, ht, rfl⟩ := hx
  simp only [map_sum, map_smul, smul_eq_mul]
  calc
    _ ≤ ∑ i, |t i * f (v i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : ι, c * H := by
      apply Finset.sum_le_sum
      intro i _
      have hi := ht i (Set.mem_univ i)
      rw [abs_mul, abs_of_nonneg hi.1]
      exact mul_le_mul hi.2 (hv i) (abs_nonneg _) hc
    _ = _ := by simp [mul_assoc]

theorem boundedSpanCell_coordinate_bound (e : Module.Basis κ ℝ V) (v : ι → V) {c H : ℝ}
    (hc : 0 ≤ c) (hv : ∀ i j, |e.repr (v i) j| ≤ H) {x : V}
    (hx : x ∈ boundedSpanCell v c) (j : κ) :
    |e.repr x j| ≤ Fintype.card ι * c * H :=
  boundedSpanCell_linear_bound v (e.coord j) hc (fun i => hv i j) hx

end Erdos3

end

section

namespace Erdos3

open scoped Matrix NNReal

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

theorem real_matrix_denominator_grid (Q : Matrix ι κ ℚ) (l : ℕ) (x : κ → ℝ)
    (hx : x ∈ realDenominatorGrid l) :
    (fun i j => (Q i j : ℝ)) *ᵥ x ∈ realDenominatorGrid (matrixDenominator Q * l) := by
  classical
  obtain ⟨z, hz⟩ := hx
  have hcoef (i : ι) (j : κ) :
      ((clearedMatrix Q i j : ℤ) : ℝ) = (matrixDenominator Q : ℝ) * (Q i j : ℝ) := by
    have h := congrFun (congrFun (clearedMatrix_cast Q) i) j
    change ((clearedMatrix Q i j : ℤ) : ℚ) = (matrixDenominator Q : ℚ) * Q i j at h
    exact_mod_cast h
  refine ⟨clearedMatrix Q *ᵥ z, funext fun i => ?_⟩
  change (((clearedMatrix Q *ᵥ z) i : ℤ) : ℝ) =
    ((matrixDenominator Q * l : ℕ) : ℝ) * ((fun i j => (Q i j : ℝ)) *ᵥ x) i
  simp only [Matrix.mulVec, dotProduct, Int.cast_sum, Int.cast_mul, Nat.cast_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  have hj : (z j : ℝ) = (l : ℝ) * x j := congrFun hz j
  rw [hcoef, hj]
  ring

omit [Fintype ι] in

theorem abs_matrix_mulVec_le (Q : Matrix ι κ ℝ) (H : ℝ≥0)
    (hQ : ∀ i j, |Q i j| ≤ H) (x : κ → ℝ) (i : ι) :
    |(Q *ᵥ x) i| ≤ ((Fintype.card κ : ℝ) + 1) * (H + 1) * ‖x‖ := by
  classical
  calc
    _ ≤ ∑ j, |Q i j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : κ, (H : ℝ) * ‖x‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hQ i j) (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)
        (abs_nonneg _) H.coe_nonneg
    _ = (Fintype.card κ : ℝ) * H * ‖x‖ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    _ ≤ _ := by gcongr <;> linarith

theorem rational_matrix_kernel_separation (Q : Matrix ι κ ℚ) (H : ℝ≥0)
    (hQ : ∀ i j, |(Q i j : ℝ)| ≤ H) (l : ℕ) (hl : 0 < l) (x y : κ → ℝ)
    (hx : x ∈ realDenominatorGrid l)
    (hy : (fun i j => (Q i j : ℝ)) *ᵥ y = 0)
    (hnear : ((matrixDenominator Q * l : ℕ) : ℝ) *
      (((Fintype.card κ : ℝ) + 1) * (H + 1)) * dist x y < 1) :
    (fun i j => (Q i j : ℝ)) *ᵥ x = 0 := by
  have hD : 0 < matrixDenominator Q * l := Nat.mul_pos (matrixDenominator_pos Q) hl
  apply eq_zero_of_mem_realDenominatorGrid_of_abs_lt hD (real_matrix_denominator_grid Q l x hx)
  intro i
  have hbound := abs_matrix_mulVec_le (fun i j => (Q i j : ℝ)) H hQ (x - y) i
  have heq := Matrix.mulVec_sub (fun i j => (Q i j : ℝ)) x y
  rw [hy, sub_zero] at heq
  rw [heq, ← dist_eq_norm] at hbound
  apply (lt_div_iff₀ (show (0 : ℝ) < ((matrixDenominator Q * l : ℕ) : ℝ) by exact_mod_cast hD)).mpr
  calc
    |((fun i j => (Q i j : ℝ)) *ᵥ x) i| * ((matrixDenominator Q * l : ℕ) : ℝ) ≤
        (((Fintype.card κ : ℝ) + 1) * (H + 1) * dist x y) * ((matrixDenominator Q * l : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ < 1 := by nlinarith [hnear]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialCongruence
namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem integer_polynomial_sub_dvd {σ : Type*} (P : MvPolynomial σ ℤ)
    (x y : σ → ℤ) (m : ℤ) (hxy : ∀ i, m ∣ x i - y i) :
    m ∣ eval x P - eval y P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ =>
    rw [eval_add, eval_add, add_sub_add_comm]
    exact dvd_add hP hQ
  | mul_X P i hP =>
    rw [eval_mul, eval_mul, eval_X, eval_X]
    have heq : eval x P * x i - eval y P * y i =
        (eval x P - eval y P) * x i + eval y P * (x i - y i) := by ring
    rw [heq]
    exact dvd_add (dvd_mul_of_dvd_left hP _) (dvd_mul_of_dvd_right (hxy i) _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTermCount
namespace OAI

section

namespace Erdos3

theorem polynomial_support_card_le {σ R : Type*} [Fintype σ] [CommSemiring R]
    (p : MvPolynomial σ R) {s : ℕ} (hp : p.totalDegree ≤ s) :
    p.support.card ≤ (s + 1) * (Fintype.card σ + 1) ^ s := by
  classical
  let code : p.support → (Σ n : Fin (s + 1), Fin n.val → σ) := fun m =>
    ⟨⟨m.val.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le ((MvPolynomial.le_totalDegree m.property).trans hp)⟩,
      m.val.toMultiset.toList.get⟩
  have hinj : Function.Injective code := by
    intro m n hmn
    have hl := congrArg (fun z : Σ n : Fin (s + 1), Fin n.val → σ => List.ofFn z.2) hmn
    change List.ofFn m.val.toMultiset.toList.get = List.ofFn n.val.toMultiset.toList.get at hl
    rw [List.ofFn_get, List.ofFn_get] at hl
    have hm := congrArg (fun l : List σ => (l : Multiset σ)) hl
    rw [Multiset.coe_toList, Multiset.coe_toList] at hm
    apply Subtype.ext
    ext x
    have hx := congrArg (fun m : Multiset σ => m.count x) hm
    simpa only [Finsupp.count_toMultiset] using hx
  have hcard := Fintype.card_le_of_injective code hinj
  simp only [Fintype.card_coe, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hcard
  calc
    p.support.card ≤ ∑ n : Fin (s + 1), Fintype.card σ ^ n.val := hcard
    _ ≤ ∑ _n : Fin (s + 1), (Fintype.card σ + 1) ^ s := by
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = (s + 1) * (Fintype.card σ + 1) ^ s := by simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialIntegerInputs
namespace OAI

section

namespace Erdos3

open MvPolynomial

def RationalPolynomialHeightLE {σ : Type*} (p : MvPolynomial σ ℚ) (H : ℕ) : Prop :=
  ∀ m, RationalHeightLE (p.coeff m) H

namespace RationalPolynomialHeightLE

variable {σ : Type*} {p : MvPolynomial σ ℚ} {H K : ℕ}

theorem mono (hp : RationalPolynomialHeightLE p H) (hHK : H ≤ K) :
    RationalPolynomialHeightLE p K := fun m => (hp m).mono hHK

theorem one_le (hp : RationalPolynomialHeightLE p H) : 1 ≤ H :=
  (Nat.one_le_iff_ne_zero.mpr (p.coeff 0).den_ne_zero).trans (hp 0).2

theorem X (x : σ) : RationalPolynomialHeightLE (MvPolynomial.X x : MvPolynomial σ ℚ) 1 := by
  classical
  intro m
  rw [coeff_X]
  split_ifs
  · exact rationalHeightLE_one le_rfl
  · exact rationalHeightLE_zero le_rfl

theorem C_mul {q : ℚ} (hq : RationalHeightLE q H)
    (hp : RationalPolynomialHeightLE p K) :
    RationalPolynomialHeightLE (MvPolynomial.C q * p) (H * K) := by
  intro m
  rw [coeff_C_mul]
  exact hq.mul (hp m)

theorem mul_X (hp : RationalPolynomialHeightLE p H) (x : σ) :
    RationalPolynomialHeightLE (p * MvPolynomial.X x) H := by
  classical
  intro m
  rw [coeff_mul_X']
  split_ifs
  · exact hp _
  · exact rationalHeightLE_zero hp.one_le

theorem sum {ι : Type*} [Fintype ι] (p : ι → MvPolynomial σ ℚ)
    (hp : ∀ i, RationalPolynomialHeightLE (p i) H) :
    RationalPolynomialHeightLE (∑ i, p i) ((Fintype.card ι + 1) * H ^ Fintype.card ι) := by
  classical
  intro m
  rw [coeff_sum]
  exact rationalHeightLE_sum (fun i => (p i).coeff m) (fun i => hp i m)

theorem sum_finset {ι : Type*} (t : Finset ι) (p : ι → MvPolynomial σ ℚ)
    (hp : ∀ i ∈ t, RationalPolynomialHeightLE (p i) H) :
    RationalPolynomialHeightLE (∑ i ∈ t, p i) ((t.card + 1) * H ^ t.card) := by
  classical
  simpa only [Fintype.card_coe, Finset.sum_coe_sort] using
    sum (fun i : t => p i) (fun i => hp i i.property)

end RationalPolynomialHeightLE

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*}

noncomputable def polynomialDenominator (P : MvPolynomial σ ℚ) : ℕ :=
  arrayDenominator (fun m : P.support => P.coeff m.val)

theorem polynomialDenominator_pos (P : MvPolynomial σ ℚ) : 0 < polynomialDenominator P :=
  arrayDenominator_pos _

theorem polynomialDenominator_le (P : MvPolynomial σ ℚ) {H : ℕ}
    (hP : RationalPolynomialHeightLE P H) : polynomialDenominator P ≤ H ^ P.support.card := by
  simpa only [polynomialDenominator, Fintype.card_coe] using
    arrayDenominator_le (fun m : P.support => P.coeff m.val) (fun m => (hP m.val).2)

noncomputable def integralNumeratorPolynomial (P : MvPolynomial σ ℚ) (q s : ℕ) :
    MvPolynomial σ ℤ := by
  classical
  exact ∑ m : P.support, monomial m.val
    (clearedArray (fun n : P.support => P.coeff n.val) m * (q : ℤ) ^ (s - m.val.sum (fun _ n => n)))

theorem product_scaled_powers [Fintype σ] (x : σ → ℚ) (q : ℚ) (m : σ →₀ ℕ) :
    (∏ i, (q * x i) ^ m i) = q ^ m.sum (fun _ n => n) * ∏ i, x i ^ m i := by
  classical
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]

theorem integralNumeratorPolynomial_eval [Fintype σ] (P : MvPolynomial σ ℚ) (q s : ℕ)
    (hdegree : P.totalDegree ≤ s) (x : σ → ℚ) (z : σ → ℤ)
    (hz : ∀ i, (q : ℚ) * x i = (z i : ℚ)) :
    ((eval z (integralNumeratorPolynomial P q s) : ℤ) : ℚ) =
      (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * eval x P := by
  classical
  rw [integralNumeratorPolynomial, map_sum]
  push_cast
  simp only [eval_monomial, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
  rw [eval_eq']
  rw [← Finset.sum_coe_sort P.support]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  have hm : m.val.sum (fun _ n => n) ≤ s := (le_totalDegree m.property).trans hdegree
  rw [clearedArray_cast]
  have hprod : ((m.val.prod (fun i n => z i ^ n) : ℤ) : ℚ) =
      (q : ℚ) ^ m.val.sum (fun _ n => n) * ∏ i, x i ^ m.val i := by
    rw [Finsupp.prod_pow]
    simp only [Int.cast_prod, Int.cast_pow]
    simp_rw [← hz]
    exact product_scaled_powers x (q : ℚ) m.val
  rw [hprod]
  change ((polynomialDenominator P : ℚ) * P.coeff m.val) * (q : ℚ) ^ (s - m.val.sum (fun _ n => n)) *
      ((q : ℚ) ^ m.val.sum (fun _ n => n) * ∏ i, x i ^ m.val i) = _
  calc
    _ = (polynomialDenominator P : ℚ) *
        ((q : ℚ) ^ (s - m.val.sum (fun _ n => n)) * (q : ℚ) ^ m.val.sum (fun _ n => n)) *
        (P.coeff m.val * ∏ i, x i ^ m.val i) := by ring
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hm]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem abs_aeval_le_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (v : σ → ℝ) {A B : ℝ} {s : ℕ} (hA : 0 ≤ A) (hB : 1 ≤ B)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A) (hv : ∀ i, |v i| ≤ B)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P| ≤ P.support.card * A * B ^ s := by
  classical
  change |P.eval₂ (algebraMap ℚ ℝ) v| ≤ _
  rw [eval₂_eq']
  calc
    _ ≤ ∑ m ∈ P.support, |algebraMap ℚ ℝ (P.coeff m) * ∏ i, v i ^ m i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ P.support, A * B ^ s := by
      apply Finset.sum_le_sum
      intro m hm
      rw [abs_mul, Finset.abs_prod]
      have hprod : (∏ i, |v i ^ m i|) ≤ B ^ s := by
        calc
          _ = ∏ i, |v i| ^ m i := by simp only [abs_pow]
          _ ≤ ∏ i, B ^ m i :=
            Finset.prod_le_prod (fun _ _ => by positivity)
              (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hv i) _)
          _ = B ^ (∑ i, m i) := Finset.prod_pow_eq_pow_sum _ _ _
          _ ≤ B ^ s := by
            apply pow_le_pow_right₀ hB
            have hmdegree := (le_totalDegree hm).trans hdegree
            rwa [Finsupp.sum_fintype _ _ (fun _ => rfl)] at hmdegree
      exact mul_le_mul (hcoeff m) hprod (by positivity) hA
    _ = _ := by simp [mul_assoc]

end Erdos3

end

section

namespace Erdos3

open MvPolynomial
open scoped NNReal

theorem abs_aeval_sub_aeval_box_bound {σ : Type*} [Fintype σ] (P : MvPolynomial σ ℚ)
    (v w : σ → ℝ) {A B δ : ℝ} {s : ℕ} (hA : 0 ≤ A) (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hcoeff : ∀ m, |((P.coeff m : ℚ) : ℝ)| ≤ A)
    (hv : ∀ i, |v i| ≤ B) (hw : ∀ i, |w i| ≤ B) (hvw : ∀ i, |v i - w i| ≤ δ)
    (hdegree : P.totalDegree ≤ s) :
    |aeval v P - aeval w P| ≤
      P.support.card * A * Fintype.card σ * s * B ^ (s * (Fintype.card σ + 1)) * δ := by
  classical
  have hmonomial (m : σ →₀ ℕ) (hm : m ∈ P.support) :
      |(∏ i, v i ^ m i) - ∏ i, w i ^ m i| ≤
        Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ := by
    have hmdeg (i : σ) : m i ≤ s :=
      (monomial_le_degreeOf i hm).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ B) (i : σ) : |u i ^ m i| ≤ B ^ s := by
      rw [abs_pow]
      exact (pow_le_pow_left₀ (abs_nonneg _) (hu i) _).trans (pow_le_pow_right₀ hB (hmdeg i))
    simpa only [Finset.card_univ] using
      abs_finset_prod_sub_prod_le Finset.univ (fun i => v i ^ m i) (fun i => w i ^ m i)
        (one_le_pow₀ hB) (by positivity)
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i)
        (fun i _ => abs_pow_sub_pow_box_bound hB hδ (hv i) (hw i) (hvw i) (hmdeg i))
  change |P.eval₂ (algebraMap ℚ ℝ) v - P.eval₂ (algebraMap ℚ ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ m ∈ P.support, |algebraMap ℚ ℝ (P.coeff m) * ∏ i, v i ^ m i -
          algebraMap ℚ ℝ (P.coeff m) * ∏ i, w i ^ m i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _m ∈ P.support, A * (Fintype.card σ * (δ * s * B ^ s) * (B ^ s) ^ Fintype.card σ) := by
      apply Finset.sum_le_sum
      intro m hm
      rw [← mul_sub, abs_mul]
      exact mul_le_mul (hcoeff m) (hmonomial m hm) (abs_nonneg _) hA
    _ = _ := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.mul_add, Nat.mul_one, pow_add, pow_mul]
      ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem monomialScale_mul_normalized_prod {σ : Type*} [Fintype σ]
    (T v : σ → ℝ) (hT : ∀ i, 0 < T i) (α : σ →₀ ℕ) :
    monomialScale T α * (∏ i, (v i / T i) ^ α i) = ∏ i, v i ^ α i := by
  classical
  rw [monomialScale, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [← mul_pow, mul_div_cancel₀ _ (hT i).ne']

theorem abs_eval_le_scaled_box_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T v : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hv : ∀ i, |v i| ≤ T i) :
    |eval v P| ≤ P.support.card * M := by
  classical
  have hv' (i : σ) : |v i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i), div_le_one (hT i)]
    exact hv i
  change |P.eval₂ (RingHom.id ℝ) v| ≤ _
  rw [eval₂_eq']
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _α ∈ P.support, M := by
      apply Finset.sum_le_sum
      intro α _
      change |P.coeff α * ∏ i, v i ^ α i| ≤ M
      rw [← monomialScale_mul_normalized_prod T v hT α, abs_mul,
        abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      have hprod : |∏ i, (v i / T i) ^ α i| ≤ 1 := by
        rw [Finset.abs_prod]
        apply Finset.prod_le_one (fun _ _ => abs_nonneg _)
        intro i _
        rw [abs_pow]
        exact pow_le_one₀ (abs_nonneg _) (hv' i)
      calc
        _ ≤ (M / monomialScale T α) * (monomialScale T α * 1) :=
          mul_le_mul (hcoeff α)
            (mul_le_mul_of_nonneg_left hprod (monomialScale_pos T hT α).le)
            (mul_nonneg (monomialScale_pos T hT α).le (abs_nonneg _))
            (div_nonneg hM (monomialScale_pos T hT α).le)
        _ = M := by rw [mul_one, div_mul_cancel₀ _ (monomialScale_pos T hT α).ne']
    _ = _ := by simp

theorem abs_eval_sub_eval_scaled_box_bound {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℝ) (T v w : σ → ℝ) (hT : ∀ i, 0 < T i)
    {M δ : ℝ} {s : ℕ} (hM : 0 ≤ M) (hδ : 0 ≤ δ)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale T α)
    (hv : ∀ i, |v i| ≤ T i) (hw : ∀ i, |w i| ≤ T i)
    (hvw : ∀ i, |v i - w i| ≤ T i * δ) (hdegree : P.totalDegree ≤ s) :
    |eval v P - eval w P| ≤ P.support.card * M * Fintype.card σ * s * δ := by
  classical
  have hunit (u : σ → ℝ) (hu : ∀ i, |u i| ≤ T i) (i : σ) :
      |u i / T i| ≤ 1 := by
    rw [abs_div, abs_of_pos (hT i), div_le_one (hT i)]
    exact hu i
  have hdiff (i : σ) : |v i / T i - w i / T i| ≤ δ := by
    rw [← sub_div, abs_div, abs_of_pos (hT i), div_le_iff₀ (hT i), mul_comm]
    exact hvw i
  have hmonomial (α : σ →₀ ℕ) (hα : α ∈ P.support) :
      |(∏ i, (v i / T i) ^ α i) - ∏ i, (w i / T i) ^ α i| ≤
        Fintype.card σ * (δ * s) := by
    have hdeg (i : σ) : α i ≤ s :=
      (monomial_le_degreeOf i hα).trans ((degreeOf_le_totalDegree P i).trans hdegree)
    have hpow (u : σ → ℝ) (hu : ∀ i, |u i| ≤ T i) (i : σ) :
        |(u i / T i) ^ α i| ≤ 1 := by
      rw [abs_pow]
      exact pow_le_one₀ (abs_nonneg _) (hunit u hu i)
    have hp (i : σ) : |(v i / T i) ^ α i - (w i / T i) ^ α i| ≤ δ * s := by
      simpa only [one_pow, mul_one] using abs_pow_sub_pow_box_bound
        (le_refl (1 : ℝ)) hδ (hunit v hv i) (hunit w hw i) (hdiff i) (hdeg i)
    simpa only [Finset.card_univ, one_pow, mul_one] using
      abs_finset_prod_sub_prod_le Finset.univ
        (fun i => (v i / T i) ^ α i) (fun i => (w i / T i) ^ α i)
        (le_refl (1 : ℝ)) (mul_nonneg hδ (Nat.cast_nonneg s))
        (fun i _ => hpow v hv i) (fun i _ => hpow w hw i) (fun i _ => hp i)
  change |P.eval₂ (RingHom.id ℝ) v - P.eval₂ (RingHom.id ℝ) w| ≤ _
  rw [eval₂_eq', eval₂_eq', ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _α ∈ P.support, M * (Fintype.card σ * (δ * s)) := by
      apply Finset.sum_le_sum
      intro α hα
      change |P.coeff α * ∏ i, v i ^ α i - P.coeff α * ∏ i, w i ^ α i| ≤ _
      rw [← mul_sub, ← monomialScale_mul_normalized_prod T v hT α,
        ← monomialScale_mul_normalized_prod T w hT α, ← mul_sub,
        abs_mul, abs_mul, abs_of_pos (monomialScale_pos T hT α)]
      calc
        _ ≤ (M / monomialScale T α) *
            (monomialScale T α * (Fintype.card σ * (δ * s))) :=
          mul_le_mul (hcoeff α)
            (mul_le_mul_of_nonneg_left (hmonomial α hα) (monomialScale_pos T hT α).le)
            (mul_nonneg (monomialScale_pos T hT α).le (abs_nonneg _))
            (div_nonneg hM (monomialScale_pos T hT α).le)
        _ = _ := by rw [← mul_assoc, div_mul_cancel₀ _ (monomialScale_pos T hT α).ne']
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem rational_polynomial_eval_sub_integer_multiple {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (q s l : ℕ) (hq : 0 < q) (hdegree : P.totalDegree ≤ s)
    (x y : σ → ℚ) (hx : x ∈ denominatorGrid q) (hy : y ∈ denominatorGrid q)
    (hxy : x - y ∈ scaledIntegerGrid (l * polynomialDenominator P * q ^ s)) :
    ∃ k : ℤ, eval x P - eval y P = (l : ℚ) * k := by
  classical
  obtain ⟨z, hz⟩ := hx
  obtain ⟨w, hw⟩ := hy
  obtain ⟨v, hv⟩ := hxy
  let T := l * polynomialDenominator P * q ^ s
  let Q := integralNumeratorPolynomial P q s
  have hdiff : ∀ i, (T : ℤ) ∣ z i - w i := by
    intro i
    refine ⟨(q : ℤ) * v i, ?_⟩
    apply Int.cast_injective (α := ℚ)
    push_cast
    have hi := congrFun hv i
    change x i - y i = (T : ℚ) * (v i : ℚ) at hi
    have hzi : (q : ℚ) * x i = (z i : ℚ) := hz i
    have hwi : (q : ℚ) * y i = (w i : ℚ) := hw i
    rw [← hzi, ← hwi, ← mul_sub, hi]
    ring
  obtain ⟨k, hk⟩ := integer_polynomial_sub_dvd Q z w (T : ℤ) hdiff
  refine ⟨k, ?_⟩
  have hD : (polynomialDenominator P : ℚ) ≠ 0 := by exact_mod_cast (polynomialDenominator_pos P).ne'
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq.ne'
  apply mul_left_cancel₀ (mul_ne_zero hD (pow_ne_zero s hq'))
  calc
    (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * (eval x P - eval y P) =
        ((eval z Q - eval w Q : ℤ) : ℚ) := by
      push_cast
      rw [integralNumeratorPolynomial_eval P q s hdegree x z hz,
        integralNumeratorPolynomial_eval P q s hdegree y w hw]
      ring
    _ = ((T : ℤ) * k : ℤ) := by rw [hk]
    _ = (polynomialDenominator P : ℚ) * (q : ℚ) ^ s * ((l : ℚ) * k) := by
      push_cast
      dsimp [T]
      push_cast
      ring

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {ι σ : Type*} [Fintype ι]

noncomputable def polynomialFamilyDenominator (P : ι → MvPolynomial σ ℚ) : ℕ :=
  ∏ i, polynomialDenominator (P i)

theorem polynomialFamilyDenominator_pos (P : ι → MvPolynomial σ ℚ) :
    0 < polynomialFamilyDenominator P :=
  Finset.prod_pos (fun i _ => polynomialDenominator_pos (P i))

theorem polynomialDenominator_dvd_family (P : ι → MvPolynomial σ ℚ) (i : ι) :
    polynomialDenominator (P i) ∣ polynomialFamilyDenominator P :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

theorem polynomialDenominator_exp_bound (P : MvPolynomial σ ℚ) {p : ℝ}
    (hp : 0 ≤ p) (a c : ℕ)
    (hcoeff : ∀ m, ((P.coeff m).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : (P.support.card : ℝ) ≤ (p + 2) ^ c) :
    (polynomialDenominator P : ℝ) ≤ Real.exp ((p + 2) ^ (a + c)) := by
  classical
  unfold polynomialDenominator arrayDenominator
  rw [Nat.cast_prod]
  apply product_exponential_budget _ _ hp a c
  · intro i _
    positivity
  · intro i _
    exact hcoeff i.val
  · simpa only [Finset.card_univ, Fintype.card_coe] using hcard

theorem polynomialFamilyDenominator_exp_bound (P : ι → MvPolynomial σ ℚ) {p : ℝ}
    (hp : 0 ≤ p) (a b c : ℕ)
    (hcoeff : ∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp ((p + 2) ^ a))
    (hcard : ∀ i, ((P i).support.card : ℝ) ≤ (p + 2) ^ c)
    (hι : (Fintype.card ι : ℝ) ≤ (p + 2) ^ b) :
    (polynomialFamilyDenominator P : ℝ) ≤ Real.exp ((p + 2) ^ (a + c + b)) := by
  classical
  unfold polynomialFamilyDenominator
  rw [Nat.cast_prod]
  apply product_exponential_budget _ _ hp (a + c) b
  · intro i _
    positivity
  · intro i _
    exact polynomialDenominator_exp_bound (P i) hp a c (hcoeff i) (hcard i)
  · simpa only [Finset.card_univ] using hι

theorem rational_polynomial_family_eval_sub_mem_grid [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (q s l : ℕ) (hq : 0 < q)
    (hdegree : ∀ i, (P i).totalDegree ≤ s) (x y : σ → ℚ)
    (hx : x ∈ denominatorGrid q) (hy : y ∈ denominatorGrid q)
    (hxy : x - y ∈ scaledIntegerGrid (l * polynomialFamilyDenominator P * q ^ s)) :
    (fun i => eval x (P i) - eval y (P i)) ∈ scaledIntegerGrid l := by
  classical
  have h (i : ι) : ∃ k : ℤ, eval x (P i) - eval y (P i) = (l : ℚ) * k := by
    apply rational_polynomial_eval_sub_integer_multiple (P i) q s l hq (hdegree i) x y hx hy
    apply scaledIntegerGrid_subset_of_dvd _ hxy
    exact mul_dvd_mul (mul_dvd_mul dvd_rfl (polynomialDenominator_dvd_family P i)) dvd_rfl
  choose z hz using h
  exact ⟨z, funext hz⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem slowPolynomial_oscillation_on_slice {I : Type*} [Fintype I]
    (N : I → ℕ) {q : ℕ} (A : ResidueBoxSlice N q)
    (hA : ∀ i, 0 < A.length i) {ρ M : ℝ} {s : ℕ}
    (hρ : 0 ≤ ρ) (hM : 0 ≤ M) (hwidth : ∀ i, (q : ℝ) * A.length i ≤ ρ * N i)
    (P : MvPolynomial I ℝ) (hdegree : P.totalDegree ≤ s)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (j : ∀ i, Fin (A.length i)) :
    |MvPolynomial.eval (fun i => ((A.point j i).val : ℝ)) P -
        MvPolynomial.eval (fun i => (A.start i : ℝ)) P| ≤
      ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * M * Fintype.card I * s * ρ := by
  have hstart (i : I) : A.start i < N i := by
    simpa only [Nat.mul_zero, Nat.add_zero] using A.inside i 0 (hA i)
  have hN (i : I) : (0 : ℝ) < N i := by exact_mod_cast (Nat.zero_le _).trans_lt (hstart i)
  have hv (i : I) : |((A.point j i).val : ℝ)| ≤ (N i : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (A.point j i).isLt.le
  have hw (i : I) : |(A.start i : ℝ)| ≤ (N i : ℝ) := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (hstart i).le
  have hvw (i : I) : |((A.point j i).val : ℝ) - (A.start i : ℝ)| ≤ (N i : ℝ) * ρ := by
    change |((A.start i + q * (j i).val : ℕ) : ℝ) - (A.start i : ℝ)| ≤ _
    rw [Nat.cast_add, Nat.cast_mul, add_sub_cancel_left, abs_of_nonneg (by positivity)]
    have hj : ((j i).val : ℝ) ≤ A.length i := by exact_mod_cast (j i).isLt.le
    exact (mul_le_mul_of_nonneg_left hj (Nat.cast_nonneg q)).trans (by simpa [mul_comm] using hwidth i)
  have hbound := abs_eval_sub_eval_scaled_box_bound P (fun i => (N i : ℝ))
    (fun i => ((A.point j i).val : ℝ)) (fun i => (A.start i : ℝ)) hN hM hρ hcoeff hv hw hvw hdegree
  have hcard : (P.support.card : ℝ) ≤ ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s := by
    exact_mod_cast polynomial_support_card_le P hdegree
  exact hbound.trans (by gcongr)

theorem exists_slowPolynomial_residueSlice {I : Type*} [Fintype I] [DecidableEq I]
    (N : I → ℕ) {q : ℕ} (hq : 0 < q) {ρ M : ℝ} {s : ℕ}
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hM : 0 ≤ M)
    (hlarge : ∀ i, 4 * (q : ℝ) ≤ ρ * N i)
    (P : MvPolynomial I ℝ) (hdegree : P.totalDegree ≤ s)
    (hcoeff : ∀ α, |P.coeff α| ≤ M / monomialScale (fun i => (N i : ℝ)) α)
    (f : (∀ i, Fin (N i)) → ℝ) :
    ∃ A : ResidueBoxSlice N q,
      (∀ i, 0 < A.length i ∧ ρ * N i ≤ 4 * q * A.length i) ∧
      ((𝔼 x, f x) ≤ 𝔼 j : (∀ i, Fin (A.length i)), f (A.point j)) ∧
      ∀ j : (∀ i, Fin (A.length i)),
        |MvPolynomial.eval (fun i => ((A.point j i).val : ℝ)) P -
            MvPolynomial.eval (fun i => (A.start i : ℝ)) P| ≤
          ((s : ℝ) + 1) * ((Fintype.card I : ℝ) + 1) ^ s * M * Fintype.card I * s * ρ := by
  obtain ⟨A, hA, hscore⟩ := exists_narrow_residueBoxSlice N hq hρ hρ1 hlarge f
  exact ⟨A, fun i => ⟨(hA i).1, (hA i).2.1⟩, hscore,
    slowPolynomial_oscillation_on_slice N A (fun i => (hA i).1) hρ.le hM
      (fun i => (hA i).2.2) P hdegree hcoeff⟩

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem polynomialFamilyDenominator_degree_budget {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (r : ℕ) {p : ℝ}
    (hdegree : ∀ i, (P i).totalDegree ≤ r) (hp : 0 ≤ p)
    (hι : (Fintype.card ι : ℝ) ≤ p) (hσ : (Fintype.card σ : ℝ) ≤ p)
    (hcoeff : ∀ i m, (((P i).coeff m).den : ℝ) ≤ Real.exp p) :
    (polynomialFamilyDenominator P : ℝ) ≤ Real.exp ((p + (r + 3)) ^ (r + 3)) := by
  let t := p + (r + 3 : ℕ)
  have ht : 3 ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hpT : p ≤ t := by dsimp [t]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) r]
  have hr : (r : ℝ) + 1 ≤ t := by dsimp [t]; push_cast; linarith
  have hvars : (Fintype.card σ : ℝ) + 1 ≤ t := by
    dsimp [t]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) r]
  have hcard : ∀ i, ((P i).support.card : ℝ) ≤ t ^ (r + 1) := by
    intro i
    have h := (Nat.cast_le (α := ℝ)).mpr (polynomial_support_card_le (P i) (hdegree i))
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_pow, Nat.cast_one] at h
    apply h.trans
    calc
      _ ≤ t * t ^ r := mul_le_mul hr (pow_le_pow_left₀ (by positivity) hvars r) (by positivity) (by linarith)
      _ = t ^ (r + 1) := (pow_succ' _ _).symm
  have hD := polynomialFamilyDenominator_exp_bound P (p := t - 2) (by linarith) 1 1 (r + 1)
    (by intro i m; rw [sub_add_cancel, pow_one]; exact (hcoeff i m).trans (Real.exp_le_exp.mpr hpT))
    (by simpa only [sub_add_cancel] using hcard)
    (by rw [sub_add_cancel, pow_one]; exact hι.trans hpT)
  simpa only [sub_add_cancel, show 1 + (r + 1) + 1 = r + 3 by omega, t, Nat.cast_add, Nat.cast_ofNat] using hD

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

theorem polynomial_integer_value_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (z : σ → ℤ) :
    ∃ a : ℤ, (polynomialDenominator P : ℚ) * eval (fun i => (z i : ℚ)) P = (a : ℚ) := by
  refine ⟨eval z (integralNumeratorPolynomial P 1 P.totalDegree), ?_⟩
  have h := integralNumeratorPolynomial_eval P 1 P.totalDegree le_rfl
    (fun i => (z i : ℚ)) z (by simp)
  simpa only [Nat.cast_one, one_pow, mul_one] using h.symm

theorem polynomial_family_integer_values_grid {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (z : σ → ℤ) :
    (fun i => eval (fun j => (z j : ℚ)) (P i)) ∈ denominatorGrid (polynomialFamilyDenominator P) := by
  classical
  have h (i : ι) : ∃ a : ℤ,
      (polynomialFamilyDenominator P : ℚ) * eval (fun j => (z j : ℚ)) (P i) = (a : ℚ) := by
    obtain ⟨k, hk⟩ := polynomialDenominator_dvd_family P i
    obtain ⟨a, ha⟩ := polynomial_integer_value_denominator (P i) z
    refine ⟨(k : ℤ) * a, ?_⟩
    rw [hk, Nat.cast_mul]
    calc
      _ = (k : ℚ) * ((polynomialDenominator (P i) : ℚ) * eval (fun j => (z j : ℚ)) (P i)) := by ring
      _ = _ := by rw [ha]; push_cast; rfl
  choose a ha using h
  exact ⟨a, ha⟩

theorem integer_difference_mem_grid {σ : Type*} (x y : σ → ℤ) (M : ℕ)
    (hxy : ∀ i, (M : ℤ) ∣ x i - y i) :
    (fun i => (x i : ℚ)) - (fun i => (y i : ℚ)) ∈ scaledIntegerGrid M := by
  classical
  choose z hz using hxy
  refine ⟨z, ?_⟩
  funext i
  have hi := congrArg (fun a : ℤ => (a : ℚ)) (hz i)
  push_cast at hi
  exact hi

theorem polynomial_family_integer_congruence {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (r l : ℕ) (hdegree : ∀ i, (P i).totalDegree ≤ r)
    (x y : σ → ℤ) (hxy : ∀ j, ((l * polynomialFamilyDenominator P : ℕ) : ℤ) ∣ x j - y j) :
    (fun i => eval (fun j => (x j : ℚ)) (P i) - eval (fun j => (y j : ℚ)) (P i)) ∈
      scaledIntegerGrid l := by
  apply rational_polynomial_family_eval_sub_mem_grid P 1 r l (by omega) hdegree
  · exact ⟨x, by simp⟩
  · exact ⟨y, by simp⟩
  · simpa only [one_pow, mul_one] using integer_difference_mem_grid x y _ hxy

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def lieStructureConstants (e : Basis ι ℚ L) (i j k : ι) : ℚ :=
  e.repr ⁅e i, e j⁆ k

theorem lie_coordinate_formula (e : Basis ι ℚ L) (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ ij : ι × ι, lieStructureConstants e ij.1 ij.2 k * e.repr a ij.1 * e.repr b ij.2 := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type,
    lieStructureConstants, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

noncomputable def coordinateRightBracket (c : ι → ι → ι → ℚ) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ) (k : ι) : MvPolynomial (X × ι) ℚ :=
  ∑ ij : ι × ι, C (c ij.1 ij.2 k) * p ij.1 * MvPolynomial.X (x, ij.2)

noncomputable def coordinateBracketList (c : ι → ι → ι → ℚ) :
    List X → (ι → MvPolynomial (X × ι) ℚ) → (ι → MvPolynomial (X × ι) ℚ)
  | [], p => p
  | x :: xs, p => coordinateBracketList c xs (coordinateRightBracket c x p)

noncomputable def dynkinCoordinatePolynomial (c : ι → ι → ι → ℚ)
    (w : FreeSemigroup X) : ι → MvPolynomial (X × ι) ℚ :=
  coordinateBracketList c w.tail (fun i => MvPolynomial.X (w.head, i))

theorem coordinateRightBracket_eval (e : Basis ι ℚ L) (f : X → L)
    (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateRightBracket (lieStructureConstants e) x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X,
    Algebra.algebraMap_self, RingHom.id_apply, hp]
  exact (lie_coordinate_formula e a (f x) k).symm

theorem coordinateBracketList_eval (e : Basis ι ℚ L) (f : X → L) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList (lieStructureConstants e) xs p k) =
      e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket (lieStructureConstants e) x p) ⁅a, f x⁆
      (coordinateRightBracket_eval e f p a hp x)

theorem dynkinCoordinatePolynomial_eval (e : Basis ι ℚ L) (f : X → L)
    (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (dynkinCoordinatePolynomial (lieStructureConstants e) w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval
  intro i
  simp only [aeval_X]

theorem coordinateRightBracket_totalDegree (c : ι → ι → ι → ℚ) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ n) (k : ι) :
    (coordinateRightBracket c x p k).totalDegree ≤ n + 1 := by
  apply totalDegree_finsetSum_le
  intro ij _
  exact (totalDegree_mul _ _).trans (by
    rw [totalDegree_X]
    have h := totalDegree_mul (C (c ij.1 ij.2 k)) (p ij.1)
    rw [totalDegree_C, zero_add] at h
    exact Nat.add_le_add_right (h.trans (hp ij.1)) 1)

theorem coordinateBracketList_totalDegree (c : ι → ι → ι → ℚ) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ n) (k : ι) :
    (coordinateBracketList c xs p k).totalDegree ≤ n + xs.length := by
  induction xs generalizing p n with
  | nil => exact hp k
  | cons x xs ih =>
    simpa only [coordinateBracketList, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using
      ih (coordinateRightBracket c x p) (coordinateRightBracket_totalDegree c x p hp)

theorem dynkinCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ)
    (w : FreeSemigroup X) (k : ι) :
    (dynkinCoordinatePolynomial c w k).totalDegree ≤ w.length := by
  have h := coordinateBracketList_totalDegree c w.tail
    (fun i => MvPolynomial.X (w.head, i)) (n := 1)
    (fun _ => (totalDegree_X _).le) k
  simpa only [dynkinCoordinatePolynomial, FreeSemigroup.length, Nat.add_comm] using h

noncomputable def bchCoordinatePolynomial (c : ι → ι → ι → ℚ) (s : ℕ)
    (k : ι) : MvPolynomial (Fin 2 × ι) ℚ :=
  ∑ w ∈ bchBracketSupport s,
    C (bchBracketCoefficient s w) * dynkinCoordinatePolynomial c w k

theorem bchCoordinatePolynomial_eval (e : Basis ι ℚ L) (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
        (bchCoordinatePolynomial (lieStructureConstants e) s k) = e.repr (lieBCH s a b) k := by
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply,
    dynkinCoordinatePolynomial_eval, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply,
    smul_eq_mul]

theorem bchCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ) (s : ℕ) (k : ι) :
    (bchCoordinatePolynomial c s k).totalDegree ≤ s := by
  apply totalDegree_finsetSum_le
  intro w hw
  have h := totalDegree_mul (C (bchBracketCoefficient s w)) (dynkinCoordinatePolynomial c w k)
  rw [totalDegree_C, zero_add] at h
  exact h.trans ((dynkinCoordinatePolynomial_totalDegree c w k).trans (bchBracketSupport_length s hw))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieStructureTransport
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

noncomputable def transportedLieConstants (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) (i j k : κ) : ℚ :=
  ∑ abc : ι × (ι × ι), P k abc.1 * c abc.2.1 abc.2.2 abc.1 * S abc.2.1 i * S abc.2.2 j

omit [Fintype κ] in
theorem transportedLieConstants_height (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) {Hc HP HS : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) Hc)
    (hP : ∀ i j, RationalHeightLE (P i j) HP)
    (hS : ∀ i j, RationalHeightLE (S i j) HS) (i j k : κ) :
    RationalHeightLE (transportedLieConstants c P S i j k)
      ((Fintype.card ι ^ 3 + 1) * (HP * Hc * HS * HS) ^ (Fintype.card ι ^ 3)) := by
  classical
  have h := rationalHeightLE_sum
    (fun abc : ι × (ι × ι) => P k abc.1 * c abc.2.1 abc.2.2 abc.1 * S abc.2.1 i * S abc.2.2 j)
    (fun abc => (((hP k abc.1).mul (hc abc.2.1 abc.2.2 abc.1)).mul (hS abc.2.1 i)).mul (hS abc.2.2 j))
  simpa only [transportedLieConstants, Fintype.card_prod, pow_succ, pow_zero, one_mul, mul_assoc] using h

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

omit [Fintype κ] in
theorem transportedLieConstants_formula (e : Basis ι ℚ L) (P : Matrix κ ι ℚ)
    (S : Matrix ι κ ℚ) (a b : L) (i j k : κ)
    (ha : ∀ u, e.repr a u = S u i) (hb : ∀ u, e.repr b u = S u j) :
    (P *ᵥ e.repr ⁅a, b⁆) k = transportedLieConstants (lieStructureConstants e) P S i j k := by
  classical
  simp only [Matrix.mulVec, dotProduct, transportedLieConstants, lie_coordinate_formula,
    ha, hb, Finset.mul_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro w _
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  ring

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in
theorem basisMatrix_mulVec (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (x : κ → ℚ) :
    LinearMap.toMatrix b e φ *ᵥ x = e.equivFun (φ (b.equivFun.symm x)) := by
  have h := LinearMap.toMatrix_mulVec_repr b e φ (b.equivFun.symm x)
  simpa only [← b.equivFun_apply, LinearEquiv.apply_symm_apply, ← e.equivFun_apply] using h

omit [DecidableEq ι] in
theorem basisMatrix_injective (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (hφ : Function.Injective φ) : Function.Injective (LinearMap.toMatrix b e φ).mulVec := by
  intro x y hxy
  rw [basisMatrix_mulVec, basisMatrix_mulVec] at hxy
  exact b.equivFun.symm.injective (hφ (e.equivFun.injective hxy))

omit [DecidableEq ι] in
theorem basisMatrix_surjective (b : Basis κ ℚ M) (e : Basis ι ℚ L) (φ : M →ₗ[ℚ] L)
    (hφ : Function.Surjective φ) : Function.Surjective (LinearMap.toMatrix b e φ).mulVec := by
  intro y
  obtain ⟨x, hx⟩ := hφ (e.equivFun.symm y)
  refine ⟨b.equivFun x, ?_⟩
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply, hx, LinearEquiv.apply_symm_apply]

omit [DecidableEq ι] in

theorem lieStructureConstants_embedding (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (P : Matrix κ ι ℚ)
    (hP : P * LinearMap.toMatrix b e φ.toLinearMap = 1) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      P (LinearMap.toMatrix b e φ.toLinearMap) i j k := by
  have hretract (x : M) : P *ᵥ e.repr (φ x) = b.repr x := by
    change P *ᵥ e.repr (φ.toLinearMap x) = b.repr x
    rw [← LinearMap.toMatrix_mulVec_repr b e φ.toLinearMap x, Matrix.mulVec_mulVec,
      hP, Matrix.one_mulVec]
  rw [lieStructureConstants, ← congrFun (hretract ⁅b i, b j⁆) k, LieHom.map_lie]
  apply transportedLieConstants_formula
  · intro u
    exact (LinearMap.toMatrix_apply b e φ.toLinearMap u i).symm
  · intro u
    exact (LinearMap.toMatrix_apply b e φ.toLinearMap u j).symm

theorem lieStructureConstants_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (σ : M →ₗ[ℚ] L) (hσ : ∀ x, φ (σ x) = x) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      (LinearMap.toMatrix e b φ.toLinearMap) (LinearMap.toMatrix b e σ) i j k := by
  have hbracket : ⁅b i, b j⁆ = φ ⁅σ (b i), σ (b j)⁆ := by rw [LieHom.map_lie, hσ, hσ]
  rw [lieStructureConstants, hbracket]
  change (b.repr (φ.toLinearMap ⁅σ (b i), σ (b j)⁆)) k = _
  rw [← congrFun (LinearMap.toMatrix_mulVec_repr e b φ.toLinearMap ⁅σ (b i), σ (b j)⁆) k]
  apply transportedLieConstants_formula
  · intro u
    exact (LinearMap.toMatrix_apply b e σ u i).symm
  · intro u
    exact (LinearMap.toMatrix_apply b e σ u j).symm

theorem basisMatrix_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ[ℚ] M) (S : Matrix ι κ ℚ)
    (hS : LinearMap.toMatrix e b φ * S = 1) (x : M) :
    φ (Matrix.toLin b e S x) = x := by
  apply b.equivFun.injective
  change (b.repr (φ (Matrix.toLin b e S x)) : κ → ℚ) = b.repr x
  rw [← LinearMap.toMatrix_mulVec_repr e b φ, Matrix.repr_toLin,
    Matrix.mulVec_mulVec, hS, Matrix.one_mulVec]

theorem lieStructureConstants_quotient_matrix (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (S : Matrix ι κ ℚ)
    (hS : LinearMap.toMatrix e b φ.toLinearMap * S = 1) (i j k : κ) :
    lieStructureConstants b i j k = transportedLieConstants (lieStructureConstants e)
      (LinearMap.toMatrix e b φ.toLinearMap) S i j k := by
  simpa only [LinearMap.toMatrix_toLin] using
    lieStructureConstants_section e b φ (Matrix.toLin b e S)
      (basisMatrix_section e b φ.toLinearMap S hS) i j k

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TruncatedSeriesFiltration
namespace OAI

section

namespace Erdos3
variable {A : Type*} [Ring A] [Algebra ℚ A]

noncomputable def truncatedSeriesLayer (s i : ℕ) : Submodule ℚ (TruncatedSeries A s) where
  carrier := {p | ∀ n (hn : n ≤ s), n < i → truncatedSeriesCoeff s n hn p = 0}
  zero_mem' n hn _ := map_zero _
  add_mem' hp hq n hn hi := by rw [map_add, hp n hn hi, hq n hn hi, zero_add]
  smul_mem' r p hp n hn hi := by rw [map_smul, hp n hn hi, smul_zero]

theorem truncatedSeriesLayer_mul {s i j : ℕ} {p q : TruncatedSeries A s}
    (hp : p ∈ truncatedSeriesLayer s i) (hq : q ∈ truncatedSeriesLayer s j) :
    p * q ∈ truncatedSeriesLayer s (i + j) := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  obtain ⟨g, rfl⟩ := truncatedSeriesMk_surjective s q
  intro n hn hij
  change PowerSeries.coeff n (f * g) = 0
  rw [PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro ab hab
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
  by_cases ha : ab.1 < i
  · change ∀ n (hn : n ≤ s), n < i → PowerSeries.coeff n f = 0 at hp
    rw [hp ab.1 (by omega) ha, zero_mul]
  · change ∀ n (hn : n ≤ s), n < j → PowerSeries.coeff n g = 0 at hq
    rw [hq ab.2 (by omega) (by omega), mul_zero]

noncomputable def truncatedSeriesFiltration (s : ℕ) : NilpotentAlgebraFiltration (TruncatedSeries A s) s where
  layer := truncatedSeriesLayer s
  antitone _ _ hij _ hp n hn hi := hp n hn (lt_of_lt_of_le hi hij)
  zero_eq_top := by ext p; simp [truncatedSeriesLayer]
  mul_mem := truncatedSeriesLayer_mul
  terminal := by
    apply le_antisymm
    · intro p hp
      rw [Submodule.mem_bot]
      apply truncatedSeries_ext
      intro n hn
      rw [map_zero]
      exact hp n hn (Nat.lt_succ_of_le hn)
    · exact bot_le

theorem truncatedSeriesLayer_one {s : ℕ} {p : TruncatedSeries A s} :
    p ∈ truncatedSeriesLayer s 1 ↔ p ∈ truncatedSeriesPositive s := by
  obtain ⟨f, rfl⟩ := truncatedSeriesMk_surjective s p
  constructor
  · intro h
    change PowerSeries.constantCoeff f = 0
    simpa only [truncatedSeriesCoeff_mk, PowerSeries.coeff_zero_eq_constantCoeff] using h 0 (Nat.zero_le s) (by decide)
  · intro h n hn hi
    have hn0 : n = 0 := Nat.lt_one_iff.mp hi
    subst n
    change PowerSeries.coeff 0 f = 0
    rw [PowerSeries.coeff_zero_eq_constantCoeff]
    exact h

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateHeight
namespace OAI

section

namespace Erdos3

open MvPolynomial

def lieCoordinateHeight (d H n : ℕ) : ℕ :=
  (d ^ 2 + H + 2) ^ ((2 * d ^ 2 + 2) ^ n)

theorem lieCoordinateHeight_pos (d H n : ℕ) : 0 < lieCoordinateHeight d H n := by
  unfold lieCoordinateHeight
  positivity

theorem lieCoordinateHeight_mono_length (d H : ℕ) : Monotone (lieCoordinateHeight d H) := by
  intro m n hmn
  unfold lieCoordinateHeight
  exact Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by omega) hmn)

theorem lieCoordinateHeight_step (d H n : ℕ) :
    (d ^ 2 + 1) * (H * lieCoordinateHeight d H n) ^ (d ^ 2) ≤
      lieCoordinateHeight d H (n + 1) := by
  let A := d ^ 2 + H + 2
  let N := d ^ 2
  let E := (2 * N + 2) ^ n
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hE : 1 ≤ E := Nat.one_le_pow _ _ (by dsimp [N]; omega)
  have hH : H ≤ A := by dsimp [A]; omega
  have hN : N + 1 ≤ A := by dsimp [A, N]; omega
  change (N + 1) * (H * A ^ E) ^ N ≤ A ^ ((2 * N + 2) ^ (n + 1))
  calc
    (N + 1) * (H * A ^ E) ^ N ≤ A * (A * A ^ E) ^ N :=
      Nat.mul_le_mul hN (Nat.pow_le_pow_left (Nat.mul_le_mul_right _ hH) _)
    _ = A ^ (1 + (1 + E) * N) := by
      rw [← pow_succ', ← pow_mul, ← pow_succ']
      congr 1
      ring
    _ ≤ A ^ ((2 * N + 2) ^ (n + 1)) := by
      apply Nat.pow_le_pow_right hA
      rw [pow_succ]
      change 1 + (1 + E) * N ≤ E * (2 * N + 2)
      nlinarith

variable {ι X : Type*} [Fintype ι]

theorem coordinateRightBracket_height (c : ι → ι → ι → ℚ) {H K : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (x : X)
    (p : ι → MvPolynomial (X × ι) ℚ)
    (hp : ∀ i, RationalPolynomialHeightLE (p i) K) (k : ι) :
    RationalPolynomialHeightLE (coordinateRightBracket c x p k)
      ((Fintype.card ι ^ 2 + 1) * (H * K) ^ (Fintype.card ι ^ 2)) := by
  have h := RationalPolynomialHeightLE.sum
    (fun ij : ι × ι => C (c ij.1 ij.2 k) * p ij.1 * MvPolynomial.X (x, ij.2))
    (fun ij => (RationalPolynomialHeightLE.C_mul (hc ij.1 ij.2 k) (hp ij.1)).mul_X (x, ij.2))
  simpa only [coordinateRightBracket, Fintype.card_prod, pow_two] using h

theorem coordinateBracketList_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (xs : List X)
    (p : ι → MvPolynomial (X × ι) ℚ) {n : ℕ}
    (hp : ∀ i, RationalPolynomialHeightLE (p i) (lieCoordinateHeight (Fintype.card ι) H n))
    (k : ι) :
    RationalPolynomialHeightLE (coordinateBracketList c xs p k)
      (lieCoordinateHeight (Fintype.card ι) H (n + xs.length)) := by
  induction xs generalizing p n with
  | nil => exact hp k
  | cons x xs ih =>
    have hstep : ∀ i, RationalPolynomialHeightLE (coordinateRightBracket c x p i)
        (lieCoordinateHeight (Fintype.card ι) H (n + 1)) := fun i =>
      (coordinateRightBracket_height c hc x p hp i).mono (lieCoordinateHeight_step _ _ _)
    simpa only [coordinateBracketList, List.length_cons, Nat.add_assoc,
      Nat.add_comm 1 xs.length] using ih (coordinateRightBracket c x p) hstep

theorem dynkinCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (w : FreeSemigroup X) (k : ι) :
    RationalPolynomialHeightLE (dynkinCoordinatePolynomial c w k)
      (lieCoordinateHeight (Fintype.card ι) H w.length) := by
  have h := coordinateBracketList_height c hc w.tail
    (fun i => MvPolynomial.X (w.head, i)) (n := 0)
    (fun i => (RationalPolynomialHeightLE.X (w.head, i)).mono
      (lieCoordinateHeight_pos (Fintype.card ι) H 0)) k
  apply h.mono
  apply lieCoordinateHeight_mono_length
  change 0 + w.tail.length ≤ w.tail.length + 1
  omega

noncomputable def bchCoordinateHeight (s d H : ℕ) : ℕ :=
  ((bchBracketSupport s).card + 1) *
    (bchCoefficientHeight s * lieCoordinateHeight d H s) ^ (bchBracketSupport s).card

theorem bchCoordinatePolynomial_height (c : ι → ι → ι → ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H) (s : ℕ) (k : ι) :
    RationalPolynomialHeightLE (bchCoordinatePolynomial c s k)
      (bchCoordinateHeight s (Fintype.card ι) H) := by
  apply RationalPolynomialHeightLE.sum_finset
  intro w hw
  exact RationalPolynomialHeightLE.C_mul (bchBracketCoefficient_height s hw)
    ((dynkinCoordinatePolynomial_height c hc w k).mono
      (lieCoordinateHeight_mono_length _ _ (bchBracketSupport_length s hw)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialDensityBudget
namespace OAI

section

namespace Erdos3

theorem natPolynomial_eval_nonneg (P : Polynomial ℕ) {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ P.eval₂ (Nat.castRingHom ℝ) p := by
  rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hp _))

theorem exists_natPolynomial_eval_budget (P : Polynomial ℕ) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ p : ℝ, 0 ≤ p →
      P.eval₂ (Nat.castRingHom ℝ) p ≤ (p + N) ^ N := by
  let N := P.eval 1 + P.natDegree + 2
  refine ⟨N, by dsimp [N]; omega, ?_⟩
  intro p hp
  have hN : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by dsimp [N]; omega)
  have ht : 1 ≤ p + N := by linarith
  have hcoeff : ((P.eval 1 : ℕ) : ℝ) ≤ p + N := by
    have h : P.eval 1 ≤ N := by dsimp [N]; omega
    exact (Nat.cast_le.mpr h).trans (le_add_of_nonneg_left hp)
  have hsum : (∑ n ∈ P.support, (P.coeff n : ℝ)) = ((P.eval 1 : ℕ) : ℝ) := by
    rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
    simp only [one_pow, mul_one, Nat.cast_sum]
  calc
    P.eval₂ (Nat.castRingHom ℝ) p = ∑ n ∈ P.support, (P.coeff n : ℝ) * p ^ n := by
      rw [Polynomial.eval₂_eq_sum, Polynomial.sum_def]
      rfl
    _ ≤ ∑ n ∈ P.support, (P.coeff n : ℝ) * (p + N) ^ P.natDegree := by
      apply Finset.sum_le_sum
      intro n hn
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (pow_le_pow_left₀ hp (le_add_of_nonneg_right (Nat.cast_nonneg N)) n).trans
      exact pow_le_pow_right₀ ht (Polynomial.le_natDegree_of_mem_supp n hn)
    _ = ((P.eval 1 : ℕ) : ℝ) * (p + N) ^ P.natDegree := by rw [← Finset.sum_mul, hsum]
    _ ≤ (p + N) * (p + N) ^ P.natDegree :=
      mul_le_mul_of_nonneg_right hcoeff (pow_nonneg (by linarith) _)
    _ = (p + N) ^ (P.natDegree + 1) := (pow_succ' _ _).symm
    _ ≤ (p + N) ^ N := pow_le_pow_right₀ ht (by dsimp [N]; omega)

end Erdos3

end

section

namespace Erdos3

theorem exists_majorPhaseDetectedDecomposition_budget (a b c m d : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let E := (p + a) ^ a
      let Q := E + p + 1
      let P := (Q + b) ^ b + Q
      let D := (P + c) ^ c
      let B := (p + C) ^ C
      E ≤ B ∧ E + D ≤ B ∧ (m : ℝ) * p + D ≤ B ∧
        (m : ℝ) * E + D ≤ B ∧ (d : ℝ) * E + D ≤ B ∧
        (d : ℝ) * p + D ≤ B ∧ D ≤ B := by
  let E : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let Q : Polynomial ℕ := E + Polynomial.X + 1
  let P : Polynomial ℕ := (Q + Polynomial.C b) ^ b + Q
  let D : Polynomial ℕ := (P + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (E + D + Polynomial.C (m + d + 1) * (Polynomial.X + E) + 1)
  refine ⟨C, hC, ?_⟩
  intro p hp
  dsimp only
  let e : ℝ := (p + a) ^ a
  let q : ℝ := e + p + 1
  let r : ℝ := (q + b) ^ b + q
  let δ : ℝ := (r + c) ^ c
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have htotal : e + δ + ((m : ℝ) + d + 1) * (p + e) + 1 ≤ (p + C) ^ C := by
    simpa [E, Q, P, D, e, q, r, δ, Polynomial.eval₂_pow, Nat.cast_add] using hbudget p hp
  change e ≤ _ ∧ e + δ ≤ _ ∧ (m : ℝ) * p + δ ≤ _ ∧
    (m : ℝ) * e + δ ≤ _ ∧ (d : ℝ) * e + δ ≤ _ ∧
    (d : ℝ) * p + δ ≤ _ ∧ δ ≤ _
  have hmp : 0 ≤ (m : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hme : 0 ≤ (m : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  have hdp : 0 ≤ (d : ℝ) * p := mul_nonneg (Nat.cast_nonneg _) hp
  have hde : 0 ≤ (d : ℝ) * e := mul_nonneg (Nat.cast_nonneg _) he
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith

theorem pow_mul_exp_le_exp_of_le_budget {q p D B : ℝ} {h m : ℕ}
    (hq0 : 0 ≤ q) (hq : q ≤ Real.exp p) (hp : 0 ≤ p)
    (hh : h ≤ m) (hbudget : (m : ℝ) * p + D ≤ B) :
    q ^ h * Real.exp D ≤ Real.exp B := by
  calc
    q ^ h * Real.exp D ≤ (Real.exp p) ^ h * Real.exp D :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq h) (Real.exp_nonneg D)
    _ = Real.exp ((h : ℝ) * p + D) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp B := by
      apply Real.exp_le_exp.mpr
      have hmul : (h : ℝ) * p ≤ (m : ℝ) * p :=
        mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hh) hp
      linarith

theorem nat_pow_mul_le_exp_of_le_budget {q l d : ℕ} {p D B : ℝ}
    (hq : (q : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp D)
    (hbudget : (d : ℝ) * p + D ≤ B) :
    ((q ^ d * l : ℕ) : ℝ) ≤ Real.exp B := by
  calc
    ((q ^ d * l : ℕ) : ℝ) = (q : ℝ) ^ d * (l : ℝ) := by norm_cast
    _ ≤ (Real.exp p) ^ d * Real.exp D :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg q) hq d) hl
        (Nat.cast_nonneg l) (pow_nonneg (Real.exp_nonneg p) d)
    _ = Real.exp ((d : ℝ) * p + D) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp B := Real.exp_le_exp.mpr hbudget

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RationalPolynomialGrid
namespace OAI

section

namespace Erdos3

open MvPolynomial

theorem polynomial_rational_value_denominator {σ : Type*} [Fintype σ]
    (P : MvPolynomial σ ℚ) (q s : ℕ) (hdegree : P.totalDegree ≤ s)
    (x : σ → ℚ) (hx : x ∈ denominatorGrid q) :
    ∃ a : ℤ, ((polynomialDenominator P * q ^ s : ℕ) : ℚ) * eval x P = (a : ℚ) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨eval z (integralNumeratorPolynomial P q s), ?_⟩
  have h := integralNumeratorPolynomial_eval P q s hdegree x z hz
  simpa only [Nat.cast_mul, Nat.cast_pow] using h.symm

theorem polynomial_family_rational_values_grid {ι σ : Type*} [Fintype ι] [Fintype σ]
    (P : ι → MvPolynomial σ ℚ) (q s : ℕ) (hdegree : ∀ i, (P i).totalDegree ≤ s)
    (x : σ → ℚ) (hx : x ∈ denominatorGrid q) :
    (fun i => eval x (P i)) ∈ denominatorGrid (polynomialFamilyDenominator P * q ^ s) := by
  classical
  have h (i : ι) : ∃ a : ℤ,
      ((polynomialFamilyDenominator P * q ^ s : ℕ) : ℚ) * eval x (P i) = (a : ℚ) := by
    obtain ⟨k, hk⟩ := polynomialDenominator_dvd_family P i
    obtain ⟨a, ha⟩ := polynomial_rational_value_denominator (P i) q s (hdegree i) x hx
    refine ⟨(k : ℤ) * a, ?_⟩
    simp only [Nat.cast_mul, Nat.cast_pow] at ha
    rw [hk]
    simp only [Nat.cast_mul, Nat.cast_pow, Int.cast_mul, Int.cast_natCast]
    calc
      _ = (k : ℚ) * ((polynomialDenominator (P i) : ℚ) * (q : ℚ) ^ s * eval x (P i)) := by ring
      _ = _ := by rw [ha]
  choose a ha using h
  exact ⟨a, ha⟩

theorem pairInput_mem_denominatorGrid {ι : Type*} (a b : ι → ℚ) (q : ℕ)
    (ha : a ∈ denominatorGrid q) (hb : b ∈ denominatorGrid q) :
    (fun xi : Fin 2 × ι => (![a, b] xi.1) xi.2) ∈ denominatorGrid q := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨v, hv⟩ := hb
  refine ⟨fun xi => (![u, v] xi.1) xi.2, ?_⟩
  rintro ⟨i, j⟩
  fin_cases i
  · exact hu j
  · exact hv j

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ConjugationGridBudget
namespace OAI

section

namespace Erdos3

theorem conjugation_grid_allowance_le_exp (K s l D q : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hl : (l : ℝ) ≤ Real.exp p) (hD : (D : ℝ) ≤ Real.exp ((p + K) ^ K))
    (hq : (q : ℝ) ≤ Real.exp p) :
    ((l * D * q ^ s : ℕ) : ℝ) ≤
      Real.exp ((p + (K + s + 5)) ^ (K + s + 5)) := by
  let J := K + s + 5
  let t := p + J
  have ht : 2 ≤ t := by
    dsimp [t, J]
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) K, Nat.cast_nonneg (α := ℝ) s]
  have hp_le : p ≤ t := by dsimp [t]; have := Nat.cast_nonneg (α := ℝ) J; linarith
  have hs_le : (s : ℝ) + 1 ≤ t := by dsimp [t, J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
  have hbig : (p + K) ^ K ≤ t ^ (J - 1) := by
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ p + K) (show p + K ≤ t by
      dsimp [t, J]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) s]) K).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [J]; omega)
  have hsmall : ((s : ℝ) + 1) * p ≤ t ^ (J - 1) := by
    apply (show ((s : ℝ) + 1) * p ≤ t ^ 2 by
      simpa only [pow_two] using mul_le_mul hs_le hp_le hp (by linarith : 0 ≤ t)).trans
    exact pow_le_pow_right₀ (by linarith) (by dsimp [J]; omega)
  have hqpow : (q : ℝ) ^ s ≤ Real.exp ((s : ℝ) * p) := by
    simpa only [← Real.exp_nat_mul] using pow_le_pow_left₀ (Nat.cast_nonneg q) hq s
  push_cast
  calc
    _ ≤ Real.exp p * Real.exp ((p + K) ^ K) * Real.exp ((s : ℝ) * p) :=
      mul_le_mul (mul_le_mul hl hD (by positivity) (by positivity)) hqpow (by positivity) (by positivity)
    _ = Real.exp ((p + K) ^ K + ((s : ℝ) + 1) * p) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (t ^ J) := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ 2 * t ^ (J - 1) := by linarith
        _ ≤ t * t ^ (J - 1) := mul_le_mul_of_nonneg_right ht (by positivity)
        _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by dsimp [J]; omega)]
    _ = _ := by simp [t, J]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHDenominatorBudget
namespace OAI

section

namespace Erdos3

open Module

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def bchCoordinateDenominator (e : Basis ι ℚ L) (s : ℕ) : ℕ :=
  polynomialFamilyDenominator (bchCoordinatePolynomial (lieStructureConstants e) s)

theorem bchCoordinateDenominator_pos (e : Basis ι ℚ L) (s : ℕ) :
    0 < bchCoordinateDenominator e s := polynomialFamilyDenominator_pos _

theorem lieBCH_mem_denominatorGrid (e : Basis ι ℚ L) (s q : ℕ) (a b : L)
    (ha : e.equivFun a ∈ denominatorGrid q) (hb : e.equivFun b ∈ denominatorGrid q) :
    e.equivFun (lieBCH s a b) ∈ denominatorGrid (bchCoordinateDenominator e s * q ^ s) := by
  have h := polynomial_family_rational_values_grid
    (bchCoordinatePolynomial (lieStructureConstants e) s) q s
    (bchCoordinatePolynomial_totalDegree _ s)
    (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2)
    (pairInput_mem_denominatorGrid (e.equivFun a) (e.equivFun b) q ha hb)
  have he : (fun k => MvPolynomial.eval
      (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2)
      (bchCoordinatePolynomial (lieStructureConstants e) s k)) = e.equivFun (lieBCH s a b) := by
    funext k
    have hi : (fun xi : Fin 2 × ι => (![e.equivFun a, e.equivFun b] xi.1) xi.2) =
        (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2) := by
      funext xi
      rcases xi with ⟨i, j⟩
      fin_cases i <;> rfl
    rw [hi]
    exact bchCoordinatePolynomial_eval e s a b k
  rw [he] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem lieCoordinateHeight_le_exp (d H n : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (lieCoordinateHeight d H n : ℝ) ≤ Real.exp ((p + 2) ^ (3 * n + 2)) := by
  have hd2 : (d : ℝ) ^ 2 ≤ p ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg d) hd 2
  have hpexp : Real.exp p ≤ Real.exp (p ^ 2 + 1) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (p - 1)])
  have hsmall : (d : ℝ) ^ 2 + 2 ≤ Real.exp (p ^ 2 + 1) := by
    have h := Real.add_one_le_exp (p ^ 2 + 1)
    linarith
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hbase : (d : ℝ) ^ 2 + H + 2 ≤ Real.exp ((p + 2) ^ 2) := by
    calc
      _ ≤ 2 * Real.exp (p ^ 2 + 1) := by linarith [hH.trans hpexp]
      _ ≤ Real.exp 1 * Real.exp (p ^ 2 + 1) :=
        mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
      _ = Real.exp (p ^ 2 + 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith)
  have hexponent : ((2 * d ^ 2 + 2) ^ n : ℕ) ≤ (p + 2) ^ (3 * n) := by
    push_cast
    rw [pow_mul]
    apply pow_le_pow_left₀ (by positivity)
    nlinarith [pow_nonneg hp 3]
  unfold lieCoordinateHeight
  push_cast
  calc
    _ ≤ (Real.exp ((p + 2) ^ 2)) ^ ((2 * d ^ 2 + 2) ^ n) :=
      pow_le_pow_left₀ (by positivity) hbase _
    _ = Real.exp ((((2 * d ^ 2 + 2) ^ n : ℕ) : ℝ) * (p + 2) ^ 2) :=
      (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp ((p + 2) ^ (3 * n) * (p + 2) ^ 2) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hexponent (by positivity))
    _ = _ := by rw [pow_add]

theorem bchCoordinateHeight_le_exp (s d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p)
    (hc : (bchCoefficientHeight s : ℝ) ≤ Real.exp p)
    (hm : ((bchBracketSupport s).card : ℝ) ≤ p) :
    (bchCoordinateHeight s d H : ℝ) ≤ Real.exp ((p + 2) ^ (3 * s + 5)) := by
  have hlie := lieCoordinateHeight_le_exp d H s hp hd hH
  have hpbudget : p ≤ (p + 2) ^ (3 * s + 2) := le_power_budget hp (by omega)
  have hprod : ((bchCoefficientHeight s * lieCoordinateHeight d H s : ℕ) : ℝ) ≤
      Real.exp ((p + 2) ^ (3 * s + 3)) := by
    push_cast
    calc
      _ ≤ Real.exp ((p + 2) ^ (3 * s + 2)) * Real.exp ((p + 2) ^ (3 * s + 2)) :=
        mul_le_mul (hc.trans (Real.exp_le_exp.mpr hpbudget)) hlie
          (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * (p + 2) ^ (3 * s + 2)) := by
        rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [show 3 * s + 3 = (3 * s + 2) + 1 by omega,
          pow_succ (p + 2) (3 * s + 2)]
        nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) (3 * s + 2)]
  have hcard : ((bchBracketSupport s).card : ℝ) ≤ (p + 2) ^ 1 := by
    rw [pow_one]
    linarith
  exact rational_sum_cost_le_exp (bchBracketSupport s).card
    (bchCoefficientHeight s * lieCoordinateHeight d H s) hp (3 * s + 3) 1 hprod hcard

theorem exists_bchCoordinateHeight_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (d H : ℕ) (p : ℝ), 0 ≤ p → (d : ℝ) ≤ p →
      (H : ℝ) ≤ Real.exp p →
      (bchCoordinateHeight s d H : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  let C := bchCoefficientHeight s + (bchBracketSupport s).card + 3 * s + 7
  refine ⟨C, by dsimp [C]; omega, ?_⟩
  intro d H p hp hd hH
  let q : ℝ := p + bchCoefficientHeight s + (bchBracketSupport s).card
  have hpq : p ≤ q := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) (bchCoefficientHeight s),
      Nat.cast_nonneg (α := ℝ) (bchBracketSupport s).card]
  have hq : 0 ≤ q := hp.trans hpq
  have hc : (bchCoefficientHeight s : ℝ) ≤ Real.exp q := by
    have h := Real.add_one_le_exp q
    dsimp [q]
    dsimp [q] at h
    linarith [Nat.cast_nonneg (α := ℝ) (bchBracketSupport s).card]
  have hm : ((bchBracketSupport s).card : ℝ) ≤ q := by
    dsimp [q]
    linarith [Nat.cast_nonneg (α := ℝ) (bchCoefficientHeight s)]
  have hbound := bchCoordinateHeight_le_exp s d H hq (hd.trans hpq)
    (hH.trans (Real.exp_le_exp.mpr hpq)) hc hm
  apply hbound.trans
  apply Real.exp_le_exp.mpr
  have hbase : q + 2 ≤ p + C := by
    dsimp [q, C]
    push_cast
    nlinarith
  calc
    (q + 2) ^ (3 * s + 5) ≤ (p + C) ^ (3 * s + 5) :=
      pow_le_pow_left₀ (by linarith) hbase _
    _ ≤ (p + C) ^ C := pow_le_pow_right₀ (by linarith) (by dsimp [C]; omega)

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bchCoordinateDenominator_exp_budget (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      (bchCoordinateDenominator e s : ℝ) ≤ Real.exp ((p + C) ^ C) := by
  obtain ⟨c, _, hc⟩ := exists_bchCoordinateHeight_exp_budget s
  let R : Polynomial ℕ :=
    (2 * Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c + Polynomial.C (s + 3)) ^ (s + 3)
  obtain ⟨C, hC, hbound⟩ := exists_natPolynomial_eval_budget R
  refine ⟨C, hC, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hstructure
  let q : ℝ := 2 * p + (p + c) ^ c
  have hpower : 0 ≤ (p + c) ^ c := by positivity
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hheight := hc (Fintype.card ι) H p hp hd hH
  have hcoeff : ∀ i α, (((bchCoordinatePolynomial (lieStructureConstants e) s i).coeff α).den : ℝ) ≤
      Real.exp q := by
    intro i α
    exact (Nat.cast_le.mpr (bchCoordinatePolynomial_height (lieStructureConstants e) hstructure s i α).2).trans
      (hheight.trans (Real.exp_le_exp.mpr (by dsimp [q]; linarith)))
  have hinputs : (Fintype.card (Fin 2 × ι) : ℝ) ≤ q := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
    dsimp [q]
    linarith
  have hD := polynomialFamilyDenominator_degree_budget (bchCoordinatePolynomial (lieStructureConstants e) s)
    s (bchCoordinatePolynomial_totalDegree _ s) hq (hd.trans hpq) hinputs hcoeff
  have hpoly : (q + (s + 3)) ^ (s + 3) ≤ (p + C) ^ C := by
    simpa [R, q, Polynomial.eval₂_pow] using hbound p hp
  exact hD.trans (Real.exp_le_exp.mpr hpoly)

theorem exists_bch_rational_closure (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
      (e : Basis ι ℚ L) (H : ℕ) (p : ℝ),
      0 ≤ p → (Fintype.card ι : ℝ) ≤ p → (H : ℝ) ≤ Real.exp p →
      (∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ q ∣ m ∧
        ∀ a b : L, e.equivFun a ∈ denominatorGrid q → e.equivFun b ∈ denominatorGrid q →
          e.equivFun (lieBCH s a b) ∈ denominatorGrid m := by
  obtain ⟨K, _, hK⟩ := exists_bchCoordinateDenominator_exp_budget s
  refine ⟨K + s + 5, by omega, ?_⟩
  intro ι L _ _ _ e H p hp hd hH hstructure q hq hqp
  let D := bchCoordinateDenominator e s
  let m := q * D * q ^ s
  have hD : 0 < D := bchCoordinateDenominator_pos e s
  have hqm : q ∣ m := ⟨D * q ^ s, Nat.mul_assoc q D (q ^ s)⟩
  have hDm : D * q ^ s ∣ m := ⟨q,
    (Nat.mul_assoc q D (q ^ s)).trans (Nat.mul_comm q (D * q ^ s))⟩
  refine ⟨m, Nat.mul_pos (Nat.mul_pos hq hD) (pow_pos hq _), ?_, hqm, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_ofNat] using conjugation_grid_allowance_le_exp K s q D q hp hqp
      (hK e H p hp hd hH hstructure) hqp
  · intro a b ha hb
    exact denominatorGrid_subset_of_dvd hDm (lieBCH_mem_denominatorGrid e s q a b ha hb)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateScalarExtension
namespace OAI

section

namespace Erdos3

open MvPolynomial Module

variable {ι X R L : Type*} [Fintype ι] [CommRing R] [Algebra ℚ R]
  [LieRing L] [LieAlgebra R L]

theorem lie_coordinate_formula_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ ij : ι × ι, algebraMap ℚ R (c ij.1 ij.2 k) * e.repr a ij.1 * e.repr b ij.2 := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Fintype.sum_prod_type, hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem coordinateRightBracket_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (x : X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (coordinateRightBracket c x p k) = e.repr ⁅a, f x⁆ k := by
  simp only [coordinateRightBracket, map_sum, map_mul, aeval_C, aeval_X, hp]
  exact (lie_coordinate_formula_over e c hc a (f x) k).symm

variable [LieAlgebra ℚ L]

theorem coordinateBracketList_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (xs : List X) (p : ι → MvPolynomial (X × ι) ℚ) (a : L)
    (hp : ∀ i, aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (p i) = e.repr a i)
    (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
        (coordinateBracketList c xs p k) = e.repr (rightBracketList f xs a) k := by
  induction xs generalizing p a with
  | nil => exact hp k
  | cons x xs ih =>
    exact ih (coordinateRightBracket c x p) ⁅a, f x⁆
      (coordinateRightBracket_eval_over e c hc f p a hp x)

theorem dynkinCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (f : X → L) (w : FreeSemigroup X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2) (dynkinCoordinatePolynomial c w k) =
      e.repr (dynkinWord f w) k := by
  apply coordinateBracketList_eval_over e c hc
  intro i
  simp only [aeval_X]

variable [IsScalarTower ℚ R L]

theorem bchCoordinatePolynomial_eval_over (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (a b : L) (k : ι) :
    aeval (fun xi : Fin 2 × ι => e.repr (![a, b] xi.1) xi.2)
      (bchCoordinatePolynomial c s k) = e.repr (lieBCH s a b) k := by
  change _ = e.coord k (lieBCH s a b)
  rw [lieBCH_bracket_formula]
  simp only [bchCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3
variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem map_freeLie_lift (φ : L →ₗ⁅ℚ⁆ M) (f : X → L) (p : FreeLieAlgebra ℚ X) :
    φ (FreeLieAlgebra.lift ℚ f p) = FreeLieAlgebra.lift ℚ (fun x => φ (f x)) p := by
  have h : φ.comp (FreeLieAlgebra.lift ℚ f) = FreeLieAlgebra.lift ℚ (fun x => φ (f x)) := by
    apply FreeLieAlgebra.hom_ext
    intro x
    simp
  exact DFunLike.congr_fun h p

theorem map_lieBCH (φ : L →ₗ⁅ℚ⁆ M) (s : ℕ) (a b : L) :
    φ (lieBCH s a b) = lieBCH s (φ a) (φ b) := by
  have hf : (fun x : Fin 2 => φ (![a, b] x)) = ![φ a, φ b] := by
    funext x
    fin_cases x <;> rfl
  simpa only [lieBCH, hf] using map_freeLie_lift φ ![a, b] (bchLiePolynomial s)

attribute [local instance] LieRing.ofAssociativeRing

noncomputable def scaledFreeLieEval (s : ℕ) :
    FreeLieAlgebra ℚ X →ₗ⁅ℚ⁆ TruncatedSeries (FreeAlgebra ℚ X) s :=
  FreeLieAlgebra.lift ℚ (scaledFreeGenerator s)

@[simp] theorem scaledFreeLieEval_of (s : ℕ) (x : X) :
    scaledFreeLieEval s (FreeLieAlgebra.of ℚ x) = scaledFreeGenerator s x :=
  FreeLieAlgebra.lift_of_apply _ _

theorem scaledFreeLieEval_eq (s : ℕ) (p : FreeLieAlgebra ℚ X) :
    scaledFreeLieEval s p = truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion p)) := by
  have h : FreeAlgebra.lift ℚ (scaledFreeGenerator (X := X) s) =
      (truncatedSeriesMk s).comp freeScaleSeries := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [scaledFreeGenerator]
  change FreeLieAlgebra.lift ℚ (scaledFreeGenerator s) p = _
  rw [← freeLieAssociativeExpansion_eval, h]
  rfl

theorem lie_lift_eq_of_scaledFreeLieEval_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (h : scaledFreeLieEval s p = scaledFreeLieEval s q) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  apply lie_lift_eq_of_scaled_series_eq f hnil
  simpa only [scaledFreeLieEval_eq] using h

end Erdos3

end

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
attribute [local instance] LieRing.ofAssociativeRing

theorem scaledFreeGenerator_mem_layer (s : ℕ) {X : Type*} (x : X) :
    scaledFreeGenerator s x ∈ (truncatedSeriesFiltration (A := FreeAlgebra ℚ X) s).layer 1 :=
  truncatedSeriesLayer_one.mpr (scaledFreeGenerator_positive s x)

theorem lieBCH_assoc (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a b c : L) :
    lieBCH s (lieBCH s a b) c = lieBCH s a (lieBCH s b c) := by
  let x : Fin 3 → FreeLieAlgebra ℚ (Fin 3) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 3)) s
  have hx (i : Fin 3) : scaledFreeGenerator s i ∈ F.layer 1 := scaledFreeGenerator_mem_layer s i
  have h : scaledFreeLieEval s (lieBCH s (lieBCH s (x 0) (x 1)) (x 2)) =
      scaledFreeLieEval s (lieBCH s (x 0) (lieBCH s (x 1) (x 2))) := by
    simp only [map_lieBCH, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq (hx 0) (hx 1), F.lieBCH_eq (hx 1) (hx 2),
      F.lieBCH_eq (F.bch_mem le_rfl (hx 0) (hx 1)) (hx 2),
      F.lieBCH_eq (hx 0) (F.bch_mem le_rfl (hx 1) (hx 2))]
    exact nilpotentBCH_assoc (F.layerAlgebra 1) F.positive_nilpotent (hx 0) (hx 1) (hx 2)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b, c] hnil h
  simpa only [map_lieBCH, x, FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, Matrix.head_cons] using he

theorem lieBCH_zero_left (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a : L) :
    lieBCH s 0 a = a := by
  let x : FreeLieAlgebra ℚ (Fin 1) := FreeLieAlgebra.of ℚ 0
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 1)) s
  have hx : scaledFreeGenerator s (0 : Fin 1) ∈ F.layer 1 := scaledFreeGenerator_mem_layer s 0
  have h : scaledFreeLieEval s (lieBCH s 0 x) = scaledFreeLieEval s x := by
    simp only [map_lieBCH, map_zero, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq (F.layer 1).zero_mem hx]
    exact nilpotentBCH_zero_left (F.isNilpotent_of_mem le_rfl hx)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq (fun _ : Fin 1 => a) hnil h
  simpa only [map_lieBCH, map_zero, x, FreeLieAlgebra.lift_of_apply] using he

theorem lieBCH_neg_left (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (a : L) :
    lieBCH s (-a) a = 0 := by
  let x : FreeLieAlgebra ℚ (Fin 1) := FreeLieAlgebra.of ℚ 0
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 1)) s
  have hx : scaledFreeGenerator s (0 : Fin 1) ∈ F.layer 1 := scaledFreeGenerator_mem_layer s 0
  have h : scaledFreeLieEval s (lieBCH s (-x) x) = scaledFreeLieEval s 0 := by
    simp only [map_lieBCH, map_neg, map_zero, x, scaledFreeLieEval_of]
    rw [F.lieBCH_eq ((F.layer 1).neg_mem hx) hx]
    exact nilpotentBCH_neg_left (F.isNilpotent_of_mem le_rfl hx)
  have he := lie_lift_eq_of_scaledFreeLieEval_eq (fun _ : Fin 1 => a) hnil h
  simpa only [map_lieBCH, map_neg, map_zero, x, FreeLieAlgebra.lift_of_apply] using he

structure NilpotentLieBCHGroup (L : Type*) [LieRing L] [LieAlgebra ℚ L] (s : ℕ)
    (_hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) where
  coord : L

namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[ext] theorem ext {a b : NilpotentLieBCHGroup L s hnil} (h : a.coord = b.coord) : a = b := by
  cases a
  cases b
  cases h
  rfl

noncomputable instance : Mul (NilpotentLieBCHGroup L s hnil) where
  mul a b := ⟨lieBCH s a.coord b.coord⟩

instance : One (NilpotentLieBCHGroup L s hnil) where
  one := ⟨0⟩

instance : Inv (NilpotentLieBCHGroup L s hnil) where
  inv a := ⟨-a.coord⟩

@[simp] theorem coord_mul (a b : NilpotentLieBCHGroup L s hnil) :
    (a * b).coord = lieBCH s a.coord b.coord := rfl
@[simp] theorem coord_one : (1 : NilpotentLieBCHGroup L s hnil).coord = 0 := rfl
@[simp] theorem coord_inv (a : NilpotentLieBCHGroup L s hnil) : (a⁻¹).coord = -a.coord := rfl

noncomputable instance : Group (NilpotentLieBCHGroup L s hnil) :=
  Group.ofLeftAxioms
    (fun a b c => ext (lieBCH_assoc hnil a.coord b.coord c.coord))
    (fun a => ext (lieBCH_zero_left hnil a.coord))
    (fun a => ext (lieBCH_neg_left hnil a.coord))

noncomputable def map {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥} (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM where
  toFun a := ⟨φ a.coord⟩
  map_one' := ext (map_zero φ)
  map_mul' a b := ext (map_lieBCH φ s a.coord b.coord)

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieBCHList (s : ℕ) (f : X → L) : List X → L
  | [] => 0
  | x :: xs => lieBCH s (f x) (lieBCHList s f xs)

theorem map_lieBCHList (φ : L →ₗ⁅ℚ⁆ M) (s : ℕ) (f : X → L) (xs : List X) :
    φ (lieBCHList s f xs) = lieBCHList s (fun x => φ (f x)) xs := by
  induction xs with
  | nil => exact map_zero φ
  | cons x xs ih => simp only [lieBCHList, map_lieBCH, ih]

theorem lieBCHList_group_prod (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) :
    ((xs.map (fun x => (⟨f x⟩ : NilpotentLieBCHGroup L s hnil))).prod).coord =
      lieBCHList s f xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.prod_cons, NilpotentLieBCHGroup.coord_mul, lieBCHList, ih]

noncomputable def bchProductLiePolynomial (s : ℕ) (xs : List X) : FreeLieAlgebra ℚ X :=
  freeLieTruncation s (lieBCHList s (FreeLieAlgebra.of ℚ) xs)

theorem bchProductLiePolynomial_eval (s : ℕ)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (f : X → L) (xs : List X) :
    FreeLieAlgebra.lift ℚ f (bchProductLiePolynomial s xs) = lieBCHList s f xs := by
  rw [bchProductLiePolynomial, lift_freeLieTruncation f hnil, map_lieBCHList]
  congr 1
  funext x
  exact FreeLieAlgebra.lift_of_apply _ _

theorem bchProductLiePolynomial_support_length (s : ℕ) (xs : List X)
    {w : FreeSemigroup X} (hw : w ∈ (freeLieWordExpansion (bchProductLiePolynomial s xs)).coeff.support) :
    w.length ≤ s := freeLieTruncation_support_length s _ hw

end Erdos3

end

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieBCH_mem (K : LieSubalgebra ℚ L) (s : ℕ) {a b : L}
    (ha : a ∈ K) (hb : b ∈ K) : lieBCH s a b ∈ K := by
  have h := map_lieBCH K.incl s (⟨a, ha⟩ : K) (⟨b, hb⟩ : K)
  change ((lieBCH s (⟨a, ha⟩ : K) (⟨b, hb⟩ : K) : K) : L) = lieBCH s a b at h
  rw [← h]
  exact (lieBCH s (⟨a, ha⟩ : K) (⟨b, hb⟩ : K)).property

namespace NilpotentLieBCHGroup
variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

def subgroup (K : LieSubalgebra ℚ L) : Subgroup (NilpotentLieBCHGroup L s hnil) where
  carrier := {a | a.coord ∈ K}
  one_mem' := K.zero_mem
  mul_mem' ha hb := lieBCH_mem K s ha hb
  inv_mem' ha := K.neg_mem ha

@[simp] theorem mem_subgroup (K : LieSubalgebra ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    a ∈ subgroup K ↔ a.coord ∈ K := Iff.rfl

end NilpotentLieBCHGroup

def lieQuotientMap (I : LieIdeal ℚ L) : L →ₗ⁅ℚ⁆ L ⧸ I :=
  { I.toSubmodule.mkQ with map_lie' := by intro a b; rfl }

theorem lieQuotientMap_surjective (I : LieIdeal ℚ L) : Function.Surjective (lieQuotientMap I) :=
  Submodule.mkQ_surjective _

@[simp] theorem lieQuotientMap_eq_zero (I : LieIdeal ℚ L) (a : L) :
    lieQuotientMap I a = 0 ↔ a ∈ I := Submodule.Quotient.mk_eq_zero _

theorem lie_quotient_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L) :
    LieModule.lowerCentralSeries ℚ (L ⧸ I) (L ⧸ I) s = ⊥ := by
  rw [← LieIdeal.lowerCentralSeries_map_eq s (lieQuotientMap_surjective I), hnil]
  simp

end Erdos3

end

section

namespace Erdos3

variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def bchProductPolynomial (s : ℕ) (xs : List X) : FreeAlgebra ℚ X :=
  finiteLog (s + 1)
    ((xs.map (fun x => finiteExp (s + 1) (FreeAlgebra.ι ℚ x))).prod - 1)

theorem bchProductPolynomial_eval (s : ℕ) (f : X → A) (xs : List X) :
    FreeAlgebra.lift ℚ f (bchProductPolynomial s xs) =
      finiteLog (s + 1) ((xs.map (fun x => finiteExp (s + 1) (f x))).prod - 1) := by
  simp only [bchProductPolynomial, map_finiteLog, map_sub, map_one,
    map_list_prod, List.map_map, Function.comp_def, map_finiteExp, FreeAlgebra.lift_ι_apply]

namespace NilpotentAlgebraFiltration

variable {s : ℕ} (F : NilpotentAlgebraFiltration A s) (f : X → A)

theorem lieBCHList_mem (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    lieBCHList s f xs ∈ F.layer 1 := by
  induction xs with
  | nil => exact (F.layer 1).zero_mem
  | cons x xs ih =>
    rw [lieBCHList, F.lieBCH_eq (hf x) ih]
    exact F.bch_mem le_rfl (hf x) ih

theorem exp_lieBCHList (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    IsNilpotent.exp (lieBCHList s f xs) = (xs.map (fun x => IsNilpotent.exp (f x))).prod := by
  induction xs with
  | nil => exact IsNilpotent.exp_zero
  | cons x xs ih =>
    rw [lieBCHList, F.lieBCH_eq (hf x) (F.lieBCHList_mem f hf xs),
      exp_nilpotentBCH (F.layerAlgebra 1) F.positive_nilpotent (hf x) (F.lieBCHList_mem f hf xs),
      ih, List.map_cons, List.prod_cons]

theorem bchProductPolynomial_formula (hf : ∀ x, f x ∈ F.layer 1) (xs : List X) :
    FreeAlgebra.lift ℚ f (bchProductPolynomial s xs) = lieBCHList s f xs := by
  have hx := F.lieBCHList_mem f hf xs
  have hn := F.isNilpotent_of_mem le_rfl hx
  have hprod : (xs.map (fun x => finiteExp (s + 1) (f x))).prod =
      IsNilpotent.exp (lieBCHList s f xs) := by
    rw [F.exp_lieBCHList f hf xs]
    congr 1
    apply List.map_congr_left
    intro x _
    exact finiteExp_eq_exp (F.pow_eq_zero le_rfl (hf x))
  rw [bchProductPolynomial_eval, hprod,
    finiteLog_eq_log (F.pow_eq_zero le_rfl (F.exp_sub_one_mem_layer hx hn)),
    nilpotentLog_exp_sub_one hn]

end NilpotentAlgebraFiltration

theorem bchProductLiePolynomial_associativeExpansion (s : ℕ) (xs : List X) :
    freeLieAssociativeExpansion (bchProductLiePolynomial s xs) =
      freeTruncation s (bchProductPolynomial s xs) := by
  rw [bchProductLiePolynomial, freeLieTruncation_associativeExpansion]
  apply freeTruncation_eq_of_scaled_series_eq
  rw [← scaledFreeLieEval_eq, map_lieBCHList]
  have hf : (fun x : X => scaledFreeLieEval s (FreeLieAlgebra.of ℚ x)) = scaledFreeGenerator s := by
    funext x
    exact scaledFreeLieEval_of s x
  rw [hf]
  have h := (truncatedSeriesFiltration (A := FreeAlgebra ℚ X) s).bchProductPolynomial_formula
    (scaledFreeGenerator s) (scaledFreeGenerator_mem_layer s) xs
  rw [← h]
  have he : FreeAlgebra.lift ℚ (scaledFreeGenerator (X := X) s) =
      (truncatedSeriesMk s).comp freeScaleSeries := by
    apply FreeAlgebra.hom_ext
    funext x
    simp [scaledFreeGenerator]
  rw [he]
  rfl

end Erdos3

end

section

namespace Erdos3

namespace NilpotentAlgebraFiltration
variable {A : Type*} [Ring A] [Algebra ℚ A] {s t : ℕ}

def extend (F : NilpotentAlgebraFiltration A s) (hst : s ≤ t) : NilpotentAlgebraFiltration A t where
  layer := F.layer
  antitone := F.antitone
  zero_eq_top := F.zero_eq_top
  mul_mem := F.mul_mem
  terminal := le_antisymm (by
    rw [← F.terminal]
    exact F.antitone (Nat.add_le_add_right hst 1)) bot_le

end NilpotentAlgebraFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_add_of_isLieAbelian [IsLieAbelian L] {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    lieBCH s a b = a + b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) 1
  have hx (i : Fin 2) : scaledFreeGenerator 1 i ∈ F.layer 1 := scaledFreeGenerator_mem_layer 1 i
  have hmul (i j : Fin 2) : scaledFreeGenerator 1 i * scaledFreeGenerator 1 j = 0 := by
    have h := F.mul_mem (hx i) (hx j)
    simpa only [F.terminal, Submodule.mem_bot] using h
  have hc : Commute (scaledFreeGenerator 1 (0 : Fin 2)) (scaledFreeGenerator 1 (1 : Fin 2)) := by
    change _ * _ = _ * _
    rw [hmul 0 1, hmul 1 0]
  have h : scaledFreeLieEval 1 (lieBCH s (x 0) (x 1)) = scaledFreeLieEval 1 (x 0 + x 1) := by
    simp only [map_lieBCH, map_add, x, scaledFreeLieEval_of]
    rw [(F.extend hs).lieBCH_eq (hx 0) (hx 1)]
    exact nilpotentBCH_eq_add_of_commute (F.isNilpotent_of_mem le_rfl (hx 0))
      (F.isNilpotent_of_mem le_rfl (hx 1)) hc
  have hn : LieModule.lowerCentralSeries ℚ L L 1 = ⊥ := by
    simp [LieModule.lowerCentralSeries_succ]
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hn h
  simpa only [map_lieBCH, map_add, x, FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem lieBCH_eq_add_of_lie_eq_zero_pos {s : ℕ} (hs : 1 ≤ s) {a b : L}
    (hab : ⁅a, b⁆ = 0) : lieBCH s a b = a + b := by
  let K := LieSubalgebra.lieSpan ℚ L ({a, b} : Set L)
  have ha : a ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have hb : b ∈ K := LieSubalgebra.subset_lieSpan (by simp)
  have : IsLieAbelian K := by
    apply LieSubalgebra.isLieAbelian_lieSpan_iff.mpr
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact lie_self _
    · exact hab
    · rw [← lie_skew, hab, neg_zero]
    · exact lie_self _
  have h := congrArg K.incl (lieBCH_eq_add_of_isLieAbelian hs (⟨a, ha⟩ : K) (⟨b, hb⟩ : K))
  simp only [map_lieBCH, map_add] at h
  change lieBCH s a b = a + b at h
  exact h

theorem lieBCH_eq_add_of_lie_eq_zero {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {a b : L}
    (hab : ⁅a, b⁆ = 0) : lieBCH s a b = a + b := by
  by_cases hs : 1 ≤ s
  · exact lieBCH_eq_add_of_lie_eq_zero_pos hs hab
  · have hs0 : s = 0 := by omega
    subst s
    have he (z : L) : z = 0 := by
      have hz : z ∈ LieModule.lowerCentralSeries ℚ L L 0 := by simp
      simpa only [hnil, LieSubmodule.mem_bot] using hz
    rw [he a, he b, zero_add, lieBCH_zero_left hnil]

end Erdos3

end

section

namespace Erdos3

open Module MvPolynomial

noncomputable def bchBoxCoordinateBound (s d H : ℕ) (B : ℝ) : ℝ :=
  (((s + 1) * (2 * d + 1) ^ s : ℕ) : ℝ) * bchCoordinateHeight s d H * (2 * d) * s *
    B ^ (s * (2 * d + 1))

theorem bchBoxCoordinateBound_nonneg (s d H : ℕ) {B : ℝ} (hB : 0 ≤ B) :
    0 ≤ bchBoxCoordinateBound s d H B := by
  unfold bchBoxCoordinateBound
  positivity

theorem lieBCH_sub_coordinates_bound {ι L : Type*} [Fintype ι]
    [LieRing L] [LieAlgebra ℝ L] [LieAlgebra ℚ L] [IsScalarTower ℚ ℝ L]
    (e : Basis ι ℝ L) (c : ι → ι → ι → ℚ) {H s : ℕ}
    (hstructure : ∀ i j k, algebraMap ℚ ℝ (c i j k) = e.repr ⁅e i, e j⁆ k)
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (x y : L) {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hx : ∀ i, |e.repr x i| ≤ B) (hy : ∀ i, |e.repr y i| ≤ B)
    (hxy : ∀ i, |e.repr x i - e.repr y i| ≤ δ) (k : ι) :
    |e.repr (lieBCH s x (-y)) k| ≤ bchBoxCoordinateBound s (Fintype.card ι) H B * δ := by
  classical
  let P := bchCoordinatePolynomial c s k
  let v : Fin 2 × ι → ℝ := fun z => e.repr (![x, -y] z.1) z.2
  let w : Fin 2 × ι → ℝ := fun z => e.repr (![y, -y] z.1) z.2
  have hdegree : P.totalDegree ≤ s := bchCoordinatePolynomial_totalDegree c s k
  have hv (z : Fin 2 × ι) : |v z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hx i
    · simpa [v] using hy i
  have hw (z : Fin 2 × ι) : |w z| ≤ B := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hy i
    · simpa [w] using hy i
  have hvw (z : Fin 2 × ι) : |v z - w z| ≤ δ := by
    rcases z with ⟨j, i⟩
    fin_cases j
    · exact hxy i
    · simpa [v, w] using hδ
  have hcoeff (m) : |((P.coeff m : ℚ) : ℝ)| ≤ bchCoordinateHeight s (Fintype.card ι) H :=
    (bchCoordinatePolynomial_height c hc s k m).abs_real_le
  have h := abs_aeval_sub_aeval_box_bound P v w (Nat.cast_nonneg _) hB hδ hcoeff hv hw hvw hdegree
  have hyneg : lieBCH s y (-y) = 0 := by
    have hg := congrArg NilpotentLieBCHGroup.coord
      (mul_inv_cancel (⟨y⟩ : NilpotentLieBCHGroup L s hnil))
    exact hg
  have hevalv : aeval v P = e.repr (lieBCH s x (-y)) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s x (-y) k
  have hevalw : aeval w P = e.repr (lieBCH s y (-y)) k :=
    bchCoordinatePolynomial_eval_over e c hstructure s y (-y) k
  rw [hevalv, hevalw, hyneg, map_zero, Finsupp.zero_apply, sub_zero] at h
  have hcard := polynomial_support_card_le P hdegree
  apply h.trans
  dsimp only [bchBoxCoordinateBound]
  simp only [Fintype.card_prod, Fintype.card_fin] at hcard
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  gcongr
  exact_mod_cast hcard

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {X : Type*}

noncomputable def bchProductWordCoefficients (s : ℕ) (xs : List X) : FreeSemigroup X →₀ ℚ :=
  (freeLieWordExpansion (bchProductLiePolynomial s xs)).coeff

noncomputable def bchProductBracketSupport (s : ℕ) (xs : List X) : Finset (FreeSemigroup X) :=
  (bchProductWordCoefficients s xs).support

noncomputable def bchProductBracketCoefficient (s : ℕ) (xs : List X) (w : FreeSemigroup X) : ℚ :=
  bchProductWordCoefficients s xs w / w.length

theorem bchProductBracketSupport_length (s : ℕ) (xs : List X) {w : FreeSemigroup X}
    (hw : w ∈ bchProductBracketSupport s xs) : w.length ≤ s :=
  bchProductLiePolynomial_support_length s xs hw

theorem bchProductWordCoefficients_eq (s : ℕ) (xs : List X) (w : FreeSemigroup X) :
    bchProductWordCoefficients s xs w =
      if w.length ≤ s then freeWordCoefficients (bchProductPolynomial s xs) w.toFreeMonoid else 0 := by
  rw [bchProductWordCoefficients, ← freeWordCoefficients_embedding,
    wordPolynomialEmbedding_freeLieExpansion, bchProductLiePolynomial_associativeExpansion,
    freeWordCoefficients_truncation, freeSemigroup_toFreeMonoid_length]

theorem lieBCHList_bracket_formula {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (f : X → L) (xs : List X) :
    lieBCHList s f xs = ∑ w ∈ bchProductBracketSupport s xs,
      bchProductBracketCoefficient s xs w • dynkinWord f w := by
  rw [← bchProductLiePolynomial_eval s hnil f xs, ← dynkinProjection_lift]
  change (bchProductWordCoefficients s xs).sum
    (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) = _
  simp only [Finsupp.sum, bchProductBracketSupport, bchProductBracketCoefficient,
    smul_smul, div_eq_mul_inv]

variable {ι : Type*} [Fintype ι]

noncomputable def bchProductCoordinatePolynomial (c : ι → ι → ι → ℚ) (s : ℕ)
    (xs : List X) (k : ι) : MvPolynomial (X × ι) ℚ :=
  ∑ w ∈ bchProductBracketSupport s xs,
    C (bchProductBracketCoefficient s xs w) * dynkinCoordinatePolynomial c w k

theorem bchProductCoordinatePolynomial_totalDegree (c : ι → ι → ι → ℚ) (s : ℕ)
    (xs : List X) (k : ι) :
    (bchProductCoordinatePolynomial c s xs k).totalDegree ≤ s := by
  apply totalDegree_finsetSum_le
  intro w hw
  have h := totalDegree_mul (C (bchProductBracketCoefficient s xs w)) (dynkinCoordinatePolynomial c w k)
  rw [totalDegree_C, zero_add] at h
  exact h.trans ((dynkinCoordinatePolynomial_totalDegree c w k).trans
    (bchProductBracketSupport_length s xs hw))

theorem bchProductCoordinatePolynomial_support_card [Fintype X]
    (c : ι → ι → ι → ℚ) (s : ℕ) (xs : List X) (k : ι) :
    (bchProductCoordinatePolynomial c s xs k).support.card ≤
      (s + 1) * (Fintype.card X * Fintype.card ι + 1) ^ s := by
  simpa only [Fintype.card_prod] using polynomial_support_card_le
    (bchProductCoordinatePolynomial c s xs k) (bchProductCoordinatePolynomial_totalDegree c s xs k)

theorem bchProductCoordinatePolynomial_eval {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (e : Basis ι ℚ L) (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (bchProductCoordinatePolynomial (lieStructureConstants e) s xs k) =
        e.repr (lieBCHList s f xs) k := by
  rw [lieBCHList_bracket_formula s hnil]
  simp only [bchProductCoordinatePolynomial, map_sum, map_mul, aeval_C,
    Algebra.algebraMap_self, RingHom.id_apply, dynkinCoordinatePolynomial_eval,
    map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]

theorem bchProductCoordinatePolynomial_eval_over {R L : Type*} [CommRing R] [Algebra ℚ R]
    [LieRing L] [LieAlgebra R L] [LieAlgebra ℚ L] [IsScalarTower ℚ R L]
    (e : Basis ι R L) (c : ι → ι → ι → ℚ)
    (hc : ∀ i j k, algebraMap ℚ R (c i j k) = e.repr ⁅e i, e j⁆ k)
    (s : ℕ) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (f : X → L) (xs : List X) (k : ι) :
    aeval (fun xi : X × ι => e.repr (f xi.1) xi.2)
      (bchProductCoordinatePolynomial c s xs k) = e.repr (lieBCHList s f xs) k := by
  change _ = e.coord k (lieBCHList s f xs)
  rw [lieBCHList_bracket_formula s hnil]
  simp only [bchProductCoordinatePolynomial, map_sum, map_mul, aeval_C,
    dynkinCoordinatePolynomial_eval_over e c hc,
    LinearMap.map_smul_of_tower, Algebra.smul_def, Basis.coord_apply]

end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

theorem lieBCH_sub_right_mem_of_mem_ideal
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L)
    {a : L} (ha : a ∈ I) (b : L) : lieBCH s a b - b ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_lieBCH, (lieQuotientMap_eq_zero I a).mpr ha,
    lieBCH_zero_left (lie_quotient_lowerCentralSeries_eq_bot hnil I), sub_self]

theorem lieBCH_sub_left_mem_of_mem_ideal
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (I : LieIdeal ℚ L)
    (a : L) {b : L} (hb : b ∈ I) : lieBCH s a b - a ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_lieBCH, (lieQuotientMap_eq_zero I b).mpr hb,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) (lie_zero _),
    add_zero, sub_self]

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dynkinWord_eq_zero_of_abelian [IsLieAbelian L] (f : X → L)
    (w : FreeSemigroup X) (hw : w.tail ≠ []) : dynkinWord f w = 0 := by
  unfold dynkinWord
  cases h : w.tail with
  | nil => exact False.elim (hw h)
  | cons x xs =>
      simp only [rightBracketList_cons, Module.End.mul_apply, rightBracket_apply,
        trivial_lie_zero, map_zero]

theorem bch_linear_words_sum {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    ∑ w ∈ (bchBracketSupport s).filter (fun w => w.tail = []),
      bchBracketCoefficient s w • dynkinWord ![a, b] w = a + b := by
  classical
  let : LieRing (ℚ × ℚ) := LieRing.ofAssociativeRing
  let : IsLieAbelian (ℚ × ℚ) :=
    ⟨fun x y => by rw [LieRing.of_associative_ring_bracket, mul_comm x y, sub_self]⟩
  let φ : (ℚ × ℚ) →ₗ[ℚ] L :=
    (LinearMap.fst ℚ ℚ ℚ).smulRight a + (LinearMap.snd ℚ ℚ ℚ).smulRight b
  let x : ℚ × ℚ := (1, 0)
  let y : ℚ × ℚ := (0, 1)
  have hxy (i : Fin 2) : φ (![x, y] i) = ![a, b] i := by
    fin_cases i <;> simp [φ, x, y]
  have hterm (w : FreeSemigroup (Fin 2)) :
      φ (dynkinWord ![x, y] w) = if w.tail = [] then dynkinWord ![a, b] w else 0 := by
    by_cases hw : w.tail = []
    · simp only [hw, if_pos, dynkinWord, rightBracketList_nil, Module.End.one_apply]
      exact hxy w.head
    · rw [dynkinWord_eq_zero_of_abelian _ _ hw, map_zero, if_neg hw]
  have h := congrArg φ (lieBCH_eq_add_of_isLieAbelian hs x y)
  rw [lieBCH_bracket_formula] at h
  simp only [map_sum, map_smul, hterm, smul_ite, smul_zero] at h
  simpa only [Finset.sum_filter, map_add, hxy 0, hxy 1, φ, x, y,
    LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.fst_apply, LinearMap.snd_apply,
    one_smul, zero_smul, add_zero, zero_add] using h

theorem lieBCH_eq_add_nonlinear_sum {s : ℕ} (hs : 1 ≤ s) (a b : L) :
    lieBCH s a b = a + b +
      ∑ w ∈ (bchBracketSupport s).filter (fun w => w.tail ≠ []),
        bchBracketCoefficient s w • dynkinWord ![a, b] w := by
  classical
  rw [lieBCH_bracket_formula, ← bch_linear_words_sum hs a b]
  exact (Finset.sum_filter_add_sum_filter_not (bchBracketSupport s)
    (fun w => w.tail = []) (fun w => bchBracketCoefficient s w • dynkinWord ![a, b] w)).symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalLieSubalgebra
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

def rationalLieStructureHeight (d H : ℕ) : ℕ :=
  (d ^ 3 + 1) * (H ^ 4) ^ (d ^ 3)

theorem rationalLieStructureHeight_le_exp (d H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (a : ℕ) (hH : (H : ℝ) ≤ Real.exp ((p + 2) ^ a)) :
    (rationalLieStructureHeight d H : ℝ) ≤ Real.exp ((p + 2) ^ (a + 6)) := by
  have hterm : ((H ^ 4 : ℕ) : ℝ) ≤ Real.exp ((p + 2) ^ (a + 2)) := by
    rw [Nat.cast_pow]
    calc
      _ ≤ (Real.exp ((p + 2) ^ a)) ^ 4 := pow_le_pow_left₀ (Nat.cast_nonneg H) hH 4
      _ = Real.exp (4 * (p + 2) ^ a) := by rw [← Real.exp_nat_mul]; norm_num
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        rw [pow_add]
        have hsq : (4 : ℝ) ≤ (p + 2) ^ 2 := by nlinarith
        simpa only [mul_comm] using
          mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ (p + 2) ^ a)
  have hcard : ((d ^ 3 : ℕ) : ℝ) ≤ (p + 2) ^ 3 := by
    rw [Nat.cast_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg d) (hd.trans (by linarith)) _
  exact rational_sum_cost_le_exp (d ^ 3) (H ^ 4) hp (a + 2) 3 hterm hcard

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

omit [Fintype κ] in
theorem transportedLieConstants_height_uniform (c : ι → ι → ι → ℚ)
    (P : Matrix κ ι ℚ) (S : Matrix ι κ ℚ) {H : ℕ}
    (hc : ∀ i j k, RationalHeightLE (c i j k) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    (hS : ∀ i j, RationalHeightLE (S i j) H) (i j k : κ) :
    RationalHeightLE (transportedLieConstants c P S i j k) (rationalLieStructureHeight (Fintype.card ι) H) := by
  have h := transportedLieConstants_height c P S hc hP hS i j k
  simpa only [rationalLieStructureHeight, pow_succ, pow_zero, one_mul] using h

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [DecidableEq ι] [DecidableEq κ]

theorem exists_bounded_lie_embedding_retraction (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H) :
    ∃ P : Matrix κ ι ℚ, P * LinearMap.toMatrix b e φ.toLinearMap = 1 ∧
      (∀ i j, RationalHeightLE (P i j) (rationalSolveHeight (Fintype.card κ) H)) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  have hli := Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ)
  obtain ⟨P, hP, hPH⟩ := exists_bounded_rational_left_inverse (LinearMap.toMatrix b e φ.toLinearMap) hli hH hB
  refine ⟨P, hP, hPH, ?_⟩
  intro i j k
  rw [lieStructureConstants_embedding b e φ P hP]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hPH u v).mono (le_max_right _ _))
    (fun u v => (hB u v).mono (le_max_left _ _)) i j k

theorem exists_bounded_lie_quotient_section (e : Basis ι ℚ L) (b : Basis κ ℚ M)
    (φ : L →ₗ⁅ℚ⁆ M) (hφ : Function.Surjective φ) {H : ℕ} (hH : 1 ≤ H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H)
    (hD : ∀ i j, RationalHeightLE (LinearMap.toMatrix e b φ.toLinearMap i j) H) :
    ∃ S : Matrix ι κ ℚ, LinearMap.toMatrix e b φ.toLinearMap * S = 1 ∧
      (∀ i j, RationalHeightLE (S i j) (rationalSolveHeight (Fintype.card κ) H)) ∧
      ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
        (rationalLieStructureHeight (Fintype.card ι) (max H (rationalSolveHeight (Fintype.card κ) H))) := by
  obtain ⟨S, hS, hSH⟩ := exists_bounded_rational_section (LinearMap.toMatrix e b φ.toLinearMap)
    (basisMatrix_surjective e b φ.toLinearMap hφ) hH hD
  refine ⟨S, hS, hSH, ?_⟩
  intro i j k
  rw [lieStructureConstants_quotient_matrix e b φ S hS]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hD u v).mono (le_max_left _ _))
    (fun u v => (hSH u v).mono (le_max_right _ _)) i j k

theorem rationalLieStructureHeight_inverse_budget (d r H : ℕ) {p : ℝ} (hp : 0 ≤ p)
    (hd : (d : ℝ) ≤ p) (hr : (r : ℝ) ≤ p) (hH : (H : ℝ) ≤ Real.exp p) :
    (rationalLieStructureHeight d (max H (rationalSolveHeight r H)) : ℝ) ≤
      Real.exp ((p + 2) ^ 11) := by
  apply rationalLieStructureHeight_le_exp d _ hp hd 5
  rw [Nat.cast_max]
  apply max_le
  · exact hH.trans (Real.exp_le_exp.mpr (le_power_budget hp (by decide : 1 ≤ 5)))
  · exact rationalSolveHeight_le_budget r H hp hr hH

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [LieRing L] [LieAlgebra ℚ L]

noncomputable def lieQuotientCoordinateEquiv (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) : (L ⧸ I) ≃ₗ[ℚ] (κ → ℚ) :=
  (Submodule.Quotient.equiv I.toSubmodule (I.toSubmodule.map e.equivFun.toLinearMap)
    e.equivFun rfl).trans (rationalQuotientEquiv D _ hker hsurj)

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
theorem lieQuotientCoordinateEquiv_apply_mk (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) (x : L) :
    lieQuotientCoordinateEquiv e I D hker hsurj (lieQuotientMap I x) = D *ᵥ e.equivFun x := by
  change rationalQuotientEquiv D _ hker hsurj (Submodule.Quotient.mk (e.equivFun x)) = _
  exact rationalQuotientEquiv_apply_mk D _ hker hsurj _

noncomputable def lieQuotientCoordinateBasis (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) : Basis κ ℚ (L ⧸ I) :=
  Basis.ofEquivFun (lieQuotientCoordinateEquiv e I D hker hsurj)

omit [DecidableEq κ] in
theorem lieQuotientCoordinateBasis_matrix (e : Basis ι ℚ L) (I : LieIdeal ℚ L)
    (D : Matrix κ ι ℚ)
    (hker : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap)
    (hsurj : Function.Surjective D.mulVec) :
    LinearMap.toMatrix e (lieQuotientCoordinateBasis e I D hker hsurj) (lieQuotientMap I).toLinearMap = D := by
  ext i j
  rw [LinearMap.toMatrix_apply, lieQuotientCoordinateBasis, Basis.ofEquivFun_repr_apply]
  change (lieQuotientCoordinateEquiv e I D hker hsurj (lieQuotientMap I (e j))) i = _
  rw [lieQuotientCoordinateEquiv_apply_mk]
  simp [Basis.equivFun_self, Matrix.mulVec, dotProduct]

omit [DecidableEq ι] in
theorem coordinate_span_matrix_range {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (v : η → L) (I : Submodule ℚ L)
    (hspan : Submodule.span ℚ (Set.range v) = I) :
    LinearMap.range (Matrix.mulVecLin (show Matrix ι η ℚ from fun i j => e.repr (v j) i)) =
      I.map e.equivFun.toLinearMap := by
  rw [Matrix.range_mulVecLin, ← hspan, Submodule.map_span, ← Set.range_comp]
  rfl

theorem exists_bounded_lie_quotient_coordinates {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (I : LieIdeal ℚ L) (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H) :
    ∃ t : ℕ, t ≤ Fintype.card η ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        ∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H)) := by
  classical
  let A : Matrix ι η ℚ := fun i j => e.repr (v j) i
  obtain ⟨t, ht, d, hd, D, S, hker, hDS, hD, hS⟩ := exists_bounded_quotient_presentation A hHpos hv
  have hker' : LinearMap.ker D.mulVecLin = I.toSubmodule.map e.equivFun.toLinearMap :=
    hker.trans (coordinate_span_matrix_range e v I.toSubmodule hspan)
  have hsurj : Function.Surjective D.mulVec := by
    intro y
    refine ⟨S *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, hDS, Matrix.one_mulVec]
  exact ⟨t, ht, d, hd, lieQuotientCoordinateBasis e I D hker' hsurj, D, S,
    lieQuotientCoordinateBasis_matrix e I D hker' hsurj, hDS, hD, hS⟩

theorem exists_bounded_lie_quotient_with_structure {η : Type*} [Fintype η]
    (e : Basis ι ℚ L) (I : LieIdeal ℚ L) (v : η → L)
    (hspan : Submodule.span ℚ (Set.range v) = I.toSubmodule) {H : ℕ} (hHpos : 1 ≤ H)
    (hv : ∀ i j, RationalHeightLE (e.repr (v j) i) H)
    (hc : ∀ i j k, RationalHeightLE (lieStructureConstants e i j k) H) :
    ∃ t : ℕ, t ≤ Fintype.card η ∧ ∃ d : ℕ, d ≤ Fintype.card ι ∧
      ∃ b : Basis (Fin d) ℚ (L ⧸ I), ∃ D : Matrix (Fin d) ι ℚ, ∃ S : Matrix ι (Fin d) ℚ,
        LinearMap.toMatrix e b (lieQuotientMap I).toLinearMap = D ∧ D * S = 1 ∧
        (∀ i j, RationalHeightLE (D i j) (rationalKernelHeight t H)) ∧
        (∀ i j, RationalHeightLE (S i j) (rationalSolveHeight d (rationalKernelHeight t H))) ∧
        ∀ i j k, RationalHeightLE (lieStructureConstants b i j k)
          (rationalLieStructureHeight (Fintype.card ι)
            (max H (max (rationalKernelHeight t H) (rationalSolveHeight d (rationalKernelHeight t H))))) := by
  obtain ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS⟩ :=
    exists_bounded_lie_quotient_coordinates e I v hspan hHpos hv
  refine ⟨t, ht, d, hd, b, D, S, hmatrix, hDS, hD, hS, ?_⟩
  intro i j k
  rw [lieStructureConstants_quotient_matrix e b (lieQuotientMap I) S
    (by rw [hmatrix]; exact hDS), hmatrix]
  exact transportedLieConstants_height_uniform _ _ _
    (fun u v w => (hc u v w).mono (le_max_left _ _))
    (fun u v => (hD u v).mono ((le_max_left _ _).trans (le_max_right _ _)))
    (fun u v => (hS u v).mono ((le_max_right _ _).trans (le_max_right _ _))) i j k

end Erdos3

end

section

namespace Erdos3

open Module

variable {ι η L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

theorem exists_bounded_lie_subalgebra_basis (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L)
    (v : η → K) (hspan : Submodule.span ℚ (Set.range v) = ⊤) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (e.repr (v i : L) j) H) :
    ∃ b : Basis (Fin (Module.finrank ℚ K)) ℚ K,
      ∀ i j, RationalHeightLE (e.repr (b i : L) j) H := by
  classical
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan, finrank_top] at hex
  obtain ⟨w, hw, hwspan, hwli⟩ := hex
  refine ⟨Basis.mk hwli (by rw [hwspan]), ?_⟩
  intro i j
  rw [Basis.mk_apply]
  obtain ⟨a, ha⟩ := hw i
  rw [← ha]
  exact hv a j

theorem lie_subalgebra_finrank_le (e : Basis ι ℚ L) (K : LieSubalgebra ℚ L) :
    Module.finrank ℚ K ≤ Fintype.card ι := by
  let : FiniteDimensional ℚ L := e.finiteDimensional_of_finite
  have h := LinearMap.finrank_le_finrank_of_injective (f := K.incl.toLinearMap)
    (fun _ _ h => Subtype.ext h)
  simpa only [Module.finrank_eq_card_basis e] using h

theorem lie_lowerCentralSeries_eq_bot_of_injective {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ M M s = ⊥ := by
  apply LieIdeal.bot_of_map_eq_bot hφ
  apply le_antisymm _ bot_le
  rw [← hnil]
  exact LieIdeal.map_lowerCentralSeries_le s

theorem lie_subalgebra_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (K : LieSubalgebra ℚ L) :
    LieModule.lowerCentralSeries ℚ K K s = ⊥ :=
  lie_lowerCentralSeries_eq_bot_of_injective K.incl (fun _ _ h => Subtype.ext h) hnil

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealWeightPMF
namespace OAI

section

namespace Erdos3

open scoped ENNReal

noncomputable def realWeightPMF {X : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) : PMF X :=
  ⟨fun x => ENNReal.ofReal (w x / ∑' y, w y), ENNReal.summable.hasSum_iff.mpr (by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun x => div_nonneg (hw x) hZ.le) (hs.div_const _),
      tsum_div_const, div_self hZ.ne', ENNReal.ofReal_one])⟩

theorem realWeightPMF_apply {X : Type*} (w : X → ℝ) (hw : ∀ x, 0 ≤ w x)
    (hs : Summable w) (hZ : 0 < ∑' x, w x) (x : X) :
    (realWeightPMF w hw hs hZ x).toReal = w x / ∑' y, w y :=
  ENNReal.toReal_ofReal (div_nonneg (hw x) hZ.le)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeExponents
namespace OAI

section

namespace Erdos3

def SquarefreeExponent {ι : Type*} (a : ι →₀ ℕ) : Prop := ∀ i, a i ≤ 1

abbrev SquarefreeIndex (ι : Type*) := {a : ι →₀ ℕ // SquarefreeExponent a}

theorem not_squarefreeExponent_add_right {ι : Type*} (a b : ι →₀ ℕ)
    (hb : ¬SquarefreeExponent b) : ¬SquarefreeExponent (a + b) := by
  intro h
  apply hb
  intro i
  have hi : a i + b i ≤ 1 := h i
  omega

theorem squarefreeExponent_add_iff {ι : Type*} (a b : ι →₀ ℕ)
    (ha : SquarefreeExponent a) (hb : SquarefreeExponent b) :
    SquarefreeExponent (a + b) ↔ Disjoint a.support b.support := by
  classical
  rw [Finset.disjoint_left]
  constructor
  · intro h i hi hj
    have hsum : a i + b i ≤ 1 := h i
    have hai := Finsupp.mem_support_iff.mp hi
    have hbi := Finsupp.mem_support_iff.mp hj
    omega
  · intro h i
    have hai := ha i
    have hbi := hb i
    change a i + b i ≤ 1
    by_cases hzero : a i = 0
    · omega
    · have hz : b i = 0 := by
        by_contra hn
        exact h (Finsupp.mem_support_iff.mpr hzero) (Finsupp.mem_support_iff.mpr hn)
      omega

noncomputable def squarefreeIndexEquiv (ι : Type*) [Fintype ι] :
    SquarefreeIndex ι ≃ (ι → Fin 2) where
  toFun a i := ⟨a.val i, Nat.lt_succ_of_le (a.property i)⟩
  invFun f := ⟨Finsupp.equivFunOnFinite.symm (fun i => (f i).val),
    fun i => Nat.le_of_lt_succ (f i).isLt⟩
  left_inv _ := Subtype.ext (Finsupp.ext fun _ => rfl)
  right_inv _ := funext fun _ => Fin.ext rfl

noncomputable instance squarefreeIndexFintype (ι : Type*) [Fintype ι] : Fintype (SquarefreeIndex ι) := by
  classical
  exact Fintype.ofEquiv (ι → Fin 2) (squarefreeIndexEquiv ι).symm

theorem card_squarefreeIndex (ι : Type*) [Fintype ι] :
    Fintype.card (SquarefreeIndex ι) = 2 ^ Fintype.card ι := by
  classical
  rw [Fintype.card_congr (squarefreeIndexEquiv ι), Fintype.card_fun, Fintype.card_fin]

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreeCoefficients
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [AddCommGroup L] [Module ℚ L]

noncomputable def squarefreeCoefficients : VectorPolynomial ι ℚ L →ₗ[ℚ] (SquarefreeIndex ι → L) where
  toFun p a := coefficients p a.val
  map_add' p q := by ext a; simp only [map_add, Finsupp.add_apply, Pi.add_apply]
  map_smul' r p := by ext a; simp only [map_smul, Finsupp.smul_apply, Pi.smul_apply, RingHom.id_apply]

@[simp] theorem squarefreeCoefficients_apply (p : VectorPolynomial ι ℚ L) (a : SquarefreeIndex ι) :
    squarefreeCoefficients p a = coefficients p a.val := rfl

theorem squarefreeCoefficients_monomial_self (a : SquarefreeIndex ι) (v : L) :
    squarefreeCoefficients (monomial a.val v) a = v := by
  classical
  simp only [squarefreeCoefficients_apply, coefficients_monomial, Finsupp.single_eq_same]

theorem squarefreeCoefficients_monomial_ne (a b : SquarefreeIndex ι) (h : a ≠ b) (v : L) :
    squarefreeCoefficients (monomial a.val v) b = 0 := by
  classical
  simp only [squarefreeCoefficients_apply, coefficients_monomial]
  exact Finsupp.single_eq_of_ne (fun he => h (Subtype.ext he.symm))

theorem squarefreeCoefficients_surjective [Fintype ι] :
    Function.Surjective (squarefreeCoefficients (ι := ι) (L := L)) := by
  classical
  intro f
  refine ⟨∑ a : SquarefreeIndex ι, monomial a.val (f a), ?_⟩
  ext b
  simp only [map_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single b]
  · exact squarefreeCoefficients_monomial_self b (f b)
  · intro a _ h
    exact squarefreeCoefficients_monomial_ne a b h (f a)
  · simp

theorem monomial_mem_squarefreeKernel (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) (v : L) :
    monomial a v ∈ LinearMap.ker (squarefreeCoefficients (ι := ι) (L := L)) := by
  classical
  change squarefreeCoefficients (monomial a v) = 0
  ext b
  simp only [squarefreeCoefficients_apply, coefficients_monomial, Pi.zero_apply]
  apply Finsupp.single_eq_of_ne
  intro he
  exact ha (he.symm ▸ b.property)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.IndependentProductTransport
namespace OAI

section

namespace Erdos3

theorem pmf_map_injective_at {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (x : X) : p.map f (f x) = p x := by
  classical
  rw [PMF.map_apply, tsum_eq_single x]
  · simp
  · intro y hy
    have hne : f x ≠ f y := fun h => hy (hf h).symm
    simp only [hne, ite_false]

theorem pmf_map_zero_off_range {X Y : Type*} (p : PMF X) (f : X → Y) (y : Y)
    (hy : y ∉ Set.range f) : p.map f y = 0 := by
  classical
  have hne (x) : y ≠ f x := fun h => hy ⟨x, h.symm⟩
  simp only [PMF.map_apply, hne, ite_false, tsum_zero]

theorem pmf_map_injective_expectation {X Y : Type*} (p : PMF X) (f : X → Y)
    (hf : Function.Injective f) (φ : Y → ℂ) :
    (∑' y, ((p.map f y).toReal : ℂ) * φ y) =
      ∑' x, ((p x).toReal : ℂ) * φ (f x) := by
  have hs : Function.support (fun y => ((p.map f y).toReal : ℂ) * φ y) ⊆ Set.range f := by
    intro y hy
    by_contra hn
    have hz := pmf_map_zero_off_range p f y hn
    exact hy (by simp only [hz, ENNReal.toReal_zero, Complex.ofReal_zero, zero_mul])
  have he := hf.tsum_eq hs
  simpa only [pmf_map_injective_at p f hf] using he.symm

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

def independentArrayRows {J I X : Type*} (z : J × I → X) : I → J → X :=
  fun i j => z (j, i)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def quotientHom (I : LieIdeal ℚ L) :
    NilpotentLieBCHGroup L s hnil →*
      NilpotentLieBCHGroup (L ⧸ I) s (lie_quotient_lowerCentralSeries_eq_bot hnil I) :=
  map (lieQuotientMap I)

@[simp] theorem quotientHom_coord (I : LieIdeal ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    (quotientHom I a).coord = lieQuotientMap I a.coord := rfl

theorem quotientHom_surjective (I : LieIdeal ℚ L) :
    Function.Surjective (quotientHom (hnil := hnil) I) := by
  intro b
  obtain ⟨a, ha⟩ := lieQuotientMap_surjective I b.coord
  exact ⟨⟨a⟩, ext ha⟩

noncomputable def quotientEquiv (I : LieIdeal ℚ L) :
    NilpotentLieBCHGroup L s hnil ⧸ (quotientHom (hnil := hnil) I).ker ≃*
      NilpotentLieBCHGroup (L ⧸ I) s (lie_quotient_lowerCentralSeries_eq_bot hnil I) :=
  QuotientGroup.quotientKerEquivOfSurjective (quotientHom I) (quotientHom_surjective I)

@[simp] theorem quotientEquiv_mk (I : LieIdeal ℚ L) (a : NilpotentLieBCHGroup L s hnil) :
    quotientEquiv I (QuotientGroup.mk a) = quotientHom I a := rfl

theorem commute_of_lie_eq_zero (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ = 0) : Commute a b := by
  apply ext
  change lieBCH s a.coord b.coord = lieBCH s b.coord a.coord
  have hba : ⁅b.coord, a.coord⁆ = 0 := by rw [← lie_skew, hab, neg_zero]
  rw [lieBCH_eq_add_of_lie_eq_zero hnil hab, lieBCH_eq_add_of_lie_eq_zero hnil hba, add_comm]

theorem commutator_mem_ideal (I : LieIdeal ℚ L) (a b : NilpotentLieBCHGroup L s hnil)
    (hab : ⁅a.coord, b.coord⁆ ∈ I) : (a * b * a⁻¹ * b⁻¹).coord ∈ I := by
  have hlie : ⁅(quotientHom I a).coord, (quotientHom I b).coord⁆ = 0 := by
    rw [quotientHom_coord, quotientHom_coord, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  have hc := commute_of_lie_eq_zero (quotientHom I a) (quotientHom I b) hlie
  have h : quotientHom I (a * b * a⁻¹ * b⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hc.eq]
    simp [mul_assoc]
  apply (lieQuotientMap_eq_zero I _).mp
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

include hnil

theorem lieBCH_sub_add_mem (I : LieIdeal ℚ L) (a b : L) (hab : ⁅a, b⁆ ∈ I) :
    lieBCH s a b - (a + b) ∈ I := by
  apply (lieQuotientMap_eq_zero I _).mp
  have hbracket : ⁅lieQuotientMap I a, lieQuotientMap I b⁆ = 0 := by
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hab
  rw [map_sub, map_add, map_lieBCH,
    lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) hbracket, sub_self]

namespace NilpotentLieBCHGroup

theorem additive_remainder_mem (I : LieIdeal ℚ L) (r w : L) (hrw : ⁅r, w⁆ ∈ I) :
    (((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹).coord) ∈ I := by
  have hsum : quotientHom I (⟨r + w⟩ : NilpotentLieBCHGroup L s hnil) =
      quotientHom I (⟨r⟩ : NilpotentLieBCHGroup L s hnil) * quotientHom I (⟨w⟩ : NilpotentLieBCHGroup L s hnil) := by
    apply ext
    change lieQuotientMap I (r + w) = lieBCH s (lieQuotientMap I r) (lieQuotientMap I w)
    rw [map_add]
    apply (lieBCH_eq_add_of_lie_eq_zero (lie_quotient_lowerCentralSeries_eq_bot hnil I) ?_).symm
    rw [← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hrw
  apply (lieQuotientMap_eq_zero I _).mp
  have h : quotientHom I
      ((⟨r⟩ : NilpotentLieBCHGroup L s hnil)⁻¹ * ⟨r + w⟩ * (⟨w⟩ : NilpotentLieBCHGroup L s hnil)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, hsum]
    simp only [inv_mul_cancel_left, mul_inv_cancel]
  exact congrArg coord h

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem coord_pow (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = n • g.coord := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, coord_mul, ih,
      lieBCH_eq_add_of_lie_eq_zero hnil (by simp [nsmul_lie]), succ_nsmul]

theorem coord_zpow (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) :
    (g ^ n).coord = n • g.coord := by
  cases n with
  | ofNat n =>
    change (g ^ (n : ℤ)).coord = (n : ℤ) • g.coord
    simpa only [zpow_natCast, natCast_zsmul] using coord_pow g n
  | negSucc n =>
    simp only [zpow_negSucc, coord_inv, coord_pow, negSucc_zsmul]

theorem coord_pow_rat (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) :
    (g ^ n).coord = (n : ℚ) • g.coord := by
  rw [coord_pow, Nat.cast_smul_eq_nsmul ℚ]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

structure NilpotentLieFiltration (s : ℕ) where
  layer : ℕ → Submodule ℚ L
  antitone : Antitone layer
  one_eq_top : layer 1 = ⊤
  lie_mem : ∀ {i j : ℕ} {a b : L}, a ∈ layer i → b ∈ layer j → ⁅a, b⁆ ∈ layer (i + j)
  terminal : layer (s + 1) = ⊥

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

def layerIdeal (i : ℕ) : LieIdeal ℚ L :=
  { F.layer i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 := by simp [F.one_eq_top]
      exact F.antitone (Nat.le_add_left i 1) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (i : ℕ) (a : L) : a ∈ F.layerIdeal i ↔ a ∈ F.layer i := Iff.rfl

theorem lowerCentralSeries_le (n : ℕ) :
    LieModule.lowerCentralSeries ℚ L L n ≤ F.layerIdeal (n + 1) := by
  induction n with
  | zero =>
    intro a _
    change a ∈ F.layer 1
    simp [F.one_eq_top]
  | succ n ih =>
    rw [LieModule.lowerCentralSeries_succ, LieSubmodule.lie_le_iff]
    intro a _ b hb
    have ha : a ∈ F.layer 1 := by simp [F.one_eq_top]
    have h := F.lie_mem ha (ih hb)
    change ⁅a, b⁆ ∈ F.layer (n + 1 + 1)
    simpa only [Nat.add_comm 1 (n + 1)] using h

theorem lowerCentralSeries_eq_bot : LieModule.lowerCentralSeries ℚ L L s = ⊥ := by
  apply bot_unique
  intro a ha
  have h := F.lowerCentralSeries_le s ha
  change a ∈ F.layer (s + 1) at h
  change a = 0
  simpa only [F.terminal, Submodule.mem_bot] using h

abbrev Group := NilpotentLieBCHGroup L s F.lowerCentralSeries_eq_bot

def subgroup (i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal i).toLieSubalgebra

@[simp] theorem mem_subgroup (i : ℕ) (a : F.Group) : a ∈ F.subgroup i ↔ a.coord ∈ F.layer i := Iff.rfl

theorem subgroup_one : F.subgroup 1 = ⊤ := by
  apply top_unique
  intro a _
  change a.coord ∈ F.layer 1
  simp [F.one_eq_top]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

def bchSubgroupCoordinates (e : Basis ι ℚ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    Set (ι → ℚ) := {x | (⟨e.equivFun.symm x⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ}

variable [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] in

theorem bchSubgroupCoordinates_comap (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) :
    bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) =
      (LinearMap.toMatrix b e φ.toLinearMap).mulVec ⁻¹' bchSubgroupCoordinates e Γ := by
  ext x
  change ((⟨φ (b.equivFun.symm x)⟩ : NilpotentLieBCHGroup L s hL) ∈ Γ) ↔
    ((⟨e.equivFun.symm (LinearMap.toMatrix b e φ.toLinearMap *ᵥ x)⟩ :
      NilpotentLieBCHGroup L s hL) ∈ Γ)
  rw [basisMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

theorem exists_bchSubgroup_comap_grid_exp_bound (b : Basis κ ℚ M) (e : Basis ι ℚ L)
    (φ : M →ₗ⁅ℚ⁆ L) (hφ : Function.Injective φ)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hL)) {H l : ℕ} (hHpos : 1 ≤ H) (hlpos : 0 < l)
    (hB : ∀ i j, RationalHeightLE (LinearMap.toMatrix b e φ.toLinearMap i j) H)
    (hinner : scaledIntegerGrid l ⊆ bchSubgroupCoordinates e Γ)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l)
    {p : ℝ} (hp : 0 ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p) (hr : (Fintype.card κ : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : (l : ℝ) ≤ Real.exp p) :
    ∃ N : ℕ, 0 < N ∧ (N : ℝ) ≤ Real.exp ((p + 2) ^ 9) ∧
      scaledIntegerGrid N ⊆ bchSubgroupCoordinates b
        (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ∧
      bchSubgroupCoordinates b (Γ.comap (NilpotentLieBCHGroup.map (hnil := hM) φ)) ⊆ denominatorGrid N := by
  rw [bchSubgroupCoordinates_comap b e φ Γ]
  exact exists_preimage_grid_exp_bound (LinearMap.toMatrix b e φ.toLinearMap)
    (Matrix.mulVec_injective_iff.mp (basisMatrix_injective b e φ.toLinearMap hφ))
    hHpos hlpos hB _ hinner houter hp hd hr hH hl

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem descendingCentralSeries : Subgroup.IsDescendingCentralSeries
    (fun n => subgroup (hnil := hnil)
      ((LieModule.lowerCentralSeries ℚ L L n : LieIdeal ℚ L) : LieSubalgebra ℚ L)) := by
  constructor
  · apply top_unique
    intro a _
    change a.coord ∈ LieModule.lowerCentralSeries ℚ L L 0
    simp
  · intro a n ha b
    change (a * b * a⁻¹ * b⁻¹).coord ∈ LieModule.lowerCentralSeries ℚ L L (n + 1)
    apply commutator_mem_ideal
    rw [← lie_skew a.coord b.coord]
    apply (LieModule.lowerCentralSeries ℚ L L (n + 1)).neg_mem
    rw [LieModule.lowerCentralSeries_succ]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top b.coord) ha

theorem lowerCentralSeries_eq_bot :
    (⊤ : Subgroup (NilpotentLieBCHGroup L s hnil)).lowerCentralSeries s = ⊥ := by
  apply bot_unique
  apply (Subgroup.descending_central_series_ge_lower _ (descendingCentralSeries (hnil := hnil)) s).trans
  intro a ha
  rw [Subgroup.mem_bot]
  apply ext
  change a.coord = 0
  change a.coord ∈ LieModule.lowerCentralSeries ℚ L L s at ha
  simpa only [hnil, LieSubmodule.mem_bot] using ha

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def conjugationCoord (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  (g * (⟨x⟩ : NilpotentLieBCHGroup L s hnil) * g⁻¹).coord

theorem conjugationCoord_nsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℕ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_pow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_pow, coord_pow]
  rfl

theorem conjugationCoord_zsmul (g : NilpotentLieBCHGroup L s hnil) (n : ℤ) (x : L) :
    conjugationCoord g (n • x) = n • conjugationCoord g x := by
  have he : (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil) =
      (⟨x⟩ : NilpotentLieBCHGroup L s hnil) ^ n := by
    apply ext
    exact (coord_zpow _ _).symm
  change ((MulAut.conj g) (⟨n • x⟩ : NilpotentLieBCHGroup L s hnil)).coord = _
  rw [he, map_zpow, coord_zpow]
  rfl

theorem conjugationCoord_rat_smul (g : NilpotentLieBCHGroup L s hnil) (q : ℚ) (x : L) :
    conjugationCoord g (q • x) = q • conjugationCoord g x := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
    calc
      _ = (q.den : ℚ) * ((q.num : ℚ) / q.den) :=
        congrArg ((q.den : ℚ) * ·) (Rat.num_div_den q).symm
      _ = _ := by field_simp
  apply smul_right_injective L hd
  dsimp only
  calc
    _ = conjugationCoord g ((q.den : ℚ) • (q • x)) := by
      simpa only [Nat.cast_smul_eq_nsmul] using (conjugationCoord_nsmul g q.den (q • x)).symm
    _ = conjugationCoord g ((q.num : ℚ) • x) := by rw [smul_smul, hq]
    _ = (q.num : ℚ) • conjugationCoord g x := by
      simpa only [Int.cast_smul_eq_zsmul] using conjugationCoord_zsmul g q.num x
    _ = _ := by rw [smul_smul, hq]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

end Erdos3

end

end OAI

end


