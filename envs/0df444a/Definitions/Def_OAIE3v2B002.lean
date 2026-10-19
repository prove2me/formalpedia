-- Prove2me | Definitions.Def_OAIE3v2B002
-- name    : OAIE3v2B002
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:47.459626+00:00
-- url     : https://prove2.me/theorems/34a1e5d5-affb-45bf-849a-f2f0a89fee23
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 3 of 311
-- statement:
--   Definitions bundle 3 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/BooleanCubeModeWitness.lean`, `Estimates/CubeTranslation.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/LieFiniteProduct.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/RiemannianLipschitz.lean`, `Estimates/RightCosetEDistance.lean`, `Estimates/SquareGradedRelative.lean`, `Estimates/SquarefreeCoefficients.lean`, `Estimates/SquarefreeExponents.lean`, `Estimates/WeightedLoweringGroup.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `Geometry/DilationPairCoordinates.lean`, `Geometry/LieCoordinateSmooth.lean`, `Geometry/RightCosetMetricMap.lean`, `Geometry/WeightedSupportDropRename.lean`, `Lattices/BoxResiduePartition.lean`, `Lattices/PhysicalSubboxResidueSlice.lean`, `Lattices/ResidueSliceCountingCost.lean`, `Lattices/SelectedResidueApproximation.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/DualIdealSteps.lean`, `Linear/DualLieAlgebra.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialCoefficientGridDenominator.lean`, `Polynomial/PolynomialKernelValues.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Polynomial/RealGradedSymbolPolynomial.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.BooleanCubeModeWitness
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open _root_.MvPolynomial
open scoped BigOperators

abbrev Variable (α β : Type*) := Option (α ⊕ β)

inductive Form (α β : Type*) where
  | coordinate : Variable α β → Form α β
  | difference : α → Form α β

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CubeTranslation
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] [DecidableEq A]

def translateSupport (a : A) (Q : Finset A) : Finset A := Q.image (fun x ↦ a + x)

theorem mem_translateSupport (a : A) (Q : Finset A) (x : A) :
    x ∈ translateSupport a Q ↔ x - a ∈ Q := by
  rw [translateSupport, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨x - a, hx, by abel⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeLieTreeCoefficientBounds
namespace OAI

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem freeSemigroup_toFreeMonoid_length (w : FreeSemigroup X) :
    w.toFreeMonoid.length = w.length := by
  cases w
  rw [FreeSemigroup.toFreeMonoid_mk_eq_cons]
  rfl

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def freeWordCoefficients : FreeAlgebra ℚ X →ₗ[ℚ] (FreeMonoid X →₀ ℚ) :=
  (MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearMap

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

noncomputable def freeWordSplits (w : FreeMonoid X) : Finset (FreeMonoid X × FreeMonoid X) := by
  classical
  exact (Finset.range (w.length + 1)).image (fun n =>
    (FreeMonoid.ofList (w.toList.take n), FreeMonoid.ofList (w.toList.drop n)))

theorem mem_freeWordSplits (w u v : FreeMonoid X) :
    (u, v) ∈ freeWordSplits w ↔ u * v = w := by
  classical
  unfold freeWordSplits
  constructor
  · intro h
    obtain ⟨n, _, hnv⟩ := Finset.mem_image.mp h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hnv
    change FreeMonoid.ofList (w.toList.take n ++ w.toList.drop n) = w
    rw [List.take_append_drop]
    rfl
  · intro h
    subst w
    apply Finset.mem_image.mpr
    refine ⟨u.length, Finset.mem_range.mpr ?_, ?_⟩
    · rw [FreeMonoid.length_mul]
      omega
    · change (FreeMonoid.ofList ((u.toList ++ v.toList).take u.toList.length),
        FreeMonoid.ofList ((u.toList ++ v.toList).drop u.toList.length)) = (u, v)
      simp only [List.take_left, List.drop_left]
      rfl

theorem freeWordSplits_card_le (w : FreeMonoid X) : (freeWordSplits w).card ≤ w.length + 1 := by
  classical
  unfold freeWordSplits
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

theorem freeWordCoefficients_mul (p q : FreeAlgebra ℚ X) (w : FreeMonoid X) :
    freeWordCoefficients (p * q) w =
      ∑ uv ∈ freeWordSplits w, freeWordCoefficients p uv.1 * freeWordCoefficients q uv.2 := by
  change (FreeAlgebra.equivMonoidAlgebraFreeMonoid (p * q)).coeff w = _
  rw [map_mul]
  exact MonoidAlgebra.coeff_mul_antidiag _ _ _ _ (fun {uv} => mem_freeWordSplits w uv.1 uv.2)

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

def FreeCoefficientBound (s D M : ℕ) (p : FreeAlgebra ℚ X) : Prop :=
  ∀ w, w.length ≤ s → ∃ a : ℤ,
    (a : ℚ) = (D : ℚ) * freeWordCoefficients p w ∧ a.natAbs ≤ M

namespace FreeCoefficientBound

variable {s D E M N : ℕ} {p q : FreeAlgebra ℚ X}

theorem neg (hp : FreeCoefficientBound s D M p) : FreeCoefficientBound s D M (-p) := by
  intro w hw
  obtain ⟨a, ha, hb⟩ := hp w hw
  refine ⟨-a, ?_, by simpa using hb⟩
  simp only [Int.cast_neg, map_neg, Finsupp.neg_apply, mul_neg, ha]

theorem mul (hp : FreeCoefficientBound s D M p) (hq : FreeCoefficientBound s E N q) :
    FreeCoefficientBound s (D * E) ((s + 1) * M * N) (p * q) := by
  classical
  intro w hw
  have hlen : ∀ uv ∈ freeWordSplits w, uv.1.length ≤ s ∧ uv.2.length ≤ s := by
    intro uv huv
    have hmul := (mem_freeWordSplits w uv.1 uv.2).mp huv
    have h := congrArg FreeMonoid.length hmul
    rw [FreeMonoid.length_mul] at h
    omega
  choose a ha haM using fun uv : freeWordSplits w => hp uv.val.1 (hlen uv uv.property).1
  choose b hb hbN using fun uv : freeWordSplits w => hq uv.val.2 (hlen uv uv.property).2
  refine ⟨∑ uv, a uv * b uv, ?_, ?_⟩
  · push_cast
    simp_rw [ha, hb]
    rw [freeWordCoefficients_mul, Finset.mul_sum]
    conv_rhs => rw [← Finset.sum_coe_sort]
    apply Finset.sum_congr rfl
    intro uv _
    ring
  · calc
      _ ≤ ∑ uv, (a uv * b uv).natAbs := Int.natAbs_sum_le _ _
      _ ≤ ∑ _uv : freeWordSplits w, M * N := by
        apply Finset.sum_le_sum
        intro uv _
        simpa only [Int.natAbs_mul] using Nat.mul_le_mul (haM uv) (hbN uv)
      _ = (freeWordSplits w).card * (M * N) := by simp
      _ ≤ (s + 1) * (M * N) := Nat.mul_le_mul_right _
        ((freeWordSplits_card_le w).trans (Nat.add_le_add_right hw 1))
      _ = _ := by ring

end FreeCoefficientBound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

open Module

section Real

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]

theorem continuous_lie_of_real_basis (e : Basis ι ℝ L) :
    Continuous (fun z : L × L => ⁅z.1, z.2⁆) := by
  classical
  have hcoord (i : ι) : Continuous (fun x : L => e.repr x i) :=
    (continuous_apply i).comp e.equivFunL.continuous
  have hformula (a b : L) : ⁅a, b⁆ =
      ∑ i, ∑ j, e.repr a i • e.repr b j • ⁅e i, e j⁆ := by
    conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
    simp only [sum_lie, lie_sum, smul_lie, lie_smul, Finset.smul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact smul_comm _ _ _
  have heq : (fun z : L × L => ⁅z.1, z.2⁆) =
      (fun z => ∑ i, ∑ j, e.repr z.1 i • e.repr z.2 j • ⁅e i, e j⁆) :=
    funext (fun z => hformula z.1 z.2)
  rw [heq]
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  exact ((hcoord i).comp continuous_fst).smul
    (((hcoord j).comp continuous_snd).smul continuous_const)

theorem continuous_lie_finiteDimensional [FiniteDimensional ℝ L] :
    Continuous (fun z : L × L => ⁅z.1, z.2⁆) :=
  continuous_lie_of_real_basis (Module.finBasis ℝ L)

end Real

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

abbrev VectorPolynomial (σ R V : Type*) [CommRing R] [AddCommGroup V] [Module R V] :=
  MvPolynomial σ R ⊗[R] V

namespace VectorPolynomial

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def coefficients : VectorPolynomial σ R V ≃ₗ[R] (σ →₀ ℕ) →₀ V := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft (MvPolynomial.basisMonomials σ R)

noncomputable def monomial (α : σ →₀ ℕ) (v : V) : VectorPolynomial σ R V :=
  MvPolynomial.monomial α (1 : R) ⊗ₜ[R] v

@[simp] theorem coefficients_tmul (p : MvPolynomial σ R) (v : V) (α : σ →₀ ℕ) :
    coefficients (p ⊗ₜ[R] v) α = p.coeff α • v := by
  classical
  exact TensorProduct.equivFinsuppOfBasisLeft_apply_tmul_apply _ _ _ _

@[simp] theorem coefficients_monomial (α : σ →₀ ℕ) (v : V) :
    coefficients (monomial (R := R) α v) = Finsupp.single α v := by
  classical
  ext β
  by_cases h : α = β
  · subst β
    simp [monomial]
  · simp [monomial, h, Ne.symm h]

@[simp] theorem coefficients_symm_single (α : σ →₀ ℕ) (v : V) :
    (coefficients (R := R)).symm (Finsupp.single α v) = monomial α v := by
  apply coefficients.injective
  simp

theorem sum_monomial_coefficients (p : VectorPolynomial σ R V) :
    (coefficients p).sum (fun α v => monomial (R := R) α v) = p := by
  classical
  exact (TensorProduct.equivFinsuppOfBasisLeft_symm_apply
    (MvPolynomial.basisMonomials σ R) (coefficients p)).symm.trans
      (coefficients.symm_apply_apply p)

noncomputable def map (f : V →ₗ[R] W) : VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R W :=
  f.lTensor (MvPolynomial σ R)

@[simp] theorem map_monomial (f : V →ₗ[R] W) (α : σ →₀ ℕ) (v : V) :
    map f (monomial α v) = monomial α (f v) := rfl

@[simp] theorem coefficients_map (f : V →ₗ[R] W) (p : VectorPolynomial σ R V)
    (α : σ →₀ ℕ) : coefficients (map f p) α = f (coefficients p α) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp [map]
  | add p q hp hq => simp [hp, hq]

def DegreeLE (w : σ → ℕ) (d : ℕ) (p : VectorPolynomial σ R V) : Prop :=
  ∀ α, d < Finsupp.weight w α → coefficients p α = 0

noncomputable def eval (x : σ → R) : VectorPolynomial σ R V →ₗ[R] V :=
  (TensorProduct.lid R V).toLinearMap.comp
    ((MvPolynomial.aeval x).toLinearMap.rTensor V)

@[simp] theorem eval_tmul (x : σ → R) (q : MvPolynomial σ R) (v : V) :
    eval x (q ⊗ₜ[R] v) = MvPolynomial.aeval x q • v := rfl

@[simp] theorem eval_monomial (x : σ → R) (α : σ →₀ ℕ) (v : V) :
    eval x (monomial α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.eval_monomial]

@[simp] theorem eval_map (x : σ → R) (f : V →ₗ[R] W) (p : VectorPolynomial σ R V) :
    eval x (map f p) = f (eval x p) := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp [map]
  | add p q hp hq => simp [hp, hq]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def multiplyVariable (i : σ) :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial σ ℚ V :=
  (LinearMap.mulLeft ℚ (MvPolynomial.X i : MvPolynomial σ ℚ)).rTensor V

@[simp] theorem multiplyVariable_tmul (i : σ) (P : MvPolynomial σ ℚ) (v : V) :
    multiplyVariable i (P ⊗ₜ[ℚ] v) = (MvPolynomial.X i * P) ⊗ₜ[ℚ] v := rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ ι R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def coefficientTensorBasis (b : Basis ι R V) :
    Basis ((σ →₀ ℕ) × ι) R (VectorPolynomial σ R V) :=
  (MvPolynomial.basisMonomials σ R).tensorProduct b

@[simp] theorem coefficientTensorBasis_apply (b : Basis ι R V) (α : σ →₀ ℕ) (i : ι) :
    coefficientTensorBasis b (α, i) = monomial α (b i) := by
  simp [coefficientTensorBasis, monomial]

theorem coefficientTensorBasis_repr (b : Basis ι R V) (p : VectorPolynomial σ R V)
    (α : σ →₀ ℕ) (i : ι) :
    (coefficientTensorBasis b).repr p (α, i) = b.repr (coefficients p α) i := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
      simp only [coefficientTensorBasis, Basis.tensorProduct_repr_tmul_apply, coefficients_tmul,
        map_smul, Finsupp.smul_apply, smul_eq_mul]
      change b.repr v i * q.coeff α = q.coeff α * b.repr v i
      exact mul_comm _ _
  | add p q hp hq =>
      simp only [map_add, Finsupp.add_apply, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [AddCommGroup V] [Module R V]

noncomputable def coordinate (f : V →+ S) (p : VectorPolynomial σ R V) : MvPolynomial σ S :=
  (MvPolynomial.basisMonomials σ S).repr.symm ((coefficients p).mapRange f f.map_zero)

@[simp] theorem coeff_coordinate (f : V →+ S) (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    (coordinate f p).coeff α = f (coefficients p α) := by
  change ((MvPolynomial.basisMonomials σ S).repr
    ((MvPolynomial.basisMonomials σ S).repr.symm _)) α = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem coordinate_monomial (f : V →+ S) (α : σ →₀ ℕ) (v : V) :
    coordinate f (monomial (R := R) α v) = MvPolynomial.monomial α (f v) := by
  classical
  ext β
  by_cases h : α = β
  · subst β
    simp
  · simp [h, Ne.symm h]

@[simp] theorem coordinate_sum {κ : Type*} (f : V →+ S) (u : Finset κ)
    (p : κ → VectorPolynomial σ R V) :
    coordinate f (∑ i ∈ u, p i) = ∑ i ∈ u, coordinate f (p i) := by
  ext α
  simp only [coeff_coordinate, map_sum, Finsupp.finsetSum_apply, MvPolynomial.coeff_sum]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W) :
    VectorPolynomial σ R (V × W) :=
  map (LinearMap.inl R V W) p + map (LinearMap.inr R V W) q

@[simp] theorem coefficients_pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W)
    (α : σ →₀ ℕ) : coefficients (pair p q) α = (coefficients p α, coefficients q α) := by
  simp [pair]

@[simp] theorem eval_pair (p : VectorPolynomial σ R V) (q : VectorPolynomial σ R W) (x : σ → R) :
    eval x (pair p q) = (eval x p, eval x q) := by
  simp [pair]

noncomputable def restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) : VectorPolynomial σ R P :=
  coefficients.symm
    { support := (coefficients p).support
      toFun α := ⟨coefficients p α, hp α⟩
      mem_support_toFun := by intro α; simp }

@[simp] theorem coefficients_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) (α : σ →₀ ℕ) :
    (coefficients (restrictCoefficients P p hp) α : V) = coefficients p α := by
  simp only [restrictCoefficients, LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem map_restrictCoefficients (P : Submodule R V) (p : VectorPolynomial σ R V)
    (hp : ∀ α, coefficients p α ∈ P) : map P.subtype (restrictCoefficients P p hp) = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_map]
  exact coefficients_restrictCoefficients P p hp α

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

def coefficientSupport (S : Set (σ →₀ ℕ)) : Submodule R (VectorPolynomial σ R V) where
  carrier := {p | ∀ a, a ∉ S → coefficients p a = 0}
  zero_mem' := by simp
  add_mem' hp hq := by
    intro a ha
    simp only [map_add, Finsupp.add_apply, hp a ha, hq a ha, add_zero]
  smul_mem' c p hp := by
    intro a ha
    simp only [map_smul, Finsupp.smul_apply, hp a ha, smul_zero]

@[simp] theorem mem_coefficientSupport (S : Set (σ →₀ ℕ)) (p : VectorPolynomial σ R V) :
    p ∈ coefficientSupport S ↔ ∀ a, a ∉ S → coefficients p a = 0 := Iff.rfl

theorem monomial_mem_coefficientSupport {S : Set (σ →₀ ℕ)} {a : σ →₀ ℕ}
    (ha : a ∈ S) (v : V) : monomial (R := R) a v ∈ coefficientSupport S := by
  classical
  intro b hb
  have hab : a ≠ b := by rintro rfl; exact hb ha
  simp [hab]

@[simp] theorem coefficientSupport_empty :
    coefficientSupport (R := R) (V := V) (∅ : Set (σ →₀ ℕ)) = ⊥ := by
  apply bot_unique
  intro p hp
  apply coefficients.injective
  ext a
  exact hp a (Set.notMem_empty a)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {σ ι R S V : Type*} [CommRing R] [CommRing S]
  [AddCommGroup V] [Module R V]

noncomputable def ofScalar (f : S →+ V) (p : MvPolynomial σ S) : VectorPolynomial σ R V :=
  coefficients.symm (((MvPolynomial.basisMonomials σ S).repr p).mapRange f f.map_zero)

@[simp] theorem coefficients_ofScalar (f : S →+ V) (p : MvPolynomial σ S) (α : σ →₀ ℕ) :
    coefficients (ofScalar (R := R) f p) α = f (p.coeff α) := by
  simp only [ofScalar, LinearEquiv.apply_symm_apply, Finsupp.mapRange_apply]
  rfl

variable [Fintype ι] [Module S V]

noncomputable def ofCoordinates (e : Module.Basis ι S V) (p : ι → MvPolynomial σ S) :
    VectorPolynomial σ R V :=
  ∑ i, ofScalar ((LinearMap.id : S →ₗ[S] S).smulRight (e i)).toAddHom (p i)

theorem coefficients_ofCoordinates (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (α : σ →₀ ℕ) :
    coefficients (ofCoordinates (R := R) e p) α = ∑ index, (p index).coeff α • e index := by
  simp [ofCoordinates]

@[simp] theorem coordinate_ofCoordinates (e : Module.Basis ι S V)
    (p : ι → MvPolynomial σ S) (i : ι) :
    coordinate (e.coord i).toAddMonoidHom (ofCoordinates (R := R) e p) = p i := by
  classical
  ext α
  rw [coeff_coordinate, coefficients_ofCoordinates]
  change e.coord i (∑ index, (p index).coeff α • e index) = _
  simp [Module.Basis.coord_apply, Finsupp.single_apply, mul_ite]

@[simp] theorem ofCoordinates_coordinate (e : Module.Basis ι S V)
    (p : VectorPolynomial σ R V) :
    ofCoordinates e (fun i => coordinate (e.coord i).toAddMonoidHom p) = p := by
  apply coefficients.injective
  ext α
  rw [coefficients_ofCoordinates]
  simp only [coeff_coordinate]
  change (∑ i, e.repr (coefficients p α) i • e i) = coefficients p α
  exact e.sum_repr _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped Pointwise

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialTranslate (h : σ → R) : MvPolynomial σ R →ₐ[R] MvPolynomial σ R :=
  MvPolynomial.aeval (fun i => X i + C (h i))

@[simp] theorem polynomialTranslate_X (h : σ → R) (i : σ) :
    polynomialTranslate h (X i) = X i + C (h i) := by simp [polynomialTranslate]

@[simp] theorem polynomialTranslate_C (h : σ → R) (r : R) :
    polynomialTranslate h (C r) = C r := by simp [polynomialTranslate]

noncomputable def weightedSupportLT (w : σ → ℕ) (d : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {α | Finsupp.weight w α < d}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators Pointwise

variable {σ : Type*}

noncomputable def scalarDirectionalDerivative [Fintype σ] (h : σ → ℚ) :
    Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) :=
  ∑ i, h i • MvPolynomial.pderiv i

theorem scalarDirectionalDerivative_apply [Fintype σ] (h : σ → ℚ) (p : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative h p = ∑ i, h i • MvPolynomial.pderiv i p := by
  change (Derivation.coeFnAddMonoidHom (∑ i, h i • MvPolynomial.pderiv i)) p = _
  rw [map_sum]
  simp only [Finset.sum_apply, Derivation.coeFnAddMonoidHom_apply, Derivation.smul_apply]

@[simp] theorem scalarDirectionalDerivative_C [Fintype σ] (h : σ → ℚ) (c : ℚ) :
    scalarDirectionalDerivative h (C c) = 0 := MvPolynomial.derivation_C _ _

@[simp] theorem scalarDirectionalDerivative_X [Fintype σ] (h : σ → ℚ) (j : σ) :
    scalarDirectionalDerivative h (X j) = C (h j) := by
  classical
  simp [scalarDirectionalDerivative_apply, MvPolynomial.pderiv_X, Pi.single_apply, MvPolynomial.C_eq_smul_one]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

@[simp] theorem polynomialTranslate_zero (V : MvPolynomial σ ℚ) :
    polynomialTranslate (0 : σ → ℚ) V = V := by
  induction V using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [hp]

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

def denominatorGrid (L : ℕ) : Set (ι → ℚ) :=
  {x | IntegralVector ((L : ℚ) • x)}

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

attribute [local instance] LieRing.ofAssociativeRing

end Erdos3

end

section

namespace Erdos3
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieFiniteProduct
namespace OAI

section

namespace Erdos3

open Module

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]

instance lieRingPi : LieRing (∀ a, M a) where
  bracket x y a := ⁅x a, y a⁆
  add_lie x y z := by funext a; exact add_lie _ _ _
  lie_add x y z := by funext a; exact lie_add _ _ _
  lie_self x := by funext a; exact lie_self _
  leibniz_lie x y z := by funext a; exact leibniz_lie _ _ _

@[simp] theorem lie_pi_apply (x y : ∀ a, M a) (a : α) : ⁅x, y⁆ a = ⁅x a, y a⁆ := rfl

variable {R : Type*} [CommRing R] [∀ a, LieAlgebra R (M a)]

instance lieAlgebraPi : LieAlgebra R (∀ a, M a) where
  lie_smul r x y := by funext a; exact lie_smul _ _ _

def liePiEval (a : α) : (∀ a, M a) →ₗ⁅R⁆ M a where
  toLinearMap := LinearMap.proj a
  map_lie' := rfl

@[simp] theorem liePiEval_apply (a : α) (x : ∀ a, M a) : liePiEval (R := R) a x = x a := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.DilationPairCoordinates
namespace OAI

section

namespace Erdos3

variable {L : Type*} [AddCommGroup L] [Module ℚ L]

def scaledPairDifference (q : ℚ) : (L × L) →ₗ[ℚ] L :=
  LinearMap.fst ℚ L L - q • LinearMap.snd ℚ L L

@[simp] theorem scaledPairDifference_apply (q : ℚ) (x : L × L) :
    scaledPairDifference q x = x.1 - q • x.2 := rfl

def scaledPairAssemble (q : ℚ) (u v : L) : L × L := (u + q • v, v)

@[simp] theorem scaledPairDifference_assemble (q : ℚ) (u v : L) :
    scaledPairDifference q (scaledPairAssemble q u v) = u := by
  simp [scaledPairAssemble]

def scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ) : Submodule ℚ (L × L) where
  carrier := {x | x.1 ∈ P ∧ x.2 ∈ P ∧ scaledPairDifference q x ∈ Q}
  zero_mem' := ⟨P.zero_mem, P.zero_mem, by simp⟩
  add_mem' hx hy := ⟨P.add_mem hx.1 hy.1, P.add_mem hx.2.1 hy.2.1,
    by simpa only [map_add] using Q.add_mem hx.2.2 hy.2.2⟩
  smul_mem' a x hx := ⟨P.smul_mem a hx.1, P.smul_mem a hx.2.1,
    by simpa only [map_smul] using Q.smul_mem a hx.2.2⟩

@[simp] theorem mem_scaledPairLayer (P Q : Submodule ℚ L) (q : ℚ) (x : L × L) :
    x ∈ scaledPairLayer P Q q ↔ x.1 ∈ P ∧ x.2 ∈ P ∧ x.1 - q • x.2 ∈ Q := Iff.rfl

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

noncomputable def residueIndexLower (a r v : ℤ) : ℤ :=
  ⌈((a : ℚ) - (v : ℚ)) / (r : ℚ)⌉

noncomputable def residueIndexLength (a b r v : ℤ) : ℕ :=
  (residueIndexLower b r v - residueIndexLower a r v).toNat

def residueAffineEmbedding (r v : ℤ) (hr : r ≠ 0) : ℤ ↪ ℤ where
  toFun k := v + r * k
  inj' _ _ h := mul_left_cancel₀ hr (add_left_cancel h)

theorem residueIndexInterval_eq (a b r v : ℤ) :
    Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v) =
      Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v) := by
  ext x
  simp only [Finset.mem_Ico, residueIndexLength]
  omega

theorem residueInterval_eq_map (a b r v : ℤ) (hr : 0 < r) :
    Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) =
      (Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v)).map
        (residueAffineEmbedding r v hr.ne') := by
  rw [Int.Ico_filter_modEq_eq, Int.Ico_filter_dvd_eq (a - v) (b - v) hr, Finset.map_map]
  simp only [Int.cast_sub]
  change (Finset.Ico (residueIndexLower a r v) (residueIndexLower b r v)).map _ = _
  rw [residueIndexInterval_eq]
  congr 1
  ext k
  change k * r + v = v + r * k
  ring

noncomputable def residueIntervalEquiv (a b r v : ℤ) (hr : 0 < r) :
    ↥(Finset.Ico (residueIndexLower a r v) (residueIndexLower a r v + residueIndexLength a b r v)) ≃
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := by
  let f : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v)) →
      ↥(Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)) := fun x =>
    ⟨v + r * x.val, by
      rw [residueInterval_eq_map a b r v hr]
      exact Finset.mem_map.mpr ⟨x.val, x.property, rfl⟩⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply Subtype.ext
    exact (residueAffineEmbedding r v hr.ne').injective (congrArg Subtype.val h)
  · intro y
    let yy : ℤ := y.val
    have hy : yy ∈ Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b) := y.property
    rw [residueInterval_eq_map a b r v hr] at hy
    obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp hy
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

@[simp] theorem residueIntervalEquiv_val (a b r v : ℤ) (hr : 0 < r)
    (x : ↥(Finset.Ico (residueIndexLower a r v)
      (residueIndexLower a r v + residueIndexLength a b r v))) :
    (residueIntervalEquiv a b r v hr x).val = v + r * x.val := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.BoxResiduePartition
namespace OAI

section

namespace Erdos3

noncomputable def integerIntervalEquivFin (a : ℤ) (N : ℕ) :
    ↥(Finset.Ico a (a + N)) ≃ Fin N where
  toFun x := ⟨(x.val - a).toNat, by have hx := Finset.mem_Ico.mp x.property; omega⟩
  invFun n := ⟨a + n.val, by simp only [Finset.mem_Ico]; omega⟩
  left_inv x := by
    apply Subtype.ext
    have hx := Finset.mem_Ico.mp x.property
    dsimp only
    omega
  right_inv n := by
    apply Fin.ext
    dsimp only
    omega

@[simp] theorem integerIntervalEquivFin_symm_val (a : ℤ) (N : ℕ) (n : Fin N) :
    ((integerIntervalEquivFin a N).symm n).val = a + n.val := rfl

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

abbrev IntegerResidueBox {I : Type*} (a b r v : I → ℤ) :=
  ∀ i, ↥(Finset.filter (fun x => x ≡ v i [ZMOD r i]) (Finset.Ico (a i) (b i)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PhysicalSubboxResidueSlice
namespace OAI

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def integerBox (T : ι → ℕ) : Finset (ι → ℤ) :=
  Fintype.piFinset (fun i ↦ Finset.Ico (0 : ℤ) (T i))

@[simp] theorem mem_integerBox (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ integerBox T ↔ ∀ i, 0 ≤ x i ∧ x i < T i := by
  simp [integerBox, Fintype.mem_piFinset]

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) : Finset (ι → ℤ) :=
  translateSupport a (integerBox T)

theorem mem_translatedIntegerBox (a : ι → ℤ) (T : ι → ℕ) (x : ι → ℤ) :
    x ∈ translatedIntegerBox a T ↔ ∀ i, a i ≤ x i ∧ x i < a i + T i := by
  rw [translatedIntegerBox, mem_translateSupport, mem_integerBox]
  apply forall_congr'
  intro i
  change (0 ≤ x i - a i ∧ x i - a i < T i) ↔ _
  omega

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def translatedIntegerBoxEquivPi {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) :
    ↥(translatedIntegerBox a N) ≃ ∀ i, ↥(Finset.Ico (a i) (a i + N i)) := by
  let e : ↥(translatedIntegerBox a N) ≃
      {x : I → ℤ // ∀ i, x i ∈ Finset.Ico (a i) (a i + N i)} :=
    Equiv.subtypeEquivRight (fun x => by simp only [mem_translatedIntegerBox, Finset.mem_Ico])
  exact e.trans Equiv.subtypePiEquivPi

@[simp] theorem translatedIntegerBoxEquivPi_val {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℤ) (N : I → ℕ) (x : ↥(translatedIntegerBox a N)) (i : I) :
    ((translatedIntegerBoxEquivPi a N x) i).val = x.val i := rfl

noncomputable def integerResidueBoxEquiv {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i) :
    ↥(translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
      (fun i => residueIndexLength (a i) (b i) (r i) (v i))) ≃ IntegerResidueBox a b r v :=
  (translatedIntegerBoxEquivPi _ _).trans
    (Equiv.piCongrRight fun i => residueIntervalEquiv (a i) (b i) (r i) (v i) (hr i))

@[simp] theorem integerResidueBoxEquiv_val {I : Type*} [Fintype I] [DecidableEq I]
    (a b r v : I → ℤ) (hr : ∀ i, 0 < r i)
    (x : ↥(translatedIntegerBox (fun i => residueIndexLower (a i) (r i) (v i))
      (fun i => residueIndexLength (a i) (b i) (r i) (v i)))) (i : I) :
    ((integerResidueBoxEquiv a b r v hr x) i).val = v i + r i * x.val i := rfl

end Erdos3

end

section

namespace Erdos3

noncomputable def physicalResidueCoordinateEquiv
    (lo hi a : ℤ) (M : ℕ) (hM : 0 < M) :
    Fin (residueIndexLength lo hi M a) ≃
      ↥(Finset.filter (fun x => x ≡ a [ZMOD (M : ℤ)]) (Finset.Ico lo hi)) :=
  (integerIntervalEquivFin (residueIndexLower lo M a)
    (residueIndexLength lo hi M a)).symm.trans
      (residueIntervalEquiv lo hi M a (Nat.cast_pos.mpr hM))

theorem physicalResidueCoordinateEquiv_val
    (lo hi a : ℤ) (M : ℕ) (hM : 0 < M)
    (j : Fin (residueIndexLength lo hi M a)) :
    (physicalResidueCoordinateEquiv lo hi a M hM j).val =
      a + M * (residueIndexLower lo M a + j.val) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialKernelValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def eval₂ (x : σ → S) : VectorPolynomial σ R V →ₗ[R] V :=
  TensorProduct.lift ((Algebra.lsmul R R V).toLinearMap.comp (MvPolynomial.aeval x).toLinearMap)

@[simp] theorem eval₂_tmul (x : σ → S) (p : MvPolynomial σ R) (v : V) :
    eval₂ x (p ⊗ₜ[R] v) = MvPolynomial.aeval x p • v := rfl

@[simp] theorem eval₂_monomial (x : σ → S) (α : σ →₀ ℕ) (v : V) :
    eval₂ x (monomial (R := R) α v) = (α.prod fun i n => x i ^ n) • v := by
  simp [monomial, MvPolynomial.aeval_monomial]

theorem eval₂_algebraMap (x : σ → R) (p : VectorPolynomial σ R V) :
    eval₂ (fun i => algebraMap R S (x i)) p = eval x p := by
  have heval (q : MvPolynomial σ R) :
      MvPolynomial.aeval (fun i => algebraMap R S (x i)) q =
        algebraMap R S (MvPolynomial.aeval x q) := by
    induction q using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [hp, hq]
    | mul_X p i hp => simp [hp]
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v => simp only [eval₂_tmul, eval_tmul, heval, IsScalarTower.algebraMap_smul]
  | add p q hp hq => simp only [map_add, hp, hq]

theorem coordinate_eval₂ (f : V →ₗ[S] S) (x : σ → S) (p : VectorPolynomial σ R V) :
    f (eval₂ x p) = MvPolynomial.eval x (coordinate f.toAddMonoidHom p) := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, coordinate_sum, coordinate_monomial,
    eval₂_monomial, MvPolynomial.eval_monomial, map_smul, smul_eq_mul, mul_comm]
  rfl

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators TensorProduct

variable {σ R V : Type*} [Fintype σ]
  [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def linearPolynomial : (σ → V) →ₗ[R] VectorPolynomial σ R V where
  toFun a := ∑ i, monomial (Finsupp.single i 1) (a i)
  map_add' a b := by
    simp only [Pi.add_apply, monomial, TensorProduct.tmul_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [Pi.smul_apply, monomial, TensorProduct.tmul_smul, Finset.smul_sum, RingHom.id_apply]

@[simp] theorem linearPolynomial_apply (a : σ → V) :
    linearPolynomial (R := R) a = ∑ i, monomial (Finsupp.single i 1) (a i) := rfl

theorem coefficients_linearPolynomial_of_ne (a : σ → V) (α : σ →₀ ℕ)
    (hα : ∀ i, Finsupp.single i 1 ≠ α) : coefficients (linearPolynomial (R := R) a) α = 0 := by
  rw [linearPolynomial_apply, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro i _
  rw [coefficients_monomial, Finsupp.single_eq_of_ne (Ne.symm (hα i))]

@[simp] theorem coefficients_linearPolynomial_zero (a : σ → V) :
    coefficients (linearPolynomial (R := R) a) 0 = 0 := by
  apply coefficients_linearPolynomial_of_ne
  intro i h
  have hi := congrArg (fun α : σ →₀ ℕ => α i) h
  simp only [Finsupp.single_eq_same, Finsupp.zero_apply, Nat.one_ne_zero] at hi

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]

@[simp] theorem lie_monomial (α β : σ →₀ ℕ) (a b : L) :
    ⁅monomial (R := R) α a, monomial (R := R) β b⁆ = monomial (R := R) (α + β) ⁅a, b⁆ := by
  simp only [monomial, LieAlgebra.ExtendScalars.bracket_tmul,
    MvPolynomial.monomial_mul, one_mul]

noncomputable def evalLie (x : σ → R) : VectorPolynomial σ R L →ₗ⁅R⁆ L where
  toLinearMap := eval x
  map_lie' {p q} := by
    change eval x ⁅p, q⁆ = ⁅eval x p, eval x q⁆
    induction p using TensorProduct.induction_on with
    | zero =>
      exact (congrArg _ (zero_lie (M := VectorPolynomial σ R L) q)).trans (by rw [map_zero, zero_lie])
    | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero =>
        exact (congrArg _ (lie_zero (L := VectorPolynomial σ R L) (a ⊗ₜ[R] v))).trans (by rw [map_zero, lie_zero])
      | tmul b w =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul, eval_tmul, map_mul,
          smul_lie, lie_smul, smul_smul, mul_comm]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

@[simp] theorem evalLie_apply (x : σ → R) (p : VectorPolynomial σ R L) :
    evalLie x p = eval x p := rfl

section Rational

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s = ⊥ := by
  have hpoly : LieModule.lowerCentralSeries (MvPolynomial σ ℚ)
      (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (VectorPolynomial σ ℚ L)
    (VectorPolynomial σ ℚ L) s : Set (VectorPolynomial σ ℚ L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int (MvPolynomial σ ℚ)
      (VectorPolynomial σ ℚ L) (VectorPolynomial σ ℚ L) s, hpoly]
  rfl

end Rational
end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedMultidegree
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def rationalLieInclusion : L →ₗ⁅ℚ⁆ (ℝ ⊗[ℚ] L) where
  toLinearMap := TensorProduct.mk ℚ ℝ L 1
  map_lie' {x y} := by simp [LieAlgebra.ExtendScalars.bracket_tmul]

@[simp]
theorem rationalLieInclusion_apply (x : L) : rationalLieInclusion x = (1 : ℝ) ⊗ₜ[ℚ] x := rfl

theorem rationalLieInclusion_coordinates (e : Basis ι ℚ L) (x : L) (i : ι) :
    (e.baseChange ℝ).repr (rationalLieInclusion x) i = (e.repr x i : ℝ) := by
  simp [Basis.baseChange_repr_tmul, Algebra.smul_def]

theorem realification_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥ := by
  have hreal : LieModule.lowerCentralSeries ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s : Set (ℝ ⊗[ℚ] L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int ℝ (ℝ ⊗[ℚ] L) (ℝ ⊗[ℚ] L) s, hreal]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RiemannianLipschitz
namespace OAI

section

namespace Erdos3

open Manifold MeasureTheory _root_.Set
open scoped Manifold ContDiff ENNReal

variable {E F H K M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace K N]
  [∀ x : M, ENorm (TangentSpace I x)] [∀ x : N, ENorm (TangentSpace J x)]

theorem pathELength_comp_le_of_mfderiv_norm_le {φ : M → N}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ ‖v‖ₑ)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_mono
  intro t
  exact (congrArg (fun v : TangentSpace J (φ (γ t)) => ‖v‖ₑ)
    (mfderiv_comp_apply t (hφ.mdifferentiableAt one_ne_zero)
      (hγ.mdifferentiableAt one_ne_zero) 1)).trans_le (hbound (γ t) _)

variable [∀ x : M, ENormSMulClass ℝ (TangentSpace I x)]
  [∀ x : N, ENormSMulClass ℝ (TangentSpace J x)]

theorem riemannianEDist_le_of_mfderiv_norm_le {φ : M → N}
    (hφ : ContMDiff I J 1 φ)
    (hbound : ∀ (x : M) (v : TangentSpace I x), ‖mfderiv I J φ x v‖ₑ ≤ ‖v‖ₑ)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ riemannianEDist I x y := by
  apply le_of_forall_gt
  intro r hr
  obtain ⟨γ, hγ0, hγ1, hγ, hlen, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hr zero_lt_one
  have hends : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 :=
    riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγ0])
      (by simp only [Function.comp_apply, hγ1]) zero_le_one
  exact (hends.trans (pathELength_comp_le_of_mfderiv_norm_le hφ hbound hγ 0 1)).trans_lt hlen

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RightCosetEDistance
namespace OAI

section

namespace Erdos3

open scoped ENNReal

variable {G : Type*} [Group G] [PseudoEMetricSpace G]

noncomputable def rightCosetEDist (Γ : Subgroup G) (x y : G) : ℝ≥0∞ :=
  ⨅ γ : Γ, edist x (y * γ)

theorem rightCosetEDist_le (Γ : Subgroup G) (x y : G) :
    rightCosetEDist Γ x y ≤ edist x y := by
  unfold rightCosetEDist
  exact iInf_le_of_le (1 : Γ) (by simp)

@[simp] theorem rightCosetEDist_self (Γ : Subgroup G) (x : G) : rightCosetEDist Γ x x = 0 :=
  le_antisymm ((rightCosetEDist_le Γ x x).trans_eq (edist_self x)) bot_le

variable [IsIsometricSMul Gᵐᵒᵖ G]

theorem rightCosetEDist_comm (Γ : Subgroup G) (x y : G) :
    rightCosetEDist Γ x y = rightCosetEDist Γ y x := by
  have h : ∀ a b : G, rightCosetEDist Γ a b ≤ rightCosetEDist Γ b a := by
    intro a b
    apply le_iInf
    intro γ
    apply (iInf_le (fun δ : Γ => edist a (b * δ)) γ⁻¹).trans_eq
    rw [← edist_mul_right a (b * (γ⁻¹ : Γ)) (γ : G)]
    simp only [Subgroup.coe_inv, inv_mul_cancel_right, edist_comm]
  exact le_antisymm (h x y) (h y x)

omit [IsIsometricSMul Gᵐᵒᵖ G] in
theorem rightCosetEDist_mul_right (Γ : Subgroup G) (x y : G) (δ : Γ) :
    rightCosetEDist Γ x (y * δ) = rightCosetEDist Γ x y := by
  apply le_antisymm
  · apply le_iInf
    intro γ
    apply (iInf_le (fun a : Γ => edist x (y * δ * a)) (δ⁻¹ * γ)).trans_eq
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, mul_inv_cancel_left]
  · apply le_iInf
    intro γ
    apply (iInf_le (fun a : Γ => edist x (y * a)) (δ * γ)).trans_eq
    simp only [Subgroup.coe_mul, mul_assoc]

theorem rightCosetEDist_mul_left (Γ : Subgroup G) (x y : G) (δ : Γ) :
    rightCosetEDist Γ (x * δ) y = rightCosetEDist Γ x y := by
  rw [rightCosetEDist_comm, rightCosetEDist_mul_right, rightCosetEDist_comm]

theorem rightCosetEDist_triangle (Γ : Subgroup G) (x y z : G) :
    rightCosetEDist Γ x z ≤ rightCosetEDist Γ x y + rightCosetEDist Γ y z := by
  apply ENNReal.le_iInf_add_iInf
  intro a b
  apply (iInf_le (fun γ : Γ => edist x (z * γ)) (b * a)).trans
  calc
    edist x (z * ↑(b * a)) ≤ edist x (y * a) + edist (y * a) (z * ↑(b * a)) :=
      edist_triangle _ _ _
    _ = edist x (y * a) + edist y (z * b) := by
      simp only [Subgroup.coe_mul, ← mul_assoc, edist_mul_right]

theorem rightCosetEDist_rel (Γ : Subgroup G) {x x' y y' : G}
    (hx : QuotientGroup.leftRel Γ x x') (hy : QuotientGroup.leftRel Γ y y') :
    rightCosetEDist Γ x y = rightCosetEDist Γ x' y' := by
  let a : Γ := ⟨x⁻¹ * x', QuotientGroup.leftRel_apply.mp hx⟩
  let b : Γ := ⟨y⁻¹ * y', QuotientGroup.leftRel_apply.mp hy⟩
  have ha : x * a = x' := by simp only [a, mul_inv_cancel_left]
  have hb : y * b = y' := by simp only [b, mul_inv_cancel_left]
  rw [← ha, ← hb, rightCosetEDist_mul_left, rightCosetEDist_mul_right]

noncomputable def quotientRightEDist (Γ : Subgroup G) : (G ⧸ Γ) → (G ⧸ Γ) → ℝ≥0∞ :=
  Quotient.lift₂ (rightCosetEDist Γ) (fun _ _ _ _ hx hy => rightCosetEDist_rel Γ hx hy)

@[simp] theorem quotientRightEDist_mk (Γ : Subgroup G) (x y : G) :
    quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) = rightCosetEDist Γ x y := rfl

@[simp] theorem quotientRightEDist_self (Γ : Subgroup G) (x : G ⧸ Γ) :
    quotientRightEDist Γ x x = 0 :=
  Quotient.inductionOn x (rightCosetEDist_self Γ)

theorem quotientRightEDist_comm (Γ : Subgroup G) (x y : G ⧸ Γ) :
    quotientRightEDist Γ x y = quotientRightEDist Γ y x :=
  Quotient.inductionOn₂ x y (rightCosetEDist_comm Γ)

theorem quotientRightEDist_triangle (Γ : Subgroup G) (x y z : G ⧸ Γ) :
    quotientRightEDist Γ x z ≤ quotientRightEDist Γ x y + quotientRightEDist Γ y z :=
  Quotient.inductionOn₃ x y z (rightCosetEDist_triangle Γ)

theorem quotientRightEDist_mk_le (Γ : Subgroup G) (x y : G) :
    quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) ≤ edist x y :=
  rightCosetEDist_le Γ x y

omit [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] in
theorem quotient_mk_mul_mem (Γ : Subgroup G) (x : G) (γ : Γ) :
    (QuotientGroup.mk (x * γ) : G ⧸ Γ) = QuotientGroup.mk x := by
  apply Eq.symm
  apply QuotientGroup.eq.mpr
  simpa only [inv_mul_cancel_left] using γ.property

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RightCosetMetricMap
namespace OAI

section

namespace Erdos3

open _root_.Set
open scoped ENNReal Topology

variable {G : Type*} [Group G] [PseudoEMetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G]

theorem quotientRightEDist_image_eball (Γ : Subgroup G) (x : G) (r : ℝ≥0∞) :
    (QuotientGroup.mk : G → G ⧸ Γ) '' Metric.eball x r =
      {y | quotientRightEDist Γ (QuotientGroup.mk x) y < r} := by
  ext y
  induction y using Quotient.inductionOn with
  | h y =>
    constructor
    · rintro ⟨w, hw, hwq⟩
      change (QuotientGroup.mk w : G ⧸ Γ) = QuotientGroup.mk y at hwq
      change quotientRightEDist Γ (QuotientGroup.mk x) (QuotientGroup.mk y) < r
      rw [← hwq]
      apply (quotientRightEDist_mk_le Γ x w).trans_lt
      simpa only [Metric.mem_eball, edist_comm] using hw
    · intro hy
      change (⨅ γ : Γ, edist x (y * γ)) < r at hy
      obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hy
      refine ⟨y * γ, ?_, quotient_mk_mul_mem Γ y γ⟩
      simpa only [Metric.mem_eball, edist_comm] using hγ

variable [IsTopologicalGroup G]

theorem quotientRightEDist_nhds_basis (Γ : Subgroup G) (x : G ⧸ Γ) :
    (𝓝 x).HasBasis (fun r : ℝ≥0∞ => 0 < r) (fun r => {y | quotientRightEDist Γ x y < r}) := by
  induction x using Quotient.inductionOn with
  | h x =>
    rw [QuotientGroup.nhds_eq]
    simpa only [quotientRightEDist_image_eball] using
      (Metric.nhds_basis_eball (x := x)).map (QuotientGroup.mk : G → G ⧸ Γ)

@[instance_reducible]
noncomputable def rightCosetPseudoEMetricSpace (Γ : Subgroup G) : PseudoEMetricSpace (G ⧸ Γ) :=
  PseudoEMetricSpace.ofEDistOfTopology (quotientRightEDist Γ)
    (quotientRightEDist_self Γ) (quotientRightEDist_comm Γ) (quotientRightEDist_triangle Γ)
    (quotientRightEDist_nhds_basis Γ)

@[instance_reducible]
noncomputable def rightCosetEMetricSpace (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    EMetricSpace (G ⧸ Γ) := by
  letI := rightCosetPseudoEMetricSpace Γ
  letI := hΓ
  exact EMetricSpace.ofT0PseudoEMetricSpace (G ⧸ Γ)

end Erdos3

namespace Erdos3

open _root_.Set

variable {G : Type*} [Group G] [MetricSpace G] [IsIsometricSMul Gᵐᵒᵖ G] [IsTopologicalGroup G]

@[instance_reducible]
noncomputable def rightCosetMetricSpace (Γ : Subgroup G) (hΓ : IsClosed (Γ : Set G)) :
    MetricSpace (G ⧸ Γ) := by
  letI := rightCosetEMetricSpace Γ hΓ
  apply EMetricSpace.toMetricSpace
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      exact ne_top_of_le_ne_top (edist_ne_top x y) (quotientRightEDist_mk_le Γ x y)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateSmooth
namespace OAI

section

namespace Erdos3

open Module
open scoped ContDiff

variable {ι X E L : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [LieRing L] [LieAlgebra ℝ L] {n : ℕ∞ω}

theorem lie_coordinate_formula_real (e : Basis ι ℝ L) (a b : L) (k : ι) :
    e.repr ⁅a, b⁆ k =
      ∑ i, ∑ j, e.repr a i * e.repr b j * e.repr ⁅e i, e j⁆ k := by
  classical
  conv_lhs => rw [← e.sum_repr a, ← e.sum_repr b]
  simp only [sum_lie, lie_sum, smul_lie, lie_smul, map_sum, map_smul,
    Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem contDiff_lie_coordinates (e : Basis ι ℝ L) (f g : E → L)
    (hf : ∀ i, ContDiff ℝ n (fun x => e.repr (f x) i))
    (hg : ∀ i, ContDiff ℝ n (fun x => e.repr (g x) i)) (k : ι) :
    ContDiff ℝ n (fun x => e.repr ⁅f x, g x⁆ k) := by
  have heq : (fun x => e.repr ⁅f x, g x⁆ k) =
      (fun x => ∑ i, ∑ j, e.repr (f x) i * e.repr (g x) j * e.repr ⁅e i, e j⁆ k) :=
    funext (fun x => lie_coordinate_formula_real e (f x) (g x) k)
  rw [heq]
  exact ContDiff.sum (fun i _ => ContDiff.sum (fun j _ =>
    ((hf i).mul (hg j)).mul contDiff_const))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

open scoped ContDiff

noncomputable def coordinateDotForm {ι : Type*} [Fintype ι] :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
    (ContinuousLinearMap.proj i) (ContinuousLinearMap.proj i)

@[simp] theorem coordinateDotForm_apply {ι : Type*} [Fintype ι] (v w : ι → ℝ) :
    coordinateDotForm v w = ∑ i, v i * w i := by
  simp [coordinateDotForm]

theorem contDiff_bilinearComp_self {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {n : ℕ∞ω}
    (B : F →L[ℝ] F →L[ℝ] ℝ) (T : E → F →L[ℝ] F) (hT : ContDiff ℝ n T) :
    ContDiff ℝ n (fun x => B.bilinearComp (T x) (T x)) := by
  have hflip : ContDiff ℝ n (fun A : F →L[ℝ] F →L[ℝ] ℝ => A.flip) :=
    (show IsBoundedLinearMap ℝ (fun A : F →L[ℝ] F →L[ℝ] ℝ => A.flip) from
      { map_add := ContinuousLinearMap.flip_add
        map_smul := ContinuousLinearMap.flip_smul
        bound := ⟨1, zero_lt_one, fun A => by simp only [one_mul, ContinuousLinearMap.opNorm_flip, le_refl]⟩ }).contDiff
  exact hflip.comp ((hflip.comp (contDiff_const.clm_comp hT)).clm_comp hT)

end Erdos3

end

section

namespace Erdos3

open _root_.Set
open scoped ENNReal Topology

theorem edist_ne_top_of_preconnected {X : Type*} [PseudoEMetricSpace X] [PreconnectedSpace X]
    (x y : X) : edist x y ≠ ⊤ := by
  have ho : IsOpen (Metric.eball x ⊤)ᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    apply Filter.mem_of_superset (Metric.eball_mem_nhds z zero_lt_one)
    intro w hw hfin
    apply hz
    change edist z x < ⊤
    have hzw : edist z w < ⊤ := by
      have hw' : edist w z < 1 := hw
      rw [edist_comm]
      exact hw'.trans (by simp)
    exact (edist_triangle z w x).trans_lt (ENNReal.add_lt_top.mpr ⟨hzw, hfin⟩)
  have hall : Metric.eball x ⊤ = univ :=
    (show IsClopen (Metric.eball x ⊤) from ⟨isOpen_compl_iff.mp ho, Metric.isOpen_eball⟩).eq_univ
      ⟨x, by simp⟩
  have hy : y ∈ Metric.eball x ⊤ := by rw [hall]; trivial
  have hxy : edist y x < ⊤ := hy
  exact (by simpa only [edist_comm] using hxy.ne)

end Erdos3

end

section

namespace Erdos3

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]

def realLieHomToRat (φ : L →ₗ⁅ℝ⁆ M) : L →ₗ⁅ℚ⁆ M where
  toLinearMap := φ.toLinearMap.restrictScalars ℚ
  map_lie' {x y} := φ.map_lie x y

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def realificationLieHom (φ : L →ₗ⁅ℚ⁆ M) :
    (ℝ ⊗[ℚ] L) →ₗ⁅ℝ⁆ (ℝ ⊗[ℚ] M) where
  toLinearMap := φ.toLinearMap.baseChange ℝ
  map_lie' {x y} := (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) φ).map_lie x y

@[simp] theorem realificationLieHom_tmul (φ : L →ₗ⁅ℚ⁆ M) (a : ℝ) (x : L) :
    realificationLieHom φ (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] φ x := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def supportedSubmoduleBasis (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) : Basis S K P := by
  let c := Basis.span (b.linearIndependent.comp (fun i : S => (i : ι)) Subtype.val_injective)
  have he : Submodule.span K (Set.range (fun i : S => b i)) = P := by
    rw [hP]
    congr 1
    ext x
    simp
  exact c.map (LinearEquiv.ofEq _ _ he)

@[simp] theorem supportedSubmoduleBasis_coe (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (i : S) :
    (supportedSubmoduleBasis b P S hP i : V) = b i := by
  simp [supportedSubmoduleBasis, Basis.map_apply]

theorem supportedSubmoduleBasis_repr (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (x : P) (i : S) :
    (supportedSubmoduleBasis b P S hP).repr x i = b.repr (x : V) i := by
  classical
  let c := supportedSubmoduleBasis b P S hP
  have he : c.coord i = (b.coord i).comp P.subtype := by
    apply c.ext
    intro j
    simp [c, Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  change c.coord i x = b.coord i (x : V)
  rw [he]
  rfl

theorem basis_mem_span_image_iff (b : Basis ι K V) (S : Set ι) (x : V) :
    x ∈ Submodule.span K (b '' S) ↔ ∀ i, i ∉ S → b.repr x i = 0 := by
  classical
  rw [b.mem_span_image]
  constructor
  · intro h i hi
    by_contra hne
    exact hi (h (Finsupp.mem_support_iff.mpr hne))
  · intro h i hi
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hi) (h i hnot)

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def basisCoordinateProjection (b : Basis ι K V) (S : Set ι) : V →ₗ[K] V := by
  classical
  exact
    { toFun := fun x => b.repr.symm ((b.repr x).filter (· ∈ S))
      map_add' := fun x y => by simp only [map_add, Finsupp.filter_add]
      map_smul' := fun c x => by simp only [map_smul, Finsupp.filter_smul, RingHom.id_apply] }

theorem basisCoordinateProjection_repr (b : Basis ι K V) (S : Set ι)
    [DecidablePred (· ∈ S)] (x : V) (i : ι) :
    b.repr (basisCoordinateProjection b S x) i = if i ∈ S then b.repr x i else 0 := by
  classical
  by_cases hi : i ∈ S <;>
    simp [basisCoordinateProjection, hi]

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem basis_isCompl_span_compl (b : Basis ι K V) (S : Set ι) :
    IsCompl (Submodule.span K (b '' S)) (Submodule.span K (b '' Sᶜ)) := by
  apply b.linearIndependent.isCompl_span_image
  · exact b.span_eq
  · exact isCompl_compl

noncomputable def supportedQuotientBasis (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) : Basis {i // i ∉ S} K (V ⧸ P) :=
  (supportedSubmoduleBasis b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl).map
    (P.quotientEquivOfIsCompl (Submodule.span K (b '' Sᶜ))
      (by rw [hP]; exact basis_isCompl_span_compl b S)).symm

@[simp] theorem supportedQuotientBasis_apply (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (i : {i // i ∉ S}) :
    supportedQuotientBasis b P S hP i = P.mkQ (b i) := by
  change P.mkQ ((supportedSubmoduleBasis b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl) i : V) = _
  exact congrArg P.mkQ (supportedSubmoduleBasis_coe b (Submodule.span K (b '' Sᶜ)) Sᶜ rfl i)

theorem supportedQuotientBasis_repr_mk (b : Basis ι K V) (P : Submodule K V) (S : Set ι)
    (hP : P = Submodule.span K (b '' S)) (x : V) (i : {i // i ∉ S}) :
    (supportedQuotientBasis b P S hP).repr (P.mkQ x) i = b.repr x i := by
  classical
  have hker : P ≤ LinearMap.ker (b.coord i) := by
    intro y hy
    rw [hP, basis_mem_span_image_iff] at hy
    exact hy i i.property
  let f := P.liftQ (b.coord i) hker
  have hf : (supportedQuotientBasis b P S hP).coord i = f := by
    apply (supportedQuotientBasis b P S hP).ext
    intro j
    change (supportedQuotientBasis b P S hP).repr (supportedQuotientBasis b P S hP j) i = _
    rw [Basis.repr_self]
    simp [f, Basis.coord_apply, Finsupp.single_apply, Subtype.ext_iff]
  change (supportedQuotientBasis b P S hP).coord i (P.mkQ x) = _
  rw [hf]
  rfl

end Erdos3

end

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

noncomputable def basisGradeProjection (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) : V →ₗ[K] V :=
  basisCoordinateProjection b {i | w i = j}

noncomputable def basisBelowProjection (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) : V →ₗ[K] V :=
  basisCoordinateProjection b {i | w i < j}

@[simp] theorem basisBelowProjection_repr (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) (i : ι) :
    b.repr (basisBelowProjection b w j x) i = if w i < j then b.repr x i else 0 :=
  basisCoordinateProjection_repr b {i | w i < j} x i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

noncomputable def unitMonomial (n : ℕ) : Unit →₀ ℕ := Finsupp.single () n

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedLoweringGroup
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

theorem weightedSupportLT_mono {w : σ → ℕ} {d e : ℕ} {p : MvPolynomial σ R}
    (hde : d ≤ e) (hp : p ∈ weightedSupportLT w d) : p ∈ weightedSupportLT w e :=
  fun _ ha => lt_of_lt_of_le (hp ha) hde

theorem weightedSupportLT_zero_eq {w : σ → ℕ} {p : MvPolynomial σ R}
    (hp : p ∈ weightedSupportLT w 0) : p = 0 := by
  apply MvPolynomial.eq_zero_iff.mpr
  intro a
  by_contra ha
  exact Nat.not_lt_zero _ (hp (MvPolynomial.mem_support_iff.mpr ha))

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialHomDifference
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) : Module.End R (MvPolynomial σ R) :=
  F.toLinearMap - LinearMap.id

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialCoefficientGridDenominator
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {U B R : Type*} [CommRing R]

noncomputable def majorShiftCoordinates (e : B → MvPolynomial U R) :
    B → MvPolynomial (U ⊕ B) R :=
  fun b => X (Sum.inr b) + rename Sum.inl (e b)

noncomputable def majorShiftSubstitution (e : B → MvPolynomial U R) :
    U ⊕ B → MvPolynomial (U ⊕ B) R :=
  Sum.elim (fun u => X (Sum.inl u)) (majorShiftCoordinates e)

@[simp] theorem majorShiftCoordinates_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R)
    (u : U → T) (b : B → T) (j : B) :
    eval₂ φ (Sum.elim u b) (majorShiftCoordinates e j) =
      b j + eval₂ φ u (e j) := by
  simp [majorShiftCoordinates, eval₂_rename, Function.comp_def]

@[simp] theorem majorShiftSubstitution_eval₂ {T : Type*} [CommRing T]
    (φ : R →+* T) (e : B → MvPolynomial U R)
    (u : U → T) (b : B → T) (j : U ⊕ B) :
    eval₂ φ (Sum.elim u b) (majorShiftSubstitution e j) =
      Sum.elim u (fun i => b i + eval₂ φ u (e i)) j := by
  cases j <;> simp [majorShiftSubstitution]

@[simp] theorem majorShiftCoordinates_eval (e : B → MvPolynomial U R)
    (u : U → R) (b : B → R) (j : B) :
    eval (Sum.elim u b) (majorShiftCoordinates e j) = b j + eval u (e j) := by
  simp [majorShiftCoordinates, eval_rename, Function.comp_def]

@[simp] theorem majorShiftSubstitution_eval (e : B → MvPolynomial U R)
    (u : U → R) (b : B → R) (j : U ⊕ B) :
    eval (Sum.elim u b) (majorShiftSubstitution e j) =
      Sum.elim u (fun i => b i + eval u (e i)) j := by
  cases j <;> simp [majorShiftSubstitution]

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {σ J R : Type*} [Fintype J] [CommRing R] [Module R ℝ]

@[simp] theorem coefficients_ofCoordinates_basisFun
    (Q : J → MvPolynomial σ ℝ) (α : σ →₀ ℕ) (j : J) :
    coefficients (ofCoordinates (R := R) (Pi.basisFun ℝ J) Q) α j =
      (Q j).coeff α := by
  have h := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (coordinate_ofCoordinates (R := R) (Pi.basisFun ℝ J) Q j)
  simpa only [coeff_coordinate, LinearMap.toAddMonoidHom_coe,
    Module.Basis.coord_apply, Pi.basisFun_repr] using h

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.WeightedSupportDropRename
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def weightedSupportDrop (w : σ → ℕ) (n r : ℕ) : Submodule R (MvPolynomial σ R) :=
  MvPolynomial.restrictSupport R {a | Finsupp.weight w a + r ≤ n}

theorem mem_weightedSupportDrop_iff (w : σ → ℕ) (n r : ℕ) (P : MvPolynomial σ R) :
    P ∈ weightedSupportDrop w n r ↔ ∀ a ∈ P.support, Finsupp.weight w a + r ≤ n := Iff.rfl

theorem weightedSupportDrop_antitone {w : σ → ℕ} {n r s : ℕ} {P : MvPolynomial σ R}
    (hrs : r ≤ s) (hP : P ∈ weightedSupportDrop w n s) : P ∈ weightedSupportDrop w n r := by
  intro a ha
  change Finsupp.weight w a + r ≤ n
  exact (Nat.add_le_add_left hrs _).trans (hP ha)

theorem weightedSupportDrop_eq_zero {w : σ → ℕ} {n r : ℕ} {P : MvPolynomial σ R}
    (hnr : n < r) (hP : P ∈ weightedSupportDrop w n r) : P = 0 := by
  apply MvPolynomial.eq_zero_iff.mpr
  intro a
  by_contra ha
  have h : Finsupp.weight w a + r ≤ n := hP (MvPolynomial.mem_support_iff.mpr ha)
  omega

theorem weightedSupportDrop_mul {w : σ → ℕ} {d e r s : ℕ} {P Q : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w d r) (hQ : Q ∈ weightedSupportDrop w e s) :
    P * Q ∈ weightedSupportDrop w (d + e) (r + s) := by
  classical
  intro a ha
  obtain ⟨b, hb, c, hc, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q ha)
  have h1 : Finsupp.weight w b + r ≤ d := hP hb
  have h2 : Finsupp.weight w c + s ≤ e := hQ hc
  change Finsupp.weight w (b + c) + (r + s) ≤ d + e
  rw [map_add]
  omega

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem weightedSupportDrop_rename {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → τ) (hf : ∀ i, v (f i) = w i)
    {n r : ℕ} {P : MvPolynomial σ R}
    (hP : P ∈ weightedSupportDrop w n r) :
    rename f P ∈ weightedSupportDrop v n r := by
  classical
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  have hweight : Finsupp.weight v (Finsupp.mapDomain f b) = Finsupp.weight w b := by
    change Finsupp.linearCombination ℕ v (Finsupp.mapDomain f b) =
      Finsupp.linearCombination ℕ w b
    rw [Finsupp.linearCombination_mapDomain]
    congr 2
    exact funext hf
  change Finsupp.weight v (Finsupp.mapDomain f b) + r ≤ n
  rw [hweight]
  exact hP hb

end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

@[simp] theorem scalarDirectionalDerivative_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

@[simp] theorem scalarDirectionalDerivative_single [DecidableEq σ] (i : σ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (Pi.single i 1) P = pderiv i P := by
  simp [scalarDirectionalDerivative_apply, Pi.single_apply]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

@[simp] theorem scalarDirectionalDerivative_neg (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (-x) P = -scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.neg_apply, neg_smul,
    Finset.sum_neg_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualLieAlgebra
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev DualLieAlgebra (L : Type*) [LieRing L] [LieAlgebra ℚ L] := DualNumber ℚ ⊗[ℚ] L

noncomputable def dualBaseLinear : DualLieAlgebra L →ₗ[ℚ] L :=
  (TensorProduct.lid ℚ L).toLinearMap.comp
    ((TrivSqZeroExt.fstHom ℚ ℚ ℚ).toLinearMap.rTensor L)

noncomputable def dualTangentLinear : DualLieAlgebra L →ₗ[ℚ] L :=
  (TensorProduct.lid ℚ L).toLinearMap.comp ((TrivSqZeroExt.sndHom ℚ ℚ).rTensor L)

@[simp] theorem dualBaseLinear_tmul (r : DualNumber ℚ) (x : L) :
    dualBaseLinear (r ⊗ₜ[ℚ] x) = r.fst • x := rfl

@[simp] theorem dualTangentLinear_tmul (r : DualNumber ℚ) (x : L) :
    dualTangentLinear (r ⊗ₜ[ℚ] x) = r.snd • x := rfl

noncomputable def dualConstantLie : L →ₗ⁅ℚ⁆ DualLieAlgebra L where
  toLinearMap := TensorProduct.mk ℚ (DualNumber ℚ) L 1
  map_lie' {x y} := by simp [LieAlgebra.ExtendScalars.bracket_tmul]

noncomputable def dualInfinitesimal : L →ₗ[ℚ] DualLieAlgebra L :=
  TensorProduct.mk ℚ (DualNumber ℚ) L DualNumber.eps

@[simp] theorem dualBaseLinear_constant (x : L) : dualBaseLinear (dualConstantLie x) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

@[simp] theorem dualTangentLinear_constant (x : L) : dualTangentLinear (dualConstantLie x) = 0 := by
  change (0 : ℚ) • x = 0
  exact zero_smul ℚ x

@[simp] theorem dualBaseLinear_infinitesimal (x : L) : dualBaseLinear (dualInfinitesimal x) = 0 := by
  change (0 : ℚ) • x = 0
  exact zero_smul ℚ x

@[simp] theorem dualTangentLinear_infinitesimal (x : L) : dualTangentLinear (dualInfinitesimal x) = x := by
  change (1 : ℚ) • x = x
  exact one_smul ℚ x

theorem dualInfinitesimal_injective : Function.Injective (dualInfinitesimal (L := L)) := by
  intro x y h
  simpa only [dualTangentLinear_infinitesimal] using congrArg dualTangentLinear h

theorem dualLie_decomposition (z : DualLieAlgebra L) :
    z = dualConstantLie (dualBaseLinear z) + dualInfinitesimal (dualTangentLinear z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    have hr : r = r.fst • (1 : DualNumber ℚ) + r.snd • DualNumber.eps := by
      ext <;> simp
    change r ⊗ₜ[ℚ] x = (1 : DualNumber ℚ) ⊗ₜ[ℚ] (r.fst • x) +
      DualNumber.eps ⊗ₜ[ℚ] (r.snd • x)
    calc
      _ = (r.fst • (1 : DualNumber ℚ) + r.snd • DualNumber.eps) ⊗ₜ[ℚ] x :=
        congrArg (fun a : DualNumber ℚ => a ⊗ₜ[ℚ] x) hr
      _ = _ := by rw [TensorProduct.add_tmul]; simp only [TensorProduct.smul_tmul, TensorProduct.tmul_smul]
  | add x y hx hy =>
    calc
      _ = (dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x)) +
          (dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y)) :=
        congrArg₂ (· + ·) hx hy
      _ = _ := by simp only [map_add]; abel

theorem dualBaseLinear_lie (x y : DualLieAlgebra L) :
    dualBaseLinear ⁅x, y⁆ = ⁅dualBaseLinear x, dualBaseLinear y⁆ := by
  induction x using TensorProduct.induction_on with
  | zero =>
    rw [zero_lie (L := DualLieAlgebra L) (M := DualLieAlgebra L)]
    simp
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero =>
      rw [lie_zero (L := DualLieAlgebra L) (M := DualLieAlgebra L)]
      simp
    | tmul q y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, dualBaseLinear_tmul,
        TrivSqZeroExt.fst_mul, smul_lie, lie_smul, smul_smul, mul_comm]
    | add y z hy hz =>
      rw [LieRing.lie_add (r ⊗ₜ[ℚ] x) y z, map_add, hy, hz, map_add, LieRing.lie_add]
  | add x z hx hz => rw [LieRing.add_lie x z y, map_add, hx, hz, map_add, LieRing.add_lie]

noncomputable def dualBaseLie : DualLieAlgebra L →ₗ⁅ℚ⁆ L where
  toLinearMap := dualBaseLinear
  map_lie' {x y} := dualBaseLinear_lie x y

theorem dualInfinitesimal_lie (x y : L) : ⁅dualInfinitesimal x, dualInfinitesimal y⁆ = 0 := by
  change ⁅DualNumber.eps ⊗ₜ[ℚ] x, DualNumber.eps ⊗ₜ[ℚ] y⁆ = 0
  rw [LieAlgebra.ExtendScalars.bracket_tmul, DualNumber.eps_mul_eps, TensorProduct.zero_tmul]

theorem dualLie_lowerCentralSeries_eq_bot {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (DualLieAlgebra L) (DualLieAlgebra L) s = ⊥ := by
  have hdual : LieModule.lowerCentralSeries (DualNumber ℚ) (DualLieAlgebra L) (DualLieAlgebra L) s = ⊥ := by
    rw [LieSubmodule.lowerCentralSeries_tensor_eq_baseChange, hnil, LieSubmodule.baseChange_bot]
  apply SetLike.coe_injective
  change (LieModule.lowerCentralSeries ℚ (DualLieAlgebra L) (DualLieAlgebra L) s : Set (DualLieAlgebra L)) = {0}
  rw [LieModule.coe_lowerCentralSeries_eq_int,
    ← LieModule.coe_lowerCentralSeries_eq_int (DualNumber ℚ) (DualLieAlgebra L) (DualLieAlgebra L) s,
    hdual]
  rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualIdealSteps
namespace OAI


namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

variable (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hT in
theorem dualIdealMorphism_left {x y : L} (hx : x ∈ I) : T ⁅x, y⁆ = ⁅T x, B y⁆ := by
  calc
    T ⁅x, y⁆ = T (-⁅y, x⁆) := congrArg T (lie_skew x y).symm
    _ = -⁅B y, T x⁆ := by rw [map_neg, hT y x hx]
    _ = ⁅T x, B y⁆ := lie_skew _ _

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

def lieHomOfLinearMap {A B : Type*} [LieRing A] [LieAlgebra ℚ A]
    [LieRing B] [LieAlgebra ℚ B] (g : A →ₗ[ℚ] B)
    (hg : ∀ x y, g ⁅x, y⁆ = ⁅g x, g y⁆) : A →ₗ⁅ℚ⁆ B :=
  ⟨g, fun {x y} => hg x y⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialDerivationDrop (w : σ → ℕ) (k : ℕ) :
    Submodule R (Derivation R (MvPolynomial σ R) (MvPolynomial σ R)) where
  carrier := {D | ∀ i, D (X i) ∈ weightedSupportDrop w (w i) k}
  zero_mem' := by
    intro i
    exact Submodule.zero_mem _
  add_mem' := by
    intro D E hD hE i
    exact (weightedSupportDrop w (w i) k).add_mem (hD i) (hE i)
  smul_mem' := by
    intro c D hD i
    exact (weightedSupportDrop w (w i) k).smul_mem c (hD i)

theorem polynomialDerivationDrop_antitone (w : σ → ℕ) :
    Antitone (polynomialDerivationDrop (R := R) w) := by
  intro a b hab D hD i
  exact weightedSupportDrop_antitone hab (hD i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedTranslationShearExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ : Type*} [Fintype σ]

theorem scalarDirectionalDerivative_direction_add (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (x + z) P =
      scalarDirectionalDerivative x P + scalarDirectionalDerivative z P := by
  simp only [scalarDirectionalDerivative_apply, Pi.add_apply, add_smul, Finset.sum_add_distrib]

theorem scalarDirectionalDerivative_direction_smul (r : ℚ) (x : σ → ℚ)
    (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (r • x) P = r • scalarDirectionalDerivative x P := by
  simp only [scalarDirectionalDerivative_apply, Pi.smul_apply, smul_eq_mul, smul_smul, Finset.smul_sum]

theorem scalarDirectionalDerivative_direction_zero (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative (0 : σ → ℚ) P = 0 := by
  simp [scalarDirectionalDerivative_apply]

theorem scalarDirectionalDerivative_commute (x z : σ → ℚ) (P : MvPolynomial σ ℚ) :
    scalarDirectionalDerivative x (scalarDirectionalDerivative z P) =
      scalarDirectionalDerivative z (scalarDirectionalDerivative x P) := by
  have h : ⁅scalarDirectionalDerivative x, scalarDirectionalDerivative z⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro i
    simp only [Derivation.commutator_apply, scalarDirectionalDerivative_X,
      scalarDirectionalDerivative_C, sub_self, Derivation.zero_apply]
  have hh := congrArg (fun D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ) => D P) h
  exact sub_eq_zero.mp hh

@[ext] structure PolynomialTranslationLie (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationLie

noncomputable def toProd : PolynomialTranslationLie σ ≃ (σ → ℚ) × MvPolynomial σ ℚ where
  toFun x := (x.base, x.polynomial)
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance instAddCommGroup : AddCommGroup (PolynomialTranslationLie σ) := toProd.addCommGroup
noncomputable instance instModuleRat : Module ℚ (PolynomialTranslationLie σ) :=
  { toProd with map_add' _ _ := rfl : PolynomialTranslationLie σ ≃+ (σ → ℚ) × MvPolynomial σ ℚ }.module ℚ

omit [Fintype σ] in
@[simp] theorem base_zero : (0 : PolynomialTranslationLie σ).base = 0 := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_zero : (0 : PolynomialTranslationLie σ).polynomial = 0 := rfl
omit [Fintype σ] in
@[simp] theorem base_add (x y : PolynomialTranslationLie σ) : (x+y).base = x.base+y.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_add (x y : PolynomialTranslationLie σ) : (x+y).polynomial = x.polynomial+y.polynomial := rfl
omit [Fintype σ] in
@[simp] theorem base_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).base = r • x.base := rfl
omit [Fintype σ] in
@[simp] theorem polynomial_smul (r : ℚ) (x : PolynomialTranslationLie σ) : (r • x).polynomial = r • x.polynomial := rfl

noncomputable instance instBracket : Bracket (PolynomialTranslationLie σ) (PolynomialTranslationLie σ) where
  bracket x y := ⟨0, scalarDirectionalDerivative x.base y.polynomial -
    scalarDirectionalDerivative y.base x.polynomial⟩

@[simp] theorem base_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.base = 0 := rfl
@[simp] theorem polynomial_lie (x y : PolynomialTranslationLie σ) : ⁅x,y⁆.polynomial =
    scalarDirectionalDerivative x.base y.polynomial - scalarDirectionalDerivative y.base x.polynomial := rfl

noncomputable instance instLieRing : LieRing (PolynomialTranslationLie σ) where
  add_lie x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_add x y z := by
    ext <;> simp [scalarDirectionalDerivative_direction_add]; abel
  lie_self x := by ext <;> simp
  leibniz_lie x y z := by
    ext
    · simp
    · simp only [polynomial_lie, base_lie, polynomial_add, map_sub,
        scalarDirectionalDerivative_direction_zero, sub_zero, zero_sub]
      rw [scalarDirectionalDerivative_commute x.base y.base,
        scalarDirectionalDerivative_commute x.base z.base,
        scalarDirectionalDerivative_commute y.base z.base]
      abel_nf

noncomputable instance instLieAlgebraRat : LieAlgebra ℚ (PolynomialTranslationLie σ) where
  lie_smul r x y := by
    ext <;> simp [scalarDirectionalDerivative_direction_smul, smul_sub]

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

namespace PolynomialTranslationLie

noncomputable def weightedLayer (w : σ → ℕ) (d k : ℕ) : Submodule ℚ (PolynomialTranslationLie σ) where
  carrier := {x | (∀ i, w i < k → x.base i = 0) ∧
    x.polynomial ∈ weightedSupportDrop w d k}
  zero_mem' := ⟨by simp, Submodule.zero_mem _⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨fun i hi => by simp [hx.1 i hi, hy.1 i hi],
      Submodule.add_mem _ hx.2 hy.2⟩
  smul_mem' := by
    intro r x hx
    exact ⟨fun i hi => by simp [hx.1 i hi], Submodule.smul_mem _ r hx.2⟩

omit [Fintype σ] in
theorem weightedLayer_antitone (w : σ → ℕ) (d : ℕ) : Antitone (weightedLayer w d) := by
  intro i j hij x hx
  exact ⟨fun a ha => hx.1 a (ha.trans_le hij), weightedSupportDrop_antitone hij hx.2⟩

omit [Fintype σ] in
theorem weightedLayer_terminal (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    weightedLayer w d (d+1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply PolynomialTranslationLie.ext
  · funext i
    exact hx.1 i (Nat.lt_succ_of_le (hw i))
  · exact weightedSupportDrop_eq_zero (Nat.lt_succ_self d) hx.2

end PolynomialTranslationLie
end Erdos3

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial

variable {σ : Type*} [Fintype σ]

def shearWeight (w : σ → ℕ) (d : ℕ) : σ ⊕ Unit → ℕ := Sum.elim w (fun _ => d)

end Erdos3.PolynomialTranslationLie

end

section

namespace Erdos3.PolynomialTranslationLie

open _root_.MvPolynomial
open scoped TensorProduct

variable {σ : Type*} [Fintype σ]

omit [Fintype σ] in
theorem shearWeight_le (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    ∀ i, shearWeight w d i ≤ d := by
  intro i
  cases i with
  | inl i => exact hw i
  | inr _ => exact le_rfl

end Erdos3.PolynomialTranslationLie

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SelectedResidueApproximation
namespace OAI

section

namespace Erdos3

abbrev ColumnResiduePattern (K I : Type*) (modulus : I → ℕ) :=
  ∀ z : K × I, ZMod (modulus z.2)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

section General

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] {N : Type*} [LieRing N] [LieAlgebra R N]

noncomputable def lieTensorLeftComm :
    (A ⊗[R] (B ⊗[R] N)) ≃ₗ⁅R⁆ (B ⊗[R] (A ⊗[R] N)) :=
  { TensorProduct.leftComm R A B N with
  map_lie' {x y} := by
    change TensorProduct.leftComm R A B N ⁅x, y⁆ =
      ⁅TensorProduct.leftComm R A B N x, TensorProduct.leftComm R A B N y⁆
    induction x using TensorProduct.induction_on with
    | zero =>
      refine (congrArg _ (zero_lie (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
      first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
    | tmul a p =>
      induction y using TensorProduct.induction_on with
      | zero =>
        refine (congrArg _ (lie_zero (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
        first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
      | tmul b q =>
        induction p using TensorProduct.induction_on with
        | zero =>
          rw [TensorProduct.tmul_zero]
          refine (congrArg _ (zero_lie (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
          first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
        | tmul f u =>
          induction q using TensorProduct.induction_on with
          | zero =>
            rw [TensorProduct.tmul_zero]
            refine (congrArg _ (lie_zero (L := (A ⊗[R] (B ⊗[R] N))) (M := (A ⊗[R] (B ⊗[R] N))) _)).trans ?_
            first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := (B ⊗[R] (A ⊗[R] N))) (M := (B ⊗[R] (A ⊗[R] N))) _).symm)
          | tmul g v =>
            simp only [LieAlgebra.ExtendScalars.bracket_tmul, TensorProduct.leftComm_tmul]
          | add q r hq hr =>
            rw [TensorProduct.tmul_add, LieRing.lie_add, map_add, hq, hr, map_add, LieRing.lie_add]
        | add p q hp hq =>
          rw [TensorProduct.tmul_add, LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]
      | add y z hy hz => rw [LieRing.lie_add, map_add, hy, hz, map_add, LieRing.lie_add]
    | add x z hx hz => rw [LieRing.add_lie, map_add, hx, hz, map_add, LieRing.add_lie] }

end General

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

section BasisCriterion

attribute [local instance 100] LieRing.ofAssociativeRing

theorem linear_map_lie_of_basis {R V W ι : Type*} [CommRing R]
    [LieRing V] [LieAlgebra R V] [LieRing W] [LieAlgebra R W]
    (b : Basis ι R V) (f : V →ₗ[R] W)
    (h : ∀ i j, f ⁅b i, b j⁆ = ⁅f (b i), f (b j)⁆) (x y : V) :
    f ⁅x, y⁆ = ⁅f x, f y⁆ := by
  have he : (LieModule.toEnd R V V).toLinearMap.compr₂ f =
      (LieModule.toEnd R W W).toLinearMap.compl₁₂ f f :=
    LinearMap.ext_basis b b h
  exact LinearMap.congr_fun (LinearMap.congr_fun he x) y

end BasisCriterion

end Erdos3

end

end OAI
end


