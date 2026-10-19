-- Prove2me | Definitions.Def_OAIE3v2B038
-- name    : OAIE3v2B038
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:12:33.129955+00:00
-- url     : https://prove2.me/theorems/6a0ee536-132a-4113-9456-91905d4285e5
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 39 of 311
-- statement:
--   Definitions bundle 39 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B000`, `OAIE3v2B001`, `OAIE3v2B002` of this split.
--
--   Modules: `Dynamics/CoefficientProfileBudget.lean`, `Estimates/ActiveProfileNoise.lean`, `Estimates/AllocatedScalarLogBounds.lean`, `Estimates/AllocatedShortAxis.lean`, `Estimates/DynkinTrees.lean`, `Estimates/FilteredLieTree.lean`, `Estimates/FreeLieTreeCoefficientBounds.lean`, `Estimates/FreePrimitiveCriterion.lean`, `Estimates/MixedArrayReference.lean`, `Estimates/ProgressionPartitionComposition.lean`, `Estimates/TruncatedSeriesFiltration.lean`, `Fourier/CommonCoveredSiteCharacter.lean`, `Fourier/EuclideanCoefficientTorus.lean`, `Fourier/EuclideanJetTorus.lean`, `Geometry/BoxBlockBudget.lean`, `Geometry/CoefficientAmbientCoordinates.lean`, `Geometry/CoefficientCoordinateEquiv.lean`, `Geometry/CoefficientDeckCoordinates.lean`, `Geometry/EmptyLayerChartBounds.lean`, `Geometry/MixedCoefficientSmallSupport.lean`, `Lattices/AffineCoefficientLaw.lean`, `Lattices/IntegerAxisTailLaw.lean`, `Lattices/ResidueSliceNormalizedCell.lean`, `Linear/BasisAxisNormalization.lean`, `Linear/CoefficientCoverKernel.lean`, `Linear/DynkinProjection.lean`, `Linear/KernelScaleIndependence.lean`, `Nilpotent/BCHNonlinearRemainder.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/IntegerPolynomialActiveProfileSupport.lean`, `Polynomial/IntegerPolynomialSupport.lean`, `Polynomial/VectorPolynomialReconstruction.lean`, `Probability/EmptyCoefficientDensity.lean`, `Probability/MixedDensityInterpolation.lean`, `Probability/OrthonormalMixedLaw.lean`, `Probability/PerturbationCoefficientLaw.lean`, `Probability/ScaledArrayLaw.lean`, `Sampling/AllocatedCoefficientSampler.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B000
import Definitions.Def_OAIE3v2B001
import Definitions.Def_OAIE3v2B002

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.CoefficientProfileBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem principalProfileSize_pos {R : ℝ} (hR : 0 < R) (b : ℕ) : 0 < principalProfileSize R b := by
  unfold principalProfileSize
  positivity

theorem tailProfileSize_pos {R σ : ℝ} (hR : 0 < R) (hσ : 0 < σ) (m : ℕ) :
    0 < tailProfileSize R σ m := by
  unfold tailProfileSize
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProgressionPartitionComposition
namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [instance] FiniteProgressionPartition.labelFintype

namespace FiniteProgressionPartition

variable {N : ℕ} (P : FiniteProgressionPartition N)

noncomputable def pointEquiv (i : P.Label) :
    Fin (P.length i) ≃ ↥(partitionCell P.cell i) := by
  let f (j : Fin (P.length i)) : ↥(partitionCell P.cell i) :=
    ⟨P.point i j, (mem_partitionCell P.cell i _).mpr (P.cell_point i j)⟩
  apply Equiv.ofBijective f
  constructor
  · intro j k h
    have he : P.equiv ⟨i, j⟩ = P.equiv ⟨i, k⟩ := congrArg Subtype.val h
    exact sigma_mk_injective (β := fun i : P.Label => Fin (P.length i)) (P.equiv.injective he)
  · intro n
    have hi : P.cell n.val = i := (mem_partitionCell P.cell i n.val).mp n.property
    rcases hx : P.equiv.symm n.val with ⟨k, j⟩
    have hki : k = i := by simpa only [cell, hx] using hi
    subst k
    refine ⟨j, Subtype.ext ?_⟩
    have he := congrArg P.equiv hx
    simpa only [f, point, Equiv.apply_symm_apply] using he.symm

end FiniteProgressionPartition
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoxBlockBudget
namespace OAI

section

namespace Erdos3.BoxProgressionPartition

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {N : ι → ℕ}
    (P : ∀ i, FiniteProgressionPartition (N i))

def point (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) : ∀ i, Fin (N i) :=
  fun i => (P i).point (a i) (j i)

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem point_val (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) (i : ι) :
    (point P a j i).val = (P i).start (a i) + (P i).step (a i) * (j i).val :=
  (P i).point_val _ _

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem cell_point (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) :
    cell P (point P a j) = a := by
  funext i
  exact (P i).cell_point _ _

noncomputable def pointEquiv (a : ∀ i, (P i).Label) :
    (∀ i, Fin ((P i).length (a i))) ≃ ↥(partitionCell (cell P) a) :=
  (Equiv.piCongrRight (fun i => (P i).pointEquiv (a i))).trans
    (Equiv.subtypePiEquivPi.symm.trans (Equiv.subtypeEquivRight (fun x => by
      simp only [mem_partitionCell, cell, funext_iff])))

@[simp] theorem pointEquiv_val (a : ∀ i, (P i).Label) (j : ∀ i, Fin ((P i).length (a i))) :
    (pointEquiv P a j).val = point P a j := rfl

end Erdos3.BoxProgressionPartition

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.VectorPolynomialReconstruction
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem monomialScale_pos {σ : Type*} (T : σ → ℝ) (hT : ∀ i, 0 < T i) (α : σ →₀ ℕ) :
    0 < monomialScale T α := by
  classical
  exact Finset.prod_pos (fun i _ => pow_pos (hT i) _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceNormalizedCell
namespace OAI

section

namespace Erdos3.ResidueBoxSlice

open _root_.MvPolynomial

variable {ι : Type*} {N : ι → ℕ} {q s d : ℕ}

noncomputable def parameters (A : ResidueBoxSlice N q) (i : ι) : MvPolynomial ι ℝ :=
  C (A.start i : ℝ) + (q : ℝ) • X i

theorem parameters_degree (A : ResidueBoxSlice N q) (i : ι) :
    A.parameters i ∈ weightedSupportLE (fun _ : ι => 1) 1 :=
  (weightedSupportLE _ _).add_mem (weightedSupportLE_C _ _ _)
    ((weightedSupportLE _ _).smul_mem _ (weightedSupportLE_X _ i))

noncomputable def reparamPatch (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d) :
    PolynomialPatch ι s d := P.reparam A.parameters A.parameters_degree

@[simp] theorem reparamPatch_kernel (A : ResidueBoxSlice N q) (P : PolynomialPatch ι s d) :
    (A.reparamPatch P).kernel = P.kernel := rfl

end Erdos3.ResidueBoxSlice

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DynkinTrees
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightBracketList_append (f : X → L) (xs ys : List X) :
    rightBracketList f (xs ++ ys) = rightBracketList f ys * rightBracketList f xs := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.cons_append, rightBracketList_cons, ih, mul_assoc]

theorem rightBracketWord_mul (f : X → L) (u v : FreeSemigroup X) :
    rightBracketWord f (u * v) = rightBracketWord f v * rightBracketWord f u := by
  change rightBracketList f ((u.head :: u.tail) ++ (v.head :: v.tail)) = _
  exact rightBracketList_append f _ _

theorem dynkinWord_mul (f : X → L) (u v : FreeSemigroup X) :
    dynkinWord f (u * v) = rightBracketWord f v (dynkinWord f u) := by
  simp only [dynkinWord, FreeSemigroup.tail_mul, FreeSemigroup.head_mul,
    rightBracketList_append, Module.End.mul_apply, rightBracketWord]

theorem rightAction_mul (f : X → L) (p q : WordPolynomial X) :
    rightAction f (p * q) = rightAction f q * rightAction f p := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂, mul_add]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂, add_mul]
    | single v t =>
      simp only [MonoidAlgebra.single_mul_single, rightAction_single, rightBracketWord_mul]
      rw [smul_mul_smul, mul_comm r t]

theorem dynkinMap_mul (f : X → L) (p q : WordPolynomial X) :
    dynkinMap f (p * q) = rightAction f q (dynkinMap f p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p₁ p₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  | single u r =>
    induction q using MonoidAlgebra.induction_linear with
    | zero => simp
    | add q₁ q₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | single v t =>
      simp only [MonoidAlgebra.single_mul_single, dynkinMap_single, rightAction_single,
        dynkinWord_mul, LinearMap.smul_apply, map_smul, smul_smul]

end Erdos3

end

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem rightBracket_lie (u v : L) :
    rightBracket ⁅u, v⁆ = rightBracket v * rightBracket u - rightBracket u * rightBracket v := by
  ext z
  change ⁅z, ⁅u, v⁆⁆ = ⁅⁅z, u⁆, v⁆ - ⁅⁅z, v⁆, u⁆
  rw [leibniz_lie, ← lie_skew u ⁅z, v⁆, sub_eq_add_neg]

theorem rightAction_commutatorTree (f : X → L) (t : FreeMagma X) :
    rightAction f (commutatorTree t) = rightBracket (lieTreeEval f t) := by
  induction t using FreeMagma.rec with
  | of x =>
    simp [commutatorTree, lieTreeEval, rightBracketWord, FreeSemigroup.of]
  | mul u v hu hv =>
    simp only [commutatorTree, map_sub, rightAction_mul, hu, hv, lieTreeEval, rightBracket_lie]

theorem dynkinMap_commutatorTree (f : X → L) (t : FreeMagma X) :
    dynkinMap f (commutatorTree t) = (t.length : ℚ) • lieTreeEval f t := by
  induction t using FreeMagma.rec with
  | of x => simp [commutatorTree, lieTreeEval, dynkinWord, FreeSemigroup.of]
  | mul u v hu hv =>
    simp only [commutatorTree, map_sub, dynkinMap_mul, rightAction_commutatorTree,
      hu, hv, rightBracket_apply, smul_lie, FreeMagma.length, Nat.cast_add,
      lieTreeEval, add_smul]
    rw [← lie_skew (lieTreeEval f v) (lieTreeEval f u), smul_neg, sub_neg_eq_add]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DynkinProjection
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem WordHomogeneous.sub {n : ℕ} {p q : WordPolynomial X}
    (hp : WordHomogeneous n p) (hq : WordHomogeneous n q) : WordHomogeneous n (p - q) := by
  intro w hw
  by_cases h : p.coeff w = 0
  · apply hq w
    intro he
    apply hw
    change p.coeff w - q.coeff w = 0
    rw [h, he, sub_zero]
  · exact hp w h

theorem commutatorTree_homogeneous (t : FreeMagma X) :
    WordHomogeneous t.length (commutatorTree t) := by
  induction t using FreeMagma.rec with
  | of x =>
    intro w hw
    have he : FreeSemigroup.of x = w := by
      classical
      by_contra hn
      apply hw
      simp [commutatorTree, hn]
    rw [← he]
    rfl
  | mul u v hu hv =>
    apply (hu.mul hv).sub
    simpa only [Nat.add_comm v.length u.length] using hv.mul hu

theorem dynkinProjection_homogeneous (f : X → L) {n : ℕ} {p : WordPolynomial X}
    (hp : WordHomogeneous n p) : dynkinProjection f p = (n : ℚ)⁻¹ • dynkinMap f p := by
  classical
  change p.coeff.sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord f w)) =
    (n : ℚ)⁻¹ • p.coeff.sum (fun w r => r • dynkinWord f w)
  rw [Finsupp.sum, Finsupp.sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  rw [hp w (Finsupp.mem_support_iff.mp hw), smul_comm]

theorem dynkinProjection_commutatorTree (f : X → L) (t : FreeMagma X) :
    dynkinProjection f (commutatorTree t) = lieTreeEval f t := by
  rw [dynkinProjection_homogeneous f (commutatorTree_homogeneous t),
    dynkinMap_commutatorTree, inv_smul_smul₀]
  exact_mod_cast (Nat.ne_zero_of_lt t.length_pos)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreePrimitiveCriterion
namespace OAI

section

namespace Erdos3

variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem wordPolynomialEmbedding_injective : Function.Injective (wordPolynomialEmbedding (X := X)) :=
  FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.injective.comp
    (MonoidAlgebra.mapDomain_injective FreeSemigroup.toFreeMonoid_injective)

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

@[simp] theorem freeWord_of (x : X) : freeWord (FreeMonoid.of x) = FreeAlgebra.ι ℚ x :=
  FreeMonoid.lift_eval_of _ _

theorem freeWord_coeff (w : FreeMonoid X) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid (freeWord w) = MonoidAlgebra.single w 1 := by
  have h : FreeAlgebra.equivMonoidAlgebraFreeMonoid.toAlgHom.toMonoidHom.comp freeWord =
      MonoidAlgebra.of ℚ (FreeMonoid X) := by
    apply FreeMonoid.hom_eq
    intro x
    simp [FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  exact DFunLike.congr_fun h w

theorem freeWord_single_symm (w : FreeMonoid X) (r : ℚ) :
    FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm (MonoidAlgebra.single w r) = r • freeWord w := by
  apply FreeAlgebra.equivMonoidAlgebraFreeMonoid.injective
  simp only [AlgEquiv.apply_symm_apply, map_smul, freeWord_coeff]
  simp

@[simp] theorem freeWordLinearMap_word {M : Type*} [AddCommGroup M] [Module ℚ M]
    (v : FreeMonoid X → M) (w : FreeMonoid X) : freeWordLinearMap v (freeWord w) = v w := by
  simp [freeWordLinearMap, freeWord_coeff]

theorem freeAlgebra_linear_induction (P : FreeAlgebra ℚ X → Prop)
    (hz : P 0) (ha : ∀ p q, P p → P q → P (p + q))
    (hs : ∀ (r : ℚ) p, P p → P (r • p)) (hw : ∀ w, P (freeWord w))
    (p : FreeAlgebra ℚ X) : P p := by
  obtain ⟨q, rfl⟩ := FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm.surjective p
  induction q using MonoidAlgebra.induction_linear with
  | zero => simpa only [map_zero] using hz
  | add p q hp hq => simpa only [map_add] using ha _ _ hp hq
  | single w r => rw [freeWord_single_symm]; exact hs r _ (hw w)

noncomputable def freeDegree : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  freeWordLinearMap (fun w => (w.length : ℚ) • freeWord w)

@[simp] theorem freeDegree_word (w : FreeMonoid X) :
    freeDegree (freeWord w) = (w.length : ℚ) • freeWord w := freeWordLinearMap_word _ _

@[simp] theorem freeDegree_one : freeDegree (1 : FreeAlgebra ℚ X) = 0 := by
  have h := freeDegree_word (1 : FreeMonoid X)
  simpa using h

@[simp] theorem freeDegree_generator (x : X) : freeDegree (FreeAlgebra.ι ℚ x) = FreeAlgebra.ι ℚ x := by
  have h := freeDegree_word (FreeMonoid.of x)
  simpa using h

theorem freeDegree_mul (p q : FreeAlgebra ℚ X) :
    freeDegree (p * q) = freeDegree p * q + p * freeDegree q := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegree (p * q) = freeDegree p * q + p * freeDegree q)
  · simp
  · intro p₁ p₂ h₁ h₂
    simp only [add_mul, map_add, h₁, h₂]
    abel
  · intro r p hp
    simp only [smul_mul_assoc, map_smul, hp, smul_add]
  · intro u
    apply freeAlgebra_linear_induction (fun q =>
      freeDegree (freeWord u * q) = freeDegree (freeWord u) * q + freeWord u * freeDegree q)
    · simp
    · intro q₁ q₂ h₁ h₂
      simp only [mul_add, map_add, h₁, h₂]
      abel
    · intro r q hq
      simp only [mul_smul_comm, map_smul, hq, smul_add]
    · intro v
      rw [← map_mul, freeDegree_word, FreeMonoid.length_mul, Nat.cast_add, add_smul,
        map_mul, freeDegree_word, freeDegree_word, smul_mul_assoc, mul_smul_comm]

end Erdos3

end

section

namespace Erdos3

variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem dynkinProjection_lift (f : X → L) (x : FreeLieAlgebra ℚ X) :
    dynkinProjection f (freeLieWordExpansion x) = FreeLieAlgebra.lift ℚ f x := by
  apply freeLie_linear_induction (fun x =>
    dynkinProjection f (freeLieWordExpansion x) = FreeLieAlgebra.lift ℚ f x)
  · simp
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro r x hx
    simp only [map_smul, hx]
  · intro t
    rw [freeLieWordExpansion_tree, dynkinProjection_commutatorTree, lift_lieTreeEval]

theorem lie_lift_eq_of_low_word_coeff_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (hpq : ∀ w, w.length ≤ s →
      (freeLieWordExpansion p).coeff w = (freeLieWordExpansion q).coeff w) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  rw [← dynkinProjection_lift f p, ← dynkinProjection_lift f q]
  exact dynkinProjection_eq_of_low_coeff_eq f hnil hpq

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}

theorem freeScaleSeries_word (w : FreeMonoid X) :
    freeScaleSeries (freeWord w) = PowerSeries.monomial w.length (freeWord w) := by
  induction w using freeMonoid_induction_right with
  | h1 => simp
  | hstep w x hw =>
    rw [map_mul, map_mul, freeWord_of, hw, freeScaleSeries_generator,
      PowerSeries.monomial_mul_monomial]
    simp only [FreeMonoid.length_mul, FreeMonoid.length_of]

@[simp] theorem freeHomogeneousPart_word (n : ℕ) (w : FreeMonoid X) :
    freeHomogeneousPart n (freeWord w) = if n = w.length then freeWord w else 0 := by
  rw [freeHomogeneousPart_apply, freeScaleSeries_word, PowerSeries.coeff_monomial]

noncomputable def freeTruncation (s : ℕ) : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  ∑ n ∈ Finset.range (s + 1), freeHomogeneousPart n

theorem freeTruncation_apply (s : ℕ) (p : FreeAlgebra ℚ X) :
    freeTruncation s p = ∑ n ∈ Finset.range (s + 1), freeHomogeneousPart n p := by
  simp [freeTruncation]

@[simp] theorem freeTruncation_word (s : ℕ) (w : FreeMonoid X) :
    freeTruncation s (freeWord w) = if w.length ≤ s then freeWord w else 0 := by
  rw [freeTruncation_apply]
  simp only [freeHomogeneousPart_word]
  simp [Finset.sum_ite_eq']

end Erdos3

end

section

namespace Erdos3

variable {X : Type*}

section Lie
variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lie_lift_eq_of_wordTruncation_eq (f : X → L) {s : ℕ}
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) {p q : FreeLieAlgebra ℚ X}
    (h : wordTruncation s (freeLieWordExpansion p) = wordTruncation s (freeLieWordExpansion q)) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q :=
  lie_lift_eq_of_low_word_coeff_eq f hnil ((wordTruncation_eq_iff _ _ _).mp h)

end Lie
end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

noncomputable def freeDynkinConvolution : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  (tensorContract freeAntipode freeDegree).comp freeCoproduct.toLinearMap

@[simp] theorem freeDynkinConvolution_one :
    freeDynkinConvolution (1 : FreeAlgebra ℚ X) = 0 := by
  simp [freeDynkinConvolution, Algebra.TensorProduct.one_def]

theorem freeDynkinConvolution_mul_generator (p : FreeAlgebra ℚ X) (x : X) :
    freeDynkinConvolution (p * FreeAlgebra.ι ℚ x) =
      -FreeAlgebra.ι ℚ x * freeDynkinConvolution p +
        (freeDynkinConvolution p * FreeAlgebra.ι ℚ x +
          freeAntipodeConvolution p * FreeAlgebra.ι ℚ x) := by
  change tensorContract freeAntipode freeDegree (freeCoproduct (p * FreeAlgebra.ι ℚ x)) = _
  rw [map_mul, freeCoproduct_generator, mul_add, map_add,
    tensorContract_mul_left _ _ freeAntipode_mul,
    tensorContract_derivation_mul_right _ _ freeDegree_mul,
    freeAntipode_generator, freeDegree_generator]
  rfl

theorem freeAntipodeConvolution_eq_augmentation (p : FreeAlgebra ℚ X) :
    freeAntipodeConvolution p = freeAugmentation p • 1 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeAntipodeConvolution p = freeAugmentation p • 1)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, add_smul]
  · intro r p hp
    simp only [map_smul, hp, smul_smul, smul_eq_mul]
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp
    | hstep w x hw =>
      rw [map_mul, freeWord_of, freeAntipodeConvolution_mul_generator, hw]
      simp

theorem freeDynkinConvolution_mem (p : FreeAlgebra ℚ X) :
    freeDynkinConvolution p ∈ freeAssociativeLieSubalgebra := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDynkinConvolution p ∈ freeAssociativeLieSubalgebra)
  · simpa only [map_zero] using freeAssociativeLieSubalgebra.zero_mem
  · intro p q hp hq
    simpa only [map_add] using freeAssociativeLieSubalgebra.add_mem hp hq
  · intro r p hp
    simpa only [map_smul] using freeAssociativeLieSubalgebra.smul_mem r hp
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp [freeAssociativeLieSubalgebra.zero_mem]
    | hstep w x hw =>
      rw [map_mul, freeWord_of, freeDynkinConvolution_mul_generator,
        freeAntipodeConvolution_eq_augmentation]
      have hbr := freeAssociativeLieSubalgebra.lie_mem hw
        (freeAssociativeLieSubalgebra_generator x)
      have hsm := freeAssociativeLieSubalgebra.smul_mem (freeAugmentation (freeWord w))
        (freeAssociativeLieSubalgebra_generator x)
      convert freeAssociativeLieSubalgebra.add_mem hbr hsm using 1
      change -FreeAlgebra.ι ℚ x * freeDynkinConvolution (freeWord w) +
          (freeDynkinConvolution (freeWord w) * FreeAlgebra.ι ℚ x +
            (freeAugmentation (freeWord w) • 1) * FreeAlgebra.ι ℚ x) =
        (freeDynkinConvolution (freeWord w) * FreeAlgebra.ι ℚ x -
          FreeAlgebra.ι ℚ x * freeDynkinConvolution (freeWord w)) +
            freeAugmentation (freeWord w) • FreeAlgebra.ι ℚ x
      rw [smul_mul_assoc, one_mul, neg_mul]
      abel

theorem FreePrimitive.dynkin_eq_degree {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    freeDynkinConvolution p = freeDegree p := by
  change tensorContract freeAntipode freeDegree (freeCoproduct p) = _
  rw [hp, map_add]
  simp

end Erdos3

end

section

namespace Erdos3
open TensorProduct
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem freeAugmentation_antipode (p : FreeAlgebra ℚ X) :
    freeAugmentation (freeAntipode p) = freeAugmentation p := by
  apply freeAlgebra_linear_induction (fun p =>
    freeAugmentation (freeAntipode p) = freeAugmentation p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    induction w using freeMonoid_induction_right with
    | h1 => simp
    | hstep w x _ => simp [freeAntipode_mul]

theorem FreePrimitive.augmentation_eq_zero {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    freeAugmentation p = 0 := by
  have hc : freeAntipode p + p = freeAugmentation p • 1 := by
    rw [← freeAntipodeConvolution_eq_augmentation]
    change _ = tensorContract freeAntipode LinearMap.id (freeCoproduct p)
    rw [hp, map_add]
    simp
  have h := congrArg freeAugmentation hc
  simp only [map_add, freeAugmentation_antipode, map_smul, map_one, smul_eq_mul, mul_one] at h
  linarith

noncomputable def freeDegreeInverse : FreeAlgebra ℚ X →ₗ[ℚ] FreeAlgebra ℚ X :=
  freeWordLinearMap (fun w => (w.length : ℚ)⁻¹ • freeWord w)

@[simp] theorem freeDegreeInverse_word (w : FreeMonoid X) :
    freeDegreeInverse (freeWord w) = (w.length : ℚ)⁻¹ • freeWord w :=
  freeWordLinearMap_word _ _

theorem freeAugmentation_word_of_ne_one {w : FreeMonoid X} (hw : w ≠ 1) :
    freeAugmentation (freeWord w) = 0 := by
  induction w using FreeMonoid.inductionOn' with
  | one => exact (hw rfl).elim
  | of_mul x w _ => simp

theorem freeDegreeInverse_degree (p : FreeAlgebra ℚ X) :
    freeDegreeInverse (freeDegree p) = p - freeAugmentation p • 1 := by
  apply freeAlgebra_linear_induction (fun p =>
    freeDegreeInverse (freeDegree p) = p - freeAugmentation p • 1)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq, add_smul]
    abel
  · intro r p hp
    simp only [map_smul, hp, smul_sub, smul_smul, smul_eq_mul]
  · intro w
    by_cases hw : w = 1
    · subst w
      simp
    · rw [freeDegree_word, map_smul, freeDegreeInverse_word, smul_smul,
        mul_inv_cancel₀ (show (w.length : ℚ) ≠ 0 by
          exact_mod_cast (FreeMonoid.length_eq_zero.not.mpr hw)), one_smul,
        freeAugmentation_word_of_ne_one hw, zero_smul, sub_zero]

theorem freeDegree_lieTree (t : FreeMagma X) :
    freeDegree (lieTreeEval (FreeAlgebra.ι ℚ) t) =
      (t.length : ℚ) • lieTreeEval (FreeAlgebra.ι ℚ) t := by
  induction t using FreeMagma.rec with
  | of x => simp [lieTreeEval]
  | mul u v hu hv =>
    change freeDegree (lieTreeEval (FreeAlgebra.ι ℚ) u * lieTreeEval (FreeAlgebra.ι ℚ) v -
        lieTreeEval (FreeAlgebra.ι ℚ) v * lieTreeEval (FreeAlgebra.ι ℚ) u) = _
    rw [map_sub, freeDegree_mul, freeDegree_mul, hu, hv]
    change _ = ((u.length + v.length : ℕ) : ℚ) •
      (lieTreeEval (FreeAlgebra.ι ℚ) u * lieTreeEval (FreeAlgebra.ι ℚ) v -
        lieTreeEval (FreeAlgebra.ι ℚ) v * lieTreeEval (FreeAlgebra.ι ℚ) u)
    simp only [Nat.cast_add, add_smul, smul_sub, smul_mul_assoc, mul_smul_comm]
    abel

theorem freeDegreeInverse_lieTree (t : FreeMagma X) :
    freeDegreeInverse (lieTreeEval (FreeAlgebra.ι ℚ) t) =
      (t.length : ℚ)⁻¹ • lieTreeEval (FreeAlgebra.ι ℚ) t := by
  have h := freeDegreeInverse_degree (lieTreeEval (FreeAlgebra.ι ℚ) t)
  rw [freeDegree_lieTree, map_smul, (freePrimitive_lieTree t).augmentation_eq_zero,
    zero_smul, sub_zero] at h
  have hlen : (t.length : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt t.length_pos)
  have hs := congrArg (fun z : FreeAlgebra ℚ X => (t.length : ℚ)⁻¹ • z) h
  simpa only [smul_smul, inv_mul_cancel₀ hlen, one_smul] using hs

theorem freeDegreeInverse_mem {p : FreeAlgebra ℚ X} (hp : p ∈ freeAssociativeLieSubalgebra) :
    freeDegreeInverse p ∈ freeAssociativeLieSubalgebra := by
  obtain ⟨l, rfl⟩ := hp
  apply freeLie_linear_induction (fun l =>
    freeDegreeInverse (freeLieAssociativeExpansion l) ∈ freeAssociativeLieSubalgebra)
  · simpa only [map_zero] using freeAssociativeLieSubalgebra.zero_mem
  · intro l m hl hm
    simpa only [map_add] using freeAssociativeLieSubalgebra.add_mem hl hm
  · intro r l hl
    simpa only [map_smul] using freeAssociativeLieSubalgebra.smul_mem r hl
  · intro t
    change freeDegreeInverse (FreeLieAlgebra.lift ℚ (FreeAlgebra.ι ℚ)
      (lieTreeEval (FreeLieAlgebra.of ℚ) t)) ∈ _
    rw [lift_lieTreeEval, freeDegreeInverse_lieTree]
    apply freeAssociativeLieSubalgebra.smul_mem
    exact ⟨lieTreeEval (FreeLieAlgebra.of ℚ) t, lift_lieTreeEval _ _⟩

theorem FreePrimitive.mem {p : FreeAlgebra ℚ X} (hp : FreePrimitive p) :
    p ∈ freeAssociativeLieSubalgebra := by
  have hm := freeDegreeInverse_mem (freeDynkinConvolution_mem p)
  rw [hp.dynkin_eq_degree, freeDegreeInverse_degree, hp.augmentation_eq_zero,
    zero_smul, sub_zero] at hm
  exact hm

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

theorem wordPolynomialEmbedding_single (w : FreeSemigroup X) (r : ℚ) :
    wordPolynomialEmbedding (MonoidAlgebra.single w r) = r • freeWord w.toFreeMonoid := by
  change FreeAlgebra.equivMonoidAlgebraFreeMonoid.symm
    (MonoidAlgebra.mapDomain FreeSemigroup.toFreeMonoid (MonoidAlgebra.single w r)) = _
  rw [MonoidAlgebra.mapDomain_single, freeWord_single_symm]

theorem wordPolynomialEmbedding_truncation (s : ℕ) (p : WordPolynomial X) :
    wordPolynomialEmbedding (wordTruncation s p) = freeTruncation s (wordPolynomialEmbedding p) := by
  induction p using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | single w r =>
    rw [wordTruncation_single, wordPolynomialEmbedding_single, map_smul, freeTruncation_word,
      freeSemigroup_toFreeMonoid_length]
    split_ifs <;> simp [wordPolynomialEmbedding_single]

theorem lie_lift_eq_of_freeTruncation_eq {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    {p q : FreeLieAlgebra ℚ X}
    (h : freeTruncation s (freeLieAssociativeExpansion p) =
      freeTruncation s (freeLieAssociativeExpansion q)) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q := by
  apply lie_lift_eq_of_wordTruncation_eq f hnil
  apply wordPolynomialEmbedding_injective
  rw [wordPolynomialEmbedding_truncation, wordPolynomialEmbedding_truncation,
    wordPolynomialEmbedding_freeLieExpansion, wordPolynomialEmbedding_freeLieExpansion]
  exact h

theorem freeTruncation_eq_of_scaled_series_eq {s : ℕ} {p q : FreeAlgebra ℚ X}
    (h : truncatedSeriesMk s (freeScaleSeries p) = truncatedSeriesMk s (freeScaleSeries q)) :
    freeTruncation s p = freeTruncation s q := by
  rw [freeTruncation_apply, freeTruncation_apply]
  apply Finset.sum_congr rfl
  intro n hn
  exact (truncatedSeriesMk_eq_iff s _ _).mp h n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

theorem lie_lift_eq_of_scaled_series_eq {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (f : X → L) {s : ℕ} (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    {p q : FreeLieAlgebra ℚ X}
    (h : truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion p)) =
      truncatedSeriesMk s (freeScaleSeries (freeLieAssociativeExpansion q))) :
    FreeLieAlgebra.lift ℚ f p = FreeLieAlgebra.lift ℚ f q :=
  lie_lift_eq_of_freeTruncation_eq f hnil (freeTruncation_eq_of_scaled_series_eq h)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

open PowerSeries

section Ring
variable {A B : Type*} [Ring A] [Algebra ℚ A] [Ring B] [Algebra ℚ B]

theorem nilpotentLog_zero : nilpotentLog (0 : A) = 0 := by
  simp [nilpotentLog_eq_sum (pow_one (0 : A))]

end Ring

end Erdos3

end

section

namespace Erdos3

open PowerSeries _root_.Finset

variable {A : Type*} [Ring A] [Algebra ℚ A]

section NilAlgebra
variable (I : NonUnitalSubalgebra ℚ A) (hI : ∀ a ∈ I, IsNilpotent a)
include hI

theorem nilpotentBCH_assoc {a b c : A} (ha : a ∈ I) (hb : b ∈ I) (hc : c ∈ I) :
    nilpotentBCH (nilpotentBCH a b) c = nilpotentBCH a (nilpotentBCH b c) := by
  have hab := nilpotentBCH_mem I ha hb (hI _ ha) (hI _ hb)
  have hbc := nilpotentBCH_mem I hb hc (hI _ hb) (hI _ hc)
  apply exp_injective_on_nilpotents
    (hI _ (nilpotentBCH_mem I hab hc (hI _ hab) (hI _ hc)))
    (hI _ (nilpotentBCH_mem I ha hbc (hI _ ha) (hI _ hbc)))
  rw [exp_nilpotentBCH I hI hab hc, exp_nilpotentBCH I hI ha hbc,
    exp_nilpotentBCH I hI ha hb, exp_nilpotentBCH I hI hb hc, mul_assoc]

end NilAlgebra

theorem nilpotentBCH_zero_left {a : A} (ha : IsNilpotent a) : nilpotentBCH 0 a = a := by
  simp only [nilpotentBCH, IsNilpotent.exp_zero, one_mul, nilpotentLog_exp_sub_one ha]

theorem nilpotentBCH_neg_left {a : A} (ha : IsNilpotent a) : nilpotentBCH (-a) a = 0 := by
  rw [nilpotentBCH, IsNilpotent.exp_neg_mul_exp_self ha, sub_self, nilpotentLog_zero]

end Erdos3

end

section

namespace Erdos3
variable {X : Type*}
attribute [local instance] LieRing.ofAssociativeRing

theorem bchHomogeneousPart_primitive (s n : ℕ) (hn : n ≤ s) :
    FreePrimitive (freeHomogeneousPart n (bchPolynomial (s + 1))) := by
  have h := (scaledFreeGenerator_primitive s (0 : Fin 2)).bch
    (scaledFreeGenerator_primitive s (1 : Fin 2))
    (scaledFreeGenerator_positive s (0 : Fin 2)) (scaledFreeGenerator_positive s (1 : Fin 2))
  rw [← scaled_bchPolynomial] at h
  exact h.coeff n hn

theorem bchHomogeneousPart_mem (s n : ℕ) (hn : n ≤ s) :
    freeHomogeneousPart n (bchPolynomial (s + 1)) ∈ freeAssociativeLieSubalgebra :=
  (bchHomogeneousPart_primitive s n hn).mem

theorem bchTruncation_mem (s : ℕ) :
    freeTruncation s (bchPolynomial (s + 1)) ∈ freeAssociativeLieSubalgebra := by
  rw [freeTruncation_apply]
  apply freeAssociativeLieSubalgebra.sum_mem
  intro n hn
  exact bchHomogeneousPart_mem s n (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn))

noncomputable def bchLiePolynomial (s : ℕ) : FreeLieAlgebra ℚ (Fin 2) :=
  Classical.choose (bchTruncation_mem s)

theorem bchLiePolynomial_expansion (s : ℕ) :
    freeLieAssociativeExpansion (bchLiePolynomial s) = freeTruncation s (bchPolynomial (s + 1)) :=
  Classical.choose_spec (bchTruncation_mem s)

noncomputable def lieBCH {L : Type*} [LieRing L] [LieAlgebra ℚ L] (s : ℕ) (a b : L) : L :=
  FreeLieAlgebra.lift ℚ ![a, b] (bchLiePolynomial s)

end Erdos3

end

section

namespace Erdos3
variable {X A : Type*} [Ring A] [Algebra ℚ A]
attribute [local instance] LieRing.ofAssociativeRing

namespace NilpotentAlgebraFiltration
variable {s : ℕ} (F : NilpotentAlgebraFiltration A s) (f : X → A)

theorem eval_freeWord_mem (hf : ∀ x, f x ∈ F.layer 1) (w : FreeMonoid X) :
    FreeAlgebra.lift ℚ f (freeWord w) ∈ F.layer w.length := by
  induction w using freeMonoid_induction_right with
  | h1 => simp [F.zero_eq_top]
  | hstep w x hw =>
    rw [map_mul, map_mul, freeWord_of, FreeAlgebra.lift_ι_apply,
      FreeMonoid.length_mul, FreeMonoid.length_of]
    exact F.mul_mem hw (hf x)

theorem eval_freeWord_eq_zero (hf : ∀ x, f x ∈ F.layer 1) (w : FreeMonoid X)
    (hw : s < w.length) : FreeAlgebra.lift ℚ f (freeWord w) = 0 := by
  have h := F.antitone (Nat.succ_le_of_lt hw) (F.eval_freeWord_mem f hf w)
  simpa only [F.terminal, Submodule.mem_bot] using h

theorem eval_freeTruncation (hf : ∀ x, f x ∈ F.layer 1) (p : FreeAlgebra ℚ X) :
    FreeAlgebra.lift ℚ f (freeTruncation s p) = FreeAlgebra.lift ℚ f p := by
  apply freeAlgebra_linear_induction (fun p =>
    FreeAlgebra.lift ℚ f (freeTruncation s p) = FreeAlgebra.lift ℚ f p)
  · simp
  · intro p q hp hq
    simp only [map_add, hp, hq]
  · intro r p hp
    simp only [map_smul, hp]
  · intro w
    rw [freeTruncation_word]
    split_ifs with hw
    · rfl
    · rw [map_zero, F.eval_freeWord_eq_zero f hf w (Nat.lt_of_not_ge hw)]

end NilpotentAlgebraFiltration

theorem NilpotentAlgebraFiltration.lieBCH_eq {s : ℕ} (F : NilpotentAlgebraFiltration A s)
    {a b : A} (ha : a ∈ F.layer 1) (hb : b ∈ F.layer 1) : lieBCH s a b = nilpotentBCH a b := by
  rw [lieBCH, ← freeLieAssociativeExpansion_eval, bchLiePolynomial_expansion,
    F.eval_freeTruncation ![a, b] (by intro x; fin_cases x <;> assumption)]
  exact F.bchPolynomial_formula ha hb

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHNonlinearRemainder
namespace OAI

section

namespace Erdos3
variable {X L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

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

namespace NilpotentLieBCHGroup
variable {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable instance instMul : Mul (NilpotentLieBCHGroup L s hnil) where
  mul a b := ⟨lieBCH s a.coord b.coord⟩

@[simp] theorem coord_mul (a b : NilpotentLieBCHGroup L s hnil) :
    (a * b).coord = lieBCH s a.coord b.coord := rfl
@[simp] theorem coord_one : (1 : NilpotentLieBCHGroup L s hnil).coord = 0 := rfl
@[simp] theorem coord_inv (a : NilpotentLieBCHGroup L s hnil) : (a⁻¹).coord = -a.coord := rfl

noncomputable instance instGroup : Group (NilpotentLieBCHGroup L s hnil) :=
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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3


open scoped BigOperators

theorem monomialScale_le_uniform_pow {K : Type*} (T : K → ℝ)
    (hT : ∀ k, 0 ≤ T k) {L : ℝ} (hL : 1 ≤ L) (hTL : ∀ k, T k ≤ L)
    (e : K →₀ ℕ) {h : ℕ} (he : e.sum (fun _ n => n) ≤ h) :
    monomialScale T e ≤ L ^ h := by
  classical
  change (∏ k ∈ e.support, T k ^ e k) ≤ _
  calc
    _ ≤ ∏ k ∈ e.support, L ^ e k :=
      Finset.prod_le_prod (fun k _ => pow_nonneg (hT k) _)
        (fun k _ => pow_le_pow_left₀ (hT k) (hTL k) _)
    _ = L ^ e.sum (fun _ n => n) := by rw [Finset.prod_pow_eq_pow_sum]; rfl
    _ ≤ L ^ h := pow_le_pow_right₀ hL he

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineCoefficientLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped ContDiff

noncomputable def affineProbabilityProfile (c w x : ℝ) : ℝ :=
  w⁻¹ * smoothProbabilityProfile ((x - c) / w)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators ContDiff

noncomputable def affineProductProfile {I : Type*} [Fintype I] (c w x : I → ℝ) : ℝ :=
  ∏ i, affineProbabilityProfile (c i) (w i) (x i)

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def affineCoefficientMeasure (c w : ℝ) : Measure ℝ :=
  realDensityMeasure volume (affineProbabilityProfile c w)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.PerturbationCoefficientLaw
namespace OAI

section

namespace Erdos3

theorem enormousPerturbation_large {V : Type*} (T : V → ℝ) (hT : ∀ i, 0 < T i)
    {K L ε : ℝ} {s : ℕ} (hL : 1 ≤ L) (hε : 0 < ε) (hTL : ∀ i, T i ≤ L)
    (hK : L ^ (s + 1) ≤ K) (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / monomialScale T e) * K := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hS := monomialScale_pos T hT e
  have hSL : L * monomialScale T e ≤ K := by
    calc
      _ ≤ L * L ^ s := mul_le_mul_of_nonneg_left
        (monomialScale_le_uniform_pow T (fun i => (hT i).le) hL hTL e he) hL0
      _ = L ^ (s + 1) := by rw [pow_succ]; ring
      _ ≤ K := hK
  have hb := mul_le_mul_of_nonneg_left hSL hε.le
  have hstep : ε * L ≤ (ε / monomialScale T e) * K := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hS).mpr
    nlinarith
  exact hεL.trans hstep

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAxisTailLaw
namespace OAI

section

namespace Erdos3

theorem integerAxisTail_width {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    {K L s : ℕ} (hL : 0 < L) (hTL : ∀ v, T v ≤ L) {ε : ℝ} (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) (ha : L ^ (s + 1) < K) :
    8 * (probabilityProfileLipschitz : ℝ) ≤ (ε / monomialScale T e) * K := by
  apply enormousPerturbation_large T hT (by exact_mod_cast hL) hε hTL
  · exact_mod_cast ha.le
  · exact hεL
  · exact he

noncomputable def integerAxisTailPMF {V : Type*} (T : V → ℝ) (hT : ∀ v, 0 < T v)
    (K L s : ℕ) (hK : 0 < K) (hL : 0 < L) (hTL : ∀ v, T v ≤ L) (ε : ℝ) (hε : 0 < ε)
    (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)
    (e : V →₀ ℕ) (he : e.sum (fun _ n => n) ≤ s) : PMF ℤ :=
  if ha : L ^ (s + 1) < K then
    normalizedIntegerPMF K 0 (ε / monomialScale T e) (by exact_mod_cast hK)
      (div_pos hε (monomialScale_pos T hT e)) (integerAxisTail_width T hT hL hTL hε hεL e he ha)
  else PMF.pure 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialActiveProfileSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (ρ γ ε : ℝ) (hρ : 0 < ρ) (hγ : 0 < γ) (hε : 0 < ε)
variable (hgap : L ^ h < K → (principalSamplingGapRatio γ * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ ε * L)

noncomputable def integerPolynomialCoordinatePMF (j : J) : PMF ℤ := by
  classical
  exact if j = j₀ then constantIntegerPMF K ρ (by exact_mod_cast hK) hρ
    else if j ∈ P then integerAxisPrincipalPMF h K L hh hK hL γ hγ hgap
    else integerAxisTailPMF T hT K L s hK hL hTL ε hε hεL (e j) (he j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IntegerPolynomialSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory

variable {J V : Type*} [Fintype J]
variable (P : Finset J) (j₀ : J) (h K L s : ℕ)
variable (hh : 0 < h) (hK : 0 < K) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 0 < T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)

variable (hgap : L ^ h < K → (principalSamplingGapRatio (principalProfileSize R P.card) * L) ^ h ≤ K)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ (tailProfileSize R σ (Fintype.card J)) * L)

noncomputable def allocatedIntegerPolynomialCoordinatePMF : J → PMF ℤ :=
  integerPolynomialCoordinatePMF P j₀ h K L s hh hK hL T hT hTL e he (R / 4) (principalProfileSize R P.card) (tailProfileSize R σ (Fintype.card J))
    (by positivity) (principalProfileSize_pos hR _) (tailProfileSize_pos hR hσ _) hgap hεL

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

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3
variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace NilpotentLieFiltration
variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)
include F

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

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FilteredLieTree
namespace OAI

section

namespace Erdos3

universe u

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

inductive FilteredLieTree (F : NilpotentLieFiltration L s) : ℕ → ℕ → Type u where
  | leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) : FilteredLieTree F d 1
  | bracket {d e r t : ℕ} (a : FilteredLieTree F d r) (b : FilteredLieTree F e t) :
      FilteredLieTree F (d + e) (r + t)

namespace FilteredLieTree

variable {F : NilpotentLieFiltration L s}

def eval : {d r : ℕ} → FilteredLieTree F d r → L
  | _, _, .leaf _ x _ => x
  | _, _, .bracket a b => ⁅eval a, eval b⁆

end FilteredLieTree

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisAxisNormalization
namespace OAI

section

namespace Erdos3

open Module
open scoped BigOperators

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem basisAxisScale_pos (b : Basis I ℝ E) (i : I) : 0 < basisAxisScale b i := by
  apply Nat.ceil_pos.mpr
  exact inv_pos.mpr (norm_pos_iff.mpr (b.ne_zero i))

noncomputable def normalizedAxisBasis (b : Basis I ℝ E) : Basis I ℝ E :=
  b.unitsSMul (fun i => Units.mk0 (basisAxisScale b i : ℝ)
    (Nat.cast_ne_zero.mpr (basisAxisScale_pos b i).ne'))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.EmptyLayerChartBounds
namespace OAI

section

namespace Erdos3

open Module Submodule MeasureTheory
open scoped BigOperators

variable {E : Type*} {n : ℕ} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]

noncomputable def normalizedOrthogonalChart (W : Submodule ℝ E) (b : Basis (Fin n) ℝ Wᗮ) :
    E ≃L[ℝ] W × (Fin n → ℝ) := orthogonalBasisChart W (normalizedAxisBasis b)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter
namespace OAI

section

namespace Erdos3

variable {D : Type*} [Fintype D] (U : Submodule ℝ (D → ℝ))

noncomputable def euclideanSubspaceArrayEquiv : euclideanSubspace U ≃L[ℝ] (Unit → U) where
  toFun x _ := ⟨WithLp.ofLp x.val, x.property⟩
  invFun x := ⟨WithLp.toLp 2 (x ()).val, (x ()).property⟩
  left_inv _ := rfl
  right_inv x := by funext u; cases u; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  continuous_toFun := by
    apply continuous_pi
    intro u
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).continuous.comp
      continuous_subtype_val).subtype_mk _
  continuous_invFun := by
    exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : D => ℝ)).symm.continuous.comp
      (continuous_subtype_val.comp (continuous_apply ()))).subtype_mk _

theorem euclideanSubspaceArrayEquiv_mem_lattice (x : euclideanSubspace U) :
    euclideanSubspaceArrayEquiv U x ∈ subspaceArrayIntegerLattice Unit U ↔
      x ∈ latticeSection (standardEuclideanLattice D) (euclideanSubspace U) := by
  change (∀ u i, ∃ n : ℤ, x.val i = n) ↔ x.val ∈ standardEuclideanLattice D
  rw [mem_standardEuclideanLattice]
  constructor
  · intro h i
    obtain ⟨n, hn⟩ := h () i
    exact ⟨n, hn.symm⟩
  · intro h u i
    obtain ⟨n, hn⟩ := h i
    exact ⟨n, hn.symm⟩

theorem euclideanSubspaceArrayEquiv_map_lattice :
    (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup.map
      (euclideanSubspaceArrayEquiv U).toLinearEquiv.toAddEquiv.toAddMonoidHom =
        subspaceArrayIntegerLattice Unit U := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (euclideanSubspaceArrayEquiv_mem_lattice U x).mpr hx
  · intro hy
    refine ⟨(euclideanSubspaceArrayEquiv U).symm y, ?_,
      (euclideanSubspaceArrayEquiv U).apply_symm_apply y⟩
    exact (euclideanSubspaceArrayEquiv_mem_lattice U _).mp (by simpa using hy)

noncomputable def euclideanSubspaceTorusEquiv :
    (euclideanSubspace U ⧸
      (latticeSection (standardEuclideanLattice D) (euclideanSubspace U)).toAddSubgroup) ≃+
        SubspaceArrayTorus Unit U :=
  QuotientAddGroup.congr _ _ (euclideanSubspaceArrayEquiv U).toLinearEquiv.toAddEquiv
    (euclideanSubspaceArrayEquiv_map_lattice U)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanJetTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

abbrev CoefficientCoordinateTori {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :=
  ∀ s : CoefficientSlot K m, SubspaceArrayTorus Unit (U s.1)

def coefficientCoordinateArray {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (s : CoefficientSlot K m) :
    CoefficientArray (K := K) U →ₗ[ℝ] (Unit → U s.1) where
  toFun x _ := x s
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coefficientCoordinateTorus {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    CoefficientTorus (K := K) U →+ CoefficientCoordinateTori (K := K) U :=
  AddMonoidHom.pi (fun s => QuotientAddGroup.map (coefficientIntegerLattice U)
    (subspaceArrayIntegerLattice Unit (U s.1)) (coefficientCoordinateArray U s).toAddMonoidHom
    (fun _x hx _ a => hx s a))

theorem coefficientCoordinateTorus_mk {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (x : CoefficientArray (K := K) U)
    (s : CoefficientSlot K m) :
    coefficientCoordinateTorus U (QuotientAddGroup.mk' (coefficientIntegerLattice U) x) s =
      QuotientAddGroup.mk' (subspaceArrayIntegerLattice Unit (U s.1)) (fun _ => x s) := rfl

theorem coefficientCoordinateTorus_surjective {K : Type*} {m : ℕ} {J : Fin m → Type*}
    (U : ∀ j, Submodule ℝ (J j → ℝ)) :
    Function.Surjective (coefficientCoordinateTorus (K := K) U) := by
  intro y
  choose v hv using fun s => QuotientAddGroup.mk'_surjective
    (subspaceArrayIntegerLattice Unit (U s.1)) (y s)
  refine ⟨QuotientAddGroup.mk' (coefficientIntegerLattice U) (fun s => v s ()), ?_⟩
  funext s
  rw [coefficientCoordinateTorus_mk]
  have he : (fun _ : Unit => v s ()) = v s := funext (fun u => by cases u; rfl)
  rw [he, hv s]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientCoordinateEquiv
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

theorem coefficientCoordinateTorus_injective :
    Function.Injective (coefficientCoordinateTorus (K := K) U) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro s i
  have hs := QuotientAddGroup.eq_iff_sub_mem.mp (congrFun h s)
  exact hs () i

noncomputable def coefficientCoordinateEquiv :
    CoefficientTorus (K := K) U ≃+ CoefficientCoordinateTori (K := K) U :=
  AddEquiv.ofBijective (coefficientCoordinateTorus U)
    ⟨coefficientCoordinateTorus_injective U, coefficientCoordinateTorus_surjective U⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.EuclideanCoefficientTorus
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {K : Type*} {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev EuclideanCoefficientLayers :=
  ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) →
    euclideanSubspace (U j) ⧸
      (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup

noncomputable def euclideanCoefficientEquiv :
    CoefficientTorus (K := K) U ≃+ EuclideanCoefficientLayers (K := K) U where
  toFun x j d := (euclideanSubspaceTorusEquiv (U j)).symm
    (coefficientCoordinateEquiv U x ⟨j, d⟩)
  invFun y := (coefficientCoordinateEquiv U).symm
    (fun s => euclideanSubspaceTorusEquiv (U s.1) (y s.1 s.2))
  left_inv x := by
    apply (coefficientCoordinateEquiv U).injective
    rw [AddEquiv.apply_symm_apply]
    funext s
    exact (euclideanSubspaceTorusEquiv (U s.1)).apply_symm_apply _
  right_inv y := by
    funext j d
    dsimp only
    rw [AddEquiv.apply_symm_apply]
    exact (euclideanSubspaceTorusEquiv (U j)).symm_apply_apply _
  map_add' x y := by
    funext j d
    simp only [map_add, Pi.add_apply]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.MixedDensityInterpolation
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

noncomputable def mixedCoefficientDensity {I J : Type*} [Fintype I] [Fintype J]
    (c w : I → ℝ) (p : J → PMF ℤ) (x : (I → ℝ) × (J → ℤ)) : ℝ :=
  affineProductProfile c w x.1 * ∏ j, (p j (x.2 j)).toReal

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.OrthonormalMixedLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module
open scoped BigOperators

variable {E I J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype I] [Fintype J]

noncomputable def orthonormalMixedDensity (b : OrthonormalBasis I ℝ E)
    (c w : I → ℝ) (p : J → PMF ℤ) (x : E × (J → ℤ)) : ℝ :=
  mixedCoefficientDensity c w p ((orthonormalMixedChart b).symm x)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedArrayReference
namespace OAI

section

namespace Erdos3

open MeasureTheory

noncomputable def mixedScalarArrayLaw {I Z J : Type*} [Fintype I] [Fintype Z] [Fintype J]
    (c w : I → J → ℝ) (p : Z → J → PMF ℤ) : Measure ((I → J → ℝ) × (Z → J → ℤ)) :=
  (Measure.pi (fun i => Measure.pi (fun j => affineCoefficientMeasure (c i j) (w i j)))).prod
    (Measure.pi (fun z => Measure.pi (fun j => (p z j).toMeasure)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MixedCoefficientSmallSupport
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

noncomputable def normalizedLatticePoint (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (x : W × (Fin n → ℤ)) : EuclideanSpace ℝ D :=
  (normalizedOrthogonalChart W b).symm (x.1, fun i => (x.2 i : ℝ) / (basisAxisScale b i : ℝ))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScaledArrayLaw
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D : Type*} [Fintype D] {n : ℕ}

noncomputable def normalizedQuotientDensity (W : Submodule ℝ (EuclideanSpace ℝ D))
    (b : Basis (Fin n) ℝ Wᗮ) (hb : span ℤ (Set.range b) = projectedIntegerLattice W)
    (Ω : Set (EuclideanSpace ℝ D)) (f : W × (Fin n → ℤ) → ℝ) :
    (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  restrictedChartDensity (normalizedLatticeQuotient W b hb) (normalizedLatticePoint W b ⁻¹' Ω)
    (ZLattice.covolume (latticeSection (standardEuclideanLattice D) W)) f

end Erdos3

end

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set

variable {D I : Type*} [Fintype D] [Fintype I] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalMixedDensity (c w : I → ℝ) (p : Fin n → PMF ℤ) :
    (W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) → ℝ :=
  normalizedQuotientDensity W b hb (standardLatticeSmallBox D) (orthonormalMixedDensity o c w p)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.EmptyCoefficientDensity
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule _root_.Set
open scoped BigOperators

variable {D I J : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (hb : span ℤ (Set.range b) = projectedIntegerLattice W) (o : OrthonormalBasis I ℝ W)

noncomputable def canonicalArrayDensity (c w : I → J → ℝ) (p : Fin n → J → PMF ℤ)
    (y : J → W ⧸ (latticeSection (standardEuclideanLattice D) W).toAddSubgroup) : ℝ :=
  ∏ j, canonicalMixedDensity W b hb o (fun i => c i j) (fun i => w i j) (fun i => p i j) (y j)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped BigOperators

variable {K : Type*} [Fintype K] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))

variable (c w : ∀ j : Fin m, I j → BoundedCoefficientExponent K (j.val + 1) → ℝ)
variable (p : ∀ j : Fin m, Fin (n j) → BoundedCoefficientExponent K (j.val + 1) → PMF ℤ)

noncomputable def canonicalCoefficientDensity (y : CoefficientTorus (K := K) U) : ℝ :=
  ∏ j, canonicalArrayDensity (euclideanSubspace (U j)) (b j) (hb j) (o j) (c j) (w j) (p j)
    (euclideanCoefficientEquiv U y j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedShortAxis
namespace OAI

section

namespace Erdos3

open MeasureTheory Module Submodule

variable {D I J V : Type*} [Fintype D] [Fintype I] [Fintype J] {n : ℕ}
variable (W : Submodule ℝ (EuclideanSpace ℝ D)) (b : Basis (Fin n) ℝ Wᗮ)
variable (Pz : Fin n → Finset J) (j₀ : J) (h L s : ℕ) (hh : 0 < h) (hL : 0 < L)
variable (T : V → ℝ) (hT : ∀ v, 1 ≤ T v) (hTL : ∀ v, T v ≤ L)
variable (e : J → V →₀ ℕ) (he : ∀ j, (e j).sum (fun _ n => n) ≤ s)
variable (R σ : ℝ) (hR : 0 < R) (hσ : 0 < σ)
variable (hgap : ∀ i, L ^ h < basisAxisScale b i →
  (principalSamplingGapRatio (principalProfileSize R (Pz i).card) * L) ^ h ≤ basisAxisScale b i)
variable (hεL : 8 * (probabilityProfileLipschitz : ℝ) ≤ tailProfileSize R σ (Fintype.card J) * L)

noncomputable def allocatedProjectionPMFs : Fin n → J → PMF ℤ :=
  fun i => allocatedIntegerPolynomialCoordinatePMF (Pz i) j₀ h (basisAxisScale b i) L s
    hh (basisAxisScale_pos b i) hL T (fun v => lt_of_lt_of_le zero_lt_one (hT v)) hTL e he
    R σ hR hσ (hgap i) hεL

end Erdos3

end

section

namespace Erdos3

open MeasureTheory

noncomputable def allocatedArrayWidths {I J V : Type*} [Fintype J] (e : J → V →₀ ℕ) (T : V → ℝ)
    (Pc : I → Finset J) (j₀ : J) (R σ : ℝ) (i : I) (j : J) : ℝ :=
  coefficientProfileWidth (Pc i) j₀ (R / 4) (principalProfileSize R (Pc i).card)
    (tailProfileSize R σ (Fintype.card J)) j / monomialScale T (e j)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedScalarLogBounds
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedLayerWidths (j : Fin m) :
    I j → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → ℝ :=
  allocatedArrayWidths Subtype.val (layerSamplerBox B U b S) (layerContinuousPrincipalSlots B j)
    (constantCoefficientSlot _ _) (R j) (σ j)

noncomputable def allocatedLayerIntegerPMFs (j : Fin m) :
    Fin (n j) → BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → PMF ℤ :=
  allocatedProjectionPMFs (euclideanSubspace (U j)) (b j) (layerIntegerPrincipalSlots B j)
    (constantCoefficientSlot _ _) (j.val + 1) S.value (layerTailDegree m) (Nat.zero_lt_succ _) S.positive
    (layerSamplerBox B U b S) (layerSamplerBox_one_le B U b S) (layerSamplerBox_le B U b S)
    Subtype.val (fun d => d.property.trans (layerDegree_le_tailDegree j))
    (R j) (σ j) (hR j) (hσ j) (S.gap j) (S.width j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientDeckCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule

variable {K : Type*} {m : ℕ} {J B : Fin m → Type*}
variable [∀ j, Fintype (J j)] [∀ j, Fintype (B j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

abbrev CoefficientDeckResidues (B : Fin m → Type*) (d : ℕ) :=
  ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) → B j → ZMod d

noncomputable def coefficientKernelCoordinates (d : ℕ) :
    (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker ≃+
      ∀ j : Fin m, BoundedCoefficientExponent K (j.val + 1) →
        (quotientIntegerCover
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup d).ker :=
  (nsmulKernelCongr (G := CoefficientTorus (K := K) U)
    (H := EuclideanCoefficientLayers (K := K) U) (euclideanCoefficientEquiv (K := K) U) d).trans
    ((nsmulKernelPiEquiv (fun j : Fin m => BoundedCoefficientExponent K (j.val + 1) →
        euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) d).trans
      (AddEquiv.piCongrRight fun j => nsmulKernelPiEquiv
        (fun _ : BoundedCoefficientExponent K (j.val + 1) => euclideanSubspace (U j) ⧸
          (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup) d))

variable (bW : ∀ j, Basis (B j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

noncomputable def coefficientDeckKernelEquiv (d : ℕ) (hd : 0 < d) :
    CoefficientDeckResidues (K := K) B d ≃+
      (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
  (AddEquiv.piCongrRight fun j : Fin m => AddEquiv.piCongrRight
    fun _ : BoundedCoefficientExponent K (j.val + 1) =>
      coverKernelBasisEquiv
        (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup
        (bW j) d hd).trans (coefficientKernelCoordinates U d).symm

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CoefficientAmbientCoordinates
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators NNReal

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}

abbrev CoefficientAmbientIndex (K : Type*) {m : ℕ} (J : Fin m → Type*) :=
  Σ s : CoefficientSlot K m, J s.1

noncomputable def coefficientAmbientTorus (U : ∀ j, Submodule ℝ (J j → ℝ))
    (x : CoefficientTorus (K := K) U) : CoefficientAmbientIndex K J → UnitAddCircle :=
  fun t => subspaceAmbientTorus (U t.1.1) (coefficientCoordinateTorus U x t.1) t.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CoefficientCoverKernel
namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {K : Type*} {m : ℕ} {J : Fin m → Type*}
variable (U : ∀ j, Submodule ℝ (J j → ℝ))

noncomputable def coefficientAmbientHom :
    CoefficientTorus (K := K) U →+ (CoefficientAmbientIndex K J → UnitAddCircle) where
  toFun := coefficientAmbientTorus U
  map_zero' := by
    funext t
    simp [coefficientAmbientTorus]
  map_add' x y := by
    funext t
    simp [coefficientAmbientTorus, map_add]

theorem coefficientAmbientTorus_injective :
    Function.Injective (coefficientAmbientTorus (K := K) U) := by
  intro x y h
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective (coefficientIntegerLattice U) y
  apply QuotientAddGroup.eq_iff_sub_mem.mpr
  intro s i
  have he : ((a s).val i : UnitAddCircle) = ((b s).val i : UnitAddCircle) := congrFun h ⟨s, i⟩
  have hz : (((a s).val i - (b s).val i : ℝ) : UnitAddCircle) = 0 := by
    rw [AddCircle.coe_sub, he, sub_self]
  obtain ⟨z, hz⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hz
  exact ⟨z, by simpa using hz.symm⟩

variable [Fintype K] [∀ j, Fintype (J j)]

theorem coefficientCoverKernel_finite (d : ℕ) (hd : 0 < d) :
    Finite (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker := by
  let T := {z : UnitAddCircle // d • z = 0}
  let : Fintype T := (AddCircle.finite_torsion (1 : ℝ) hd).fintype
  let f : (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker →
      CoefficientAmbientIndex K J → T := fun x i =>
    ⟨coefficientAmbientHom U x.val i, by
      change (d • coefficientAmbientHom U x.val) i = 0
      rw [← map_nsmul]
      have hx : d • x.val = 0 := x.property
      rw [hx, map_zero]
      rfl⟩
  apply Finite.of_injective f
  intro x y hxy
  apply Subtype.ext
  apply coefficientAmbientTorus_injective U
  funext i
  exact congrArg Subtype.val (congrFun hxy i)

@[instance_reducible]
noncomputable def coefficientCoverKernelFintype (d : ℕ) (hd : 0 < d) :
    Fintype (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker := by
  let : Finite (quotientIntegerCover (coefficientIntegerLattice (K := K) U) d).ker :=
    coefficientCoverKernel_finite U d hd
  exact Fintype.ofFinite _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)

noncomputable def allocatedCoefficientDensity :
    CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℝ :=
  canonicalCoefficientDensity U b hb o (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S)

noncomputable def allocatedCoefficientSource :
    Measure (CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n) :=
  Measure.pi (fun j => mixedScalarArrayLaw (allocatedLayerCenters B U b S j)
    (allocatedLayerWidths B U b S j) (allocatedLayerIntegerPMFs B U b hR hσ S j))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ActiveProfileNoise
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

abbrev SamplerCoefficientSlot {D : Type*} (G : Type*) (B : D → Type*)
    (h : D → ℕ) (d : D) := BoundedCoefficientExponent (SamplerTupleIndex G B h) (h d)

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

abbrev ActiveProfileCoefficientIndex {D : Type*} (G : Type*) (B : D → Type*)
    (h : D → ℕ) (P : D → Prop) := Σ d : {d // ¬P d}, SamplerCoefficientSlot G B h d.val

end Erdos3

end

end OAI
end


