-- Prove2me | Definitions.Def_OAIE3v2B003
-- name    : OAIE3v2B003
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T09:57:13.264786+00:00
-- url     : https://prove2.me/theorems/03e4ddca-5632-45d2-a349-a8774d7508af
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 4 of 311
-- statement:
--   Definitions bundle 4 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports no other bundle of this split.
--
--   Modules: `Estimates/LieTreeMultidegree.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/PartialComplexScaledQuadrature.lean`, `Estimates/ProductOrbitCongruence.lean`, `Estimates/RealSubquotientEquiv.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/RealifiedTripleLayers.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/RepresentativeWindowPatch.lean`, `Estimates/UniformProductAccuracy.lean`, `Estimates/VectorAlgebraicMajorDecomposition.lean`, `Fourier/RectangularGridCharacter.lean`, `Geometry/LieCoordinateHeight.lean`, `Geometry/LieCoordinateScalarExtension.lean`, `Geometry/RealifiedTripleCoordinates.lean`, `Geometry/RightCosetMetricMap.lean`, `Lattices/AffineBlockScale.lean`, `Lattices/FactorialIntegerScalars.lean`, `Lattices/IntegerAffineSubstitution.lean`, `Lattices/RectangularLatticeCells.lean`, `Linear/RationalMatrixSeparation.lean`, `Linear/SquareBasisGeometry.lean`, `Nilpotent/CurrentBracketInductionStep.lean`, `Nilpotent/FactorwiseBCHCovers.lean`, `Nilpotent/FreeNilpotentLieAlgebra.lean`, `Nilpotent/LinearBCHAbelian.lean`, `Nilpotent/NilpotentBilinearExponential.lean`, `Nilpotent/SquarefreeBracketHeight.lean`, `Polynomial/LieCoordinatePolynomials.lean`, `Polynomial/MajorTranslationPolynomialSymbolDegree.lean`, `Polynomial/MajorWeightedDegreeTools.lean`, `Polynomial/MixedWeightedPolynomialRename.lean`, `Polynomial/PolynomialPatchShearOrbitConverse.lean`, `Polynomial/PolynomialPrimitive.lean`, `Polynomial/PolynomialShearParameterBudget.lean`, `Polynomial/PolynomialTermCount.lean`, `Polynomial/PolynomialTranslationActionCompatibility.lean`, `Polynomial/PolynomialTranslationSeries.lean`, `Polynomial/SquarefreeBlockDegree.lean`, `Polynomial/TotalDegreeSplitDownsets.lean`, `Polynomial/TranslationPhaseQuotient.lean`, `Polynomial/WeightedLinearPolynomialRestriction.lean`, `Probability/FiniteDensityMassBound.lean`, `Sampling/RationalSpanGrid.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NilpotentBilinearExponential
namespace OAI

section

namespace Erdos3

open IsNilpotent TensorProduct Module.End

variable {R M N P : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [Module ℚ M]
  [AddCommGroup N] [Module R N] [Module ℚ N]
  [AddCommGroup P] [Module R P] [Module ℚ P]

theorem nilpotentExp_bilinear
    (b : M →ₗ[R] N →ₗ[R] P)
    (DM : Module.End R M) (DN : Module.End R N) (DP : Module.End R P)
    (hM : IsNilpotent DM) (hN : IsNilpotent DN) (hP : IsNilpotent DP)
    (hb : ∀ x y, DP (b x y) = b (DM x) y + b x (DN y)) (x : M) (y : N) :
    exp DP (b x y) = b (exp DM x) (exp DN y) := by
  let DL : Module.End R (M ⊗[R] N) := DM.rTensor N
  let DR : Module.End R (M ⊗[R] N) := DN.lTensor M
  have hL : IsNilpotent DL := hM.map (rTensorAlgHom R M N)
  have hR : IsNilpotent DR := hN.map (lTensorAlgHom R N M)
  have hc : Commute DL DR := by ext; simp [DL, DR]
  let m : M ⊗[R] N →ₗ[R] P := TensorProduct.lift b
  have he : exp DP ∘ₗ m = m ∘ₗ exp (DL + DR) := by
    apply Module.End.commute_exp_left_of_commute (hc.isNilpotent_add hL hR) hP
    ext x y
    simp [m, DL, DR, hb]
  have heL : exp DL = (exp DM).rTensor N := (hM.map_exp (rTensorAlgHom R M N)).symm
  have heR : exp DR = (exp DN).lTensor M := (hN.map_exp (lTensorAlgHom R N M)).symm
  have h := LinearMap.congr_fun he (x ⊗ₜ[R] y)
  simpa [m, exp_add_of_commute hc hL hR, heL, heR] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

theorem abs_finset_prod_sub_prod_le {ι : Type*} (S : Finset ι) (f g : ι → ℝ)
    {B δ : ℝ} (hB : 1 ≤ B) (hδ : 0 ≤ δ)
    (hf : ∀ i ∈ S, |f i| ≤ B) (hg : ∀ i ∈ S, |g i| ≤ B)
    (hdiff : ∀ i ∈ S, |f i - g i| ≤ δ) :
    |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| ≤ S.card * δ * B ^ S.card := by
  classical
  revert hf hg hdiff
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | @insert a S ha ih =>
    intro hf hg hdiff
    have hfS := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hgS := fun i hi => hg i (Finset.mem_insert_of_mem hi)
    have hdS := fun i hi => hdiff i (Finset.mem_insert_of_mem hi)
    have hrec := ih hfS hgS hdS
    have hprod : |∏ i ∈ S, g i| ≤ B ^ S.card := by
      rw [Finset.abs_prod]
      calc
        _ ≤ ∏ _i ∈ S, B := Finset.prod_le_prod (fun _ _ => abs_nonneg _) hgS
        _ = _ := by simp
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = |f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i) + (f a - g a) * ∏ i ∈ S, g i| := by
        congr 1
        ring
      _ ≤ |f a| * |(∏ i ∈ S, f i) - ∏ i ∈ S, g i| + |f a - g a| * |∏ i ∈ S, g i| := by
        simpa only [abs_mul] using abs_add_le
          (f a * ((∏ i ∈ S, f i) - ∏ i ∈ S, g i)) ((f a - g a) * ∏ i ∈ S, g i)
      _ ≤ B * (S.card * δ * B ^ S.card) + δ * B ^ S.card :=
        add_le_add (mul_le_mul (hf a (Finset.mem_insert_self _ _)) hrec
          (abs_nonneg _) (by linarith))
          (mul_le_mul (hdiff a (Finset.mem_insert_self _ _)) hprod (abs_nonneg _) hδ)
      _ = (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ S.card := by rw [pow_succ]; ring
      _ ≤ (S.card : ℝ) * δ * B ^ (S.card + 1) + δ * B ^ (S.card + 1) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (Nat.le_succ _)) hδ)
      _ = _ := by push_cast; ring

theorem abs_pow_sub_pow_box_bound {x y B δ : ℝ} {n s : ℕ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hx : |x| ≤ B) (hy : |y| ≤ B)
    (hxy : |x - y| ≤ δ) (hn : n ≤ s) :
    |x ^ n - y ^ n| ≤ δ * s * B ^ s := by
  apply (abs_pow_sub_pow_le x y n).trans
  apply mul_le_mul (mul_le_mul hxy (Nat.cast_le.mpr hn) (Nat.cast_nonneg _) hδ)
  · exact (pow_le_pow_left₀ (le_max_of_le_left (abs_nonneg _)) (max_le hx hy) _).trans
      (pow_le_pow_right₀ hB (by omega))
  · positivity
  · positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MixedWeightedPolynomialRename
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def polynomialTranslationPath (x : σ → ℚ) :
    MvPolynomial σ ℚ →ₐ[ℚ] Polynomial (MvPolynomial σ ℚ) :=
  MvPolynomial.aeval fun i =>
    Polynomial.C (X i) - Polynomial.C (C (x i)) * Polynomial.X

@[simp] theorem polynomialTranslationPath_C (x : σ → ℚ) (c : ℚ) :
    polynomialTranslationPath x (C c) = Polynomial.C (C c) := by
  simp [polynomialTranslationPath]

@[simp] theorem polynomialTranslationPath_X (x : σ → ℚ) (i : σ) :
    polynomialTranslationPath x (X i) =
      Polynomial.C (X i) - Polynomial.C (C (x i)) * Polynomial.X := by
  simp [polynomialTranslationPath]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.RectangularLatticeCells
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

variable {J : Type*} [Fintype J]

noncomputable def rectangularLatticePoint (a S : J → ℝ) (k : J → ℤ) : J → ℝ :=
  fun j => ((k j : ℝ) - a j) / S j

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

def scaledIntegerGrid (L : ℕ) : Set (ι → ℚ) :=
  {x | ∃ z : ι → ℤ, x = (L : ℚ) • (fun i => (z i : ℚ))}

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LieCoordinatePolynomials
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {ι X L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]

noncomputable def lieStructureConstants (e : Basis ι ℚ L) (i j k : ι) : ℚ :=
  e.repr ⁅e i, e j⁆ k

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateHeight
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.LieCoordinateScalarExtension
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LieTreeMultidegree
namespace OAI

section

namespace Erdos3

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L]

def lieTreeWeight (w : I → ℕ) : FreeMagma I → ℕ
  | .of i => w i
  | .mul a b => lieTreeWeight w a + lieTreeWeight w b

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

variable {J : Type*} [Fintype J]

noncomputable def rectangularWeight (f : (J → ℝ) → ℝ) (a S : J → ℝ) (k : J → ℤ) : ℝ :=
  f (rectangularLatticePoint a S k)

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.RectangularGridCharacter
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def gridResidueEquiv (M : ℕ) [NeZero M] : Fin M ≃ ZMod M where
  toFun k := (k.val : ZMod M)
  invFun r := ⟨r.val, ZMod.val_lt r⟩
  left_inv k := by
    apply Fin.ext
    simp only [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
  right_inv r := ZMod.natCast_zmod_val r

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreeBlockDegree
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι]

noncomputable def blockDegree (π : ι → σ) (a : ι →₀ ℕ) : σ → ℕ := by
  classical
  exact fun i => ∑ j, if π j = i then a j else 0

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MultidegreeDilationPair
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def multidegreeWeight {σ : Type*} [Fintype σ] (c a : σ → ℕ) : ℕ := ∑ i, c i * a i

theorem multidegreeWeight_add {σ : Type*} [Fintype σ] (c a b : σ → ℕ) :
    multidegreeWeight c (a + b) = multidegreeWeight c a + multidegreeWeight c b := by
  simp only [multidegreeWeight, Pi.add_apply, mul_add, Finset.sum_add_distrib]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RightCosetMetricMap
namespace OAI

section

namespace Erdos3

open scoped NNReal ENNReal

variable {G H : Type*} [Group G] [Group H]

def cosetMap (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H) (hφ : Γ ≤ Λ.comap φ) :
    (G ⧸ Γ) → (H ⧸ Λ) :=
  Quotient.map φ (fun {a b} h => by
    apply QuotientGroup.leftRel_apply.mpr
    have hm := hφ (QuotientGroup.leftRel_apply.mp h)
    simpa only [Subgroup.mem_comap, map_mul, map_inv] using hm)

@[simp] theorem cosetMap_mk (Γ : Subgroup G) (Λ : Subgroup H) (φ : G →* H)
    (hφ : Γ ≤ Λ.comap φ) (x : G) :
    cosetMap Γ Λ φ hφ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSubquotientEquiv
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem real_baseChange_iSup {I : Sort*} {L : Type*} [AddCommGroup L] [Module ℚ L]
    (P : I → Submodule ℚ L) :
    (⨆ i, P i).baseChange ℝ = ⨆ i, (P i).baseChange ℝ := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro x ⟨y, hy, rfl⟩
    apply Submodule.iSup_induction P hy
      (motive := fun y => (1 : ℝ) ⊗ₜ[ℚ] y ∈ ⨆ i, (P i).baseChange ℝ)
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i (Submodule.tmul_mem_baseChange_of_mem 1 hy)
    · simp only [TensorProduct.tmul_zero, Submodule.zero_mem]
    · intro y z hy hz
      rw [TensorProduct.tmul_add]
      exact Submodule.add_mem _ hy hz
  · apply iSup_le
    intro i
    exact Submodule.baseChange_mono ℝ (le_iSup P i)

theorem real_restrictScalars_iSup {I : Sort*} {L : Type*} [AddCommGroup L]
    [Module ℚ L] [Module ℝ L] [IsScalarTower ℚ ℝ L] (P : I → Submodule ℝ L) :
    (⨆ i, P i).restrictScalars ℚ = ⨆ i, (P i).restrictScalars ℚ := by
  apply le_antisymm
  · intro x hx
    change x ∈ ⨆ i, P i at hx
    apply Submodule.iSup_induction P hx
      (motive := fun y => y ∈ ⨆ i, (P i).restrictScalars ℚ)
    · intro i y hy
      exact Submodule.mem_iSup_of_mem i hy
    · exact Submodule.zero_mem _
    · intro y z hy hz
      exact Submodule.add_mem _ hy hz
  · apply iSup_le
    intro i x hx
    exact Submodule.mem_iSup_of_mem i hx

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realification_subtype_injective (P : Submodule ℚ V) :
    Function.Injective (P.subtype.baseChange ℝ) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) P.subtype
    (fun _ _ h => Subtype.ext h)

noncomputable def realificationSubmoduleEquiv (P : Submodule ℚ V) :
    (ℝ ⊗[ℚ] P) ≃ₗ[ℝ] P.baseChange ℝ :=
  LinearEquiv.ofInjective (P.subtype.baseChange ℝ) (realification_subtype_injective P)

@[simp] theorem realificationSubmoduleEquiv_coe (P : Submodule ℚ V) (x : ℝ ⊗[ℚ] P) :
    (realificationSubmoduleEquiv P x : ℝ ⊗[ℚ] V) = P.subtype.baseChange ℝ x := rfl

@[simp] theorem realificationSubmoduleEquiv_tmul (P : Submodule ℚ V) (r : ℝ) (x : P) :
    (realificationSubmoduleEquiv P (r ⊗ₜ[ℚ] x) : ℝ ⊗[ℚ] V) = r ⊗ₜ[ℚ] (x : V) := rfl

end Erdos3

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

theorem realLieBasis_structure (e : Basis ι ℚ L) (i j k : ι) :
    (e.baseChange ℝ).repr ⁅e.baseChange ℝ i, e.baseChange ℝ j⁆ k =
      (lieStructureConstants e i j k : ℝ) := by
  simp [Basis.baseChange_apply, LieAlgebra.ExtendScalars.bracket_tmul,
    Basis.baseChange_repr_tmul, Algebra.smul_def, lieStructureConstants]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealifiedTripleCoordinates
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

def tripleNeutral : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.2.1 + x.2.2 - x.1
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_add, smul_sub]

def tripleLeft : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.1 - x.2.2
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_sub]

def tripleRight : (L × L × L) →ₗ[ℚ] L where
  toFun x := x.1 - x.2.1
  map_add' x y := by dsimp; abel
  map_smul' r x := by simp [smul_sub]

def tripleAssemble (a b c : L) : L × L × L := (a + b + c, a + b, a + c)

@[simp] theorem tripleNeutral_assemble (a b c : L) : tripleNeutral (tripleAssemble a b c) = a := by
  change a + b + (a + c) - (a + b + c) = a
  abel

@[simp] theorem tripleLeft_assemble (a b c : L) : tripleLeft (tripleAssemble a b c) = b := by
  change a + b + c - (a + c) = b
  abel

@[simp] theorem tripleRight_assemble (a b c : L) : tripleRight (tripleAssemble a b c) = c := by
  change a + b + c - (a + b) = c
  abel

theorem tripleAssemble_decompose (x : L × L × L) :
    tripleAssemble (tripleNeutral x) (tripleLeft x) (tripleRight x) = x := by
  apply Prod.ext
  · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.2) + (x.1 - x.2.1) = x.1
    abel
  · apply Prod.ext
    · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.2) = x.2.1
      abel
    · change (x.2.1 + x.2.2 - x.1) + (x.1 - x.2.1) = x.2.2
      abel

omit [LieAlgebra ℚ L] in
theorem tripleAssemble_lie (a b c a' b' c' : L)
    (hbb : ⁅b, b'⁆ = 0) (hbc : ⁅b, c'⁆ = 0)
    (hcb : ⁅c, b'⁆ = 0) (hcc : ⁅c, c'⁆ = 0) :
    ⁅tripleAssemble a b c, tripleAssemble a' b' c'⁆ =
      tripleAssemble ⁅a, a'⁆ (⁅a, b'⁆ + ⁅b, a'⁆) (⁅a, c'⁆ + ⁅c, a'⁆) := by
  apply Prod.ext
  · change ⁅a + b + c, a' + b' + c'⁆ = _
    simp only [LieRing.add_lie, LieRing.lie_add, hbb, hbc, hcb, hcc, add_zero]
    change _ = ⁅a, a'⁆ + (⁅a, b'⁆ + ⁅b, a'⁆) + (⁅a, c'⁆ + ⁅c, a'⁆)
    abel
  · apply Prod.ext
    · change ⁅a + b, a' + b'⁆ = ⁅a, a'⁆ + (⁅a, b'⁆ + ⁅b, a'⁆)
      simp only [LieRing.add_lie, LieRing.lie_add, hbb, add_zero]
      abel
    · change ⁅a + c, a' + c'⁆ = ⁅a, a'⁆ + (⁅a, c'⁆ + ⁅c, a'⁆)
      simp only [LieRing.add_lie, LieRing.lie_add, hcc, add_zero]
      abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.SquarefreeBracketHeight
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem lie_mem_real_baseChange {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (P Q W : Submodule ℚ L)
    (h : ∀ a ∈ P, ∀ b ∈ Q, ⁅a, b⁆ ∈ W)
    {a b : ℝ ⊗[ℚ] L} (ha : a ∈ P.baseChange ℝ) (hb : b ∈ Q.baseChange ℝ) :
    ⁅a, b⁆ ∈ W.baseChange ℝ := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul t y =>
      change (r * t) ⊗ₜ[ℚ] ⁅(x : L), (y : L)⁆ ∈ W.baseChange ℝ
      exact Submodule.tmul_mem_baseChange_of_mem _ (h x x.property y y.property)
    | add y z hy hz =>
      simpa only [map_add, lie_add] using (W.baseChange ℝ).add_mem hy hz
  | add x z hx hz =>
    simpa only [map_add, add_lie] using (W.baseChange ℝ).add_mem hx hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTripleLayers
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem multidegreeWeight_le_sum {σ : Type*} [Fintype σ]
    (c a : σ → ℕ) (hc : ∀ i, c i ≤ 1) : multidegreeWeight c a ≤ ∑ i, a i := by
  apply Finset.sum_le_sum
  intro i _
  simpa only [one_mul] using Nat.mul_le_mul_right (a i) (hc i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPrimitive
namespace OAI

section

namespace Erdos3

open Polynomial

variable {A : Type*} [CommRing A] [Algebra ℚ A]

noncomputable def polynomialPrimitive (p : Polynomial A) : Polynomial A :=
  p.sum fun n a => monomial (n + 1) (((n + 1 : ℕ) : ℚ)⁻¹ • a)

@[simp] theorem polynomialPrimitive_derivative (p : Polynomial A) :
    (polynomialPrimitive p).derivative = p := by
  classical
  have hcoef (n : ℕ) (a : A) :
      (((n + 1 : ℕ) : ℚ)⁻¹ • a) * ((n : A) + 1) = a := by
    rw [← Nat.cast_add_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
    rw [mul_inv_cancel₀ (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)), one_smul]
  simp only [polynomialPrimitive, sum_def, derivative_sum, derivative_monomial_succ, hcoef]
  exact sum_monomial_eq p

@[simp] theorem polynomialPrimitive_eval_zero (p : Polynomial A) :
    (polynomialPrimitive p).eval 0 = 0 := by
  classical
  simp only [polynomialPrimitive, sum_def, eval_finsetSum, eval_monomial]
  simp

omit [Algebra ℚ A] in
theorem polynomial_eq_of_derivative_of_eval_zero [IsAddTorsionFree A]
    {p q : Polynomial A} (hderiv : p.derivative = q.derivative)
    (hzero : p.eval 0 = q.eval 0) : p = q := by
  have hd : (p - q).derivative = 0 := by rw [derivative_sub, hderiv, sub_self]
  have hconst := eq_C_of_derivative_eq_zero hd
  have hz : (p - q).coeff 0 = 0 := by
    simpa only [← coeff_zero_eq_eval_zero, coeff_sub, sub_eq_zero] using hzero
  rw [hz, map_zero] at hconst
  exact sub_eq_zero.mp hconst

theorem polynomialPrimitive_unique [IsAddTorsionFree A]
    {p q : Polynomial A} (hderiv : q.derivative = p) (hzero : q.eval 0 = 0) :
    polynomialPrimitive p = q := by
  apply polynomial_eq_of_derivative_of_eval_zero
  · simpa using hderiv.symm
  · simpa using hzero.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationSeries
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

@[ext] structure PolynomialTranslationGroup (σ : Type*) where
  base : σ → ℚ
  polynomial : MvPolynomial σ ℚ

namespace PolynomialTranslationGroup

noncomputable instance instOne : One (PolynomialTranslationGroup σ) where
  one := ⟨0, 0⟩

end PolynomialTranslationGroup
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.VectorAlgebraicMajorDecomposition
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {R B : Type*} [CommRing R]

@[ext] structure PolynomialTranslationGroupOver (R B : Type*) [CommRing R] where
  base : B → R
  polynomial : MvPolynomial B R

namespace PolynomialTranslationGroupOver

noncomputable instance instOne : One (PolynomialTranslationGroupOver R B) where
  one := ⟨0, 0⟩

end PolynomialTranslationGroupOver

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorWeightedDegreeTools
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ ι R : Type*} [CommRing R]

noncomputable def coordinateShearHom (i : τ) (f : σ → τ) (Q : MvPolynomial σ R) :
    MvPolynomial τ R →ₐ[R] MvPolynomial τ R := by
  classical
  exact aeval (Function.update X i (X i + rename f Q))

theorem coordinateShearHom_X [DecidableEq τ] (i : τ) (f : σ → τ) (Q : MvPolynomial σ R) (j : τ) :
    coordinateShearHom i f Q (X j) =
      Function.update (X : τ → MvPolynomial τ R) i (X i + rename f Q) j := by
  classical
  by_cases h : j = i
  · subst j
    simp only [coordinateShearHom, MvPolynomial.aeval_X, Function.update_self]
  · simp [coordinateShearHom, Function.update, h]

theorem coordinateShearHom_rename (i : τ) (f : σ → τ) (Q : MvPolynomial σ R)
    (g : ι → τ) (hg : ∀ j, g j ≠ i) (P : MvPolynomial ι R) :
    coordinateShearHom i f Q (rename g P) = rename g P := by
  classical
  rw [coordinateShearHom, MvPolynomial.aeval_rename]
  have he : (Function.update (X : τ → MvPolynomial τ R) i (X i + rename f Q)) ∘ g = X ∘ g := by
    funext j
    exact Function.update_of_ne (hg j) _ _
  rw [he, ← MvPolynomial.rename_eq_aeval]

theorem coordinateShearHom_comp_neg (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) :
    (coordinateShearHom i f Q).comp (coordinateShearHom i f (-Q)) = AlgHom.id R _ := by
  classical
  apply MvPolynomial.algHom_ext
  intro j
  change coordinateShearHom i f Q (coordinateShearHom i f (-Q) (X j)) = X j
  rw [coordinateShearHom_X]
  by_cases h : j = i
  · subst j
    rw [Function.update_self, map_add, coordinateShearHom_X, Function.update_self,
      coordinateShearHom_rename i f Q f hf, map_neg]
    exact add_neg_cancel_right (X i) (rename f Q)
  · rw [Function.update_of_ne h, coordinateShearHom_X, Function.update_of_ne h]

noncomputable def coordinateShearEquiv (i : τ) (f : σ → τ) (hf : ∀ j, f j ≠ i)
    (Q : MvPolynomial σ R) : MvPolynomial τ R ≃ₐ[R] MvPolynomial τ R :=
  AlgEquiv.ofAlgHom (coordinateShearHom i f Q) (coordinateShearHom i f (-Q))
    (coordinateShearHom_comp_neg i f hf Q)
    (by simpa only [neg_neg] using coordinateShearHom_comp_neg i f hf (-Q))

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialTranslationActionCompatibility
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {σ : Type*}

noncomputable def integerCoefficientPolynomials (σ : Type*) : Subalgebra ℤ (MvPolynomial σ ℚ) :=
  (MvPolynomial.mapAlgHom (Int.castRingHom ℚ).toIntAlgHom).range

theorem mem_integerCoefficientPolynomials (P : MvPolynomial σ ℚ) :
    P ∈ integerCoefficientPolynomials σ ↔ ∃ Q : MvPolynomial σ ℤ,
      MvPolynomial.map (Int.castRingHom ℚ) Q = P := Iff.rfl

theorem integerCoefficientPolynomials_X (i : σ) :
    (X i : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ :=
  ⟨X i, MvPolynomial.map_X _ _⟩

theorem integerCoefficientPolynomials_C (z : ℤ) :
    (C (z : ℚ) : MvPolynomial σ ℚ) ∈ integerCoefficientPolynomials σ :=
  ⟨C z, MvPolynomial.map_C _ _⟩

theorem integerPolynomialHom_preserves
    (F : MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial σ ℚ)
    (hF : ∀ i, F (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    F P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  clear hP
  induction Q using MvPolynomial.induction_on with
  | C z =>
    rw [MvPolynomial.map_C]
    change F (C (z : ℚ)) ∈ integerCoefficientPolynomials σ
    rw [show F (C (z : ℚ)) = C (z : ℚ) from F.commutes _]
    exact integerCoefficientPolynomials_C z
  | add P Q hP hQ =>
    simpa only [map_add] using (integerCoefficientPolynomials σ).add_mem hP hQ
  | mul_X P i hP =>
    simpa only [map_mul, MvPolynomial.map_X] using
      (integerCoefficientPolynomials σ).mul_mem hP (hF i)

theorem integerPolynomialDerivation_preserves
    (D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))
    (hD : ∀ i, D (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    D P ∈ integerCoefficientPolynomials σ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  clear hP
  induction Q using MvPolynomial.induction_on with
  | C z =>
    simp only [MvPolynomial.map_C, MvPolynomial.derivation_C]
    exact (integerCoefficientPolynomials σ).zero_mem
  | add P Q hP hQ =>
    simpa only [map_add] using (integerCoefficientPolynomials σ).add_mem hP hQ
  | mul_X P i hP =>
    rw [map_mul, MvPolynomial.map_X, D.leibniz, smul_eq_mul, smul_eq_mul]
    exact (integerCoefficientPolynomials σ).add_mem
      ((integerCoefficientPolynomials σ).mul_mem ⟨P, rfl⟩ (hD i))
      ((integerCoefficientPolynomials σ).mul_mem (integerCoefficientPolynomials_X i) hP)

theorem integerPolynomialDerivation_pow
    (D : Derivation ℚ (MvPolynomial σ ℚ) (MvPolynomial σ ℚ))
    (hD : ∀ i, D (X i) ∈ integerCoefficientPolynomials σ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) (k : ℕ) :
    (D.toLinearMap ^ k) P ∈ integerCoefficientPolynomials σ := by
  induction k with
  | zero => exact hP
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact integerPolynomialDerivation_preserves D hD ih

end Erdos3


namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*}

theorem integerCoefficientPolynomials_rename (f : σ → τ)
    {P : MvPolynomial σ ℚ} (hP : P ∈ integerCoefficientPolynomials σ) :
    rename f P ∈ integerCoefficientPolynomials τ := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  exact ⟨rename f Q, MvPolynomial.map_rename _ _ _⟩

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TranslationPhaseQuotient
namespace OAI


namespace Erdos3

open _root_.MvPolynomial

variable {B U : Type*}

theorem eval_integer_polynomial_real (Q : MvPolynomial B ℤ) (β : B → ℤ) :
    eval (fun i => (β i : ℝ)) (MvPolynomial.map (Int.castRingHom ℝ) Q) =
      (eval β Q : ℝ) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq, Int.cast_add]
  | mul_X p i hp => simp only [map_mul, map_X, eval_X, hp, Int.cast_mul]

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.FactorialIntegerScalars
namespace OAI

section

namespace Erdos3

theorem rat_nat_div_integer_of_dvd {m n : ℕ} (h : n ∣ m) :
    ∃ z : ℤ, (m : ℚ) / n = (z : ℚ) := by
  obtain ⟨d, rfl⟩ := h
  by_cases hn : n = 0
  · exact ⟨0, by simp [hn]⟩
  · exact ⟨d, by push_cast; field_simp⟩

theorem factorial_exp_scalar_integer (s k : ℕ) (hk : k ≤ s) :
    ∃ z : ℤ, (k.factorial : ℚ)⁻¹ * (s.factorial : ℚ) ^ k = (z : ℚ) := by
  cases k with
  | zero => exact ⟨1, by simp⟩
  | succ k =>
    have hd : (k + 1).factorial ∣ s.factorial ^ (k + 1) := by
      rw [pow_succ']
      exact (Nat.factorial_dvd_factorial hk).trans (Nat.dvd_mul_right _ _)
    obtain ⟨z, hz⟩ := rat_nat_div_integer_of_dvd hd
    exact ⟨z, by simpa only [Nat.cast_pow, div_eq_mul_inv, mul_comm] using hz⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedLinearPolynomialRestriction
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial
open scoped BigOperators

variable {σ τ : Type*} [Fintype σ] [Fintype τ]

noncomputable def linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) : MvPolynomial τ ℚ := by
  classical
  exact ∑ j, A (Pi.single j 1) i • X j

noncomputable def polynomialLinearRestriction
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) :
    MvPolynomial σ ℚ →ₐ[ℚ] MvPolynomial τ ℚ :=
  aeval (linearCoordinatePolynomial A)

omit [Fintype σ] in
theorem linearMap_apply_sum_coordinates [DecidableEq τ]
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (i : σ) :
    ∑ j, A (Pi.single j 1) i * x j = A x i := by
  classical
  have hx : (∑ j, x j • Pi.single j (1 : ℚ)) = x := by
    ext j
    simp [Pi.single_apply]
  conv_rhs => rw [← hx]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

omit [Fintype σ] in
@[simp] theorem polynomialLinearRestriction_X
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (i : σ) :
    polynomialLinearRestriction A (X i) = linearCoordinatePolynomial A i := by
  simp [polynomialLinearRestriction]

omit [Fintype σ] in
@[simp] theorem polynomialLinearRestriction_C
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (r : ℚ) :
    polynomialLinearRestriction A (C r) = C r := by
  simp [polynomialLinearRestriction]

omit [Fintype σ] in
@[simp] theorem eval_linearCoordinatePolynomial
    (A : (τ → ℚ) →ₗ[ℚ] (σ → ℚ)) (x : τ → ℚ) (i : σ) :
    eval x (linearCoordinatePolynomial A i) = A x i := by
  classical
  simp only [linearCoordinatePolynomial, map_sum, ← C_mul', map_mul, eval_C, eval_X]
  exact linearMap_apply_sum_coordinates A x i

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LinearBCHAbelian
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem linearMap_baseChange_lie_eq_zero {L V : Type*} [LieRing L] [LieAlgebra ℚ L]
    [AddCommGroup V] [Module ℚ V] (f : L →ₗ[ℚ] V)
    (hf : ∀ x y : L, f ⁅x, y⁆ = 0) (a b : ℝ ⊗[ℚ] L) :
    f.baseChange ℝ ⁅a, b⁆ = 0 := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.baseChange_tmul, hf,
        TensorProduct.tmul_zero]
    | add b c hb hc => rw [lie_add, map_add, hb, hc, add_zero]
  | add a b ha hb => rw [add_lie, map_add, ha, hb, add_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FactorwiseBCHCovers
namespace OAI

section

namespace Erdos3

open Module

variable {α : Type*} {M : α → Type*} [∀ a, LieRing (M a)]
  [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

variable [Fintype α] {κ : α → Type*} [∀ a, Fintype (κ a)]

theorem pi_basis_equivFun_symm_apply (f : ∀ a, Basis (κ a) ℚ (M a))
    (x : (Σ a, κ a) → ℚ) (a : α) :
    (Pi.basis f).equivFun.symm x a = (f a).equivFun.symm (fun i => x ⟨a, i⟩) := by
  apply (f a).equivFun.injective
  funext i
  change (Pi.basis f).equivFun ((Pi.basis f).equivFun.symm x) ⟨a, i⟩ = _
  simp only [LinearEquiv.apply_symm_apply]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem baseChange_mem_of_mapsTo {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W] (P : Submodule ℚ V) (Q : Submodule ℚ W)
    (f : V →ₗ[ℚ] W) (hf : ∀ x ∈ P, f x ∈ Q) {x : ℝ ⊗[ℚ] V}
    (hx : x ∈ P.baseChange ℝ) : f.baseChange ℝ x ∈ Q.baseChange ℝ := by
  have hm : P.baseChange ℝ ≤ (Q.baseChange ℝ).comap (f.baseChange ℝ) := by
    rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    exact Submodule.tmul_mem_baseChange_of_mem 1 (hf a ha)
  exact hm hx

variable {ι : Type*} {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]

noncomputable def realProductSingle (i : ι) :
    (ℝ ⊗[ℚ] L i) →ₗ[ℝ] (ℝ ⊗[ℚ] (∀ j, L j)) := by
  classical
  exact (LinearMap.single ℚ L i).baseChange ℝ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.TotalDegreeSplitDownsets
namespace OAI

section

namespace Erdos3

open scoped BigOperators

def totalDegreeSplitBound (s : ℕ) (b : Bool) : Fin 2 → ℕ :=
  ![if b then s else 0, if b then s - 1 else s]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*}

abbrev ReplicatedIndex (bound : σ → ℕ) := Σ i, Fin (bound i)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.FiniteDensityMassBound
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem sum_support_eq_tsum {X : Type*} (w : X → ℝ) (S : Finset X)
    (hw : ∀ x ∉ S, w x = 0) : (∑ x : S, w x.val) = ∑' x, w x := by
  calc
    _ = ∑ x ∈ S, w x := Finset.sum_coe_sort S w
    _ = _ := (hasSum_sum_of_ne_finset_zero hw).tsum_eq.symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RepresentativeWindowPatch
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal

structure RepresentativeWindow where
  center : ℝ
  value : ℝ → ℝ
  lip : ℝ≥0
  nonneg : ∀ x, 0 ≤ value x
  le_one : ∀ x, value x ≤ 1
  interior : ∀ x, value x ≠ 0 → 0 < x ∧ x < 1
  small : ∀ x, value x ≠ 0 → |x - center| < 1 / 4
  lipschitz : LipschitzWith lip value

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ R : Type*} [CommRing R]

theorem sumExponent_injective (β : τ →₀ ℕ) :
    Function.Injective (fun α : σ →₀ ℕ => α.sumElim β) := by
  intro α γ h
  ext i
  exact congrArg (fun a : σ ⊕ τ →₀ ℕ => a (Sum.inl i)) h

noncomputable def polynomialSlotCoefficient (β : τ →₀ ℕ) :
    MvPolynomial (σ ⊕ τ) R →ₗ[R] MvPolynomial σ R :=
  (MvPolynomial.basisMonomials σ R).repr.symm.toLinearMap.comp
    ((Finsupp.lcomapDomain (fun α : σ →₀ ℕ => α.sumElim β) (sumExponent_injective β)).comp
      (MvPolynomial.basisMonomials (σ ⊕ τ) R).repr.toLinearMap)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchShearOrbitConverse
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ τ : Type*} {s d : ℕ}

noncomputable def symbolicShearPrefixSubstitution (i : Fin d) :
    τ ⊕ Fin d → MvPolynomial (τ ⊕ Fin i.val) ℝ :=
  Sum.elim (fun a => X (Sum.inl a))
    (fun j => if h : j.val < i.val then X (Sum.inr ⟨j.val, h⟩) else 0)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearParameterBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module
open scoped NNReal TensorProduct

variable {σ : Type*} [Fintype σ] (w : σ → ℕ)

def polynomialShearDisplacementBound (s d : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  s * (1 + d * ((s + 1) * (d + 1) ^ s : ℕ) * s) ^ s * B ^ s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

section

namespace Erdos3

def centeredFundamentalBox {J : Type*} (Q K : ℕ) (center z : J → ℤ) : Prop :=
  ∀ j, center j - (Q : ℤ) * K ≤ z j ∧ z j < center j + ((Q : ℤ) + 1) * K

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerAffineSubstitution
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ τ : Type*} [Fintype τ]

noncomputable def integerAffinePolynomial (A : σ → τ → ℤ) (b : σ → ℤ) (i : σ) :
    MvPolynomial τ ℚ :=
  MvPolynomial.C (b i : ℚ) + ∑ j, MvPolynomial.C (A i j : ℚ) * MvPolynomial.X j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SquareBasisGeometry
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev QuotientTopBasisIndex (s : ℕ) (ω : ι → ℕ) := {i : ι // ¬ s + 1 ≤ ω i}

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.CurrentBracketInductionStep
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

section General

variable {R L ι : Type*} [Field R] [LieRing L] [LieAlgebra R L]

def BasisHomogeneousBrackets (b : Basis ι R L) (w : ι → ℕ) : Prop :=
  ∀ i j k, w k ≠ w i + w j → b.repr ⁅b i, b j⁆ k = 0

end General

theorem BasisHomogeneousBrackets.baseChange {L ι : Type*} [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (w : ι → ℕ) (hb : BasisHomogeneousBrackets b w) :
    BasisHomogeneousBrackets (b.baseChange ℝ) w := by
  intro i j k hk
  rw [Basis.baseChange_apply, Basis.baseChange_apply,
    LieAlgebra.ExtendScalars.bracket_tmul, one_mul, Basis.baseChange_repr_tmul, hb i j k hk]
  exact zero_smul ℚ (1 : ℝ)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FreeNilpotentLieAlgebra
namespace OAI

section

namespace Erdos3

variable (X : Type*) (s : ℕ)

def FreeNilpotentLieAlgebra :=
  FreeLieAlgebra ℚ X ⧸ LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s

namespace FreeNilpotentLieAlgebra

noncomputable instance instLieRing : LieRing (FreeNilpotentLieAlgebra X s) :=
  inferInstanceAs (LieRing (FreeLieAlgebra ℚ X ⧸
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s))

noncomputable instance instLieAlgebra : LieAlgebra ℚ (FreeNilpotentLieAlgebra X s) :=
  inferInstanceAs (LieAlgebra ℚ (FreeLieAlgebra ℚ X ⧸
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s))

variable {X s} {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lowerCentralSeries_le_lift_ker (f : X → L)
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :
    LieModule.lowerCentralSeries ℚ (FreeLieAlgebra ℚ X) (FreeLieAlgebra ℚ X) s ≤
      (FreeLieAlgebra.lift ℚ f).ker := by
  apply LieIdeal.map_eq_bot_iff.mp
  apply bot_unique
  rw [← hnil]
  exact LieIdeal.map_lowerCentralSeries_le s

end FreeNilpotentLieAlgebra

end Erdos3

end

end OAI
end


