-- Prove2me | Definitions.Def_OAIE3v2B068
-- name    : OAIE3v2B068
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:15:30.98935+00:00
-- url     : https://prove2.me/theorems/84a15dc7-aa28-4797-a394-966fe6f1c055
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 69 of 311
-- statement:
--   Definitions bundle 69 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B038`, `OAIE3v2B039`, `OAIE3v2B045` of this split.
--
--   Modules: `Estimates/DilationPairFiltration.lean`, `Estimates/FilteredLieTree.lean`, `Estimates/LieFiniteProduct.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/MultidegreeDilationPair.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/ShiftedAdaptedIdeal.lean`, `Estimates/SquarefreePermutationFiltration.lean`, `FixedDensity/OrderedRemoval.lean`, `Geometry/LieCoordinateSmooth.lean`, `Nilpotent/BCHChartCutoffSmooth.lean`, `Nilpotent/BCHConjugationLinear.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHQuotientLocalIsometry.lean`, `Nilpotent/BCHSubgroupGridExistence.lean`, `Nilpotent/DegreeRankLieBrackets.lean`, `Nilpotent/LieBCHContinuity.lean`, `Polynomial/AdaptedBinomialFactorization.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/DegreeRankLayers.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/ShiftedPolynomialIdeals.lean`, `Polynomial/SquarefreePolynomialQuotient.lean`, `Polynomial/WeightedPolynomialRestriction.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B038
import Definitions.Def_OAIE3v2B039
import Definitions.Def_OAIE3v2B045

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.LieBCHContinuity
namespace OAI

section

namespace Erdos3

noncomputable def bchWordCoefficients (s : ℕ) : FreeSemigroup (Fin 2) →₀ ℚ :=
  (freeLieWordExpansion (bchLiePolynomial s)).coeff

noncomputable def bchBracketSupport (s : ℕ) : Finset (FreeSemigroup (Fin 2)) :=
  (bchWordCoefficients s).support

noncomputable def bchBracketCoefficient (s : ℕ) (w : FreeSemigroup (Fin 2)) : ℚ :=
  bchWordCoefficients s w / w.length

theorem lieBCH_bracket_formula {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (s : ℕ) (a b : L) :
    lieBCH s a b = ∑ w ∈ bchBracketSupport s, bchBracketCoefficient s w • dynkinWord ![a, b] w := by
  rw [lieBCH, ← dynkinProjection_lift]
  change (bchWordCoefficients s).sum (fun w r => r • ((w.length : ℚ)⁻¹ • dynkinWord ![a, b] w)) = _
  simp only [Finsupp.sum, bchBracketSupport, bchBracketCoefficient, smul_smul, div_eq_mul_inv]

end Erdos3

end

section

namespace Erdos3

open Module

section General

variable {X Y L : Type*} [TopologicalSpace Y] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]

theorem continuous_lieBCH
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) (s : ℕ) :
    Continuous (fun z : L × L => lieBCH s z.1 z.2) := by
  simp only [lieBCH_bracket_formula]
  apply continuous_finsetSum
  intro w _
  apply Continuous.const_smul
  exact continuous_dynkinWord hlie (fun i (z : L × L) => ![z.1, z.2] i)
    (by intro i; fin_cases i; exact continuous_fst; exact continuous_snd) w

end General

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubgroupGridExistence
namespace OAI

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DilationPairFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairLayer (q : ℚ) (n : ℕ) : Submodule ℚ (L × L) :=
  scaledPairLayer (F.layer n) (F.layer (n + 1)) (q ^ n)

@[simp] theorem mem_dilationPairLayer (q : ℚ) (n : ℕ) (x : L × L) :
    x ∈ F.dilationPairLayer q n ↔
      x.1 ∈ F.layer n ∧ x.2 ∈ F.layer n ∧ x.1 - q ^ n • x.2 ∈ F.layer (n + 1) := Iff.rfl

theorem dilationPairLayer_antitone (q : ℚ) : Antitone (F.dilationPairLayer q) := by
  intro i j hij x hx
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact hx
  refine ⟨F.antitone hij hx.1, F.antitone hij hx.2.1, ?_⟩
  change x.1 - q ^ i • x.2 ∈ F.layer (i + 1)
  have hdiff : x.1 - q ^ i • x.2 = (x.1 - q ^ j • x.2) + (q ^ j - q ^ i) • x.2 := by
    rw [sub_smul]
    abel
  rw [hdiff]
  exact (F.layer (i + 1)).add_mem
    (F.antitone (Nat.add_le_add_right hij 1) hx.2.2)
    ((F.layer (i + 1)).smul_mem _ (F.antitone (Nat.succ_le_of_lt hlt) hx.2.1))

theorem dilationPairLayer_lie_mem (q : ℚ) {i j : ℕ} {x y : L × L}
    (hx : x ∈ F.dilationPairLayer q i) (hy : y ∈ F.dilationPairLayer q j) :
    ⁅x, y⁆ ∈ F.dilationPairLayer q (i + j) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - q ^ (i + j) • ⁅x.2, y.2⁆ ∈ F.layer (i + j + 1)
  have hdiff : ⁅x.1, y.1⁆ - q ^ (i + j) • ⁅x.2, y.2⁆ =
      ⁅x.1 - q ^ i • x.2, y.1⁆ + q ^ i • ⁅x.2, y.1 - q ^ j • y.2⁆ := by
    simp only [sub_lie, lie_sub, smul_lie, lie_smul, smul_sub, smul_smul, pow_add]
    abel
  rw [hdiff]
  exact (F.layer (i + j + 1)).add_mem
    (by simpa only [scaledPairDifference_apply, Nat.add_right_comm i 1 j] using F.lie_mem hx.2.2 hy.1)
    ((F.layer (i + j + 1)).smul_mem _
      (by simpa only [scaledPairDifference_apply, Nat.add_assoc] using F.lie_mem hx.2.1 hy.2.2))

theorem dilationPairLayer_terminal (q : ℚ) : F.dilationPairLayer q (s + 1) = ⊥ := by
  apply bot_unique
  intro x hx
  change x = 0
  apply Prod.ext
  · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.1)
  · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.2.1)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def dilationPairSubalgebra (q : ℚ) : LieSubalgebra ℚ (L × L) :=
  { F.dilationPairLayer q 1 with
    lie_mem' := fun hx hy => F.dilationPairLayer_antitone q (by decide : 1 ≤ 1 + 1)
      (F.dilationPairLayer_lie_mem q hx hy) }

@[simp] theorem mem_dilationPairSubalgebra (q : ℚ) (x : L × L) :
    x ∈ F.dilationPairSubalgebra q ↔ x.1 - q • x.2 ∈ F.layer 2 := by
  change x ∈ F.dilationPairLayer q 1 ↔ _
  simp only [mem_dilationPairLayer, F.one_eq_top, Submodule.mem_top, pow_one, true_and]

def dilationPairFiltration (q : ℚ) : NilpotentLieFiltration (F.dilationPairSubalgebra q) s where
  layer n := (F.dilationPairLayer q n).comap (F.dilationPairSubalgebra q).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.dilationPairLayer_antitone q h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.dilationPairLayer_lie_mem q hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × L)
    have h : x.val ∈ F.dilationPairLayer q (s + 1) := hx
    simpa only [F.dilationPairLayer_terminal, Submodule.mem_bot] using h

@[simp] theorem mem_dilationPairFiltration_layer (q : ℚ) (n : ℕ)
    (x : F.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairFiltration q).layer n ↔ x.val ∈ F.dilationPairLayer q n := Iff.rfl

end Erdos3.NilpotentLieFiltration

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

namespace FilteredLieTree

variable {F : NilpotentLieFiltration L s}

@[simp] theorem eval_leaf {d : ℕ} (hd : 0 < d) (x : L) (hx : x ∈ F.layer d) :
    eval (leaf hd x hx) = x := rfl

@[simp] theorem eval_bracket {d e r t : ℕ} (a : FilteredLieTree F d r)
    (b : FilteredLieTree F e t) : eval (bracket a b) = ⁅eval a, eval b⁆ := rfl

theorem rank_le_degree {d r : ℕ} (a : FilteredLieTree F d r) : r ≤ d := by
  induction a with
  | leaf hd x hx => omega
  | bracket a b ha hb => omega

theorem eval_mem {d r : ℕ} (a : FilteredLieTree F d r) : a.eval ∈ F.layer d := by
  induction a with
  | leaf hd x hx => exact hx
  | bracket a b ha hb => exact F.lie_mem ha hb

end FilteredLieTree

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

variable {R : Type*} [CommRing R] [∀ a, LieAlgebra R (M a)]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

namespace NilpotentLieFiltration

variable [∀ a, LieAlgebra ℚ (M a)] {s : ℕ}

def pi (F : ∀ a, NilpotentLieFiltration (M a) s) : NilpotentLieFiltration (∀ a, M a) s where
  layer n := Submodule.pi Set.univ (fun a => (F a).layer n)
  antitone _ _ h := Submodule.pi_mono (fun a _ => (F a).antitone h)
  one_eq_top := by simp only [one_eq_top, Submodule.pi_top]
  lie_mem {i j x y} hx hy a ha := (F a).lie_mem (hx a ha) (hy a ha)
  terminal := by simp only [terminal, Submodule.pi_univ_bot]

@[simp] theorem mem_pi_layer (F : ∀ a, NilpotentLieFiltration (M a) s) (n : ℕ) (x : ∀ a, M a) :
    x ∈ (pi F).layer n ↔ ∀ a, x a ∈ (F a).layer n := by simp [pi, Submodule.mem_pi]

end NilpotentLieFiltration

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

variable [LieAlgebra ℚ L]

variable [IsScalarTower ℚ ℝ L]

theorem contDiff_lieBCH_coordinates (e : Basis ι ℝ L) (s : ℕ) (f g : E → L)
    (hf : ∀ i, ContDiff ℝ n (fun x => e.repr (f x) i))
    (hg : ∀ i, ContDiff ℝ n (fun x => e.repr (g x) i)) (k : ι) :
    ContDiff ℝ n (fun x => e.repr (lieBCH s (f x) (g x)) k) := by
  change ContDiff ℝ n (fun x => e.coord k (lieBCH s (f x) (g x)))
  simp only [lieBCH_bracket_formula, map_sum, LinearMap.map_smul_of_tower,
    Algebra.smul_def, Basis.coord_apply]
  apply ContDiff.sum
  intro w _
  apply contDiff_const.mul
  exact contDiff_dynkinWord_coordinates e (fun i x => ![f x, g x] i)
    (by intro i k; fin_cases i; exact hf k; exact hg k) w k

theorem contDiff_coordinateBCH (e : Basis ι ℝ L) (s : ℕ) :
    ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2))) := by
  apply contDiff_pi.mpr
  intro k
  apply contDiff_lieBCH_coordinates e s
  · intro i
    change ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (e.equivFun.symm z.1) i)
    simp only [LinearEquiv.apply_symm_apply]
    exact (contDiff_apply ℝ ℝ i).comp contDiff_fst
  · intro i
    change ContDiff ℝ n (fun z : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (e.equivFun.symm z.2) i)
    simp only [LinearEquiv.apply_symm_apply]
    exact (contDiff_apply ℝ ℝ i).comp contDiff_snd

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

section Values

variable {σ K V : Type*} [Field K] [Infinite K] [AddCommGroup V] [Module K V]

theorem eq_zero_of_eval_zero (p : VectorPolynomial σ K V) (hp : ∀ x : σ → K, eval x p = 0) : p = 0 := by
  let b := Module.Free.chooseBasis K V
  apply coefficients.injective
  apply Finsupp.ext
  intro α
  apply b.repr.injective
  apply Finsupp.ext
  intro i
  have hc : coordinate (b.coord i).toAddMonoidHom p = 0 := by
    apply MvPolynomial.funext
    intro x
    rw [map_zero, ← coordinate_eval₂]
    have he : eval₂ x p = 0 := by
      simpa using (eval₂_algebraMap (S := K) x p).trans (hp x)
    rw [he, map_zero]
  have h := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff α) hc
  simp only [coeff_coordinate, AddMonoidAlgebra.coeff_zero] at h
  change b.repr (coefficients p α) i = 0 at h
  simpa only [map_zero, Finsupp.zero_apply] using h

theorem eval_mem_iff_coefficients (U : Submodule K V) (p : VectorPolynomial σ K V) :
    (∀ x : σ → K, eval x p ∈ U) ↔ ∀ α, coefficients p α ∈ U := by
  constructor
  · intro hp
    have hz : map U.mkQ p = 0 := by
      apply eq_zero_of_eval_zero
      intro x
      rw [eval_map]
      exact (Submodule.Quotient.mk_eq_zero U).mpr (hp x)
    intro α
    apply (Submodule.Quotient.mk_eq_zero U).mp
    change U.mkQ (coefficients p α) = 0
    have hc := congrArg (fun q : VectorPolynomial σ K (V ⧸ U) => coefficients q α) hz
    simpa only [coefficients_map, map_zero, Finsupp.zero_apply] using hc
  · intro hp x
    classical
    rw [← sum_monomial_coefficients p]
    simp only [Finsupp.sum, map_sum, eval_monomial]
    exact U.sum_mem (fun α _ => U.smul_mem _ (hp α))

end Values

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def weightedDilation (w : σ → ℕ) (r : R) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V where
  toFun p := coefficients.symm (Finsupp.onFinset (coefficients p).support
    (fun α => r ^ Finsupp.weight w α • coefficients p α) (by
      intro α hα
      apply Finsupp.mem_support_iff.mpr
      intro hz
      exact hα (by rw [hz, smul_zero])))
  map_add' p q := by
    apply coefficients.injective
    ext α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply,
      map_add, Finsupp.add_apply, smul_add]
  map_smul' c p := by
    apply coefficients.injective
    ext α
    simp only [LinearEquiv.apply_symm_apply, Finsupp.onFinset_apply,
      map_smul, Finsupp.smul_apply, RingHom.id_apply]
    exact smul_comm _ _ _

@[simp] theorem coefficients_weightedDilation (w : σ → ℕ) (r : R)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedDilation w r p) α = r ^ Finsupp.weight w α • coefficients p α := by
  simp only [weightedDilation, LinearMap.coe_mk, AddHom.coe_mk, LinearEquiv.apply_symm_apply,
    Finsupp.onFinset_apply]

@[simp] theorem weightedDilation_one (w : σ → ℕ) (p : VectorPolynomial σ R V) :
    weightedDilation w 1 p = p := by
  apply coefficients.injective
  ext α
  simp

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def translate (h : σ → R) : VectorPolynomial σ R V →ₗ[R] VectorPolynomial σ R V :=
  (polynomialTranslate h).toLinearMap.rTensor V

@[simp] theorem translate_tmul (h : σ → R) (p : MvPolynomial σ R) (v : V) :
    translate h (p ⊗ₜ[R] v) = polynomialTranslate h p ⊗ₜ[R] v := rfl

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SquarefreePolynomialQuotient
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L]

abbrev SquarefreePolynomial (ι L : Type*) [LieRing L] [LieAlgebra ℚ L] :=
  VectorPolynomial ι ℚ L ⧸ (squarefreePolynomialIdeal (ι := ι) (L := L))

noncomputable def squarefreeMk : VectorPolynomial ι ℚ L →ₗ⁅ℚ⁆ SquarefreePolynomial ι L :=
  lieQuotientMap squarefreePolynomialIdeal

noncomputable def squarefreePolynomialEquiv [Fintype ι] :
    SquarefreePolynomial ι L ≃ₗ[ℚ] (SquarefreeIndex ι → L) :=
  LinearMap.quotKerEquivOfSurjective (squarefreeCoefficients (ι := ι) (L := L))
    (squarefreeCoefficients_surjective (ι := ι) (L := L))

@[simp] theorem squarefreePolynomialEquiv_mk [Fintype ι] (p : VectorPolynomial ι ℚ L) :
    squarefreePolynomialEquiv (squarefreeMk p) = squarefreeCoefficients p := rfl

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

variable (σ L : Type*) [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

structure MultidegreeLieFiltration (s : ℕ) (bound : σ → ℕ) where
  ordinary : NilpotentLieFiltration L s
  layer : (σ → ℕ) → Submodule ℚ L
  antitone : Antitone layer
  zero_eq_top : layer 0 = ⊤
  lie_mem : ∀ {a b : σ → ℕ} {x y : L}, x ∈ layer a → y ∈ layer b → ⁅x, y⁆ ∈ layer (a + b)
  terminal : ∀ a, ¬a ≤ bound → layer a = ⊥
  degree_eq : ∀ n, ordinary.layer n = ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i), layer a

namespace MultidegreeLieFiltration

variable {σ L} {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def layerIdeal (a : σ → ℕ) : LieIdeal ℚ L :=
  { F.layer a with
    lie_mem := by
      intro x y hy
      change ⁅x, y⁆ ∈ F.layer a
      have hx : x ∈ F.layer 0 := by simp only [F.zero_eq_top, Submodule.mem_top]
      simpa only [zero_add] using F.lie_mem hx hy }

@[simp] theorem mem_layerIdeal (a : σ → ℕ) (x : L) :
    x ∈ F.layerIdeal a ↔ x ∈ F.layer a := Iff.rfl

theorem layer_le_ordinary (a : σ → ℕ) : F.layer a ≤ F.ordinary.layer (∑ i, a i) := by
  rw [F.degree_eq]
  exact le_iSup_of_le a (le_iSup_of_le le_rfl le_rfl)

abbrev Group := F.ordinary.Group

def subgroup (a : σ → ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal a).toLieSubalgebra

@[simp] theorem mem_subgroup (a : σ → ℕ) (x : F.Group) :
    x ∈ F.subgroup a ↔ x.coord ∈ F.layer a := Iff.rfl

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}

theorem pi_degree_eq (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) (n : ℕ) :
    Submodule.pi Set.univ (fun i => (F i).ordinary.layer n) =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ j, a j), Submodule.pi Set.univ (fun i => (F i).layer a) := by
  classical
  apply le_antisymm
  · rw [← Submodule.iSup_map_single]
    refine iSup_le fun i => ?_
    rw [(F i).degree_eq]
    simp only [Submodule.map_iSup]
    refine iSup_le fun a => iSup_le fun ha => ?_
    apply le_trans (Submodule.map_le_iff_le_comap.mpr
      (Submodule.le_comap_single_pi (fun i => (F i).layer a)))
    exact le_iSup_of_le a (le_iSup_of_le ha le_rfl)
  · refine iSup_le fun a => iSup_le fun ha => ?_
    exact Submodule.pi_mono fun i _ => ((F i).layer_le_ordinary a).trans ((F i).ordinary.antitone ha)

noncomputable def pi (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound) :
    MultidegreeLieFiltration σ (∀ i, L i) s bound where
  ordinary := NilpotentLieFiltration.pi (fun i => (F i).ordinary)
  layer a := Submodule.pi Set.univ (fun i => (F i).layer a)
  antitone _ _ h := Submodule.pi_mono (fun i _ => (F i).antitone h)
  zero_eq_top := by simp only [zero_eq_top, Submodule.pi_top]
  lie_mem hx hy i hi := (F i).lie_mem (hx i hi) (hy i hi)
  terminal a ha := by
    simp only [show ∀ i, (F i).layer a = ⊥ from fun i => (F i).terminal a ha, Submodule.pi_univ_bot]
  degree_eq := pi_degree_eq F

@[simp] theorem mem_pi_layer (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)
    (a : σ → ℕ) (x : ∀ i, L i) :
    x ∈ (pi F).layer a ↔ ∀ i, x i ∈ (F i).layer a := by
  simp only [pi, Submodule.mem_pi, Set.mem_univ, forall_true_left]

end Erdos3.MultidegreeLieFiltration

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

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realificationHom :
    NilpotentLieBCHGroup L s hnil →*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) :=
  map rationalLieInclusion

@[simp]
theorem realificationHom_coord (g : NilpotentLieBCHGroup L s hnil) :
    (realificationHom g).coord = rationalLieInclusion g.coord := rfl

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realLayer (i : ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) := (F.layerIdeal i).baseChange ℝ

theorem realLayer_antitone : Antitone F.realLayer := by
  intro i j hij
  exact Submodule.baseChange_mono ℝ (F.antitone hij)

theorem realLayer_one : F.realLayer 1 = ⊤ := by
  have h : F.layerIdeal 1 = ⊤ := by
    ext a
    change a ∈ F.layer 1 ↔ a ∈ (⊤ : Submodule ℚ L)
    rw [F.one_eq_top]
  simp only [realLayer, h, LieSubmodule.baseChange_top]

theorem realLayer_terminal : F.realLayer (s + 1) = ⊥ := by
  have h : F.layerIdeal (s + 1) = ⊥ := by
    ext a
    change a ∈ F.layer (s + 1) ↔ a ∈ (⊥ : Submodule ℚ L)
    rw [F.terminal]
  simp only [realLayer, h, LieSubmodule.baseChange_bot]

theorem lie_realLayer_le (i j : ℕ) : ⁅F.realLayer i, F.realLayer j⁆ ≤ F.realLayer (i + j) := by
  have h : ⁅F.layerIdeal i, F.layerIdeal j⁆ ≤ F.layerIdeal (i + j) := by
    rw [LieSubmodule.lie_le_iff]
    exact fun a ha b hb => F.lie_mem ha hb
  rw [realLayer, realLayer, ← LieSubmodule.lie_baseChange]
  exact Submodule.baseChange_mono ℝ h

theorem realLayer_lie_mem {i j : ℕ} {a b : ℝ ⊗[ℚ] L}
    (ha : a ∈ F.realLayer i) (hb : b ∈ F.realLayer j) : ⁅a, b⁆ ∈ F.realLayer (i + j) :=
  F.lie_realLayer_le i j (LieSubmodule.lie_mem_lie ha hb)

noncomputable def realification : NilpotentLieFiltration (ℝ ⊗[ℚ] L) s where
  layer i := (F.realLayer i).toSubmodule.restrictScalars ℚ
  antitone := F.realLayer_antitone
  one_eq_top := by rw [F.realLayer_one]; rfl
  lie_mem := F.realLayer_lie_mem
  terminal := by rw [F.realLayer_terminal]; rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHChartCutoffSmooth
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥} [TopologicalSpace L]

instance instTopologicalSpace : TopologicalSpace (NilpotentLieBCHGroup L s hnil) :=
  TopologicalSpace.induced coord inferInstance

@[fun_prop]
theorem continuous_coord : Continuous (coord : NilpotentLieBCHGroup L s hnil → L) :=
  continuous_induced_dom

@[fun_prop]
theorem continuous_mk : Continuous (fun x : L => (⟨x⟩ : NilpotentLieBCHGroup L s hnil)) :=
  continuous_induced_rng.mpr continuous_id

def coordHomeomorph : NilpotentLieBCHGroup L s hnil ≃ₜ L where
  toFun := coord
  invFun x := ⟨x⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_coord
  continuous_invFun := continuous_mk

instance instContractibleSpace [ContractibleSpace L] : ContractibleSpace (NilpotentLieBCHGroup L s hnil) :=
  (coordHomeomorph (hnil := hnil)).contractibleSpace

theorem isTopologicalGroup_of_continuous_lie [IsTopologicalAddGroup L] [ContinuousConstSMul ℚ L]
    (hlie : Continuous (fun z : L × L => ⁅z.1, z.2⁆)) :
    IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) where
  continuous_mul := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
      (⟨lieBCH s z.1.coord z.2.coord⟩ : NilpotentLieBCHGroup L s hnil))
    have hcoords : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord)) :=
      (continuous_coord.comp continuous_fst).prodMk (continuous_coord.comp continuous_snd)
    have hbch : Continuous
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          lieBCH s z.1.coord z.2.coord) :=
      Continuous.comp
        (g := fun z : L × L => lieBCH s z.1 z.2)
        (f := fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (z.1.coord, z.2.coord))
        (continuous_lieBCH (L := L) hlie s) hcoords
    exact (continuous_mk (hnil := hnil)).comp hbch
  continuous_inv := by
    change Continuous (fun z : NilpotentLieBCHGroup L s hnil =>
      (⟨-z.coord⟩ : NilpotentLieBCHGroup L s hnil))
    exact (continuous_mk (hnil := hnil)).comp (continuous_coord (hnil := hnil)).neg

section Real

variable [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] [FiniteDimensional ℝ L]

instance instIsTopologicalGroup : IsTopologicalGroup (NilpotentLieBCHGroup L s hnil) := by
  let : ContinuousConstSMul ℚ L := ⟨fun q => by
    simpa only [algebraMap_smul] using
      (continuous_const_smul (algebraMap ℚ ℝ q) : Continuous (fun x : L => algebraMap ℚ ℝ q • x))⟩
  exact isTopologicalGroup_of_continuous_lie continuous_lie_finiteDimensional

end Real

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Topology

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def basisHomeomorph (e : Basis ι ℝ L) :
    NilpotentLieBCHGroup L s hnil ≃ₜ (ι → ℝ) :=
  (coordHomeomorph (hnil := hnil)).trans e.equivFunL.toHomeomorph

@[simp]
theorem basisHomeomorph_apply (e : Basis ι ℝ L) (g : NilpotentLieBCHGroup L s hnil) :
    basisHomeomorph e g = e.equivFun g.coord := rfl

theorem closed_discrete_subgroup_of_grid (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : ∀ g ∈ Γ, e.equivFun g.coord ∈ realDenominatorGrid l) :
    IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil)) ∧
      IsDiscrete (Γ : Set (NilpotentLieBCHGroup L s hnil)) := by
  let f := basisHomeomorph (hnil := hnil) e
  have hsub : (Γ : Set (NilpotentLieBCHGroup L s hnil)) ⊆ f ⁻¹' realDenominatorGrid l :=
    fun g hg => hgrid g hg
  have hd : IsDiscrete (f ⁻¹' realDenominatorGrid l) :=
    (isDiscrete_realDenominatorGrid l hl).preimage f.continuous.continuousOn f.injective
  have hc : IsClosed (f ⁻¹' realDenominatorGrid l) :=
    (isClosed_realDenominatorGrid l).preimage f.continuous
  exact ⟨isClosed_of_subset_discrete_closed hsub hd hc, hd.mono hsub⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def basisChartedSpace (e : Basis ι ℝ L) :
    ChartedSpace (ι → ℝ) (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph (hnil := hnil) e).isOpenEmbedding.singletonChartedSpace

variable (e : Basis ι ℝ L)

theorem isManifold_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    IsManifold 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) :=
  (basisHomeomorph e).isOpenEmbedding.isManifold_singleton

theorem contMDiff_basisHomeomorph (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e) :=
  contMDiff_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding

theorem contMDiff_basisHomeomorph_symm (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) n (basisHomeomorph (hnil := hnil) e).symm := by
  let := basisChartedSpace (hnil := hnil) e
  apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
  have heq : (basisHomeomorph (hnil := hnil) e) ∘ (basisHomeomorph e).symm = id :=
    funext (fun x => (basisHomeomorph e).apply_symm_apply x)
  rw [heq]
  exact contMDiff_id

variable [IsScalarTower ℚ ℝ L]

theorem lieGroup_basis (n : ℕ∞ω) :
    letI := basisChartedSpace (hnil := hnil) e
    LieGroup 𝓘(ℝ, ι → ℝ) n (NilpotentLieBCHGroup L s hnil) := by
  let := basisChartedSpace (hnil := hnil) e
  refine
    { __ := isManifold_basis (hnil := hnil) e n
      contMDiff_mul := ?_
      contMDiff_inv := ?_ }
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hcoords : ContMDiff (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
        𝓘(ℝ, (ι → ℝ) × (ι → ℝ)) n
        (fun z : NilpotentLieBCHGroup L s hnil × NilpotentLieBCHGroup L s hnil =>
          (basisHomeomorph e z.1, basisHomeomorph e z.2)) :=
      ((contMDiff_basisHomeomorph e n).comp contMDiff_fst).prodMk_space
        ((contMDiff_basisHomeomorph e n).comp contMDiff_snd)
    have hbch := (contDiff_coordinateBCH (n := n) e s).contMDiff.comp hcoords
    have he : (basisHomeomorph e) ∘ (fun p : NilpotentLieBCHGroup L s hnil ×
          NilpotentLieBCHGroup L s hnil => p.1 * p.2) =
        ((fun z => e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2))) ∘ fun z =>
          ((basisHomeomorph e) z.1, (basisHomeomorph e) z.2)) := by
      funext z
      simp only [Function.comp_apply, basisHomeomorph_apply, LinearEquiv.symm_apply_apply]
      rfl
    rw [he]
    exact hbch
  · apply ContMDiff.of_comp_isOpenEmbedding (basisHomeomorph e).isOpenEmbedding
    have hneg := (contDiff_neg (𝕜 := ℝ) (F := ι → ℝ) (n := n)).contMDiff.comp
      (contMDiff_basisHomeomorph (hnil := hnil) e n)
    have heq : (basisHomeomorph (hnil := hnil) e) ∘ (fun z => z⁻¹) =
        (fun z => -z) ∘ (basisHomeomorph e) := by
      funext z i
      change e.equivFun (-z.coord) i = -(e.equivFun z.coord i)
      simp only [map_neg, Pi.neg_apply]
    rw [heq]
    exact hneg

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realificationHom_coordinates (e : Basis ι ℚ L) (g : NilpotentLieBCHGroup L s hnil) :
    (e.baseChange ℝ).equivFun (realificationHom g).coord = fun i => (e.repr g.coord i : ℝ) := by
  funext i
  exact rationalLieInclusion_coordinates e g.coord i

theorem realification_subgroup_grid (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    ∀ g ∈ Γ.map realificationHom,
      (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  rw [realificationHom_coordinates, real_cast_mem_denominatorGrid_iff]
  apply hgrid
  change (⟨e.equivFun.symm (e.equivFun a.coord)⟩ : NilpotentLieBCHGroup L s hnil) ∈ Γ
  simpa only [LinearEquiv.symm_apply_apply] using ha

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

theorem realification_subgroup_closed_discrete (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (hgrid : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    IsClosed (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) ∧
    IsDiscrete (Γ.map realificationHom : Set
      (NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))) :=
  closed_discrete_subgroup_of_grid (e.baseChange ℝ) (Γ.map realificationHom) l hl
    (realification_subgroup_grid e Γ l hgrid)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHConjugationLinear
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ}

attribute [local instance] LieRing.ofAssociativeRing

theorem lieBCH_eq_of_step_le (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (hst : s ≤ t) (a b : L) : lieBCH t a b = lieBCH s a b := by
  let x : Fin 2 → FreeLieAlgebra ℚ (Fin 2) := FreeLieAlgebra.of ℚ
  let F := truncatedSeriesFiltration (A := FreeAlgebra ℚ (Fin 2)) s
  have hx (i : Fin 2) : scaledFreeGenerator s i ∈ F.layer 1 := scaledFreeGenerator_mem_layer s i
  have h : scaledFreeLieEval s (lieBCH t (x 0) (x 1)) =
      scaledFreeLieEval s (lieBCH s (x 0) (x 1)) := by
    simp only [map_lieBCH, x, scaledFreeLieEval_of]
    rw [(F.extend hst).lieBCH_eq (hx 0) (hx 1), F.lieBCH_eq (hx 0) (hx 1)]
  have he := lie_lift_eq_of_scaledFreeLieEval_eq ![a, b] hnil h
  simpa only [map_lieBCH, x, FreeLieAlgebra.lift_of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using he

theorem lieBCH_eq_of_nilpotent_steps (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) (a b : L) : lieBCH s a b = lieBCH t a b := by
  rcases le_total s t with hst | hts
  · exact (lieBCH_eq_of_step_le hs hst a b).symm
  · exact lieBCH_eq_of_step_le ht hts a b

theorem map_lieBCH_of_nilpotent_steps (φ : L →ₗ⁅ℚ⁆ M)
    (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ M M t = ⊥) (a b : L) :
    φ (lieBCH s a b) = lieBCH t (φ a) (φ b) := by
  rcases le_total s t with hst | hts
  · rw [← lieBCH_eq_of_step_le hs hst, map_lieBCH]
  · rw [map_lieBCH, lieBCH_eq_of_step_le ht hts]

end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L M N : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  [LieRing N] [LieAlgebra ℚ N] {s t u : ℕ}
  {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}
  {hN : LieModule.lowerCentralSeries ℚ N N u = ⊥}

noncomputable def mapOfSteps (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup L s hL →* NilpotentLieBCHGroup M t hM where
  toFun g := ⟨φ g.coord⟩
  map_one' := ext (map_zero φ)
  map_mul' g h := ext (map_lieBCH_of_nilpotent_steps φ hL hM g.coord h.coord)

@[simp] theorem mapOfSteps_coord (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) :
    (mapOfSteps (hM := hM) φ g).coord = φ g.coord := rfl

noncomputable def changeStep (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) :
    NilpotentLieBCHGroup L s hs ≃* NilpotentLieBCHGroup L t ht where
  toFun g := ⟨g.coord⟩
  invFun g := ⟨g.coord⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := ext (lieBCH_eq_of_nilpotent_steps hs ht g.coord h.coord)

@[simp] theorem changeStep_coord (hs : LieModule.lowerCentralSeries ℚ L L s = ⊥)
    (ht : LieModule.lowerCentralSeries ℚ L L t = ⊥) (g : NilpotentLieBCHGroup L s hs) :
    (changeStep hs ht g).coord = g.coord := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightTranslate (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) : ι → ℝ :=
  basisHomeomorph e ((basisHomeomorph e).symm x * g)

@[simp] theorem rightTranslate_coordinates (g h : NilpotentLieBCHGroup L s hnil) :
    rightTranslate e h (basisHomeomorph e g) = basisHomeomorph e (g * h) := by
  simp only [rightTranslate, Homeomorph.symm_apply_apply]

@[simp] theorem rightTranslate_one : rightTranslate (hnil := hnil) e 1 = id := by
  funext x
  simp only [rightTranslate, mul_one, Homeomorph.apply_symm_apply, id_eq]

theorem rightTranslate_comp (g h : NilpotentLieBCHGroup L s hnil) :
    rightTranslate e h ∘ rightTranslate e g = rightTranslate e (g * h) := by
  funext x
  simp only [Function.comp_apply, rightTranslate, Homeomorph.symm_apply_apply, mul_assoc]

variable [IsScalarTower ℚ ℝ L]

theorem contDiff_rightTranslate (g : NilpotentLieBCHGroup L s hnil) (n : ℕ∞ω) :
    ContDiff ℝ n (rightTranslate e g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e n
  exact ((contMDiff_basisHomeomorph e n).comp
    ((contMDiff_basisHomeomorph_symm e n).mul contMDiff_const)).contDiff

theorem rightTranslate_fderiv_leftInverse (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    (fderiv ℝ (rightTranslate e g⁻¹) (rightTranslate e g x)).comp
      (fderiv ℝ (rightTranslate e g) x) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  have hg := (contDiff_rightTranslate e g 1).differentiable (by decide)
  have hi := (contDiff_rightTranslate e g⁻¹ 1).differentiable (by decide)
  rw [← fderiv_comp x hi.differentiableAt hg.differentiableAt,
    rightTranslate_comp, mul_inv_cancel, rightTranslate_one, fderiv_id]

theorem rightTranslate_fderiv_injective (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    Function.Injective (fderiv ℝ (rightTranslate e g) x) := by
  intro v w hvw
  have h := congrArg (fderiv ℝ (rightTranslate e g⁻¹) (rightTranslate e g x)) hvw
  simpa only [← ContinuousLinearMap.comp_apply, rightTranslate_fderiv_leftInverse,
    ContinuousLinearMap.id_apply] using h

noncomputable def rightVelocity (g : NilpotentLieBCHGroup L s hnil) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  fderiv ℝ (rightTranslate e g⁻¹) (basisHomeomorph e g)

theorem rightVelocity_injective (g : NilpotentLieBCHGroup L s hnil) :
    Function.Injective (rightVelocity e g) :=
  rightTranslate_fderiv_injective e g⁻¹ (basisHomeomorph e g)

omit [IsScalarTower ℚ ℝ L] in
@[simp] theorem rightVelocity_one :
    rightVelocity (hnil := hnil) e 1 = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  simp only [rightVelocity, inv_one, rightTranslate_one, fderiv_id]

theorem rightVelocity_mul (g h : NilpotentLieBCHGroup L s hnil) :
    (rightVelocity e (g * h)).comp (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g)) =
      rightVelocity e g := by
  have hh := (contDiff_rightTranslate e h 1).differentiable (by decide)
  have hi := (contDiff_rightTranslate e (g * h)⁻¹ 1).differentiable (by decide)
  unfold rightVelocity
  rw [← rightTranslate_coordinates e g h, ← fderiv_comp _ hi.differentiableAt hh.differentiableAt,
    rightTranslate_comp]
  simp only [mul_inv_rev, mul_inv_cancel_left]

theorem contDiff_rightVelocity :
    ContDiff ℝ ∞ (fun x : ι → ℝ => rightVelocity (hnil := hnil) e ((basisHomeomorph e).symm x)) := by
  have h : ContDiff ℝ ∞ (fun p : (ι → ℝ) × (ι → ℝ) =>
      e.equivFun (lieBCH s (e.equivFun.symm p.2) (e.equivFun.symm (-p.1)))) :=
    ContDiff.comp
      (g := fun z : (ι → ℝ) × (ι → ℝ) =>
        e.equivFun (lieBCH s (e.equivFun.symm z.1) (e.equivFun.symm z.2)))
      (f := fun p : (ι → ℝ) × (ι → ℝ) => (p.2, -p.1))
      (contDiff_coordinateBCH (n := ∞) e s) (contDiff_snd.prodMk contDiff_fst.neg)
  have hd : ContDiff ℝ ∞ (fun x : ι → ℝ =>
      fderiv ℝ (fun y => e.equivFun (lieBCH s (e.equivFun.symm y) (e.equivFun.symm (-x)))) x) :=
    h.fderiv contDiff_id (by simp)
  convert hd using 1
  funext x
  unfold rightVelocity
  rw [Homeomorph.apply_symm_apply]
  apply congrArg (fun f : (ι → ℝ) → (ι → ℝ) => fderiv ℝ f x)
  funext y
  change e.equivFun (lieBCH s (e.equivFun.symm y) (-e.equivFun.symm x)) = _
  rw [map_neg]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightInnerForm (g : NilpotentLieBCHGroup L s hnil) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ :=
  coordinateDotForm.bilinearComp (rightVelocity e g) (rightVelocity e g)

theorem rightInnerForm_apply (g : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e g v w = ∑ i, rightVelocity e g v i * rightVelocity e g w i := by
  simp only [rightInnerForm, ContinuousLinearMap.bilinearComp_apply, coordinateDotForm_apply]

theorem rightInnerForm_symm (g : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e g v w = rightInnerForm e g w v := by
  simp only [rightInnerForm_apply, mul_comm]

@[simp] theorem rightInnerForm_one : rightInnerForm (hnil := hnil) e 1 = coordinateDotForm := by
  ext v w
  simp only [rightInnerForm, rightVelocity_one, ContinuousLinearMap.bilinearComp_apply,
    ContinuousLinearMap.id_apply]

variable [IsScalarTower ℚ ℝ L]

theorem rightInnerForm_pos (g : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) (hv : v ≠ 0) :
    0 < rightInnerForm e g v v := by
  have hne : rightVelocity e g v ≠ 0 := by
    intro h
    apply hv
    exact (rightVelocity_injective e g) (h.trans (map_zero _).symm)
  obtain ⟨i, hi⟩ : ∃ i, rightVelocity e g v i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  rw [rightInnerForm_apply]
  exact (Finset.sum_pos_iff_of_nonneg (fun j _ => mul_self_nonneg _)).mpr
    ⟨i, Finset.mem_univ i, mul_self_pos.mpr hi⟩

theorem rightInnerForm_right_invariant (g h : NilpotentLieBCHGroup L s hnil) (v w : ι → ℝ) :
    rightInnerForm e (g * h)
      (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) v)
      (fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) w) = rightInnerForm e g v w := by
  have hv := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) (rightVelocity_mul e g h)
  have hw := congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T w) (rightVelocity_mul e g h)
  simp only [ContinuousLinearMap.comp_apply] at hv hw
  simp only [rightInnerForm_apply, hv, hw]

theorem contDiff_rightInnerForm :
    ContDiff ℝ ∞ (fun x : ι → ℝ => rightInnerForm (hnil := hnil) e ((basisHomeomorph e).symm x)) :=
  contDiff_bilinearComp_self (E := ι → ℝ) (F := ι → ℝ) (n := ∞) coordinateDotForm
    (fun x => rightVelocity (hnil := hnil) e ((basisHomeomorph e).symm x))
    (contDiff_rightVelocity (hnil := hnil) e)

theorem rightInnerForm_isVonNBounded (g : NilpotentLieBCHGroup L s hnil) :
    Bornology.IsVonNBounded ℝ {v : ι → ℝ | rightInnerForm e g v v < 1} := by
  let A := fderiv ℝ (rightTranslate e g)
    (rightTranslate e g⁻¹ (basisHomeomorph e g))
  have hleft : A.comp (rightVelocity e g) = ContinuousLinearMap.id ℝ (ι → ℝ) := by
    simpa only [inv_inv, A, rightVelocity] using
      rightTranslate_fderiv_leftInverse e g⁻¹ (basisHomeomorph e g)
  apply (NormedSpace.isVonNBounded_iff' ℝ).mpr
  refine ⟨‖A‖, ?_⟩
  intro v hv
  change rightInnerForm e g v v < 1 at hv
  have hTv : ‖rightVelocity e g v‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
    intro i
    have hi : rightVelocity e g v i * rightVelocity e g v i ≤ rightInnerForm e g v v := by
      rw [rightInnerForm_apply]
      exact Finset.single_le_sum (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> nlinarith
  have heq : A (rightVelocity e g v) = v := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun T : (ι → ℝ) →L[ℝ] (ι → ℝ) => T v) hleft
  calc
    ‖v‖ = ‖A (rightVelocity e g v)‖ := congrArg norm heq.symm
    _ ≤ ‖A‖ * ‖rightVelocity e g v‖ := A.le_opNorm _
    _ ≤ ‖A‖ := mul_le_of_le_one_right (norm_nonneg _) hTv

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

noncomputable def rightRiemannianMetric :
    letI := basisChartedSpace (hnil := hnil) e
    RiemannianMetric (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  refine
    { inner := fun g => ?_
      symm := ?_
      pos := ?_
      continuousAt := ?_
      isVonNBounded := ?_ }
  · exact rightInnerForm e g
  · intro g v w
    exact rightInnerForm_symm e g v w
  · intro g v hv
    exact rightInnerForm_pos e g v hv
  · intro g
    exact ((rightInnerForm e g).continuous.clm_apply continuous_id).continuousAt
  · intro g
    exact rightInnerForm_isVonNBounded e g

omit [IsScalarTower ℚ ℝ L] in
theorem basisChart_mem_source (x y : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    y ∈ (chartAt (ι → ℝ) x).source := by
  let := basisChartedSpace (hnil := hnil) e
  change y ∈ ((basisHomeomorph e).isOpenEmbedding.toOpenPartialHomeomorph (basisHomeomorph e)).source
  simp

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangentCoordChange (x y z : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    tangentCoordChange 𝓘(ℝ, ι → ℝ) x y z = ContinuousLinearMap.id ℝ (ι → ℝ) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  apply ContinuousLinearMap.ext
  intro v
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) x x z v = v
  apply tangentCoordChange_self
  rw [extChartAt_source]
  exact basisChart_mem_source e x z

omit [IsScalarTower ℚ ℝ L] in
theorem basis_tangent_symmL (x y : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e 1
    (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symmL ℝ y v = v := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e 1
  rw [TangentBundle.symmL_trivializationAt_eq_core (basisChart_mem_source e x y)]
  change tangentCoordChange 𝓘(ℝ, ι → ℝ) x y y v = v
  rw [basis_tangentCoordChange]
  rfl

theorem contMDiff_rightInnerForm :
    letI := basisChartedSpace (hnil := hnil) e
    ContMDiff 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, (ι → ℝ) →L[ℝ] (ι → ℝ) →L[ℝ] ℝ) ∞
      (rightInnerForm (hnil := hnil) e) := by
  let := basisChartedSpace (hnil := hnil) e
  have h := (contDiff_rightInnerForm (hnil := hnil) e).contMDiff.comp
    (contMDiff_basisHomeomorph (hnil := hnil) e ∞)
  simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using h

noncomputable def rightSmoothRiemannianMetric :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    ContMDiffRiemannianMetric 𝓘(ℝ, ι → ℝ) ∞ (ι → ℝ)
      (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  refine
    { __ := rightRiemannianMetric (hnil := hnil) e
      contMDiff := ?_ }
  intro x
  rw [contMDiffAt_section]
  convert (contMDiff_rightInnerForm (hnil := hnil) e).contMDiffAt (x := x) using 1; try rfl
  funext y
  ext v w
  simp [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates,
    rightRiemannianMetric, Trivialization.continuousLinearMapAt_apply]
  have hy : y ∈ (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).baseSet :=
    basisChart_mem_source e x y
  have hw : (trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symm y w = w :=
    (Trivialization.symmL_apply (R := ℝ) _ hy w).symm.trans (basis_tangent_symmL e x y w)
  change rightInnerForm e y
    ((trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symmL ℝ y v)
    ((trivializationAt (ι → ℝ) (TangentSpace 𝓘(ℝ, ι → ℝ)) x).symm y w) = rightInnerForm e y v w
  exact congrArg₂ (fun a b : ι → ℝ => rightInnerForm e y a b)
    (basis_tangent_symmL e x y v) hw

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle
open scoped Manifold ContDiff

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

@[instance_reducible]
noncomputable def rightRiemannianBundle :
    letI := basisChartedSpace (hnil := hnil) e
    RiemannianBundle (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  exact ⟨(rightSmoothRiemannianMetric (hnil := hnil) e).toRiemannianMetric⟩

theorem rightRiemannianBundle_continuous :
    letI := basisChartedSpace (hnil := hnil) e
    letI := isManifold_basis (hnil := hnil) e ∞
    letI := rightRiemannianBundle (hnil := hnil) e
    IsContinuousRiemannianBundle (ι → ℝ)
      (fun g : NilpotentLieBCHGroup L s hnil => TangentSpace 𝓘(ℝ, ι → ℝ) g) := by
  let := basisChartedSpace (hnil := hnil) e
  let := isManifold_basis (hnil := hnil) e ∞
  let := rightRiemannianBundle (hnil := hnil) e
  exact ⟨(rightSmoothRiemannianMetric e).inner,
    (rightSmoothRiemannianMetric e).contMDiff.continuous, fun _ _ _ => rfl⟩

@[instance_reducible]
noncomputable def rightEMetricSpace : EMetricSpace (NilpotentLieBCHGroup L s hnil) := by
  letI := basisChartedSpace (hnil := hnil) e
  letI := isManifold_basis (hnil := hnil) e ∞
  letI := rightRiemannianBundle (hnil := hnil) e
  letI := rightRiemannianBundle_continuous (hnil := hnil) e
  letI : T3Space (NilpotentLieBCHGroup L s hnil) := (basisHomeomorph e).isEmbedding.t3Space
  exact EMetricSpace.ofRiemannianMetric 𝓘(ℝ, ι → ℝ) (NilpotentLieBCHGroup L s hnil)

@[instance_reducible]
noncomputable def rightMetricSpace : MetricSpace (NilpotentLieBCHGroup L s hnil) := by
  letI := rightEMetricSpace (hnil := hnil) e
  exact EMetricSpace.toMetricSpace edist_ne_top_of_preconnected

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

theorem basis_extChartAt_apply (g x : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    extChartAt 𝓘(ℝ, ι → ℝ) g x = basisHomeomorph e x := rfl

theorem basis_extChartAt_symm_apply (g : NilpotentLieBCHGroup L s hnil) (x : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    (extChartAt 𝓘(ℝ, ι → ℝ) g).symm x = (basisHomeomorph e).symm x := by
  let := basisChartedSpace (hnil := hnil) e
  have hs : (basisHomeomorph e).symm x ∈ (extChartAt 𝓘(ℝ, ι → ℝ) g).source := by
    rw [extChartAt_source]
    exact basisChart_mem_source e g _
  have h := (extChartAt 𝓘(ℝ, ι → ℝ) g).left_inv hs
  rw [basis_extChartAt_apply, Homeomorph.apply_symm_apply] at h
  exact h

variable [IsScalarTower ℚ ℝ L]

theorem mfderiv_mul_right_coordinates (g h : NilpotentLieBCHGroup L s hnil) (v : ι → ℝ) :
    letI := basisChartedSpace (hnil := hnil) e
    mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v =
      fderiv ℝ (rightTranslate e h) (basisHomeomorph e g) v := by
  let := basisChartedSpace (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e 1
  have hm : MDifferentiableAt 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g :=
    contMDiff_mul_right.mdifferentiableAt one_ne_zero
  rw [hm.mfderiv]
  simp only [writtenInExtChartAt, Function.comp_def, basis_extChartAt_apply,
    basis_extChartAt_symm_apply, modelWithCornersSelf_coe, Set.range_id, fderivWithin_univ]
  rfl

theorem enorm_mfderiv_mul_right (g h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    ∀ v : TangentSpace 𝓘(ℝ, ι → ℝ) g,
      ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v‖ₑ = ‖v‖ₑ := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  intro v
  have hn : ‖mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v‖ = ‖v‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    congr 1
    change rightInnerForm e (g * h)
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v)
      (mfderiv 𝓘(ℝ, ι → ℝ) 𝓘(ℝ, ι → ℝ) (fun x => x * h) g v) = rightInnerForm e g v v
    have hv := mfderiv_mul_right_coordinates e g h v
    exact (congrArg₂ (fun a b : ι → ℝ => rightInnerForm e (g * h) a b) hv hv).trans
      (rightInnerForm_right_invariant e g h v v)
  exact enorm_eq_iff_norm_eq.mpr hn

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Bundle Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

variable (e : Basis ι ℝ L)

theorem riemannianEDist_mul_right_le (x y h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    riemannianEDist 𝓘(ℝ, ι → ℝ) (x * h) (y * h) ≤ riemannianEDist 𝓘(ℝ, ι → ℝ) x y := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := lieGroup_basis (hnil := hnil) e 1
  exact riemannianEDist_le_of_mfderiv_norm_le contMDiff_mul_right
    (fun z v => (enorm_mfderiv_mul_right e z h v).le) x y

theorem riemannianEDist_mul_right (x y h : NilpotentLieBCHGroup L s hnil) :
    letI := basisChartedSpace (hnil := hnil) e
    letI := rightRiemannianBundle (hnil := hnil) e
    riemannianEDist 𝓘(ℝ, ι → ℝ) (x * h) (y * h) = riemannianEDist 𝓘(ℝ, ι → ℝ) x y := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  apply le_antisymm (riemannianEDist_mul_right_le e x y h)
  simpa only [mul_inv_cancel_right] using riemannianEDist_mul_right_le e (x * h) (y * h) h⁻¹

theorem rightMetricSpace_isometry_mul_right (h : NilpotentLieBCHGroup L s hnil) :
    letI := rightMetricSpace (hnil := hnil) e
    Isometry (fun x => x * h) := by
  let := basisChartedSpace (hnil := hnil) e
  let := rightRiemannianBundle (hnil := hnil) e
  let := rightMetricSpace (hnil := hnil) e
  intro x y
  exact riemannianEDist_mul_right e x y h

theorem rightMetricSpace_isIsometricSMul :
    letI := rightMetricSpace (hnil := hnil) e
    IsIsometricSMul (NilpotentLieBCHGroup L s hnil)ᵐᵒᵖ (NilpotentLieBCHGroup L s hnil) := by
  let := rightMetricSpace (hnil := hnil) e
  exact ⟨fun h => rightMetricSpace_isometry_mul_right e h.unop⟩

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3

open Module

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M] [IsScalarTower ℚ ℝ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def mapReal (φ : L →ₗ⁅ℝ⁆ M) :
    NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M t hM :=
  mapOfSteps (realLieHomToRat φ)

open scoped Manifold ContDiff

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module

variable {ι κ L M : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [LieRing M] [LieAlgebra ℚ M] [LieAlgebra ℝ M]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul ℝ M] [T2Space M]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

variable (e : Basis ι ℝ L) (f : Basis κ ℝ M)
  (φ : NilpotentLieBCHGroup L s hnil →* NilpotentLieBCHGroup M s hM)

noncomputable def homCoordinates (v : ι → ℝ) : κ → ℝ :=
  basisHomeomorph f (φ ((basisHomeomorph e).symm v))

@[simp] theorem homCoordinates_zero : homCoordinates e f φ 0 = 0 := by
  have he : (basisHomeomorph (hnil := hnil) e).symm 0 = 1 := by
    apply ext
    exact map_zero e.equivFun.symm
  simp only [homCoordinates, he, map_one]
  exact map_zero f.equivFun

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module Manifold
open scoped Manifold ContDiff Bundle

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def coordinateLine (e : Basis ι ℝ L) (v : ι → ℝ) (t : ℝ) :
    NilpotentLieBCHGroup L s hnil := (basisHomeomorph e).symm (t • v)

variable (e : Basis ι ℝ L) (v : ι → ℝ)

@[simp] theorem coordinateLine_zero : coordinateLine (hnil := hnil) e v 0 = 1 := by
  apply ext
  change e.equivFun.symm ((0 : ℝ) • v) = 0
  simp only [zero_smul, map_zero]

@[simp] theorem coordinateLine_one :
    coordinateLine (hnil := hnil) e v 1 = (basisHomeomorph e).symm v := by
  simp only [coordinateLine, one_smul]

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHQuotientLocalIsometry
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module _root_.Set

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] [TopologicalSpace L] [IsTopologicalAddGroup L]
  [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[instance_reducible]
noncomputable def quotientMetricSpace (e : Basis ι ℝ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (hΓ : IsClosed (Γ : Set (NilpotentLieBCHGroup L s hnil))) :
    MetricSpace (NilpotentLieBCHGroup L s hnil ⧸ Γ) := by
  letI : FiniteDimensional ℝ L := e.finiteDimensional_of_finite
  letI := rightMetricSpace (hnil := hnil) e
  letI := rightMetricSpace_isIsometricSMul (hnil := hnil) e
  exact rightCosetMetricSpace Γ hΓ

end Erdos3.NilpotentLieBCHGroup

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]

local notation "G" => NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)

@[instance_reducible]
noncomputable def realificationQuotientMetricSpace (e : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (l : ℕ) (hl : 0 < l)
    (houter : bchSubgroupCoordinates e Γ ⊆ denominatorGrid l) :
    MetricSpace (G ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) :=
  NilpotentLieBCHGroup.quotientMetricSpace (e.baseChange ℝ)
    (Γ.map NilpotentLieBCHGroup.realificationHom)
    (NilpotentLieBCHGroup.realification_subgroup_closed_discrete e Γ l hl houter).1

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {ι κ L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

namespace NilpotentLieBCHGroup

variable {s t : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M t = ⊥}

noncomputable def realificationMap (φ : L →ₗ⁅ℚ⁆ M) :
    NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil) →*
      NilpotentLieBCHGroup (ℝ ⊗[ℚ] M) t (realification_lowerCentralSeries_eq_bot hM) :=
  mapReal (realificationLieHom φ)

@[simp] theorem realificationMap_coord (φ : L →ₗ⁅ℚ⁆ M)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    (realificationMap (hnil := hnil) (hM := hM) φ g).coord = realificationLieHom φ g.coord := rfl

end NilpotentLieBCHGroup
end Erdos3

end

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped NNReal

section BasisChange

variable {ι κ L : Type*} [Fintype ι] [Fintype κ]
  [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] [IsScalarTower ℚ ℝ L]
  [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

omit [TopologicalSpace L] [IsTopologicalAddGroup L] [ContinuousSMul ℝ L] [T2Space L] in
@[simp] theorem mapReal_id (x : NilpotentLieBCHGroup L s hnil) :
    mapReal (hM := hnil) (LieHom.id : L →ₗ⁅ℝ⁆ L) x = x := rfl

end BasisChange

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedPolynomialSubstitution
namespace OAI


namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {σ τ υ R V W : Type*} [CommRing R] [AddCommGroup V] [Module R V]
  [AddCommGroup W] [Module R W]

noncomputable def substitute (f : σ → MvPolynomial τ R) :
    VectorPolynomial σ R V →ₗ[R] VectorPolynomial τ R V :=
  (MvPolynomial.aeval (R := R) f).toLinearMap.rTensor V

@[simp] theorem substitute_tmul (f : σ → MvPolynomial τ R) (p : MvPolynomial σ R) (v : V) :
    substitute f (p ⊗ₜ[R] v) = MvPolynomial.aeval (R := R) f p ⊗ₜ[R] v := rfl

theorem coefficients_substitute_monomial (f : σ → MvPolynomial τ R)
    (α : σ →₀ ℕ) (β : τ →₀ ℕ) (v : V) :
    coefficients (substitute f (monomial α v)) β =
      (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial α 1)).coeff β • v := by
  rw [monomial, substitute_tmul, coefficients_tmul]

theorem coefficients_substitute (f : σ → MvPolynomial τ R) (p : VectorPolynomial σ R V)
    (α : τ →₀ ℕ) :
    coefficients (substitute f p) α = ∑ β ∈ (coefficients p).support,
      (MvPolynomial.aeval (R := R) f (MvPolynomial.monomial β 1)).coeff α • coefficients p β := by
  conv_lhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, Finsupp.finsetSum_apply, coefficients_substitute_monomial]

noncomputable def substituteLie {L : Type*} [LieRing L] [LieAlgebra R L]
    (f : σ → MvPolynomial τ R) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial τ R L where
  toLinearMap := substitute f
  map_lie' {p q} := by
    change substitute f ⁅p, q⁆ = ⁅substitute f p, substitute f q⁆
    induction p using TensorProduct.induction_on with
    | zero => refine (congrArg _ (zero_lie (L := VectorPolynomial σ R L) (M := VectorPolynomial σ R L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (zero_lie (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm) | exact (zero_lie (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm
    | tmul a v =>
      induction q using TensorProduct.induction_on with
      | zero => refine (congrArg _ (lie_zero (L := VectorPolynomial σ R L) (M := VectorPolynomial σ R L) _)).trans ?_; first | (simp; done) | (rw [map_zero]; exact (lie_zero (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm) | exact (lie_zero (L := VectorPolynomial τ R L) (M := VectorPolynomial τ R L) _).symm
      | tmul b w => simp only [LieAlgebra.ExtendScalars.bracket_tmul, substitute_tmul, map_mul]
      | add p q hp hq => rw [LieRing.lie_add, map_add, hp, hq, map_add, LieRing.lie_add]
    | add p q hp hq => rw [LieRing.add_lie, map_add, hp, hq, map_add, LieRing.add_lie]

end Erdos3.VectorPolynomial


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

def Adapted (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) : Prop :=
  ∀ i, DegreeLE w i (VectorPolynomial.map (F.layer (i + 1)).mkQ p)

theorem adapted_iff_coefficients (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    F.Adapted w p ↔ ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α) := by
  constructor
  · intro hp α
    generalize hd : Finsupp.weight w α = d
    cases d with
    | zero =>
      apply F.antitone (Nat.zero_le 1)
      simp [F.one_eq_top]
    | succ d =>
      have h := hp d α (by rw [hd]; exact Nat.lt_succ_self d)
      rw [coefficients_map] at h
      exact (Submodule.Quotient.mk_eq_zero _).mp h
  · intro hp i α hα
    rw [coefficients_map]
    exact (Submodule.Quotient.mk_eq_zero _).mpr (F.antitone hα (hp α))

noncomputable def adaptedSubmodule (w : σ → ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp α)

theorem mem_adaptedSubmodule (w : σ → ℕ) (p : VectorPolynomial σ ℚ L) :
    p ∈ F.adaptedSubmodule w ↔ F.Adapted w p := (F.adapted_iff_coefficients w p).symm

theorem monomial_mem_adaptedSubmodule (w : σ → ℕ) (α : σ →₀ ℕ) {a : L}
    (ha : a ∈ F.layer (Finsupp.weight w α)) :
    monomial (R := ℚ) α a ∈ F.adaptedSubmodule w := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_adaptedSubmodule (w : σ → ℕ) {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.adaptedSubmodule w) (hq : q ∈ F.adaptedSubmodule w) :
    ⁅p, q⁆ ∈ F.adaptedSubmodule w := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun α => monomial (R := ℚ) α (coefficients p α))
    (fun β => monomial (R := ℚ) β (coefficients q β))]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_adaptedSubmodule
  rw [map_add]
  exact F.lie_mem (hp α) (hq β)

noncomputable def adaptedLieSubalgebra (w : σ → ℕ) : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { F.adaptedSubmodule w with lie_mem' := F.lie_mem_adaptedSubmodule w }

end Erdos3.NilpotentLieFiltration


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialSubgroup (w : σ → ℕ) :
    Subgroup (NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s
      (VectorPolynomial.lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot)) :=
  NilpotentLieBCHGroup.subgroup (F.adaptedLieSubalgebra w)

abbrev PolynomialOrbit (w : σ → ℕ) : Type _ := ↥(F.polynomialSubgroup w)

variable {F}

def PolynomialOrbit.log {w : σ → ℕ} (p : F.PolynomialOrbit w) : VectorPolynomial σ ℚ L :=
  p.val.coord

theorem PolynomialOrbit.adapted {w : σ → ℕ} (p : F.PolynomialOrbit w) : F.Adapted w p.log :=
  (F.mem_adaptedSubmodule w p.log).mp p.property

def polynomialOrbitOfLog {w : σ → ℕ} (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) :
    F.PolynomialOrbit w := ⟨⟨p⟩, (F.mem_adaptedSubmodule w p).mpr hp⟩

@[simp] theorem polynomialOrbitOfLog_log {w : σ → ℕ}
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) :
    (polynomialOrbitOfLog p hp).log = p := rfl

variable (F)

noncomputable def polynomialOrbitEval (w : σ → ℕ) (x : σ → ℤ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (evalLie (fun i => (x i : ℚ)))).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℤ) :
    (F.polynomialOrbitEval w x p).coord = eval (fun i => (x i : ℚ)) p.log := rfl

end Erdos3.NilpotentLieFiltration


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem adapted_substitute (w : σ → ℕ) (v : τ → ℕ) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) :
    F.Adapted v (VectorPolynomial.substitute f p) := by
  apply (F.adapted_iff_coefficients v _).mpr
  intro α
  rw [coefficients_substitute]
  apply Submodule.sum_mem
  intro β _
  by_cases hc : (MvPolynomial.aeval (R := ℚ) f (MvPolynomial.monomial β 1)).coeff α = 0
  · rw [hc, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    apply F.antitone _ ((F.adapted_iff_coefficients w p).mp hp β)
    exact aeval_monomial_weightedSupport f w v hf β (MvPolynomial.mem_support_iff.mpr hc)

noncomputable def polynomialOrbitSubstitute {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) :
    F.PolynomialOrbit w →* F.PolynomialOrbit v where
  toFun p := polynomialOrbitOfLog (VectorPolynomial.substitute f p.log)
    (F.adapted_substitute w v f hf p.adapted)
  map_one' := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact map_zero (VectorPolynomial.substitute f)
  map_mul' p q := by
    apply Subtype.ext
    apply NilpotentLieBCHGroup.ext
    exact map_lieBCH (VectorPolynomial.substituteLie f) s p.log q.log

@[simp] theorem polynomialOrbitSubstitute_log {w : σ → ℕ} {v : τ → ℕ}
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i))
    (p : F.PolynomialOrbit w) :
    (F.polynomialOrbitSubstitute f hf p).log = VectorPolynomial.substitute f p.log := rfl

end Erdos3.NilpotentLieFiltration

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdaptedBinomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial Module
open scoped Manifold ContDiff TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitRealEval (w : σ → ℕ) (x : σ → ℝ) :
    F.PolynomialOrbit w →* F.Group :=
  (NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (L := L) x)).comp
    (F.polynomialSubgroup w).subtype

@[simp] theorem polynomialOrbitRealEval_coord (w : σ → ℕ)
    (p : F.PolynomialOrbit w) (x : σ → ℝ) :
    (F.polynomialOrbitRealEval w x p).coord = eval₂ x p.log := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F G : NilpotentLieFiltration L s) (hGF : G = F) (w : σ → ℕ)

noncomputable def realPolynomialOrbitChangeFiltration
    (orbit : F.realification.PolynomialOrbit w) : G.realification.PolynomialOrbit w :=
  polynomialOrbitOfLog orbit.log (by rw [hGF]; exact orbit.adapted)

@[simp] theorem realPolynomialOrbitChangeFiltration_log
    (orbit : F.realification.PolynomialOrbit w) :
    (F.realPolynomialOrbitChangeFiltration G hGF w orbit).log = orbit.log := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankLayers
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def rankGenerators (d r : ℕ) : Set L :=
  {x | ∃ k, r ≤ k ∧ ∃ a : FilteredLieTree F d k, a.eval = x}

def rankLayer (d r : ℕ) : Submodule ℚ L :=
  F.layer (d + 1) ⊔ Submodule.span ℚ (F.rankGenerators d r)

theorem layer_succ_le_rankLayer (d r : ℕ) : F.layer (d + 1) ≤ F.rankLayer d r := le_sup_left

theorem span_rankGenerators_le_rankLayer (d r : ℕ) :
    Submodule.span ℚ (F.rankGenerators d r) ≤ F.rankLayer d r := le_sup_right

theorem tree_eval_mem_rankLayer {d r k : ℕ} (a : FilteredLieTree F d k) (hr : r ≤ k) :
    a.eval ∈ F.rankLayer d r :=
  F.span_rankGenerators_le_rankLayer d r (Submodule.subset_span ⟨k, hr, a, rfl⟩)

theorem rankLayer_le_layer (d r : ℕ) : F.rankLayer d r ≤ F.layer d := by
  apply sup_le (F.antitone (by omega))
  apply Submodule.span_le.mpr
  rintro x ⟨k, _, a, rfl⟩
  exact a.eval_mem

theorem rankLayer_rank_antitone (d : ℕ) : Antitone (F.rankLayer d) := by
  intro r t hrt
  apply sup_le_sup_left
  apply Submodule.span_mono
  rintro x ⟨k, htk, a, hx⟩
  exact ⟨k, hrt.trans htk, a, hx⟩

theorem rankLayer_degree_le {d e : ℕ} (hde : d < e) (r t : ℕ) :
    F.rankLayer e t ≤ F.rankLayer d r :=
  (F.rankLayer_le_layer e t).trans
    ((F.antitone (show d + 1 ≤ e by omega)).trans (F.layer_succ_le_rankLayer d r))

theorem rankLayer_lex_antitone {d e r t : ℕ} (h : d < e ∨ d = e ∧ r ≤ t) :
    F.rankLayer e t ≤ F.rankLayer d r := by
  rcases h with h | ⟨rfl, h⟩
  · exact F.rankLayer_degree_le h r t
  · exact F.rankLayer_rank_antitone d h

theorem rankLayer_eq_layer_of_rank_le_one (d : ℕ) {r : ℕ} (hr : r ≤ 1) :
    F.rankLayer d r = F.layer d := by
  apply le_antisymm (F.rankLayer_le_layer d r)
  intro x hx
  by_cases hd : d = 0
  · subst d
    exact F.layer_succ_le_rankLayer 0 r (by simp only [zero_add, F.one_eq_top, Submodule.mem_top])
  · exact F.tree_eval_mem_rankLayer (.leaf (by omega) x hx) hr

theorem rankLayer_zero (d : ℕ) : F.rankLayer d 0 = F.layer d :=
  F.rankLayer_eq_layer_of_rank_le_one d (by omega)

theorem rankLayer_one (d : ℕ) : F.rankLayer d 1 = F.layer d :=
  F.rankLayer_eq_layer_of_rank_le_one d le_rfl

theorem rankLayer_eq_next_of_degree_lt_rank {d r : ℕ} (hdr : d < r) :
    F.rankLayer d r = F.layer (d + 1) := by
  have hgen : F.rankGenerators d r = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨k, hrk, a, _⟩
    have := a.rank_le_degree
    omega
  simp only [rankLayer, hgen, Submodule.span_empty, sup_bot_eq]

theorem rankLayer_top_terminal (r : ℕ) (hr : s < r) : F.rankLayer s r = ⊥ := by
  rw [F.rankLayer_eq_next_of_degree_lt_rank hr, F.terminal]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DegreeRankLieBrackets
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem rank_span_lie_mem {d e r t : ℕ} {x y : L}
    (hx : x ∈ Submodule.span ℚ (F.rankGenerators d r))
    (hy : y ∈ Submodule.span ℚ (F.rankGenerators e t)) :
    ⁅x, y⁆ ∈ F.rankLayer (d + e) (r + t) := by
  induction hx, hy using Submodule.span_induction₂ with
  | mem_mem x y hx hy =>
    obtain ⟨i, hi, a, rfl⟩ := hx
    obtain ⟨j, hj, b, rfl⟩ := hy
    exact F.tree_eval_mem_rankLayer (a.bracket b) (Nat.add_le_add hi hj)
  | zero_left y _ => rw [zero_lie]; exact Submodule.zero_mem _
  | zero_right x _ => rw [lie_zero]; exact Submodule.zero_mem _
  | add_left x y z _ _ _ hx hy => rw [add_lie]; exact Submodule.add_mem _ hx hy
  | add_right x y z _ _ _ hx hy => rw [lie_add]; exact Submodule.add_mem _ hx hy
  | smul_left c x y _ _ h => rw [smul_lie]; exact Submodule.smul_mem _ c h
  | smul_right c x y _ _ h => rw [lie_smul]; exact Submodule.smul_mem _ c h

theorem rankLayer_lie_mem {d e r t : ℕ} {x y : L}
    (hx : x ∈ F.rankLayer d r) (hy : y ∈ F.rankLayer e t) :
    ⁅x, y⁆ ∈ F.rankLayer (d + e) (r + t) := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, hc, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
  have hb' : b ∈ F.layer d := F.rankLayer_le_layer d r (F.span_rankGenerators_le_rankLayer d r hb)
  have hz' : z ∈ F.layer e := F.rankLayer_le_layer e t (F.span_rankGenerators_le_rankLayer e t hz)
  have hc' : c ∈ F.layer e := F.antitone (by omega) hc
  have hleft {u v : L} (hu : u ∈ F.layer (d + 1)) (hv : v ∈ F.layer e) :
      ⁅u, v⁆ ∈ F.rankLayer (d + e) (r + t) := by
    apply F.layer_succ_le_rankLayer
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using F.lie_mem hu hv
  have hright : ⁅b, c⁆ ∈ F.rankLayer (d + e) (r + t) := by
    apply F.layer_succ_le_rankLayer
    simpa only [Nat.add_assoc] using F.lie_mem hb' hc
  simp only [add_lie, lie_add]
  exact Submodule.add_mem _ (Submodule.add_mem _ (hleft ha hc') hright)
    (Submodule.add_mem _ (hleft ha hz') (F.rank_span_lie_mem hb hz))

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3

variable (L : Type*) [LieRing L] [LieAlgebra ℚ L]

namespace DegreeRankLieFiltration

variable {L} {s r : ℕ} (F : DegreeRankLieFiltration L s r)

theorem zero_eq_top : F.layer 0 0 = ⊤ := by
  apply top_unique
  rw [← F.one_eq_top]
  exact F.degree_antitone 0 (by omega)

def associatedDegree : NilpotentLieFiltration L s where
  layer d := F.layer d 0
  antitone := F.degree_antitone 0
  one_eq_top := F.one_eq_top
  lie_mem hx hy := F.lie_mem hx hy
  terminal := F.layer_eq_bot_of_past_top (Or.inl (by omega))

@[simp] theorem associatedDegree_layer (d : ℕ) : F.associatedDegree.layer d = F.layer d 0 := rfl

end DegreeRankLieFiltration

namespace NilpotentLieFiltration

variable {L} {s : ℕ} (F : NilpotentLieFiltration L s)

def canonicalDegreeRank : DegreeRankLieFiltration L s s where
  rank_le_degree := le_rfl
  layer := F.rankLayer
  lex_antitone := F.rankLayer_lex_antitone
  one_eq_top := by rw [F.rankLayer_zero, F.one_eq_top]
  rank_zero_eq_one d := by rw [F.rankLayer_zero, F.rankLayer_one]
  overshoot d i h := by rw [F.rankLayer_eq_next_of_degree_lt_rank h, F.rankLayer_zero]
  lie_mem := F.rankLayer_lie_mem
  terminal := F.rankLayer_top_terminal (s + 1) (by omega)

@[simp] theorem canonicalDegreeRank_associatedDegree_layer (d : ℕ) :
    F.canonicalDegreeRank.associatedDegree.layer d = F.layer d := F.rankLayer_zero d

end NilpotentLieFiltration

end Erdos3

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {ι : Type*} [Nonempty ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s r : ℕ}

def pi (F : ∀ i, DegreeRankLieFiltration (L i) s r) :
    DegreeRankLieFiltration (∀ i, L i) s r where
  rank_le_degree := (F (Classical.choice inferInstance)).rank_le_degree
  layer d j := Submodule.pi Set.univ (fun i => (F i).layer d j)
  lex_antitone h := Submodule.pi_mono (fun i _ => (F i).lex_antitone h)
  one_eq_top := by simp only [one_eq_top, Submodule.pi_top]
  rank_zero_eq_one d := by simp only [rank_zero_eq_one]
  overshoot d j h := congrArg (Submodule.pi Set.univ)
    (funext (fun i => (F i).overshoot d j h))
  lie_mem hx hy i hi := (F i).lie_mem (hx i hi) (hy i hi)
  terminal := by simp only [terminal, Submodule.pi_univ_bot]

@[simp] theorem mem_pi_layer (F : ∀ i, DegreeRankLieFiltration (L i) s r)
    (d j : ℕ) (x : ∀ i, L i) :
    x ∈ (pi F).layer d j ↔ ∀ i, x i ∈ (F i).layer d j := by
  simp [pi, Submodule.mem_pi]

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def rankFlag (n : ℕ) : Submodule ℚ L := F.layer (n / (s + 1)) (n % (s + 1))

@[simp] theorem rankFlag_zero : F.rankFlag 0 = ⊤ := by
  simpa only [rankFlag, Nat.zero_div, Nat.zero_mod] using F.zero_eq_top

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def polynomialFiltration : DegreeRankLieFiltration (VectorPolynomial σ ℚ L) s r where
  rank_le_degree := F.rank_le_degree
  layer d i := coefficientSubmodule (F.layer d i)
  lex_antitone := fun h _ hp α => F.lex_antitone h (hp α)
  one_eq_top := by
    apply top_unique
    intro p _ α
    rw [F.one_eq_top]
    trivial
  rank_zero_eq_one d := by rw [F.rank_zero_eq_one]
  overshoot d i hi := by rw [F.overshoot d i hi]
  lie_mem := by
    intro d e i j p q hp hq
    apply (eval_mem_iff_coefficients (F.layer (d + e) (i + j)) ⁅p, q⁆).mp
    intro t
    have hp' := (eval_mem_iff_coefficients (F.layer d i) p).mpr hp t
    have hq' := (eval_mem_iff_coefficients (F.layer e j) q).mpr hq t
    change evalLie t ⁅p, q⁆ ∈ F.layer (d + e) (i + j)
    rw [LieHom.map_lie]
    exact F.lie_mem hp' hq'
  terminal := by
    apply bot_unique
    intro p hp
    change p = 0
    apply coefficients.injective
    ext α
    simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using hp α

@[simp] theorem polynomialFiltration_layer (d i : ℕ) :
    (F.polynomialFiltration (σ := σ)).layer d i = coefficientSubmodule (F.layer d i) := rfl

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def higherHorizontalKernel (i : ℕ) : Submodule ℚ (F.layer i 1) :=
  (F.layer i 2).comap (F.layer i 1).subtype

abbrev HigherHorizontal (i : ℕ) := (F.layer i 1) ⧸ F.higherHorizontalKernel i

def higherHorizontalMk (i : ℕ) : F.layer i 1 →ₗ[ℚ] F.HigherHorizontal i :=
  (F.higherHorizontalKernel i).mkQ

theorem higherHorizontalMk_surjective (i : ℕ) : Function.Surjective (F.higherHorizontalMk i) :=
  (F.higherHorizontalKernel i).mkQ_surjective

noncomputable def higherHorizontalRepresentative (i : ℕ) (v : F.HigherHorizontal i) : F.layer i 1 := by
  classical
  exact if v = 0 then 0 else Classical.choose (F.higherHorizontalMk_surjective i v)

@[simp] theorem higherHorizontalRepresentative_zero (i : ℕ) :
    F.higherHorizontalRepresentative i 0 = 0 := by
  classical
  simp [higherHorizontalRepresentative]

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquarefreePermutationFiltration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (hF : F.layer (s + 1) = ⊥)

def dropTop : NilpotentLieFiltration L s where
  layer := F.layer
  antitone := F.antitone
  one_eq_top := F.one_eq_top
  lie_mem := F.lie_mem
  terminal := hF

@[simp] theorem dropTop_layer (i : ℕ) : (F.dropTop hF).layer i = F.layer i := rfl

@[simp] theorem dropTop_realification_layer (i : ℕ) :
    (F.dropTop hF).realification.layer i = F.realification.layer i := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

def Adapted (p : VectorPolynomial σ ℚ L) : Prop :=
  ∀ a, coefficients p a ∈ F.layer (fun i => a i)

noncomputable def adaptedSubmodule : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | F.Adapted p}
  zero_mem' := by intro a; simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  add_mem' hp hq := by
    intro a
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp a) (hq a)
  smul_mem' c p hp := by
    intro a
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem c (hp a)

theorem monomial_mem_adaptedSubmodule (a : σ →₀ ℕ) {x : L} (hx : x ∈ F.layer (fun i => a i)) :
    monomial (R := ℚ) a x ∈ F.adaptedSubmodule := by
  classical
  intro b
  by_cases h : a = b
  · subst b
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp [h]

theorem lie_mem_adaptedSubmodule {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.adaptedSubmodule) (hq : q ∈ F.adaptedSubmodule) :
    ⁅p, q⁆ ∈ F.adaptedSubmodule := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum (coefficients p).support (coefficients q).support
    (fun a => monomial (R := ℚ) a (coefficients p a))
    (fun b => monomial (R := ℚ) b (coefficients q b))]
  apply Submodule.sum_mem
  intro a _
  apply Submodule.sum_mem
  intro b _
  rw [lie_monomial]
  apply F.monomial_mem_adaptedSubmodule
  exact F.lie_mem (hp a) (hq b)

noncomputable def adaptedLieSubalgebra : LieSubalgebra ℚ (VectorPolynomial σ ℚ L) :=
  { F.adaptedSubmodule with lie_mem' := F.lie_mem_adaptedSubmodule }

noncomputable def polynomialSubgroup : Subgroup
    (NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s
      (VectorPolynomial.lowerCentralSeries_eq_bot F.ordinary.lowerCentralSeries_eq_bot)) :=
  NilpotentLieBCHGroup.subgroup F.adaptedLieSubalgebra

abbrev PolynomialOrbit := ↥F.polynomialSubgroup

def PolynomialOrbit.log (p : F.PolynomialOrbit) : VectorPolynomial σ ℚ L := p.val.coord

noncomputable def polynomialOrbitEval (x : σ → ℤ) : F.PolynomialOrbit →* F.Group :=
  (NilpotentLieBCHGroup.map (evalLie (fun i => (x i : ℚ)))).comp F.polynomialSubgroup.subtype

@[simp] theorem polynomialOrbitEval_coord (p : F.PolynomialOrbit) (x : σ → ℤ) :
    (F.polynomialOrbitEval x p).coord = eval (fun i => (x i : ℚ)) (p.log F) := rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

noncomputable def lieQuotientDescend (I : LieIdeal ℚ L) (f : L →ₗ⁅ℚ⁆ M)
    (hI : ∀ x ∈ I, f x = 0) : (L ⧸ I) →ₗ⁅ℚ⁆ M :=
  { toLinearMap := I.toSubmodule.liftQ f.toLinearMap hI
    map_lie' {x y} := by
      obtain ⟨a, rfl⟩ := lieQuotientMap_surjective I x
      obtain ⟨b, rfl⟩ := lieQuotientMap_surjective I y
      exact f.map_lie a b }

@[simp] theorem lieQuotientDescend_mk (I : LieIdeal ℚ L) (f : L →ₗ⁅ℚ⁆ M)
    (hI : ∀ x ∈ I, f x = 0) (x : L) :
    lieQuotientDescend I f hI (lieQuotientMap I x) = f x := rfl

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s)

def quotientLie (I : LieIdeal ℚ L) (hI : F.layer (t + 1) ≤ I.toSubmodule) :
    NilpotentLieFiltration (L ⧸ I) t where
  layer j := (F.layer j).map (lieQuotientMap I).toLinearMap
  antitone := fun _ _ hij => Submodule.map_mono (F.antitone hij)
  one_eq_top := by
    rw [F.one_eq_top, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (lieQuotientMap_surjective I)
  lie_mem := by
    rintro i j x y ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨⁅a, b⁆, F.lie_mem ha hb, (lieQuotientMap I).map_lie a b⟩
  terminal := by
    apply bot_unique
    rintro x ⟨a, ha, rfl⟩
    exact (lieQuotientMap_eq_zero I a).mpr (hI ha)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

noncomputable def quotientStepHom : F.Group →* (F.quotientLie I hI).Group :=
  mapOfSteps (lieQuotientMap I)

@[simp] theorem quotientStepHom_coord (g : F.Group) :
    (F.quotientStepHom I hI g).coord = lieQuotientMap I g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareLayer (j : ℕ) : Submodule ℚ (L × L) where
  carrier := {x | x.1 ∈ F.layer j ∧ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1)}
  zero_mem' := by simp
  add_mem' hx hy := by
    refine ⟨(F.layer j).add_mem hx.1 hy.1, (F.layer j).add_mem hx.2.1 hy.2.1, ?_⟩
    change _ + _ - (_ + _) ∈ F.layer (j + 1)
    rw [show ∀ a b c d : L, a + b - (c + d) = (a - c) + (b - d) by intros; abel]
    exact (F.layer (j + 1)).add_mem hx.2.2 hy.2.2
  smul_mem' r x hx := by
    refine ⟨(F.layer j).smul_mem r hx.1, (F.layer j).smul_mem r hx.2.1, ?_⟩
    change r • x.1 - r • x.2 ∈ F.layer (j + 1)
    rw [← smul_sub]
    exact (F.layer (j + 1)).smul_mem r hx.2.2

@[simp] theorem mem_squareLayer (j : ℕ) (x : L × L) :
    x ∈ F.squareLayer j ↔
      x.1 ∈ F.layer j ∧ x.2 ∈ F.layer j ∧ x.1 - x.2 ∈ F.layer (j + 1) := Iff.rfl

theorem squareLayer_antitone : Antitone F.squareLayer := by
  intro i j hij x hx
  exact ⟨F.antitone hij hx.1, F.antitone hij hx.2.1,
    F.antitone (Nat.add_le_add_right hij 1) hx.2.2⟩

theorem squareLayer_lie_mem {i j : ℕ} {x y : L × L}
    (hx : x ∈ F.squareLayer i) (hy : y ∈ F.squareLayer j) :
    ⁅x, y⁆ ∈ F.squareLayer (i + j) := by
  refine ⟨F.lie_mem hx.1 hy.1, F.lie_mem hx.2.1 hy.2.1, ?_⟩
  change ⁅x.1, y.1⁆ - ⁅x.2, y.2⁆ ∈ F.layer (i + j + 1)
  have he : ⁅x.1, y.1⁆ - ⁅x.2, y.2⁆ =
      ⁅x.1 - x.2, y.1⁆ + ⁅x.2, y.1 - y.2⁆ := by
    simp only [sub_lie, lie_sub]
    abel
  rw [he]
  exact (F.layer (i + j + 1)).add_mem
    (by simpa only [Nat.add_right_comm i 1 j] using F.lie_mem hx.2.2 hy.1)
    (by simpa only [Nat.add_assoc] using F.lie_mem hx.2.1 hy.2.2)

def squareLieSubalgebra : LieSubalgebra ℚ (L × L) :=
  { F.squareLayer 1 with
    lie_mem' := fun hx hy => F.squareLayer_antitone (by omega) (F.squareLayer_lie_mem hx hy) }

@[simp] theorem mem_squareLieSubalgebra (x : L × L) :
    x ∈ F.squareLieSubalgebra ↔ x.1 - x.2 ∈ F.layer 2 := by
  change x ∈ F.squareLayer 1 ↔ _
  simp only [mem_squareLayer, F.one_eq_top, Submodule.mem_top, true_and]

def squareFiltration : NilpotentLieFiltration F.squareLieSubalgebra s where
  layer j := (F.squareLayer j).comap F.squareLieSubalgebra.incl.toLinearMap
  antitone := fun _ _ hij x hx => F.squareLayer_antitone hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.squareLayer_lie_mem hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    apply Prod.ext
    · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.1)
    · exact (Submodule.mem_bot ℚ).mp (F.terminal ▸ hx.2.1)

@[simp] theorem mem_squareFiltration_layer (j : ℕ) (x : F.squareLieSubalgebra) :
    x ∈ F.squareFiltration.layer j ↔ (x : L × L) ∈ F.squareLayer j := Iff.rfl

def squareFst : F.squareLieSubalgebra →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L L).comp F.squareLieSubalgebra.incl

def squareSnd : F.squareLieSubalgebra →ₗ⁅ℚ⁆ L :=
  (LieHom.snd ℚ L L).comp F.squareLieSubalgebra.incl

@[simp] theorem squareFst_apply (x : F.squareLieSubalgebra) : F.squareFst x = x.val.1 := rfl
@[simp] theorem squareSnd_apply (x : F.squareLieSubalgebra) : F.squareSnd x = x.val.2 := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareFstHom : F.squareFiltration.Group →* F.Group :=
  map F.squareFst

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ShiftedAdaptedIdeal
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def shiftedAdaptedSubmodule (w : σ → ℕ) (k : ℕ) :
    Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α + k)}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer _).add_mem (hp α) (hq α)
  smul_mem' r p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer _).smul_mem r (hp α)

theorem monomial_mem_shiftedAdaptedSubmodule (w : σ → ℕ) (k : ℕ)
    (α : σ →₀ ℕ) {a : L} (ha : a ∈ F.layer (Finsupp.weight w α + k)) :
    monomial (R := ℚ) α a ∈ F.shiftedAdaptedSubmodule w k := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_shiftedAdaptedSubmodule (w : σ → ℕ) {i j : ℕ}
    {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.shiftedAdaptedSubmodule w i) (hq : q ∈ F.shiftedAdaptedSubmodule w j) :
    ⁅p, q⁆ ∈ F.shiftedAdaptedSubmodule w (i + j) := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum]
  rw [sum_lie_sum]
  apply Submodule.sum_mem
  intro α _
  apply Submodule.sum_mem
  intro β _
  rw [lie_monomial]
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simpa only [map_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using F.lie_mem (hp α) (hq β)

noncomputable def shiftedAdaptedIdeal (w : σ → ℕ) : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { (F.shiftedAdaptedSubmodule w 1).comap (F.adaptedLieSubalgebra w).incl.toLinearMap with
    lie_mem := by
      intro p q hq
      have hp : (p : VectorPolynomial σ ℚ L) ∈ F.shiftedAdaptedSubmodule w 0 := by
        intro α
        simpa only [Nat.add_zero] using p.property α
      exact F.lie_mem_shiftedAdaptedSubmodule w hp hq }

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.FixedDensity.OrderedRemoval
namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

@[simp]
theorem simplexCoordinateSum_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateSum (r + 2) N
      (diagonalAPSimplex r N A p) = 0 := by
  simp [diagonalAPSimplex]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialIdeals
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def shiftedPolynomialIdeal (k : ℕ) : LieIdeal ℚ (F.adaptedLieSubalgebra w) :=
  { (F.shiftedAdaptedSubmodule w k).comap (F.adaptedLieSubalgebra w).incl.toLinearMap with
    lie_mem := by
      intro p q hq
      have hp : p.val ∈ F.shiftedAdaptedSubmodule w 0 := by
        intro α
        simpa only [Nat.add_zero] using p.property α
      change ⁅p.val, q.val⁆ ∈ F.shiftedAdaptedSubmodule w k
      have hq' : q.val ∈ F.shiftedAdaptedSubmodule w k := hq
      simpa only [Nat.zero_add] using F.lie_mem_shiftedAdaptedSubmodule w hp hq' }

@[simp] theorem mem_shiftedPolynomialIdeal (k : ℕ) (p : F.adaptedLieSubalgebra w) :
    p ∈ F.shiftedPolynomialIdeal w k ↔
      ∀ α, coefficients p.val α ∈ F.layer (Finsupp.weight w α + k) := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end


