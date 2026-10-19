-- Prove2me | Definitions.Def_OAIE3v2B118
-- name    : OAIE3v2B118
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:47:31.858385+00:00
-- url     : https://prove2.me/theorems/a501596e-8e1f-4a07-9bbd-e6ab2ef32c9e
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 120 of 311
-- statement:
--   Definitions bundle 120 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B101`, `OAIE3v2B102`, `OAIE3v2B104`, `OAIE3v2B105`, `OAIE3v2B106` of this split.
--
--   Modules: `Estimates/PetalComparisonTree.lean`, `Estimates/PolarizedCoefficientPermutation.lean`, `Estimates/ProductOrbitCongruence.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealMultidegreeQuotientOrbit.lean`, `Estimates/RealifiedDilationMultidegree.lean`, `Estimates/RealifiedTripleLayers.lean`, `Estimates/ReplicatedLieAction.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/WeightedOrbitNormalization.lean`, `Geometry/MultidegreeCoordinateFreezing.lean`, `Geometry/MultidegreeCoordinateSplit.lean`, `Lattices/SupportedQuotientLatticeFaithful.lean`, `Linear/MultiaffineTripleLayerBasis.lean`, `Linear/RankQuotientHeightBudget.lean`, `Linear/RealifiedTripleProjections.lean`, `Polynomial/AdditiveTriplePolynomialRestriction.lean`, `Polynomial/DilationPairPolynomial.lean`, `Polynomial/MultiaffineTriplePolynomial.lean`, `Polynomial/WeightedPolynomialRestriction.lean`, `Polynomial/ZeroDegreeCoordinate.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B101
import Definitions.Def_OAIE3v2B102
import Definitions.Def_OAIE3v2B104
import Definitions.Def_OAIE3v2B105
import Definitions.Def_OAIE3v2B106

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedTripleLayers
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedFiltration (c : σ → ℕ) :
    NilpotentLieFiltration (F.weightedSubalgebra c) (multidegreeWeight c bound) where
  layer n := (F.weightedLayer c (max 1 n)).toSubmodule.comap (F.weightedSubalgebra c).incl.toLinearMap
  antitone := by
    intro i j hij x hx
    exact F.weightedLayer_antitone c (max_le_max_left 1 hij) hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := by
    intro i j x y hx hy
    change ⁅(x : L), (y : L)⁆ ∈ F.weightedLayer c (max 1 (i + j))
    exact F.weightedLayer_antitone c (by omega : max 1 (i + j) ≤ max 1 i + max 1 j)
      (F.weightedLayer_lie_mem c hx hy)
  terminal := by
    apply bot_unique
    intro x hx
    change (x : L) ∈ F.weightedLayer c (max 1 (multidegreeWeight c bound + 1)) at hx
    rw [max_eq_right (by omega : 1 ≤ multidegreeWeight c bound + 1), F.weightedLayer_terminal c] at hx
    change x = 0
    exact Subtype.ext ((LieSubmodule.mem_bot (x : L)).mp hx)

theorem mem_weightedFiltration_layer (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n)
    (x : F.weightedSubalgebra c) :
    x ∈ (F.weightedFiltration c).layer n ↔ (x : L) ∈ F.weightedLayer c n := by
  change (x : L) ∈ F.weightedLayer c (max 1 n) ↔ _
  rw [max_eq_right hn]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedLayer_realification (c : σ → ℕ) (n : ℕ) :
    (F.realification.weightedLayer c n).toSubmodule =
      ((F.weightedLayer c n).toSubmodule.baseChange ℝ).restrictScalars ℚ := by
  simp only [weightedLayer, LieSubmodule.iSup_toSubmodule,
    real_baseChange_iSup, real_restrictScalars_iSup]
  rfl

noncomputable def realifiedWeightedEquiv (c : σ → ℕ) :
    (ℝ ⊗[ℚ] F.weightedSubalgebra c) ≃ₗ[ℚ] F.realification.weightedSubalgebra c :=
  ((realificationSubmoduleEquiv (F.weightedSubalgebra c).toSubmodule).restrictScalars ℚ).trans
    (LinearEquiv.ofEq _ _ (F.weightedLayer_realification c 1).symm)

theorem realifiedWeightedEquiv_coe (c : σ → ℕ) (x : ℝ ⊗[ℚ] F.weightedSubalgebra c) :
    (F.realifiedWeightedEquiv c x : ℝ ⊗[ℚ] L) =
      realificationLieHom (F.weightedSubalgebra c).incl x := rfl

theorem realifiedWeightedEquiv_mem_layer (c : σ → ℕ) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.weightedSubalgebra c) :
    x ∈ (F.weightedFiltration c).realification.layer n ↔
      F.realifiedWeightedEquiv c x ∈ (F.realification.weightedFiltration c).layer n := by
  change x ∈ ((F.weightedLayer c (max 1 n)).toSubmodule.comap
    (F.weightedSubalgebra c).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change (F.weightedSubalgebra c).incl.toLinearMap.baseChange ℝ x ∈
    (F.weightedLayer c (max 1 n)).toSubmodule.baseChange ℝ ↔
      (F.realifiedWeightedEquiv c x : ℝ ⊗[ℚ] L) ∈ F.realification.weightedLayer c (max 1 n)
  rw [F.realifiedWeightedEquiv_coe]
  have h := F.weightedLayer_realification c (max 1 n)
  change _ = _ at h
  change _ ↔ _ ∈ (F.realification.weightedLayer c (max 1 n)).toSubmodule
  rw [h]
  rfl

theorem realifiedWeightedEquiv_symm_mem_layer (c : σ → ℕ) (n : ℕ)
    (x : F.realification.weightedSubalgebra c) :
    (F.realifiedWeightedEquiv c).symm x ∈ (F.weightedFiltration c).realification.layer n ↔
      x ∈ (F.realification.weightedFiltration c).layer n := by
  rw [F.realifiedWeightedEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem coordinateActiveLayer_realification (i : σ) (n : ℕ) :
    F.realification.coordinateActiveLayer i n =
      ((F.coordinateActiveLayer i n).baseChange ℝ).restrictScalars ℚ := by
  rw [coordinateActiveLayer, coordinateActiveLayer, realification_inf]
  rfl

theorem realTripleEquiv_mem_layer (i : σ) (c : σ → ℕ) (n : ℕ)
    (x : ℝ ⊗[ℚ] (L × L × L)) :
    realTripleEquiv x ∈ F.realification.additiveTripleLayer i c n ↔
      x ∈ (F.additiveTripleLayer i c n).baseChange ℝ := by
  have hw (y : ℝ ⊗[ℚ] L) : y ∈ F.realification.weightedLayer c n ↔
      y ∈ (F.weightedLayer c n).toSubmodule.baseChange ℝ := by
    change y ∈ (F.realification.weightedLayer c n).toSubmodule ↔ _
    rw [F.weightedLayer_realification]
    rfl
  have ha (y : ℝ ⊗[ℚ] L) : y ∈ F.realification.coordinateActiveLayer i n ↔
      y ∈ (F.coordinateActiveLayer i n).baseChange ℝ := by
    rw [F.coordinateActiveLayer_realification]
    rfl
  rw [F.realification.mem_additiveTripleLayer, hw, ha, ha,
    realTripleEquiv_neutral, realTripleEquiv_left, realTripleEquiv_right]
  simp only [additiveTripleLayer, realification_inf, realification_comap,
    Submodule.mem_inf, Submodule.mem_comap]

noncomputable def realifiedTripleLayerEquiv (i : σ) (c : σ → ℕ) (n : ℕ) :
    ((F.additiveTripleLayer i c n).baseChange ℝ) ≃ₗ[ℚ]
      F.realification.additiveTripleLayer i c n where
  toFun x := ⟨realTripleEquiv x.val, (F.realTripleEquiv_mem_layer i c n x.val).mpr x.property⟩
  invFun x := ⟨realTripleEquiv.symm x.val, (F.realTripleEquiv_mem_layer i c n _).mp (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv x := Subtype.ext (realTripleEquiv.symm_apply_apply x.val)
  right_inv x := Subtype.ext (realTripleEquiv.apply_symm_apply x.val)
  map_add' x y := Subtype.ext (realTripleEquiv.map_add x.val y.val)
  map_smul' r x := Subtype.ext ((realTripleEquiv.restrictScalars ℚ).map_smul r x.val)

noncomputable def realifiedAdditiveTripleEquiv (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) :
    (ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) ≃ₗ[ℚ]
      F.realification.additiveTripleSubalgebra i hi c hc :=
  ((realificationSubmoduleEquiv (F.additiveTripleLayer i c 1)).restrictScalars ℚ).trans
    (F.realifiedTripleLayerEquiv i c 1)

theorem realifiedAdditiveTripleEquiv_coe (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    (F.realifiedAdditiveTripleEquiv i hi c hc x :
      (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) =
        realTripleEquiv (realificationLieHom (F.additiveTripleSubalgebra i hi c hc).incl x) := rfl

theorem realifiedAdditiveTripleEquiv_mem_layer (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    x ∈ (F.additiveTripleFiltration i hi c hc).realification.layer n ↔
      F.realifiedAdditiveTripleEquiv i hi c hc x ∈
        (F.realification.additiveTripleFiltration i hi c hc).layer n := by
  change x ∈ ((F.additiveTripleLayer i c n).comap
    (F.additiveTripleSubalgebra i hi c hc).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.additiveTripleSubalgebra i hi c hc).incl x ∈
    (F.additiveTripleLayer i c n).baseChange ℝ ↔
      (F.realifiedAdditiveTripleEquiv i hi c hc x :
        (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
          F.realification.additiveTripleLayer i c n
  rw [F.realifiedAdditiveTripleEquiv_coe, F.realTripleEquiv_mem_layer]

theorem realifiedAdditiveTripleEquiv_symm_mem_layer (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (n : ℕ)
    (x : F.realification.additiveTripleSubalgebra i hi c hc) :
    (F.realifiedAdditiveTripleEquiv i hi c hc).symm x ∈
        (F.additiveTripleFiltration i hi c hc).realification.layer n ↔
      x ∈ (F.realification.additiveTripleFiltration i hi c hc).layer n := by
  rw [F.realifiedAdditiveTripleEquiv_mem_layer, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.WeightedPolynomialRestriction
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedAdaptedSubmodule (c : σ → ℕ) (v : τ → ℕ) :
    Submodule ℚ (VectorPolynomial τ ℚ L) where
  carrier := {p | F.WeightedAdapted c v p}
  zero_mem' := by intro a; simp only [map_zero, Finsupp.zero_apply, LieSubmodule.zero_mem]
  add_mem' hp hq := by
    intro a
    rw [map_add, Finsupp.add_apply]
    exact (F.weightedLayer c _).add_mem (hp a) (hq a)
  smul_mem' r p hp := by
    intro a
    rw [map_smul, Finsupp.smul_apply]
    exact (F.weightedLayer c _).smul_mem r (hp a)

theorem weightedAdapted_monomial (c : σ → ℕ) (v : τ → ℕ) (a : τ →₀ ℕ) {x : L}
    (hx : x ∈ F.weightedLayer c (Finsupp.weight v a)) :
    F.WeightedAdapted c v (monomial a x) := by
  classical
  intro b
  by_cases h : a = b
  · subst b
    simpa only [coefficients_monomial, Finsupp.single_eq_same] using hx
  · simp [h]

theorem weightedAdapted_lie (c : σ → ℕ) (v : τ → ℕ) {p q : VectorPolynomial τ ℚ L}
    (hp : F.WeightedAdapted c v p) (hq : F.WeightedAdapted c v q) :
    F.WeightedAdapted c v ⁅p, q⁆ := by
  classical
  change ⁅p, q⁆ ∈ F.weightedAdaptedSubmodule c v
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
  apply F.weightedAdapted_monomial
  rw [map_add]
  exact F.weightedLayer_lie_mem c (hp a) (hq b)

noncomputable def weightedAdaptedLieSubalgebra (c : σ → ℕ) (v : τ → ℕ) :
    LieSubalgebra ℚ (VectorPolynomial τ ℚ L) :=
  { F.weightedAdaptedSubmodule c v with lie_mem' := F.weightedAdapted_lie c v }

theorem weightedAdapted_bch (c : σ → ℕ) (v : τ → ℕ) (t : ℕ)
    {p q : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (hq : F.WeightedAdapted c v q) :
    F.WeightedAdapted c v (lieBCH t p q) :=
  lieBCH_mem (F.weightedAdaptedLieSubalgebra c v) t hp hq

theorem weightedAdapted_constant (c : σ → ℕ) (v : τ → ℕ) (x : L) :
    F.WeightedAdapted c v (monomial 0 x) := by
  apply F.weightedAdapted_monomial
  simp only [map_zero, F.weightedLayer_zero, LieSubmodule.mem_top]

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem weightedAdapted_coefficients_mem (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    {p : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (a : τ →₀ ℕ) : coefficients p a ∈ F.weightedSubalgebra c := by
  classical
  by_cases ha : a = 0
  · rw [ha, hzero]
    exact (F.weightedSubalgebra c).zero_mem
  · have hi : ∃ i, a i ≠ 0 := by
      by_contra h
      push Not at h
      apply ha
      ext i
      exact h i
    obtain ⟨i, hi⟩ := hi
    have hpos : 1 ≤ Finsupp.weight v a := (hv i).trans_le (Finsupp.le_weight_of_ne_zero' v hi)
    exact F.weightedLayer_antitone c hpos (hp a)

noncomputable def restrictWeightedPolynomial (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    VectorPolynomial τ ℚ (F.weightedSubalgebra c) :=
  restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
    (F.weightedAdapted_coefficients_mem c v hv hp hzero)

theorem restrictWeightedPolynomial_adapted (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    (F.weightedFiltration c).Adapted v (F.restrictWeightedPolynomial c v hv p hp hzero) := by
  apply ((F.weightedFiltration c).adapted_iff_coefficients v _).mpr
  intro a
  change (coefficients (restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
      (F.weightedAdapted_coefficients_mem c v hv hp hzero)) a : L) ∈
    F.weightedLayer c (max 1 (Finsupp.weight v a))
  rw [coefficients_restrictCoefficients]
  by_cases hn : 1 ≤ Finsupp.weight v a
  · rw [max_eq_right hn]
    exact hp a
  · have hz : Finsupp.weight v a = 0 := by omega
    rw [hz]
    exact F.weightedAdapted_coefficients_mem c v hv hp hzero a

theorem restrictWeightedPolynomial_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (x : τ → ℚ) :
    (eval (V := F.weightedSubalgebra c) x
      (F.restrictWeightedPolynomial c v hv p hp hzero) : L) = eval x p :=
  eval_restrictCoefficients (F.weightedSubalgebra c).toSubmodule p
    (F.weightedAdapted_coefficients_mem c v hv hp hzero) x

noncomputable def restrictWeightedOrbit (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0) :
    (F.weightedFiltration c).PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog (F.restrictWeightedPolynomial c v hv p hp hzero)
    (F.restrictWeightedPolynomial_adapted c v hv p hp hzero)

theorem restrictWeightedOrbit_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (hzero : coefficients p 0 = 0)
    (x : τ → ℤ) :
    (((F.weightedFiltration c).polynomialOrbitEval v x
      (F.restrictWeightedOrbit c v hv p hp hzero)).coord : L) =
      eval (fun i => (x i : ℚ)) p :=
  F.restrictWeightedPolynomial_eval c v hv p hp hzero (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (I : LieIdeal ℚ L)
  (hI : F.layer (t + 1) ≤ I.toSubmodule)

theorem realQuotientPolynomialOrbit_eval {σ : Type*} {w : σ → ℕ}
    (q : F.realification.PolynomialOrbit w) (x : σ → ℤ) :
    (F.quotientLie I hI).realification.polynomialOrbitEval w x
      (F.realQuotientPolynomialOrbit I hI q) =
        F.realQuotientStepHom I hI (F.realification.polynomialOrbitEval w x q) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ)) (VectorPolynomial.map
    (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap q.log) = _
  rw [eval_map]
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealifiedTripleProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realAdditiveTripleProjection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3) :
    (F.additiveTripleFiltration i hi c hc).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.additiveTripleFiltration i hi c hc).lowerCentralSeries_eq_bot)
    (hM := F.ordinary.lowerCentralSeries_eq_bot) (F.additiveTripleProjection i hi c hc j)

theorem realifiedAdditiveTripleEquiv_projection (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (x : ℝ ⊗[ℚ] F.additiveTripleSubalgebra i hi c hc) :
    tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc x).val j =
      realificationLieHom (F.additiveTripleProjection i hi c hc j) x := by
  rw [F.realifiedAdditiveTripleEquiv_coe]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [realificationLieHom_tmul, realTripleEquiv_tmul, realificationLieHom_tmul]
    fin_cases j <;> rfl
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem realAdditiveTripleProjection_coord (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (j : Fin 3)
    (g : (F.additiveTripleFiltration i hi c hc).realification.Group) :
    (F.realAdditiveTripleProjection i hi c hc j g).coord =
      tripleToPi (F.realifiedAdditiveTripleEquiv i hi c hc g.coord).val j :=
  (F.realifiedAdditiveTripleEquiv_projection i hi c hc j g.coord).symm

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {τ L : Type*} [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s)

theorem restrictDilationPairPolynomial_adapted (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.dilationPairFiltration r).Adapted w
      (F.restrictDilationPairPolynomial r w hw q hq hq0) := by
  apply ((F.dilationPairFiltration r).adapted_iff_coefficients w _).mpr
  intro a
  change (coefficients (F.restrictDilationPairPolynomial r w hw q hq hq0) a : L × L) ∈
    F.dilationPairLayer r (Finsupp.weight w a)
  rw [restrictDilationPairPolynomial, coefficients_restrictCoefficients]
  exact hq a

noncomputable def restrictDilationPairOrbit (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) : (F.dilationPairFiltration r).PolynomialOrbit w :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F.restrictDilationPairPolynomial r w hw q hq hq0)
    (F.restrictDilationPairPolynomial_adapted r w hw q hq hq0)

theorem restrictDilationPairOrbit_eval (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) (x : τ → ℤ) :
    (((F.dilationPairFiltration r).polynomialOrbitEval w x
      (F.restrictDilationPairOrbit r w hw q hq hq0)).coord : L × L) =
      eval (fun j => (x j : ℚ)) q :=
  F.restrictDilationPairPolynomial_eval r w hw q hq hq0 _

theorem restrictDilationPairOrbit_zero (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.dilationPairFiltration r).polynomialOrbitEval w 0
      (F.restrictDilationPairOrbit r w hw q hq hq0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.dilationPairFiltration r).polynomialOrbitEval w 0
    (F.restrictDilationPairOrbit r w hw q hq hq0)).coord : L × L) = 0
  rw [F.restrictDilationPairOrbit_eval]
  simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hq0

theorem exists_dilationPairOrbit_of_coefficients (r : ℚ) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L))
    (hq : ∀ a, coefficients q a ∈ F.dilationPairLayer r (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    ∃ g : (F.dilationPairFiltration r).PolynomialOrbit w,
      (F.dilationPairFiltration r).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : τ → ℤ,
        (((F.dilationPairFiltration r).polynomialOrbitEval w x g).coord : L × L) =
          eval (fun j => (x j : ℚ)) q :=
  ⟨F.restrictDilationPairOrbit r w hw q hq hq0,
    F.restrictDilationPairOrbit_zero r w hw q hq hq0,
    F.restrictDilationPairOrbit_eval r w hw q hq hq0⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedGroupInclusion (c : σ → ℕ) :
    (F.weightedFiltration c).Group →* F.Group :=
  NilpotentLieBCHGroup.mapOfSteps (F.weightedSubalgebra c).incl

theorem weightedGroupInclusion_injective (c : σ → ℕ) :
    Function.Injective (F.weightedGroupInclusion c) :=
  NilpotentLieBCHGroup.mapOfSteps_injective _ (fun _ _ h => Subtype.ext h)

theorem weightedNormalizationLog_adapted (c : σ → ℕ) (v : τ → ℕ)
    {p : VectorPolynomial τ ℚ L} (hp : F.WeightedAdapted c v p) (a b : F.Group) :
    F.WeightedAdapted c v (F.weightedNormalizationLog p a b) :=
  F.weightedAdapted_bch c v s
    (F.weightedAdapted_bch c v s (F.weightedAdapted_constant c v _) hp)
    (F.weightedAdapted_constant c v _)

theorem weightedNormalizationLog_eval (p : VectorPolynomial τ ℚ L) (a b : F.Group)
    (x : τ → ℚ) :
    eval x (F.weightedNormalizationLog p a b) =
      (a⁻¹ * (⟨eval x p⟩ : F.Group) * b⁻¹).coord := by
  simp only [weightedNormalizationLog, eval_lieBCH, eval_monomial,
    Finsupp.prod_zero_index, one_smul, NilpotentLieBCHGroup.coord_mul,
    NilpotentLieBCHGroup.coord_inv]

theorem weightedNormalizationLog_zero (p : VectorPolynomial τ ℚ L) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    coefficients (F.weightedNormalizationLog p a b) 0 = 0 := by
  rw [← eval_zero_eq_coefficient, F.weightedNormalizationLog_eval, hzero]
  simp

noncomputable def normalizedWeightedOrbit (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    (F.weightedFiltration c).PolynomialOrbit v :=
  F.restrictWeightedOrbit c v hv (F.weightedNormalizationLog p a b)
    (F.weightedNormalizationLog_adapted c v hp a b) (F.weightedNormalizationLog_zero p a b hzero)

theorem normalizedWeightedOrbit_eval (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) (x : τ → ℤ) :
    F.weightedGroupInclusion c ((F.weightedFiltration c).polynomialOrbitEval v x
      (F.normalizedWeightedOrbit c v hv p hp a b hzero)) =
      a⁻¹ * (⟨eval (fun i => (x i : ℚ)) p⟩ : F.Group) * b⁻¹ := by
  apply NilpotentLieBCHGroup.ext
  change (((F.weightedFiltration c).polynomialOrbitEval v x
    (F.restrictWeightedOrbit c v hv _ _ _)).coord : L) = _
  rw [F.restrictWeightedOrbit_eval, F.weightedNormalizationLog_eval]

theorem normalizedWeightedOrbit_zero (c : σ → ℕ) (v : τ → ℕ) (hv : ∀ i, 0 < v i)
    (p : VectorPolynomial τ ℚ L) (hp : F.WeightedAdapted c v p) (a b : F.Group)
    (hzero : (⟨eval (fun _ => 0) p⟩ : F.Group) = a * b) :
    (F.weightedFiltration c).polynomialOrbitEval v 0
      (F.normalizedWeightedOrbit c v hv p hp a b hzero) = 1 := by
  apply F.weightedGroupInclusion_injective c
  rw [F.normalizedWeightedOrbit_eval, map_one]
  simp only [Pi.zero_apply, Int.cast_zero, hzero, inv_mul_cancel_left, mul_inv_cancel]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateFreezing
namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ : Type*} [DecidableEq σ]

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_normalized_frozen_orbit (S : Finset σ) (b : σ → ℤ)
    (p : F.PolynomialOrbit) (a γ : F.Group)
    (hzero : F.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).PolynomialOrbit (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.weightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).polynomialOrbitEval _ x q) =
          a⁻¹ * F.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
  let r := VectorPolynomial.substitute (freezingPolynomial S b) (p.log F)
  have hr : F.WeightedAdapted (retainedCoordinateWeight S) (fun _ : S => 1) r :=
    F.weightedAdapted_substitute _ _ _ (freezingPolynomial_support S b) (p.adapted F)
  have heval (x : S → ℤ) : (⟨eval (fun i => (x i : ℚ)) r⟩ : F.Group) =
      F.polynomialOrbitEval (freezeCoordinates S b x) p := by
    apply NilpotentLieBCHGroup.ext
    change eval (fun i => (x i : ℚ)) r = _
    simp only [r, eval_substitute, freezingPolynomial_eval, F.polynomialOrbitEval_coord]
  have hz : (⟨eval (fun _ => 0) r⟩ : F.Group) = a * γ := by
    simpa only [Pi.zero_apply, Int.cast_zero] using (heval 0).trans hzero
  refine ⟨F.normalizedWeightedOrbit _ _ (fun _ => by decide) r hr a γ hz,
    F.normalizedWeightedOrbit_zero _ _ (fun _ => by decide) r hr a γ hz, ?_⟩
  intro x
  rw [F.normalizedWeightedOrbit_eval, heval]

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

theorem symbolRationalGrid_mono {l m : ℕ} (hl : 0 < l) (hlm : l ∣ m)
    (g : F.RealPolynomialSymbolGroup v) (hg : F.SymbolRationalGrid b w hlayers v l g) :
    F.SymbolRationalGrid b w hlayers v m g :=
  realDenominatorGrid_subset_of_dvd hl hlm hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem realificationLieHom_incl_injective (K : LieSubalgebra ℚ L) :
    Function.Injective (realificationLieHom K.incl) := by
  let : Module.Free ℚ ℝ := Module.Free.of_divisionRing ℚ ℝ
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := ℝ) K.incl.toLinearMap
    (fun _ _ h => Subtype.ext h)

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realWeightedGroupInclusion (c : σ → ℕ) :
    (F.weightedFiltration c).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.weightedFiltration c).lowerCentralSeries_eq_bot)
    (hM := F.ordinary.lowerCentralSeries_eq_bot) (F.weightedSubalgebra c).incl

theorem realWeightedGroupInclusion_injective (c : σ → ℕ) :
    Function.Injective (F.realWeightedGroupInclusion c) := by
  intro x y hxy
  apply NilpotentLieBCHGroup.ext
  exact realificationLieHom_incl_injective (F.weightedSubalgebra c)
    (congrArg NilpotentLieBCHGroup.coord hxy)

noncomputable def realifiedWeightedOrbit {τ : Type*} (c : σ → ℕ) {v : τ → ℕ}
    (q : (F.realification.weightedFiltration c).PolynomialOrbit v) :
    (F.weightedFiltration c).realification.PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (VectorPolynomial.map (F.realifiedWeightedEquiv c).symm.toLinearMap q.log)
    ((F.realification.weightedFiltration c).adapted_map (F.weightedFiltration c).realification
      (F.realifiedWeightedEquiv c).symm.toLinearMap
      (fun n x hx => (F.realifiedWeightedEquiv_symm_mem_layer c n x).mpr hx) v q.adapted)

theorem realifiedWeightedOrbit_eval {τ : Type*} (c : σ → ℕ) {v : τ → ℕ}
    (q : (F.realification.weightedFiltration c).PolynomialOrbit v) (x : τ → ℤ) :
    F.realWeightedGroupInclusion c
      ((F.weightedFiltration c).realification.polynomialOrbitEval v x (F.realifiedWeightedOrbit c q)) =
        F.realification.weightedGroupInclusion c
          ((F.realification.weightedFiltration c).polynomialOrbitEval v x q) := by
  apply NilpotentLieBCHGroup.ext
  change realificationLieHom (F.weightedSubalgebra c).incl
    (eval (fun i => (x i : ℚ))
      (VectorPolynomial.map (F.realifiedWeightedEquiv c).symm.toLinearMap q.log)) = _
  rw [eval_map, ← F.realifiedWeightedEquiv_coe]
  exact congrArg (fun z : F.realification.weightedSubalgebra c => (z : ℝ ⊗[ℚ] L))
    ((F.realifiedWeightedEquiv c).apply_symm_apply _)

theorem exists_real_normalized_frozen_orbit [DecidableEq σ] (S : Finset σ) (b : σ → ℤ)
    (p : F.realification.PolynomialOrbit) (a γ : F.realification.Group)
    (hzero : F.realification.polynomialOrbitEval (freezeCoordinates S b 0) p = a * γ) :
    ∃ q : (F.weightedFiltration (retainedCoordinateWeight S)).realification.PolynomialOrbit
        (fun _ : S => 1),
      (F.weightedFiltration (retainedCoordinateWeight S)).realification.polynomialOrbitEval _ 0 q = 1 ∧
      ∀ x : S → ℤ, F.realWeightedGroupInclusion (retainedCoordinateWeight S)
        ((F.weightedFiltration (retainedCoordinateWeight S)).realification.polynomialOrbitEval _ x q) =
          a⁻¹ * F.realification.polynomialOrbitEval (freezeCoordinates S b x) p * γ⁻¹ := by
  obtain ⟨q, hq, hval⟩ := F.realification.exists_normalized_frozen_orbit S b p a γ hzero
  refine ⟨F.realifiedWeightedOrbit _ q, ?_, ?_⟩
  · apply F.realWeightedGroupInclusion_injective (retainedCoordinateWeight S)
    rw [F.realifiedWeightedOrbit_eval, hq, map_one, map_one]
  · intro x
    rw [F.realifiedWeightedOrbit_eval, hval]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AdditiveTriplePolynomialRestriction
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ τ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem restrictAdditiveTripleOrbit_zero (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    (F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0
      (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0
    (F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0)).coord : L × L × L) = 0
  rw [F.restrictAdditiveTripleOrbit_eval]
  simpa only [Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using hq0

theorem exists_additiveTripleOrbit_of_coefficients (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) (w : τ → ℕ) (hw : ∀ j, 0 < w j)
    (q : VectorPolynomial τ ℚ (L × L × L))
    (hq : ∀ a, coefficients q a ∈ F.additiveTripleLayer i c (Finsupp.weight w a))
    (hq0 : coefficients q 0 = 0) :
    ∃ g : (F.additiveTripleFiltration i hi c hc).PolynomialOrbit w,
      (F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : τ → ℤ,
        (((F.additiveTripleFiltration i hi c hc).polynomialOrbitEval w x g).coord : L × L × L) =
          eval (fun j => (x j : ℚ)) q :=
  ⟨F.restrictAdditiveTripleOrbit i hi c hc w hw q hq hq0,
    F.restrictAdditiveTripleOrbit_zero i hi c hc w hw q hq hq0,
    F.restrictAdditiveTripleOrbit_eval i hi c hc w hw q hq hq0⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DilationPairPolynomial
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ L : Type*} [AddCommGroup L] [Module ℚ L]

theorem eval_dilationPair (w : σ → ℕ) (q : ℚ) (p : VectorPolynomial σ ℚ L) (x : σ → ℚ) :
    eval x (dilationPair w q p) = (eval (fun i => q ^ w i * x i) p, eval x p) := by
  simp only [dilationPair, eval_pair, eval_weightedDilation]

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem dilationPair_coefficients (w : σ → ℕ) (q : ℚ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted w p) (a : σ →₀ ℕ) :
    coefficients (dilationPair w q p) a ∈ F.dilationPairLayer q (Finsupp.weight w a) := by
  rw [coefficients_dilationPair, F.mem_dilationPairLayer]
  have ha := (F.adapted_iff_coefficients w p).mp hp a
  exact ⟨(F.layer _).smul_mem _ ha, ha, by simp⟩

theorem exists_dilationPair_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i) (q : ℚ)
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) (hp0 : coefficients p 0 = 0) :
    ∃ g : (F.dilationPairFiltration q).PolynomialOrbit w,
      (F.dilationPairFiltration q).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairFiltration q).polynomialOrbitEval w x g).coord : L × L) =
          (eval (fun i => q ^ w i * (x i : ℚ)) p, eval (fun i => (x i : ℚ)) p) := by
  obtain ⟨g, hg0, hg⟩ := F.exists_dilationPairOrbit_of_coefficients q w hw (dilationPair w q p)
    (F.dilationPair_coefficients w q hp) (by simp only [coefficients_dilationPair, hp0, smul_zero]; rfl)
  exact ⟨g, hg0, fun x => (hg x).trans (eval_dilationPair w q p _)⟩

theorem exists_integer_dilationPair_orbit (w : σ → ℕ) (hw : ∀ i, 0 < w i) (q : ℤ)
    (p : F.PolynomialOrbit w) (hp0 : F.polynomialOrbitEval w 0 p = 1) :
    ∃ g : (F.dilationPairFiltration (q : ℚ)).PolynomialOrbit w,
      (F.dilationPairFiltration (q : ℚ)).polynomialOrbitEval w 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairFiltration (q : ℚ)).polynomialOrbitEval w x g).coord : L × L) =
          ((F.polynomialOrbitEval w (fun i => q ^ w i * x i) p).coord,
            (F.polynomialOrbitEval w x p).coord) := by
  have hz : coefficients p.log 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  obtain ⟨g, hg0, hg⟩ := F.exists_dilationPair_orbit w hw (q : ℚ) p.log p.adapted hz
  exact ⟨g, hg0, fun x => by
    simpa only [F.polynomialOrbitEval_coord, Int.cast_mul, Int.cast_pow] using hg x⟩

end NilpotentLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.MultidegreeCoordinateSplit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem split_substitution_zero_weighted (i : σ)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) :
    F.WeightedAdapted (omittedCoordinateWeight i) (fun _ : Option σ => 1)
      (VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) :=
  F.weightedAdapted_substitute _ _ _ (splitCoordinatePolynomial_zero_support i) hp

theorem split_substitution_sub_mem_active (i : σ)
    (u : MvPolynomial (Option σ) ℚ) (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : Option σ →₀ ℕ) :
    coefficients (VectorPolynomial.substitute (splitCoordinatePolynomial i u) p -
      VectorPolynomial.substitute (splitCoordinatePolynomial i 0) p) a ∈
        F.coordinateActiveLayer i (Finsupp.weight (fun _ : Option σ => 1) a) := by
  refine ⟨F.split_substitution_sub_mem_coordinate i u 0 hp a, ?_⟩
  rw [map_sub, Finsupp.sub_apply]
  exact (F.ordinary.layer _).sub_mem
    ((F.ordinary.adapted_iff_coefficients _ _).mp (F.split_substitution_adapted i u hu hp) a)
    ((F.ordinary.adapted_iff_coefficients _ _).mp
      (F.split_substitution_adapted i 0 (Submodule.zero_mem _) hp) a)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.MultiaffineTriplePolynomial
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ V : Type*} [DecidableEq σ] [AddCommGroup V] [Module ℚ V]

theorem eval_splitTriple (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) (x : Option σ → ℚ) :
    eval x (splitTriple i u v p) =
      (eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x (u + v))) p,
       eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x u)) p,
       eval (Function.update (fun j => x (some j)) i (MvPolynomial.aeval (R := ℚ) x v)) p) := by
  simp only [splitTriple, eval_pair, eval_substitute, splitCoordinatePolynomial_eval]

theorem splitTriple_zero (i : σ) (u v : MvPolynomial (Option σ) ℚ)
    (p : VectorPolynomial σ ℚ V) (hp : coefficients p 0 = 0)
    (hu : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) u = 0)
    (hv : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) v = 0) :
    coefficients (splitTriple i u v p) 0 = 0 := by
  rw [← eval_zero_eq_coefficient, eval_splitTriple]
  simp only [map_add, hu, hv, add_zero, Function.update_eq_self, eval_zero_eq_coefficient, hp]
  rfl

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem splitTriple_coefficient_mem (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hv : v ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    {p : VectorPolynomial σ ℚ L} (hp : F.Adapted p) (a : Option σ →₀ ℕ) :
    coefficients (splitTriple i u v p) a ∈
      F.additiveTripleLayer i (omittedCoordinateWeight i) (Finsupp.weight (fun _ : Option σ => 1) a) := by
  rw [F.mem_additiveTripleLayer, F.splitTriple_neutral i hi u v hp,
    F.splitTriple_left i hi u v hp, F.splitTriple_right i hi u v hp]
  exact ⟨F.split_substitution_zero_weighted i hp a,
    F.split_substitution_sub_mem_active i u hu hp a,
    F.split_substitution_sub_mem_active i v hv hp a⟩

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PolarizedCoefficientPermutation
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem strictUpperLayer_zero : F.strictUpperLayer 0 = ⊤ := by
  have h : F.ordinary.layer 1 ≤ (F.strictUpperLayer 0).toSubmodule := by
    rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    have hlt : (0 : σ → ℕ) < a := by
      refine lt_iff_le_not_ge.mpr ⟨fun _ => Nat.zero_le _, ?_⟩
      intro hzero
      have heq : a = 0 := le_antisymm hzero (fun _ => Nat.zero_le _)
      simp only [heq, Pi.zero_apply, Finset.sum_const_zero] at ha
      omega
    intro x hx
    exact F.layer_le_strictUpperLayer hlt hx
  apply top_unique
  intro x _
  exact h (by simp only [F.ordinary.one_eq_top, Submodule.mem_top])

theorem dilationPairLayer_zero (q : ℚ) : F.dilationPairLayer q 0 = ⊤ := by
  apply top_unique
  intro x _
  rw [F.mem_dilationPairLayer]
  simp only [F.zero_eq_top, F.strictUpperLayer_zero, Submodule.mem_top, LieSubmodule.mem_top,
    true_and]

theorem dilationPair_degree_comap (q : ℚ) (n : ℕ) :
    (F.ordinary.dilationPairFiltration q).layer n =
      ⨆ (a : σ → ℕ) (_ha : n ≤ ∑ i, a i),
        (F.dilationPairLayer q a).comap (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap := by
  let K := F.ordinary.dilationPairSubalgebra q
  let ι := K.incl.toLinearMap
  by_cases hn : n = 0
  · subst n
    have hleft : (F.ordinary.dilationPairFiltration q).layer 0 = ⊤ := by
      apply top_unique
      rw [← (F.ordinary.dilationPairFiltration q).one_eq_top]
      exact (F.ordinary.dilationPairFiltration q).antitone (by decide : 0 ≤ 1)
    rw [hleft]
    symm
    apply top_unique
    apply le_iSup_of_le (0 : σ → ℕ)
    apply le_iSup_of_le (show 0 ≤ ∑ _ : σ, 0 from Nat.zero_le _)
    rw [F.dilationPairLayer_zero, Submodule.comap_top]
  · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    have hr (a : σ → ℕ) (ha : n ≤ ∑ i, a i) :
        F.dilationPairLayer q a ≤ LinearMap.range ι := by
      intro x hx
      exact ⟨⟨x, F.dilationPairLayer_le_subalgebra q a (hn1.trans ha) hx⟩, rfl⟩
    change (F.ordinary.dilationPairLayer q n).comap ι = _
    rw [← F.dilationPairDegreeLayer_eq, dilationPairDegreeLayer]
    rw [submodule_comap_iSup_of_le_range ι Subtype.val_injective _
      (fun a => iSup_le (fun ha => hr a ha))]
    apply iSup_congr
    intro a
    exact submodule_comap_iSup_of_le_range ι Subtype.val_injective _ (hr a)

noncomputable def dilationPairMultidegree (q : ℚ) :
    MultidegreeLieFiltration σ (F.ordinary.dilationPairSubalgebra q) s bound where
  ordinary := F.ordinary.dilationPairFiltration q
  layer a := (F.dilationPairLayer q a).comap (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.dilationPairLayer_antitone q h hx
  zero_eq_top := by rw [F.dilationPairLayer_zero, Submodule.comap_top]
  lie_mem := fun hx hy => F.dilationPairLayer_lie_mem q hx hy
  terminal a ha := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × L)
    have h : x.val ∈ F.dilationPairLayer q a := hx
    simpa only [F.dilationPairLayer_terminal q a ha, Submodule.mem_bot] using h
  degree_eq := F.dilationPair_degree_comap q

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

namespace MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem dilationPair_top_group_relation (q : ℤ)
    (g : (F.dilationPairMultidegree (q : ℚ)).Group)
    (hg : g ∈ (F.dilationPairMultidegree (q : ℚ)).subgroup bound) :
    (NilpotentLieBCHGroup.map (F.ordinary.dilationPairFirst (q : ℚ)) g : F.Group) =
      (NilpotentLieBCHGroup.map (F.ordinary.dilationPairSecond (q : ℚ)) g) ^ (q ^ ∑ i, bound i) := by
  apply NilpotentLieBCHGroup.ext
  rw [NilpotentLieBCHGroup.coord_zpow]
  change g.coord.val.1 = (q ^ ∑ i, bound i) • g.coord.val.2
  rw [← Int.cast_smul_eq_zsmul ℚ, Int.cast_pow]
  exact F.dilationPairLayer_top_relation (q : ℚ) hg

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem exists_splitTriple_orbit (i : σ) (hi : bound i ≤ 1)
    (u v : MvPolynomial (Option σ) ℚ)
    (hu : u ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hv : v ∈ weightedSupportLE (fun _ : Option σ => 1) 1)
    (hu0 : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) u = 0)
    (hv0 : MvPolynomial.aeval (R := ℚ) (fun _ : Option σ => (0 : ℚ)) v = 0)
    (p : VectorPolynomial σ ℚ L) (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          eval (fun j => (x j : ℚ)) (splitTriple i u v p) :=
  F.exists_additiveTripleOrbit_of_coefficients i hi (omittedCoordinateWeight i)
    (omittedCoordinateWeight_le_one i) (fun _ => 1) (fun _ => by decide) (splitTriple i u v p)
    (F.splitTriple_coefficient_mem i hi u v hu hv hp) (splitTriple_zero i u v p hp0 hu0 hv0)

theorem exists_coordinateAddition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.PolynomialOrbit) (hp0 : F.polynomialOrbitEval 0 p = 1) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        (((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).polynomialOrbitEval _ x g).coord : L × L × L) =
          ((F.polynomialOrbitEval
              (Function.update (fun j => x (some j)) i (x (some i) + x none)) p).coord,
           (F.polynomialOrbitEval (fun j => x (some j)) p).coord,
           (F.polynomialOrbitEval (Function.update (fun j => x (some j)) i (x none)) p).coord) := by
  have hz : coefficients (p.log F) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  have hX (j : Option σ) : (MvPolynomial.X j : MvPolynomial (Option σ) ℚ) ∈
      weightedSupportLE (fun _ : Option σ => 1) 1 := by
    simpa only [MvPolynomial.X, Finsupp.weight_single, smul_eq_mul, mul_one] using
      weightedSupportLE_monomial (fun _ : Option σ => 1) (Finsupp.single j 1) (1 : ℚ)
  obtain ⟨g, hg0, hg⟩ := F.exists_splitTriple_orbit i hi (MvPolynomial.X (some i)) (MvPolynomial.X none)
    (hX _) (hX _) (by simp) (by simp) (p.log F) (p.adapted F) hz
  refine ⟨g, hg0, fun x => ?_⟩
  have hcast (y : σ → ℤ) (n : ℤ) : (fun j => (Function.update y i n j : ℚ)) =
      Function.update (fun j => (y j : ℚ)) i (n : ℚ) := by
    funext j
    by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  simpa only [eval_splitTriple, F.polynomialOrbitEval_coord, map_add, MvPolynomial.aeval_X,
    Function.update_eq_self, hcast, Int.cast_add] using hg x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def dilationPairLog (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    VectorPolynomial σ ℚ (F.ordinary.dilationPairSubalgebra q) :=
  F.ordinary.restrictDilationPairPolynomial q (fun _ : σ => 1) (fun _ => by decide)
    (dilationPair (fun _ : σ => 1) q p)
    (F.ordinary.dilationPair_coefficients _ q (F.adapted_ordinary hp))
    (by simp only [coefficients_dilationPair, hp0, smul_zero]; rfl)

theorem dilationPairMultidegree_mem_layer (q : ℚ) (a : σ → ℕ)
    (x : F.ordinary.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairMultidegree q).layer a ↔ x.val ∈ F.dilationPairLayer q a := Iff.rfl

theorem dilationPairLog_adapted (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).Adapted (F.dilationPairLog q p hp hp0) := by
  intro a
  rw [F.dilationPairMultidegree_mem_layer]
  rw [dilationPairLog, NilpotentLieFiltration.restrictDilationPairPolynomial,
    coefficients_restrictCoefficients, coefficients_dilationPair]
  have hw : Finsupp.weight (fun _ : σ => 1) a = ∑ i, a i := by
    simp only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one]
  rw [hw]
  exact F.dilationPairLayer_diagonal q _ (hp a)

omit [DecidableEq σ] in
theorem dilationPairLog_eval (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) (x : σ → ℚ) :
    (eval (V := F.ordinary.dilationPairSubalgebra q) x (F.dilationPairLog q p hp hp0) : L × L) =
      (eval (fun i => q * x i) p, eval x p) := by
  rw [dilationPairLog, NilpotentLieFiltration.restrictDilationPairPolynomial_eval,
    eval_dilationPair]
  simp only [pow_one]

noncomputable def dilationPairPolynomialOrbit (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).PolynomialOrbit :=
  (F.dilationPairMultidegree q).polynomialOrbitOfLog
    (F.dilationPairLog q p hp hp0) (F.dilationPairLog_adapted q p hp hp0)

theorem dilationPairPolynomialOrbit_eval (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) (x : σ → ℤ) :
    (((F.dilationPairMultidegree q).polynomialOrbitEval x
      (F.dilationPairPolynomialOrbit q p hp hp0)).coord : L × L) =
      (eval (fun i => q * (x i : ℚ)) p, eval (fun i => (x i : ℚ)) p) :=
  F.dilationPairLog_eval q p hp hp0 _

theorem dilationPairPolynomialOrbit_zero (q : ℚ) (p : VectorPolynomial σ ℚ L)
    (hp : F.Adapted p) (hp0 : coefficients p 0 = 0) :
    (F.dilationPairMultidegree q).polynomialOrbitEval 0
      (F.dilationPairPolynomialOrbit q p hp hp0) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change (((F.dilationPairMultidegree q).polynomialOrbitEval 0
    (F.dilationPairPolynomialOrbit q p hp hp0)).coord : L × L) = (0 : L × L)
  have h := F.dilationPairPolynomialOrbit_eval q p hp hp0 0
  simp only [Pi.zero_apply, Int.cast_zero, mul_zero, eval_zero_eq_coefficient, hp0] at h
  exact h

theorem exists_integer_dilationPair_orbit (q : ℤ) (p : F.PolynomialOrbit)
    (hp0 : F.polynomialOrbitEval 0 p = 1) :
    ∃ g : (F.dilationPairMultidegree (q : ℚ)).PolynomialOrbit,
      (F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval 0 g = 1 ∧
      ∀ x : σ → ℤ,
        (((F.dilationPairMultidegree (q : ℚ)).polynomialOrbitEval x g).coord : L × L) =
          ((F.polynomialOrbitEval (fun i => q * x i) p).coord, (F.polynomialOrbitEval x p).coord) := by
  have hz : coefficients (p.log F) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp0
    simpa only [F.polynomialOrbitEval_coord, NilpotentLieBCHGroup.coord_one,
      Pi.zero_apply, Int.cast_zero, eval_zero_eq_coefficient] using h
  refine ⟨F.dilationPairPolynomialOrbit (q : ℚ) (p.log F) (p.adapted F) hz,
    F.dilationPairPolynomialOrbit_zero (q : ℚ) (p.log F) (p.adapted F) hz, fun x => ?_⟩
  simpa only [F.polynomialOrbitEval_coord, Int.cast_mul] using
    F.dilationPairPolynomialOrbit_eval (q : ℚ) (p.log F) (p.adapted F) hz x

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductOrbitCongruence
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ : Type*} [Fintype ι] [Fintype σ] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {bound : σ → ℕ}
  (F : ∀ i, MultidegreeLieFiltration σ (L i) s bound)

theorem realProductSingle_mem_layer (i : ι) (a : σ → ℕ) {x : ℝ ⊗[ℚ] L i}
    (hx : x ∈ (F i).realification.layer a) :
    realProductSingle i x ∈ (pi F).realification.layer a := by
  classical
  apply baseChange_mem_of_mapsTo ((F i).layer a) ((pi F).layer a)
    (LinearMap.single ℚ L i) _ hx
  intro y hy
  apply (mem_pi_layer F a _).mpr
  intro j
  change Pi.single i y j ∈ (F j).layer a
  by_cases hji : j = i
  · subst j
    simpa only [Pi.single_eq_same] using hy
  · rw [Pi.single_eq_of_ne hji]
    exact Submodule.zero_mem _

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealMultidegreeQuotientOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (I : LieIdeal ℚ L)

theorem realQuotientMultidegree_mem_layer (a : σ → ℕ) {x : ℝ ⊗[ℚ] L}
    (hx : x ∈ F.realification.layer a) :
    realificationLieHom (lieQuotientMap I) x ∈ (F.quotientMultidegree I).realification.layer a := by
  change realificationLieHom (lieQuotientMap I) x ∈
    ((F.layer a).map (lieQuotientMap I).toLinearMap).baseChange ℝ
  rw [realification_map]
  exact ⟨x, hx, rfl⟩

noncomputable def realQuotientMultidegreeMap :
    F.realification.Group →* (F.quotientMultidegree I).realification.Group :=
  realificationMap (hnil := F.ordinary.lowerCentralSeries_eq_bot)
    (hM := (F.quotientMultidegree I).ordinary.lowerCentralSeries_eq_bot) (lieQuotientMap I)

noncomputable def realQuotientMultidegreeOrbit (g : F.realification.PolynomialOrbit) :
    (F.quotientMultidegree I).realification.PolynomialOrbit :=
  (F.quotientMultidegree I).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) (by
        intro a
        rw [coefficients_map]
        exact F.realQuotientMultidegree_mem_layer I (fun i => a i)
          (PolynomialOrbit.adapted F.realification g a))

theorem realQuotientMultidegreeOrbit_eval (g : F.realification.PolynomialOrbit) (x : σ → ℤ) :
    (F.quotientMultidegree I).realification.polynomialOrbitEval x (F.realQuotientMultidegreeOrbit I g) =
      F.realQuotientMultidegreeMap I (F.realification.polynomialOrbitEval x g) := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun i => (x i : ℚ))
    (VectorPolynomial.map (realLieHomToRat (realificationLieHom (lieQuotientMap I))).toLinearMap
      (PolynomialOrbit.log F.realification g)) = _
  rw [eval_map]
  rfl

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedDilationMultidegree
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem strictUpperLayer_realification (a : σ → ℕ) :
    (F.realification.strictUpperLayer a).toSubmodule =
      ((F.strictUpperLayer a).toSubmodule.baseChange ℝ).restrictScalars ℚ := by
  simp only [strictUpperLayer, LieSubmodule.iSup_toSubmodule,
    real_baseChange_iSup, real_restrictScalars_iSup]
  rfl

theorem realPairEquiv_mem_dilationPairLayer (q : ℚ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] (L × L)) :
    realPairEquiv x ∈ F.realification.dilationPairLayer q a ↔
      x ∈ (F.dilationPairLayer q a).baseChange ℝ := by
  change realPairEquiv x ∈ scaledPairLayer (F.realification.layer a)
    (F.realification.strictUpperLayer a).toSubmodule (q ^ ∑ i, a i) ↔ _
  rw [F.strictUpperLayer_realification]
  exact realPairEquiv_mem_scaledPairLayer (F.layer a) (F.strictUpperLayer a).toSubmodule _ x

theorem realifiedDilationPairEquiv_mem_multidegree (q : ℚ) (a : σ → ℕ)
    (x : ℝ ⊗[ℚ] F.ordinary.dilationPairSubalgebra q) :
    x ∈ (F.dilationPairMultidegree q).realification.layer a ↔
      F.ordinary.realifiedDilationPairEquiv q x ∈ (F.realification.dilationPairMultidegree q).layer a := by
  change x ∈ ((F.dilationPairLayer q a).comap
    (F.ordinary.dilationPairSubalgebra q).incl.toLinearMap).baseChange ℝ ↔ _
  rw [realification_comap]
  change realificationLieHom (F.ordinary.dilationPairSubalgebra q).incl x ∈
    (F.dilationPairLayer q a).baseChange ℝ ↔
      (F.ordinary.realifiedDilationPairEquiv q x : (ℝ ⊗[ℚ] L) × (ℝ ⊗[ℚ] L)) ∈
        F.realification.dilationPairLayer q a
  rw [F.ordinary.realifiedDilationPairEquiv_coe, F.realPairEquiv_mem_dilationPairLayer]

theorem realifiedDilationPairEquiv_symm_mem_multidegree (q : ℚ) (a : σ → ℕ)
    (x : F.ordinary.realification.dilationPairSubalgebra q) :
    (F.ordinary.realifiedDilationPairEquiv q).symm x ∈
        (F.dilationPairMultidegree q).realification.layer a ↔
      x ∈ (F.realification.dilationPairMultidegree q).layer a := by
  rw [F.realifiedDilationPairEquiv_mem_multidegree, LinearEquiv.apply_symm_apply]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ReplicatedLieAction
namespace OAI

section

namespace Erdos3

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedTopCoefficient :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) →ₗ[ℚ] F.layer bound where
  toFun x := ⟨squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound)), by
    have h := (x.property (SquarefreeIndex.full (ReplicatedIndex bound))).1
    simpa only [replicated_blockDegree_full] using h⟩
  map_add' x y := by
    apply Subtype.ext
    exact congrFun (map_add squarefreePolynomialEquiv x.val y.val) _
  map_smul' r x := by
    apply Subtype.ext
    exact congrFun (map_smul squarefreePolynomialEquiv r x.val) _

theorem replicatedTopCoefficient_apply
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    (F.replicatedTopCoefficient x).val =
      squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound)) := rfl

end MultidegreeLieFiltration

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators TensorProduct

namespace MultidegreeLieFiltration

theorem ordinary_top_eq {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) :
    F.ordinary.layer (∑ i, bound i) = F.layer bound := by
  classical
  apply le_antisymm
  · rw [F.degree_eq]
    apply iSup_le
    intro a
    apply iSup_le
    intro ha
    by_cases hle : a ≤ bound
    · have hsum : (∑ i, a i) = ∑ i, bound i :=
        le_antisymm (Finset.sum_le_sum (fun i _ => hle i)) ha
      have heq : a = bound := funext (fun i =>
        (Finset.sum_eq_sum_iff_of_le (fun j _ => hle j)).mp hsum i (Finset.mem_univ i))
      rw [heq]
    · rw [F.terminal a hle]
      exact bot_le
  · exact F.layer_le_ordinary bound

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SupportedQuotientLatticeFaithful
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

open Module
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem mem_realification_integral_lattice_iff (b : Basis ι ℚ L)
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil)) (N : ℕ)
    (hgrid : bchSubgroupCoordinates b Γ = scaledIntegerGrid N)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil)) :
    g ∈ Γ.map realificationHom ↔
      ∃ z : ι → ℤ, ∀ i, (b.baseChange ℝ).repr g.coord i = (N : ℝ) * (z i : ℝ) := by
  constructor
  · intro hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    have hc := (bchSubgroupCoordinates_repr b Γ a).mpr ha
    rw [hgrid] at hc
    obtain ⟨z, hz⟩ := hc
    refine ⟨z, fun i => ?_⟩
    rw [← Basis.equivFun_apply, realificationHom_coordinates]
    have hi := congrFun hz i
    change b.repr a.coord i = (N : ℚ) * (z i : ℚ) at hi
    change (b.repr a.coord i : ℝ) = _
    rw [hi]
    push_cast
    rfl
  · rintro ⟨z, hz⟩
    let a : NilpotentLieBCHGroup L s hnil :=
      ⟨b.equivFun.symm (fun i => (N : ℚ) * (z i : ℚ))⟩
    have ha : a ∈ Γ := by
      apply (bchSubgroupCoordinates_repr b Γ a).mp
      rw [hgrid]
      change b.equivFun (b.equivFun.symm _) ∈ scaledIntegerGrid N
      rw [LinearEquiv.apply_symm_apply]
      exact ⟨z, rfl⟩
    refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
    apply NilpotentLieBCHGroup.ext
    apply (b.baseChange ℝ).equivFun.injective
    rw [realificationHom_coordinates]
    funext i
    change (b.equivFun (b.equivFun.symm _) i : ℝ) = _
    rw [LinearEquiv.apply_symm_apply]
    push_cast
    exact (hz i).symm

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankQuotientHeightBudget
namespace OAI

section

namespace Erdos3

open Module
open scoped Matrix

theorem exists_bounded_submodule_basis_from_spanning
    {L μ κ : Type*} [AddCommGroup L] [Module ℚ L] [Fintype μ]
    (b : Basis μ ℚ L) (V : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = V) {H : ℕ}
    (hv : ∀ i j, RationalHeightLE (b.repr (v i) j) H) :
    ∃ e : Basis (Fin (Module.finrank ℚ V)) ℚ V,
      ∀ i j, RationalHeightLE (b.repr (e i : L) j) H := by
  classical
  let : FiniteDimensional ℚ L := b.finiteDimensional_of_finite
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hspan] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro i j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz i
  rw [← hk]
  exact hv k j

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.MultiaffineTripleLayerBasis
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def additiveTripleLayerEquiv (i : σ) (c : σ → ℕ) (n : ℕ) :
    (F.weightedLayer c n × F.coordinateActiveLayer i n × F.coordinateActiveLayer i n)
      ≃ₗ[ℚ] F.additiveTripleLayer i c n where
  toFun x := ⟨tripleAssemble (x.1 : L) (x.2.1 : L) (x.2.2 : L), by
    rw [F.mem_additiveTripleLayer, tripleNeutral_assemble, tripleLeft_assemble,
      tripleRight_assemble]
    exact ⟨x.1.property, x.2.1.property, x.2.2.property⟩⟩
  invFun x := (⟨tripleNeutral x.val, x.property.1⟩,
    ⟨tripleLeft x.val, x.property.2.1⟩, ⟨tripleRight x.val, x.property.2.2⟩)
  left_inv x := by
    apply Prod.ext
    · exact Subtype.ext (tripleNeutral_assemble _ _ _)
    · exact Prod.ext (Subtype.ext (tripleLeft_assemble _ _ _))
        (Subtype.ext (tripleRight_assemble _ _ _))
  right_inv x := Subtype.ext (tripleAssemble_decompose x.val)
  map_add' x y := by
    apply Subtype.ext
    ext <;> simp only [tripleAssemble, Prod.fst_add, Prod.snd_add,
      Submodule.coe_add, LieSubmodule.coe_add] <;> abel
  map_smul' r x := by
    apply Subtype.ext
    ext <;> simp [tripleAssemble, smul_add]

theorem exists_additiveTriple_layer_basis {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (e : Basis ι ℚ L) (i : σ) (c : σ → ℕ) (n : ℕ)
    (a : Basis α ℚ (F.weightedLayer c n))
    (b : Basis β ℚ (F.coordinateActiveLayer i n))
    {H : ℕ} (hH : 1 ≤ H)
    (ha : ∀ j k, RationalHeightLE (e.repr (a j : L) k) H)
    (hb : ∀ j k, RationalHeightLE (e.repr (b j : L) k) H) :
    ∃ q : Basis (Fin (finrank ℚ (F.additiveTripleLayer i c n))) ℚ
        (F.additiveTripleLayer i c n),
      ∀ j k, RationalHeightLE (e.repr (q j).val.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.2 k) H := by
  classical
  let q := (a.prod (b.prod b)).map (F.additiveTripleLayerEquiv i c n)
  have hzero (k : ι) : RationalHeightLE (e.repr 0 k) H := by
    simpa only [map_zero, Finsupp.zero_apply] using rationalHeightLE_zero hH
  have hq (j : α ⊕ (β ⊕ β)) (k : ι) :
      RationalHeightLE (e.repr (q j).val.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.1 k) H ∧
        RationalHeightLE (e.repr (q j).val.2.2 k) H := by
    rcases j with j | j | j
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (a j : L) k) H ∧
          RationalHeightLE (e.repr (a j : L) k) H ∧
          RationalHeightLE (e.repr (a j : L) k) H from ⟨ha j k, ha j k, ha j k⟩)
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr 0 k) H from ⟨hb j k, hb j k, hzero k⟩)
    · simpa [q, Basis.prod_apply, additiveTripleLayerEquiv, tripleAssemble] using
        (show RationalHeightLE (e.repr (b j : L) k) H ∧
          RationalHeightLE (e.repr 0 k) H ∧
          RationalHeightLE (e.repr (b j : L) k) H from ⟨hb j k, hzero k, hb j k⟩)
  let r := q.reindex (Fintype.equivFinOfCardEq (finrank_eq_card_basis q).symm)
  refine ⟨r, fun j k => ?_⟩
  simpa only [r, Basis.reindex_apply] using hq _ k

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ZeroDegreeCoordinate
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace VectorPolynomial

theorem eval_eq_of_zero_coordinate {σ R V : Type*} [CommRing R]
    [AddCommGroup V] [Module R V] (p : VectorPolynomial σ R V) (i : σ)
    (hp : ∀ a, a i ≠ 0 → coefficients p a = 0)
    (x y : σ → R) (hxy : ∀ j, j ≠ i → x j = y j) : eval x p = eval y p := by
  classical
  conv_lhs => rw [← sum_monomial_coefficients p]
  conv_rhs => rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, eval_monomial, Finsupp.prod]
  apply Finset.sum_congr rfl
  intro a ha
  have hi : a i = 0 := by
    by_contra h
    exact (Finsupp.mem_support_iff.mp ha) (hp a h)
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j
    simp only [hi, pow_zero]
  · rw [hxy j hj]

end VectorPolynomial

namespace MultidegreeLieFiltration

open VectorPolynomial

theorem polynomialOrbitEval_eq_of_zero_coordinate {σ L : Type*} [Fintype σ]
    [LieRing L] [LieAlgebra ℚ L] {s : ℕ} {bound : σ → ℕ}
    (F : MultidegreeLieFiltration σ L s bound) (i : σ) (hi : bound i = 0)
    (g : F.PolynomialOrbit) (x y : σ → ℤ)
    (hxy : ∀ j, j ≠ i → x j = y j) :
    F.polynomialOrbitEval x g = F.polynomialOrbitEval y g := by
  apply NilpotentLieBCHGroup.ext
  apply VectorPolynomial.eval_eq_of_zero_coordinate (g.log F) i
  · intro a ha
    have hn : ¬(fun j => a j) ≤ bound := by
      intro h
      exact ha (Nat.eq_zero_of_le_zero (by simpa only [hi] using h i))
    have h := g.adapted F a
    simpa only [F.terminal _ hn, Submodule.mem_bot] using h
  · intro j hj
    exact congrArg (fun z : ℤ => (z : ℚ)) (hxy j hj)

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end


