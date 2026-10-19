-- Prove2me | Definitions.Def_OAIE3v2B087
-- name    : OAIE3v2B087
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:19:48.787736+00:00
-- url     : https://prove2.me/theorems/df909a6b-5bbe-4246-9cca-8fb8710b50ce
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 88 of 311
-- statement:
--   Definitions bundle 88 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B068`, `OAIE3v2B069` of this split.
--
--   Modules: `Estimates/LowerStepSquare.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/RealifiedMultidegree.lean`, `Estimates/ShiftedAdaptedIdeal.lean`, `Estimates/SquareGradedRelative.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Estimates/WeightedOrbitNormalization.lean`, `Estimates/WeightedTranslationShearExponential.lean`, `FixedDensity/OrderedRemoval.lean`, `Linear/DualAdjointAction.lean`, `Linear/DualDerivativeRemoval.lean`, `Linear/DualIdealSteps.lean`, `Linear/RankHorizontalSymbol.lean`, `Nilpotent/DegreeRankBCH.lean`, `Nilpotent/DualBCHDifferential.lean`, `Nilpotent/FilteredAdjointFirstBracket.lean`, `Polynomial/AdaptedPolynomialSubstitution.lean`, `Polynomial/DegreeRankSunflower.lean`, `Polynomial/ExtendedPolynomialValues.lean`, `Polynomial/PolynomialShearAffineExponential.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/RealAdaptedPolynomialGroup.lean`, `Polynomial/RealGradedSymbolPolynomial.lean`, `Polynomial/RealPolynomialChartSubstitution.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Polynomial/ShiftedPolynomialIdeals.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B068
import Definitions.Def_OAIE3v2B069

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ExtendedPolynomialValues
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators

variable {σ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem weightedDilation_monomial (w : σ → ℕ) (r : R) (α : σ →₀ ℕ) (v : V) :
    weightedDilation w r (monomial α v) = r ^ Finsupp.weight w α • monomial α v := by
  classical
  apply coefficients.injective
  ext β
  by_cases h : α = β <;> simp [h]

section Lie

variable {L : Type*} [LieRing L] [LieAlgebra R L]

theorem weightedDilation_lie (w : σ → ℕ) (r : R) (p q : VectorPolynomial σ R L) :
    weightedDilation w r ⁅p, q⁆ = ⁅weightedDilation w r p, weightedDilation w r q⁆ := by
  classical
  rw [← sum_monomial_coefficients p, ← sum_monomial_coefficients q]
  simp only [Finsupp.sum, map_sum, sum_lie_sum, weightedDilation_monomial,
    lie_monomial, map_add, pow_add]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  rw [smul_lie (r ^ Finsupp.weight w α) (monomial (R := R) α (coefficients p α))
      (r ^ Finsupp.weight w β • monomial (R := R) β (coefficients q β)),
    lie_smul (r ^ Finsupp.weight w β) (monomial (R := R) α (coefficients p α))
      (monomial (R := R) β (coefficients q β)),
    lie_monomial, smul_smul]

end Lie
end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open Module
open scoped TensorProduct

variable {σ R S V W : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
  [AddCommGroup W] [Module R W] [Module S W] [IsScalarTower R S W]

section Field

variable {K : Type*} [Field K] [Infinite K] [Algebra R K]
  [Module K V] [IsScalarTower R K V]

theorem eq_zero_of_eval₂_zero (p : VectorPolynomial σ R V) (hp : ∀ x : σ → K, eval₂ x p = 0) :
    p = 0 := by
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
    rw [map_zero, ← coordinate_eval₂, hp, map_zero]
  have h := congrArg (fun polynomial : MvPolynomial σ K => polynomial.coeff α) hc
  simp only [coeff_coordinate, AddMonoidAlgebra.coeff_zero] at h
  change b.repr (coefficients p α) i = 0 at h
  simpa only [map_zero, Finsupp.zero_apply] using h

end Field

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealifiedMultidegree
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realLayer (a : σ → ℕ) : LieIdeal ℝ (ℝ ⊗[ℚ] L) := (F.layerIdeal a).baseChange ℝ

end Erdos3.MultidegreeLieFiltration

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

theorem eval_substitute (f : σ → MvPolynomial τ R) (x : τ → R) (p : VectorPolynomial σ R V) :
    eval x (substitute f p) = eval (fun i => MvPolynomial.aeval (R := R) x (f i)) p := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul q v =>
    simp only [substitute_tmul, eval_tmul]
    rw [MvPolynomial.comp_aeval_apply]
  | add p q hp hq => simp only [map_add, hp, hq]

end Erdos3.VectorPolynomial


namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def restrictLieSubalgebra (K : LieSubalgebra ℚ L) : NilpotentLieFiltration K s where
  layer i := (F.layer i).comap K.incl.toLinearMap
  antitone := fun _ _ hij _ hx => F.antitone hij hx
  one_eq_top := by simp only [F.one_eq_top, Submodule.comap_top]
  lie_mem := fun ha hb => F.lie_mem ha hb
  terminal := by
    ext a
    change (a : L) ∈ F.layer (s + 1) ↔ a = 0
    rw [F.terminal, Submodule.mem_bot]
    constructor
    · intro h
      exact Subtype.val_injective h
    · intro h
      rw [h]
      rfl

noncomputable def polynomialLayer (i : ℕ) : Submodule ℚ (VectorPolynomial σ ℚ L) where
  carrier := {p | ∀ α, coefficients p α ∈ F.layer i}
  zero_mem' := by intro α; simp
  add_mem' hp hq := by
    intro α
    simpa only [map_add, Finsupp.add_apply] using (F.layer i).add_mem (hp α) (hq α)
  smul_mem' c p hp := by
    intro α
    simpa only [map_smul, Finsupp.smul_apply] using (F.layer i).smul_mem c (hp α)

theorem monomial_mem_polynomialLayer (i : ℕ) (α : σ →₀ ℕ) {a : L} (ha : a ∈ F.layer i) :
    monomial (R := ℚ) α a ∈ F.polynomialLayer i := by
  classical
  intro β
  by_cases h : α = β
  · subst β
    simpa using ha
  · simp [h]

theorem lie_mem_polynomialLayer {i j : ℕ} {p q : VectorPolynomial σ ℚ L}
    (hp : p ∈ F.polynomialLayer i) (hq : q ∈ F.polynomialLayer j) :
    ⁅p, q⁆ ∈ F.polynomialLayer (i + j) := by
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
  exact F.monomial_mem_polynomialLayer _ _ (F.lie_mem (hp α) (hq β))

noncomputable def polynomialFiltration : NilpotentLieFiltration (VectorPolynomial σ ℚ L) s where
  layer := F.polynomialLayer
  antitone := fun _ _ hij _ hp α => F.antitone hij (hp α)
  one_eq_top := by
    apply top_unique
    intro p _ α
    simp [F.one_eq_top]
  lie_mem := F.lie_mem_polynomialLayer
  terminal := by
    apply bot_unique
    intro p hp
    change p = 0
    apply coefficients.injective
    ext α
    have h := hp α
    simpa only [F.terminal, Submodule.mem_bot, map_zero, Finsupp.zero_apply] using h

noncomputable def adaptedPolynomialFiltration (w : σ → ℕ) :
    NilpotentLieFiltration (F.adaptedLieSubalgebra w) s :=
  F.polynomialFiltration.restrictLieSubalgebra (F.adaptedLieSubalgebra w)

end Erdos3.NilpotentLieFiltration


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.DegreeRankSunflower
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {I L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def fourHorizontalLayer (d : ℕ) : Submodule ℚ (Fin 4 → L) :=
  Submodule.pi Set.univ (fun _ => F.layer d 1)

theorem mem_fourHorizontalLayer (d : ℕ) (v : Fin 4 → L) :
    v ∈ F.fourHorizontalLayer d ↔ ∀ k, v k ∈ F.layer d 1 := by
  simp [fourHorizontalLayer, Submodule.mem_pi]

def fourHorizontalMap (d : ℕ) : F.fourHorizontalLayer d →ₗ[ℚ] (Fin 4 → F.HigherHorizontal d) where
  toFun v k := F.higherHorizontalMk d ⟨v.val k, (F.mem_fourHorizontalLayer d v.val).mp v.property k⟩
  map_add' x y := by
    funext k
    exact map_add (F.higherHorizontalMk d)
      ⟨x.val k, (F.mem_fourHorizontalLayer d x.val).mp x.property k⟩
      ⟨y.val k, (F.mem_fourHorizontalLayer d y.val).mp y.property k⟩
  map_smul' c x := by
    funext k
    exact map_smul (F.higherHorizontalMk d) c
      ⟨x.val k, (F.mem_fourHorizontalLayer d x.val).mp x.property k⟩

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuotientInducedMark
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L) (π : L →ₗ⁅ℚ⁆ M) (hker : ∀ x ∈ I, π x = 0)

noncomputable def quotientInducedMark : (L ⧸ I) →ₗ⁅ℚ⁆ M :=
  lieQuotientDescend I π hker

@[simp] theorem quotientInducedMark_mk (x : L) :
    quotientInducedMark I π hker (lieQuotientMap I x) = π x := rfl

@[simp] theorem quotientInducedMark_comp :
    (quotientInducedMark I π hker).comp (lieQuotientMap I) = π := by
  ext x
  rfl

@[simp] theorem quotientInducedMark_real_mk (x : ℝ ⊗[ℚ] L) :
    realificationLieHom (quotientInducedMark I π hker)
      (realificationLieHom (lieQuotientMap I) x) = realificationLieHom π x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

@[simp] theorem quotientInducedMark_real_comp :
    (realificationLieHom (quotientInducedMark I π hker)).comp
      (realificationLieHom (lieQuotientMap I)) = realificationLieHom π := by
  ext x
  exact quotientInducedMark_real_mk I π hker x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def squareSndHom : F.squareFiltration.Group →* F.Group :=
  map F.squareSnd

@[simp] theorem squareFstHom_coord (g : F.squareFiltration.Group) :
    (F.squareFstHom g).coord = g.coord.val.1 := rfl

@[simp] theorem squareSndHom_coord (g : F.squareFiltration.Group) :
    (F.squareSndHom g).coord = g.coord.val.2 := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realLayer_eq_span_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) :
    (F.realLayer i).toSubmodule = Submodule.span ℝ (b.baseChange ℝ '' S) := by
  change (F.layer i).baseChange ℝ = _
  rw [hS, Submodule.baseChange_span, Set.image_image]
  congr 2
  funext j
  exact (Basis.baseChange_apply ℝ b j).symm

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

theorem adapted_constant (w : σ → ℕ) (a : L) : F.Adapted w (monomial 0 a) := by
  apply (F.mem_adaptedSubmodule w _).mp
  apply F.monomial_mem_adaptedSubmodule
  rw [map_zero]
  apply F.antitone (Nat.zero_le 1)
  rw [F.one_eq_top]
  trivial

noncomputable def adaptedConstant (w : σ → ℕ) (a : L) : F.adaptedLieSubalgebra w :=
  ⟨monomial 0 a, (F.mem_adaptedSubmodule w _).mpr (F.adapted_constant w a)⟩

theorem adaptedConstant_mem_shiftedIdeal (w : σ → ℕ) (a : L) :
    F.adaptedConstant w a ∈ F.shiftedAdaptedIdeal w := by
  apply F.monomial_mem_shiftedAdaptedSubmodule
  simp only [map_zero, Nat.zero_add, F.one_eq_top, Submodule.mem_top]

end Erdos3.NilpotentLieFiltration

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

@[simp] theorem shiftedPolynomialIdeal_one : F.shiftedPolynomialIdeal w 1 = F.shiftedAdaptedIdeal w := by
  rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ShiftedPolynomialBasis
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

abbrev PolynomialSymbol (w : σ → ℕ) :=
  F.adaptedLieSubalgebra w ⧸ F.shiftedAdaptedIdeal w

noncomputable def polynomialSymbolMap (w : σ → ℕ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  lieQuotientMap (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_surjective (w : σ → ℕ) :
    Function.Surjective (F.polynomialSymbolMap w) :=
  lieQuotientMap_surjective (F.shiftedAdaptedIdeal w)

theorem polynomialSymbolMap_eq_zero_iff (w : σ → ℕ) (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p = 0 ↔
      ∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer (Finsupp.weight w α + 1) :=
  lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) p

theorem polynomialSymbolMap_eq_iff (w : σ → ℕ) (p q : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolMap w p = F.polynomialSymbolMap w q ↔
      ∀ α, coefficients ((p : VectorPolynomial σ ℚ L) - (q : VectorPolynomial σ ℚ L)) α ∈
        F.layer (Finsupp.weight w α + 1) := by
  rw [← sub_eq_zero, ← map_sub, F.polynomialSymbolMap_eq_zero_iff]
  rfl

theorem polynomialSymbol_lowerCentralSeries_eq_bot (w : σ → ℕ) :
    LieModule.lowerCentralSeries ℚ (F.PolynomialSymbol w) (F.PolynomialSymbol w) s = ⊥ :=
  lie_quotient_lowerCentralSeries_eq_bot (F.adaptedPolynomialFiltration w).lowerCentralSeries_eq_bot
    (F.shiftedAdaptedIdeal w)

abbrev PolynomialSymbolGroup (w : σ → ℕ) :=
  NilpotentLieBCHGroup (F.PolynomialSymbol w) s (F.polynomialSymbol_lowerCentralSeries_eq_bot w)

noncomputable def polynomialSymbolHom (w : σ → ℕ) :
    (F.adaptedPolynomialFiltration w).Group →* F.PolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.polynomialSymbolMap w)

@[simp] theorem polynomialSymbolHom_coord (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.polynomialSymbolHom w g).coord = F.polynomialSymbolMap w g.coord := rfl

@[simp] theorem polynomialSymbolMap_constant (w : σ → ℕ) (a : L) :
    F.polynomialSymbolMap w (F.adaptedConstant w a) = 0 :=
  (lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) _).mpr
    (F.adaptedConstant_mem_shiftedIdeal w a)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedCoefficientMap (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.adaptedLieSubalgebra w →ₗ[ℚ] L :=
  (Finsupp.lapply α).comp
    (coefficients.toLinearMap.comp (F.adaptedLieSubalgebra w).incl.toLinearMap)

@[simp] theorem adaptedCoefficientMap_apply (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    F.adaptedCoefficientMap w α p = coefficients (p : VectorPolynomial σ ℚ L) α := rfl

noncomputable def polynomialSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.PolynomialSymbol w →ₗ[ℚ] L ⧸ F.layer (Finsupp.weight w α + 1) :=
  (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
    ((F.layer (Finsupp.weight w α + 1)).mkQ.comp (F.adaptedCoefficientMap w α)) (by
      intro p hp
      exact (Submodule.Quotient.mk_eq_zero _).mpr (hp α))

@[simp] theorem polynomialSymbolCoefficient_map (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolCoefficient w α (F.polynomialSymbolMap w p) =
      (F.layer (Finsupp.weight w α + 1)).mkQ (coefficients (p : VectorPolynomial σ ℚ L) α) := rfl

theorem polynomialSymbol_ext (w : σ → ℕ) (x y : F.PolynomialSymbol w)
    (h : ∀ α, F.polynomialSymbolCoefficient w α x = F.polynomialSymbolCoefficient w α y) :
    x = y := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
  apply (F.polynomialSymbolMap_eq_iff w p q).mpr
  intro α
  have he := h α
  rw [F.polynomialSymbolCoefficient_map, F.polynomialSymbolCoefficient_map] at he
  have hzero : (F.layer (Finsupp.weight w α + 1)).mkQ
      (coefficients (p : VectorPolynomial σ ℚ L) α - coefficients (q : VectorPolynomial σ ℚ L) α) = 0 := by
    rw [map_sub, he, sub_self]
  simpa only [map_sub, Finsupp.sub_apply] using (Submodule.Quotient.mk_eq_zero _).mp hzero

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem mem_layer_iff_basis_coordinates (j : ℕ) (v : L) :
    v ∈ F.layer j ↔ ∀ i, ¬ j ≤ ω i → b.repr v i = 0 := by
  rw [hlayers, basis_mem_span_image_iff]
  rfl

theorem adaptedSubmodule_eq_span_tensorBasis (w : σ → ℕ) :
    F.adaptedSubmodule w = Submodule.span ℚ
      (coefficientTensorBasis b '' {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 ≤ ω z.2}) := by
  ext p
  change (∀ α, coefficients p α ∈ F.layer (Finsupp.weight w α)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hlayers]
  constructor
  · intro h z hz
    rcases z with ⟨α, i⟩
    rw [coefficientTensorBasis_repr]
    exact h α i hz
  · intro h α i hi
    have hh := h (α, i) hi
    simpa only [coefficientTensorBasis_repr] using hh

noncomputable def adaptedMonomialBasis (w : σ → ℕ) :
    Basis {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} ℚ (F.adaptedLieSubalgebra w) :=
  supportedSubmoduleBasis (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2} (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w)

@[simp] theorem adaptedMonomialBasis_coe (w : σ → ℕ)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (F.adaptedMonomialBasis b ω hlayers w z : VectorPolynomial σ ℚ L) =
      monomial z.val.1 (b z.val.2) := by
  exact (supportedSubmoduleBasis_coe (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w) z).trans
      (coefficientTensorBasis_apply b _ _)

theorem adaptedMonomialBasis_repr (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2}) :
    (F.adaptedMonomialBasis b ω hlayers w).repr p z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  exact (supportedSubmoduleBasis_repr (coefficientTensorBasis b) (F.adaptedSubmodule w)
    {z | Finsupp.weight w z.1 ≤ ω z.2}
    (F.adaptedSubmodule_eq_span_tensorBasis b ω hlayers w) p z).trans
      (coefficientTensorBasis_repr b _ _ _)

theorem shiftedAdaptedIdeal_eq_span_monomialBasis (w : σ → ℕ) :
    (F.shiftedAdaptedIdeal w).toSubmodule = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hlayers w ''
        {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + 1)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hlayers]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hlayers _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def adaptedWeightedDilation (w : σ → ℕ) (r : ℚ) :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ F.adaptedLieSubalgebra w :=
  { ((weightedDilation w r).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (F.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α ∈ _
        rw [coefficients_weightedDilation]
        exact (F.layer _).smul_mem _ (p.property α)) with
    map_lie' := by
      intro p q
      apply Subtype.ext
      exact weightedDilation_lie w r (p : VectorPolynomial σ ℚ L) (q : VectorPolynomial σ ℚ L) }

theorem adaptedWeightedDilation_mem_shiftedIdeal (w : σ → ℕ) (r : ℚ)
    {p : F.adaptedLieSubalgebra w} (hp : p ∈ F.shiftedAdaptedIdeal w) :
    F.adaptedWeightedDilation w r p ∈ F.shiftedAdaptedIdeal w := by
  intro α
  change coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α ∈ _
  rw [coefficients_weightedDilation]
  exact (F.layer _).smul_mem _ (hp α)

noncomputable def polynomialSymbolDilation (w : σ → ℕ) (r : ℚ) :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ F.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
      ((F.polynomialSymbolMap w).toLinearMap.comp (F.adaptedWeightedDilation w r).toLinearMap) (by
        intro p hp
        exact (lieQuotientMap_eq_zero (F.shiftedAdaptedIdeal w) _).mpr
          (F.adaptedWeightedDilation_mem_shiftedIdeal w r hp))
    map_lie' := by
      intro x y
      obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
      obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
      change F.polynomialSymbolMap w (F.adaptedWeightedDilation w r ⁅p, q⁆) =
        ⁅F.polynomialSymbolMap w (F.adaptedWeightedDilation w r p),
          F.polynomialSymbolMap w (F.adaptedWeightedDilation w r q)⁆
      rw [LieHom.map_lie, LieHom.map_lie] }

@[simp] theorem polynomialSymbolDilation_map (w : σ → ℕ) (r : ℚ)
    (p : F.adaptedLieSubalgebra w) :
    F.polynomialSymbolDilation w r (F.polynomialSymbolMap w p) =
      F.polynomialSymbolMap w (F.adaptedWeightedDilation w r p) := rfl

theorem polynomialSymbolCoefficient_dilation (w : σ → ℕ) (r : ℚ)
    (α : σ →₀ ℕ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolCoefficient w α (F.polynomialSymbolDilation w r x) =
      r ^ Finsupp.weight w α • F.polynomialSymbolCoefficient w α x := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolDilation_map, F.polynomialSymbolCoefficient_map,
    F.polynomialSymbolCoefficient_map]
  change (F.layer (Finsupp.weight w α + 1)).mkQ
    (coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) α) = _
  rw [coefficients_weightedDilation, map_smul]

@[simp] theorem polynomialSymbolDilation_one (w : σ → ℕ) (x : F.PolynomialSymbol w) :
    F.polynomialSymbolDilation w 1 x = x := by
  apply F.polynomialSymbol_ext w
  intro α
  simp only [F.polynomialSymbolCoefficient_dilation, one_pow, one_smul]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev SymbolBasisIndex (w : σ → ℕ) (ω : ι → ℕ) :=
  {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 = ω z.2}

def symbolSurvivorEquiv (w : σ → ℕ) (ω : ι → ℕ) :
    ↥({z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
      Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}ᶜ) ≃ SymbolBasisIndex w ω where
  toFun z := ⟨z.val.val, by
    have hle := z.val.property
    have hlt := z.property
    change ¬ Finsupp.weight w z.val.val.1 + 1 ≤ ω z.val.val.2 at hlt
    omega⟩
  invFun z := ⟨⟨z.val, z.property.le⟩, by
    change ¬ Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2
    have hz := z.property
    omega⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def polynomialSymbolBasis (w : σ → ℕ) :
    Basis (SymbolBasisIndex w ω) ℚ (F.PolynomialSymbol w) :=
  (supportedQuotientBasis (F.adaptedMonomialBasis b ω hlayers w)
    (F.shiftedAdaptedIdeal w).toSubmodule
    {z | Finsupp.weight w z.val.1 + 1 ≤ ω z.val.2}
    (F.shiftedAdaptedIdeal_eq_span_monomialBasis b ω hlayers w)).reindex (symbolSurvivorEquiv w ω)

@[simp] theorem polynomialSymbolBasis_apply (w : σ → ℕ) (z : SymbolBasisIndex w ω) :
    F.polynomialSymbolBasis b ω hlayers w z =
      F.polynomialSymbolMap w (F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩) := by
  rw [polynomialSymbolBasis, Basis.reindex_apply, supportedQuotientBasis_apply]
  rfl

theorem polynomialSymbolBasis_repr_map (w : σ → ℕ) (p : F.adaptedLieSubalgebra w)
    (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr (F.polynomialSymbolMap w p) z =
      b.repr (coefficients (p : VectorPolynomial σ ℚ L) z.val.1) z.val.2 := by
  rw [polynomialSymbolBasis, Basis.repr_reindex_apply]
  change (supportedQuotientBasis _ _ _ _).repr
    ((F.shiftedAdaptedIdeal w).toSubmodule.mkQ p) _ = _
  rw [supportedQuotientBasis_repr_mk, F.adaptedMonomialBasis_repr]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem shiftedPolynomialIdeal_eq_span_monomialBasis (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w k).toSubmodule = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hF w ''
        {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + k)) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.adaptedMonomialBasis_repr]
    exact h z.val.1 z.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α ≤ ω i
    · have hz := h ⟨(α, i), hdeg⟩ hi
      simpa only [F.adaptedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

abbrev ShiftedMonomialIndex (w : σ → ℕ) (ω : ι → ℕ) (k : ℕ) :=
  {z : {z : (σ →₀ ℕ) × ι // Finsupp.weight w z.1 ≤ ω z.2} |
    Finsupp.weight w z.val.1 + k ≤ ω z.val.2}

noncomputable def shiftedMonomialBasis (w : σ → ℕ) (k : ℕ) :
    Basis (ShiftedMonomialIndex w ω k) ℚ (F.shiftedPolynomialIdeal w k) :=
  supportedSubmoduleBasis (F.adaptedMonomialBasis b ω hF w)
    (F.shiftedPolynomialIdeal w k).toSubmodule
    {z | Finsupp.weight w z.val.1 + k ≤ ω z.val.2}
    (F.shiftedPolynomialIdeal_eq_span_monomialBasis b ω hF w k)

@[simp] theorem shiftedMonomialBasis_coe (w : σ → ℕ) (k : ℕ) (z : ShiftedMonomialIndex w ω k) :
    (F.shiftedMonomialBasis b ω hF w k z : F.adaptedLieSubalgebra w) =
      F.adaptedMonomialBasis b ω hF w z.val :=
  supportedSubmoduleBasis_coe _ _ _ _ z

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedOrbitNormalization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem horizontal_bch (a b : L) :
    lieQuotientMap (F.layerIdeal 2) (lieBCH s a b) =
      lieQuotientMap (F.layerIdeal 2) a + lieQuotientMap (F.layerIdeal 2) b := by
  rw [map_lieBCH]
  apply lieBCH_eq_add_of_lie_eq_zero
    (lie_quotient_lowerCentralSeries_eq_bot F.lowerCentralSeries_eq_bot (F.layerIdeal 2))
  rw [← LieHom.map_lie]
  apply (lieQuotientMap_eq_zero _ _).mpr
  exact F.lie_mem (show a ∈ F.layer 1 by rw [F.one_eq_top]; trivial)
    (show b ∈ F.layer 1 by rw [F.one_eq_top]; trivial)

def horizontalLog (g : F.Group) : L ⧸ F.layerIdeal 2 := lieQuotientMap (F.layerIdeal 2) g.coord

@[simp] theorem horizontalLog_mul (g h : F.Group) :
    F.horizontalLog (g * h) = F.horizontalLog g + F.horizontalLog h := F.horizontal_bch _ _

@[simp] theorem horizontalLog_inv (g : F.Group) : F.horizontalLog g⁻¹ = -F.horizontalLog g :=
  map_neg (lieQuotientMap (F.layerIdeal 2)) g.coord

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DualBCHDifferential
namespace OAI


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev DualGroup (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (DualLieAlgebra L) s (dualLie_lowerCentralSeries_eq_bot hnil)

noncomputable def dualConstantHom : NilpotentLieBCHGroup L s hnil →* DualGroup hnil :=
  map dualConstantLie

noncomputable def dualBaseHom : DualGroup hnil →* NilpotentLieBCHGroup L s hnil :=
  map dualBaseLie

noncomputable def dualTangentElement (x : L) : DualGroup hnil := ⟨dualInfinitesimal x⟩

@[simp] theorem dualBaseHom_constant (g : NilpotentLieBCHGroup L s hnil) :
    dualBaseHom (dualConstantHom g) = g := by
  apply ext
  exact dualBaseLinear_constant g.coord

@[simp] theorem dualBaseHom_tangent (x : L) :
    dualBaseHom (dualTangentElement (hnil := hnil) x) = 1 := by
  apply ext
  exact dualBaseLinear_infinitesimal x

theorem dualTangentElement_injective : Function.Injective (dualTangentElement (hnil := hnil)) := by
  intro x y h
  exact dualInfinitesimal_injective (congrArg coord h)

@[simp] theorem dualTangentElement_zero : dualTangentElement (hnil := hnil) (0 : L) = 1 := by
  apply ext
  exact map_zero dualInfinitesimal

theorem dualTangentElement_mul (x y : L) :
    dualTangentElement (hnil := hnil) x * dualTangentElement y = dualTangentElement (x + y) := by
  apply ext
  change lieBCH s (dualInfinitesimal x) (dualInfinitesimal y) = dualInfinitesimal (x + y)
  rw [lieBCH_eq_add_of_lie_eq_zero (dualLie_lowerCentralSeries_eq_bot hnil) (dualInfinitesimal_lie x y),
    map_add]

theorem dualTangentElement_neg (x : L) :
    dualTangentElement (hnil := hnil) (-x) = (dualTangentElement x)⁻¹ := by
  apply ext
  exact map_neg dualInfinitesimal x

theorem dualBaseHom_eq_one_iff (g : DualGroup hnil) :
    dualBaseHom g = 1 ↔ g = dualTangentElement (dualTangentLinear g.coord) := by
  constructor
  · intro hg
    have hb : dualBaseLinear g.coord = 0 := congrArg coord hg
    apply ext
    change g.coord = dualInfinitesimal (dualTangentLinear g.coord)
    conv_lhs => rw [dualLie_decomposition g.coord, hb, map_zero, zero_add]
  · intro hg
    rw [hg, dualBaseHom_tangent]

end Erdos3.NilpotentLieBCHGroup


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def dualAdjoint (g : NilpotentLieBCHGroup L s hnil) (x : L) : L :=
  dualTangentLinear
    (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹).coord

theorem dualAdjoint_spec (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹ =
      dualTangentElement (dualAdjoint g x) := by
  apply (dualBaseHom_eq_one_iff _).mp
  simp only [map_mul, map_inv, dualBaseHom_constant, dualBaseHom_tangent, mul_one, mul_inv_cancel]

theorem dualAdjoint_neg_spec (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualConstantHom g * dualTangentElement (-x) * (dualConstantHom g)⁻¹ =
      dualTangentElement (-dualAdjoint g x) := by
  calc
    _ = (dualConstantHom g * dualTangentElement x * (dualConstantHom g)⁻¹)⁻¹ := by
      rw [dualTangentElement_neg]
      group
    _ = _ := by rw [dualAdjoint_spec, dualTangentElement_neg]

noncomputable def dualLogDerivative (z : DualGroup hnil) : L :=
  dualTangentLinear (z * (dualConstantHom (dualBaseHom z))⁻¹).coord

end Erdos3.NilpotentLieBCHGroup

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualAdjointAction
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[simp] theorem dualAdjoint_zero (g : NilpotentLieBCHGroup L s hnil) :
    dualAdjoint g 0 = 0 := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, dualTangentElement_zero, mul_one, mul_inv_cancel]

theorem dualAdjoint_add (g : NilpotentLieBCHGroup L s hnil) (x y : L) :
    dualAdjoint g (x + y) = dualAdjoint g x + dualAdjoint g y := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, ← dualTangentElement_mul, ← dualTangentElement_mul,
    ← dualAdjoint_spec, ← dualAdjoint_spec]
  group

@[simp] theorem dualAdjoint_neg (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g (-x) = -dualAdjoint g x := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, dualAdjoint_neg_spec]

@[simp] theorem dualAdjoint_one (x : L) :
    dualAdjoint (1 : NilpotentLieBCHGroup L s hnil) x = x := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, map_one, one_mul, inv_one, mul_one]

theorem dualAdjoint_mul (g h : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint (g * h) x = dualAdjoint g (dualAdjoint h x) := by
  apply dualTangentElement_injective (hnil := hnil)
  rw [← dualAdjoint_spec, ← dualAdjoint_spec, ← dualAdjoint_spec, map_mul]
  group

@[simp] theorem dualAdjoint_inv_cancel (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g⁻¹ (dualAdjoint g x) = x := by
  rw [← dualAdjoint_mul, inv_mul_cancel, dualAdjoint_one]

@[simp] theorem dualAdjoint_cancel_inv (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjoint g (dualAdjoint g⁻¹ x) = x := by
  rw [← dualAdjoint_mul, mul_inv_cancel, dualAdjoint_one]

noncomputable def dualAdjointAddEquiv (g : NilpotentLieBCHGroup L s hnil) : L ≃+ L where
  toFun := dualAdjoint g
  invFun := dualAdjoint g⁻¹
  left_inv := dualAdjoint_inv_cancel g
  right_inv := dualAdjoint_cancel_inv g
  map_add' := dualAdjoint_add g

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualIdealSteps
namespace OAI


namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dualConstant_infinitesimal_lie (x y : L) :
    ⁅dualConstantLie x, dualInfinitesimal y⁆ = dualInfinitesimal ⁅x, y⁆ := by
  change ⁅(1 : DualNumber ℚ) ⊗ₜ[ℚ] x, DualNumber.eps ⊗ₜ[ℚ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  rfl

theorem dualInfinitesimal_constant_lie (x y : L) :
    ⁅dualInfinitesimal x, dualConstantLie y⁆ = dualInfinitesimal ⁅x, y⁆ := by
  change ⁅DualNumber.eps ⊗ₜ[ℚ] x, (1 : DualNumber ℚ) ⊗ₜ[ℚ] y⁆ = _
  rw [LieAlgebra.ExtendScalars.bracket_tmul, mul_one]
  rfl

theorem dualTangentLinear_lie (x y : DualLieAlgebra L) :
    dualTangentLinear ⁅x, y⁆ =
      ⁅dualBaseLinear x, dualTangentLinear y⁆ + ⁅dualTangentLinear x, dualBaseLinear y⁆ := by
  have he := congrArg₂ (fun a b : DualLieAlgebra L => ⁅a, b⁆)
    (dualLie_decomposition x) (dualLie_decomposition y)
  calc
    _ = dualTangentLinear ⁅dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x),
      dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y)⁆ :=
      congrArg dualTangentLinear he
    _ = _ := by
      rw [LieRing.add_lie (dualConstantLie (dualBaseLinear x)) (dualInfinitesimal (dualTangentLinear x))
        (dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y))]
      rw [LieRing.lie_add (dualConstantLie (dualBaseLinear x)) (dualConstantLie (dualBaseLinear y))
        (dualInfinitesimal (dualTangentLinear y))]
      rw [LieRing.lie_add (dualInfinitesimal (dualTangentLinear x)) (dualConstantLie (dualBaseLinear y))
        (dualInfinitesimal (dualTangentLinear y))]
      rw [dualConstant_infinitesimal_lie, dualInfinitesimal_constant_lie, dualInfinitesimal_lie,
        ← dualConstantLie.map_lie]
      simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, add_zero]

noncomputable def dualIdealSubalgebra (I : LieIdeal ℚ L) : LieSubalgebra ℚ (DualLieAlgebra L) :=
  { I.toSubmodule.comap dualTangentLinear with
    lie_mem' := by
      intro x y hx hy
      change dualTangentLinear ⁅x, y⁆ ∈ I
      rw [dualTangentLinear_lie]
      exact I.add_mem (I.lie_mem hy) (lie_mem_left ℚ L I _ _ hx) }

@[simp] theorem mem_dualIdealSubalgebra (I : LieIdeal ℚ L) (x : DualLieAlgebra L) :
    x ∈ dualIdealSubalgebra I ↔ dualTangentLinear x ∈ I := Iff.rfl

noncomputable def dualIdealRealization (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) : dualIdealSubalgebra I →ₗ⁅ℚ⁆ L ⧸ J :=
  { toLinearMap := (lieQuotientMap J).toLinearMap.comp
      ((dualBaseLinear + dualTangentLinear).comp (dualIdealSubalgebra I).incl.toLinearMap)
    map_lie' := by
      intro x y
      change lieQuotientMap J (dualBaseLinear ⁅x.val, y.val⁆ + dualTangentLinear ⁅x.val, y.val⁆) =
        ⁅lieQuotientMap J (dualBaseLinear x.val + dualTangentLinear x.val),
          lieQuotientMap J (dualBaseLinear y.val + dualTangentLinear y.val)⁆
      rw [← (lieQuotientMap J).map_lie]
      rw [← sub_eq_zero, ← map_sub]
      apply (lieQuotientMap_eq_zero J _).mpr
      rw [dualBaseLinear_lie, dualTangentLinear_lie, LieRing.add_lie, LieRing.lie_add,
        LieRing.lie_add]
      have he : ⁅dualBaseLinear x.val, dualBaseLinear y.val⁆ +
          (⁅dualBaseLinear x.val, dualTangentLinear y.val⁆ +
            ⁅dualTangentLinear x.val, dualBaseLinear y.val⁆) -
          (⁅dualBaseLinear x.val, dualBaseLinear y.val⁆ +
            ⁅dualBaseLinear x.val, dualTangentLinear y.val⁆ +
              (⁅dualTangentLinear x.val, dualBaseLinear y.val⁆ +
                ⁅dualTangentLinear x.val, dualTangentLinear y.val⁆)) =
          -⁅dualTangentLinear x.val, dualTangentLinear y.val⁆ := by abel
      rw [he]
      exact J.neg_mem (hIJ _ x.property _ y.property) }

@[simp] theorem dualIdealRealization_apply (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (x : dualIdealSubalgebra I) :
    dualIdealRealization I J hIJ x =
      lieQuotientMap J (dualBaseLinear x.val + dualTangentLinear x.val) := rfl

noncomputable def dualQuotientEvaluate (J : LieIdeal ℚ L) : DualLieAlgebra L →ₗ[ℚ] L ⧸ J :=
  (lieQuotientMap J).toLinearMap.comp (dualBaseLinear + dualTangentLinear)

@[simp] theorem dualQuotientEvaluate_apply (J : LieIdeal ℚ L) (x : DualLieAlgebra L) :
    dualQuotientEvaluate J x = lieQuotientMap J (dualBaseLinear x + dualTangentLinear x) := rfl

@[simp] theorem dualQuotientEvaluate_constant (J : LieIdeal ℚ L) (x : L) :
    dualQuotientEvaluate J (dualConstantLie x) = lieQuotientMap J x := by
  rw [dualQuotientEvaluate_apply, dualBaseLinear_constant, dualTangentLinear_constant, add_zero]

@[simp] theorem dualQuotientEvaluate_infinitesimal (J : LieIdeal ℚ L) (x : L) :
    dualQuotientEvaluate J (dualInfinitesimal x) = lieQuotientMap J x := by
  rw [dualQuotientEvaluate_apply, dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, zero_add]

end Erdos3


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualCoordinates : DualLieAlgebra L ≃ₗ[ℚ] L × L where
  toLinearMap := dualBaseLinear.prod dualTangentLinear
  invFun x := dualConstantLie x.1 + dualInfinitesimal x.2
  left_inv x := (dualLie_decomposition x).symm
  right_inv x := by ext <;> simp

@[simp] theorem dualCoordinates_apply (x : DualLieAlgebra L) :
    dualCoordinates x = (dualBaseLinear x, dualTangentLinear x) := rfl

@[simp] theorem dualCoordinates_symm_apply (x : L × L) :
    dualCoordinates.symm x = dualConstantLie x.1 + dualInfinitesimal x.2 := rfl

end Erdos3


namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]

theorem dual_ext {x y : DualLieAlgebra M}
    (hb : dualBaseLinear x = dualBaseLinear y) (ht : dualTangentLinear x = dualTangentLinear y) : x = y := by
  calc
    x = dualConstantLie (dualBaseLinear x) + dualInfinitesimal (dualTangentLinear x) := dualLie_decomposition x
    _ = dualConstantLie (dualBaseLinear y) + dualInfinitesimal (dualTangentLinear y) := by rw [hb, ht]
    _ = y := (dualLie_decomposition y).symm

noncomputable def dualLinearLift (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) :
    DualLieAlgebra L →ₗ[ℚ] DualLieAlgebra M :=
  dualConstantLie.toLinearMap.comp (B.toLinearMap.comp dualBaseLinear) +
    dualInfinitesimal.comp (T.comp dualTangentLinear)

@[simp] theorem dualLinearLift_apply (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualLinearLift B T x = dualConstantLie (B (dualBaseLinear x)) +
      dualInfinitesimal (T (dualTangentLinear x)) := rfl

@[simp] theorem dualLinearLift_base (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualBaseLinear (dualLinearLift B T x) = B (dualBaseLinear x) := by
  rw [dualLinearLift_apply, map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem dualLinearLift_tangent (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : DualLieAlgebra L) :
    dualTangentLinear (dualLinearLift B T x) = T (dualTangentLinear x) := by
  rw [dualLinearLift_apply, map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem dualLinearLift_constant (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : L) :
    dualLinearLift B T (dualConstantLie x) = dualConstantLie (B x) := by
  rw [dualLinearLift_apply, dualBaseLinear_constant, dualTangentLinear_constant, map_zero,
    map_zero, add_zero]

@[simp] theorem dualLinearLift_infinitesimal (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M) (x : L) :
    dualLinearLift B T (dualInfinitesimal x) = dualInfinitesimal (T x) := by
  rw [dualLinearLift_apply, dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal, map_zero,
    map_zero, zero_add]

variable (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

noncomputable def dualIdealMorphism : dualIdealSubalgebra I →ₗ⁅ℚ⁆ DualLieAlgebra M :=
  { toLinearMap := (dualLinearLift B T).comp (dualIdealSubalgebra I).incl.toLinearMap
    map_lie' := by
      intro x y
      apply dual_ext
      · change dualBaseLinear (dualLinearLift B T ⁅x.val, y.val⁆) =
          dualBaseLinear ⁅dualLinearLift B T x.val, dualLinearLift B T y.val⁆
        rw [dualLinearLift_base, dualBaseLinear_lie, dualBaseLinear_lie,
          dualLinearLift_base, dualLinearLift_base, B.map_lie]
      · change dualTangentLinear (dualLinearLift B T ⁅x.val, y.val⁆) =
          dualTangentLinear ⁅dualLinearLift B T x.val, dualLinearLift B T y.val⁆
        rw [dualLinearLift_tangent, dualTangentLinear_lie, dualTangentLinear_lie,
          dualLinearLift_base, dualLinearLift_base, dualLinearLift_tangent, dualLinearLift_tangent,
          map_add, hT _ _ y.property, dualIdealMorphism_left I B T hT x.property] }

include hT in
theorem dualLinearLift_lieBCH (s : ℕ) {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualLinearLift B T (lieBCH s x y) = lieBCH s (dualLinearLift B T x) (dualLinearLift B T y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualLinearLift B T ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualLinearLift B T) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH (dualIdealMorphism I B T hT) s a b

end Erdos3


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

noncomputable instance dualRealModule : Module ℝ (DualLieAlgebra L) :=
  (dualCoordinates (L := L)).toAddEquiv.module ℝ

noncomputable def dualRealCoordinates : DualLieAlgebra L ≃ₗ[ℝ] L × L :=
  (dualCoordinates (L := L)).toAddEquiv.linearEquiv ℝ

@[simp] theorem dualRealCoordinates_apply (x : DualLieAlgebra L) :
    dualRealCoordinates x = (dualBaseLinear x, dualTangentLinear x) := rfl

@[simp] theorem dualRealCoordinates_symm_apply (x : L × L) :
    dualRealCoordinates.symm x = dualConstantLie x.1 + dualInfinitesimal x.2 := rfl

@[simp] theorem dualBaseLinear_smul_real (r : ℝ) (x : DualLieAlgebra L) :
    dualBaseLinear (r • x) = r • dualBaseLinear x :=
  congrArg Prod.fst (dualRealCoordinates.map_smul r x)

@[simp] theorem dualTangentLinear_smul_real (r : ℝ) (x : DualLieAlgebra L) :
    dualTangentLinear (r • x) = r • dualTangentLinear x :=
  congrArg Prod.snd (dualRealCoordinates.map_smul r x)

end Erdos3


namespace Erdos3.NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  (hM : LieModule.lowerCentralSeries ℚ M M s = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hT in
theorem dualLinearLift_adjoint (g : NilpotentLieBCHGroup L s hL) (x : L) (hx : x ∈ I) :
    T (dualAdjoint g x) = dualAdjoint (map (hM := hM) B g) (T x) := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hh := dualLinearLift_lieBCH I B T hT s
    (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc)
  rw [dualLinearLift_lieBCH I B T hT s hc ht, dualLinearLift_constant,
    dualLinearLift_infinitesimal, map_neg, dualLinearLift_constant] at hh
  have he := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent] at he
  exact he

include hT in
theorem dualLinearLift_adjoint_eq (g : NilpotentLieBCHGroup L s hL) (x : L) (hx : x ∈ I)
    (g' : NilpotentLieBCHGroup M s hM) (x' : M)
    (hg : B g.coord = g'.coord) (hxx' : T x = x') :
    T (dualAdjoint g x) = dualAdjoint g' x' := by
  have hmap : map (hM := hM) B g = g' := NilpotentLieBCHGroup.ext hg
  have he := dualLinearLift_adjoint hM I B T hT g x hx
  rw [hmap, hxx'] at he
  exact he

end Erdos3.NilpotentLieBCHGroup


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualInvariantSubalgebra (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieSubalgebra ℚ (DualLieAlgebra L) :=
  { U.toSubmodule.comap dualBaseLinear ⊓ V.comap dualTangentLinear with
    lie_mem' := by
      intro x y hx hy
      constructor
      · change dualBaseLinear ⁅x, y⁆ ∈ U
        rw [dualBaseLinear_lie]
        exact U.lie_mem hx.1 hy.1
      · change dualTangentLinear ⁅x, y⁆ ∈ V
        rw [dualTangentLinear_lie]
        apply V.add_mem (hUV _ hx.1 _ hy.2)
        rw [← lie_skew]
        exact V.neg_mem (hUV _ hy.1 _ hx.2) }

@[simp] theorem mem_dualInvariantSubalgebra (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) (x : DualLieAlgebra L) :
    x ∈ dualInvariantSubalgebra U V hUV ↔ dualBaseLinear x ∈ U ∧ dualTangentLinear x ∈ V :=
  Iff.rfl

namespace NilpotentLieBCHGroup

variable {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L) (hx : x ∈ V) :
    dualAdjoint g x ∈ V := by
  let S := dualInvariantSubalgebra U V hUV
  have hc : dualConstantLie g.coord ∈ S := by
    change dualBaseLinear (dualConstantLie g.coord) ∈ U ∧
      dualTangentLinear (dualConstantLie g.coord) ∈ V
    simpa only [dualBaseLinear_constant, dualTangentLinear_constant] using And.intro hg V.zero_mem
  have ht : dualInfinitesimal x ∈ S := by
    change dualBaseLinear (dualInfinitesimal x) ∈ U ∧ dualTangentLinear (dualInfinitesimal x) ∈ V
    simpa only [dualBaseLinear_infinitesimal, dualTangentLinear_infinitesimal] using And.intro U.zero_mem hx
  exact (lieBCH_mem S s (lieBCH_mem S s hc ht) (S.neg_mem hc)).2

end NilpotentLieBCHGroup
end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.FilteredAdjointFirstBracket
namespace OAI

section

namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def dualBaseSubalgebra (U : LieSubalgebra ℚ L) :
    LieSubalgebra ℚ (DualLieAlgebra L) :=
  dualInvariantSubalgebra U ⊤ (fun _ _ _ _ => trivial)

noncomputable def dualInvariantTangentIdeal (U : LieSubalgebra ℚ L) (V : Submodule ℚ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V) : LieIdeal ℚ (dualBaseSubalgebra U) :=
  { (dualBaseLinear.comp (dualBaseSubalgebra U).incl.toLinearMap).ker ⊓
      V.comap (dualTangentLinear.comp (dualBaseSubalgebra U).incl.toLinearMap) with
    lie_mem := by
      intro x y hy
      change dualBaseLinear ⁅x.val, y.val⁆ = 0 ∧ dualTangentLinear ⁅x.val, y.val⁆ ∈ V
      change dualBaseLinear y.val = 0 ∧ dualTangentLinear y.val ∈ V at hy
      simp only [dualBaseLinear_lie, dualTangentLinear_lie, hy.1, lie_zero, add_zero]
      exact ⟨trivial, hUV _ x.property.1 _ hy.2⟩ }

@[simp] theorem mem_dualInvariantTangentIdeal (U : LieSubalgebra ℚ L)
    (V : Submodule ℚ L) (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (z : dualBaseSubalgebra U) :
    z ∈ dualInvariantTangentIdeal U V hUV ↔
      dualBaseLinear z.val = 0 ∧ dualTangentLinear z.val ∈ V := Iff.rfl

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualDerivativeRemoval
namespace OAI

section

namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

@[simp] theorem dualLogDerivative_one : dualLogDerivative (1 : DualGroup hnil) = 0 := by
  simp only [dualLogDerivative, map_one, inv_one, mul_one, coord_one, map_zero]

end NilpotentLieBCHGroup

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolynomialChartSubstitution
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

variable {σ : Type*}

namespace VectorPolynomial

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def directionalDerivative [Fintype σ] (h : σ → ℚ) :
    VectorPolynomial σ ℚ L →ₗ[ℚ] VectorPolynomial σ ℚ L :=
  ∑ i, h i • (MvPolynomial.pderiv i).toLinearMap.rTensor L

@[simp] theorem directionalDerivative_tmul [Fintype σ]
    (h : σ → ℚ) (p : MvPolynomial σ ℚ) (x : L) :
    directionalDerivative h (p ⊗ₜ[ℚ] x) =
      ∑ i, h i • (MvPolynomial.pderiv i p ⊗ₜ[ℚ] x) := by
  simp [directionalDerivative]

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem pderiv_lie (i : σ) (p q : VectorPolynomial σ ℚ L) :
    (MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅p, q⁆ =
      ⁅(MvPolynomial.pderiv i).toLinearMap.rTensor L p, q⁆ +
        ⁅p, (MvPolynomial.pderiv i).toLinearMap.rTensor L q⁆ := by
  induction p using TensorProduct.induction_on with
  | zero =>
    simp only [zero_lie (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L), map_zero, zero_add]
  | tmul a x =>
    induction q using TensorProduct.induction_on with
    | zero =>
      simp only [lie_zero (L := VectorPolynomial σ ℚ L) (M := VectorPolynomial σ ℚ L), map_zero, zero_add]
    | tmul b y =>
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.rTensor_tmul]
      change MvPolynomial.pderiv i (a * b) ⊗ₜ[ℚ] ⁅x, y⁆ =
        (MvPolynomial.pderiv i a * b) ⊗ₜ[ℚ] ⁅x, y⁆ +
          (a * MvPolynomial.pderiv i b) ⊗ₜ[ℚ] ⁅x, y⁆
      rw [MvPolynomial.pderiv_mul, TensorProduct.add_tmul]
    | add q r hq hr =>
      simp only [LieRing.lie_add, map_add, hq, hr]
      abel
  | add p r hp hr =>
    simp only [LieRing.add_lie, map_add, hp, hr]
    abel

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

abbrev PolynomialGroup (σ : Type*) (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) :=
  NilpotentLieBCHGroup (VectorPolynomial σ ℚ L) s (VectorPolynomial.lowerCentralSeries_eq_bot hnil)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def formalPolynomialJetLie (i : σ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ DualLieAlgebra (VectorPolynomial σ ℚ L) where
  toLinearMap := dualConstantLie.toLinearMap +
    dualInfinitesimal.comp ((MvPolynomial.pderiv i).toLinearMap.rTensor L)
  map_lie' {P Q} := by
    change dualConstantLie ⁅P, Q⁆ +
      dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L ⁅P, Q⁆) =
      ⁅dualConstantLie P + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P),
        dualConstantLie Q + dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L Q)⁆
    apply dual_ext
    · simp only [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal,
        add_zero, dualBaseLinear_lie]
    · simp only [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal,
        zero_add, dualTangentLinear_lie, dualBaseLinear_constant,
        dualBaseLinear_infinitesimal, add_zero]
      rw [pderiv_lie]
      exact add_comm _ _

noncomputable def formalPolynomialJetHom (i : σ) :
    PolynomialGroup σ hnil →* DualGroup (VectorPolynomial.lowerCentralSeries_eq_bot (σ := σ) hnil) :=
  NilpotentLieBCHGroup.map (formalPolynomialJetLie i)

@[simp] theorem formalPolynomialJet_base (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (formalPolynomialJetHom i P).coord = P.coord := by
  change dualBaseLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem formalPolynomialJet_tangent (i : σ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (formalPolynomialJetHom i P).coord =
      (MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord := by
  change dualTangentLinear (dualConstantLie P.coord +
    dualInfinitesimal ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord)) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem formalPolynomialJet_baseHom (i : σ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (formalPolynomialJetHom i P) = P :=
  NilpotentLieBCHGroup.ext (formalPolynomialJet_base i P)

noncomputable def formalLogDerivative (i : σ) (P : PolynomialGroup σ hnil) :
    VectorPolynomial σ ℚ L := dualLogDerivative (formalPolynomialJetHom i P)

@[simp] theorem formalLogDerivative_one (i : σ) :
    formalLogDerivative i (1 : PolynomialGroup σ hnil) = 0 := by
  simp only [formalLogDerivative, map_one, dualLogDerivative_one]

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

noncomputable def realPolynomialValueHom (t : σ → ℝ) :
    PolynomialGroup σ hnil →* NilpotentLieBCHGroup L s hnil :=
  NilpotentLieBCHGroup.map (eval₂Lie (R := ℚ) (S := ℝ) (L := L) t)

@[simp] theorem realPolynomialValueHom_coord (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    (realPolynomialValueHom t P).coord = eval₂ t P.coord := rfl

noncomputable def realPolynomialJet (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    DualGroup hnil :=
  ⟨dualConstantLie (eval₂ t P.coord) +
    dualInfinitesimal (eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord))⟩

@[simp] theorem realPolynomialJet_base (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseLinear (realPolynomialJet i t P).coord = eval₂ t P.coord := by
  change dualBaseLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualBaseLinear_constant, dualBaseLinear_infinitesimal, add_zero]

@[simp] theorem realPolynomialJet_tangent (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualTangentLinear (realPolynomialJet i t P).coord =
      eval₂ t ((MvPolynomial.pderiv i).toLinearMap.rTensor L P.coord) := by
  change dualTangentLinear (dualConstantLie _ + dualInfinitesimal _) = _
  rw [map_add, dualTangentLinear_constant, dualTangentLinear_infinitesimal, zero_add]

@[simp] theorem realPolynomialJet_baseHom (i : σ) (t : σ → ℝ) (P : PolynomialGroup σ hnil) :
    dualBaseHom (realPolynomialJet i t P) = realPolynomialValueHom t P :=
  NilpotentLieBCHGroup.ext (realPolynomialJet_base i t P)

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

variable {σ τ υ V : Type*} [AddCommGroup V] [Module ℚ V] [Module ℝ V]
  [IsScalarTower ℚ ℝ V]

noncomputable def realCoefficientEquiv :
    VectorPolynomial σ ℚ V ≃ₗ[ℚ] VectorPolynomial σ ℝ V :=
  (coefficients (σ := σ) (R := ℚ) (V := V)).trans
    ((coefficients (σ := σ) (R := ℝ) (V := V)).restrictScalars ℚ).symm

@[simp] theorem coefficients_realCoefficientEquiv (p : VectorPolynomial σ ℚ V) :
    coefficients (realCoefficientEquiv p) = coefficients p := by
  simp [realCoefficientEquiv]

@[simp] theorem coefficients_realCoefficientEquiv_symm (p : VectorPolynomial σ ℝ V) :
    coefficients (realCoefficientEquiv.symm p) = coefficients p := by
  simp [realCoefficientEquiv]

@[simp] theorem realCoefficientEquiv_monomial (α : σ →₀ ℕ) (v : V) :
    realCoefficientEquiv (monomial (R := ℚ) α v) = monomial (R := ℝ) α v := by
  apply coefficients.injective
  simp

theorem eval_realCoefficientEquiv (x : σ → ℝ) (p : VectorPolynomial σ ℚ V) :
    eval x (realCoefficientEquiv p) = eval₂ x p := by
  classical
  rw [← sum_monomial_coefficients p]
  simp only [Finsupp.sum, map_sum, realCoefficientEquiv_monomial, eval_monomial, eval₂_monomial]

theorem eval₂_realCoefficientEquiv_symm (x : σ → ℝ) (p : VectorPolynomial σ ℝ V) :
    eval₂ x (realCoefficientEquiv.symm p) = eval x p := by
  obtain ⟨q, rfl⟩ := realCoefficientEquiv.surjective p
  rw [LinearEquiv.symm_apply_apply, eval_realCoefficientEquiv]

noncomputable def realChartSubstitute (f : σ → MvPolynomial τ ℝ) :
    VectorPolynomial σ ℚ V →ₗ[ℚ] VectorPolynomial τ ℚ V :=
  realCoefficientEquiv.symm.toLinearMap.comp
    (((substitute f).restrictScalars ℚ).comp realCoefficientEquiv.toLinearMap)

theorem eval₂_realChartSubstitute (f : σ → MvPolynomial τ ℝ)
    (x : τ → ℝ) (p : VectorPolynomial σ ℚ V) :
    eval₂ x (realChartSubstitute f p) =
      eval₂ (fun i => MvPolynomial.eval x (f i)) p := by
  simp only [realChartSubstitute, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.restrictScalars_apply, eval₂_realCoefficientEquiv_symm,
    eval_substitute, MvPolynomial.aeval_eq_eval, eval_realCoefficientEquiv]

end Erdos3.VectorPolynomial

namespace Erdos3.VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L]

theorem realChartSubstitute_lie (f : σ → MvPolynomial τ ℝ)
    (p q : VectorPolynomial σ ℚ L) :
    realChartSubstitute f ⁅p, q⁆ = ⁅realChartSubstitute f p, realChartSubstitute f q⁆ := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval₂_zero (K := ℝ)
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  rw [eval₂_realChartSubstitute]
  change eval₂Lie (R := ℚ) (fun i => MvPolynomial.eval x (f i)) ⁅p, q⁆ =
    eval₂Lie (R := ℚ) x ⁅realChartSubstitute f p, realChartSubstitute f q⁆
  rw [LieHom.map_lie, LieHom.map_lie]
  simp only [eval₂Lie_apply, eval₂_realChartSubstitute]

attribute [local irreducible] realChartSubstitute

noncomputable def realChartSubstituteLie (f : σ → MvPolynomial τ ℝ) :
    VectorPolynomial σ ℚ L →ₗ⁅ℚ⁆ VectorPolynomial τ ℚ L :=
  lieHomOfLinearMap (realChartSubstitute f) (realChartSubstitute_lie f)

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥)

noncomputable def realPolynomialChartSubstitution (f : σ → MvPolynomial τ ℝ) :
    PolynomialGroup σ hnil →* PolynomialGroup τ hnil :=
  NilpotentLieBCHGroup.map (realChartSubstituteLie f)

@[simp] theorem realPolynomialChartSubstitution_coord (f : σ → MvPolynomial τ ℝ)
    (p : PolynomialGroup σ hnil) :
    (realPolynomialChartSubstitution hnil f p).coord = realChartSubstitute f p.coord := rfl

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialShearAffineExponential
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial Module

variable {σ R : Type*} [CommRing R]

abbrev PolynomialShearIndex (w : σ → ℕ) :=
  Σ i : σ, {a : σ →₀ ℕ // Finsupp.weight w a + 1 ≤ w i}

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

attribute [local instance 100] LieRing.ofAssociativeRing

variable {σ R : Type*} [CommRing R] {w : σ → ℕ}

noncomputable def polynomialShearEnd (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) where
  toFun P := ⟨D.val P, weightedSupportDrop_le
    (weightedDerivation_apply_le w D.val 1 D.property P.property)⟩
  map_add' P Q := by
    apply Subtype.ext
    exact D.val.map_add P Q
  map_smul' c P := by
    apply Subtype.ext
    exact D.val.map_smul c P

theorem polynomialShearEnd_pow_coe (D : PolynomialShearLieAlgebra w R) (n k : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    ((polynomialShearEnd D n ^ k) P : MvPolynomial σ R) =
      (D.val.toLinearMap ^ k) (P : MvPolynomial σ R) := by
  induction k generalizing P with
  | zero => rfl
  | succ k ih =>
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply]
      rfl

theorem polynomialShearEnd_pow_eq_zero (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    polynomialShearEnd D n ^ (n + 1) = 0 := by
  apply LinearMap.ext
  intro P
  apply Subtype.ext
  change ((polynomialShearEnd D n ^ (n + 1)) P : MvPolynomial σ R) = 0
  rw [polynomialShearEnd_pow_coe]
  exact weightedDerivation_pow_eq_zero w D.val D.property P.property

theorem polynomialShearEnd_isNilpotent (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    IsNilpotent (polynomialShearEnd D n) := ⟨n + 1, polynomialShearEnd_pow_eq_zero D n⟩

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearExpOn (D : PolynomialShearLieAlgebra w R) (n : ℕ) :
    Module.End R (weightedSupportLE (R := R) w n) :=
  IsNilpotent.exp (polynomialShearEnd D n)

theorem polynomialShearExpOn_sum (D : PolynomialShearLieAlgebra w R) (n : ℕ)
    (P : weightedSupportLE (R := R) w n) :
    (polynomialShearExpOn D n P : MvPolynomial σ R) =
      ∑ k ∈ Finset.range (n + 1), (k.factorial : ℚ)⁻¹ •
        (D.val.toLinearMap ^ k) (P : MvPolynomial σ R) := by
  simp [polynomialShearExpOn, IsNilpotent.exp_eq_sum (a := polynomialShearEnd D n) (polynomialShearEnd_pow_eq_zero D n),
    polynomialShearEnd_pow_coe]

end Erdos3

end

section

namespace Erdos3

open _root_.MvPolynomial

variable {σ R : Type*} [CommRing R] [Algebra ℚ R] {w : σ → ℕ}

noncomputable def polynomialShearExp (D : PolynomialShearLieAlgebra w R)
    (P : MvPolynomial σ R) : MvPolynomial σ R :=
  polynomialShearExpOn D (P.weightedTotalDegree w)
    ⟨P, (mem_weightedSupportLE_iff w _ P).mpr le_rfl⟩

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

variable {σ : Type*} [Fintype σ]

namespace PolynomialTranslationLie

noncomputable def weightedFiltration (w : σ → ℕ) (d : ℕ) (hw : ∀ i, w i ≤ d) :
    NilpotentLieFiltration (weightedSubalgebra w d) d where
  layer k := (weightedLayer w d k).comap (weightedSubalgebra w d).subtype
  antitone := fun i j hij x hx => weightedLayer_antitone w d hij hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => weightedLayer_lie_mem w d hx hy
  terminal := by
    rw [weightedLayer_terminal w d hw]
    exact LinearMap.ker_eq_bot.mpr (weightedSubalgebra w d).subtype_injective

end PolynomialTranslationLie
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankHorizontalSymbol
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial
open scoped BigOperators

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def rankLayerCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.adaptedLieSubalgebra w →ₗ[ℚ] F.layer (Finsupp.weight w α) 1 :=
  (F.associatedDegree.adaptedCoefficientMap w α).codRestrict (F.layer (Finsupp.weight w α) 1) (by
    intro p
    rw [← F.rank_zero_eq_one]
    exact p.property α)

@[simp] theorem rankLayerCoefficient_coe (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.associatedDegree.adaptedLieSubalgebra w) :
    (F.rankLayerCoefficient w α p : L) = coefficients p.val α := rfl

noncomputable def higherHorizontalCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.adaptedLieSubalgebra w →ₗ[ℚ] F.HigherHorizontal (Finsupp.weight w α) :=
  (F.higherHorizontalMk (Finsupp.weight w α)).comp (F.rankLayerCoefficient w α)

end Erdos3.DegreeRankLieFiltration

end

section

namespace Erdos3.DegreeRankLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

noncomputable def higherHorizontalSymbolCoefficient (w : σ → ℕ) (α : σ →₀ ℕ) :
    F.associatedDegree.PolynomialSymbol w →ₗ[ℚ] F.HigherHorizontal (Finsupp.weight w α) :=
  (F.associatedDegree.shiftedAdaptedIdeal w).toSubmodule.liftQ
    (F.higherHorizontalCoefficient w α) (by
      intro p hp
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      exact F.lex_antitone (Or.inl (Nat.lt_succ_self (Finsupp.weight w α))) (hp α))

@[simp] theorem higherHorizontalSymbolCoefficient_map (w : σ → ℕ) (α : σ →₀ ℕ)
    (p : F.associatedDegree.adaptedLieSubalgebra w) :
    F.higherHorizontalSymbolCoefficient w α (F.associatedDegree.polynomialSymbolMap w p) =
      F.higherHorizontalCoefficient w α p := rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RankPolynomialFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hlayers

theorem polynomialSymbolBasis_bracket [DecidableEq σ] (w : σ → ℕ) (u v z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hlayers w).repr
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ z =
      if u.val.1 + v.val.1 = z.val.1 then b.repr ⁅b u.val.2, b v.val.2⁆ z.val.2 else 0 := by
  classical
  let lift (x : SymbolBasisIndex w ω) : F.adaptedLieSubalgebra w :=
    F.adaptedMonomialBasis b ω hlayers w ⟨x.val, x.property.le⟩
  have hlift (x : SymbolBasisIndex w ω) :
      (lift x : VectorPolynomial σ ℚ L) = monomial x.val.1 (b x.val.2) :=
    F.adaptedMonomialBasis_coe b ω hlayers w _
  have hbracket : (⁅lift u, lift v⁆ : F.adaptedLieSubalgebra w).val =
      monomial (u.val.1 + v.val.1) ⁅b u.val.2, b v.val.2⁆ := by
    change ⁅(lift u : VectorPolynomial σ ℚ L), (lift v : VectorPolynomial σ ℚ L)⁆ = _
    rw [hlift, hlift, lie_monomial]
  rw [F.polynomialSymbolBasis_apply b ω hlayers w u,
    F.polynomialSymbolBasis_apply b ω hlayers w v, ← LieHom.map_lie,
    F.polynomialSymbolBasis_repr_map]
  change b.repr (coefficients ((⁅lift u, lift v⁆ : F.adaptedLieSubalgebra w) :
    VectorPolynomial σ ℚ L) z.val.1) z.val.2 = _
  rw [hbracket, coefficients_monomial]
  by_cases h : u.val.1 + v.val.1 = z.val.1 <;> simp [h]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

theorem symbolBasisIndex_degree_le (z : SymbolBasisIndex w ω) :
    z.val.1.sum (fun _ n => n) ≤ s := by
  apply le_trans ?_ (z.property.le.trans (hω z.val.2))
  simp only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul]
  exact Finset.sum_le_sum (fun i _ => Nat.le_mul_of_pos_right _ (hw i))

noncomputable def symbolBasisCode (z : SymbolBasisIndex w ω) :
    (Σ n : Fin (s + 1), Fin n.val → σ) × ι :=
  (⟨⟨z.val.1.toMultiset.toList.length, by
      rw [Multiset.length_toList, Finsupp.card_toMultiset]
      exact Nat.lt_succ_of_le (symbolBasisIndex_degree_le w ω s hw hω z)⟩,
    z.val.1.toMultiset.toList.get⟩, z.val.2)

theorem symbolBasisCode_injective : Function.Injective (symbolBasisCode w ω s hw hω) := by
  classical
  intro z u h
  have hi := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => t.2) h
  change z.val.2 = u.val.2 at hi
  have hl := congrArg (fun t : (Σ n : Fin (s + 1), Fin n.val → σ) × ι => List.ofFn t.1.2) h
  change List.ofFn z.val.1.toMultiset.toList.get = List.ofFn u.val.1.toMultiset.toList.get at hl
  rw [List.ofFn_get, List.ofFn_get] at hl
  have hm := congrArg (fun t : List σ => (t : Multiset σ)) hl
  rw [Multiset.coe_toList, Multiset.coe_toList] at hm
  apply Subtype.ext
  apply Prod.ext _ hi
  ext i
  have hh := congrArg (fun t : Multiset σ => t.count i) hm
  simpa only [Finsupp.count_toMultiset] using hh

variable [Fintype σ] [Fintype ι]

theorem symbolBasisIndex_finite : Finite (SymbolBasisIndex w ω) :=
  Finite.of_injective (symbolBasisCode w ω s hw hω) (symbolBasisCode_injective w ω s hw hω)

@[instance_reducible] noncomputable def symbolBasisIndexFintype : Fintype (SymbolBasisIndex w ω) := by
  let : Finite (SymbolBasisIndex w ω) := symbolBasisIndex_finite w ω s hw hω
  exact Fintype.ofFinite _

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialSymbolFiltration (w : σ → ℕ) :
    NilpotentLieFiltration (F.PolynomialSymbol w) s :=
  (F.adaptedPolynomialFiltration w).quotientLie (F.shiftedAdaptedIdeal w) (by
    rw [(F.adaptedPolynomialFiltration w).terminal]
    exact bot_le)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def polynomialOrbitCoordinates (w : σ → ℕ) :
    F.PolynomialOrbit w ≃* (F.adaptedPolynomialFiltration w).Group where
  toFun g := ⟨⟨g.log, g.property⟩⟩
  invFun g := ⟨⟨g.coord.val⟩, g.coord.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' g h := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact (map_lieBCH (F.adaptedLieSubalgebra w).incl s
      (⟨g.log, g.property⟩ : F.adaptedLieSubalgebra w)
      (⟨h.log, h.property⟩ : F.adaptedLieSubalgebra w)).symm

@[simp] theorem polynomialOrbitCoordinates_log (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    ((F.polynomialOrbitCoordinates w g).coord : VectorPolynomial σ ℚ L) = g.log := rfl

@[simp] theorem polynomialOrbitCoordinates_symm_log (w : σ → ℕ)
    (g : (F.adaptedPolynomialFiltration w).Group) :
    (F.polynomialOrbitCoordinates w |>.symm g).log = g.coord.val := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial

@[simp] theorem weight_unitMonomial (n : ℕ) :
    Finsupp.weight (fun _ : Unit => 1) (unitMonomial n) = n := by
  simp [unitMonomial, Finsupp.weight_single]

@[simp] theorem unitMonomial_weight (α : Unit →₀ ℕ) :
    unitMonomial (Finsupp.weight (fun _ : Unit => 1) α) = α := by
  have h : α = Finsupp.single () (α ()) := by
    apply Finsupp.ext
    intro i
    cases i
    simp
  rw [h]
  simp [unitMonomial, Finsupp.weight_single]

theorem unitMonomial_injective : Function.Injective unitMonomial := by
  intro m n h
  have hh := congrArg (Finsupp.weight (fun _ : Unit => 1)) h
  simpa only [weight_unitMonomial] using hh

@[simp] theorem unitMonomial_add (m n : ℕ) :
    unitMonomial (m + n) = unitMonomial m + unitMonomial n :=
  Finsupp.single_add _ _ _

namespace NilpotentLieFiltration

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

abbrev AssociatedGraded (F : NilpotentLieFiltration L s) :=
  F.PolynomialSymbol (fun _ : Unit => 1)

noncomputable def associatedGradedIndexEquiv (ω : ι → ℕ) :
    SymbolBasisIndex (fun _ : Unit => 1) ω ≃ ι where
  toFun z := z.val.2
  invFun i := ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · exact (congrArg unitMonomial z.property.symm).trans (unitMonomial_weight z.val.1)
    · rfl
  right_inv _ := rfl

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def associatedGradedBasis : Basis ι ℚ F.AssociatedGraded :=
  (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).reindex (associatedGradedIndexEquiv ω)

@[simp] theorem associatedGradedBasis_apply (i : ι) :
    F.associatedGradedBasis b ω hlayers i =
      F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.reindex_apply]
  rfl

theorem associatedGradedBasis_repr (x : F.AssociatedGraded) (i : ι) :
    (F.associatedGradedBasis b ω hlayers).repr x i =
      (F.polynomialSymbolBasis b ω hlayers (fun _ : Unit => 1)).repr x
        ⟨(unitMonomial (ω i), i), weight_unitMonomial (ω i)⟩ := by
  rw [associatedGradedBasis, Basis.repr_reindex_apply]
  rfl

theorem associatedGradedBasis_bracket (i j k : ι) :
    (F.associatedGradedBasis b ω hlayers).repr
      ⁅F.associatedGradedBasis b ω hlayers i, F.associatedGradedBasis b ω hlayers j⁆ k =
      if ω i + ω j = ω k then b.repr ⁅b i, b j⁆ k else 0 := by
  classical
  rw [F.associatedGradedBasis_repr, F.associatedGradedBasis_apply,
    F.associatedGradedBasis_apply, F.polynomialSymbolBasis_bracket]
  simp only [← unitMonomial_add, unitMonomial_injective.eq_iff]

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def gradedMonomialLinear (j : ℕ) :
    F.layer j →ₗ[ℚ] F.adaptedLieSubalgebra (fun _ : Unit => 1) where
  toFun v := ⟨monomial (unitMonomial j) (v : L),
    F.monomial_mem_adaptedSubmodule (fun _ : Unit => 1) (unitMonomial j)
      (by simpa only [weight_unitMonomial] using v.property)⟩
  map_add' x y := by
    apply Subtype.ext
    exact TensorProduct.tmul_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    exact TensorProduct.tmul_smul a _ _

@[simp] theorem gradedMonomialLinear_coe (j : ℕ) (v : F.layer j) :
    (F.gradedMonomialLinear j v : VectorPolynomial Unit ℚ L) = monomial (unitMonomial j) (v : L) := rfl

noncomputable def associatedGradedPieceMap (j : ℕ) : F.layer j →ₗ[ℚ] F.AssociatedGraded :=
  (F.polynomialSymbolMap (fun _ : Unit => 1)).toLinearMap.comp (F.gradedMonomialLinear j)

@[simp] theorem associatedGradedPieceMap_apply (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v =
      F.polynomialSymbolMap (fun _ : Unit => 1) (F.gradedMonomialLinear j v) := rfl

theorem associatedGradedPieceMap_eq_zero_iff (j : ℕ) (v : F.layer j) :
    F.associatedGradedPieceMap j v = 0 ↔ (v : L) ∈ F.layer (j + 1) := by
  rw [F.associatedGradedPieceMap_apply, F.polynomialSymbolMap_eq_zero_iff]
  simp only [F.gradedMonomialLinear_coe, coefficients_monomial]
  constructor
  · intro h
    simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h (unitMonomial j)
  · intro h α
    by_cases hα : unitMonomial j = α
    · subst α
      simpa only [Finsupp.single_eq_same, weight_unitMonomial] using h
    · rw [Finsupp.single_eq_of_ne (Ne.symm hα)]
      exact Submodule.zero_mem _

theorem associatedGradedPieceMap_lie (i j : ℕ) (u : F.layer i) (v : F.layer j) :
    ⁅F.associatedGradedPieceMap i u, F.associatedGradedPieceMap j v⁆ =
      F.associatedGradedPieceMap (i + j) ⟨⁅(u : L), (v : L)⁆, F.lie_mem u.property v.property⟩ := by
  simp only [F.associatedGradedPieceMap_apply]
  rw [← LieHom.map_lie]
  apply congrArg (F.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  change ⁅monomial (unitMonomial i) (u : L), monomial (unitMonomial j) (v : L)⁆ = _
  rw [lie_monomial, ← unitMonomial_add]
  rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (U : LieSubalgebra ℚ F.AssociatedGraded)

noncomputable def gradedRefiltrationLayer (j : ℕ) : Submodule ℚ L :=
  (U.toSubmodule.comap (F.associatedGradedPieceMap j)).map (F.layer j).subtype

theorem mem_gradedRefiltrationLayer (j : ℕ) (v : L) :
    v ∈ F.gradedRefiltrationLayer U j ↔
      ∃ hv : v ∈ F.layer j, F.associatedGradedPieceMap j ⟨v, hv⟩ ∈ U := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.property, hx⟩
  · rintro ⟨hv, hU⟩
    exact ⟨⟨v, hv⟩, hU, rfl⟩

theorem gradedRefiltrationLayer_le (j : ℕ) : F.gradedRefiltrationLayer U j ≤ F.layer j := by
  intro v hv
  exact ((F.mem_gradedRefiltrationLayer U j v).mp hv).choose

theorem layer_succ_le_gradedRefiltrationLayer (j : ℕ) :
    F.layer (j + 1) ≤ F.gradedRefiltrationLayer U j := by
  intro v hv
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.antitone (Nat.le_succ j) hv, ?_⟩
  rw [(F.associatedGradedPieceMap_eq_zero_iff j _).mpr hv]
  exact U.zero_mem

theorem gradedRefiltrationLayer_antitone : Antitone (F.gradedRefiltrationLayer U) := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact (F.gradedRefiltrationLayer_le U j).trans
      ((F.antitone hlt).trans (F.layer_succ_le_gradedRefiltrationLayer U i))
  · exact le_rfl

theorem gradedRefiltrationLayer_lie_mem {i j : ℕ} {v z : L}
    (hv : v ∈ F.gradedRefiltrationLayer U i) (hz : z ∈ F.gradedRefiltrationLayer U j) :
    ⁅v, z⁆ ∈ F.gradedRefiltrationLayer U (i + j) := by
  obtain ⟨hv, hUv⟩ := (F.mem_gradedRefiltrationLayer U i v).mp hv
  obtain ⟨hz, hUz⟩ := (F.mem_gradedRefiltrationLayer U j z).mp hz
  rw [F.mem_gradedRefiltrationLayer]
  refine ⟨F.lie_mem hv hz, ?_⟩
  rw [← F.associatedGradedPieceMap_lie i j ⟨v, hv⟩ ⟨z, hz⟩]
  exact U.lie_mem hUv hUz

theorem gradedRefiltrationLayer_terminal : F.gradedRefiltrationLayer U (s + 1) = ⊥ :=
  bot_unique ((F.gradedRefiltrationLayer_le U (s + 1)).trans F.terminal.le)

noncomputable def gradedRefiltrationSubalgebra : LieSubalgebra ℚ L :=
  { F.gradedRefiltrationLayer U 1 with
    lie_mem' := fun hv hz => F.gradedRefiltrationLayer_antitone U (by decide : 1 ≤ 1 + 1)
      (F.gradedRefiltrationLayer_lie_mem U hv hz) }

noncomputable def gradedRefiltration :
    NilpotentLieFiltration (F.gradedRefiltrationSubalgebra U) s where
  layer j := (F.gradedRefiltrationLayer U j).comap (F.gradedRefiltrationSubalgebra U).incl.toLinearMap
  antitone := fun _ _ hij _ hv => F.gradedRefiltrationLayer_antitone U hij hv
  one_eq_top := by
    apply top_unique
    intro v _
    exact v.property
  lie_mem := fun hv hz => F.gradedRefiltrationLayer_lie_mem U hv hz
  terminal := by
    apply bot_unique
    intro v hv
    change v = 0
    apply Subtype.ext
    exact (Submodule.mem_bot ℚ).mp ((F.gradedRefiltrationLayer_terminal U) ▸ hv)

@[simp] theorem mem_gradedRefiltration_layer (j : ℕ) (v : F.gradedRefiltrationSubalgebra U) :
    v ∈ (F.gradedRefiltration U).layer j ↔ (v : L) ∈ F.gradedRefiltrationLayer U j := Iff.rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SymbolAbsorptionBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

abbrev RealPolynomialSymbol {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  ℝ ⊗[ℚ] F.PolynomialSymbol w

abbrev RealPolynomialSymbolGroup {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) :=
  NilpotentLieBCHGroup (F.RealPolynomialSymbol w) s
    (realification_lowerCentralSeries_eq_bot (F.polynomialSymbol_lowerCentralSeries_eq_bot w))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def SymbolSlowBound {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  ∀ z : SymbolBasisIndex w ω,
    |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr g.coord z| ≤
      M / monomialScale T z.val.1

@[simp] theorem symbolSlowBound_inv_iff {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound b ω hlayers w T M g⁻¹ ↔ F.SymbolSlowBound b ω hlayers w T M g := by
  simp only [SymbolSlowBound, NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply, abs_neg]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

noncomputable def truncateRealGrades (j : ℕ) (g : F.realification.Group) : F.realification.Group :=
  ⟨basisBelowProjection (b.baseChange ℝ) w j g.coord⟩

@[simp] theorem truncateRealGrades_coord (j : ℕ) (g : F.realification.Group) :
    (F.truncateRealGrades b w j g).coord = basisBelowProjection (b.baseChange ℝ) w j g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i})) (v : σ → ℕ)

noncomputable def truncateRealSymbol (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    F.RealPolynomialSymbolGroup v :=
  (F.polynomialSymbolFiltration v).truncateRealGrades
    (F.polynomialSymbolBasis b w hlayers v) (fun z => w z.val.2) j g

@[simp] theorem truncateRealSymbol_coord (j : ℕ) (g : F.RealPolynomialSymbolGroup v) :
    (F.truncateRealSymbol b w hlayers v j g).coord =
      basisBelowProjection ((F.polynomialSymbolBasis b w hlayers v).baseChange ℝ)
        (fun z => w z.val.2) j g.coord := rfl

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module

variable {σ ι R S V : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]

noncomputable def mixedCoordinates (b : Basis ι S V) :
    VectorPolynomial σ R V ≃ₗ[R] ((σ →₀ ℕ) × ι) →₀ S :=
  coefficients.trans ((Finsupp.mapRange.linearEquiv (b.repr.restrictScalars R)).trans
    (Finsupp.curryLinearEquiv R).symm)

@[simp] theorem mixedCoordinates_apply (b : Basis ι S V)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) (i : ι) :
    mixedCoordinates b p (α, i) = b.repr (coefficients p α) i := rfl

@[simp] theorem mixedCoordinates_symm_apply (b : Basis ι S V)
    (c : ((σ →₀ ℕ) × ι) →₀ S) (α : σ →₀ ℕ) (i : ι) :
    b.repr (coefficients ((mixedCoordinates b).symm c : VectorPolynomial σ R V) α) i =
      c (α, i) := by
  rw [← mixedCoordinates_apply, LinearEquiv.apply_symm_apply]

noncomputable def ofSupportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : (A →₀ S) →ₗ[R] VectorPolynomial σ R V :=
  (mixedCoordinates b).symm.toLinearMap.comp (Finsupp.lmapDomain S R Subtype.val)

@[simp] theorem ofSupportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) (z : A) :
    b.repr (coefficients (ofSupportedCoordinates (R := R) b A c) z.val.1) z.val.2 = c z := by
  change mixedCoordinates b ((mixedCoordinates b).symm _) z.val = _
  rw [LinearEquiv.apply_symm_apply]
  exact Finsupp.mapDomain_apply Subtype.val_injective c z

theorem ofSupportedCoordinates_apply_of_not_mem (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) (α : σ →₀ ℕ) (i : ι)
    (h : (α, i) ∉ A) :
    b.repr (coefficients (ofSupportedCoordinates (R := R) b A c) α) i = 0 := by
  change mixedCoordinates b ((mixedCoordinates b).symm _) (α, i) = _
  rw [LinearEquiv.apply_symm_apply]
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨z, hz⟩
  exact h (hz ▸ z.property)

noncomputable def supportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) : VectorPolynomial σ R V →ₗ[R] A →₀ S :=
  (Finsupp.lsubtypeDomain A).comp (mixedCoordinates b).toLinearMap

@[simp] theorem supportedCoordinates_apply (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (p : VectorPolynomial σ R V) (z : A) :
    supportedCoordinates b A p z = b.repr (coefficients p z.val.1) z.val.2 := rfl

@[simp] theorem supportedCoordinates_ofSupportedCoordinates (b : Basis ι S V)
    (A : Set ((σ →₀ ℕ) × ι)) (c : A →₀ S) :
    supportedCoordinates b A (ofSupportedCoordinates (R := R) b A c) = c := by
  ext z
  exact ofSupportedCoordinates_apply b A c z

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realificationLinearEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) ≃ₗ[ℚ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) :=
  TensorProduct.leftComm ℚ ℝ (MvPolynomial σ ℚ) V

@[simp] theorem coefficients_realificationLinearEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ V) (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    change coefficients (f ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v)) α = _
    rw [coefficients_tmul, coefficients_tmul, TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

end Linear

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]

noncomputable def realificationLieEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ L) ≃ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  lieTensorLeftComm

@[simp] theorem realificationLieEquiv_tmul_tmul (a : ℝ) (p : MvPolynomial σ ℚ) (v : L) :
    realificationLieEquiv (a ⊗ₜ[ℚ] (p ⊗ₜ[ℚ] v)) = p ⊗ₜ[ℚ] (a ⊗ₜ[ℚ] v) :=
  TensorProduct.leftComm_tmul ℚ _ _ _

@[simp] theorem coefficients_realificationLieEquiv_tmul
    (a : ℝ) (p : VectorPolynomial σ ℚ L) (α : σ →₀ ℕ) :
    coefficients (realificationLieEquiv (a ⊗ₜ[ℚ] p)) α = a ⊗ₜ[ℚ] coefficients p α := by
  induction p using TensorProduct.induction_on with
  | zero => simp
  | tmul f v =>
    rw [realificationLieEquiv_tmul_tmul, coefficients_tmul, coefficients_tmul,
      TensorProduct.tmul_smul]
  | add p q hp hq =>
    simp only [TensorProduct.tmul_add, map_add, Finsupp.add_apply, hp, hq]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable instance realModule : Module ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) :=
  (realificationLinearEquiv (σ := σ) (V := V)).symm.toAddEquiv.module ℝ

noncomputable def realificationRealLinearEquiv :
    (ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) ≃ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) :=
  ((realificationLinearEquiv (σ := σ) (V := V)).symm.toAddEquiv.linearEquiv ℝ).symm

@[simp] theorem realificationRealLinearEquiv_apply
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) :
    realificationRealLinearEquiv x = realificationLinearEquiv x := rfl

theorem coefficients_realification_smul (a : ℝ)
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) (α : σ →₀ ℕ) :
    coefficients (realificationLinearEquiv (a • x)) α =
      a • coefficients (realificationLinearEquiv x) α := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r p =>
    rw [TensorProduct.smul_tmul', coefficients_realificationLinearEquiv_tmul,
      coefficients_realificationLinearEquiv_tmul, TensorProduct.smul_tmul']
  | add x y hx hy =>
    simp only [smul_add, map_add, Finsupp.add_apply, hx, hy]

@[simp] theorem coefficients_smul_real (a : ℝ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) (α : σ →₀ ℕ) :
    coefficients (a • P) α = a • coefficients P α := by
  obtain ⟨x, rfl⟩ := realificationRealLinearEquiv.surjective P
  rw [← map_smul, realificationRealLinearEquiv_apply, realificationRealLinearEquiv_apply]
  exact coefficients_realification_smul a x α

noncomputable def realCoefficient (α : σ →₀ ℕ) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) →ₗ[ℝ] ℝ ⊗[ℚ] V where
  toFun P := coefficients P α
  map_add' P Q := by simp only [map_add, Finsupp.add_apply]
  map_smul' a P := coefficients_smul_real a P α

@[simp] theorem realCoefficient_apply (α : σ →₀ ℕ)
    (P : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) : realCoefficient α P = coefficients P α := rfl

noncomputable def realMonomial (α : σ →₀ ℕ) :
    (ℝ ⊗[ℚ] V) →ₗ[ℝ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V) where
  toFun := monomial α
  map_add' x y := by
    apply coefficients.injective
    simp only [coefficients_monomial, map_add, Finsupp.single_add]
  map_smul' a x := by
    apply coefficients.injective
    ext β
    simp only [coefficients_smul_real, coefficients_monomial]
    exact DFunLike.congr_fun (Finsupp.smul_single a α x).symm β

@[simp] theorem realMonomial_apply (α : σ →₀ ℕ) (x : ℝ ⊗[ℚ] V) :
    realMonomial α x = monomial (R := ℚ) α x := rfl

end Linear

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

namespace VectorPolynomial

theorem ofSupportedCoordinates_single {σ ι R S V : Type*}
    [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V]
    (b : Basis ι S V) (A : Set ((σ →₀ ℕ) × ι)) (z : A) (c : S) :
    ofSupportedCoordinates (R := R) b A (Finsupp.single z c) =
      monomial z.val.1 (c • b z.val.2) := by
  classical
  apply (mixedCoordinates b).injective
  change mixedCoordinates b ((mixedCoordinates b).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  change Finsupp.mapDomain Subtype.val (Finsupp.single z c) = _
  rw [Finsupp.mapDomain_single]
  apply Finsupp.ext
  rintro ⟨α, i⟩
  rw [mixedCoordinates_apply, coefficients_monomial]
  by_cases hα : z.val.1 = α <;> by_cases hi : z.val.2 = i <;>
    simp [Finsupp.single_apply, Prod.ext_iff, hα, hi]

end VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def gradedSymbolPolynomial :
    F.PolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ F.AssociatedGraded :=
  (ofSupportedCoordinates (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}).comp
      (F.polynomialSymbolBasis b ω hlayers w).repr.toLinearMap

@[simp] theorem gradedSymbolPolynomial_coefficient (x : F.PolynomialSymbol w)
    (z : SymbolBasisIndex w ω) :
    (F.associatedGradedBasis b ω hlayers).repr
      (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) z.val.1) z.val.2 =
      (F.polynomialSymbolBasis b ω hlayers w).repr x z := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize (F.polynomialSymbolBasis b ω hlayers w).repr x = c
  have h := ofSupportedCoordinates_apply (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    c z
  convert h using 2

theorem gradedSymbolPolynomial_coefficient_of_ne (x : F.PolynomialSymbol w)
    (α : σ →₀ ℕ) (i : ι) (h : Finsupp.weight w α ≠ ω i) :
    (F.associatedGradedBasis b ω hlayers).repr
      (coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α) i = 0 := by
  dsimp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe]
  generalize (F.polynomialSymbolBasis b ω hlayers w).repr x = c
  have hh := ofSupportedCoordinates_apply_of_not_mem (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
    c α i h
  convert hh using 2

@[simp] theorem gradedSymbolPolynomial_basis (z : SymbolBasisIndex w ω) :
    F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w z) =
      monomial z.val.1 (F.associatedGradedBasis b ω hlayers z.val.2) := by
  simp only [gradedSymbolPolynomial, LinearMap.comp_apply, LinearEquiv.coe_coe, Basis.repr_self]
  have h := ofSupportedCoordinates_single (R := ℚ) (F.associatedGradedBasis b ω hlayers)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2} z (1 : ℚ)
  simpa only [one_smul] using h

theorem gradedSymbolPolynomial_lie_basis (u v : SymbolBasisIndex w ω) :
    F.gradedSymbolPolynomial b ω hlayers w
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ =
      ⁅F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w u),
        F.gradedSymbolPolynomial b ω hlayers w (F.polynomialSymbolBasis b ω hlayers w v)⁆ := by
  classical
  rw [F.gradedSymbolPolynomial_basis, F.gradedSymbolPolynomial_basis, lie_monomial]
  apply coefficients.injective
  ext α
  apply (F.associatedGradedBasis b ω hlayers).repr.injective
  ext i
  rw [coefficients_monomial]
  by_cases hα : u.val.1 + v.val.1 = α
  · subst α
    rw [Finsupp.single_eq_same]
    rw [F.associatedGradedBasis_bracket]
    by_cases hd : Finsupp.weight w (u.val.1 + v.val.1) = ω i
    · have hgrade : ω u.val.2 + ω v.val.2 = ω i := by
        simpa only [map_add, u.property, v.property] using hd
      rw [if_pos hgrade]
      have hc := F.gradedSymbolPolynomial_coefficient b ω hlayers w
        ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆
        ⟨(u.val.1 + v.val.1, i), hd⟩
      exact hc.trans (by rw [F.polynomialSymbolBasis_bracket, if_pos rfl])
    · have hgrade : ω u.val.2 + ω v.val.2 ≠ ω i := by
        simpa only [map_add, u.property, v.property] using hd
      rw [if_neg hgrade]
      exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ _ _ hd
  · rw [Finsupp.single_eq_of_ne (Ne.symm hα), map_zero, Finsupp.zero_apply]
    by_cases hd : Finsupp.weight w α = ω i
    · have hc := F.gradedSymbolPolynomial_coefficient b ω hlayers w
        ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆
        ⟨(α, i), hd⟩
      exact hc.trans (by rw [F.polynomialSymbolBasis_bracket, if_neg hα])
    · exact F.gradedSymbolPolynomial_coefficient_of_ne b ω hlayers w _ _ _ hd

noncomputable def gradedSymbolPolynomialLie :
    F.PolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ F.AssociatedGraded where
  toLinearMap := F.gradedSymbolPolynomial b ω hlayers w
  map_lie' {x y} := by
    change F.gradedSymbolPolynomial b ω hlayers w ⁅x, y⁆ =
      ⁅F.gradedSymbolPolynomial b ω hlayers w x, F.gradedSymbolPolynomial b ω hlayers w y⁆
    apply linear_map_lie_of_basis (F.polynomialSymbolBasis b ω hlayers w)
      (F.gradedSymbolPolynomial b ω hlayers w) ?_ x y
    intro u v
    have h := F.gradedSymbolPolynomial_lie_basis b ω hlayers w u v
    convert h using 2

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realGradedSymbolPolynomial :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.AssociatedGraded) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.gradedSymbolPolynomialLie b ω hlayers w))

@[simp] theorem realGradedSymbolPolynomial_coefficient_tmul
    (a : ℝ) (x : F.PolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (F.realGradedSymbolPolynomial b ω hlayers w (a ⊗ₜ[ℚ] x)) α =
      a ⊗ₜ[ℚ] coefficients (F.gradedSymbolPolynomial b ω hlayers w x) α := by
  simp only [realGradedSymbolPolynomial, LieHom.comp_apply, LieEquiv.coe_toLieHom,
    LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply]
  have he : F.gradedSymbolPolynomialLie b ω hlayers w x = F.gradedSymbolPolynomial b ω hlayers w x := rfl
  rw [he]
  exact coefficients_realificationLieEquiv_tmul a (F.gradedSymbolPolynomial b ω hlayers w x) α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PetalComparisonTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def symbolPointwiseSubalgebra (U : LieSubalgebra ℚ F.AssociatedGraded) :
    LieSubalgebra ℚ (F.PolynomialSymbol w) :=
  (coefficientLieSubalgebra U).comap (F.gradedSymbolPolynomialLie b ω hlayers w)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_smul_real (g : NilpotentLieBCHGroup L s hnil) (r : ℝ) (x : L) :
    dualAdjoint g (r • x) = r • dualAdjoint g x := by
  let T : L →ₗ[ℚ] L := r • LinearMap.id
  have hT : ∀ a b : L, b ∈ (⊤ : LieIdeal ℚ L) →
      T ⁅a, b⁆ = ⁅(LieHom.id : L →ₗ⁅ℚ⁆ L) a, T b⁆ := by
    intro a b _
    change r • ⁅a, b⁆ = ⁅a, r • b⁆
    exact (lie_smul r a b).symm
  exact (dualLinearLift_adjoint_eq hnil ⊤ LieHom.id T hT g x
    (by trivial) g (r • x) rfl rfl).symm

noncomputable def dualAdjointRealLinearEquiv (g : NilpotentLieBCHGroup L s hnil) :
    L ≃ₗ[ℝ] L :=
  { dualAdjointAddEquiv g with map_smul' := dualAdjoint_smul_real g }

@[simp] theorem dualAdjointRealLinearEquiv_apply
    (g : NilpotentLieBCHGroup L s hnil) (x : L) :
    dualAdjointRealLinearEquiv g x = dualAdjoint g x := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualAdjoint_real_mem_of_invariant (U : LieSubalgebra ℚ L) (V : Submodule ℝ L)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : L) (hx : x ∈ V) :
    dualAdjoint g x ∈ V :=
  dualAdjoint_mem_of_invariant U (V.restrictScalars ℚ) hUV g hg x hx

noncomputable def invariantRealAdjoint (U : LieSubalgebra ℚ L) (W : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) : W ≃ₗ[ℝ] W where
  toFun x := ⟨dualAdjoint g x.val, dualAdjoint_real_mem_of_invariant U W hUW g hg x.val x.property⟩
  invFun x := ⟨dualAdjoint g⁻¹ x.val,
    dualAdjoint_real_mem_of_invariant U W hUW g⁻¹ (U.neg_mem hg) x.val x.property⟩
  left_inv x := Subtype.ext (dualAdjoint_inv_cancel g x.val)
  right_inv x := Subtype.ext (dualAdjoint_cancel_inv g x.val)
  map_add' x y := Subtype.ext (dualAdjoint_add g x.val y.val)
  map_smul' r x := Subtype.ext (dualAdjoint_smul_real g r x.val)

@[simp] theorem invariantRealAdjoint_coe (U : LieSubalgebra ℚ L) (W : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : W) :
    (invariantRealAdjoint U W hUW g hg x : L) = dualAdjoint g x.val := rfl

theorem invariantRealAdjoint_map_submodule (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) :
    (V.comap W.subtype).map (invariantRealAdjoint U W hUW g hg).toLinearMap = V.comap W.subtype := by
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    exact dualAdjoint_real_mem_of_invariant U V hUV g hg x.val hx
  · intro y hy
    refine ⟨(invariantRealAdjoint U W hUW g hg).symm y, ?_, ?_⟩
    · exact dualAdjoint_real_mem_of_invariant U V hUV g⁻¹ (U.neg_mem hg) y.val hy
    · exact (invariantRealAdjoint U W hUW g hg).apply_symm_apply y

noncomputable def invariantRealAdjointQuotient (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) :
    (W ⧸ V.comap W.subtype) ≃ₗ[ℝ] (W ⧸ V.comap W.subtype) :=
  Submodule.Quotient.equiv _ _ (invariantRealAdjoint U W hUW g hg)
    (invariantRealAdjoint_map_submodule U W V hUW hUV g hg)

@[simp] theorem invariantRealAdjointQuotient_mk (U : LieSubalgebra ℚ L) (W V : Submodule ℝ L)
    (hUW : ∀ u ∈ U, ∀ w ∈ W, ⁅u, w⁆ ∈ W)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (g : NilpotentLieBCHGroup L s hnil) (hg : g.coord ∈ U) (x : W) :
    invariantRealAdjointQuotient U W V hUW hUV g hg ((V.comap W.subtype).mkQ x) =
      (V.comap W.subtype).mkQ (invariantRealAdjoint U W hUW g hg x) := rfl

end Erdos3.NilpotentLieBCHGroup

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def realSymbolRepresentative :
    F.RealPolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) where
  toFun x := ofSupportedCoordinates (b.baseChange ℝ)
    {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
      (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x)
  map_add' x y := by simp only [map_add]
  map_smul' a x := by
    have h := (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.restrictScalars ℚ).map_smul a x
    change ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr (a • x) =
      a • ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x at h
    rw [h, map_smul]
    rfl

noncomputable def realSymbolOfPolynomial :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) →ₗ[ℚ] F.RealPolynomialSymbol w :=
  (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.symm.restrictScalars ℚ).toLinearMap.comp
    (supportedCoordinates (b.baseChange ℝ)
      {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2})

@[simp] theorem realSymbolRepresentative_coefficient
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (b.baseChange ℝ).repr
      (coefficients (F.realSymbolRepresentative b ω hlayers w x) z.val.1) z.val.2 =
      ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z := by
  dsimp only [realSymbolRepresentative, LinearMap.coe_mk, AddHom.coe_mk]
  generalize ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x = c
  have hc := ofSupportedCoordinates_apply (σ := σ) (ι := ι) (R := ℚ) (S := ℝ) (V := ℝ ⊗[ℚ] L) (b.baseChange ℝ)
        {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
        c z
  convert hc using 2

theorem realSymbolRepresentative_coefficient_of_ne
    (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) (i : ι)
    (h : Finsupp.weight w α ≠ ω i) :
    (b.baseChange ℝ).repr (coefficients (F.realSymbolRepresentative b ω hlayers w x) α) i = 0 := by
  dsimp only [realSymbolRepresentative, LinearMap.coe_mk, AddHom.coe_mk]
  generalize ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x = c
  have hc := ofSupportedCoordinates_apply_of_not_mem (σ := σ) (ι := ι) (R := ℚ) (S := ℝ) (V := ℝ ⊗[ℚ] L) (b.baseChange ℝ)
        {z : (σ →₀ ℕ) × ι | Finsupp.weight w z.1 = ω z.2}
        c α i h
  convert hc using 2

@[simp] theorem realSymbolOfPolynomial_coordinate
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      (F.realSymbolOfPolynomial b ω hlayers w p) z =
      (b.baseChange ℝ).repr (coefficients p z.val.1) z.val.2 := by
  change (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
    (((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.symm _)) z = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

@[simp] theorem realSymbolOfPolynomial_representative (x : F.RealPolynomialSymbol w) :
    F.realSymbolOfPolynomial b ω hlayers w (F.realSymbolRepresentative b ω hlayers w x) = x := by
  apply ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr.injective
  ext z
  rw [F.realSymbolOfPolynomial_coordinate, F.realSymbolRepresentative_coefficient]

include hlayers

theorem real_mem_layer_iff_basis_coordinates (j : ℕ) (v : ℝ ⊗[ℚ] L) :
    v ∈ F.realification.layer j ↔ ∀ i, ¬ j ≤ ω i → (b.baseChange ℝ).repr v i = 0 := by
  change v ∈ (F.realLayer j).toSubmodule ↔ _
  rw [F.realLayer_eq_span_basis b j {i | j ≤ ω i} (hlayers j), basis_mem_span_image_iff]
  rfl

theorem realSymbolRepresentative_adapted (x : F.RealPolynomialSymbol w) :
    F.realification.Adapted w (F.realSymbolRepresentative b ω hlayers w x) := by
  rw [F.realification.adapted_iff_coefficients]
  intro α
  apply (F.real_mem_layer_iff_basis_coordinates b ω hlayers _ _).mpr
  intro i hi
  exact F.realSymbolRepresentative_coefficient_of_ne b ω hlayers w x α i
    (fun h => hi h.le)

noncomputable def realAdaptedSymbolRepresentative (x : F.RealPolynomialSymbol w) :
    F.realification.adaptedLieSubalgebra w :=
  ⟨F.realSymbolRepresentative b ω hlayers w x,
    (F.realification.mem_adaptedSubmodule w _).mpr
      (F.realSymbolRepresentative_adapted b ω hlayers w x)⟩

@[simp] theorem realAdaptedSymbolRepresentative_coe (x : F.RealPolynomialSymbol w) :
    (F.realAdaptedSymbolRepresentative b ω hlayers w x : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) =
      F.realSymbolRepresentative b ω hlayers w x := rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

noncomputable def gradedBasisSplitting : F.AssociatedGraded ≃ₗ[ℚ] L :=
  (F.associatedGradedBasis b ω hlayers).repr.trans b.repr.symm

@[simp] theorem gradedBasisSplitting_coordinate (x : F.AssociatedGraded) (i : ι) :
    b.repr (F.gradedBasisSplitting b ω hlayers x) i =
      (F.associatedGradedBasis b ω hlayers).repr x i := by
  simp [gradedBasisSplitting]

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
theorem simplexCoordinateMoment_diagonalAPSimplex
    (r N : ℕ) (A : Finset (ZMod N))
    (p : DiagonalAPParameter r N A) :
    simplexCoordinateMoment (r + 2) N
      (diagonalAPSimplex r N A p) = p.1.1 := by
  simp [diagonalAPSimplex]

end Erdos3.FixedDensity

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DegreeRankBCH
namespace OAI

section

namespace Erdos3.DegreeRankLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (F : DegreeRankLieFiltration L s r)

def layerIdeal (d i : ℕ) : LieIdeal ℚ L :=
  { F.layer d i with
    lie_mem := by
      intro x y hy
      have hx : x ∈ F.layer 1 0 := by simp only [F.one_eq_top, Submodule.mem_top]
      exact F.lex_antitone (Or.inl (show d < 1 + d by omega)) (F.lie_mem hx hy) }

@[simp] theorem mem_layerIdeal (d i : ℕ) (x : L) :
    x ∈ F.layerIdeal d i ↔ x ∈ F.layer d i := Iff.rfl

abbrev Group := F.associatedDegree.Group

def subgroup (d i : ℕ) : Subgroup F.Group :=
  NilpotentLieBCHGroup.subgroup (F.layerIdeal d i).toLieSubalgebra

@[simp] theorem mem_subgroup (d i : ℕ) (x : F.Group) :
    x ∈ F.subgroup d i ↔ x.coord ∈ F.layer d i := Iff.rfl

end Erdos3.DegreeRankLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealAdaptedPolynomialGroup
namespace OAI

section

namespace Erdos3

namespace VectorPolynomial

variable {σ R L M : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]

noncomputable def mapLie (f : L →ₗ⁅R⁆ M) :
    VectorPolynomial σ R L →ₗ⁅R⁆ VectorPolynomial σ R M where
  toLinearMap := map f.toLinearMap
  map_lie' {p q} :=
    (LieAlgebra.ExtendScalars.map (AlgHom.id R (MvPolynomial σ R)) f).map_lie p q

end VectorPolynomial

namespace NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

noncomputable def filteredPolynomialMap :
    F.adaptedLieSubalgebra w →ₗ⁅ℚ⁆ G.adaptedLieSubalgebra w :=
  { ((VectorPolynomial.map f.toLinearMap).comp (F.adaptedLieSubalgebra w).incl.toLinearMap).codRestrict
      (G.adaptedLieSubalgebra w).toSubmodule (by
        intro p α
        change coefficients (VectorPolynomial.map f.toLinearMap p.val) α ∈ _
        rw [coefficients_map]
        exact hf _ _ (p.property α)) with
    map_lie' {p q} := by
      apply Subtype.ext
      exact (VectorPolynomial.mapLie f).map_lie p.val q.val }

@[simp] theorem filteredPolynomialMap_coe (p : F.adaptedLieSubalgebra w) :
    (F.filteredPolynomialMap G f hf w p : VectorPolynomial σ ℚ M) =
      VectorPolynomial.map f.toLinearMap p.val := rfl

theorem filteredPolynomialMap_mem_shiftedIdeal {p : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.shiftedAdaptedIdeal w) :
    F.filteredPolynomialMap G f hf w p ∈ G.shiftedAdaptedIdeal w := by
  intro α
  change coefficients (VectorPolynomial.map f.toLinearMap p.val) α ∈ _
  rw [coefficients_map]
  exact hf _ _ (hp α)

noncomputable def filteredPolynomialSymbolMap : F.PolynomialSymbol w →ₗ⁅ℚ⁆ G.PolynomialSymbol w :=
  { toLinearMap := (F.shiftedAdaptedIdeal w).toSubmodule.liftQ
      ((G.polynomialSymbolMap w).toLinearMap.comp (F.filteredPolynomialMap G f hf w).toLinearMap) (by
        intro p hp
        exact (lieQuotientMap_eq_zero (G.shiftedAdaptedIdeal w) _).mpr
          (F.filteredPolynomialMap_mem_shiftedIdeal G f hf w hp))
    map_lie' {x y} := by
      obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
      obtain ⟨q, rfl⟩ := F.polynomialSymbolMap_surjective w y
      change G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w ⁅p, q⁆) =
        ⁅G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w p),
          G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w q)⁆
      rw [LieHom.map_lie, LieHom.map_lie] }

@[simp] theorem filteredPolynomialSymbolMap_symbol (p : F.adaptedLieSubalgebra w) :
    F.filteredPolynomialSymbolMap G f hf w (F.polynomialSymbolMap w p) =
      G.polynomialSymbolMap w (F.filteredPolynomialMap G f hf w p) := rfl

noncomputable def associatedGradedMap : F.AssociatedGraded →ₗ⁅ℚ⁆ G.AssociatedGraded :=
  F.filteredPolynomialSymbolMap G f hf (fun _ : Unit => 1)

@[simp] theorem associatedGradedMap_piece (j : ℕ) (x : F.layer j) :
    F.associatedGradedMap G f hf (F.associatedGradedPieceMap j x) =
      G.associatedGradedPieceMap j ⟨f x, hf j x x.property⟩ := by
  change G.polynomialSymbolMap (fun _ : Unit => 1)
    (F.filteredPolynomialMap G f hf (fun _ : Unit => 1) (F.gradedMonomialLinear j x)) = _
  apply congrArg (G.polynomialSymbolMap (fun _ : Unit => 1))
  apply Subtype.ext
  exact VectorPolynomial.map_monomial f.toLinearMap (unitMonomial j) x

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

variable {σ L M : Type*} [LieRing L] [LieAlgebra ℚ L]
  [LieRing M] [LieAlgebra ℚ M] {s t : ℕ}
  (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M t)
  (f : L →ₗ⁅ℚ⁆ M) (hf : ∀ j, ∀ x ∈ F.layer j, f x ∈ G.layer j)
  (w : σ → ℕ)

@[simp] theorem filteredPolynomialMap_coefficient (p : F.adaptedLieSubalgebra w)
    (α : σ →₀ ℕ) :
    coefficients (F.filteredPolynomialMap G f hf w p).val α = f (coefficients p.val α) :=
  coefficients_map f.toLinearMap p.val α

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (w : σ → ℕ)

noncomputable def realAdaptedPolynomialMap :
    (ℝ ⊗[ℚ] F.adaptedLieSubalgebra w) →ₗ⁅ℚ⁆ VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) :=
  VectorPolynomial.realificationLieEquiv.toLieHom.comp
    (LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.adaptedLieSubalgebra w).incl)

@[simp] theorem realAdaptedPolynomialMap_coefficient_tmul
    (a : ℝ) (p : F.adaptedLieSubalgebra w) (α : σ →₀ ℕ) :
    coefficients (F.realAdaptedPolynomialMap w (a ⊗ₜ[ℚ] p)) α =
      a ⊗ₜ[ℚ] coefficients (p : VectorPolynomial σ ℚ L) α := by
  change coefficients (VectorPolynomial.realificationLieEquiv
    (a ⊗ₜ[ℚ] (p : VectorPolynomial σ ℚ L))) α = _
  have hc := coefficients_realificationLieEquiv_tmul a (p : VectorPolynomial σ ℚ L) α
  convert hc using 2

end Erdos3.NilpotentLieFiltration

end

end OAI
end


