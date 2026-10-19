-- Prove2me | Definitions.Def_OAIE3v2B163
-- name    : OAIE3v2B163
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T11:12:28.477981+00:00
-- url     : https://prove2.me/theorems/2bb17f31-81ef-4e03-8f9b-5a4031321b30
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 165 of 311
-- statement:
--   Definitions bundle 165 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B151`, `OAIE3v2B152` of this split.
--
--   Modules: `Estimates/CommonRefilteredFactorization.lean`, `Estimates/ComparisonAmbient.lean`, `Estimates/NativeDilationDescent.lean`, `Estimates/NativeDilationOrbit.lean`, `Estimates/NormalizedComparisonOrbit.lean`, `Estimates/RealPolarizedLogDiagonal.lean`, `Fourier/ControlledReplicatedFrequency.lean`, `Geometry/RealPolarizedCoefficientCoordinates.lean`, `Linear/NativeDilationPairProjections.lean`, `Linear/RankUnadaptedFactorization.lean`, `Linear/RealComparisonCoefficientProjections.lean`, `Polynomial/RealComparisonPolynomialProjections.lean`, `Polynomial/RealPolarizedPolynomialOrbit.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B151
import Definitions.Def_OAIE3v2B152

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ComparisonAmbient
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realSquarefreeLayerMap (a : SquarefreeIndex ι) :
    (F.layer (blockDegree π a.val)).baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :=
  ((F.squarefreeLayerMap π a).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).symm.toLinearMap

theorem realSquarefreeLayerMap_tmul (a : SquarefreeIndex ι) (r : ℝ)
    (v : F.layer (blockDegree π a.val)) :
    F.realSquarefreeLayerMap π a
      (realificationSubmoduleEquiv (F.layer (blockDegree π a.val)) (r ⊗ₜ[ℚ] v)) =
      r ⊗ₜ[ℚ] F.squarefreeLayerMap π a v := by
  simp only [realSquarefreeLayerMap, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem realSquarefreeLayerMap_zero (a : SquarefreeIndex ι) (ha : a.val = 0)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeLayerMap π a v = 0 := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul, F.squarefreeLayerMap_zero π a ha,
      TensorProduct.tmul_zero]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

theorem realSquarefreeLayerMap_mem (a : SquarefreeIndex ι)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeLayerMap π a v ∈
      (F.squarefreeMultidegreeLayer π (fun i => a.val i)).baseChange ℝ := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.squarefreeLayerMap_mem π a x)
  | add x y hx hy =>
    simpa only [map_add] using
      ((F.squarefreeMultidegreeLayer π (fun i => a.val i)).baseChange ℝ).add_mem hx hy

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realBlockCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) : (F.layer (blockDegree π a.val)).baseChange ℝ :=
  ⟨coefficients p.val (blockExponent π a.val), p.property (blockExponent π a.val)⟩

noncomputable def realPolarizedCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) : ℝ ⊗[ℚ] F.SquarefreeAlgebra π :=
  (multidegreeFactorial (blockDegree π a.val) : ℚ) •
    F.realSquarefreeLayerMap π a (F.realBlockCoefficient π p a)

theorem realPolarizedCoefficient_zero (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val = 0) : F.realPolarizedCoefficient π p a = 0 := by
  rw [realPolarizedCoefficient, F.realSquarefreeLayerMap_zero π a ha, smul_zero]

theorem realPolarizedCoefficient_mem (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) :
    F.realPolarizedCoefficient π p a ∈
      (F.squarefreeMultidegreeFiltration π).realification.layer (fun i => a.val i) :=
  ((F.squarefreeMultidegreeFiltration π).realification.layer _).smul_mem _
    (F.realSquarefreeLayerMap_mem π a (F.realBlockCoefficient π p a))

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realSquarefreeInclusion :
    (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) →ₗ[ℝ] (ℝ ⊗[ℚ] SquarefreePolynomial ι L) :=
  (F.squarefreeAdaptedSubalgebra π).toSubmodule.subtype.baseChange ℝ

theorem realSquarefreeInclusion_injective : Function.Injective (F.realSquarefreeInclusion π) :=
  realification_subtype_injective (F.squarefreeAdaptedSubalgebra π).toSubmodule

theorem realSquarefreeInclusion_layerMap (a : SquarefreeIndex ι) (ha : a.val ≠ 0)
    (v : (F.layer (blockDegree π a.val)).baseChange ℝ) :
    F.realSquarefreeInclusion π (F.realSquarefreeLayerMap π a v) =
      (squarefreeMonomial a).baseChange ℝ v.val := by
  obtain ⟨x, rfl⟩ := (realificationSubmoduleEquiv (F.layer (blockDegree π a.val))).surjective v
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    rw [F.realSquarefreeLayerMap_tmul]
    change r ⊗ₜ[ℚ] (F.squarefreeLayerMap π a x).val = r ⊗ₜ[ℚ] squarefreeMonomial a x.val
    rw [F.squarefreeLayerMap_coe π a ha]
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy

theorem realSquarefreeInclusion_permute (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i)
    (x : ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :
    F.realSquarefreeInclusion π ((F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ x) =
      (squarefreePermute (L := L) e).toLinearMap.baseChange ℝ (F.realSquarefreeInclusion π x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]

theorem realSquarefreePermute_monomial (e : Equiv.Perm ι) (a : SquarefreeIndex ι)
    (x : ℝ ⊗[ℚ] L) :
    (squarefreePermute (L := L) e).toLinearMap.baseChange ℝ
        ((squarefreeMonomial a).baseChange ℝ x) =
      (squarefreeMonomial (SquarefreeIndex.permute e a)).baseChange ℝ x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r x =>
    simp only [LinearMap.baseChange_tmul, LinearEquiv.coe_coe, squarefreePermute_monomial]
  | add x y hx hy => simp only [map_add, hx, hy]

namespace MultidegreeLieFiltration

variable {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedCoefficient_inclusion (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val ≠ 0) :
    F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a) =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        (squarefreeMonomial a).baseChange ℝ (coefficients p.val (blockExponent π a.val)) := by
  rw [realPolarizedCoefficient, LinearMap.map_smul_of_tower,
    F.realSquarefreeInclusion_layerMap π a ha]
  rfl

theorem realPolarizedCoefficient_permute (p : F.realification.adaptedLieSubalgebra)
    (e : Equiv.Perm ι) (he : ∀ i, π (e i) = π i) (a : SquarefreeIndex ι) :
    (F.squarefreeBlockPermute π e he).toLinearMap.baseChange ℝ (F.realPolarizedCoefficient π p a) =
      F.realPolarizedCoefficient π p (SquarefreeIndex.permute e a) := by
  by_cases ha : a.val = 0
  · rw [F.realPolarizedCoefficient_zero π p a ha,
      F.realPolarizedCoefficient_zero π p _ ((SquarefreeIndex.permute_zero_iff e a).mpr ha),
      map_zero]
  · have hea : (SquarefreeIndex.permute e a).val ≠ 0 :=
      fun h => ha ((SquarefreeIndex.permute_zero_iff e a).mp h)
    apply F.realSquarefreeInclusion_injective π
    rw [F.realSquarefreeInclusion_permute, F.realPolarizedCoefficient_inclusion π p a ha,
      F.realPolarizedCoefficient_inclusion π p _ hea, LinearMap.map_smul_of_tower,
      realSquarefreePermute_monomial, SquarefreeIndex.permute_blockDegree π e he a,
      blockExponent_permute π e he a]

end MultidegreeLieFiltration
end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonSubalgebra : LieSubalgebra ℚ (L × F.SquarefreeAlgebra π) :=
  { F.comparisonLayer π 1 with
    lie_mem' := fun hx hy => F.comparisonLayer_antitone π (by decide : 1 ≤ 1 + 1)
      (F.comparisonLayer_lie_mem π hx hy) }

noncomputable def comparisonFiltration :
    NilpotentLieFiltration (F.comparisonSubalgebra π) (max s (Fintype.card ι)) where
  layer n := (F.comparisonLayer π n).comap (F.comparisonSubalgebra π).incl.toLinearMap
  antitone := fun _ _ h _ hx => F.comparisonLayer_antitone π h hx
  one_eq_top := by
    apply top_unique
    intro x _
    exact x.property
  lie_mem := fun hx hy => F.comparisonLayer_lie_mem π hx hy
  terminal := by
    apply bot_unique
    intro x hx
    change x = 0
    apply Subtype.ext
    change x.val = (0 : L × F.SquarefreeAlgebra π)
    have h : x.val ∈ F.comparisonLayer π (max s (Fintype.card ι) + 1) := hx
    simpa only [F.comparisonLayer_terminal, Submodule.mem_bot] using h

noncomputable def comparisonFirst : F.comparisonSubalgebra π →ₗ⁅ℚ⁆ L :=
  (LieHom.fst ℚ L (F.SquarefreeAlgebra π)).comp (F.comparisonSubalgebra π).incl

noncomputable def comparisonSecond : F.comparisonSubalgebra π →ₗ⁅ℚ⁆ F.SquarefreeAlgebra π :=
  (LieHom.snd ℚ L (F.SquarefreeAlgebra π)).comp (F.comparisonSubalgebra π).incl

theorem comparisonFirst_mem_layer (n : ℕ) {x : F.comparisonSubalgebra π}
    (hx : x ∈ (F.comparisonFiltration π).layer n) : F.comparisonFirst π x ∈ F.ordinary.layer n :=
  (F.comparisonLayer_le_product π n hx).1

theorem comparisonSecond_mem_layer (n : ℕ) {x : F.comparisonSubalgebra π}
    (hx : x ∈ (F.comparisonFiltration π).layer n) :
    F.comparisonSecond π x ∈ F.squarefreeDegreeLayer π n :=
  (F.comparisonLayer_le_product π n hx).2

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonGraphLift (a : σ → ℕ) (ha : a ≠ 0) :
    F.layer a →ₗ[ℚ] F.comparisonSubalgebra π where
  toFun x := ⟨F.comparisonGraph π a ha x, F.comparisonGraph_mem_layer π 1 a ha (by
    by_contra h
    have hs : (∑ i, a i) = 0 := by omega
    apply ha
    funext i
    change a i = 0
    exact (Finset.sum_eq_zero_iff.mp hs) i (Finset.mem_univ i)) x⟩
  map_add' x y := Subtype.ext (map_add (F.comparisonGraph π a ha) x y)
  map_smul' r x := Subtype.ext (map_smul (F.comparisonGraph π a ha) r x)

theorem comparisonGraphLift_first (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonFirst π (F.comparisonGraphLift π a ha x) = x.val := rfl

theorem comparisonGraphLift_second (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonSecond π (F.comparisonGraphLift π a ha x) = F.blockLayerMap π a ha x := rfl

theorem comparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0) (x : F.layer a) :
    F.comparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).layer (∑ i, a i) :=
  F.comparisonGraph_mem_layer π _ a ha le_rfl x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def comparisonFiltrationLayerEquiv (n : ℕ) (hn : 1 ≤ n) :
    (F.comparisonFiltration π).layer n ≃ₗ[ℚ] F.comparisonLayer π n where
  toFun x := ⟨x.val.val, x.property⟩
  invFun x := ⟨⟨x.val, F.comparisonLayer_antitone π hn x.property⟩, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonGraphLift (a : σ → ℕ) (ha : a ≠ 0) :
    (F.layer a).baseChange ℝ →ₗ[ℝ] (ℝ ⊗[ℚ] F.comparisonSubalgebra π) :=
  ((F.comparisonGraphLift π a ha).baseChange ℝ).comp
    (realificationSubmoduleEquiv (F.layer a)).symm.toLinearMap

theorem realComparisonGraphLift_tmul (a : σ → ℕ) (ha : a ≠ 0) (r : ℝ) (x : F.layer a) :
    F.realComparisonGraphLift π a ha (realificationSubmoduleEquiv (F.layer a) (r ⊗ₜ[ℚ] x)) =
      r ⊗ₜ[ℚ] F.comparisonGraphLift π a ha x := by
  simp only [realComparisonGraphLift, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, LinearMap.baseChange_tmul]

theorem realComparisonGraphLift_first (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonGraphLift π a ha x) = x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul, realificationLieHom_tmul, F.comparisonGraphLift_first]
    rfl
  | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

theorem realComparisonGraphLift_second (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonGraphLift π a ha x)) =
      (factorialBlockMonomial π a).baseChange ℝ x.val := by
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul, realificationLieHom_tmul, F.comparisonGraphLift_second]
    change r ⊗ₜ[ℚ] (F.blockLayerMap π a ha y).val = r ⊗ₜ[ℚ] factorialBlockMonomial π a y.val
    rw [F.blockLayerMap_coe]
  | add y z hy hz => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hy hz

theorem realComparisonGraphLift_mem_degree (a : σ → ℕ) (ha : a ≠ 0)
    (x : (F.layer a).baseChange ℝ) :
    F.realComparisonGraphLift π a ha x ∈ (F.comparisonFiltration π).realification.layer (∑ i, a i) := by
  change F.realComparisonGraphLift π a ha x ∈ ((F.comparisonFiltration π).layer (∑ i, a i)).baseChange ℝ
  obtain ⟨y, rfl⟩ := (realificationSubmoduleEquiv (F.layer a)).surjective x
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r y =>
    rw [F.realComparisonGraphLift_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem r (F.comparisonGraphLift_mem_degree π a ha y)
  | add y z hy hz =>
    simpa only [map_add] using (((F.comparisonFiltration π).layer (∑ i, a i)).baseChange ℝ).add_mem hy hz

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonCoefficient (p : F.realification.adaptedLieSubalgebra)
    (a : σ →₀ ℕ) : ℝ ⊗[ℚ] F.comparisonSubalgebra π := by
  classical
  exact if ha : a = 0 then 0 else
    F.realComparisonGraphLift π (fun i => a i)
      (fun h => ha (Finsupp.ext fun i => congrFun h i))
      ⟨coefficients p.val a, p.property a⟩

theorem realComparisonCoefficient_zero_index (p : F.realification.adaptedLieSubalgebra) :
    F.realComparisonCoefficient π p 0 = 0 := by
  simp [realComparisonCoefficient]

theorem realComparisonCoefficient_zero_value (p : F.realification.adaptedLieSubalgebra)
    (a : σ →₀ ℕ) (h : coefficients p.val a = 0) : F.realComparisonCoefficient π p a = 0 := by
  by_cases ha : a = 0
  · subst a
    exact F.realComparisonCoefficient_zero_index π p
  · rw [realComparisonCoefficient, dif_neg ha]
    have hz : (⟨coefficients p.val a, p.property a⟩ :
        (F.layer (fun i => a i)).baseChange ℝ) = 0 := Subtype.ext h
    rw [hz, map_zero]

theorem realComparisonCoefficient_mem (p : F.realification.adaptedLieSubalgebra) (a : σ →₀ ℕ) :
    F.realComparisonCoefficient π p a ∈
      (F.comparisonFiltration π).realification.layer (Finsupp.weight (fun _ => 1) a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index]
    exact Submodule.zero_mem _
  · rw [realComparisonCoefficient, dif_neg ha]
    have h := F.realComparisonGraphLift_mem_degree π (fun i => a i)
      (fun h => ha (Finsupp.ext fun i => congrFun h i))
      ⟨coefficients p.val a, p.property a⟩
    simpa only [Finsupp.weight_eq_sum, smul_eq_mul, mul_one] using h

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem comparisonFirst_real_mem_layer (n : ℕ) (x : ℝ ⊗[ℚ] F.comparisonSubalgebra π)
    (hx : x ∈ (F.comparisonFiltration π).realification.layer n) :
    realificationLieHom (F.comparisonFirst π) x ∈ F.ordinary.realification.layer n :=
  (F.comparisonFiltration π).realificationLieHom_mem_layer F.ordinary (F.comparisonFirst π)
    (fun j _ hj => F.comparisonFirst_mem_layer π j hj) n x hx

theorem comparisonSecond_real_mem_layer (n : ℕ) (x : ℝ ⊗[ℚ] F.comparisonSubalgebra π)
    (hx : x ∈ (F.comparisonFiltration π).realification.layer n) :
    realificationLieHom (F.comparisonSecond π) x ∈
      (F.squarefreeOrdinaryFiltration π).realification.layer n :=
  (F.comparisonFiltration π).realificationLieHom_mem_layer (F.squarefreeOrdinaryFiltration π)
    (F.comparisonSecond π) (fun j _ hj => F.comparisonSecond_mem_layer π j hj) n x hx

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.ControlledReplicatedFrequency
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open Module

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def replicatedFrequency (η : L →ₗ[ℚ] ℚ) :
    F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1) →ₗ[ℚ] ℚ :=
  η.comp ((F.layer bound).subtype.comp F.replicatedTopCoefficient)

theorem replicatedFrequency_apply (η : L →ₗ[ℚ] ℚ)
    (x : F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)) :
    F.replicatedFrequency η x =
      η (squarefreePolynomialEquiv x.val (SquarefreeIndex.full (ReplicatedIndex bound))) := rfl

variable {κ : SquarefreeIndex (ReplicatedIndex bound) → Type*}
  (b : ∀ a, Basis (κ a) ℚ (F.squarefreeCoefficientLayer (fun j : ReplicatedIndex bound => j.1) a))

theorem replicatedFrequency_basis_full (η : L →ₗ[ℚ] ℚ)
    (j : κ (SquarefreeIndex.full (ReplicatedIndex bound))) :
    F.replicatedFrequency η
        (F.squarefreeBasis (fun j : ReplicatedIndex bound => j.1) b ⟨SquarefreeIndex.full _, j⟩) =
      η (b (SquarefreeIndex.full _) j).val := by
  rw [F.replicatedFrequency_apply, F.squarefreeBasis_coefficient_self]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem replicatedTopCoefficient_blockLayerMap (hb : bound ≠ 0) (x : F.layer bound) :
    F.replicatedTopCoefficient (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) bound hb x) =
      (multidegreeFactorial bound : ℚ) • x := by
  classical
  apply Subtype.ext
  rw [F.replicatedTopCoefficient_apply, F.blockLayerMap_coe,
    factorialBlockMonomial_coefficient, replicated_blockDegree_full, if_pos rfl]
  rfl

theorem replicatedFrequency_blockLayerMap_top (η : L →ₗ[ℚ] ℚ)
    (hb : bound ≠ 0) (x : F.layer bound) :
    F.replicatedFrequency η (F.blockLayerMap (fun j : ReplicatedIndex bound => j.1) bound hb x) =
      (multidegreeFactorial bound : ℚ) * η x.val := by
  change η (F.replicatedTopCoefficient (F.blockLayerMap _ bound hb x)).val = _
  rw [F.replicatedTopCoefficient_blockLayerMap hb x]
  exact map_smul η _ x.val

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open scoped BigOperators

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem comparisonLayer_top_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : L × F.SquarefreeAlgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ F.comparisonLayer (fun j : ReplicatedIndex bound => j.1) s) :
    (multidegreeFactorial bound : ℚ) * η z.1 = F.replicatedFrequency η z.2 := by
  have hterminal : F.comparisonProductLayer (fun j : ReplicatedIndex bound => j.1) (s + 1) = ⊥ := by
    have h := F.comparisonProductLayer_terminal (fun j : ReplicatedIndex bound => j.1)
    simpa only [replicatedIndex_card, ← hstep, max_self] using h
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hz
  have hu0 : u = 0 := by simpa only [hterminal, Submodule.mem_bot] using hu
  rw [hu0, zero_add]
  refine F.comparisonGraphLayer_induction (fun j : ReplicatedIndex bound => j.1) s
    (P := fun z => (multidegreeFactorial bound : ℚ) * η z.1 = F.replicatedFrequency η z.2) hv ?_ ?_ ?_
  · intro a ha hsa x
    by_cases hab : a ≤ bound
    · have heq : a = bound := by
        funext i
        apply le_antisymm (hab i)
        by_contra hi
        have hlt : a i < bound i := Nat.lt_of_not_ge hi
        have hsum : (∑ j, a j) < ∑ j, bound j :=
          Finset.sum_lt_sum (fun j _ => hab j) ⟨i, Finset.mem_univ i, hlt⟩
        omega
      subst a
      exact (F.replicatedFrequency_blockLayerMap_top η ha x).symm
    · have hx0 : x = 0 := by
        apply Subtype.ext
        have h : x.val ∈ (⊥ : Submodule ℚ L) := F.terminal a hab ▸ x.property
        exact (Submodule.mem_bot ℚ).mp h
      rw [hx0, map_zero]
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero]
  · simp only [Prod.fst_zero, Prod.snd_zero, map_zero, mul_zero]
  · intro x y hx hy
    change (multidegreeFactorial bound : ℚ) * η (x.1 + y.1) = F.replicatedFrequency η (x.2 + y.2)
    rw [map_add, map_add, mul_add, hx, hy]

theorem comparisonTop_frequency (hstep : s = ∑ i, bound i) (η : L →ₗ[ℚ] ℚ)
    {z : F.comparisonSubalgebra (fun j : ReplicatedIndex bound => j.1)}
    (hz : z ∈ (F.comparisonFiltration (fun j : ReplicatedIndex bound => j.1)).layer s) :
    (multidegreeFactorial bound : ℚ) * η (F.comparisonFirst (fun j : ReplicatedIndex bound => j.1) z) =
      F.replicatedFrequency η (F.comparisonSecond (fun j : ReplicatedIndex bound => j.1) z) :=
  F.comparisonLayer_top_frequency hstep η hz

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonRefilteredFactorization
namespace OAI

section

namespace Erdos3

open Module

namespace MultidegreeLieFiltration

variable {σ L : Type*} [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def weightedLayerEquiv (c : σ → ℕ) (n : ℕ) (hn : 1 ≤ n) :
    (F.weightedFiltration c).layer n ≃ₗ[ℚ] F.weightedLayer c n where
  toFun x := ⟨x.val.val, (F.mem_weightedFiltration_layer c n hn x.val).mp x.property⟩
  invFun x := ⟨⟨x.val, F.weightedLayer_antitone c hn x.property⟩,
    (F.mem_weightedFiltration_layer c n hn _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem exists_weighted_layer_coordinate_basis {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : σ → ℕ) (e : Basis ι ℚ L) (b : Basis κ ℚ (F.weightedSubalgebra c))
    (n : ℕ) (hn : 1 ≤ n)
    (a : Basis (Fin (finrank ℚ (F.weightedLayer c n))) ℚ (F.weightedLayer c n))
    {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i k, RationalHeightLE (e.repr (b i : L) k) H)
    (ha : ∀ i k, RationalHeightLE (e.repr (a i : L) k) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p) :
    ∃ a' : Basis (Fin (finrank ℚ ((F.weightedFiltration c).layer n))) ℚ
        ((F.weightedFiltration c).layer n),
      ∀ i k, rationalLogHeight (b.repr (a' i : F.weightedSubalgebra c) k) ≤ (p + 2) ^ 8 := by
  let E := F.weightedLayerEquiv c n hn
  let a' := (a.map E.symm).reindex (finCongr E.finrank_eq.symm)
  have hval (i) : ((a' i : F.weightedSubalgebra c) : L) =
      (a ((finCongr E.finrank_eq.symm).symm i) : L) := by
    simp only [a', Basis.reindex_apply, Basis.map_apply, E, weightedLayerEquiv]
    rfl
  refine ⟨a', fun i k => ?_⟩
  apply rationalLogHeight_le_of_height
    (embedding_basis_coordinate_height b e (F.weightedSubalgebra c).incl.toLinearMap
      (fun _ _ h => Subtype.ext h) hH (fun k i => hb i k)
      (a' i : F.weightedSubalgebra c) (K := H) (fun k => by
        change RationalHeightLE (e.repr ((a' i : F.weightedSubalgebra c) : L) k) H
        rw [hval]
        exact ha _ k) k)
  exact embedding_coordinate_height_budget _ _ H H hp hι hκ hHp hHp

end MultidegreeLieFiltration

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeDilationPairProjections
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

noncomputable def realDilationPairProjection (q : ℚ) (j : Fin 2) :
    (F.dilationPairFiltration q).realification.Group →* F.realification.Group :=
  NilpotentLieBCHGroup.realificationMap
    (hnil := (F.dilationPairFiltration q).lowerCentralSeries_eq_bot)
    (hM := F.lowerCentralSeries_eq_bot) (F.dilationPairProjection q j)

theorem realifiedDilationPairEquiv_projection (q : ℚ) (j : Fin 2)
    (x : ℝ ⊗[ℚ] F.dilationPairSubalgebra q) :
    pairToPi (F.realifiedDilationPairEquiv q x).val j =
      realificationLieHom (F.dilationPairProjection q j) x := by
  rw [F.realifiedDilationPairEquiv_coe]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul scalar vector =>
    rw [realificationLieHom_tmul, realPairEquiv_tmul, realificationLieHom_tmul]
    fin_cases j <;> rfl
  | add first second hfirst hsecond =>
    simp only [map_add, Pi.add_apply, hfirst, hsecond]

theorem realDilationPairProjection_coord (q : ℚ) (j : Fin 2)
    (g : (F.dilationPairFiltration q).realification.Group) :
    (F.realDilationPairProjection q j g).coord =
      pairToPi (F.realifiedDilationPairEquiv q g.coord).val j :=
  (F.realifiedDilationPairEquiv_projection q j g.coord).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

theorem realifiedDilationPairPolynomial_adapted (q : ℚ)
    (p : VectorPolynomial σ ℚ (F.ordinary.realification.dilationPairSubalgebra q))
    (hp : (F.realification.dilationPairMultidegree q).Adapted p) :
    (F.dilationPairMultidegree q).realification.Adapted
      (VectorPolynomial.map (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap p) := by
  intro a
  rw [coefficients_map]
  exact (F.realifiedDilationPairEquiv_symm_mem_multidegree q _ _).mpr (hp a)

noncomputable def realifiedDilationPairOrbit (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit) :
    (F.dilationPairMultidegree q).realification.PolynomialOrbit :=
  (F.dilationPairMultidegree q).realification.polynomialOrbitOfLog
    (VectorPolynomial.map (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap
      (p.log (F.realification.dilationPairMultidegree q)))
    (F.realifiedDilationPairPolynomial_adapted q _ (p.adapted _))

theorem realifiedDilationPairOrbit_eval (q : ℚ)
    (p : (F.realification.dilationPairMultidegree q).PolynomialOrbit) (x : σ → ℤ) :
    F.ordinary.realifiedDilationPairEquiv q
      (((F.dilationPairMultidegree q).realification.polynomialOrbitEval x
        (F.realifiedDilationPairOrbit q p)).coord) =
      ((F.realification.dilationPairMultidegree q).polynomialOrbitEval x p).coord := by
  change F.ordinary.realifiedDilationPairEquiv q
    (eval (fun j => (x j : ℚ)) (VectorPolynomial.map
      (F.ordinary.realifiedDilationPairEquiv q).symm.toLinearMap
        (p.log (F.realification.dilationPairMultidegree q)))) = _
  rw [eval_map]
  exact (F.ordinary.realifiedDilationPairEquiv q).apply_symm_apply _

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeDilationDescent
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound)

noncomputable def realifiedAdditiveTripleOrbit {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v) :
    (F.additiveTripleFiltration i hi c hc).realification.PolynomialOrbit v :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (VectorPolynomial.map (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap q.log)
    ((F.realification.additiveTripleFiltration i hi c hc).adapted_map
      (F.additiveTripleFiltration i hi c hc).realification
      (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap
      (fun n x hx => (F.realifiedAdditiveTripleEquiv_symm_mem_layer i hi c hc n x).mpr hx) v q.adapted)

theorem realifiedAdditiveTripleOrbit_eval {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v) (x : τ → ℤ) :
    F.realifiedAdditiveTripleEquiv i hi c hc
      (((F.additiveTripleFiltration i hi c hc).realification.polynomialOrbitEval v x
        (F.realifiedAdditiveTripleOrbit i hi c hc q)).coord) =
      ((F.realification.additiveTripleFiltration i hi c hc).polynomialOrbitEval v x q).coord := by
  change F.realifiedAdditiveTripleEquiv i hi c hc
    (eval (fun j => (x j : ℚ)) (VectorPolynomial.map
      (F.realifiedAdditiveTripleEquiv i hi c hc).symm.toLinearMap q.log)) = _
  rw [eval_map]
  exact (F.realifiedAdditiveTripleEquiv i hi c hc).apply_symm_apply _

theorem realifiedAdditiveTripleOrbit_zero {τ : Type*} (i : σ) (hi : bound i ≤ 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1) {v : τ → ℕ}
    (q : (F.realification.additiveTripleFiltration i hi c hc).PolynomialOrbit v)
    (hq : (F.realification.additiveTripleFiltration i hi c hc).polynomialOrbitEval v 0 q = 1) :
    (F.additiveTripleFiltration i hi c hc).realification.polynomialOrbitEval v 0
      (F.realifiedAdditiveTripleOrbit i hi c hc q) = 1 := by
  apply NilpotentLieBCHGroup.ext
  apply (F.realifiedAdditiveTripleEquiv i hi c hc).injective
  rw [F.realifiedAdditiveTripleOrbit_eval, hq]
  exact (map_zero _).symm

theorem exists_real_normalized_addition_orbit (i : σ) (hi : bound i ≤ 1)
    (p : F.realification.PolynomialOrbit) (a b : F.realification.Group)
    (hp0 : F.realification.polynomialOrbitEval 0 p = a * b) :
    ∃ g : (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).realification.PolynomialOrbit (fun _ : Option σ => 1),
      (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
        (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ 0 g = 1 ∧
      ∀ x : Option σ → ℤ,
        let h := (F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
          (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ x g
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 0 h =
          a⁻¹ * F.realification.polynomialOrbitEval
            (Function.update (fun j => x (some j)) i (x (some i) + x none)) p * b⁻¹ ∧
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 1 h =
          a⁻¹ * F.realification.polynomialOrbitEval (fun j => x (some j)) p * b⁻¹ ∧
        F.realAdditiveTripleProjection i hi _ (omittedCoordinateWeight_le_one i) 2 h =
          a⁻¹ * F.realification.polynomialOrbitEval
            (Function.update (fun j => x (some j)) i (x none)) p * b⁻¹ := by
  obtain ⟨q, hq0, hq⟩ := F.realification.exists_normalizedCoordinateAddition_orbit i hi p a b hp0
  refine ⟨F.realifiedAdditiveTripleOrbit i hi _ (omittedCoordinateWeight_le_one i) q,
    F.realifiedAdditiveTripleOrbit_zero i hi _ (omittedCoordinateWeight_le_one i) q hq0, ?_⟩
  intro x
  dsimp only
  have he (j : Fin 3) := F.realAdditiveTripleProjection_coord i hi _
    (omittedCoordinateWeight_le_one i) j
    ((F.additiveTripleFiltration i hi (omittedCoordinateWeight i)
      (omittedCoordinateWeight_le_one i)).realification.polynomialOrbitEval _ x
      (F.realifiedAdditiveTripleOrbit i hi _ (omittedCoordinateWeight_le_one i) q))
  simp only [F.realifiedAdditiveTripleOrbit_eval, hq x] at he
  exact ⟨NilpotentLieBCHGroup.ext (he 0), NilpotentLieBCHGroup.ext (he 1),
    NilpotentLieBCHGroup.ext (he 2)⟩

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealPolarizedPolynomialOrbit
namespace OAI

section

namespace Erdos3

open VectorPolynomial
open scoped BigOperators

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℚ V]

noncomputable def squarefreePolynomialLift (f : SquarefreeIndex ι → V) : VectorPolynomial ι ℚ V :=
  ∑ a, monomial a.val (f a)

theorem squarefreePolynomialLift_coefficient (f : SquarefreeIndex ι → V) (a : SquarefreeIndex ι) :
    coefficients (squarefreePolynomialLift f) a.val = f a := by
  classical
  simp only [squarefreePolynomialLift, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · simp only [coefficients_monomial, Finsupp.single_eq_same]
  · intro b _ hb
    rw [coefficients_monomial]
    exact Finsupp.single_eq_of_ne (fun h => hb (Subtype.ext h.symm))
  · simp

theorem squarefreePolynomialLift_coefficient_nonsquarefree (f : SquarefreeIndex ι → V)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) : coefficients (squarefreePolynomialLift f) a = 0 := by
  classical
  simp only [squarefreePolynomialLift, map_sum, Finsupp.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro b _
  rw [coefficients_monomial]
  apply Finsupp.single_eq_of_ne
  intro h
  apply ha
  rw [h]
  exact b.property

theorem squarefreePolynomialLift_eval (f : SquarefreeIndex ι → V) (x : ι → ℚ) :
    eval x (squarefreePolynomialLift f) = ∑ a, (a.val.prod fun i n => x i ^ n) • f a := by
  simp only [squarefreePolynomialLift, map_sum, eval_monomial]

end Erdos3

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realPolarizedLog (p : F.realification.adaptedLieSubalgebra) :
    VectorPolynomial ι ℚ (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) :=
  squarefreePolynomialLift (F.realPolarizedCoefficient π p)

theorem realPolarizedLog_coefficient (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) :
    coefficients (F.realPolarizedLog π p) a.val = F.realPolarizedCoefficient π p a :=
  squarefreePolynomialLift_coefficient _ a

theorem realPolarizedLog_coefficient_nonsquarefree (p : F.realification.adaptedLieSubalgebra)
    (a : ι →₀ ℕ) (ha : ¬SquarefreeExponent a) :
    coefficients (F.realPolarizedLog π p) a = 0 :=
  squarefreePolynomialLift_coefficient_nonsquarefree _ a ha

theorem realPolarizedLog_adapted (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.Adapted (F.realPolarizedLog π p) := by
  intro a
  by_cases ha : SquarefreeExponent a
  · rw [F.realPolarizedLog_coefficient π p ⟨a, ha⟩]
    exact F.realPolarizedCoefficient_mem π p ⟨a, ha⟩
  · rw [F.realPolarizedLog_coefficient_nonsquarefree π p a ha]
    exact Submodule.zero_mem _

theorem realPolarizedLog_eval (p : F.realification.adaptedLieSubalgebra) (x : ι → ℚ) :
    eval x (F.realPolarizedLog π p) =
      ∑ a, (a.val.prod fun i n => x i ^ n) • F.realPolarizedCoefficient π p a :=
  squarefreePolynomialLift_eval _ x

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realPolarizedOrbit (p : F.realification.adaptedLieSubalgebra) :
    (F.squarefreeMultidegreeFiltration π).realification.PolynomialOrbit :=
  (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitOfLog
    (F.realPolarizedLog π p) (F.realPolarizedLog_adapted π p)

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.RealPolarizedCoefficientCoordinates
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedCoefficient_self (p : F.realification.adaptedLieSubalgebra)
    (a : SquarefreeIndex ι) (ha : a.val ≠ 0) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a)) a =
      (multidegreeFactorial (blockDegree π a.val) : ℚ) •
        coefficients p.val (blockExponent π a.val) := by
  rw [F.realPolarizedCoefficient_inclusion π p a ha, map_rat_smul, Pi.smul_apply,
    realSquarefreeMonomial_self]

theorem realPolarizedCoefficient_ne (p : F.realification.adaptedLieSubalgebra)
    (a c : SquarefreeIndex ι) (hac : a ≠ c) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p a)) c = 0 := by
  by_cases ha : a.val = 0
  · rw [F.realPolarizedCoefficient_zero π p a ha, map_zero, map_zero, Pi.zero_apply]
  · rw [F.realPolarizedCoefficient_inclusion π p a ha, map_rat_smul, Pi.smul_apply,
      realSquarefreeMonomial_ne a c hac, smul_zero]

theorem realPolarizedLog_eval_coefficient (p : F.realification.adaptedLieSubalgebra)
    (x : ι → ℚ) (c : SquarefreeIndex ι) :
    realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (eval x (F.realPolarizedLog π p))) c =
      (c.val.prod fun i n => x i ^ n) •
        realSquarefreePolynomialEquiv (F.realSquarefreeInclusion π (F.realPolarizedCoefficient π p c)) c := by
  classical
  let C : (ℝ ⊗[ℚ] F.SquarefreeAlgebra π) →ₗ[ℝ] (ℝ ⊗[ℚ] L) := (LinearMap.proj c).comp
    (realSquarefreePolynomialEquiv.toLinearMap.comp (F.realSquarefreeInclusion π))
  change C (eval x (F.realPolarizedLog π p)) = _
  rw [F.realPolarizedLog_eval, map_sum]
  simp only [LinearMap.map_smul_of_tower]
  rw [Finset.sum_eq_single c]
  · rfl
  · intro a _ hac
    have hz : C (F.realPolarizedCoefficient π p a) = 0 := F.realPolarizedCoefficient_ne π p a c hac
    rw [hz, smul_zero]
  · simp

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealPolarizedLogDiagonal
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realPolarizedLog_diagonal (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    F.realSquarefreeInclusion π (eval (fun j => x (π j)) (F.realPolarizedLog π p)) =
      realBlockPolynomialEval π p.val x := by
  apply realSquarefreePolynomialEquiv.injective
  ext c
  rw [F.realPolarizedLog_eval_coefficient, realBlockPolynomialEval_coefficient,
    blockExponent_weight π c.val x]
  by_cases hc : c.val = 0
  · rw [F.realPolarizedCoefficient_zero π p c hc, map_zero, map_zero, Pi.zero_apply]
    simp only [smul_zero, hc, blockExponent_zero, hp]
  · rw [F.realPolarizedCoefficient_self π p c hc]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealComparisonCoefficientProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonCoefficient_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    realificationLieHom (F.comparisonFirst π) (F.realComparisonCoefficient π p a) =
      coefficients p.val a := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, hp]
  · rw [realComparisonCoefficient, dif_neg ha, F.realComparisonGraphLift_first]

theorem realComparisonCoefficient_second (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (a : σ →₀ ℕ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (F.realComparisonCoefficient π p a)) =
      (factorialBlockMonomial π (fun i => a i)).baseChange ℝ (coefficients p.val a) := by
  by_cases ha : a = 0
  · subst a
    rw [F.realComparisonCoefficient_zero_index, map_zero, map_zero, hp, map_zero]
  · rw [realComparisonCoefficient, dif_neg ha, F.realComparisonGraphLift_second]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealComparisonPolynomialProjections
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial
open scoped TensorProduct BigOperators

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def realComparisonLog (p : F.realification.adaptedLieSubalgebra) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] F.comparisonSubalgebra π) :=
  ∑ a ∈ (coefficients p.val).support, monomial a (F.realComparisonCoefficient π p a)

theorem realComparisonLog_coefficient (p : F.realification.adaptedLieSubalgebra) (a : σ →₀ ℕ) :
    coefficients (F.realComparisonLog π p) a = F.realComparisonCoefficient π p a := by
  classical
  simp only [realComparisonLog, map_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single a]
  · rw [coefficients_monomial, Finsupp.single_eq_same]
  · intro b _ hba
    rw [coefficients_monomial]
    exact Finsupp.single_eq_of_ne (Ne.symm hba)
  · intro ha
    rw [coefficients_monomial, Finsupp.single_eq_same]
    exact F.realComparisonCoefficient_zero_value π p a (Finsupp.notMem_support_iff.mp ha)

theorem realComparisonLog_adapted (p : F.realification.adaptedLieSubalgebra) :
    (F.comparisonFiltration π).realification.Adapted (fun _ => 1) (F.realComparisonLog π p) := by
  apply ((F.comparisonFiltration π).realification.adapted_iff_coefficients _ _).mpr
  intro a
  rw [F.realComparisonLog_coefficient]
  exact F.realComparisonCoefficient_mem π p a

theorem realComparisonLog_eval (p : F.realification.adaptedLieSubalgebra) (x : σ → ℚ) :
    eval x (F.realComparisonLog π p) =
      ∑ a ∈ (coefficients p.val).support,
        (a.prod fun i n => x i ^ n) • F.realComparisonCoefficient π p a := by
  simp only [realComparisonLog, map_sum, eval_monomial]

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

theorem realComparisonLog_first (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) :
    VectorPolynomial.map ((realificationLieHom (F.comparisonFirst π)).toLinearMap.restrictScalars ℚ)
      (F.realComparisonLog π p) = p.val := by
  apply coefficients.injective
  ext a
  rw [coefficients_map, F.realComparisonLog_coefficient]
  exact F.realComparisonCoefficient_first π p hp a

theorem realComparisonLog_first_eval (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    realificationLieHom (F.comparisonFirst π) (eval x (F.realComparisonLog π p)) = eval x p.val := by
  change ((realificationLieHom (F.comparisonFirst π)).toLinearMap.restrictScalars ℚ)
    (eval x (F.realComparisonLog π p)) = _
  rw [← eval_map, F.realComparisonLog_first π p hp]

theorem realComparisonLog_second_ambient (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    F.realSquarefreeInclusion π
        (realificationLieHom (F.comparisonSecond π) (eval x (F.realComparisonLog π p))) =
      realBlockPolynomialEval π p.val x := by
  rw [F.realComparisonLog_eval]
  simp only [map_sum, map_rat_smul, F.realComparisonCoefficient_second π p hp]
  rfl

theorem realComparisonLog_second_eval (p : F.realification.adaptedLieSubalgebra)
    (hp : coefficients p.val 0 = 0) (x : σ → ℚ) :
    realificationLieHom (F.comparisonSecond π) (eval x (F.realComparisonLog π p)) =
      eval (fun j => x (π j)) (F.realPolarizedLog π p) := by
  apply F.realSquarefreeInclusion_injective π
  rw [F.realComparisonLog_second_ambient π p hp, F.realPolarizedLog_diagonal π p hp]

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NormalizedComparisonOrbit
namespace OAI

section

namespace Erdos3.MultidegreeLieFiltration

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def polarizeRealOrbit (p : F.realification.PolynomialOrbit) :
    (F.squarefreeMultidegreeFiltration π).realification.PolynomialOrbit :=
  F.realPolarizedOrbit π
    ⟨PolynomialOrbit.log F.realification p, PolynomialOrbit.adapted F.realification p⟩

end Erdos3.MultidegreeLieFiltration

end

section

namespace Erdos3.MultidegreeLieFiltration

open VectorPolynomial

variable {ι σ L : Type*} [Fintype ι] [Fintype σ] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {bound : σ → ℕ} (F : MultidegreeLieFiltration σ L s bound) (π : ι → σ)

noncomputable def compareRealOrbit (p : F.realification.PolynomialOrbit) :
    (F.comparisonFiltration π).realification.PolynomialOrbit (fun _ : σ => 1) :=
  NilpotentLieFiltration.polynomialOrbitOfLog
    (F := (F.comparisonFiltration π).realification)
    (F.realComparisonLog π ⟨p.log F.realification, p.adapted F.realification⟩)
    (F.realComparisonLog_adapted π ⟨p.log F.realification, p.adapted F.realification⟩)

theorem compareRealOrbit_zero (p : F.realification.PolynomialOrbit) :
    (F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) 0
      (F.compareRealOrbit π p) = 1 := by
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ => 0)
    (F.realComparisonLog π ⟨p.log F.realification, p.adapted F.realification⟩) = 0
  rw [eval_zero_eq_coefficient, F.realComparisonLog_coefficient, F.realComparisonCoefficient_zero_index]

theorem compareRealOrbit_projections (p : F.realification.PolynomialOrbit)
    (hp : F.realification.polynomialOrbitEval 0 p = 1) (x : σ → ℤ) :
    NilpotentLieBCHGroup.mapReal (realificationLieHom (F.comparisonFirst π))
        ((F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) x
          (F.compareRealOrbit π p)) = F.realification.polynomialOrbitEval x p ∧
      NilpotentLieBCHGroup.mapReal (realificationLieHom (F.comparisonSecond π))
        ((F.comparisonFiltration π).realification.polynomialOrbitEval (fun _ => 1) x
          (F.compareRealOrbit π p)) =
      (F.squarefreeMultidegreeFiltration π).realification.polynomialOrbitEval
        (fun j => x (π j)) (F.polarizeRealOrbit π p) := by
  have hz : coefficients (p.log F.realification) 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hp
    change eval (fun _ => 0) (p.log F.realification) = 0 at h
    rwa [eval_zero_eq_coefficient] at h
  constructor
  · apply NilpotentLieBCHGroup.ext
    exact F.realComparisonLog_first_eval π
      ⟨p.log F.realification, p.adapted F.realification⟩ hz (fun i => (x i : ℚ))
  · apply NilpotentLieBCHGroup.ext
    exact F.realComparisonLog_second_eval π
      ⟨p.log F.realification, p.adapted F.realification⟩ hz (fun i => (x i : ℚ))

end Erdos3.MultidegreeLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RankUnadaptedFactorization
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

def rankVerticalSelectionBudget (p : ℝ) : ℝ := p + verticalDecompositionBudget (p + 1) + 1

end Erdos3

end

end OAI
end


