-- Prove2me | Definitions.Def_OAIErdos3B060
-- name    : OAIErdos3B060
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T07:46:06.964828+00:00
-- url     : https://prove2.me/theorems/1a55cc76-73c6-4d05-a411-4ae2388cfc06
-- title:
--   OpenAI Erdős-3 split, definitions bundle 61 of 198
-- statement:
--   Definitions bundle 61 of 198 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B059`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 61 available.
--
--   Modules: `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_commonFreePolynomialOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_dependentFreePolynomialOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_native_commonFreePolynomialOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.CoefficientBases.exists_native_dependentFreePolynomialOrbit`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeRealFiltration`, `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFreeRealFiltration_eq_native`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coefficient_bases`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_controlled_coefficient_bases`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_native_common_free_model`, `OAI.Erdos3.NilpotentLieFiltration.exists_positiveUnivariate_orbit_lift`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.paired`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable_lipschitz`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable_norm`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable_unit`, `OAI.Erdos3.RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable_vertical`, `OAI.Erdos3.SubspaceFreeLift.Algebra`, `OAI.Erdos3.SubspaceFreeLift.Alphabet`, `OAI.Erdos3.SubspaceFreeLift.alphabet_card_le`, `OAI.Erdos3.SubspaceFreeLift.coefficientLift`, `OAI.Erdos3.SubspaceFreeLift.coefficientLift_range`, `OAI.Erdos3.SubspaceFreeLift.evaluation`, `OAI.Erdos3.SubspaceFreeLift.evaluation_coefficientLift`, `OAI.Erdos3.SubspaceFreeLift.evaluation_generator`, `OAI.Erdos3.SubspaceFreeLift.exists_native_model`, `OAI.Erdos3.SubspaceFreeLift.exists_native_pair_orbit`, `OAI.Erdos3.SubspaceFreeLift.exists_native_polynomialOrbit`, `OAI.Erdos3.SubspaceFreeLift.exists_polynomialOrbit`, `OAI.Erdos3.SubspaceFreeLift.filtration`, `OAI.Erdos3.SubspaceFreeLift.generator`, `OAI.Erdos3.SubspaceFreeLift.generatorSpan`, `OAI.Erdos3.SubspaceFreeLift.generatorSpan_le_layer`, `OAI.Erdos3.SubspaceFreeLift.native_pair_observable_eval`, `OAI.Erdos3.SubspaceFreeLift.realCoefficientLift`, `OAI.Erdos3.SubspaceFreeLift.realCoefficientLift_baseChange`, `OAI.Erdos3.SubspaceFreeLift.realCoefficientLift_mem`, `OAI.Erdos3.SubspaceFreeLift.realEvaluation_coefficientLift`, `OAI.Erdos3.SubspaceFreeLift.weight`, `OAI.Erdos3.SubspaceFreeLift.weight_pos`, `OAI.Erdos3.VectorPolynomial.map_positiveUnivariate`, `OAI.Erdos3.VectorPolynomial.positiveUnivariate_reconstruct`, `OAI.Erdos3.exists_native_shared_common_factorization`, `OAI.Erdos3.exists_native_shared_free_family`, `OAI.Erdos3.pairDifferenceFunctional_eq_piFrequency`, `OAI.Erdos3.realify_pairDifferenceFunctional`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B184

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators NNReal

theorem realify_pairDifferenceFunctional {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (η : L →ₗ[ℚ] ℚ) (x : ℝ ⊗[ℚ] (Fin 2 → L)) :
    realifyFunctional (pairDifferenceFunctional η) x =
      realifyFunctional η (realificationLieHom (liePiEval (0 : Fin 2)) x) -
        realifyFunctional η (realificationLieHom (liePiEval (1 : Fin 2)) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    simp only [realifyFunctional_tmul, pairDifferenceFunctional_apply,
      realificationLieHom_tmul, liePiEval_apply, Rat.cast_sub, mul_sub]
  | add x y hx hy => simp only [map_add, hx, hy]; ring

theorem pairDifferenceFunctional_eq_piFrequency {L : Type*} [LieRing L] [LieAlgebra ℚ L]
    (η : L →ₗ[ℚ] ℚ) :
    pairDifferenceFunctional η = piFrequency (fun i : Fin 2 => if i = 0 then η else -η) := by
  ext x
  simp [piFrequency_apply, Fin.sum_univ_two, pairDifferenceFunctional_apply, sub_eq_add_neg]

namespace RationalFilteredNilmanifold.UnitVerticalObservable

variable {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))]
  {D : RationalFilteredNilmanifold L s d} (T : D.DegreeRankStructure r) {p : ℝ}
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)

noncomputable def pairedObservable (a : I × I) (x : (pi (fun _ : Fin 2 => D)).Space) : ℂ :=
  V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x) *
    star (V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x))

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_unit (x : (pi (fun _ : Fin 2 => D)).Space) :
    ∑ a, ‖V.pairedObservable T a x‖ ^ 2 = 1 := by
  simp only [pairedObservable, norm_mul, norm_star, mul_pow, Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, V.unit, mul_one]

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_norm (a : I × I) (x : (pi (fun _ : Fin 2 => D)).Space) :
    ‖V.pairedObservable T a x‖ ≤ 1 := by
  simpa only [pairedObservable, norm_mul, norm_star, mul_one] using
    mul_le_mul (V.norm a.1 _) (V.norm a.2 _) (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

theorem pairedObservable_lipschitz (a : I × I) :
    letI := (pi (fun _ : Fin 2 => D)).metricSpace
    LipschitzWith
      (2 * (V.lipBound * coordinateLipschitzBound d (Fintype.card (Σ _ : Fin 2, Fin d)) 1))
      (V.pairedObservable T a) := by
  let := D.metricSpace
  let := (pi (fun _ : Fin 2 => D)).metricSpace
  have h₀ := (V.lipschitz a.1).comp (productProjection_lipschitz (fun _ : Fin 2 => D) 0)
  have h₁ := (V.lipschitz a.2).comp (productProjection_lipschitz (fun _ : Fin 2 => D) 1)
  change LipschitzWith _ (fun x : (pi (fun _ : Fin 2 => D)).Space =>
    V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x) *
      star (V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x)))
  exact (lipschitz_mul_star_of_bounds
    (fun x : (pi (fun _ : Fin 2 => D)).Space => V.observable a.1 (productProjection (fun _ : Fin 2 => D) 0 x))
    (fun x : (pi (fun _ : Fin 2 => D)).Space => V.observable a.2 (productProjection (fun _ : Fin 2 => D) 1 x))
    (Bf := 1) (Bg := 1) h₀ h₁ (fun x => V.norm a.1 _) (fun x => V.norm a.2 _)).weaken
      (by simp only [one_mul, two_mul, le_refl])

omit [TopologicalSpace (ℝ ⊗[ℚ] (Fin 2 → L))]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] (Fin 2 → L))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (Fin 2 → L))] [T2Space (ℝ ⊗[ℚ] (Fin 2 → L))] in
theorem pairedObservable_vertical (a : I × I) (z : (pi (fun _ : Fin 2 => D)).RealGroup)
    (hz : z ∈ (piRank (fun _ : Fin 2 => D) (fun _ => T)).realSubgroup s r)
    (x : (pi (fun _ : Fin 2 => D)).Space) :
    V.pairedObservable T a (z • x) =
      CircleFourier.character
        ((realifyFunctional (pairDifferenceFunctional V.frequency) z.coord : ℝ) : CircleFourier.Circle) *
        V.pairedObservable T a x := by
  simp only [pairedObservable, productProjection_smul]
  rw [V.vertical a.1 _ (productProjectionHom_mem_rank (fun _ : Fin 2 => D)
    (fun _ => T) 0 s r z hz), V.vertical a.2 _
    (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 1 s r z hz)]
  rw [star_mul, realify_pairDifferenceFunctional, AddCircle.coe_sub,
    sub_eq_add_neg, CircleFourier.character_add, CircleFourier.character_neg]
  simp only [productProjectionHom, NilpotentLieBCHGroup.realificationMap_coord]
  ring

noncomputable def paired (hp : 2 ≤ p) (hD : D.GeometryComplexityLE p) :
    (pi (fun _ : Fin 2 => D)).UnitVerticalObservable
      ((piRank (fun _ : Fin 2 => D) (fun _ => T)).realSubgroup s r) (I × I)
      (p + (p ^ 2 + p + 3) ^ 2 + 2) where
  observable := V.pairedObservable T
  unit := V.pairedObservable_unit T
  norm := V.pairedObservable_norm T
  lipBound := 2 * (V.lipBound * coordinateLipschitzBound d (Fintype.card (Σ _ : Fin 2, Fin d)) 1)
  lip_bound := by
    have hp₀ : 0 ≤ p := by linarith
    have hproj := productProjection_lipschitz_bound (fun _ : Fin 2 => D) hp₀
      (by simpa using hp) (fun _ => hD) 0
    simp only [NNReal.coe_mul, NNReal.coe_ofNat]
    calc
      _ ≤ Real.exp 2 * (Real.exp p * Real.exp ((p ^ 2 + p + 3) ^ 2)) :=
        mul_le_mul (by linarith [Real.add_one_le_exp (2 : ℝ)])
          (mul_le_mul V.lip_bound hproj (by positivity) (Real.exp_pos _).le)
          (by positivity) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  lipschitz := V.pairedObservable_lipschitz T
  frequency := pairDifferenceFunctional V.frequency
  height i := by
    have hsmall : p ≤ p + (p ^ 2 + p + 3) ^ 2 + 2 := by nlinarith [sq_nonneg (p ^ 2 + p + 3)]
    apply le_trans _ hsmall
    rw [pairDifferenceFunctional_eq_piFrequency]
    apply piFrequency_logHeight
    intro j k
    split_ifs
    · exact V.height k
    · simpa [rationalLogHeight] using V.height k
  vertical := V.pairedObservable_vertical T
  integral z hz hL := by
    have hmem (i : Fin 2) : productProjectionHom (fun _ : Fin 2 => D) i z ∈ D.realLattice :=
      NilpotentLieBCHGroup.realificationMap_subgroup (liePiEval i) _ _
        (productProjection_lattice (fun _ : Fin 2 => D) i) hL
    obtain ⟨m, hm⟩ := V.integral _
      (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 0 s r z hz) (hmem 0)
    obtain ⟨n, hn⟩ := V.integral _
      (productProjectionHom_mem_rank (fun _ : Fin 2 => D) (fun _ => T) 1 s r z hz) (hmem 1)
    refine ⟨m - n, ?_⟩
    rw [realify_pairDifferenceFunctional]
    change realifyFunctional V.frequency (productProjectionHom (fun _ : Fin 2 => D) 0 z).coord -
      realifyFunctional V.frequency (productProjectionHom (fun _ : Fin 2 => D) 1 z).coord = _
    rw [hm, hn, Int.cast_sub]

end RationalFilteredNilmanifold.UnitVerticalObservable
end Erdos3

end

section

namespace Erdos3.VectorPolynomial

variable {V W : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] {s : ℕ}

theorem map_positiveUnivariate (f : V →ₗ[ℚ] W) (v : Fin s → V) :
    map f (positiveUnivariate v) = positiveUnivariate (fun d => f (v d)) := by
  simp only [positiveUnivariate, map_sum, map_monomial]

theorem positiveUnivariate_reconstruct (p : VectorPolynomial Unit ℚ V)
    (hp : DegreeLE (fun _ : Unit => 1) s p) (hzero : coefficients p 0 = 0) :
    positiveUnivariate (fun d : Fin s => coefficients p (Finsupp.single () (d.val + 1))) = p := by
  apply coefficients.injective
  ext α
  have hα : Finsupp.single () (α ()) = α := by
    apply Finsupp.ext
    intro u
    cases u
    simp
  have hweight : Finsupp.weight (fun _ : Unit => 1) α = α () := by
    rw [← hα]
    simp [Finsupp.weight_single]
  by_cases h0 : α () = 0
  · have hz : α = 0 := by simpa only [h0, Finsupp.single_zero] using hα.symm
    rw [hz, positiveUnivariate_zero, hzero]
  · by_cases hle : α () ≤ s
    · let d : Fin s := ⟨α () - 1, by omega⟩
      have hd : d.val + 1 = α () := by dsimp only [d]; omega
      have he : Finsupp.single () (d.val + 1) = α := by rw [hd]; exact hα
      rw [← he, positiveUnivariate_coefficient]
    · have hhigh : s < Finsupp.weight (fun _ : Unit => 1) α := by rw [hweight]; omega
      rw [hp α hhigh]
      apply positiveUnivariate_coefficient_eq_zero
      intro d he
      have hv := congrArg (fun β : Unit →₀ ℕ => β ()) he
      simp only [Finsupp.single_eq_same] at hv
      omega

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open VectorPolynomial

theorem exists_positiveUnivariate_orbit_lift
    {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M] {s : ℕ}
    (F : NilpotentLieFiltration L s) (G : NilpotentLieFiltration M s)
    (π : L →ₗ[ℚ] M) (g : G.PolynomialOrbit (fun _ : Unit => 1))
    (hg : G.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (v : Fin s → L) (hv : ∀ d, v d ∈ F.layer (d.val + 1))
    (hπ : ∀ d, π (v d) = coefficients g.log (Finsupp.single () (d.val + 1))) :
    ∃ q : F.PolynomialOrbit (fun _ : Unit => 1),
      q.log = positiveUnivariate v ∧ F.polynomialOrbitEval (fun _ : Unit => 1) 0 q = 1 ∧
      VectorPolynomial.map π q.log = g.log ∧
      ∀ x : Unit → ℤ, π (F.polynomialOrbitEval (fun _ : Unit => 1) x q).coord =
        (G.polynomialOrbitEval (fun _ : Unit => 1) x g).coord := by
  have hadapt : F.Adapted (fun _ : Unit => 1) (positiveUnivariate v) := by
    apply (F.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hv d
  let q := polynomialOrbitOfLog (positiveUnivariate v) hadapt
  have hzero : coefficients g.log 0 = 0 := by
    have h := congrArg NilpotentLieBCHGroup.coord hg
    simpa only [G.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using h
  have hmap : VectorPolynomial.map π q.log = g.log := by
    change VectorPolynomial.map π (positiveUnivariate v) = g.log
    rw [map_positiveUnivariate, show (fun d => π (v d)) =
      (fun d : Fin s => coefficients g.log (Finsupp.single () (d.val + 1))) from funext hπ]
    exact positiveUnivariate_reconstruct g.log g.degreeLE hzero
  refine ⟨q, rfl, ?_, hmap, ?_⟩
  · apply NilpotentLieBCHGroup.ext
    change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
    rw [eval_zero_eq_coefficient, positiveUnivariate_zero]
  · intro x
    rw [F.polynomialOrbitEval_coord, G.polynomialOrbitEval_coord, ← eval_map, hmap]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

abbrev Alphabet := Σ d : Fin s, Fin (finrank ℚ (S d))

def weight (x : Alphabet S) : ℕ := x.1.val + 1

theorem weight_pos (x : Alphabet S) : 0 < weight S x := Nat.succ_pos _

abbrev Algebra (r : ℕ) := FreeDegreeRankLieAlgebra (Alphabet S) s r (weight S) (weight_pos S)

noncomputable def filtration (hr : r ≤ s) : DegreeRankLieFiltration (Algebra S r) s r :=
  FreeDegreeRankLieAlgebra.filtration (Alphabet S) s r (weight S) (weight_pos S) hr

noncomputable def generator (r : ℕ) (x : Alphabet S) : Algebra S r :=
  FreeDegreeRankLieAlgebra.of (Alphabet S) s r (weight S) (weight_pos S) x

noncomputable def generatorSpan (r : ℕ) (d : Fin s) : Submodule ℚ (Algebra S r) :=
  Submodule.span ℚ (Set.range (fun i => generator S r ⟨d, i⟩))

theorem generatorSpan_le_layer (hr : r ≤ s) (d : Fin s) :
    generatorSpan S r d ≤ (filtration S hr).layer (d.val + 1) 1 := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact FreeDegreeRankLieAlgebra.of_mem_layer (Alphabet S) s r (weight S) (weight_pos S) hr ⟨d, i⟩

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

noncomputable def coefficientLift (r : ℕ) (d : Fin s) : S d →ₗ[ℚ] Algebra S r :=
  (B d).constr ℚ (fun i => generator S r ⟨d, i⟩)

theorem coefficientLift_range (r : ℕ) (d : Fin s) :
    LinearMap.range (coefficientLift S B r d) = generatorSpan S r d :=
  (B d).constr_range ℚ

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

noncomputable def evaluation : Algebra S r →ₗ⁅ℚ⁆ L :=
  FreeDegreeRankLieAlgebra.lift F (weight S) (weight_pos S)
    (fun x => (B x.1 x.2).val) (fun x => hS x.1 (B x.1 x.2).property)

theorem evaluation_generator (x : Alphabet S) :
    evaluation S B F hS (generator S r x) = (B x.1 x.2).val :=
  FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x

theorem evaluation_coefficientLift (d : Fin s) (x : S d) :
    evaluation S B F hS (coefficientLift S B r d x) = x.val := by
  have heq : (evaluation S B F hS).toLinearMap.comp (coefficientLift S B r d) =
      (S d).subtype := by
    apply (B d).ext
    intro i
    change evaluation S B F hS ((B d).constr ℚ _ (B d i)) = _
    rw [Basis.constr_basis]
    exact evaluation_generator S B F hS ⟨d, i⟩
  exact LinearMap.congr_fun heq x

noncomputable def realCoefficientLift (d : Fin s) :
    (S d).baseChange ℝ →ₗ[ℝ] ℝ ⊗[ℚ] Algebra S r :=
  ((coefficientLift S B r d).baseChange ℝ).comp
    (realificationSubmoduleEquiv (S d)).symm.toLinearMap

theorem realCoefficientLift_baseChange (d : Fin s) (x : ℝ ⊗[ℚ] S d) :
    realCoefficientLift S B (r := r) d (realificationSubmoduleEquiv _ x) =
      (coefficientLift S B r d).baseChange ℝ x :=
  congrArg ((coefficientLift S B r d).baseChange ℝ)
    ((realificationSubmoduleEquiv _).symm_apply_apply x)

theorem realCoefficientLift_mem (d : Fin s) (x : (S d).baseChange ℝ) :
    realCoefficientLift S B (r := r) d x ∈ (generatorSpan S r d).baseChange ℝ := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [realCoefficientLift_baseChange]
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    rw [LinearMap.baseChange_tmul]
    exact Submodule.tmul_mem_baseChange_of_mem a
      ((coefficientLift_range S B r d).le ⟨v, rfl⟩)
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

theorem realEvaluation_coefficientLift (d : Fin s) (x : (S d).baseChange ℝ) :
    realificationLieHom (evaluation S B F hS) (realCoefficientLift S B d x) = x.val := by
  obtain ⟨v, rfl⟩ := (realificationSubmoduleEquiv _).surjective x
  rw [realCoefficientLift_baseChange, realificationSubmoduleEquiv_coe]
  change (evaluation S B F hS).toLinearMap.baseChange ℝ
    ((coefficientLift S B r d).baseChange ℝ v) = _
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul a v =>
    change a ⊗ₜ[ℚ] evaluation S B F hS (coefficientLift S B r d v) = a ⊗ₜ[ℚ] v.val
    rw [evaluation_coefficientLift]
  | add v w hv hw => simp only [map_add, hv, hw]

theorem exists_polynomialOrbit
    (g : F.associatedDegree.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : F.associatedDegree.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (S d).baseChange ℝ) :
    let G := (filtration S F.rank_le_degree).associatedDegree.realification
    ∃ u : G.PolynomialOrbit (fun _ : Unit => 1),
      G.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (generatorSpan S r d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (evaluation S B F hS)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := (filtration S F.rank_le_degree).associatedDegree.lowerCentralSeries_eq_bot)
        (hM := F.associatedDegree.lowerCentralSeries_eq_bot) (evaluation S B F hS)
        (G.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          F.associatedDegree.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  intro G
  let v (d : Fin s) := realCoefficientLift S B (r := r) d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (generatorSpan S r d).baseChange ℝ :=
    realCoefficientLift_mem S B d _
  have hv (d : Fin s) : v d ∈ G.layer (d.val + 1) := by
    change v d ∈ ((filtration S F.rank_le_degree).layer (d.val + 1) 0).baseChange ℝ
    rw [(filtration S F.rank_le_degree).rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (generatorSpan_le_layer S F.rank_le_degree d) (hvspan d)
  let π := (realificationLieHom (evaluation S B F hS)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    realEvaluation_coefficientLift S B F hS d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ := G.exists_positiveUnivariate_orbit_lift
    F.associatedDegree.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e : ℕ}
  (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
  (S : Fin s → Submodule ℚ L)
  (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
  (hS : ∀ j, S j ≤ T.filtration.layer (j.val + 1) 0)
  (E : RationalFilteredNilmanifold (Algebra S r) s e) (Q : E.DegreeRankStructure r)
  (hQ : Q.filtration = filtration S T.filtration.rank_le_degree)

include Q hQ

theorem exists_native_polynomialOrbit
    (g : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ j : Fin s, coefficients g.log (Finsupp.single () (j.val + 1)) ∈
      (S j).baseChange ℝ) :
    ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
        (generatorSpan S r j).baseChange ℝ) ∧
      VectorPolynomial.map
        ((realificationLieHom (evaluation S B T.filtration hS)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := E.filtration.lowerCentralSeries_eq_bot)
        (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS)
        (E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let hD := congrArg NilpotentLieFiltration.realification T.associated.symm
  let g' := D.filtration.realification.orbitEquivOfEq hD (fun _ : Unit => 1) g
  have hg' : T.filtration.associatedDegree.realification.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g' = 1 :=
    (D.filtration.realification.orbitEquivOfEq_eval hD _ g 0).trans hg
  have hlog' : g'.log = g.log := D.filtration.realification.orbitEquivOfEq_log hD _ g
  obtain ⟨u, hu0, huc, humap, hueval⟩ := exists_polynomialOrbit S B T.filtration hS g' hg'
    (fun j => by rw [hlog']; exact hcoeff j)
  let G := (filtration S T.filtration.rank_le_degree).associatedDegree.realification
  have hE : G = E.filtration.realification :=
    congrArg NilpotentLieFiltration.realification
      ((congrArg DegreeRankLieFiltration.associatedDegree hQ).symm.trans Q.associated)
  let u' := G.orbitEquivOfEq hE (fun _ : Unit => 1) u
  have hulog : u'.log = u.log := G.orbitEquivOfEq_log hE _ u
  have hueq (x : Unit → ℤ) :
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        G.polynomialOrbitEval (fun _ : Unit => 1) x u := G.orbitEquivOfEq_eval hE _ u x
  refine ⟨u', (hueq 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hulog] using huc
  · exact (congrArg _ hulog).trans (humap.trans hlog')
  · intro x
    rw [hueq]
    exact (hueval x).trans (D.filtration.realification.orbitEquivOfEq_eval hD _ g x)

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r d e : ℕ}
  (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
  (S : Fin s → Submodule ℚ (Fin 2 → L))
  (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
  (hS : ∀ j, S j ≤ (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration.layer (j.val + 1) 0)
  (M : RationalFilteredNilmanifold (Algebra S r) s e) (Q : M.DegreeRankStructure r)
  (hQ : Q.filtration = filtration S T.filtration.rank_le_degree)

include Q hQ in
theorem exists_native_pair_orbit
    (a : Fin 2 → D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (ha : ∀ i, D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (a i) = 1)
    (hc : ∀ j : Fin s,
      (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => L)).symm
        (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) ∈ (S j).baseChange ℝ) :
    let φ := evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS
    ∃ u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ j : Fin s, coefficients u.log (Finsupp.single () (j.val + 1)) ∈
        (generatorSpan S r j).baseChange ℝ) ∧
      ∀ i x, productProjectionHom (fun _ : Fin 2 => D) i
        (realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
          (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot) φ
          (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
        D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i) := by
  intro φ
  let g := NilpotentLieFiltration.piRealOrbit (fun _ : Fin 2 => D.filtration) a
  have hg : (pi (fun _ : Fin 2 => D)).filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g = 1 := by
    apply (realBCHPiEquiv (fun _ : Fin 2 => D.filtration)).injective
    funext i
    change realificationMap
      (hnil := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot)
      (hM := D.filtration.lowerCentralSeries_eq_bot) (liePiEval i) _ = (1 : D.RealGroup)
    exact (NilpotentLieFiltration.piRealOrbit_eval (fun _ : Fin 2 => D.filtration) a 0 i).trans (ha i)
  have hcoeff (j : Fin s) : coefficients g.log (Finsupp.single () (j.val + 1)) ∈
      (S j).baseChange ℝ := by
    have heq : coefficients g.log (Finsupp.single () (j.val + 1)) =
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => L)).symm
          (fun i => coefficients (a i).log (Finsupp.single () (j.val + 1))) := by
      apply (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => L)).injective
      rw [LinearEquiv.apply_symm_apply]
      funext i
      rw [realification_piRight_apply]
      exact NilpotentLieFiltration.piRealOrbit_coefficient (fun _ : Fin 2 => D.filtration) a _ i
    rw [heq]
    exact hc j
  obtain ⟨u, hu0, huc, _, hueval⟩ := exists_native_polynomialOrbit
    (pi (fun _ : Fin 2 => D)) (piRank (fun _ : Fin 2 => D) (fun _ => T))
    S B hS M Q hQ g hg hcoeff
  refine ⟨u, hu0, huc, ?_⟩
  intro i x
  rw [hueval]
  exact NilpotentLieFiltration.piRealOrbit_eval (fun _ : Fin 2 => D.filtration) a x i

variable {I : Type*} [Fintype I] {p q : ℝ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  [TopologicalSpace (ℝ ⊗[ℚ] Algebra S r)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] Algebra S r)] [T2Space (ℝ ⊗[ℚ] Algebra S r)]
  (V : D.UnitVerticalObservable (T.realSubgroup s r) I p)
  (Z : M.UnitVerticalObservable (Q.realSubgroup s r) (I × I) q)

theorem native_pair_observable_eval
    (hobs : ∀ i z, Z.observable i (QuotientGroup.mk z) =
      V.pairedObservable T i (QuotientGroup.mk (realificationMap
        (hnil := M.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot)
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS) z)))
    (a : Fin 2 → D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (u : M.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hlift : ∀ i x, productProjectionHom (fun _ : Fin 2 => D) i
      (realificationMap (hnil := M.filtration.lowerCentralSeries_eq_bot)
        (hM := (pi (fun _ : Fin 2 => D)).filtration.lowerCentralSeries_eq_bot)
        (evaluation S B (piRank (fun _ : Fin 2 => D) (fun _ => T)).filtration hS)
        (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
      D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a i))
    (i : I × I) (x : Unit → ℤ) :
    Z.observable i (QuotientGroup.mk
      (M.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u)) =
      V.observable i.1 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a 0))) *
      star (V.observable i.2 (QuotientGroup.mk
        (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x (a 1)))) := by
  rw [hobs]
  simp only [RationalFilteredNilmanifold.UnitVerticalObservable.pairedObservable,
    productProjection_mk, hlift]

end Erdos3.SubspaceFreeLift

end

section

namespace Erdos3.SubspaceFreeLift

open Module NilpotentLieBCHGroup
open scoped TensorProduct

theorem alphabet_card_le {L : Type*} [LieRing L] [LieAlgebra ℚ L] [Module.Finite ℚ L]
    {s : ℕ} (S : Fin s → Submodule ℚ L) :
    Fintype.card (Alphabet S) ≤ s * finrank ℚ L := by
  change Fintype.card (Σ d : Fin s, Fin (finrank ℚ (S d))) ≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _d : Fin s, finrank ℚ L := Finset.sum_le_sum
      (fun d _ => by simpa only [Fintype.card_fin] using Submodule.finrank_le (S d))
    _ = _ := by simp

theorem exists_native_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (L I : Type*) [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (r d : ℕ) (D : RationalFilteredNilmanifold L s d) (T : D.DegreeRankStructure r)
      (S : Fin s → Submodule ℚ L)
      (B : ∀ j, Basis (Fin (finrank ℚ (S j))) ℚ (S j))
      (hS : ∀ j, S j ≤ T.filtration.layer (j.val + 1) 0)
      (p : ℝ), 0 ≤ p → T.ComplexityLE p →
      (∀ j a i, rationalLogHeight (D.basis.repr (B j a : L) i) ≤ p) →
      ∀ U : D.UnitVerticalObservable (T.realSubgroup s r) I p,
      ∃ E : RationalFilteredNilmanifold (Algebra S r) s (finrank ℚ (Algebra S r)),
        ∃ Q : E.DegreeRankStructure r,
          Q.filtration = filtration S T.filtration.rank_le_degree ∧
          Q.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (D.basis.repr
            (evaluation S B T.filtration hS (E.basis j)) i) ≤ (p + C) ^ C) ∧
          E.lattice ≤ D.lattice.comap (mapOfSteps
            (hL := E.filtration.lowerCentralSeries_eq_bot)
            (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS)) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (Q.realSubgroup s r) I ((p + C) ^ C),
             V.frequency = U.frequency.comp (evaluation S B T.filtration hS).toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := E.filtration.lowerCentralSeries_eq_bot)
                 (hM := D.filtration.lowerCentralSeries_eq_bot) (evaluation S B T.filtration hS) x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_unit_observable s
  let K₀ : Polynomial ℕ := Polynomial.C (s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ r d D T S B hS p hp hT hB U
  let : Module.Finite ℚ L := D.basis.finiteDimensional_of_finite
  let K := ((s + 1 : ℕ) : ℝ) * p + 1
  have hpK : p ≤ K := by dsimp only [K]; push_cast; nlinarith [show (0 : ℝ) ≤ s from Nat.cast_nonneg s]
  have hK : 0 ≤ K := hp.trans hpK
  have hdim : (finrank ℚ L : ℝ) ≤ p := by
    simpa only [finrank_eq_card_basis D.basis, Fintype.card_fin] using hT.1.1
  have hcard : (Fintype.card (Alphabet S) : ℝ) ≤ K := by
    calc
      _ ≤ (s : ℝ) * finrank ℚ L := by exact_mod_cast alphabet_card_le S
      _ ≤ (s : ℝ) * p := mul_le_mul_of_nonneg_left hdim (Nat.cast_nonneg _)
      _ ≤ K := by dsimp only [K]; push_cast; nlinarith
  have hbound : (K + a) ^ a ≤ (p + C) ^ C := by
    simpa [K₀, K, Polynomial.eval₂_pow] using hbudget p hp
  obtain ⟨E, Q, hQ, hQc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree (Alphabet S) L I r d T.filtration.rank_le_degree D T (weight S) (weight_pos S)
      (fun x => (B x.1 x.2).val) (fun x => hS x.1 (B x.1 x.2).property) K hK hcard
      (hT.mono T hpK) (fun x i => (hB x.1 x.2 i).trans hpK) (U.mono hpK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] Algebra S r)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] Algebra S r) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  exact ⟨E, Q, hQ, hQc.mono Q hbound, hcentral, ⟨frame.mono hbound⟩,
    (fun i j => (hmatrix i j).trans hbound), hlattice, V.mono hbound, hfreq, hobs⟩

end Erdos3.SubspaceFreeLift

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.NativeFreePolynomialLifts
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  {Q : ℝ} (B : D.CoefficientBases Q)

noncomputable def coefficientFreeRealFiltration :
    NilpotentLieFiltration (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) s :=
  D.coefficientFreeFiltration.associatedDegree.realification

theorem CoefficientBases.exists_commonFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : D.coefficientFreeRealFiltration.PolynomialOrbit (fun _ : Unit => 1),
      D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.commonFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.coefficientFreeFiltration.associatedDegree.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let v (d : Fin s) := B.realCommonFreeLift D d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (D.commonFreeSpan d).baseChange ℝ :=
    B.realCommonFreeLift_mem D d _
  have hv (d : Fin s) : v d ∈ D.coefficientFreeRealFiltration.layer (d.val + 1) := by
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_layer d) (hvspan d)
  let π := (realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    B.realEvaluation_commonFreeLift D d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ :=
    D.coefficientFreeRealFiltration.exists_positiveUnivariate_orbit_lift
      W.model.filtration.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

theorem CoefficientBases.exists_dependentFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : D.coefficientFreeRealFiltration.PolynomialOrbit (fun _ : Unit => 1),
      D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, NilpotentLieBCHGroup.realificationMap
        (hnil := D.coefficientFreeFiltration.associatedDegree.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  let v (d : Fin s) := B.realDependentFreeLift D d
    ⟨coefficients g.log (Finsupp.single () (d.val + 1)), hcoeff d⟩
  have hvspan (d : Fin s) : v d ∈ (D.dependentFreeSpan d).baseChange ℝ :=
    B.realDependentFreeLift_mem D d _
  have hv (d : Fin s) : v d ∈ D.coefficientFreeRealFiltration.layer (d.val + 1) := by
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_layer d) (hvspan d)
  let π := (realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ
  have hπ (d : Fin s) : π (v d) = coefficients g.log (Finsupp.single () (d.val + 1)) :=
    B.realEvaluation_dependentFreeLift D d _
  obtain ⟨u, hu, hu0, humap, hueval⟩ :=
    D.coefficientFreeRealFiltration.exists_positiveUnivariate_orbit_lift
      W.model.filtration.realification π g hg v hv hπ
  refine ⟨u, hu0, ?_, humap, ?_⟩
  · intro d
    rw [hu, positiveUnivariate_coefficient]
    exact hvspan d
  · intro x
    apply NilpotentLieBCHGroup.ext
    exact hueval x

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : F.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem coefficientFreeRealFiltration_eq_native :
    D.coefficientFreeRealFiltration = F.filtration.realification := by
  apply congrArg NilpotentLieFiltration.realification
  exact (congrArg DegreeRankLieFiltration.associatedDegree hT).symm.trans T.associated

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.exists_native_commonFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : F.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.commonFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := F.filtration.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  obtain ⟨u, hu0, huc, humap, hueval⟩ := B.exists_commonFreePolynomialOrbit D g hg hcoeff
  let hF := D.coefficientFreeRealFiltration_eq_native F T hT
  let u' := D.coefficientFreeRealFiltration.orbitEquivOfEq hF (fun _ : Unit => 1) u
  have hlog : u'.log = u.log :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_log hF _ u
  have heval (x : Unit → ℤ) :
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_eval hF _ u x
  refine ⟨u', (heval 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hlog] using huc
  · simpa only [hlog] using humap
  · intro x
    rw [heval]
    exact hueval x

theorem CoefficientBases.exists_native_dependentFreePolynomialOrbit
    (g : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hg : W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 g = 1)
    (hcoeff : ∀ d : Fin s, coefficients g.log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ) :
    ∃ u : F.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 ∧
      (∀ d : Fin s, coefficients u.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentFreeSpan d).baseChange ℝ) ∧
      VectorPolynomial.map ((realificationLieHom (B.freeEvaluation D)).toLinearMap.restrictScalars ℚ)
        u.log = g.log ∧
      ∀ x : Unit → ℤ, realificationMap
        (hnil := F.filtration.lowerCentralSeries_eq_bot)
        (hM := W.model.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)
        (F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u) =
          W.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x g := by
  obtain ⟨u, hu0, huc, humap, hueval⟩ := B.exists_dependentFreePolynomialOrbit D g hg hcoeff
  let hF := D.coefficientFreeRealFiltration_eq_native F T hT
  let u' := D.coefficientFreeRealFiltration.orbitEquivOfEq hF (fun _ : Unit => 1) u
  have hlog : u'.log = u.log :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_log hF _ u
  have heval (x : Unit → ℤ) :
      F.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x u' =
        D.coefficientFreeRealFiltration.polynomialOrbitEval (fun _ : Unit => 1) x u :=
    D.coefficientFreeRealFiltration.orbitEquivOfEq_eval hF _ u x
  refine ⟨u', (heval 0).trans hu0, ?_, ?_, ?_⟩
  · simpa only [hlog] using huc
  · simpa only [hlog] using humap
  · intro x
    rw [heval]
    exact hueval x

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSharedFreeFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_coefficient_bases (hP : 0 ≤ P) (hbP : b ≤ P) :
    Nonempty (D.CoefficientBases (coefficientSpaceBasisBudget P)) := by
  classical
  choose c hc e he using fun d : Fin s =>
    D.exists_coefficient_space_bases hP hbP
      ⟨d.val + 1, Nat.succ_lt_succ d.isLt⟩ (Nat.succ_pos d.val)
  exact ⟨⟨c, e, hc, he⟩⟩

theorem exists_controlled_coefficient_bases :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {s r N : ℕ} [NeZero N] {b p q P : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P), 0 ≤ P → b ≤ P → Nonempty (D.CoefficientBases ((P + C) ^ C)) := by
  obtain ⟨C, hC, hbound⟩ := coefficientSpaceBasisBudget_bound
  refine ⟨C, hC, ?_⟩
  intro s r N _ b p q P W out H R D hP hbP
  obtain ⟨B⟩ := D.exists_coefficient_bases hP hbP
  exact ⟨B.mono D (hbound P hP)⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module NilpotentLieBCHGroup
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_free_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {b p q P M : ℝ}
      {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
      {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q}
      (D : R.CommonData P) (B : D.CoefficientBases M)
      (E : RationalFilteredNilmanifold W.L s W.dim) (S : E.DegreeRankStructure r),
      S.filtration = W.rank.filtration → E.basis = W.model.basis →
      0 ≤ M → S.ComplexityLE M → ∀ (I : Type*) [Fintype I]
      (U : E.UnitVerticalObservable (S.realSubgroup s r) I M),
      ∃ F : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
          (finrank ℚ D.CoefficientFreeLieAlgebra),
        ∃ T : F.DegreeRankStructure r,
          T.filtration = D.coefficientFreeFiltration ∧
          T.ComplexityLE ((M + C) ^ C) ∧ IsCentralLieBasis F.basis ∧
          Nonempty (FreeCoordinateFrame F.basis ((M + C) ^ C)) ∧
          (∀ i j, rationalLogHeight (E.basis.repr (B.freeEvaluation D (F.basis j)) i) ≤ (M + C) ^ C) ∧
          F.lattice ≤ E.lattice.comap (mapOfSteps
            (hL := F.filtration.lowerCentralSeries_eq_bot)
            (hM := E.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D)) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 F.basis
           ∃ V : F.UnitVerticalObservable (T.realSubgroup s r) I ((M + C) ^ C),
             V.frequency = U.frequency.comp (B.freeEvaluation D).toLinearMap ∧
             ∀ i x, V.observable i (QuotientGroup.mk x) =
               U.observable i (QuotientGroup.mk (realificationMap
                 (hnil := F.filtration.lowerCentralSeries_eq_bot)
                 (hM := E.filtration.lowerCentralSeries_eq_bot) (B.freeEvaluation D) x))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_free_unit_observable s
  let K₀ : Polynomial ℕ := Polynomial.C (2 * s + 1) * Polynomial.X + 1
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((K₀ + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro r N _ b p q P M W out H R D B E S hS hE hM hcomplex I _ U
  let K := ((2 * s + 1 : ℕ) : ℝ) * M + 1
  have hcoef : (1 : ℝ) ≤ (2 * s + 1 : ℕ) := by exact_mod_cast (show 1 ≤ 2 * s + 1 by omega)
  have hMK : M ≤ K := by dsimp only [K]; nlinarith
  have hK : 0 ≤ K := hM.trans hMK
  have hdim : (W.dim : ℝ) ≤ M := hcomplex.1.1
  have hcard : (Fintype.card D.CoefficientAlphabet : ℝ) ≤ K := by
    calc
      _ ≤ (2 : ℝ) * s * W.dim := by exact_mod_cast D.coefficientAlphabet_card
      _ ≤ (2 : ℝ) * s * M := mul_le_mul_of_nonneg_left hdim (by positivity)
      _ ≤ K := by dsimp only [K]; push_cast; nlinarith
  have hbound : (K + a) ^ a ≤ (M + C) ^ C := by
    simpa [K₀, K, Polynomial.eval₂_pow] using hbudget M hM
  have hgen (x : D.CoefficientAlphabet) :
      B.generator D x ∈ S.filtration.layer (D.coefficientWeight x) 0 := by
    rw [hS]
    exact B.generator_mem_layer D x
  have hheight (x : D.CoefficientAlphabet) (i : Fin W.dim) :
      rationalLogHeight (E.basis.repr (B.generator D x) i) ≤ K := by
    rw [hE]
    exact (B.generator_height D x i).trans hMK
  obtain ⟨F, T, hT, hTc, hcentral, ⟨frame⟩, hmatrix, hlattice, hV⟩ :=
    hfree D.CoefficientAlphabet W.L I r W.dim W.rank.filtration.rank_le_degree E S
      D.coefficientWeight D.coefficientWeight_pos (B.generator D) hgen K hK hcard
      (hcomplex.mono S hMK) hheight (U.mono hMK)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 F.basis
  obtain ⟨V, hfreq, hobs⟩ := hV
  have heval : FreeDegreeRankLieAlgebra.lift S.filtration D.coefficientWeight
      D.coefficientWeight_pos (B.generator D) hgen = B.freeEvaluation D := by
    apply FreeDegreeRankLieAlgebra.hom_ext
    intro x
    exact (FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x).trans
      (B.freeEvaluation_generator D x).symm
  rw [heval] at hmatrix hlattice hfreq hobs
  refine ⟨F, T, hT, hTc.mono T hbound, hcentral,
    ⟨frame.mono hbound⟩, (fun i j => (hmatrix i j).trans hbound), hlattice, ?_⟩
  exact ⟨V.mono hbound, hfreq, hobs⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∃ H' : Finset (ZMod N), H' ⊆ A.shifts ∧ H'.Nonempty ∧
                Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
              ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
                (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
                (Λ.subgroupOf W.family.model.lattice).Normal ∧
                (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
                (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                ∃ (K : ℕ) (hK : 0 < K)
                  (hin : scaledIntegerGrid K ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
                  (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid K),
                  (W.family.rank.withLattice Λ K hK hin hout).ComplexityLE ((p + C) ^ C) ∧
              ∃ U : (W.family.model.withLattice Λ K hK hin hout).UnitVerticalObservable
                  ((W.family.rank.withLattice Λ K hK hin hout).realSubgroup s r)
                  (Fin W.family.outputDim) ((p + C) ^ C),
                U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                  (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                    (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_frozen_common_factorization s hs
  obtain ⟨b, _, hshared⟩ := exists_native_shared_frozen_orbit_correlations s 1
  let B₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B₀ + (B₀ + 2 + Polynomial.C b) ^ b + 2)
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  let T := (B + 2 + b) ^ b
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hT : 0 ≤ T := by dsimp only [T]; positivity
  have hcost : B + T + 2 ≤ (p + C) ^ C := by
    simpa [B₀, B, T, Polynomial.eval₂_pow] using hbudget p hp
  have hBC : B ≤ (p + C) ^ C := by linarith
  have hTC : T ≤ (p + C) ^ C := by linarith
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  have hA : A.shifts.Nonempty := by
    have hcard : (0 : ℝ) < Fintype.card (ZMod N) := by exact_mod_cast Fintype.card_pos
    have hpos := (mul_pos (Real.exp_pos (-B)) hcard).trans_le hdensity
    exact Finset.card_pos.mp (by exact_mod_cast hpos)
  have hdata (h : {h // h ∈ A.shifts}) := hsplit h h.property
  choose ε γ v hε₀ hγ₀ hv₀ hε hγ heq hdep hy hperiod using hdata
  choose y _hunit V using hy
  let ε' (h : ZMod N) := if hh : h ∈ A.shifts then ε ⟨h, hh⟩ else 1
  let γ' (h : ZMod N) := if hh : h ∈ A.shifts then γ ⟨h, hh⟩ else 1
  let v' (h : ZMod N) := if hh : h ∈ A.shifts then v ⟨h, hh⟩ else 1
  let y' (h : ZMod N) := if hh : h ∈ A.shifts then y ⟨h, hh⟩ else 0
  have hε' (h : ZMod N) (hh : h ∈ A.shifts) :
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp (((B + 2) + 2) ^ 1)) (ε' h).log := by
    simp only [ε', dif_pos hh]
    exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) (hε ⟨h, hh⟩)
      (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
  have hγ' (h : ZMod N) (hh : h ∈ A.shifts) :
      CoefficientGrid (W.family.model.basis.baseChange ℝ) n (γ' h).log := by
    simpa only [γ', dif_pos hh] using hγ ⟨h, hh⟩
  have hcorr (h : ZMod N) (hh : h ∈ A.shifts) :
      Nonempty (NativeVectorCorrelation (s - 1) N (B + 2)
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε' h) (ξ * v' h) (γ' h) (y' h) x))) := by
    simpa only [ε', γ', v', y', dif_pos hh] using
      (show Nonempty _ from ⟨(Classical.choice (V ⟨h, hh⟩)).mono (show B ≤ B + 2 by linarith)⟩)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, K, hK, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, hU⟩ :=
    hshared W hF (show 0 ≤ B + 2 by linarith) hpB n hn
      (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
      A.shifts ε' γ' (fun h => ξ * v' h) y' hA hε' hγ' hcorr
  have hdense' : Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) := by
    calc
      _ ≤ Real.exp (-(B + T)) * Fintype.card (ZMod N) :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (Nat.cast_nonneg _)
      _ = Real.exp (-T) * (Real.exp (-B) * Fintype.card (ZMod N)) := by
        rw [← mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ Real.exp (-T) * A.shifts.card := mul_le_mul_of_nonneg_left hdensity (Real.exp_pos _).le
      _ ≤ _ := hdense
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst,
    H', hsub, hnonempty, hdense', Λ, hΛ, hchar, hnormal, hfinite,
    hindex.trans (Real.exp_le_exp.mpr hTC), K, hK, hin, hout, hRank.mono _ hTC,
    U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    let h' : {h // h ∈ A.shifts} := ⟨h, hsub hh⟩
    refine ⟨ε h', γ h', v h', hε₀ h', hγ₀ h', hv₀ h', ?_, hγ h', heq h', hdep h', ?_, hperiod h'⟩
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) (hε h')
        (Real.exp_le_exp.mpr hBC)
    · simpa only [v', dif_pos (hsub hh), h', UnitVerticalObservable.mono] using
        (show Nonempty _ from ⟨(Classical.choice (hU h hh)).mono hTC⟩)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_free_family (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
        Real.exp ((p + C) ^ C) ≤ N →
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (B : D.CoefficientBases ((p + C) ^ C))
            (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
              (finrank ℚ D.CoefficientFreeLieAlgebra))
            (T : E.DegreeRankStructure r),
            T.filtration = D.coefficientFreeFiltration ∧
            T.ComplexityLE ((p + C) ^ C) ∧ IsCentralLieBasis E.basis ∧
            Nonempty (FreeCoordinateFrame E.basis ((p + C) ^ C)) ∧
            (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
             letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
               IsModuleTopology.topologicalAddGroup ℝ _
             letI := realification_moduleTopology_t2 E.basis
             ∃ V : E.UnitVerticalObservable (T.realSubgroup s r)
                 (Fin W.family.outputDim) ((p + C) ^ C),
               V.frequency = B.freeFrequency D ∧
               ∃ ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                 E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                 (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
                   (D.commonFreeSpan d).baseChange ℝ) ∧
                 ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H' ⊆ W.shifts ∧ H'.Nonempty ∧
                   CyclicShortShiftSet H' ∧
                   Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                   ∀ h ∈ H', ∃ v : E.filtration.realification.PolynomialOrbit
                       (fun _ : Unit => 1),
                     E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                     (∀ d : Fin s, coefficients v.log (Finsupp.single () (d.val + 1)) ∈
                       (D.dependentFreeSpan d).baseChange ℝ) ∧
                     Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                       (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                         (E.filtration.realification.polynomialOrbitEval
                           (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) := by
  obtain ⟨a, _, hshared⟩ := exists_native_shared_common_factorization s hs
  obtain ⟨b, _, hbases⟩ := NativeRankRelation.CommonData.exists_controlled_coefficient_bases
  obtain ⟨e, _, hfree⟩ := NativeRankRelation.CommonData.exists_native_common_free_model s
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let M₀ : Polynomial ℕ := A₀ + (A₀ + Polynomial.C b) ^ b
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (M₀ + (M₀ + Polynomial.C e) ^ e)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  obtain ⟨c, τ, _, _, _, hLayers, _⟩ :=
    W.family.model.exists_controlled_adapted_basis hp W.family.complexity.1
  have hG (j : ℕ) : W.family.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}) := by
    rw [W.family.rank.associated]
    exact hLayers j
  let A := (p + a) ^ a
  let M := A + (A + b) ^ b
  let Q := (M + e) ^ e
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hAB : 0 ≤ (A + b) ^ b := by positivity
  have hM : 0 ≤ M := add_nonneg hA hAB
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hAM : A ≤ M := le_add_of_nonneg_right hAB
  have hMC : M ≤ (p + C) ^ C := by
    have h : M + Q ≤ (p + C) ^ C := by
      simpa [A₀, M₀, A, M, Q, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_right hQ).trans h
  have hQC : Q ≤ (p + C) ^ C := by
    have h : M + Q ≤ (p + C) ^ C := by
      simpa [A₀, M₀, A, M, Q, Polynomial.eval₂_pow] using hbudget p hp
    exact (le_add_of_nonneg_left hM).trans h
  have hAC := hAM.trans hMC
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA, R, D, anchors,
      hanchors, _hdensity, n, m, _hn, _hnA, _hm, _hmA, _hproj, ξ, hξ0, hcommon,
      H', hsub, hnonempty, hdense, Λ, _hΛ, _hchar, _hnormal, _hfinite, _hindex,
      k, hk, hin, hout, hRank, U, hfreq, hfactor⟩ :=
    hshared W hf c τ hG ((Real.exp_le_exp.mpr hAC).trans hN)
  have hP : 0 ≤ P := hp.trans (hpq.trans hqP)
  obtain ⟨B₀⟩ := hbases D hP (hpq.trans hqP)
  have hBM : (P + b) ^ b ≤ M := by
    calc
      (P + b) ^ b ≤ (A + b) ^ b :=
        pow_le_pow_left₀ (by positivity) (by change P + (b : ℝ) ≤ A + b; linarith) b
      _ ≤ M := le_add_of_nonneg_left hA
  let B := B₀.mono D hBM
  obtain ⟨E, T, hT, hTc, hcentral, ⟨frame⟩, _hmatrix, _hlattice, hV⟩ :=
    hfree D B (W.family.model.withLattice Λ k hk hin hout)
      (W.family.rank.withLattice Λ k hk hin hout) rfl rfl hM
      (hRank.mono _ hAM) (Fin W.family.outputDim) (U.mono hAM)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hVfreq, hVobs⟩ := hV
  have hdegree (d : Fin s) :
      Finsupp.weight (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) ≤ s := by
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  have hξcoeff (d : Fin s) : coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
    have h := (D.native_coefficient_mem_common (by omega) c τ hG (fun _ : Unit => 1)
      (Finsupp.single () (d.val + 1)) (hdegree d) ξ).mpr (hcommon d (hdegree d))
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
  obtain ⟨ξ', hξ'0, hξ'coeff, _hξ'log, hξ'eval⟩ :=
    B.exists_native_commonFreePolynomialOrbit D E T hT ξ hξ0 hξcoeff
  have hH'H : H' ⊆ H := hsub.trans anchors.shifts_subset
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA.trans hAC, R, D,
    B.mono D hMC, E, T, hT, hTc.mono T hQC, hcentral, ⟨frame.mono hQC⟩, V.mono hQC, ?_, ξ', hξ'0,
    hξ'coeff, H', hH'H, hsub.trans hanchors, hnonempty,
    (fun x hx y hy => hshort x (hH'H hx) y (hH'H hy)), ?_, ?_⟩
  · change V.frequency = W.family.vertical.frequency.comp (B.freeEvaluation D).toLinearMap
    change V.frequency = U.frequency.comp (B.freeEvaluation D).toLinearMap at hVfreq
    rw [hfreq] at hVfreq
    exact hVfreq
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hAC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    obtain ⟨ε, γ, v, _hε0, _hγ0, hv0, _hε, _hγ, _heq, hdep, hcorr, _hperiod⟩ := hfactor h hh
    have hvcoeff (d : Fin s) : coefficients v.log (Finsupp.single () (d.val + 1)) ∈
        (D.dependentCoefficientSpace ⟨d.val + 1, by omega⟩).baseChange ℝ := by
      have h := (D.native_coefficient_mem_dependent (by omega) c τ hG (fun _ : Unit => 1)
        (Finsupp.single () (d.val + 1)) (hdegree d) v).mpr (hdep d (hdegree d))
      simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using h
    obtain ⟨v', hv'0, hv'coeff, _hv'log, hv'eval⟩ :=
      B.exists_native_dependentFreePolynomialOrbit D E T hT v hv0 hvcoeff
    refine ⟨v', hv'0, hv'coeff, ?_⟩
    have hvalue (i : Fin W.family.outputDim) (x : ZMod N) :
        (V.mono hQC).observable i (QuotientGroup.mk
          (E.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ' * v'))) =
        U.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))) := by
      change V.observable i _ = _
      rw [hVobs]
      change U.observable i _ = U.observable i _
      congr 2
      rw [map_mul, map_mul, hξ'eval, hv'eval, map_mul]
    have heq : (fun (i : Fin W.family.outputDim) (x : ZMod N) =>
        (V.mono hQC).observable i (QuotientGroup.mk
        (E.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ' * v')))) =
        (fun (i : Fin W.family.outputDim) (x : ZMod N) => U.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))) :=
      funext fun i => funext (hvalue i)
    rw [heq]
    exact ⟨(Classical.choice hcorr).mono hAC⟩

end Erdos3

end

end OAI

end


