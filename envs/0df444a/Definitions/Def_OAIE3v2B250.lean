-- Prove2me | Definitions.Def_OAIE3v2B250
-- name    : OAIE3v2B250
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T05:25:21.664984+00:00
-- url     : https://prove2.me/theorems/93013946-1eb3-423c-8d72-bcddfd7d6116
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 255 of 311
-- statement:
--   Definitions bundle 255 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B228`, `OAIE3v2B239`, `OAIE3v2B240`, `OAIE3v2B241` of this split.
--
--   Modules: `Estimates/FreeCoefficientCorrectionControl.lean`, `Estimates/SharedFreeRoundingThreshold.lean`, `Lattices/SharedFreeAffineOrbitFamily.lean`, `Polynomial/BufferedSampledCurrentGradePhase.lean`, `Polynomial/FullChartPolynomialLiftControl.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B228
import Definitions.Def_OAIE3v2B239
import Definitions.Def_OAIE3v2B240
import Definitions.Def_OAIE3v2B241

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeCoefficientCorrectionControl
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N n : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s n)
  (T : E.DegreeRankStructure r) (hT : T.filtration = D.coefficientFreeFiltration)

include T hT

theorem exists_native_freeCoefficientPolynomialOrbit
    (v : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
    (hv : ∀ d, v d ∈ (D.coefficientFreeSpan d).baseChange ℝ) :
    ∃ u : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      u.log = positiveUnivariate v ∧
      E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 u = 1 := by
  have hfil := D.coefficientFreeRealFiltration_eq_native E T hT
  have hlayer (d : Fin s) : v d ∈ E.filtration.realification.layer (d.val + 1) := by
    rw [← hfil]
    change v d ∈ (D.coefficientFreeFiltration.layer (d.val + 1) 0).baseChange ℝ
    rw [D.coefficientFreeFiltration.rank_zero_eq_one]
    exact Submodule.baseChange_mono ℝ (D.coefficientFreeSpan_le_layer d) (hv d)
  have hadapt : E.filtration.realification.Adapted (fun _ : Unit => 1)
      (positiveUnivariate v) := by
    apply (E.filtration.realification.adapted_iff_coefficients _ _).mpr
    apply positiveUnivariate_coefficients_mem
    intro d
    simpa only [Finsupp.weight_single, smul_eq_mul, mul_one] using hlayer d
  let u := NilpotentLieFiltration.polynomialOrbitOfLog (positiveUnivariate v) hadapt
  refine ⟨u, rfl, ?_⟩
  apply NilpotentLieBCHGroup.ext
  change eval (fun _ : Unit => (0 : ℚ)) (positiveUnivariate v) = 0
  rw [eval_zero_eq_coefficient, positiveUnivariate_zero]

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeRoundingThreshold
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_native_full_coefficient_corrections (hs : 1 ≤ s) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    let I := R.interval ⟨t, D.subset ht⟩
    let V : I.SunflowerWitness P := D.witness t ht
    ∃ E Q : ∀ α : Unit →₀ ℕ,
        (W.rank.filtration.fourHorizontalLayer (Finsupp.weight (fun _ : Unit => 1) α)).baseChange ℝ,
      (∀ α j, |(W.fourRankBasis.baseChange ℝ).repr (E α).val j| ≤
        Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α) ∧
      (∀ α, (W.fourRankBasis.baseChange ℝ).equivFun (Q α).val ∈
        realDenominatorGrid V.projectedDenominator) ∧
      ∀ (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s),
        (fun k => coefficients
          (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (E α).val -
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (Q α).val ∈
            D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  intro I V
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_bounded_coefficient_corrections hs hP t ht
  refine ⟨E, Q, hE, hQ, ?_⟩
  intro α hα
  let d : Fin (s + 1) := ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩
  let e4 := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  let u := e4 (V.projectedOrbitCoefficient α).val
  let β : Fin 4 → ℝ ⊗[ℚ] W.L := fun k => coefficients
    (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α
  let e := e4 (E α).val
  let a := e4 (Q α).val
  have hu : u - e - a ∈ D.realCoefficientFourSpace d := by
    have h := (D.mem_real_coefficientFourSpace d (V.projectedOrbitCoefficient α - E α - Q α)).mpr
      (hres α hα)
    simpa only [Submodule.coe_sub, map_sub] using h
  have hk (k : Fin 4) : (u - e - a) k - (β - e - a) k ∈
      (W.rank.filtration.layer d.val 2).baseChange ℝ := by
    have heq : (u - e - a) k - (β - e - a) k = u k - β k := by
      simp only [Pi.sub_apply]
      abel
    rw [heq]
    exact V.projectedOrbitCoefficient_native_log_mod_kernel hs c τ hG α k
  exact (D.realCoefficientFourSpace_congr_mod_kernel d _ _ hk).mp hu

theorem native_full_scaled_correction (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
      ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
        Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
      (fun k => coefficients
        (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α) -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
          D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.exists_native_full_coefficient_corrections hs hP c τ hG t ht
  let I := R.interval ⟨t, D.subset ht⟩
  have hlength : (0 : ℝ) < I.length := by exact_mod_cast I.length_pos
  have hnorm : ‖(W.fourRankBasis.baseChange ℝ).equivFun (E α).val‖ ≤
      Real.exp ((P + 3) ^ 2) / monomialScale (fun _ : Unit => (I.length : ℝ)) α := by
    apply (pi_norm_le_iff_of_nonneg (div_nonneg (Real.exp_pos _).le
      (monomialScale_pos _ (fun _ => hlength) α).le)).mpr
    exact fun j => hE α j
  refine ⟨(E α).val, (Q α).val, ?_, ?_, hres α hα⟩
  · have h := I.norm_bound_on_modulus hp α hα (Real.exp_pos _).le
      ((W.fourRankBasis.baseChange ℝ).equivFun (E α).val) hnorm
    simpa only [Real.exp_add] using h
  · simpa only [hdenom t ht] using hQ α

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem native_shared_scaled_correction (hs : 1 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P)
    (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i}))
    (ξ : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (horbit : ∀ h, W.orbit h = ξ * v h)
    (l : ℕ) (hdenom : ∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator = l)
    (α : Unit →₀ ℕ) (hα : Finsupp.weight (fun _ : Unit => 1) α ≤ s)
    (t : ZMod N × ZMod N × ZMod N) (ht : t ∈ D.quadruples) :
    ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
      ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
        Real.exp ((P + 3) ^ 2 + (s : ℝ) * p) / monomialScale (fun _ : Unit => (N : ℝ)) α ∧
      (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l ∧
      sharedLogCoefficientTuple W.model.filtration ξ v α t -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E -
        (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q ∈
          D.realCoefficientFourSpace ⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hα⟩ := by
  obtain ⟨E, Q, hE, hQ, hres⟩ := D.native_full_scaled_correction hs hp hP c τ hG
    l hdenom α hα t ht
  refine ⟨E, Q, hE, hQ, ?_⟩
  apply (D.realCoefficientFourSpace_congr_mod_kernel _ _ _ ?_).mp hres
  intro k
  let a := rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)
  let e := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) E k
  let z := (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) Q k
  change (coefficients (W.orbit a).log α - e - z) -
    (coefficients ξ.log α + coefficients (v a).log α - e - z) ∈ _
  rw [horbit a]
  have heq : (coefficients (ξ * v a).log α - e - z) -
      (coefficients ξ.log α + coefficients (v a).log α - e - z) =
      coefficients (ξ * v a).log α - (coefficients ξ.log α + coefficients (v a).log α) := by abel
  rw [heq]
  exact W.rank.orbit_log_mul_mod_rank_two hs c τ hG (fun _ : Unit => 1) α ξ (v a)

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_uniform_shared_refinement
    (hs : 2 ≤ s) (hp : 0 ≤ p) (hP : 0 ≤ P) (hbP : b ≤ P) (hpP : p ≤ P)
    (U V : Fin s → Submodule ℚ W.L) (hVU : ∀ d, V d ≤ U d)
    (u : ∀ d, Basis (Fin (finrank ℚ (U d))) ℚ (U d))
    (v : ∀ d, Basis (Fin (finrank ℚ (V d))) ℚ (V d))
    (hu : ∀ d a i, rationalLogHeight (W.model.basis.repr (u d a : W.L) i) ≤ P)
    (hv : ∀ d a i, rationalLogHeight (W.model.basis.repr (v d a : W.L) i) ≤ P)
    (ξ : W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (g : ZMod N → W.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (horbit : ∀ h, W.orbit h = ξ * g h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈ (U d).baseChange ℝ)
    (hg : ∀ h (d : Fin s), coefficients (g h).log (Finsupp.single () (d.val + 1)) ∈
      (V d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P + 1)) ≤ (N : ℝ)) :
    let B := (P + 2) ^ 3 + 2 * P
    let z := 8 * sharedRefinementInputBudget s P + 1
    ∃ D₁ : R.CommonData B, D₁.quadruples ⊆ D.quadruples ∧ D₁.spaces = D.spaces ∧
      ∀ d : Fin s, ∃ m : ℕ, 0 < m ∧
        (m : ℝ) ≤ Real.exp (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ∧
        ∀ t ∈ D₁.quadruples, ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → W.L),
          ‖(W.fourRankBasis.baseChange ℝ).equivFun E‖ ≤
            (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
              monomialScale (fun _ : Unit => (N : ℝ)) (Finsupp.single () (d.val + 1)) ∧
          (W.fourRankBasis.baseChange ℝ).equivFun Q ∈ realDenominatorGrid m ∧
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).symm
              (sharedLogCoefficientTuple W.model.filtration ξ g (Finsupp.single () (d.val + 1)) t) -
            E - Q ∈ (fourRefinedRelation (U d) (V d)
              (D.coefficientFourSpace ⟨d.val + 1, by omega⟩)).baseChange ℝ := by
  intro B z
  classical
  let A := sharedRefinementInputBudget s P
  obtain ⟨hB, hPB, hA, hPA, hHA, hEA, hLA⟩ := sharedRefinementInputBudget_bounds s hP
  have hAz : A ≤ z := by dsimp only [z, A]; linarith
  have hdim : (Fintype.card (Fin W.dim) : ℝ) ≤ A := by
    simpa only [Fintype.card_fin] using W.complexity.1.1.trans (hbP.trans hPA)
  let : FiniteDimensional ℚ W.L := W.model.basis.finiteDimensional_of_finite
  obtain ⟨c, τ, _, _, hF⟩ := W.rank.filtration.associatedDegree.exists_sorted_adapted_basis
  obtain ⟨D₁, l, hsub, hspaces, hl, hlbound, hdenom⟩ := D.exists_common_projected_denominator hP
  refine ⟨D₁, hsub, hspaces, ?_⟩
  intro d
  let δ : Fin (s + 1) := ⟨d.val + 1, by omega⟩
  let α : Unit →₀ ℕ := Finsupp.single () (d.val + 1)
  have hα : Finsupp.weight (fun _ : Unit => 1) α = δ.val := by
    simp only [α, δ, Finsupp.weight_single, smul_eq_mul, mul_one]
  have hαs : Finsupp.weight (fun _ : Unit => 1) α ≤ s := by rw [hα]; exact Nat.le_of_lt_succ δ.isLt
  have hα0 : α ≠ 0 := by simp [α]
  obtain ⟨k, hk⟩ := D₁.exists_coefficientFour_basis hs hB (hbP.trans hPB) δ
  have hlA : (l : ℝ) ≤ Real.exp A := hlbound.trans (Real.exp_le_exp.mpr hLA)
  obtain ⟨m, hm, hmp, _, hsolve⟩ := exists_fourRefinedRelation_correction W.model.basis
    (U d) (V d) (hVU d) (D₁.coefficientFourSpace δ) (u d) (v d) k hA hdim
    (fun a i => (hu d a i).trans hPA) (fun a i => (hv d a i).trans hPA)
    (fun a i => (hk a i).trans hHA) l hl hlA (fun _ : Unit => (N : ℝ)) (fun _ => hN)
  refine ⟨m, hm, hmp, ?_⟩
  intro t ht
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hres⟩ := D₁.native_shared_scaled_correction (by omega) hp hB
    c τ hF ξ g horbit l hdenom α hαs t ht
  have hδ : (⟨Finsupp.weight (fun _ : Unit => 1) α, Nat.lt_succ_of_le hαs⟩ : Fin (s + 1)) = δ :=
    Fin.ext hα
  rw [hδ] at hres
  let e4 := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  let β := sharedLogCoefficientTuple W.model.filtration ξ g α t
  let x := e4.symm β
  have hxK : x - E₀ - Q₀ ∈ (D₁.coefficientFourSpace δ).baseChange ℝ := by
    change β - e4 E₀ - e4 Q₀ ∈ ((D₁.coefficientFourSpace δ).baseChange ℝ).map e4.toLinearMap at hres
    have h := (Submodule.mem_map_equiv _).mp hres
    change e4.symm (β - e4 E₀ - e4 Q₀) ∈ _ at h
    rw [map_sub, map_sub, e4.symm_apply_apply, e4.symm_apply_apply] at h
    exact h
  have hxS : x ∈ (fourCommonModulo (U d) (V d)).baseChange ℝ := by
    have h := sharedLogCoefficientTuple_mem_common W.model.filtration (U d) (V d) (hVU d)
      ξ g α t (hξ d) (fun h => hg h d)
    rw [← realification_fourCommonModulo] at h
    exact (Submodule.mem_map_equiv _).mp h
  have herror : (B + 3) ^ 2 + (s : ℝ) * p ≤ z := by
    have hmul := mul_le_mul_of_nonneg_left hpP (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
    exact (add_le_add_right hmul _).trans (hEA.trans hAz)
  have hEbound : ‖(W.fourRankBasis.baseChange ℝ).equivFun E₀‖ ≤
      Real.exp z / monomialScale (fun _ : Unit => (N : ℝ)) α := by
    apply hE₀.trans
    apply div_le_div_of_nonneg_right (Real.exp_le_exp.mpr herror)
    exact (monomialScale_pos _ (fun _ => by exact_mod_cast NeZero.pos N) α).le
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα0 x E₀ Q₀ hxK hxS hEbound hQ₀
  have hK : D₁.coefficientFourSpace δ = D.coefficientFourSpace δ := by
    rw [D₁.coefficientFourSpace_eq_sup, D.coefficientFourSpace_eq_sup, hspaces]
  rw [hK] at hmem
  exact ⟨E, Q, hE, hQ, hmem⟩

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_controlled_shared_free_refinement
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P' + 1)) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let z := 8 * sharedRefinementInputBudget s P' + 1
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∀ d : Fin s, ∃ m : ℕ, 0 < m ∧
        (m : ℝ) ≤ Real.exp (z + ((z + 2) ^ 3 + (z + 2) ^ 36)) ∧
        ∀ t ∈ D₁.quadruples, ∃ A S : ℝ ⊗[ℚ] (Fin 4 → D.CoefficientFreeLieAlgebra),
          ‖((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun A‖ ≤
            (Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
              monomialScale (fun _ : Unit => (N : ℝ)) (Finsupp.single () (d.val + 1)) ∧
          ((Pi.basis (fun _ : Fin 4 => E.basis)).baseChange ℝ).equivFun S ∈ realDenominatorGrid m ∧
          (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra)).symm
              (sharedLogCoefficientTuple E.filtration ξ v (Finsupp.single () (d.val + 1)) t) - A - S ∈
            (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).baseChange ℝ := by
  have hC := fun d : Fin s => D.exists_coefficientFreeSpan_basis E.basis F (by omega) d
  have hD := fun d : Fin s => D.exists_dependentFreeSpan_basis E.basis F (by omega) d
  choose c hc using hC
  choose a ha using hD
  exact D'.exists_uniform_shared_refinement hs hp' hP' hQP' hpp'
    D.coefficientFreeSpan D.dependentFreeSpan D.dependentFreeSpan_le_coefficientFreeSpan c a
    (fun d j i => (hc d j i).trans hQP') (fun d j i => (ha d j i).trans hQP') ξ v hsplit
    (fun d => Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d)) hv hN

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

namespace NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_controlled_shared_free_equations
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp (separationBudget (8 * sharedRefinementInputBudget s P' + 1)) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let z := 8 * sharedRefinementInputBudget s P' + 1
    let A := sharedFreeEquationInputBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∀ d : Fin s, ∃ n : ℕ, n ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
        ∃ ℓ : (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin n → ℚ),
          Function.Surjective ℓ ∧ LinearMap.ker ℓ =
            fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
          (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
              fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((A + 2) ^ 4) ∧
            let α := Finsupp.single () (d.val + 1)
            let φ := ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)
            let a := fun h => realifyCoordinateMap φ (coefficients (v h).log α)
            let c := realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (coefficients ξ.log α)
            ∀ t ∈ D₁.quadruples, ∃ q ∈ realDenominatorGrid m,
              ‖c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
                a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) - q‖ ≤
                Real.exp ((A + 2) ^ 3) *
                  ((Real.exp z + Real.exp ((z + 2) ^ 3 + (z + 2) ^ 18 + z)) /
                    monomialScale (fun _ : Unit => (N : ℝ)) α) := by
  intro B z A
  classical
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  obtain ⟨hA, hdimA, hheightA, hdenomA⟩ := sharedFreeEquationInputBudget_bounds s hQ hP'
  obtain ⟨D₁, hsub, hspaces, hcorr⟩ :=
    D.exists_controlled_shared_free_refinement E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  refine ⟨D₁, hsub, hspaces, ?_⟩
  intro d
  obtain ⟨n, hn, ℓ, hsurj, hker, hheight, _, _, _⟩ :=
    D.exists_correlation_refined_annihilator E T hbQ hT F V g hg D' hs hP' hQP' d
  obtain ⟨l, hl, hlp, hcorr⟩ := hcorr d
  let e4 := Pi.basis (fun _ : Fin 4 => E.basis)
  let H := ⌈Real.exp (fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P'))⌉₊
  have hheightH : ∀ j i, RationalHeightLE (ℓ (e4 i) j) H := by
    intro j i
    apply rationalHeightLE_ceil_exp
    have he : e4 i = LinearMap.single ℚ
        (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) i.1 (E.basis i.2) := by
      simp only [e4, Pi.basis_apply, LinearMap.single_apply]
    rw [he]
    exact hheight i.1 i.2 j
  have hdim : (4 : ℝ) * finrank ℚ D.CoefficientFreeLieAlgebra ≤ 4 * P' :=
    mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num)
  have hI : (Fintype.card (Σ _ : Fin 4, Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) : ℝ) ≤ A := by
    simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const, Finset.card_univ,
      smul_eq_mul, Nat.cast_mul, Nat.cast_ofNat] using hdim.trans hdimA
  have hJ : (Fintype.card (Fin n) : ℝ) ≤ A := by
    have hn' := (Nat.cast_le (α := ℝ)).mpr hn
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hn'
    simpa only [Fintype.card_fin] using hn'.trans (hdim.trans hdimA)
  have hH : (H : ℝ) ≤ Real.exp A :=
    (ceil_exp_le_exp_add_one (fourRefinementAnnihilatorBudget_nonneg
      (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP')))).trans
        (Real.exp_le_exp.mpr hheightA)
  have hlA : (l : ℝ) ≤ Real.exp A := hlp.trans (Real.exp_le_exp.mpr hdenomA)
  obtain ⟨m, hm, hmA, _, hsolve⟩ :=
    exists_real_annihilator_correction e4 ℓ hheightH hA hI hJ hH hl hlA
  refine ⟨n, hn, ℓ, hsurj, hker, hheight, m, hm, hmA, ?_⟩
  intro α φ a c t ht
  obtain ⟨E₀, Q₀, hE₀, hQ₀, hmem⟩ := hcorr t ht
  rw [← hker] at hmem
  obtain ⟨q, hq, hbound⟩ := hsolve _ E₀ Q₀ _ hmem hE₀ hQ₀
  refine ⟨q, hq, ?_⟩
  have hbalanced : fourBalancedDependent (D.dependentFreeSpan d) ≤ LinearMap.ker ℓ := by
    rw [hker]
    exact fourBalancedDependent_le_refined _ _ _
  have hdecomp := sharedLogCoefficientTuple_annihilator_decomposition E.filtration
    (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
    (D.dependentFreeSpan_le_coefficientFreeSpan d) ℓ hbalanced ξ v α t
    (Submodule.baseChange_mono ℝ (D.commonFreeSpan_le_coefficientFreeSpan d) (hξ d))
    (fun h => hv h d)
  change realFourCoordinateMap ℓ (sharedLogCoefficientTuple E.filtration ξ v α t) =
    c + (a (rankQuadrupleParameters t 1) + a (rankQuadrupleParameters t 2) -
      a (rankQuadrupleParameters t 0) - a (rankQuadrupleParameters t 3)) at hdecomp
  change ‖realFourCoordinateMap ℓ (sharedLogCoefficientTuple E.filtration ξ v α t) - q‖ ≤ _ at hbound
  rw [hdecomp] at hbound
  exact hbound

end NativeRankRelation.CommonData
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SharedFreeAffineOrbitFamily
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_affine_recovery
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ (n : Fin s → ℕ)
        (ℓ : ∀ d : Fin s, (Fin 4 → D.CoefficientFreeLieAlgebra) →ₗ[ℚ] (Fin (n d) → ℚ))
        (m : Fin s → ℕ),
        (∀ d, n d ≤ 4 * finrank ℚ D.CoefficientFreeLieAlgebra ∧
          Function.Surjective (ℓ d) ∧ LinearMap.ker (ℓ d) =
            fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
              (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩) ∧
          (∀ k i j, rationalLogHeight (ℓ d (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) k (E.basis i)) j) ≤
              fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P')) ∧
          0 < m d ∧ (m d : ℝ) ≤ Real.exp Λ) ∧
        let a := fun h (d : Fin s) => realifyCoordinateMap
          ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
          (coefficients (v h).log (Finsupp.single () (d.val + 1)))
        let n₀ := Fintype.card (Σ d : Fin s, Fin (n d))
        (n₀ : ℝ) ≤ 4 * (s : ℝ) * P' ∧
        ∃ J ⊆ H', J.Nonempty ∧
          Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
          ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N)
            (h₀ : ZMod N) (α : ∀ d, Fin (n d) → ℝ) (β : Fin r₀ → ∀ d, Fin (n d) → ℝ),
            (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧
            (∀ d i, α d i ∈ Set.Ico (0 : ℝ) (1 / m d)) ∧
            (∀ j d i, β j d i ∈ Set.Ico (0 : ℝ) (1 / m d)) ∧
            ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
              (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
              ∀ d, ∃ q ∈ realDenominatorGrid (m d),
                ‖a h d - (α d + ∑ j, (x j : ℝ) • β j d) - q‖ ≤
                  Real.exp Λ / (N : ℝ) ^ (d.val + 1) := by
  intro B Λ
  classical
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let z₀ := 8 * sharedRefinementInputBudget s P' + 1
  let A := sharedFreeEquationInputBudget s Q P'
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hbudget₀ := (sharedFreeAffineConstant_spec s).2 Q P' hQ hQP' hP' 0
    (by simpa only [Nat.cast_zero] using
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Nat.cast_nonneg s)) hP')
  have hcut := sharedFreeRecoveryThreshold_spec s hQ hP' N
    ((Real.exp_le_exp.mpr hbudget₀.1).trans hN)
  have hcoeff := sharedFreeRecoveryThreshold_coefficient_bounds s hQ hP'
  obtain ⟨D₁, hsub, hspaces, hblocks⟩ :=
    D.exists_controlled_shared_free_equations E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hcut.1
  choose n hn ℓ hsurj hker hheight m hm hmA hnear using hblocks
  have hdenom (d : Fin s) : (m d : ℝ) ≤ Real.exp Λ :=
    (hmA d).trans (Real.exp_le_exp.mpr (hcoeff.1.trans hbudget₀.1))
  have hnum : 2 * (Real.exp ((A + 2) ^ 3) *
      (Real.exp z₀ + Real.exp ((z₀ + 2) ^ 3 + (z₀ + 2) ^ 18 + z₀))) ≤ Real.exp Λ :=
    hcoeff.2.trans (Real.exp_le_exp.mpr hbudget₀.1)
  let a := fun h (d : Fin s) => realifyCoordinateMap
    ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
    (coefficients (v h).log (Finsupp.single () (d.val + 1)))
  let c := fun d : Fin s => realifyCoordinateMap ((ℓ d).comp (fourDiagonalMap (R := ℚ)))
    (coefficients ξ.log (Finsupp.single () (d.val + 1)))
  let ε := fun d : Fin s => Real.exp ((A + 2) ^ 3) *
    ((Real.exp z₀ + Real.exp ((z₀ + 2) ^ 3 + (z₀ + 2) ^ 18 + z₀)) / (N : ℝ) ^ (d.val + 1))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  have hε : ∀ d, 0 < ε d := by intro d; dsimp [ε]; positivity
  have hsmall : ∀ d, 2 * (m d : ℝ) * ε d ≤ 1 := by
    intro d
    exact hcut.2 (m d) (d.val + 1) (by omega) (hmA d)
  have hnear' : ∀ t ∈ D₁.quadruples, ∀ d, ∃ q ∈ realDenominatorGrid (m d),
      ‖c d + (a (rankQuadrupleParameters t 1) d + a (rankQuadrupleParameters t 2) d -
        a (rankQuadrupleParameters t 0) d - a (rankQuadrupleParameters t 3) d) - q‖ ≤ ε d := by
    intro t ht d
    simpa only [a, c, ε, monomialScale, Finsupp.prod_single_index, pow_zero] using hnear d t ht
  have hdim : (Fintype.card (Σ d : Fin s, Fin (n d)) : ℝ) ≤ 4 * (s : ℝ) * P' := by
    rw [Fintype.card_sigma, Nat.cast_sum]
    simp only [Fintype.card_fin]
    calc
      (∑ d : Fin s, (n d : ℝ)) ≤ ∑ _d : Fin s, 4 * P' := by
        apply Finset.sum_le_sum
        intro d _hd
        have hnR := (Nat.cast_le (α := ℝ)).mpr (hn d)
        simp only [Nat.cast_mul, Nat.cast_ofNat] at hnR
        exact hnR.trans (mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num))
      _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
  refine ⟨D₁, hsub, hspaces, n, ℓ, m, ?_, hdim, ?_⟩
  · intro d
    exact ⟨hn d, hsurj d, hker d, hheight d, hm d, hdenom d⟩
  · obtain ⟨J, hJH, hJ, hsize, r₀, R₀, η, h₀, α, β, hrank, hproper, hα, hβ, hrepr⟩ :=
      D₁.degreewise_proper_affine_recovery hB a c m hm ε hε hsmall hnear'
    have hbudget := sharedFreeAffineConstant_proper_spec s hP' _ hdim
    refine ⟨J, hJH, hJ, ?_, r₀, R₀, η, h₀, α, β, hrank.trans hbudget.2.2, hproper, hα, hβ, ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (Real.exp_le_exp.mpr (neg_le_neg hbudget.1)) (Nat.cast_nonneg _)).trans hsize
    · intro h hh
      obtain ⟨x, hx, hspace, herr⟩ := hrepr h hh
      refine ⟨x, hx, hspace, ?_⟩
      intro d
      obtain ⟨q, hq, he⟩ := herr d
      refine ⟨q, hq, he.trans ?_⟩
      simpa only [ε, mul_div_assoc] using
        div_le_div_of_nonneg_right hnum (pow_nonneg (Nat.cast_nonneg N) (d.val + 1))

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_affine_petal
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let L := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : Fin s → ℕ) (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ (∀ d, 0 < m d ∧ (m d : ℝ) ≤ Real.exp L) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp L) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp L) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∀ d, ∃ e q u : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra,
              e ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
              q ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
              u ∈ (fourPetalSpace (D.dependentFreeSpan d)
                (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                  (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ ∧
              coefficients (v h).log (Finsupp.single () (d.val + 1)) =
                (α d + ∑ j, (x j : ℝ) • β j d) + e + q + u ∧
              ‖(E.basis.baseChange ℝ).equivFun e‖ ≤ Real.exp L / (N : ℝ) ^ (d.val + 1) ∧
              (E.basis.baseChange ℝ).equivFun q ∈ realDenominatorGrid (m d) := by
  intro B Λ L
  classical
  obtain ⟨D₁, hsub, hspaces, n, ℓ, l, hdata, _hdim, J, hJH, hJ, hcard,
      r₀, R₀, η, h₀, α, β, hrank, hproper, hα, hβ, hrepr⟩ :=
    D.exists_shared_free_affine_recovery E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let A := sharedFreePetalLiftInput s Q P'
  let t := (A + 2) ^ 4 + 1
  let C := (t + 2) ^ 3 + (t + 2) ^ 18
  have hQ : 0 ≤ Q := (Nat.cast_nonneg _).trans hT.1.1
  have hΛ : 0 ≤ Λ := by dsimp [Λ]; positivity
  have ha : 0 ≤ fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P') :=
    fourRefinementAnnihilatorBudget_nonneg (add_nonneg hQ (coefficientFourHeightBudget_nonneg hP'))
  have hA : 0 ≤ A := by dsimp [A, sharedFreePetalLiftInput]; positivity
  have h4A : 4 * P' ≤ A := by dsimp [A, sharedFreePetalLiftInput]; linarith
  have hPA : P' ≤ A := by linarith
  have hQA : Q ≤ A := hQP'.trans hPA
  have hΛA : Λ ≤ A := by dsimp [A, sharedFreePetalLiftInput]; linarith
  have haA : fourRefinementAnnihilatorBudget (Q + coefficientFourHeightBudget P') ≤ A := by
    dsimp [A, sharedFreePetalLiftInput]
    linarith
  have hsections (d : Fin s) :
      ∃ (σ : (Fin (n d) → ℝ) →ₗ[ℝ] (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
        0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
        (∀ y, σ y ∈ (D.dependentFreeSpan d).baseChange ℝ) ∧
        (∀ w ∈ (D.dependentFreeSpan d).baseChange ℝ,
          realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
            (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
              (σ (realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
                (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) w)) =
            realifyCoordinateMap ((ℓ d).comp (LinearMap.single ℚ
              (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0)) w) ∧
        (∀ y, ‖(E.basis.baseChange ℝ).equivFun (σ y)‖ ≤ Real.exp C * ‖y‖) ∧
        ∀ y ∈ realDenominatorGrid (l d),
          (E.basis.baseChange ℝ).equivFun (σ y) ∈ realDenominatorGrid m := by
    obtain ⟨c, hc⟩ := D.exists_dependentFreeSpan_basis E.basis F (by omega) d
    obtain ⟨hn, _hsurj, _hker, hheight, hl, hlΛ⟩ := hdata d
    have hcspan : Submodule.span ℚ (Set.range (fun j => (c j : D.CoefficientFreeLieAlgebra))) =
        D.dependentFreeSpan d := by
      change Submodule.span ℚ (Set.range ((D.dependentFreeSpan d).subtype ∘ c)) = _
      rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
    apply exists_logHeight_subspace_image_section E.basis (D.dependentFreeSpan d)
      (fun j => (c j : D.CoefficientFreeLieAlgebra)) hcspan
      ((ℓ d).comp (LinearMap.single ℚ (fun _ : Fin 4 => D.CoefficientFreeLieAlgebra) 0))
      (l d) hl hA
    · simpa only [Fintype.card_fin] using (hT.1.1.trans hQP').trans hPA
    · have hnR := (Nat.cast_le (α := ℝ)).mpr hn
      simp only [Nat.cast_mul, Nat.cast_ofNat] at hnR
      have hdim := mul_le_mul_of_nonneg_left (hT.1.1.trans hQP') (by norm_num : (0 : ℝ) ≤ 4)
      simpa only [Fintype.card_fin] using hnR.trans (hdim.trans h4A)
    · have hcR : (finrank ℚ (D.dependentFreeSpan d) : ℝ) ≤
          finrank ℚ D.CoefficientFreeLieAlgebra := by
        exact_mod_cast Submodule.finrank_le (D.dependentFreeSpan d)
      simpa only [Fintype.card_fin] using hcR.trans ((hT.1.1.trans hQP').trans hPA)
    · intro j i
      exact (hc j i).trans hQA
    · intro i j
      exact (hheight 0 i j).trans haA
    · exact hlΛ.trans (Real.exp_le_exp.mpr hΛA)
  choose σ m hm hmb hσU hσfix hσnorm hσgrid using hsections
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have h18 : (t + 2) ^ 18 ≤ (t + 2) ^ 36 := pow_le_pow_right₀ (by linarith) (by decide)
  have hL : L = (t + 2) ^ 3 + (t + 2) ^ 36 + Λ := rfl
  have hCL : C + Λ ≤ L := by dsimp [C]; rw [hL]; linarith
  have hCL' : C ≤ L := (le_add_of_nonneg_right hΛ).trans hCL
  have hunit (d : Fin s) (y : Fin (n d) → ℝ)
      (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) (1 / l d)) : ‖y‖ ≤ 1 := by
    have hl : 0 < l d := (hdata d).2.2.2.2.1
    have hlR : (0 : ℝ) < l d := by exact_mod_cast hl
    have hl1 : (1 : ℝ) ≤ l d := by exact_mod_cast hl
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (hy i).1]
    exact (hy i).2.le.trans ((div_le_one hlR).mpr hl1)
  have hσunit (d : Fin s) (y : Fin (n d) → ℝ)
      (hy : ∀ i, y i ∈ Set.Ico (0 : ℝ) (1 / l d)) :
      ‖(E.basis.baseChange ℝ).equivFun (σ d y)‖ ≤ Real.exp L := by
    calc
      _ ≤ Real.exp C * ‖y‖ := hσnorm d y
      _ ≤ Real.exp C * 1 := mul_le_mul_of_nonneg_left (hunit d y hy) (Real.exp_pos _).le
      _ ≤ _ := by rw [mul_one]; exact Real.exp_le_exp.mpr hCL'
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m,
    (fun d => σ d (α d)), (fun j d => σ d (β j d)), hrank, hproper, ?_, ?_, ?_, ?_⟩
  · intro d
    exact ⟨hm d, (hmb d).trans (Real.exp_le_exp.mpr (by rw [hL]; linarith))⟩
  · intro d
    exact ⟨hσU d _, hσunit d _ (hα d)⟩
  · intro j d
    exact ⟨hσU d _, hσunit d _ (hβ j d)⟩
  · intro h hh
    obtain ⟨x, hx, hspace, herr⟩ := hrepr h hh
    refine ⟨x, hx, hspace, ?_⟩
    intro d
    obtain ⟨q, hq, he⟩ := herr d
    obtain ⟨e, q', u, heU, hqU, hu, heq, hbound, hgrid⟩ :=
      affine_petal_decomposition E.basis (D.dependentFreeSpan d) _ (ℓ d) (hdata d).2.2.1
        (σ d) (hσU d) (hσfix d) (Real.exp_pos _).le (hσnorm d) (hσgrid d)
        (α d) (fun j => β j d) x (coefficients (v h).log (Finsupp.single () (d.val + 1)))
        (hv h d) q hq he
    refine ⟨e, q', u, heU, hqU, hu, heq, hbound.trans ?_, hgrid⟩
    calc
      Real.exp C * (Real.exp Λ / (N : ℝ) ^ (d.val + 1)) =
          Real.exp (C + Λ) / (N : ℝ) ^ (d.val + 1) := by rw [← mul_div_assoc, ← Real.exp_add]
      _ ≤ _ := div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hCL) (by positivity)

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial CyclicCrootSisask
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P Q : ℝ} {f : ZMod N → ℂ}
  {W : NativeCorrelationStructure s r N b f} {out : Fin W.family.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W.family out H p q} (D : R.CommonData P)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
  (F : FreeCoordinateFrame E.basis Q)
  [TopologicalSpace (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  [T2Space (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)]
  (V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) Q)
  (g : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
  (hg : ∀ h, E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 (g h) = 1)

variable {out' : Fin W.family.outputDim} {H' : Finset (ZMod N)} {p' q' P' : ℝ}
  {R' : NativeRankRelation (W.replacementFamily E T hbQ hT V g hg) out' H' p' q'}
  (D' : R'.CommonData P')

include F

theorem exists_shared_free_affine_orbit_family
    (hTfil : T.filtration = D.coefficientFreeFiltration)
    (hs : 2 ≤ s) (hp' : 0 ≤ p') (hP' : 0 ≤ P') (hQP' : Q ≤ P') (hpp' : p' ≤ P')
    (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hsplit : ∀ h, g h = ξ * v h)
    (hξ : ∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
      (D.commonFreeSpan d).baseChange ℝ)
    (hv : ∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
      (D.dependentFreeSpan d).baseChange ℝ)
    (hN : Real.exp ((P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s) ≤ (N : ℝ)) :
    let B := (P' + 2) ^ 3 + 2 * P'
    let Λ := (P' + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s
    let L := sharedFreePetalLiftBudget s Q P'
    ∃ D₁ : R'.CommonData B, D₁.quadruples ⊆ D'.quadruples ∧ D₁.spaces = D'.spaces ∧
      ∃ J ⊆ H', J.Nonempty ∧ Real.exp (-Λ) * H'.card ≤ (J.card : ℝ) ∧
        ∃ (r₀ : ℕ) (R₀ : Fin r₀ → ℕ) (η : (Fin r₀ → ℤ) →+ ZMod N) (h₀ : ZMod N)
          (m : ℕ) (α : Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
          (β : Fin r₀ → Fin s → ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra),
          (r₀ : ℝ) ≤ Λ ∧ Set.InjOn η {x | ∀ j, |x j| ≤ (R₀ j : ℤ)} ∧ 0 < m ∧ (m : ℝ) ≤ Real.exp ((s : ℝ) * L) ∧
          (∀ d, α d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (α d)‖ ≤ Real.exp L) ∧
          (∀ j d, β j d ∈ (D.dependentFreeSpan d).baseChange ℝ ∧
            ‖(E.basis.baseChange ℝ).equivFun (β j d)‖ ≤ Real.exp L) ∧
          ∀ h ∈ J, ∃ x : Fin r₀ → ℤ,
            (∀ j, |x j| ≤ (R₀ j : ℤ)) ∧ h = h₀ + η x ∧
            ∃ A ε ρ U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
              A.log = positiveUnivariate (fun d => α d + ∑ j, (x j : ℝ) • β j d) ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 A = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ρ = 1 ∧
              E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 U = 1 ∧
              CoefficientBound (E.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ)) (Real.exp L) ε.log ∧
              CoefficientGrid (E.basis.baseChange ℝ) m ρ.log ∧
              ∀ d : Fin s,
                coefficients U.log (Finsupp.single () (d.val + 1)) ∈
                  (fourPetalSpace (D.dependentFreeSpan d)
                    (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
                      (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ ∧
                coefficients (v h).log (Finsupp.single () (d.val + 1)) =
                  coefficients A.log (Finsupp.single () (d.val + 1)) +
                  coefficients ε.log (Finsupp.single () (d.val + 1)) +
                  coefficients ρ.log (Finsupp.single () (d.val + 1)) +
                  coefficients U.log (Finsupp.single () (d.val + 1)) := by
  intro B Λ L
  classical
  obtain ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, l, α, β,
      hrank, hproper, hl, hα, hβ, hrepr⟩ :=
    D.exists_shared_free_affine_petal E T hbQ hT F V g hg D'
      hs hp' hP' hQP' hpp' ξ v hsplit hξ hv hN
  let m := ∏ d, l d
  have hm : 0 < m := Finset.prod_pos (fun d _ => (hl d).1)
  have hdiv (d : Fin s) : l d ∣ m := Finset.dvd_prod_of_mem l (Finset.mem_univ d)
  have hmb : (m : ℝ) ≤ Real.exp ((s : ℝ) * L) := by
    change ((∏ d, l d : ℕ) : ℝ) ≤ _
    rw [Nat.cast_prod]
    calc
      _ ≤ ∏ _d : Fin s, Real.exp L :=
        Finset.prod_le_prod (fun d _ => Nat.cast_nonneg (l d)) (fun d _ => (hl d).2)
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Real.exp_nat_mul]
  refine ⟨D₁, hsub, hspaces, J, hJH, hJ, hcard, r₀, R₀, η, h₀, m, α, β,
    hrank, hproper, hm, hmb, hα, hβ, ?_⟩
  intro h hh
  obtain ⟨x, hx, hspace, hcoeff⟩ := hrepr h hh
  choose e q u he hq hu heq herr hgrid using hcoeff
  have hdep (d : Fin s) :=
    Submodule.baseChange_mono ℝ (D.dependentFreeSpan_le_coefficientFreeSpan d)
  have ha (d : Fin s) : α d + ∑ j, (x j : ℝ) • β j d ∈
      (D.coefficientFreeSpan d).baseChange ℝ := by
    apply hdep d
    exact Submodule.add_mem _ (hα d).1
      (Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hβ j d).1))
  have huC (d : Fin s) : u d ∈ (D.coefficientFreeSpan d).baseChange ℝ :=
    hdep d (Submodule.baseChange_mono ℝ inf_le_left (hu d))
  obtain ⟨A, hA, hA0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil _ ha
  obtain ⟨ε, hε, hε0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil e
    (fun d => hdep d (he d))
  obtain ⟨ρ, hρ, hρ0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil q
    (fun d => hdep d (hq d))
  obtain ⟨U, hU, hU0⟩ := D.exists_native_freeCoefficientPolynomialOrbit E T hTfil u huC
  refine ⟨x, hx, hspace, A, ε, ρ, U, hA, hA0, hε0, hρ0, hU0, ?_, ?_, ?_⟩
  · rw [hε]
    apply positiveUnivariate_coefficientBound (E.basis.baseChange ℝ) e
      (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N) (Real.exp_pos L).le
    intro d
    simpa only [monomialScale, Finsupp.prod_single_index, pow_zero] using herr d
  · rw [hρ]
    apply positiveUnivariate_coefficientGrid
    exact fun d => realDenominatorGrid_subset_of_dvd (hl d).1 (hdiv d) (hgrid d)
  · intro d
    rw [hA, hε, hρ, hU, positiveUnivariate_coefficient, positiveUnivariate_coefficient,
      positiveUnivariate_coefficient, positiveUnivariate_coefficient]
    exact ⟨hu d, heq d⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.BufferedSampledCurrentGradePhase
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type} (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    (c : Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)

theorem majorPhaseNearestLift_eq_of_close
    (u : X → ℤ) (b : Fin (Fintype.card (LowTaggedIndex J k)) → ℤ)
    (hb : ∀ i, |MvPolynomial.eval (fun x => (u x : ℝ))
      (lowTaggedPolynomial J k poly i) - c i - (b i : ℝ)| ≤ 1 / 8) :
    majorPhaseNearestLift J k poly c u = b := by
  apply Eq.symm
  apply (majorPhasePlateauKernel _).buffered_lift_unique
    (fun i => MvPolynomial.eval (fun x => (u x : ℝ)) (lowTaggedPolynomial J k poly i) - c i)
    (majorPhaseNearestLift J k poly c u) b
    (majorPhaseNearestLift_close J k poly c u)
  rw [majorPhasePlateauKernel_one _ hb]
  norm_num

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup RationalFilteredNilmanifold
open scoped TensorProduct

attribute [local irreducible] realChartSubstitute

theorem FullChartControlledFactors.exists_degree_bounded_chart
    {m : ℕ} {X L ι : Type} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (J : Fin m → Type) [∀ j, Fintype (J j)]
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ)
    (left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
    {budget : ℝ} (h : FullChartControlledFactors F b ω hF J poly N left right budget) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.exp budget ∧
      ∃ Echart : PolynomialGroup (X ⊕ (Σ j, J j))
          F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot,
        F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left =
          realPolynomialChartSubstitution
            F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
            (normalizedRealPolynomialChart (fun i => (N i : ℝ))
              (fullTaggedMajorTopCoordinates J poly)) Echart ∧
        CoefficientBound ((F.associatedGradedBasis b ω hF).baseChange ℝ) (fun _ => 1)
          (Real.exp budget) Echart.coord ∧
        DegreeLE (fullTaggedVariableWeight (X := X) J) s Echart.coord ∧
        DegreeLE (fun _ => 1) s Echart.coord ∧
        CoefficientGrid ((F.associatedGradedBasis b ω hF).baseChange ℝ) q
          (F.realGradedSymbolPolynomialHom b ω hF
            (fullTaggedVariableWeight (X := X) J) right).coord := by
  obtain ⟨q, hq, hqB, E, hchart, hbound, hgrid⟩ := h
  let w := fullTaggedVariableWeight (X := X) J
  let E' : PolynomialGroup (X ⊕ (Σ j, J j))
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot :=
    ⟨weightedDegreeTruncate w s E.coord⟩
  refine ⟨q, hq, hqB, E', ?_, ?_, degreeLE_weightedDegreeTruncate w s E.coord,
    degreeLE_one_weightedDegreeTruncate w (fullTaggedVariableWeight_pos J) s E.coord, hgrid⟩
  · have hd := F.realGradedSymbolPolynomialHom_degreeLE b ω hF
      (fullTaggedVariableWeight (X := X) J) left
    have he := realPolynomialChartSubstitution_truncate_of_degreeLE
      F.associatedGradedFiltration.realification.lowerCentralSeries_eq_bot
      (fullTaggedVariableWeight (X := X) J)
      (normalizedRealPolynomialChart (fun i => (N i : ℝ)) (fullTaggedMajorTopCoordinates J poly))
      (fullTaggedMajorChart_homogeneous J poly (fun i => (N i : ℝ))) s
      (F.realGradedSymbolPolynomialHom b ω hF (fullTaggedVariableWeight (X := X) J) left)
      E hchart hd
    exact he
  · exact CoefficientBound.weightedDegreeTruncate _ _ (fun _ => zero_lt_one)
      (Real.exp_pos budget).le hbound w s

end Erdos3.NilpotentLieFiltration

end

end OAI
end


