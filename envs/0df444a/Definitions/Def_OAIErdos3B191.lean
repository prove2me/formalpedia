-- Prove2me | Definitions.Def_OAIErdos3B191
-- name    : OAIErdos3B191
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-10T08:15:58.518661+00:00
-- url     : https://prove2.me/theorems/b7c2f68a-0369-4998-8c54-a3fa843739ac
-- title:
--   OpenAI Erdős-3 split, definitions bundle 192 of 202
-- statement:
--   Definitions bundle 192 of 202 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs) and OpenAI's `@[simp]` lemmas from the same modules.
--
--   It imports the previous bundle `OAIErdos3B190`, so the bundles form a chain and importing this one makes the definitions of bundles 1 to 192 available.
--
--   Modules: `OAI.Erdos3.NativeRankRelation.CommonData.coefficientFourSpace_eq_sup`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coefficientFour_basis`, `OAI.Erdos3.NativeRankRelation.CommonData.exists_coefficientFour_generators`, `OAI.Erdos3.NativeRankRelation.CommonData.fourKernel_le_coefficientFourSpace`, `OAI.Erdos3.NativeRankRelation.CommonData.realCoefficientFourSpace_congr_mod_kernel`, `OAI.Erdos3.NativeRankRelation.CommonData.real_fourKernel_le_coefficientFourSpace`, `OAI.Erdos3.coefficientFourHeightBudget`, `OAI.Erdos3.coefficientFourHeightBudget_nonneg`, `OAI.Erdos3.exists_bounded_four_annihilator`, `OAI.Erdos3.exists_bounded_refined_four_annihilator`, `OAI.Erdos3.exists_fourBalancedDependent_basis_logHeight`, `OAI.Erdos3.exists_fourCommonModulo_basis_logHeight`, `OAI.Erdos3.exists_fourRefinedRelation_annihilator`, `OAI.Erdos3.exists_fourRefinedRelation_basis_logHeight`, `OAI.Erdos3.exists_fourRefinedRelation_correction`, `OAI.Erdos3.exists_native_shared_free_rank_relation`, `OAI.Erdos3.exists_real_annihilator_correction`, `OAI.Erdos3.fourBalanceProjection`, `OAI.Erdos3.fourBalanceProjection_apply`, `OAI.Erdos3.fourBalanceProjection_image`, `OAI.Erdos3.fourBalancedGenerators_logHeight`, `OAI.Erdos3.fourBalancedGenerators_span`, `OAI.Erdos3.fourBasisVectors`, `OAI.Erdos3.fourBasisVectors_apply`, `OAI.Erdos3.fourBasisVectors_logHeight`, `OAI.Erdos3.fourBasisVectors_span`, `OAI.Erdos3.fourCommonGenerators_span`, `OAI.Erdos3.fourCommonModulo_eq_sup`, `OAI.Erdos3.fourPetalSpace_eq_inf_ker`, `OAI.Erdos3.fourRefinementAnnihilatorBudget`, `OAI.Erdos3.fourRefinementAnnihilatorBudget_nonneg`, `OAI.Erdos3.fourRefinementBasisBudget`, `OAI.Erdos3.fourRefinementBasisBudget_nonneg`, `OAI.Erdos3.four_submodule_finrank_le`, `OAI.Erdos3.mem_real_petal_annihilator_iff`, `OAI.Erdos3.mem_realified_coordinate_kernel_iff`, `OAI.Erdos3.mem_realified_coordinate_kernel_iff_eq_zero`, `OAI.Erdos3.realFourCoordinateMap`, `OAI.Erdos3.realFourCoordinateMap_decomposition`, `OAI.Erdos3.realFourCoordinateMap_diagonal`, `OAI.Erdos3.realFourCoordinateMap_shared_decomposition`, `OAI.Erdos3.realFourCoordinateMap_single`, `OAI.Erdos3.real_four_diagonal`, `OAI.Erdos3.sharedRefinementInputBudget`, `OAI.Erdos3.sharedRefinementInputBudget_bounds`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B060

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeSharedFreeRankRelation
namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_shared_free_rank_relation (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ (A : ℝ) (hpA : p ≤ A), A ≤ (p + C) ^ C ∧
      ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
        H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
        p ≤ q ∧ q ≤ P ∧ P ≤ A ∧
        ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
          (B : D.CoefficientBases A)
          (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
            (finrank ℚ D.CoefficientFreeLieAlgebra))
          (T : E.DegreeRankStructure r) (hT : T.ComplexityLE A),
          T.filtration = D.coefficientFreeFiltration ∧ IsCentralLieBasis E.basis ∧
          Nonempty (FreeCoordinateFrame E.basis A) ∧
          (letI := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 E.basis
           ∃ V : E.UnitVerticalObservable (T.realSubgroup s r) (Fin W.family.outputDim) A,
             V.frequency = B.freeFrequency D ∧
             ∃ (ξ : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
               (hξ : E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1),
               (∀ d : Fin s, coefficients ξ.log (Finsupp.single () (d.val + 1)) ∈
                 (D.commonFreeSpan d).baseChange ℝ) ∧
               ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H' ⊆ W.shifts ∧ H'.Nonempty ∧
                 CyclicShortShiftSet H' ∧
                 Real.exp (-A) * Fintype.card (ZMod N) ≤ (H'.card : ℝ) ∧
                 ∃ (v : ZMod N → E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                   (hv : ∀ h, E.filtration.realification.polynomialOrbitEval
                     (fun _ : Unit => 1) 0 (v h) = 1),
                   (∀ h (d : Fin s), coefficients (v h).log (Finsupp.single () (d.val + 1)) ∈
                     (D.dependentFreeSpan d).baseChange ℝ) ∧
                   (∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N A
                     (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                       (E.filtration.realification.polynomialOrbitEval
                         (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v h))))))) ∧
                   (let U := W.replacementFamily E T hpA hT V (fun h => ξ * v h)
                     (fun h => by rw [map_mul, hξ, hv h, one_mul])
                    ∃ (out' : Fin U.outputDim) (H'' : Finset (ZMod N)) (q' : ℝ),
                      H'' ⊆ H' ∧ H''.Nonempty ∧ CyclicShortShiftSet H'' ∧
                      Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (H''.card : ℝ) ∧
                      A ≤ q' ∧ q' ≤ (p + C) ^ C ∧
                      ∃ R' : NativeRankRelation U out' H'' q' q',
                        Nonempty (R'.CommonData ((p + C) ^ C)))) := by
  obtain ⟨a, _, hfree⟩ := exists_native_shared_free_family s hs
  obtain ⟨c, _, hrelation⟩ := exists_native_common_rank_relation s (by omega)
  let A₀ : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (A₀ + (A₀ + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ p f W hf hN
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let A := (p + a) ^ a
  let Z := (A + c) ^ c
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hAZ : A + Z ≤ (p + C) ^ C := by
    simpa [A₀, A, Z, Polynomial.eval₂_pow] using hbudget p hp
  have hAC : A ≤ (p + C) ^ C := (le_add_of_nonneg_right hZ).trans hAZ
  have hZC : Z ≤ (p + C) ^ C := (le_add_of_nonneg_left hA).trans hAZ
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA, R, D, B, E, T,
    hfiltration, hT, hcentral, hframe, hdata⟩ :=
    hfree W hf ((Real.exp_le_exp.mpr hAC).trans hN)
  have hpA : p ≤ A := hpq.trans (hqP.trans hPA)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 E.basis
  obtain ⟨V, hfreq, ξ, hξ, hcommon, H', hH'H, hH'W, hH', hshort', hdense, hfactor⟩ := hdata
  have hall (h : ZMod N) :
      ∃ v : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
        E.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
        (∀ d : Fin s, coefficients v.log (Finsupp.single () (d.val + 1)) ∈
          (D.dependentFreeSpan d).baseChange ℝ) ∧
        (h ∈ H' → Nonempty (NativeVectorCorrelation (s - 1) N A
          (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
            (E.filtration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) := by
    by_cases hh : h ∈ H'
    · obtain ⟨v, hv, hcoeff, hc⟩ := hfactor h hh
      exact ⟨v, hv, hcoeff, fun _ => hc⟩
    · refine ⟨1, map_one _, ?_, fun hh' => (hh hh').elim⟩
      intro d
      change (0 : ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) ∈ _
      exact Submodule.zero_mem _
  choose v hv hcoeff hcorr using hall
  let X := W.replaceRank E T hpA hT V (fun h => ξ * v h)
    (fun h => by rw [map_mul, hξ, hv h, one_mul]) H' hH' hdense hcorr
  obtain ⟨out', H'', q', hsub, hnonempty, hshort'', hdense'', hAq, hqZ, R', ⟨D'⟩⟩ :=
    hrelation X hf ((Real.exp_le_exp.mpr hZC).trans hN)
  refine ⟨A, hpA, hAC, out, H, q, P, hHW, hH, hshort, hpq, hqP, hPA,
    R, D, B, E, T, hT, hfiltration, hcentral, hframe, V, hfreq, ξ, hξ, hcommon,
    H', hH'H, hH'W, hH', hshort', hdense, v, hv, hcoeff, hcorr,
    out', H'', q', hsub, hnonempty, hshort'', ?_, hAq, hqZ.trans hZC, R', ⟨D'.mono hZC⟩⟩
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hZC))
    (Nat.cast_nonneg _)).trans hdense''

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem coefficientFourSpace_eq_sup (d : Fin (s + 1)) :
    D.coefficientFourSpace d = D.spaces d ⊔
      Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2) := by
  let F := W.rank.filtration
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    change F.fourHorizontalMap d.val w ∈ F.horizontalImageOfSubmodule (D.spaces d) d.val at hw
    obtain ⟨z, hz, he⟩ := hw
    apply Submodule.mem_sup.mpr
    refine ⟨z.val, hz, w.val - z.val, ?_, by abel⟩
    apply Submodule.mem_pi.mpr
    intro k _
    exact (F.higherHorizontalMk_eq d.val _ _).mp (congrFun he.symm k)
  · intro hv
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    have hx' := D.spaces_le_fourHorizontalLayer d hx
    have hy' : y ∈ F.fourHorizontalLayer d.val := by
      apply (F.mem_fourHorizontalLayer d.val y).mpr
      intro k
      exact F.lex_antitone (Or.inr ⟨rfl, by omega⟩) ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))
    let z : F.fourHorizontalLayer d.val := ⟨x, hx'⟩
    let w : F.fourHorizontalLayer d.val := ⟨x + y, (F.fourHorizontalLayer d.val).add_mem hx' hy'⟩
    apply (D.mem_coefficientFourSpace d w).mpr
    change F.fourHorizontalMap d.val w ∈ F.horizontalImageOfSubmodule (D.spaces d) d.val
    refine ⟨z, hx, ?_⟩
    funext k
    apply (F.higherHorizontalMk_eq d.val _ _).mpr
    change x k - (x k + y k) ∈ F.layer d.val 2
    simpa only [sub_add_cancel_left] using
      (F.layer d.val 2).neg_mem ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))

theorem fourKernel_le_coefficientFourSpace (d : Fin (s + 1)) :
    Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2) ≤
      D.coefficientFourSpace d := by
  rw [D.coefficientFourSpace_eq_sup]
  exact le_sup_right

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem real_fourKernel_le_coefficientFourSpace (d : Fin (s + 1))
    (v : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hv : ∀ k, v k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v ∈ D.realCoefficientFourSpace d := by
  let e := TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)
  have hbase : e.symm v ∈
      (Submodule.pi Set.univ (fun _ : Fin 4 => W.rank.filtration.layer d.val 2)).baseChange ℝ := by
    apply (mem_realified_four_product_iff _ _).mpr
    intro k
    change e (e.symm v) k ∈ _
    rw [e.apply_symm_apply]
    exact hv k
  exact ⟨e.symm v, Submodule.baseChange_mono ℝ (D.fourKernel_le_coefficientFourSpace d) hbase,
    e.apply_symm_apply v⟩

theorem realCoefficientFourSpace_congr_mod_kernel (d : Fin (s + 1))
    (v z : Fin 4 → ℝ ⊗[ℚ] W.L)
    (hz : ∀ k, v k - z k ∈ (W.rank.filtration.layer d.val 2).baseChange ℝ) :
    v ∈ D.realCoefficientFourSpace d ↔ z ∈ D.realCoefficientFourSpace d := by
  have h := D.real_fourKernel_le_coefficientFourSpace d (v - z) hz
  constructor
  · intro hv
    simpa only [sub_sub_cancel] using (D.realCoefficientFourSpace d).sub_mem hv h
  · intro hz
    simpa only [sub_add_cancel] using (D.realCoefficientFourSpace d).add_mem h hz

end Erdos3.NativeRankRelation.CommonData

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonCoefficientFourAnnihilators
namespace OAI

section

namespace Erdos3

open Module

variable {R V ι κ : Type*} [Field R] [AddCommGroup V] [Module R V]

noncomputable def fourBasisVectors (D : Submodule R V) (b : Basis κ R D) :
    (Σ _ : Fin 4, κ) → (Fin 4 → V) :=
  (LinearMap.pi (fun k => D.subtype.comp (LinearMap.proj k))) ∘
    Pi.basis (fun _ : Fin 4 => b)

theorem fourBasisVectors_apply (D : Submodule R V) (b : Basis κ R D) (a : Σ _ : Fin 4, κ) :
    fourBasisVectors D b a = LinearMap.single R (fun _ : Fin 4 => V) a.1 (b a.2 : V) := by
  classical
  funext k
  simp only [fourBasisVectors, Function.comp_apply, LinearMap.pi_apply,
    LinearMap.comp_apply, LinearMap.proj_apply, Pi.basis_apply, LinearMap.single_apply]
  by_cases h : k = a.1
  · subst k
    simp only [Pi.single_eq_same]
    rfl
  · simp only [Pi.single_eq_of_ne h]
    rfl

theorem fourBasisVectors_span (D : Submodule R V) (b : Basis κ R D) :
    Submodule.span R (Set.range (fourBasisVectors D b)) =
      Submodule.pi Set.univ (fun _ : Fin 4 => D) := by
  classical
  rw [fourBasisVectors, Set.range_comp, ← Submodule.map_span,
    (Pi.basis (fun _ : Fin 4 => b)).span_eq, Submodule.map_top]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_pi.mpr (fun k _ => (y k).property)
  · intro hx
    exact ⟨fun k => ⟨x k, (Submodule.mem_pi.mp hx) k (Set.mem_univ k)⟩, rfl⟩

theorem fourCommonModulo_eq_sup (C D : Submodule R V) (hDC : D ≤ C) :
    fourCommonModulo C D = C.map (fourDiagonalMap (R := R)) ⊔
      Submodule.pi Set.univ (fun _ : Fin 4 => D) := by
  ext v
  constructor
  · intro hv
    obtain ⟨hc, hd⟩ := (mem_fourCommonModulo C D v).mp hv
    apply Submodule.mem_sup.mpr
    exact ⟨fourDiagonalMap (R := R) (v 0), ⟨v 0, hc 0, rfl⟩,
      v - fourDiagonalMap (R := R) (v 0), Submodule.mem_pi.mpr (fun k _ => hd k),
      by abel⟩
  · intro hv
    obtain ⟨_, ⟨x, hx, rfl⟩, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
    apply (mem_fourCommonModulo C D _).mpr
    refine ⟨fun k => C.add_mem hx (hDC ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))), ?_⟩
    intro k
    change (x + y k) - (x + y 0) ∈ D
    have he : (x + y k) - (x + y 0) = y k - y 0 := by abel
    rw [he]
    exact D.sub_mem ((Submodule.mem_pi.mp hy) k (Set.mem_univ k))
      ((Submodule.mem_pi.mp hy) 0 (Set.mem_univ 0))

theorem fourCommonGenerators_span (C D : Submodule R V) (hDC : D ≤ C)
    (c : Basis ι R C) (b : Basis κ R D) :
    Submodule.span R (Set.range (Sum.elim (fun i => fourDiagonalMap (R := R) (c i : V))
      (fourBasisVectors D b))) = fourCommonModulo C D := by
  rw [span_range_sumElim, fourBasisVectors_span, fourCommonModulo_eq_sup C D hDC]
  congr 1
  change Submodule.span R (Set.range ((fourDiagonalMap (R := R)).comp C.subtype ∘ c)) = _
  rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top,
    LinearMap.range_comp, Submodule.range_subtype]

end Erdos3

end

section

namespace Erdos3

open Module

variable {R V κ : Type*} [Field R] [AddCommGroup V] [Module R V]

def fourBalanceProjection : (Fin 4 → V) →ₗ[R] (Fin 4 → V) :=
  LinearMap.id + (LinearMap.single R (fun _ : Fin 4 => V) 3).comp (fourAlternatingMap (R := R))

theorem fourBalanceProjection_apply (v : Fin 4 → V) :
    fourBalanceProjection (R := R) v = ![v 0, v 1, v 2, v 0 + v 1 - v 2] := by
  ext k
  fin_cases k <;>
    simp [fourBalanceProjection, fourAlternatingMap_apply]

theorem fourBalanceProjection_image (D : Submodule R V) :
    (Submodule.pi Set.univ (fun _ : Fin 4 => D)).map (fourBalanceProjection (R := R)) =
      fourBalancedDependent D := by
  ext z
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h (k : Fin 4) : v k ∈ D := (Submodule.mem_pi.mp hv) k (Set.mem_univ k)
    apply (mem_fourBalancedDependent D _).mpr
    constructor
    · intro k
      rw [fourBalanceProjection_apply]
      fin_cases k
      · exact h 0
      · exact h 1
      · exact h 2
      · exact D.sub_mem (D.add_mem (h 0) (h 1)) (h 2)
    · rw [fourBalanceProjection_apply]
      dsimp
      abel
  · intro hz
    obtain ⟨hmem, hzero⟩ := (mem_fourBalancedDependent D z).mp hz
    refine ⟨z, Submodule.mem_pi.mpr (fun k _ => hmem k), ?_⟩
    change z + LinearMap.single R (fun _ : Fin 4 => V) 3 (fourAlternatingMap (R := R) z) = z
    rw [fourAlternatingMap_apply, hzero, map_zero, add_zero]

theorem fourBalancedGenerators_span (D : Submodule R V) (b : Basis κ R D) :
    Submodule.span R (Set.range ((fourBalanceProjection (R := R)) ∘ fourBasisVectors D b)) =
      fourBalancedDependent D := by
  rw [Set.range_comp, ← Submodule.map_span, fourBasisVectors_span]
  exact fourBalanceProjection_image D

end Erdos3

end

section

namespace Erdos3

open Module

theorem exists_bounded_four_annihilator
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (K : Submodule ℚ (Fin 4 → V)) (v : κ → Fin 4 → V)
    (hspan : Submodule.span ℚ (Set.range v) = K) {p : ℝ} (hp : 0 ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ a k i, rationalLogHeight (e.repr (v a k) i) ≤ p) :
    ∃ m : ℕ, m ≤ 4 * Fintype.card ι ∧ ∃ ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = K ∧
      ∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i)) j) ≤
        (p + 3) ^ 7 := by
  classical
  let b := Pi.basis (fun _ : Fin 4 => e)
  obtain ⟨H, _, hH, m, hm, f, hf⟩ := exists_submodule_quotient_basis_exp b K v hspan
    (one_le_ceil_exp p) (fun a i => rationalHeightLE_ceil_exp (hv a i.1 i.2))
    (by linarith : 0 ≤ p + 1) (hκ.trans (by linarith)) (ceil_exp_le_exp_add_one hp)
  let ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ) := f.equivFun.toLinearMap.comp K.mkQ
  have hker : LinearMap.ker ℓ = K := by
    ext x
    change f.equivFun (K.mkQ x) = 0 ↔ x ∈ K
    rw [f.equivFun.map_eq_zero_iff]
    exact Submodule.Quotient.mk_eq_zero K
  refine ⟨m, ?_, ℓ, f.equivFun.surjective.comp K.mkQ_surjective, hker, ?_⟩
  · simpa only [Fintype.card_sigma, Fintype.card_fin, Finset.sum_const,
      Finset.card_univ, smul_eq_mul] using hm
  · intro k i j
    have he : b ⟨k, i⟩ = LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i) := by
      simp only [b, Pi.basis_apply, LinearMap.single_apply]
    rw [← he]
    change rationalLogHeight (f.repr (K.mkQ (b ⟨k, i⟩)) j) ≤ _
    have h := rationalLogHeight_le_of_height (hf j ⟨k, i⟩) hH
    simpa only [show p + 1 + 2 = p + 3 by ring] using h

theorem fourPetalSpace_eq_inf_ker
    {R V E : Type*} [CommRing R] [AddCommGroup V] [Module R V]
    [AddCommGroup E] [Module R E] (D : Submodule R V)
    (K : Submodule R (Fin 4 → V)) (ℓ : (Fin 4 → V) →ₗ[R] E)
    (hℓ : LinearMap.ker ℓ = K) :
    fourPetalSpace D K = D ⊓ LinearMap.ker
      (ℓ.comp (LinearMap.single R (fun _ : Fin 4 => V) 0)) := by
  rw [LinearMap.ker_comp, hℓ]
  rfl

theorem exists_bounded_refined_four_annihilator
    {V ι κ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [Fintype κ]
    (e : Basis ι ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → V)) (v : κ → Fin 4 → V)
    (hspan : Submodule.span ℚ (Set.range v) = fourRefinedRelation C D K)
    {p : ℝ} (hp : 0 ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hv : ∀ a k i, rationalLogHeight (e.repr (v a k) i) ≤ p) :
    ∃ m : ℕ, m ≤ 4 * Fintype.card ι ∧ ∃ ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = fourRefinedRelation C D K ∧
      (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i)) j) ≤
        (p + 3) ^ 7) ∧
      (∀ x ∈ D, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
      (∀ z ∈ fourRefinedRelation C D K,
        ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
          ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) 0 (z 0 + z 1 - z 2 - z 3)) = 0) ∧
      fourPetalSpace D (fourRefinedRelation C D K) =
        D ⊓ LinearMap.ker (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) := by
  obtain ⟨m, hm, ℓ, hsurj, hker, hheight⟩ :=
    exists_bounded_four_annihilator e _ v hspan hp hκ hv
  have hzero (z) (hz : z ∈ fourRefinedRelation C D K) : ℓ z = 0 := by
    exact LinearMap.mem_ker.mp (hker.symm ▸ hz)
  refine ⟨m, hm, ℓ, hsurj, hker, hheight, ?_, ?_, fourPetalSpace_eq_inf_ker D _ ℓ hker⟩
  · exact fun x hx => four_annihilator_common_zero D ℓ
      (fun z hz => hzero z (fourBalancedDependent_le_refined C D K hz)) x hx
  · exact fun z hz => four_refined_annihilator_identity C D hDC K ℓ hzero z hz

end Erdos3

end

section

namespace Erdos3

open Module

variable {V μ ι κ : Type*} [AddCommGroup V] [Module ℚ V]

theorem fourBasisVectors_logHeight (e : Basis μ ℚ V) (D : Submodule ℚ V)
    (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (a : Σ _ : Fin 4, κ) (k : Fin 4) (i : μ) :
    rationalLogHeight (e.repr (fourBasisVectors D b a k) i) ≤ p := by
  classical
  rw [fourBasisVectors_apply, LinearMap.single_apply]
  by_cases h : k = a.1
  · rw [h, Pi.single_eq_same]
    exact hb a.2 i
  · rw [Pi.single_eq_of_ne h]
    simpa [rationalLogHeight] using hp

theorem fourBalancedGenerators_logHeight (e : Basis μ ℚ V) (D : Submodule ℚ V)
    (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (a : Σ _ : Fin 4, κ) (k : Fin 4) (i : μ) :
    rationalLogHeight (e.repr (fourBalanceProjection (R := ℚ) (fourBasisVectors D b a) k) i) ≤ p := by
  classical
  rcases a with ⟨a, j⟩
  rw [fourBasisVectors_apply, fourBalanceProjection_apply]
  fin_cases a <;> fin_cases k <;>
    first
    | simpa [LinearMap.single_apply, rationalLogHeight] using hb j i
    | simpa [LinearMap.single_apply, rationalLogHeight] using hp

theorem exists_fourCommonModulo_basis_logHeight [Fintype μ]
    (e : Basis μ ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (c : Basis ι ℚ C) (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p) :
    ∃ a : Basis (Fin (finrank ℚ (fourCommonModulo C D))) ℚ (fourCommonModulo C D),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (a j : Fin 4 → V) i) ≤ p := by
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 4 => e)) _
    (Sum.elim (fun i => fourDiagonalMap (R := ℚ) (c i : V)) (fourBasisVectors D b))
    (fourCommonGenerators_span C D hDC c b)
  intro a i
  cases a with
  | inl a => exact hc a i.2
  | inr a => exact fourBasisVectors_logHeight e D b hp hb a i.1 i.2

theorem exists_fourBalancedDependent_basis_logHeight [Fintype μ]
    (e : Basis μ ℚ V) (D : Submodule ℚ V) (b : Basis κ ℚ D) {p : ℝ} (hp : 0 ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p) :
    ∃ a : Basis (Fin (finrank ℚ (fourBalancedDependent D))) ℚ (fourBalancedDependent D),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (a j : Fin 4 → V) i) ≤ p := by
  apply exists_submodule_basis_of_spanning_logHeight (Pi.basis (fun _ : Fin 4 => e)) _
    ((fourBalanceProjection (R := ℚ)) ∘ fourBasisVectors D b) (fourBalancedGenerators_span D b)
  intro a i
  exact fourBalancedGenerators_logHeight e D b hp hb a i.1 i.2

end Erdos3

end

section

namespace Erdos3

open Module

noncomputable def fourRefinementBasisBudget (p : ℝ) : ℝ :=
  p + preimageBasisBudget (4 * p)

noncomputable def fourRefinementAnnihilatorBudget (p : ℝ) : ℝ :=
  (4 * p + fourRefinementBasisBudget p + 3) ^ 7

theorem fourRefinementBasisBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ fourRefinementBasisBudget p :=
  add_nonneg hp (preimageBasisBudget_nonneg (by positivity))

theorem fourRefinementAnnihilatorBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ fourRefinementAnnihilatorBudget p := by
  have h := fourRefinementBasisBudget_nonneg hp
  unfold fourRefinementAnnihilatorBudget
  positivity

variable {V μ : Type*} [AddCommGroup V] [Module ℚ V] [Fintype μ]

theorem four_submodule_finrank_le (e : Basis μ ℚ V)
    (U : Submodule ℚ (Fin 4 → V)) : finrank ℚ U ≤ 4 * Fintype.card μ := by
  let e4 := Pi.basis (fun _ : Fin 4 => e)
  let : FiniteDimensional ℚ (Fin 4 → V) := e4.finiteDimensional_of_finite
  calc
    finrank ℚ U ≤ finrank ℚ (Fin 4 → V) := U.finrank_le
    _ = Fintype.card (Σ _ : Fin 4, μ) := finrank_eq_card_basis e4
    _ = 4 * Fintype.card μ := by simp

theorem exists_fourRefinedRelation_basis_logHeight
    (e : Basis μ ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → V))
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (b : Basis (Fin (finrank ℚ D)) ℚ D)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i,
      rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ a : Basis (Fin (finrank ℚ (fourRefinedRelation C D K))) ℚ (fourRefinedRelation C D K),
      ∀ j i, rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr
        (a j : Fin 4 → V) i) ≤ fourRefinementBasisBudget p := by
  classical
  let e4 := Pi.basis (fun _ : Fin 4 => e)
  have hspan (U : Submodule ℚ (Fin 4 → V)) (a : Basis (Fin (finrank ℚ U)) ℚ U) :
      Submodule.span ℚ (Set.range (fun j => (a j : Fin 4 → V))) = U := by
    change Submodule.span ℚ (Set.range (U.subtype ∘ a)) = U
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hdim4 : (Fintype.card (Σ _ : Fin 4, μ) : ℝ) ≤ 4 * p := by
    simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  have hcard (U : Submodule ℚ (Fin 4 → V)) :
      (Fintype.card (Fin (finrank ℚ U)) : ℝ) ≤ 4 * p := by
    have h := (Nat.cast_le (α := ℝ)).mpr (four_submodule_finrank_le e U)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    simpa using h.trans (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  have hp4 : p ≤ 4 * p := by linarith
  obtain ⟨s, hs⟩ := exists_fourCommonModulo_basis_logHeight e C D hDC c b hp hc hb
  have hu := exists_preimage_basis_logHeight e4 e4 K (fourCommonModulo C D)
    LinearMap.id (fun j => (k j : Fin 4 → V)) (fun j => (s j : Fin 4 → V))
    (hspan K k) (hspan _ s) (by positivity : 0 ≤ 4 * p) hdim4 (hcard K) (hcard _)
    (fun a i => (hk a i).trans hp4) (fun a i => (hs a i).trans hp4)
    (fun a i => (hk a i).trans hp4)
  obtain ⟨u, hu⟩ := hu
  obtain ⟨v, hv⟩ := exists_fourBalancedDependent_basis_logHeight e D b hp hb
  have hsum : Submodule.span ℚ (Set.range (Sum.elim
      (fun j => (u j : Fin 4 → V)) (fun j => (v j : Fin 4 → V)))) =
      fourRefinedRelation C D K := by
    rw [span_range_sumElim, hspan _ u, hspan _ v]
    rfl
  apply exists_submodule_basis_of_spanning_logHeight e4 _ _ hsum
  intro a i
  cases a with
  | inl a => exact (hu a i).trans (le_add_of_nonneg_left hp)
  | inr a =>
    exact (hv a i).trans
      (le_add_of_nonneg_right (preimageBasisBudget_nonneg (by positivity)))

theorem exists_fourRefinedRelation_annihilator
    (e : Basis μ ℚ V) (C D : Submodule ℚ V) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → V))
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (b : Basis (Fin (finrank ℚ D)) ℚ D)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : V) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : V) i) ≤ p)
    (hk : ∀ a i,
      rationalLogHeight ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → V) i) ≤ p) :
    ∃ m : ℕ, m ≤ 4 * Fintype.card μ ∧ ∃ ℓ : (Fin 4 → V) →ₗ[ℚ] (Fin m → ℚ),
      Function.Surjective ℓ ∧ LinearMap.ker ℓ = fourRefinedRelation C D K ∧
      (∀ k i j, rationalLogHeight (ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) k (e i)) j) ≤
        fourRefinementAnnihilatorBudget p) ∧
      (∀ x ∈ D, ℓ (fourDiagonalMap (R := ℚ) x) = 0) ∧
      (∀ z ∈ fourRefinedRelation C D K,
        ℓ (fourDiagonalMap (R := ℚ) (z 0)) +
          ℓ (LinearMap.single ℚ (fun _ : Fin 4 => V) 0 (z 0 + z 1 - z 2 - z 3)) = 0) ∧
      fourPetalSpace D (fourRefinedRelation C D K) =
        D ⊓ LinearMap.ker (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) := by
  obtain ⟨a, ha⟩ := exists_fourRefinedRelation_basis_logHeight e C D hDC K c b k hp hdim hc hb hk
  have hspan : Submodule.span ℚ (Set.range (fun j => (a j : Fin 4 → V))) =
      fourRefinedRelation C D K := by
    change Submodule.span ℚ (Set.range ((fourRefinedRelation C D K).subtype ∘ a)) = _
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hB := fourRefinementBasisBudget_nonneg hp
  have hcard : (Fintype.card (Fin (finrank ℚ (fourRefinedRelation C D K))) : ℝ) ≤
      4 * p + fourRefinementBasisBudget p := by
    have h := (Nat.cast_le (α := ℝ)).mpr (four_submodule_finrank_le e (fourRefinedRelation C D K))
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    simpa using (h.trans (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))).trans
      (le_add_of_nonneg_right hB)
  exact exists_bounded_refined_four_annihilator e C D hDC K (fun j => (a j : Fin 4 → V))
    hspan (by positivity) hcard
    (fun j k i => (ha j ⟨k, i⟩).trans (le_add_of_nonneg_left (by positivity)))

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

theorem exists_fourRefinedRelation_correction
    {L μ σ : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype μ]
    (e : Basis μ ℚ L) (C D : Submodule ℚ L) (hDC : D ≤ C)
    (K : Submodule ℚ (Fin 4 → L))
    (c : Basis (Fin (finrank ℚ C)) ℚ C) (b : Basis (Fin (finrank ℚ D)) ℚ D)
    (k : Basis (Fin (finrank ℚ K)) ℚ K) {p : ℝ} (hp : 0 ≤ p)
    (hdim : (Fintype.card μ : ℝ) ≤ p)
    (hc : ∀ a i, rationalLogHeight (e.repr (c a : L) i) ≤ p)
    (hb : ∀ a i, rationalLogHeight (e.repr (b a : L) i) ≤ p)
    (hk : ∀ a i, rationalLogHeight
      ((Pi.basis (fun _ : Fin 4 => e)).repr (k a : Fin 4 → L) i) ≤ p)
    (l : ℕ) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget (8 * p + 1)) ≤ T i) :
    let q := 8 * p + 1
    let B := ((Pi.basis (fun _ : Fin 4 => e)).baseChange ℝ).equivFun
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp (q + ((q + 2) ^ 3 + (q + 2) ^ 36)) ∧
      l ∣ m ∧ ∀ (α : σ →₀ ℕ), α ≠ 0 → ∀ (x u v : ℝ ⊗[ℚ] (Fin 4 → L)),
        x - u - v ∈ K.baseChange ℝ → x ∈ (fourCommonModulo C D).baseChange ℝ →
        ‖B u‖ ≤ Real.exp q / monomialScale T α → B v ∈ realDenominatorGrid l →
        ∃ E Q : ℝ ⊗[ℚ] (Fin 4 → L),
          ‖B E‖ ≤ (Real.exp q + Real.exp ((q + 2) ^ 3 + (q + 2) ^ 18 + q)) /
            monomialScale T α ∧ B Q ∈ realDenominatorGrid m ∧
          x - E - Q ∈ (fourRefinedRelation C D K).baseChange ℝ := by
  intro q B
  classical
  let e4 := Pi.basis (fun _ : Fin 4 => e)
  obtain ⟨a, ha⟩ := exists_fourCommonModulo_basis_logHeight e C D hDC c b hp hc hb
  have hdim4 : (Fintype.card (Σ _ : Fin 4, μ) : ℝ) ≤ 4 * p := by
    simpa using mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4)
  have hcard (U : Submodule ℚ (Fin 4 → L)) :
      (finrank ℚ U : ℝ) ≤ 4 * p := by
    have h := (Nat.cast_le (α := ℝ)).mpr (four_submodule_finrank_le e U)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    exact h.trans (mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 4))
  have hcols : (Fintype.card
      (Fin (finrank ℚ K) ⊕ Fin (finrank ℚ (fourCommonModulo C D))) : ℝ) ≤ q := by
    simp only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add]
    have hK := hcard K
    have hS := hcard (fourCommonModulo C D)
    dsimp only [q]
    linarith
  have hpq : p ≤ q := by dsimp only [q]; linarith
  have hHp : (⌈Real.exp p⌉₊ : ℝ) ≤ Real.exp q :=
    (ceil_exp_le_exp_add_one hp).trans (Real.exp_le_exp.mpr (by dsimp only [q]; linarith))
  have hkspan : Submodule.span ℚ (Set.range (fun j => (k j : Fin 4 → L))) = K := by
    change Submodule.span ℚ (Set.range (K.subtype ∘ k)) = K
    rw [Set.range_comp, ← Submodule.map_span, k.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have haspan : Submodule.span ℚ (Set.range (fun j => (a j : Fin 4 → L))) =
      fourCommonModulo C D := by
    change Submodule.span ℚ (Set.range ((fourCommonModulo C D).subtype ∘ a)) = _
    rw [Set.range_comp, ← Submodule.map_span, a.span_eq, Submodule.map_top,
      Submodule.range_subtype]
  have hkH : ∀ j i, RationalHeightLE (e4.repr (k j : Fin 4 → L) i) ⌈Real.exp p⌉₊ :=
    fun j i => rationalHeightLE_ceil_exp (hk j i)
  have haH : ∀ j i, RationalHeightLE (e4.repr (a j : Fin 4 → L) i) ⌈Real.exp p⌉₊ :=
    fun j i => rationalHeightLE_ceil_exp (ha j i)
  have hdimq : (Fintype.card (Σ _ : Fin 4, μ) : ℝ) ≤ q :=
    hdim4.trans (by dsimp only [q]; linarith)
  have hlq : (l : ℝ) ≤ Real.exp q := hlp.trans (Real.exp_le_exp.mpr hpq)
  obtain ⟨m, hm, hmp, hlm, hsolve⟩ := exists_basis_intersection_correction
    (μ := Σ _ : Fin 4, μ) (κ := Fin (finrank ℚ K))
    (ν := Fin (finrank ℚ (fourCommonModulo C D))) (σ := σ) (L := Fin 4 → L)
    (H := ⌈Real.exp p⌉₊) (p := q) (l := l) e4 K
    (fourCommonModulo C D) (fun j => (k j : Fin 4 → L)) (fun j => (a j : Fin 4 → L))
    hkspan haspan (one_le_ceil_exp p) hl hkH haH
    (hp.trans hpq) hdimq hcols hHp hlq T hT
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α hα x u v hx hS hu hv
  obtain ⟨E, Q, hE, hQ, hmem⟩ := hsolve α hα x u v hx hS hu hv
  exact ⟨E, Q, hE, hQ, Submodule.baseChange_mono ℝ
    (show K ⊓ fourCommonModulo C D ≤ fourRefinedRelation C D K from le_sup_left) hmem⟩

end Erdos3

end

section

namespace Erdos3

def coefficientFourHeightBudget (p : ℝ) : ℝ := p + refiltrationCoordinateBudget p + 2

theorem coefficientFourHeightBudget_nonneg {p : ℝ} (hp : 0 ≤ p) :
    0 ≤ coefficientFourHeightBudget p := by
  have h := refiltrationCoordinateBudget_nonneg hp
  unfold coefficientFourHeightBudget
  linarith

namespace NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem exists_coefficientFour_generators (hs : 2 ≤ s) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) :
    ∃ v : Fin (Fintype.card (Σ _ : Fin 4, Fin W.dim)) → (Fin 4 → W.L),
      Submodule.span ℚ (Set.range v) = D.coefficientFourSpace d ∧
      ∀ a j, rationalLogHeight (W.fourRankBasis.repr (v a) j) ≤ coefficientFourHeightBudget P := by
  classical
  obtain ⟨v, hv, hvH⟩ := (mem_heightBoundedSubspaces W.fourRankBasis _ _ _).mp
    (D.spaces_mem_candidates hP d)
  let K := W.rank.filtration.layer d.val 2
  let e := W.rank.basis d ⟨2, by omega⟩
  let φ : (Fin 4 → K) →ₗ[ℚ] (Fin 4 → W.L) :=
    LinearMap.pi (fun k => K.subtype.comp (LinearMap.proj k))
  let u : (Σ _ : Fin 4, Fin (finrank ℚ K)) → (Fin 4 → W.L) :=
    φ ∘ Pi.basis (fun _ : Fin 4 => e)
  have hu : Submodule.span ℚ (Set.range u) = Submodule.pi Set.univ (fun _ : Fin 4 => K) := by
    rw [show u = φ ∘ Pi.basis (fun _ : Fin 4 => e) from rfl, Set.range_comp,
      ← Submodule.map_span, (Pi.basis (fun _ : Fin 4 => e)).span_eq, Submodule.map_top]
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact Submodule.mem_pi.mpr (fun k _ => (y k).property)
    · intro hx
      exact ⟨fun k => ⟨x k, (Submodule.mem_pi.mp hx) k (Set.mem_univ k)⟩, rfl⟩
  let Q := P + refiltrationCoordinateBudget P + 1
  have hcost := refiltrationCoordinateBudget_nonneg hP
  have hQ : 0 ≤ Q := by dsimp only [Q]; linarith
  have hPQ : P ≤ Q := by dsimp only [Q]; linarith
  have hvQ (a) (j) : rationalLogHeight (W.fourRankBasis.repr (v a) j) ≤ Q := by
    have h := rationalLogHeight_le_of_height (hvH a j) (ceil_exp_le_exp_add_one hcost)
    exact h.trans (by dsimp only [Q]; linarith)
  have huQ (a) (j) : rationalLogHeight (W.fourRankBasis.repr (u a) j) ≤ Q := by
    rw [NativeDegreeRankFamily.fourRankBasis, Pi.basis_repr]
    change rationalLogHeight (W.model.basis.repr
      ((Pi.basis (fun _ : Fin 4 => e) a j.1 : K) : W.L) j.2) ≤ Q
    rw [Pi.basis_apply]
    by_cases hja : j.1 = a.1
    · rw [hja, Pi.single_eq_same]
      exact ((W.complexity.mono W.rank hbP).2 d ⟨2, by omega⟩ a.2 j.2).trans hPQ
    · rw [Pi.single_eq_of_ne hja]
      simpa [rationalLogHeight] using hQ
  have hspan : Submodule.span ℚ (Set.range (Sum.elim v u)) = D.coefficientFourSpace d := by
    rw [span_range_sumElim, hv, hu, D.coefficientFourSpace_eq_sup]
  obtain ⟨z, hz, hzH⟩ := exists_bounded_submodule_ambient_spanning W.fourRankBasis
    (D.coefficientFourSpace d) (Sum.elim v u) hspan (one_le_ceil_exp Q)
    (fun a j => rationalHeightLE_ceil_exp (by
      cases a with
      | inl a => exact hvQ a j
      | inr a => exact huQ a j))
  refine ⟨z, hz, fun a j => ?_⟩
  have h := rationalLogHeight_le_of_height (hzH a j) (ceil_exp_le_exp_add_one hQ)
  simpa only [Q, coefficientFourHeightBudget, add_assoc, one_add_one_eq_two] using h

theorem exists_coefficientFour_basis (hs : 2 ≤ s) (hP : 0 ≤ P) (hbP : b ≤ P)
    (d : Fin (s + 1)) :
    ∃ e : Basis (Fin (finrank ℚ (D.coefficientFourSpace d))) ℚ (D.coefficientFourSpace d),
      ∀ a j, rationalLogHeight (W.fourRankBasis.repr (e a : Fin 4 → W.L) j) ≤
        coefficientFourHeightBudget P := by
  classical
  let : FiniteDimensional ℚ (Fin 4 → W.L) := W.fourRankBasis.finiteDimensional_of_finite
  obtain ⟨v, hv, hvH⟩ := D.exists_coefficientFour_generators hs hP hbP d
  have hex := Submodule.exists_fun_fin_finrank_span_eq ℚ (Set.range v)
  rw [hv] at hex
  obtain ⟨z, hz, hzspan, hzli⟩ := hex
  refine ⟨(Basis.span hzli).map (LinearEquiv.ofEq _ _ hzspan), ?_⟩
  intro a j
  simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.coe_span_apply]
  obtain ⟨k, hk⟩ := hz a
  rw [← hk]
  exact hvH k j

end NativeRankRelation.CommonData
end Erdos3

end

section

namespace Erdos3

namespace NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff NativeIntegerExpansion.lie NativeIntegerExpansion.algebra NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

end NativeRankRelation.CommonData
end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedRefinementBudget
namespace OAI

section

namespace Erdos3

def sharedRefinementInputBudget (s : ℕ) (p : ℝ) : ℝ :=
  let B := (p + 2) ^ 3 + 2 * p
  p + coefficientFourHeightBudget B + ((B + 3) ^ 2 + (s : ℝ) * p) + ((p + 2) ^ 3 + p)

theorem sharedRefinementInputBudget_bounds (s : ℕ) {p : ℝ} (hp : 0 ≤ p) :
    let B := (p + 2) ^ 3 + 2 * p
    let A := sharedRefinementInputBudget s p
    0 ≤ B ∧ p ≤ B ∧ 0 ≤ A ∧ p ≤ A ∧ coefficientFourHeightBudget B ≤ A ∧
      (B + 3) ^ 2 + (s : ℝ) * p ≤ A ∧ (p + 2) ^ 3 + p ≤ A := by
  intro B A
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hpB : p ≤ B := by dsimp only [B]; nlinarith [sq_nonneg (p + 2)]
  have hH := coefficientFourHeightBudget_nonneg hB
  have hE : 0 ≤ (B + 3) ^ 2 + (s : ℝ) * p := by positivity
  have hL : 0 ≤ (p + 2) ^ 3 + p := by positivity
  have hA : A = p + coefficientFourHeightBudget B + ((B + 3) ^ 2 + (s : ℝ) * p) +
      ((p + 2) ^ 3 + p) := rfl
  refine ⟨hB, hpB, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourAnnihilatorKernel
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem mem_realified_coordinate_kernel_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔
      ∀ j, realifyFunctional ((LinearMap.proj j).comp ℓ) x = 0 := by
  have hker : LinearMap.ker ℓ = ⨅ j, LinearMap.ker ((LinearMap.proj j).comp ℓ) := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_iInf, LinearMap.comp_apply, LinearMap.proj_apply]
    exact funext_iff
  rw [hker, real_baseChange_iInf]
  simp only [Submodule.mem_iInf, mem_realified_frequency_kernel_iff]

theorem mem_real_petal_annihilator_iff
    {V J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype J]
    (D : Submodule ℚ V) (K : Submodule ℚ (Fin 4 → V))
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (hker : LinearMap.ker ℓ = K)
    (v : ℝ ⊗[ℚ] V) :
    v ∈ (fourPetalSpace D K).baseChange ℝ ↔
      v ∈ D.baseChange ℝ ∧ ∀ j, realifyFunctional
        (((LinearMap.proj j).comp ℓ).comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0)) v = 0 := by
  rw [fourPetalSpace_eq_inf_ker D K ℓ hker, realification_inf, Submodule.mem_inf,
    mem_realified_coordinate_kernel_iff]
  rfl

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealAnnihilatorCorrections
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {V I J : Type*} [AddCommGroup V] [Module ℚ V] [Fintype I] [Fintype J]

theorem mem_realified_coordinate_kernel_iff_eq_zero
    (ℓ : V →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    x ∈ (LinearMap.ker ℓ).baseChange ℝ ↔ realifyCoordinateMap ℓ x = 0 := by
  rw [mem_realified_coordinate_kernel_iff]
  exact ⟨fun h => funext h, fun h j => congrFun h j⟩

theorem exists_real_annihilator_correction
    (b : Basis I ℚ V) (ℓ : V →ₗ[ℚ] (J → ℚ)) {H l : ℕ} {p : ℝ}
    (hℓ : ∀ j i, RationalHeightLE (ℓ (b i) j) H) (hp : 0 ≤ p)
    (hI : (Fintype.card I : ℝ) ≤ p) (hJ : (Fintype.card J : ℝ) ≤ p)
    (hH : (H : ℝ) ≤ Real.exp p) (hl : 0 < l) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 4) ∧ l ∣ m ∧
      ∀ (x E Q : ℝ ⊗[ℚ] V) (ε : ℝ),
        x - E - Q ∈ (LinearMap.ker ℓ).baseChange ℝ →
        ‖(b.baseChange ℝ).equivFun E‖ ≤ ε →
        (b.baseChange ℝ).equivFun Q ∈ realDenominatorGrid l →
        ∃ q ∈ realDenominatorGrid m,
          ‖realifyCoordinateMap ℓ x - q‖ ≤ Real.exp ((p + 2) ^ 3) * ε := by
  let A := coordinateFunctionalMatrix b ℓ
  have hm := matrixDenominator_allowance_le_exp A l H hℓ hp hJ hI hH hlp
  rw [Nat.mul_comm l] at hm
  refine ⟨matrixDenominator A * l, Nat.mul_pos (matrixDenominator_pos A) hl, hm,
    ⟨matrixDenominator A, Nat.mul_comm _ _⟩, ?_⟩
  intro x E Q ε hker hE hQ
  refine ⟨realifyCoordinateMap ℓ Q, realifyCoordinateMap_grid b ℓ l Q hQ, ?_⟩
  have hz := (mem_realified_coordinate_kernel_iff_eq_zero ℓ _).mp hker
  rw [map_sub, map_sub] at hz
  have heq : realifyCoordinateMap ℓ x - realifyCoordinateMap ℓ Q =
      realifyCoordinateMap ℓ E := by
    calc
      _ = (realifyCoordinateMap ℓ x - realifyCoordinateMap ℓ E -
          realifyCoordinateMap ℓ Q) + realifyCoordinateMap ℓ E := by abel
      _ = _ := by rw [hz, zero_add]
  rw [heq]
  have hfac : ((Fintype.card I : ℝ) + 1) * (H + 1) ≤ Real.exp ((p + 2) ^ 3) := by
    calc
      _ ≤ ((Fintype.card I : ℝ) + 1) * (Real.exp ((p + 2) ^ 1) + 1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hHp : (H : ℝ) ≤ Real.exp ((p + 2) ^ 1) :=
          hH.trans (Real.exp_le_exp.mpr (by rw [pow_one]; linarith))
        linarith
      _ ≤ _ := matrix_weighted_factor_le_exp_power (Fintype.card I) hp hI 1 (by decide)
  exact (realifyCoordinateMap_norm_bound b ℓ hℓ E).trans
    ((mul_le_mul_of_nonneg_right hfac (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hE (Real.exp_nonneg _)))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealFourBalancedDual
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

variable {V J : Type*} [AddCommGroup V] [Module ℚ V]

noncomputable def realFourCoordinateMap (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) :
    (Fin 4 → ℝ ⊗[ℚ] V) →ₗ[ℝ] (J → ℝ) :=
  (realifyCoordinateMap ℓ).comp
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm.toLinearMap

theorem real_four_diagonal (x : ℝ ⊗[ℚ] V) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V))
        ((fourDiagonalMap (R := ℚ)).baseChange ℝ x) =
      fourDiagonalMap (R := ℝ) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realFourCoordinateMap_diagonal
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (x : ℝ ⊗[ℚ] V) :
    realFourCoordinateMap ℓ (fourDiagonalMap (R := ℝ) x) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) x := by
  change realifyCoordinateMap ℓ
    ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm _) = _
  rw [← real_four_diagonal, LinearEquiv.symm_apply_apply, realifyCoordinateMap_comp]

theorem realFourCoordinateMap_single
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ)) (k : Fin 4) (x : ℝ ⊗[ℚ] V) :
    realFourCoordinateMap ℓ (LinearMap.single ℝ (fun _ : Fin 4 => ℝ ⊗[ℚ] V) k x) =
      realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) k)) x := by
  change realifyCoordinateMap ℓ
    ((TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => V)).symm _) = _
  rw [← real_four_single, LinearEquiv.symm_apply_apply, realifyCoordinateMap_comp]

variable [Fintype J]

theorem realFourCoordinateMap_decomposition (C D : Submodule ℚ V)
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (v : Fin 4 → ℝ ⊗[ℚ] V) (hv : v ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ)) :
    realFourCoordinateMap ℓ v =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) (v 0) +
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (v 0 + v 1 - v 2 - v 3) := by
  have hzero (z) (hz : z ∈ fourBalancedDependent (D.baseChange ℝ)) :
      realFourCoordinateMap ℓ z = 0 := by
    rw [← realification_fourBalancedDependent] at hz
    have hmem := (Submodule.mem_map_equiv _).mp hz
    exact (mem_realified_coordinate_kernel_iff_eq_zero ℓ _).mp
      (Submodule.baseChange_mono ℝ hℓ hmem)
  have h := four_annihilator_decomposition (C.baseChange ℝ) (D.baseChange ℝ)
    (realFourCoordinateMap ℓ) hzero v hv
  simpa only [realFourCoordinateMap_diagonal, realFourCoordinateMap_single,
    fourAlternatingMap_apply] using h

theorem realFourCoordinateMap_shared_decomposition (C D : Submodule ℚ V) (hDC : D ≤ C)
    (ℓ : (Fin 4 → V) →ₗ[ℚ] (J → ℚ))
    (hℓ : fourBalancedDependent D ≤ LinearMap.ker ℓ)
    (c : ℝ ⊗[ℚ] V) (hc : c ∈ C.baseChange ℝ)
    (v : Fin 4 → ℝ ⊗[ℚ] V) (hv : ∀ k, v k ∈ D.baseChange ℝ) :
    realFourCoordinateMap ℓ (fun k => c + v k) =
      realifyCoordinateMap (ℓ.comp (fourDiagonalMap (R := ℚ))) c +
        realifyCoordinateMap (ℓ.comp (LinearMap.single ℚ (fun _ : Fin 4 => V) 0))
          (v 0 + v 1 - v 2 - v 3) := by
  have hmem : (fun k => c + v k) ∈ fourCommonModulo (C.baseChange ℝ) (D.baseChange ℝ) := by
    apply (mem_fourCommonModulo _ _ _).mpr
    refine ⟨fun k => (C.baseChange ℝ).add_mem hc
      (Submodule.baseChange_mono ℝ hDC (hv k)), ?_⟩
    intro k
    rw [add_sub_add_left_eq_sub]
    exact (D.baseChange ℝ).sub_mem (hv k) (hv 0)
  have hdiag : D ≤ LinearMap.ker (ℓ.comp (fourDiagonalMap (R := ℚ))) := by
    intro x hx
    exact four_annihilator_common_zero D ℓ (fun z hz => hℓ hz) x hx
  have hz := (mem_realified_coordinate_kernel_iff_eq_zero
    (ℓ.comp (fourDiagonalMap (R := ℚ))) (v 0)).mp
      (Submodule.baseChange_mono ℝ hdiag (hv 0))
  have halt : (c + v 0) + (c + v 1) - (c + v 2) - (c + v 3) =
      v 0 + v 1 - v 2 - v 3 := by abel
  have h := realFourCoordinateMap_decomposition C D ℓ hℓ (fun k => c + v k) hmem
  rw [halt, map_add, hz, add_zero] at h
  exact h

end Erdos3

end

end OAI

end


