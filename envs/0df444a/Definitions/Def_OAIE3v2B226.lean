-- Prove2me | Definitions.Def_OAIE3v2B226
-- name    : OAIE3v2B226
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:46:43.485303+00:00
-- url     : https://prove2.me/theorems/2bdb3b59-4d3c-4ae5-a7f7-d4421297d312
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 231 of 311
-- statement:
--   Definitions bundle 231 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B198`, `OAIE3v2B199`, `OAIE3v2B203`, `OAIE3v2B205`, `OAIE3v2B206`, `OAIE3v2B207`, `OAIE3v2B210` of this split.
--
--   Modules: `Dynamics/SharedFreeCorrelationBudget.lean`, `Dynamics/SharedFreeLowerComparisonBudget.lean`, `Estimates/AntisymmetricPairVerticalModel.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/FreeCorrelationRelationRefinement.lean`, `Estimates/MixedPairComparison.lean`, `Estimates/NativeSubspaceFreeModel.lean`, `Estimates/OriginalMixedRootEquivalence.lean`, `Estimates/QuadraticPairCorrelator.lean`, `Estimates/QuadraticPairStepDrop.lean`, `Estimates/RationalTaggedConstraintHistory.lean`, `Estimates/SharedFreeComparisonLift.lean`, `Estimates/SharedFreeComparisonOrbit.lean`, `Geometry/BoundedCertifiedFullChartMajorIteration.lean`, `Geometry/CertifiedFullChartBudgetedTreeBounds.lean`, `Geometry/CertifiedFullChartForwardEarlyTree.lean`, `Geometry/FullChartHomogeneousCorrection.lean`, `Geometry/FullTaggedChartCoefficientRange.lean`, `Geometry/TerminalChartSlowEvaluation.lean`, `Lattices/PrimeStabilityTree.lean`, `Linear/AntisymmetricPairProjections.lean`, `Linear/BinaryLowerRankFamily.lean`, `Linear/CommonFreeSpanBounds.lean`, `Linear/NativeCoefficientKernel.lean`, `Linear/RealCoefficientKernel.lean`, `Nilpotent/AntisymmetricPairNiltest.lean`, `Polynomial/AntisymmetricPairPolynomial.lean`, `Polynomial/FullChartPolynomialLiftControl.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B198
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B203
import Definitions.Def_OAIE3v2B205
import Definitions.Def_OAIE3v2B206
import Definitions.Def_OAIE3v2B207
import Definitions.Def_OAIE3v2B210

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.NativeCoefficientKernel
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

namespace NativeRankInterval.SunflowerWitness

variable {κ : Type*} {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {t : ZMod N × ZMod N × ZMod N} {branch : Bool}
  {I : NativeRankInterval W out H t branch p q} (D : I.SunflowerWitness P)

theorem projectedOrbitCoefficient_native_log_mod_kernel
    (hs : 1 ≤ s) (c : Basis κ ℚ W.L) (τ : κ → ℕ)
    (hG : ∀ j, W.rank.filtration.associatedDegree.layer j =
      Submodule.span ℚ (c '' {i | j ≤ τ i})) (α : Unit →₀ ℕ) (k : Fin 4) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) (D.projectedOrbitCoefficient α).val k -
      coefficients (W.orbit (rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k))).log α ∈
        (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 2).baseChange ℝ := by
  let a := rankQuadrupleParameters t ((![1, 2, 0, 3] : Fin 4 → Fin 4) k)
  let v := W.rank.filtration.realFourLayerComponent (Finsupp.weight (fun _ : Unit => 1) α) k
    (D.projectedOrbitCoefficient α)
  let z : (W.rank.filtration.layer (Finsupp.weight (fun _ : Unit => 1) α) 1).baseChange ℝ :=
    ⟨coefficients (W.orbit a).log α, W.logCoefficient_mem_rank_one α a⟩
  have heq : W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) v =
      W.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) α) z :=
    (W.rank.filtration.realFourLayerComponent_horizontal _ k (D.projectedOrbitCoefficient α)).symm.trans
      ((D.projectedOrbitCoefficient_native_component hs c τ hG α k).trans
        (W.horizontalCoefficient_real_log hs c τ hG α a z rfl))
  have h := (W.rank.filtration.realHorizontalMap_eq _ v z).mp heq
  simpa only [v, z, a, W.rank.filtration.realFourLayerComponent_coe, real_four_projection] using h

end NativeRankInterval.SunflowerWitness
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)

theorem mem_coefficientFourSpace (d : Fin (s + 1))
    (v : W.rank.filtration.fourHorizontalLayer d.val) :
    v.val ∈ D.coefficientFourSpace d ↔
      W.rank.filtration.fourHorizontalMap d.val v ∈ D.horizontal d := by
  constructor
  · rintro ⟨w, hw, he⟩
    have h : w = v := Subtype.ext he
    exact h ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CommonFreeSpanBounds
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

variable {s r N : ℕ} [NeZero N] {b p q P : ℝ}
  {W : NativeDegreeRankFamily s r (ZMod N) b} {out : Fin W.outputDim}
  {H : Finset (ZMod N)} {R : NativeRankRelation W out H p q} (D : R.CommonData P)
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_dependentFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.dependentFreeSpan d))) ℚ (D.dependentFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q :=
  exists_submodule_basis_of_spanning_logHeight e _
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩)) rfl
    (fun a i => F.generator_height hs (Sum.inr ⟨d, a⟩) i)

theorem exists_coefficientFreeSpan_basis (hs : 1 ≤ s) (d : Fin s) :
    ∃ c : Basis (Fin (finrank ℚ (D.coefficientFreeSpan d))) ℚ (D.coefficientFreeSpan d),
      ∀ a i, rationalLogHeight (e.repr (c a : D.CoefficientFreeLieAlgebra) i) ≤ Q := by
  let v := Sum.elim (fun a => D.coefficientFreeGenerator (Sum.inl ⟨d, a⟩))
    (fun a => D.coefficientFreeGenerator (Sum.inr ⟨d, a⟩))
  have hspan : Submodule.span ℚ (Set.range v) = D.coefficientFreeSpan d := by
    dsimp only [v]
    rw [span_range_sumElim]
    rfl
  apply exists_submodule_basis_of_spanning_logHeight e _ v hspan
  intro a i
  cases a with
  | inl a => exact F.generator_height hs (Sum.inl ⟨d, a⟩) i
  | inr a => exact F.generator_height hs (Sum.inr ⟨d, a⟩) i

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BinaryLowerRankFamily
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem HasLowerRankOrbitFamily.mono {L I σ τ : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {w : σ → ℕ} {f : τ → I → (σ → ℤ) → ℂ} {p q : ℝ}
    (h : D.HasLowerRankOrbitFamily R w f p) (hpq : p ≤ q) :
    D.HasLowerRankOrbitFamily R w f q := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc.mono U hpq, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, hKe⟩ := hK
  exact ⟨K, hKn, (fun i => (hKc i).mono hpq), hKu, a, ha0, hKe⟩

theorem exists_lower_rank_product_family {ι σ τ : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] {L : ι → Type*}
    [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {I : ι → Type*} [∀ i, Fintype (I i)]
    {s r : ℕ} {d : ι → ℕ}
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (R : ∀ i, (D i).DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f : ∀ i, τ → I i → (σ → ℤ) → ℂ) {p : ℝ}
    (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (h : ∀ i, (D i).HasLowerRankOrbitFamily (R i) w (f i) p) :
    ∃ n : ι → ℕ, (∀ i, n i ≤ d i) ∧
      ∃ Q : ∀ i, RationalFilteredNilmanifold (L i ⧸ (R i).filtration.layerIdeal s (r + 1)) s (n i),
        ∃ U : ∀ i, (Q i).DegreeRankStructure r,
          (piRank Q U).ComplexityLE (productNiltestBudget p) ∧
          (letI : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun _ => moduleTopology ℝ _
           letI : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun _ => IsModuleTopology.topologicalAddGroup ℝ _
           letI : ∀ i, T2Space (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             fun i => realification_moduleTopology_t2 (Q i).basis
           letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1)))
           letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
             IsModuleTopology.topologicalAddGroup ℝ _
           letI := realification_moduleTopology_t2 (pi Q).basis
           ∃ K : (∀ i, I i) → (pi Q).Niltest w,
             (∀ j, (K j).normBound = 1) ∧
             (∀ j, (K j).ComplexityLE (productNiltestBudget p)) ∧
             (∀ x, ∑ j, ‖(K j).observable x‖ ^ 2 = 1) ∧
             ∃ a : τ → (pi Q).filtration.realification.PolynomialOrbit w,
               (∀ t, (pi Q).filtration.realification.polynomialOrbitEval w 0 (a t) = 1) ∧
               ∀ t j x, ((K j).withOrbit (a t)).eval x = ∏ i, f i t (j i) x) := by
  classical
  choose n hn Q U hUc hK using h
  refine ⟨n, hn, Q, U,
    (piRank_complexity Q U hp hι hUc).mono _ (productNiltestBudget_geometry hp), ?_⟩
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] (L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    fun i => realification_moduleTopology_t2 (Q i).basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i ⧸ (R i).filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi Q).basis
  choose K hKn hKc hKu a ha0 hKe using hK
  obtain ⟨_, V, hVn, hVc, hVu, hVa, hVe⟩ := exists_normalized_product_unit_family Q K U hp hι hUc
    (fun i j => (hKn i j).le) hKc hKu (fun t i => a i t) (fun t i => ha0 i t)
  refine ⟨V, hVn, hVc, hVu,
    (fun t => NilpotentLieFiltration.piRealOrbit (fun i => (Q i).filtration) (fun i => a i t)),
    hVa, ?_⟩
  intro t j x
  rw [hVe]
  exact Finset.prod_congr rfl (fun i _ => hKe i t (j i) x)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module
open scoped TensorProduct BigOperators

theorem exists_binary_lower_rank_unit_family
    {σ τ : Type*} {I J L₀ L₁ : Type} [Fintype I] [Fintype J]
    [LieRing L₀] [LieAlgebra ℚ L₀] [LieRing L₁] [LieAlgebra ℚ L₁]
    {s r d₀ d₁ : ℕ} (D₀ : RationalFilteredNilmanifold L₀ s d₀)
    (D₁ : RationalFilteredNilmanifold L₁ s d₁)
    (R₀ : D₀.DegreeRankStructure (r + 1)) (R₁ : D₁.DegreeRankStructure (r + 1))
    (w : σ → ℕ) (f₀ : τ → I → (σ → ℤ) → ℂ) (f₁ : τ → J → (σ → ℤ) → ℂ)
    {p : ℝ} (hp : 2 ≤ p)
    (h₀ : D₀.HasLowerRankOrbitFamily R₀ w f₀ p)
    (h₁ : D₁.HasLowerRankOrbitFamily R₁ w f₁ p) :
    ∃ F : NativeUnitRankFamily w s r τ (I × J) (productNiltestBudget p),
      F.dim ≤ d₀ + d₁ ∧ ∀ t ij x, F.eval t ij x = f₀ t ij.1 x * f₁ t ij.2 x := by
  classical
  let D := optionFactors D₀ (fun _ : Unit => D₁)
  let R : ∀ i : Option Unit, (D i).DegreeRankStructure (r + 1)
    | none => R₀
    | some _ => R₁
  let K : Option Unit → Type
    | none => I
    | some _ => J
  let : ∀ i, Fintype (K i) := fun i => match i with
    | none => inferInstanceAs (Fintype I)
    | some _ => inferInstanceAs (Fintype J)
  let f : ∀ i, τ → K i → (σ → ℤ) → ℂ
    | none => f₀
    | some _ => f₁
  have h : ∀ i, (D i).HasLowerRankOrbitFamily (R i) w (f i) p := fun i => by
    match i with
    | none => exact h₀
    | some _ => exact h₁
  obtain ⟨n, hn, Q, U, hU, hfamily⟩ := exists_lower_rank_product_family D R w f
    (by linarith) (by simpa using hp) h
  let L (i : Option Unit) :=
    optionLieSpace L₀ (fun _ : Unit => L₁) i ⧸ (R i).filtration.layerIdeal s (r + 1)
  let : ∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i) := fun _ => moduleTopology ℝ _
  let : ∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i) :=
    fun _ => IsModuleTopology.topologicalAddGroup ℝ _
  let : ∀ i, T2Space (ℝ ⊗[ℚ] L i) := fun i => realification_moduleTopology_t2 (Q i).basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, L i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i)) := IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 (pi Q).basis
  obtain ⟨V, hVn, hVc, hVu, a, ha, he⟩ := hfamily
  let e : (∀ i, K i) ≃ I × J := {
    toFun := fun k => (k none, k (some ()))
    invFun := fun ij i => match i with
      | none => ij.1
      | some _ => ij.2
    left_inv := by
      intro k
      funext i
      rcases i with _ | ⟨⟩ <;> rfl
    right_inv := fun _ => rfl
  }
  let F : NativeUnitRankFamily w s r τ (I × J) (productNiltestBudget p) := {
    L := ∀ i, L i
    dim := Fintype.card (Σ i : Option Unit, Fin (n i))
    model := pi Q
    rank := piRank Q U
    complexity := hU
    test := fun ij => V (e.symm ij)
    test_norm := fun ij => hVn (e.symm ij)
    test_complexity := fun ij => hVc (e.symm ij)
    unit := fun x => (e.symm.sum_comp (fun k => ‖(V k).observable x‖ ^ 2)).trans (hVu x)
    orbit := a
    normalized := ha
  }
  refine ⟨F, ?_, ?_⟩
  · change Fintype.card (Σ i : Option Unit, Fin (n i)) ≤ d₀ + d₁
    simp only [Fintype.card_sigma, Fintype.card_fin]
    rw [Fintype.sum_option, Fintype.sum_unique]
    exact Nat.add_le_add (hn none) (hn (some ()))
  · intro t ij x
    have hprod := he t (e.symm ij) x
    rw [Fintype.prod_option, Fintype.prod_unique] at hprod
    exact hprod

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeSubspaceFreeModel
namespace OAI

section

namespace Erdos3.SubspaceFreeLift

open Module VectorPolynomial
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s r : ℕ}
  (S : Fin s → Submodule ℚ L)

variable (B : ∀ d, Basis (Fin (finrank ℚ (S d))) ℚ (S d))

variable (F : DegreeRankLieFiltration L s r)
  (hS : ∀ d, S d ≤ F.layer (d.val + 1) 0)

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FreeCorrelationRelationRefinement
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

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

noncomputable def realCoefficientFourSpace (d : Fin (s + 1)) :
    Submodule ℝ (Fin 4 → ℝ ⊗[ℚ] W.L) :=
  ((D.coefficientFourSpace d).baseChange ℝ).map
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)).toLinearMap

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3.NativeRankRelation.CommonData

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

theorem mem_real_coefficientFourSpace (d : Fin (s + 1))
    (v : (W.rank.filtration.fourHorizontalLayer d.val).baseChange ℝ) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 4 => W.L)) v.val ∈
        D.realCoefficientFourSpace d ↔
      W.rank.filtration.realFourHorizontalMap d.val v ∈ (D.horizontal d).baseChange ℝ := by
  obtain ⟨x, rfl⟩ :=
    (realificationSubmoduleEquiv (W.rank.filtration.fourHorizontalLayer d.val)).surjective v
  rw [W.rank.filtration.realFourHorizontalMap_baseChange]
  unfold realCoefficientFourSpace
  rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply,
    realificationSubmoduleEquiv_coe, coefficientFourSpace, realification_map, realification_comap]
  constructor
  · rintro ⟨y, hy, he⟩
    have h := realification_subtype_injective (W.rank.filtration.fourHorizontalLayer d.val) he
    exact h ▸ hy
  · intro hx
    exact ⟨x, hx, rfl⟩

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealCoefficientKernel
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

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

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonOrbit
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module VectorPolynomial
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
  (B : D.CoefficientBases Q)
  (E : RationalFilteredNilmanifold D.CoefficientFreeLieAlgebra s
    (finrank ℚ D.CoefficientFreeLieAlgebra))
  (T : E.DegreeRankStructure r) (hbQ : b ≤ Q) (hT : T.ComplexityLE Q)
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

theorem paired_affine_orbit_coefficient_mem_comparison
    (hTfil : T.filtration = D.coefficientFreeFiltration) (hs : 1 ≤ s)
    (A K U : E.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
    (hA : ∀ d : Fin s, coefficients A.log (Finsupp.single () (d.val + 1)) ∈
      ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
        (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
    (hK : ∀ d : Fin s, coefficients K.log (Finsupp.single () (d.val + 1)) ∈
      (T.filtration.layer (d.val + 1) 2).baseChange ℝ)
    (hU : ∀ d : Fin s, coefficients U.log (Finsupp.single () (d.val + 1)) ∈
      (fourPetalSpace (D.dependentFreeSpan d)
        (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
    (d : Fin s) :
    (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => D.CoefficientFreeLieAlgebra)).symm
      ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] ∈
      (petalComparisonSpace
        ((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0))
        (fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)))
        (D.coefficientFreeFiltration.layer (d.val + 1) 2)).baseChange ℝ := by
  have h₁ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
    (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) A K
  have h₂ := T.polynomialOrbit_mul_coefficient_sub_mem_rank_two hs
    (fun _ : Unit => 1) (Finsupp.single () (d.val + 1)) (A * K) U
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one] at h₁ h₂
  have herr : coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
      (coefficients A.log (Finsupp.single () (d.val + 1)) +
        coefficients U.log (Finsupp.single () (d.val + 1))) ∈
      (D.coefficientFreeFiltration.layer (d.val + 1) 2).baseChange ℝ := by
    rw [← hTfil]
    convert ((T.filtration.layer (d.val + 1) 2).baseChange ℝ).add_mem
      (((T.filtration.layer (d.val + 1) 2).baseChange ℝ).add_mem h₂ h₁) (hK d) using 1
    abel
  have hp : ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] ∈
      petalComparisonSpace
        (((fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
          (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩)).map (LinearMap.proj 0)).baseChange ℝ)
        ((fourPetalSpace (D.dependentFreeSpan d)
          (fourRefinedRelation (D.coefficientFreeSpan d) (D.dependentFreeSpan d)
            (D'.coefficientFourSpace ⟨d.val + 1, by omega⟩))).baseChange ℝ)
        ((D.coefficientFreeFiltration.layer (d.val + 1) 2).baseChange ℝ) := by
    apply (mem_petalComparisonSpace _ _ _ _).mpr
    constructor
    · exact Submodule.mem_sup_left (hA d)
    · apply Submodule.mem_sup.mpr
      refine ⟨_, hU d, _, herr, ?_⟩
      change coefficients U.log (Finsupp.single () (d.val + 1)) +
        (coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
          (coefficients A.log (Finsupp.single () (d.val + 1)) +
            coefficients U.log (Finsupp.single () (d.val + 1)))) =
        coefficients (A * K * U).log (Finsupp.single () (d.val + 1)) -
          coefficients A.log (Finsupp.single () (d.val + 1))
      abel
  rw [← realification_petalComparisonSpace] at hp
  obtain ⟨y, hy, heq⟩ := hp
  have hy' : (TensorProduct.piRight ℚ ℝ ℝ (fun _ : Fin 2 => D.CoefficientFreeLieAlgebra)).symm
      ![coefficients (A * K * U).log (Finsupp.single () (d.val + 1)),
        coefficients A.log (Finsupp.single () (d.val + 1))] = y := by
    rw [← heq]
    exact LinearEquiv.symm_apply_apply _ _
  rw [hy']
  exact hy

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SharedFreeComparisonLift
namespace OAI

section

namespace Erdos3.NativeRankRelation.CommonData

open Module
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
  (e : Basis (Fin (finrank ℚ D.CoefficientFreeLieAlgebra)) ℚ D.CoefficientFreeLieAlgebra)
  {Q : ℝ} (F : FreeCoordinateFrame e Q)

include F

theorem exists_coefficientFreeSpan_projector (hs : 1 ≤ s) (d : Fin s)
    (l : ℕ) (hl : 0 < l) {A : ℝ} (hA : 0 ≤ A) (hQA : Q ≤ A)
    (hdim : (finrank ℚ D.CoefficientFreeLieAlgebra : ℝ) ≤ A)
    (hlA : (l : ℝ) ≤ Real.exp A) :
    let t := A + 1
    ∃ (P : (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra) →ₗ[ℝ]
        (ℝ ⊗[ℚ] D.CoefficientFreeLieAlgebra)) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((t + 2) ^ 3 + (t + 2) ^ 36) ∧
      (∀ x, P x ∈ (D.coefficientFreeSpan d).baseChange ℝ) ∧
      (∀ x ∈ (D.coefficientFreeSpan d).baseChange ℝ, P x = x) ∧
      (∀ x, ‖(e.baseChange ℝ).equivFun (P x)‖ ≤
        Real.exp ((t + 2) ^ 3 + (t + 2) ^ 18) * ‖(e.baseChange ℝ).equivFun x‖) ∧
      ∀ x, (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l →
        (e.baseChange ℝ).equivFun (P x) ∈ realDenominatorGrid m := by
  obtain ⟨c, hc⟩ := D.exists_coefficientFreeSpan_basis e F hs d
  have hcspan : Submodule.span ℚ (Set.range (fun j => (c j : D.CoefficientFreeLieAlgebra))) =
      D.coefficientFreeSpan d := by
    change Submodule.span ℚ (Set.range ((D.coefficientFreeSpan d).subtype ∘ c)) = _
    rw [Set.range_comp, ← Submodule.map_span, c.span_eq, Submodule.map_top, Submodule.range_subtype]
  apply exists_controlled_subspace_projector e (D.coefficientFreeSpan d)
    (fun j => (c j : D.CoefficientFreeLieAlgebra)) hcspan l hl hA
  · simpa only [Fintype.card_fin] using hdim
  · have hd : (finrank ℚ (D.coefficientFreeSpan d) : ℝ) ≤
        finrank ℚ D.CoefficientFreeLieAlgebra := by
      exact_mod_cast Submodule.finrank_le (D.coefficientFreeSpan d)
    simpa only [Fintype.card_fin] using hd.trans hdim
  · exact fun j i => (hc j i).trans hQA
  · exact hlA

end Erdos3.NativeRankRelation.CommonData

end

section

namespace Erdos3

noncomputable def sharedFreeComparisonModelBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (q + 2 + sharedFreeComparisonBasisBudget q p + nativePairModelConstant s) ^ nativePairModelConstant s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeLowerComparisonBudget
namespace OAI

section

namespace Erdos3

noncomputable def sharedFreeLowerComparisonBudget (s : ℕ) (q p : ℝ) : ℝ :=
  (sharedFreeComparisonModelBudget s q p + rankUnitDescentConstant s) ^ rankUnitDescentConstant s

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.SharedFreeCorrelationBudget
namespace OAI

section

namespace Erdos3

theorem sharedFreeCorrelationInput_bounds (s : ℕ) {q p : ℝ}
    (hq : 0 ≤ q) (hqp : q ≤ p) (hp : 0 ≤ p) :
    2 ≤ sharedFreeCorrelationInput s p ∧ q ≤ sharedFreeCorrelationInput s p ∧
    (p + sharedFreeAffineConstant s) ^ sharedFreeAffineConstant s ≤ sharedFreeCorrelationInput s p ∧
    (s : ℝ) * (sharedFreeCommonCorrectionBudget s q p + sharedFreePetalLiftBudget s q p) ≤
      sharedFreeCorrelationInput s p ∧
    Real.exp (sharedFreeCommonCorrectionBudget s q p) + Real.exp (sharedFreePetalLiftBudget s q p) ≤
      Real.exp ((sharedFreeCorrelationInput s p + 2) ^ 1) ∧
    (p + sharedFreeFactorFreezingConstant s) ^ sharedFreeFactorFreezingConstant s ≤
      sharedFreeCorrelationInput s p := by
  let a := (exists_sharedFreeFullOrbitBudget_bound s).choose
  let b := sharedFreeFactorFreezingConstant s
  have ha : 0 ≤ (p + a) ^ a := by positivity
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have h2 : 2 ≤ sharedFreeCorrelationInput s p := by
    change 2 ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hpa : (p + a) ^ a ≤ sharedFreeCorrelationInput s p := by
    change (p + a) ^ a ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hpb : (p + b) ^ b ≤ sharedFreeCorrelationInput s p := by
    change (p + b) ^ b ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  have hqT : q ≤ sharedFreeCorrelationInput s p := by
    change q ≤ p + (p + a) ^ a + (p + b) ^ b + 2
    linarith
  obtain ⟨hΛ, _, _, hden, hslow⟩ := (exists_sharedFreeFullOrbitBudget_bound s).choose_spec.2 q p hq hqp hp
  refine ⟨h2, hqT, hΛ.trans hpa, hden.trans hpa, ?_, hpb⟩
  exact hslow.trans (Real.exp_le_exp.mpr (by simpa only [pow_one] using
    (hpa.trans (show sharedFreeCorrelationInput s p ≤ sharedFreeCorrelationInput s p + 2 by linarith))))

theorem sharedFreeCorrelationInput_le_budget (s : ℕ) (hs : 2 ≤ s) {p : ℝ} (hp : 0 ≤ p) :
    sharedFreeCorrelationInput s p ≤ sharedFreeCorrelationBudget s hs p := by
  let T := sharedFreeCorrelationInput s p
  let C := sharedFactorCorrelationConstant s hs
  have hT : 2 ≤ T := (sharedFreeCorrelationInput_bounds s hp le_rfl hp).1
  have hC : 2 ≤ C := (exists_shared_factor_correlations s hs).choose_spec.1
  have hbase : 1 ≤ T + C := by linarith [Nat.cast_nonneg (α := ℝ) C]
  change T ≤ (T + C) ^ C
  exact (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) C)).trans
    ((pow_one (T + C)).symm.le.trans (pow_le_pow_right₀ hbase (by omega : 1 ≤ C)))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairCorrelator
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem antisymmetricPairTests_eval (n : Fin 2 → ℤ) :
    (∏ k, (V.antisymmetricPairTests k).eval n) =
      W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by decide : 1 ≤ ∑ l, mixedCorrelationDegree 1 l)).conjugate.eval n *
    ((W.pairComponent i 0 1).conjugate.eval n * (W.pairComponent j 1 0).eval n) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.pairComponent_eval, W.pairComponent_eval]
  unfold NativeMultidegreeNilcharacter.antisymmetricKernel
  ring

theorem antisymmetricPairTests_vertical (k : Option (Fin 2))
    (z : (V.antisymmetricPairModels k).RealGroup)
    (hz : z ∈ (V.antisymmetricPairModels k).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l))
    (x : (V.antisymmetricPairModels k).Space) :
    (V.antisymmetricPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.antisymmetricPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.antisymmetricPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by decide : 1 < ∑ l, mixedCorrelationDegree 1 l) z hz x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.pairComponent_vertical i 0 1) z hz x
    · exact W.pairComponent_vertical j 1 0 z hz x

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.AntisymmetricPairNiltest
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))
  [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem antisymmetricPairNiltest_complexity :
    V.antisymmetricPairNiltest.ComplexityLE (productNiltestBudget (antisymmetricPairBudget p q)) :=
  piNiltest_complexity V.antisymmetricPairModels V.antisymmetricPairTests _ _ _

theorem antisymmetricPairNiltest_eval (n : Fin 2 → ℤ) :
    V.antisymmetricPairNiltest.eval n =
      W.antisymmetricKernel i j (n 0) (n 1) * star (V.test.eval n) := by
  rw [antisymmetricPairNiltest, piNiltest_eval]
  exact V.antisymmetricPairTests_eval n

theorem antisymmetricPairNiltest_vertical
    (z : (pi V.antisymmetricPairModels).RealGroup)
    (hz : z ∈ (pi V.antisymmetricPairModels).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (pi V.antisymmetricPairModels).Space) :
    V.antisymmetricPairNiltest.observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (piFrequency V.antisymmetricPairFrequencies) z.coord : ℝ) :
          CircleFourier.Circle) * V.antisymmetricPairNiltest.observable x :=
  piNiltest_vertical V.antisymmetricPairModels V.antisymmetricPairTests
    V.antisymmetricPairFrequencies _ _ _ V.antisymmetricPairTests_vertical z hz x

theorem antisymmetricPairNiltest_bias :
    Real.exp (-q) ≤ ‖𝔼 n ∈ integerBox (fun _ : Fin 2 => N), V.antisymmetricPairNiltest.eval n‖ := by
  rw [integerBox_expect_eq_zmod]
  simp_rw [V.antisymmetricPairNiltest_eval]
  exact V.correlation

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.AntisymmetricPairPolynomial
namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

variable [TopologicalSpace (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)]

theorem antisymmetricPairNiltest_symbol {ι : Type*}
    (b : Module.Basis ι ℚ V.AntisymmetricPairAlgebra) (w : ι → ℕ)
    (hF : ∀ k, (pi V.antisymmetricPairModels).filtration.layer k =
      Submodule.span ℚ (b '' {a | k ≤ w a})) :
    V.antisymmetricPairNiltest.symbol b w hF =
      (pi V.antisymmetricPairModels).filtration.realPolynomialSymbolHom b w hF
        (fun _ : Fin 2 => 1) V.antisymmetricPairPolynomial := rfl

end Erdos3.NativeSampleCorrelation

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.QuadraticPairStepDrop
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem pairComparisonTests_vertical (a b : Fin W.outputDim) (k : Option (Fin 2))
    (z : (V.antisymmetricPairModels k).RealGroup)
    (hz : z ∈ (V.antisymmetricPairModels k).filtration.realification.subgroup
      (∑ l, mixedCorrelationDegree 1 l)) (x : (V.antisymmetricPairModels k).Space) :
    (V.pairComparisonTests a b k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.antisymmetricPairFrequencies k) z.coord : ℝ) :
          CircleFourier.Circle) * (V.pairComparisonTests a b k).observable x := by
  cases k with
  | none => exact Niltest.oneOnOrbit_vertical _ z x
  | some k =>
    fin_cases k
    · exact Niltest.conjugate_vertical _ _ (W.pairComponent_vertical a 0 1) z hz x
    · exact W.pairComponent_vertical b 1 0 z hz x

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AntisymmetricPairProjections
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem antisymmetricPairPolynomialMap_eq (k : Fin 2) (out : Fin W.outputDim) :
    V.antisymmetricPairPolynomialMap k V.antisymmetricPairPolynomial =
      W.pairComponentPolynomial out k k.rev := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom (liePiEval (some k))).toLinearMap.restrictScalars ℚ)
    (NilpotentLieFiltration.piRealOrbit (fun l => (V.antisymmetricPairModels l).filtration)
      (fun l => (V.antisymmetricPairTests l).orbit)).log = (W.pairComponent out k k.rev).orbit.log
  rw [NilpotentLieFiltration.piRealOrbit_projection_log]
  fin_cases k <;> rfl

end NativeSampleCorrelation

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

namespace NativePolynomialOrbitFactors

variable (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
  V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
  (fun _ : Fin 2 => (N : ℝ)) r)

theorem pair_projected_product (k : Fin 2) (out : Fin W.outputDim) :
    V.antisymmetricPairPolynomialMap k R.slow * V.antisymmetricPairPolynomialMap k R.middle *
      V.antisymmetricPairPolynomialMap k R.rational *
        W.model.filtration.realification.adaptedConstantGroupHom (fun _ : Fin 2 => 1)
          (productProjectionHom V.antisymmetricPairModels (some k) R.latticeConstant) =
      W.pairComponentPolynomial out k k.rev := by
  have h := congrArg (V.antisymmetricPairPolynomialMap k) R.product
  simpa only [map_mul, V.antisymmetricPairPolynomialMap_constant,
    V.antisymmetricPairPolynomialMap_eq k out] using h

theorem pair_eval_component (k : Fin 2) (out : Fin W.outputDim) (n : Fin 2 → ℤ) :
    W.eval out (correlationInput (n k) (n k.rev)) =
      (W.pairComponent out k k.rev).observable (QuotientGroup.mk
        (W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.slow) *
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.middle) *
          W.model.filtration.adaptedPolynomialRealValueHom (fun _ : Fin 2 => 1) (fun a => (n a : ℝ))
            (V.antisymmetricPairPolynomialMap k R.rational))) := by
  have h := Niltest.eval_of_lattice_factorization W.model (fun _ : Fin 2 => 1)
    (W.pairComponent out k k.rev) (V.antisymmetricPairPolynomialMap k R.slow)
    (V.antisymmetricPairPolynomialMap k R.middle) (V.antisymmetricPairPolynomialMap k R.rational)
    (productProjectionHom V.antisymmetricPairModels (some k) R.latticeConstant)
    (V.antisymmetricPairProjection_lattice k R.latticeConstant R.latticeConstant_mem)
    (R.pair_projected_product k out) n
  simpa only [W.pairComponent_eval] using h

end NativePolynomialOrbitFactors

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}

namespace NativePolynomialOrbitFactors

variable (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
  V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
  (fun _ : Fin 2 => (N : ℝ)) r)

theorem pairFrozenVector_diagonal (k : Fin 2) (out : Fin W.outputDim) (x : Fin 2 → ℤ) :
    W.eval out (correlationInput (x k) (x k.rev)) =
      R.pairFrozenVector k (R.slowValue x) (R.rationalValue x) out x := by
  rw [R.pair_eval_component k out x]
  simp only [pairFrozenVector, frozenMiddleValue, slowValue, rationalValue,
    productProjection_mk, map_mul, V.antisymmetricPairPolynomialMap_value]
  rfl

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.OriginalMixedRootEquivalence
namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeSampleCorrelation

variable {n : ℕ} {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : MixedReplicatedIndex (n + 1) => 1) p}
  {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin (n + 2) => 1) (n + 1) q
    Finset.univ (fun z : Fin (n + 2) → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.mixedAntisymmetric i j (fun k => ((z k).val : ℤ))))

theorem mixedPairTests_eval (x : Fin (n + 2) → ℤ) :
    (∏ k, (V.mixedPairTests k).eval x) =
      W.mixedAntisymmetric i j x * star (V.test.eval x) := by
  rw [Fintype.prod_option, Fin.prod_univ_two]
  change (V.test.raiseStep (by rw [mixedReplicated_totalDegree]; omega : n + 1 ≤ ∑ _ : MixedReplicatedIndex (n + 1), 1)).conjugate.eval x *
    ((W.mixedPairComponent i id).eval x *
      (W.mixedPairComponent j (mixedExchangeCoordinate n)).conjugate.eval x) = _
  rw [Niltest.eval_conjugate, Niltest.raiseStep_eval, Niltest.eval_conjugate,
    W.mixedPairComponent_eval, W.mixedPairComponent_eval]
  have h0 : mixedExchangeCoordinate n 0 = 1 := rfl
  have h1 : mixedExchangeCoordinate n 1 = 0 := rfl
  have ht (k : Fin n) : mixedExchangeCoordinate n k.succ.succ = k.succ.succ := rfl
  simp only [id_eq, h0, h1, ht, NativeMultidegreeNilcharacter.mixedAntisymmetric]
  ring

theorem mixedPairTests_vertical (k : Option (Fin 2))
    (z : (V.mixedPairModels k).RealGroup)
    (hz : z ∈ (V.mixedPairModels k).filtration.realification.subgroup (∑ _ : MixedReplicatedIndex (n + 1), 1))
    (x : (V.mixedPairModels k).Space) :
    (V.mixedPairTests k).observable (z • x) =
      CircleFourier.character
        ((realifyFunctional (V.mixedPairFrequencies k) z.coord : ℝ) : CircleFourier.Circle) *
          (V.mixedPairTests k).observable x := by
  cases k with
  | none =>
    exact V.test.conjugate.raiseStep_top_vertical
      (by rw [mixedReplicated_totalDegree]; omega : n + 1 < ∑ _ : MixedReplicatedIndex (n + 1), 1) z hz x
  | some k =>
    fin_cases k
    · exact W.mixedPairComponent_vertical i id z hz x
    · exact Niltest.conjugate_vertical _ _ (W.mixedPairComponent_vertical j (mixedExchangeCoordinate n)) z hz x

end NativeSampleCorrelation
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.MixedPairComparison
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open scoped TensorProduct

theorem HasLowerRankOrbitFamily.reindex {L I σ τ τ' : Type*}
    [LieRing L] [LieAlgebra ℚ L] [Fintype I] {s r d : ℕ}
    {D : RationalFilteredNilmanifold L s d} {R : D.DegreeRankStructure (r + 1)}
    {w : σ → ℕ} {f : τ → I → (σ → ℤ) → ℂ} {p : ℝ}
    (h : D.HasLowerRankOrbitFamily R w f p) (j : τ' → τ) :
    D.HasLowerRankOrbitFamily R w (fun t => f (j t)) p := by
  obtain ⟨n, hn, Q, U, hUc, hK⟩ := h
  refine ⟨n, hn, Q, U, hUc, ?_⟩
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1)))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (L ⧸ R.filtration.layerIdeal s (r + 1))) :=
    IsModuleTopology.topologicalAddGroup ℝ _
  let := realification_moduleTopology_t2 Q.basis
  obtain ⟨K, hKn, hKc, hKu, a, ha0, ha⟩ := hK
  exact ⟨K, hKn, hKc, hKu, (fun t => a (j t)),
    (fun t => ha0 (j t)), fun t i x => ha (j t) i x⟩

end Erdos3.RationalFilteredNilmanifold

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RationalTaggedConstraintHistory
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

variable {m : ℕ} (J : Fin m → Type*) [∀ j, Fintype (J j)]
    {X R S V : Type*} [CommRing R] [CommRing S]
    [AddCommGroup V] [Module R V]

theorem lowTaggedVectorExtend_weightedHomogeneousPart (k n : ℕ)
    (P : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) R V) :
    lowTaggedVectorExtend J k (weightedHomogeneousPart (lowTaggedVariableWeight J k) n P) =
      weightedHomogeneousPart (fullTaggedVariableWeight J) n (lowTaggedVectorExtend J k P) := by
  have hX (i : X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) :
      (MvPolynomial.X (lowTaggedVariableEmbedding J k i) :
        MvPolynomial (X ⊕ (Σ j, J j)) R).IsWeightedHomogeneous
        (fullTaggedVariableWeight J) (lowTaggedVariableWeight J k i) := by
    rw [← lowTaggedVariableEmbedding_weight J k i]
    exact MvPolynomial.isWeightedHomogeneous_X (R := R)
      (fullTaggedVariableWeight J) (lowTaggedVariableEmbedding J k i)
  induction P using TensorProduct.induction_on with
  | zero => simp
  | tmul P v =>
    rw [weightedHomogeneousPart_tmul, lowTaggedVectorExtend_tmul,
      lowTaggedVectorExtend_tmul, weightedHomogeneousPart_tmul]
    simp only [MvPolynomial.rename_eq_aeval]
    exact congrArg (fun Q => Q ⊗ₜ[R] v)
      (aeval_weightedHomogeneousComponent (lowTaggedVariableWeight J k)
        (fullTaggedVariableWeight J) (MvPolynomial.X ∘ lowTaggedVariableEmbedding J k)
        hX n P)
  | add P Q hP hQ => simp only [map_add, hP, hQ]

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

variable {m : ℕ} {X κ : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

theorem fullTaggedGradedBaseIntersection_subset (k : ℕ)
    (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
    (K : κ → Submodule ℝ (Fin (Fintype.card (LowTaggedIndex J k)) → ℝ)) :
    fullTaggedGradedBaseIntersection J k K₀ K ⊆ K₀ := fun _ ht => ht.1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullTaggedChartCoefficientRange
namespace OAI

section

namespace Erdos3

open Module VectorPolynomial
open scoped BigOperators

variable {B I U : Type*} [Fintype B] [Fintype I]
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K)

include hA

theorem normalizedChart_coefficients_mem (α : U →₀ ℕ) :
    coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A) α ∈ K := by
  have heq : coefficients (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A) α =
      fun b => (A b).coeff α := by
    funext b
    exact coefficients_ofCoordinates_basisFun A α b
  rw [heq]
  exact hA α

noncomputable def normalizedChartSubspaceCoordinates : I → MvPolynomial U ℝ :=
  fun i => coordinate (e.coord i).toAddMonoidHom
    (restrictCoefficients K (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A)
      (normalizedChart_coefficients_mem K A hA))

omit [Fintype I] in
theorem normalizedChartSubspaceCoordinates_coeff (α : U →₀ ℕ) (i : I) :
    (normalizedChartSubspaceCoordinates K e A hA i).coeff α =
      e.repr ⟨fun b => (A b).coeff α, hA α⟩ i := by
  unfold normalizedChartSubspaceCoordinates
  rw [coeff_coordinate]
  change e.repr (coefficients
    (restrictCoefficients K (ofCoordinates (R := ℝ) (Pi.basisFun ℝ B) A)
      (normalizedChart_coefficients_mem K A hA)) α) i = _
  congr 1
  apply congrArg e.repr
  apply Subtype.ext
  rw [coefficients_restrictCoefficients]
  funext b
  exact coefficients_ofCoordinates_basisFun A α b

theorem normalizedChartSubspaceCoordinates_reconstruct (b : B) :
    A b = ∑ i, (e i : B → ℝ) b • normalizedChartSubspaceCoordinates K e A hA i := by
  classical
  ext α
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_smul,
    normalizedChartSubspaceCoordinates_coeff, smul_eq_mul]
  have heq := congrArg (fun z : K => (z : B → ℝ) b)
    (e.sum_repr ⟨fun c => (A c).coeff α, hA α⟩)
  simpa only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul, mul_comm] using heq.symm

end Erdos3

end

section

namespace Erdos3
open Module _root_.MvPolynomial _root_.OAI.MvPolynomial
open scoped BigOperators

variable {U B I : Type*} [Fintype B] [Fintype I]

theorem normalizedChartSubspaceCoordinates_reconstruct_C
    (K : Submodule ℝ (B → ℝ)) (e : Basis I ℝ K)
    (A : B → MvPolynomial U ℝ)
    (hA : ∀ α, (fun b => (A b).coeff α) ∈ K) (b : B) :
    A b = ∑ i, C ((e i : B → ℝ) b) * normalizedChartSubspaceCoordinates K e A hA i := by
  simpa only [MvPolynomial.smul_eq_C_mul] using
    normalizedChartSubspaceCoordinates_reconstruct K e A hA b

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open _root_.MvPolynomial _root_.OAI.MvPolynomial

variable {m : ℕ} {X : Type*} (J : Fin m → Type*) [∀ j, Fintype (J j)]

omit [∀ j, Fintype (J j)] in

theorem fullTaggedMajorChart_homogeneous
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (i : X ⊕ (Σ j, J j)) :
    (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly) i).IsWeightedHomogeneous
      (fullTaggedVariableWeight J) (fullTaggedVariableWeight J i) := by
  cases i with
  | inl x =>
    exact (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inl x)).C_mul _
  | inr a =>
    apply (isWeightedHomogeneous_X (R := ℝ) (fullTaggedVariableWeight J) (Sum.inr a)).sub
    apply majorParameterRename_homogeneous (fun _ : X => 1)
      (fun a : Σ j, J j => a.1.val + 1)
    exact weightedHomogeneousComponent_isWeightedHomogeneous _ _

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.FullChartHomogeneousCorrection
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X M : Type} [LieRing M] [LieAlgebra ℚ M]
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def CertifiedFullChartDetectedDecomposition : Prop :=
  ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
    (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
    0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
    K' ⊆ K₀ ∧
    (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
    (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
    (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
    (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
    (∀ t ∈ K', ∀ j ≤ k,
      F.realSymbolGradeEvaluation b ω hF wt j t
        ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
            (realChartSubstitute chart pS))⁻¹ * Z *
          (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
        fast.baseChange ℝ) ∧
    (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
      (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
      pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
      K' = fullTaggedGradedBaseIntersection J k K₀
        (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
    RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
    ∀ t ∈ K', fast.mkQ.baseChange ℝ
      (F.realSymbolGradeEvaluation b ω hF wt k t (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute chart pS) + eval₂ t pR

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

namespace VectorPolynomial

variable {σ R V η : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem weightedHomogeneousPart_idempotent (w : σ → ℕ) (k : ℕ)
    (p : VectorPolynomial σ R V) :
    weightedHomogeneousPart w k (weightedHomogeneousPart w k p) =
      weightedHomogeneousPart w k p :=
  weightedHomogeneousPart_eq_self (weightedHomogeneousPart_homogeneous w k p)

theorem weightedHomogeneousPart_coordinate_bound (w : σ → ℕ) (k : ℕ)
    (f : η → V →+ ℝ) (p : VectorPolynomial σ R V) {C : ℝ} (hC : 0 ≤ C)
    (hp : ∀ α i, |f i (coefficients p α)| ≤ C) :
    ∀ α i, |f i (coefficients (weightedHomogeneousPart w k p) α)| ≤ C := by
  intro α i
  rw [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α i
  · simpa only [map_zero, abs_zero] using hC

theorem weightedHomogeneousPart_coefficients_grid (w : σ → ℕ) (k : ℕ)
    (f : η → V →+ ℝ) (p : VectorPolynomial σ R V) (q : ℕ)
    (hp : ∀ α, (fun i => f i (coefficients p α)) ∈ realDenominatorGrid q) :
    ∀ α, (fun i => f i (coefficients (weightedHomogeneousPart w k p) α)) ∈
      realDenominatorGrid q := by
  intro α
  simp only [coefficients_weightedHomogeneousPart]
  split_ifs
  · exact hp α
  · refine ⟨fun _ => 0, ?_⟩
    ext i
    simp

theorem weightedHomogeneousPart_coordinate_totalDegree_le
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (k : ℕ) (f : V →+ ℝ)
    (p : VectorPolynomial σ R V) :
    (coordinate f (weightedHomogeneousPart w k p)).totalDegree ≤ k := by
  rw [coordinate_weightedHomogeneousPart]
  exact weightedHomogeneousComponent_totalDegree_le_of_positive w hw k _

end VectorPolynomial

namespace NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ) (fast : Submodule ℚ F.AssociatedGraded)
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)

theorem restrictedMajorCorrection_weightedHomogeneousPart (k : ℕ)
    (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) :
    F.restrictedMajorCorrection b ω hF w fast lift k (weightedHomogeneousPart w k p) =
      F.restrictedMajorCorrection b ω hF w fast lift k p := by
  simp only [restrictedMajorCorrection, weightedHomogeneousPart_idempotent]

variable {m : ℕ} {X : Type} (J : Fin m → Type)

theorem restrictedMajorCorrection_fullChart_homogeneous (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (p : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))) :
    F.restrictedMajorCorrection b ω hF (fullTaggedVariableWeight J) fast lift k
      (realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
        (weightedHomogeneousPart (fullTaggedVariableWeight J) k p)) =
    F.restrictedMajorCorrection b ω hF (fullTaggedVariableWeight J) fast lift k
      (realChartSubstitute (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) p) := by
  rw [realChartSubstitute_weightedHomogeneousPart _ _ _
    (fullTaggedMajorChart_homogeneous J poly H),
    restrictedMajorCorrection_weightedHomogeneousPart]

theorem fullChart_quotient_identity_homogeneous (k : ℕ)
    (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (H : X → ℝ)
    (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight J))
    (K : Set (X ⊕ (Σ j, J j) → ℝ))
    (hK : ∀ t ∈ K, ∀ r : ℚ,
      (fun i => (r : ℝ) ^ fullTaggedVariableWeight J i * t i) ∈ K)
    (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
      (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
    (hquot : ∀ t ∈ K, fast.mkQ.baseChange ℝ
      (F.realSymbolGradeEvaluation b ω hF (fullTaggedVariableWeight J) k t
        (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute
        (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly)) pS) + eval₂ t pR) :
    ∀ t ∈ K, eval₂ t
      (F.realSymbolGradeQuotientPolynomial b ω hF (fullTaggedVariableWeight J) fast k
        (left⁻¹ * Z * right⁻¹).coord) =
      eval₂ t (realChartSubstitute
        (normalizedRealPolynomialChart H (fullTaggedMajorTopCoordinates J poly))
          (weightedHomogeneousPart (fullTaggedVariableWeight J) k pS)) +
      eval₂ t (weightedHomogeneousPart (fullTaggedVariableWeight J) k pR) := by
  intro t ht
  rw [realChartSubstitute_weightedHomogeneousPart _ _ _
    (fullTaggedMajorChart_homogeneous J poly H)]
  apply eval₂_weightedHomogeneousPart_decomposition_on _ _ _ _ K hK k
    (F.realSymbolGradeQuotientPolynomial_homogeneous b ω hF _ fast k _) _ t ht
  intro x hx
  rw [realSymbolGradeQuotientPolynomial_eval]
  exact hquot x hx

section Certified

variable {η : Type*} [Fintype η] [∀ j, Fintype (J j)] (k : ℕ)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ)) (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

theorem CertifiedFullChartDetectedDecomposition.exists_homogeneous
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    ∃ (pS pR : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal)
      (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ)),
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pS α = 0) ∧
      (∀ α, Finsupp.weight wt α ≠ k → coefficients pR α = 0) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pS).totalDegree ≤ k) ∧
      (∀ i, (coordinate (basis.coord i).toAddMonoidHom pR).totalDegree ≤ k) ∧
      0 < q ∧ (q : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget) ∧
      K' ⊆ K₀ ∧
      (∀ t ∈ K', ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ K') ∧
      (∀ t ∈ K₀, (∀ j, (fun a => t (Sum.inr ⟨j, a⟩)) ∈ Utag j) → t ∈ K') ∧
      (∀ α i, |basis.coord i (coefficients pS α)| ≤ Real.exp budget) ∧
      (∀ α, (fun i => basis.coord i (coefficients pR α)) ∈ realDenominatorGrid q) ∧
      (∀ t ∈ K', ∀ j ≤ k,
        F.realSymbolGradeEvaluation b ω hF wt j t
          ((left * F.restrictedMajorCorrection b ω hF wt fast lift k
              (realChartSubstitute chart pS))⁻¹ * Z *
            (F.restrictedMajorCorrection b ω hF wt fast lift k pR * right)⁻¹).coord ∈
          fast.baseChange ℝ) ∧
      (∃ (detectedfast : η → LieSubalgebra ℚ (weightedSubalgebra (lowTaggedWeight J k) k))
        (slow rat : VectorPolynomial (X ⊕ Fin (Fintype.card (LowTaggedIndex J k))) ℚ quotientReal),
        pS = lowTaggedVectorExtend J k slow ∧ pR = lowTaggedVectorExtend J k rat ∧
        K' = fullTaggedGradedBaseIntersection J k K₀
          (fun i => majorPhaseDetectedRealBase J k (detectedfast i))) ∧
      RationalTaggedConstraintCertificate J K₀ K' budget (Fintype.card η * m) ∧
      ∀ t ∈ K', eval₂ t
        (F.realSymbolGradeQuotientPolynomial b ω hF wt fast k (left⁻¹ * Z * right⁻¹).coord) =
        eval₂ t (realChartSubstitute chart pS) + eval₂ t pR := by
  obtain ⟨pS, pR, q, K', hq, hqB, hsub, hdilate, hretain, hcap, hgrid,
    hnext, horigin, hcertificate, hquot⟩ := h
  refine ⟨weightedHomogeneousPart wt k pS, weightedHomogeneousPart wt k pR, q, K',
    weightedHomogeneousPart_homogeneous wt k pS,
    weightedHomogeneousPart_homogeneous wt k pR,
    (fun i => weightedHomogeneousPart_coordinate_totalDegree_le wt
      (fullTaggedVariableWeight_pos J) k (basis.coord i).toAddMonoidHom pS),
    (fun i => weightedHomogeneousPart_coordinate_totalDegree_le wt
      (fullTaggedVariableWeight_pos J) k (basis.coord i).toAddMonoidHom pR),
    hq, hqB, hsub, hdilate, hretain,
    weightedHomogeneousPart_coordinate_bound wt k (fun i => (basis.coord i).toAddMonoidHom)
      pS (Real.exp_nonneg budget) hcap,
    weightedHomogeneousPart_coefficients_grid wt k (fun i => (basis.coord i).toAddMonoidHom)
      pR q hgrid, ?_, ?_, hcertificate, ?_⟩
  · intro t ht j hj
    rw [restrictedMajorCorrection_fullChart_homogeneous,
      restrictedMajorCorrection_weightedHomogeneousPart]
    with_reducible exact hnext t ht j hj
  · obtain ⟨detectedfast, slow, rat, hs, hr, hK⟩ := horigin
    refine ⟨detectedfast, weightedHomogeneousPart (lowTaggedVariableWeight J k) k slow,
      weightedHomogeneousPart (lowTaggedVariableWeight J k) k rat, ?_, ?_, hK⟩
    · rw [hs, lowTaggedVectorExtend_weightedHomogeneousPart]
    · rw [hr, lowTaggedVectorExtend_weightedHomogeneousPart]
  · with_reducible
      exact fullChart_quotient_identity_homogeneous F b ω hF fast J k poly
        (fun i => (N i : ℝ)) Z left right K' hdilate pS pR (by with_reducible exact hquot)

end Certified

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.BoundedCertifiedFullChartMajorIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

namespace CertifiedFullChartFiniteHistory

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

noncomputable def initial
    (hK : ∀ t ∈ Kinitial, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ Kinitial) :
    State 0 where
  slow := fun _ => 0
  rat := fun _ => 0
  q := fun _ => 1
  K := Kinitial
  certificate := by simpa using RationalTaggedConstraintCertificate.empty (J := J) Kinitial Bphase
  subset := fun _ ht => ht
  dilation := hK
  retained := fun _ ht _ => ht
  slow_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  q_pos := fun j hj => (Nat.not_lt_zero j hj).elim
  q_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  rat_grid := fun j hj => (Nat.not_lt_zero j hj).elim
  invariant := by
    dsimp only
    intro t ht j hj
    have hj0 : j = 0 := Nat.eq_zero_of_le_zero hj
    subst j
    rw [F.realSymbolGradeEvaluation_zero]
    exact Submodule.zero_mem _

end CertifiedFullChartFiniteHistory
end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.FullChartPolynomialLiftControl
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module
open scoped BigOperators

variable {σ τ R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

noncomputable def weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) : VectorPolynomial σ R V :=
  ∑ j ∈ Finset.range (d + 1), weightedHomogeneousPart w j p

theorem coefficients_weightedDegreeTruncate (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (α : σ →₀ ℕ) :
    coefficients (weightedDegreeTruncate w d p) α =
      if Finsupp.weight w α ≤ d then coefficients p α else 0 := by
  classical
  simp [weightedDegreeTruncate, coefficients_weightedHomogeneousPart]

theorem weightedDegreeTruncate_eq_self (w : σ → ℕ) (d : ℕ)
    (p : VectorPolynomial σ R V) (hp : DegreeLE w d p) :
    weightedDegreeTruncate w d p = p := by
  classical
  apply coefficients.injective
  ext α
  rw [coefficients_weightedDegreeTruncate]
  split_ifs with h
  · rfl
  · exact (hp α (lt_of_not_ge h)).symm

section Real
variable {W : Type*} [AddCommGroup W] [Module ℚ W] [Module ℝ W] [IsScalarTower ℚ ℝ W]

theorem realChartSubstitute_weightedDegreeTruncate (w : σ → ℕ) (v : τ → ℕ)
    (f : σ → MvPolynomial τ ℝ)
    (hf : ∀ i, (f i).IsWeightedHomogeneous v (w i))
    (d : ℕ) (p : VectorPolynomial σ ℚ W) :
    realChartSubstitute f (weightedDegreeTruncate w d p) =
      weightedDegreeTruncate v d (realChartSubstitute f p) := by
  simp only [weightedDegreeTruncate, map_sum,
    realChartSubstitute_weightedHomogeneousPart w v f hf]
end Real

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieBCHGroup

open VectorPolynomial

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]
  [IsScalarTower ℚ ℝ L] {s : ℕ}

attribute [local irreducible] realChartSubstitute

theorem realPolynomialChartSubstitution_truncate_of_degreeLE
    (hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥) (w : σ → ℕ)
    (f : σ → MvPolynomial σ ℝ) (hf : ∀ i, (f i).IsWeightedHomogeneous w (w i))
    (d : ℕ) (g E : PolynomialGroup σ hnil)
    (heq : g = realPolynomialChartSubstitution hnil f E) (hg : DegreeLE w d g.coord) :
    g = realPolynomialChartSubstitution hnil f ⟨weightedDegreeTruncate w d E.coord⟩ := by
  apply NilpotentLieBCHGroup.ext
  rw [realPolynomialChartSubstitution_coord]
  have he := congrArg NilpotentLieBCHGroup.coord heq
  rw [realPolynomialChartSubstitution_coord] at he
  have ht := weightedDegreeTruncate_eq_self w d g.coord hg
  have hc := realChartSubstitute_weightedDegreeTruncate w w f hf d E.coord
  exact ht.symm.trans ((congrArg (weightedDegreeTruncate w d) he).trans hc.symm)

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.TerminalChartSlowEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

local notation "quotientReal" => ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)

theorem CertifiedFullChartDetectedDecomposition.exists_admissible_stage
    (h : CertifiedFullChartDetectedDecomposition F b ω hF J k fast basis lift
      Z left right K₀ Utag poly N budget) :
    ∃ (q : ℕ) (K' : Set (X ⊕ (Σ j, J j) → ℝ))
      (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal ×
        VectorPolynomial (X ⊕ (Σ j, J j)) ℚ quotientReal),
      FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
        Z left right K₀ Utag poly N budget q K' pair := by
  obtain ⟨pS, pR, q, K', hpair⟩ := CertifiedFullChartDetectedDecomposition.exists_homogeneous
    (F := F) (b := b) (ω := ω) (hF := hF) (fast := fast) (lift := lift)
    (J := J) (k := k) (basis := basis) (Z := Z) (left := left) (right := right)
    (K₀ := K₀) (Utag := Utag) (poly := poly) (N := N) (budget := budget) h
  refine ⟨q, K', (pS, pR), ?_⟩
  unfold FullChartAdmissibleStageCorrection
  with_reducible exact hpair

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial outer

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

theorem append_admissible_K
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    (H.append_admissible budget hbudget q K' pair hpair).K = K' :=
  (Classical.choose_spec (exists_append_admissible H budget hbudget q K' pair hpair)).2.2.2

theorem append_admissible_prefix
    {n : ℕ} (H : State n) (budget : ℝ) (hbudget : budget ≤ Bphase) (q : ℕ)
  (K' : Set (X ⊕ (Σ j, J j) → ℝ))
  (pair : VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)) ×
    VectorPolynomial (X ⊕ (Σ j, J j)) ℚ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) (j : ℕ) (hj : j < n) :
    (H.append_admissible budget hbudget q K' pair hpair).slow j = H.slow j ∧
    (H.append_admissible budget hbudget q K' pair hpair).rat j = H.rat j ∧
    (H.append_admissible budget hbudget q K' pair hpair).q j = H.q j := by
  simp only [CertifiedFullChartFiniteHistory.append_admissible_slow,
    CertifiedFullChartFiniteHistory.append_admissible_rat, CertifiedFullChartFiniteHistory.append_admissible_q,
    Function.update_of_ne (Nat.ne_of_lt hj), and_self]

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration
open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (budget : ℝ)

theorem exists_fullChart_admissible_stage_branches
    {past p : ℝ} {blocks : ℕ}
    (hprevious : RationalTaggedConstraintCertificate J Set.univ K₀ past blocks)
    (hp : 0 ≤ p) (hpast : past ≤ p) (hbudget : budget ≤ p)
    (hm : (m : ℝ) ≤ p) (hJ : (Fintype.card (Σ j, J j) : ℝ) ≤ p)
    (hblocks : ((blocks + Fintype.card η * m : ℕ) : ℝ) ≤ p) :
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * budget + (p + 8) ^ 8) ∧
      ∃ branches : Fin n → ℕ × Set ((X ⊕ (Σ j, J j)) → ℝ),
        (∀ i, 0 < (branches i).1 ∧
          (branches i).1 ≤ ⌊Real.exp ((Fintype.card η : ℝ) * budget)⌋₊ ∧
          RationalTaggedConstraintCertificate J Set.univ (branches i).2 p
            (blocks + Fintype.card η * m)) ∧
        ∀ q K' pair, FullChartAdmissibleStageCorrection F b ω hF J k fast basis lift
          Z left right K₀ Utag poly N budget q K' pair →
          ∃ i, branches i = (q, K') := by
  obtain ⟨n, hn, branches, hvalid, hcover⟩ :=
    exists_finite_rational_stage_branches Set.univ p ((Fintype.card η : ℝ) * budget)
      hp (blocks + Fintype.card η * m) hm hJ hblocks
  refine ⟨n, hn, branches, hvalid, ?_⟩
  intro q K' pair hpair
  rcases hpair with ⟨_, _, _, _, hq, hqB, _, _, _, _, _, _, _, hcertificate, _⟩
  exact hcover q K' hq hqB
    ((hprevious.monoB hpast).trans (hcertificate.monoB hbudget))

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial PolynomialTranslationLie RationalFilteredNilmanifold
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeQuotientPolynomial realSymbolGradeEvaluation restrictedMajorCorrection

variable {m : ℕ} {X : Type}
variable {ι L η : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)] (k : ℕ)
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z left right : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (K₀ : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (budget : ℝ)

noncomputable def fullChartStageCountConstant (k a : ℕ) : ℕ :=
  Classical.choose (exists_finite_primitive_correction_budget k a)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] realSymbolGradeEvaluation restrictedMajorCorrection
  realSymbolGradeQuotientPolynomial outer realChartSubstitute

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}

variable (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
variable (J : Fin m → Type) [∀ j, Fintype (J j)]
variable (fast : Submodule ℚ F.AssociatedGraded)
variable (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
variable (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
variable (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
variable (Kinitial : Set (X ⊕ (Σ j, J j) → ℝ))
variable (Utag : ∀ j, Submodule ℝ (J j → ℝ))
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (N : X → ℕ) (Bphase : ℝ)

local notation "wt" => fullTaggedVariableWeight (X := X) J
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase

variable {F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase}

structure StageBounds (cap cumulative : ℕ → ℝ) {n : ℕ} (H : State n) : Prop where
  certificate : RationalTaggedConstraintCertificate J Kinitial H.K (cumulative n)
    (n * (Fintype.card η * m))
  slow_bound : ∀ j < n, ∀ α i,
    |basis.coord i (coefficients (H.slow j) α)| ≤ Real.exp (cap j)
  q_bound : ∀ j < n, (H.q j : ℝ) ≤ Real.exp ((Fintype.card η : ℝ) * cap j)

theorem StageBounds.initial (cap cumulative : ℕ → ℝ)
    (hK : ∀ t ∈ Kinitial, ∀ r : ℚ, (fun i => (r : ℝ) ^ wt i * t i) ∈ Kinitial) :
    StageBounds cap cumulative
      (initial F b ω hF J fast basis lift Z Kinitial Utag poly N Bphase hK) where
  certificate := by
    unfold CertifiedFullChartFiniteHistory.initial
    simpa only [Nat.zero_mul] using
      RationalTaggedConstraintCertificate.empty (J := J) Kinitial (cumulative 0)
  slow_bound := fun j hj => (Nat.not_lt_zero j hj).elim
  q_bound := fun j hj => (Nat.not_lt_zero j hj).elim

theorem StageBounds.of_admissible_child {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (Hnext : State (n + 1))
    (hprefix : ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (cap n) (Hnext.q n) Hnext.K
        (Hnext.slow n, Hnext.rat n))
    (hmono : cumulative n ≤ cumulative (n + 1)) (hcap : cap n ≤ cumulative (n + 1)) :
    StageBounds cap cumulative Hnext := by
  have hcoeff := hpair.2.2.2.2.2.2.2.2.2.1
  have hq := hpair.2.2.2.2.2.1
  have hcert := hpair.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.succ_mul] using
      (hH.certificate.monoB hmono).trans (hcert.monoB hcap)
  · intro j hj α i
    by_cases h : j = n
    · subst j
      exact hcoeff α i
    · rw [(hprefix j (by omega)).1]
      exact hH.slow_bound j (by omega) α i
  · intro j hj
    by_cases h : j = n
    · subst j
      exact hq
    · rw [(hprefix j (by omega)).2.2]
      exact hH.q_bound j (by omega)

noncomputable def StageBounds.to_budget {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (hcap : ∀ j < n, cap j ≤ cumulative n) :
    CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z Kinitial Utag poly N
      (cumulative n) n where
  slow := H.slow
  rat := H.rat
  q := H.q
  K := H.K
  certificate := hH.certificate
  subset := H.subset
  dilation := H.dilation
  retained := H.retained
  slow_bound := fun j hj α i => (hH.slow_bound j hj α i).trans (Real.exp_le_exp.mpr (hcap j hj))
  q_pos := H.q_pos
  q_bound := fun j hj => (hH.q_bound j hj).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hcap j hj) (Nat.cast_nonneg _)))
  rat_grid := H.rat_grid
  invariant := H.invariant

theorem StageBounds.to_budget_outer {n : ℕ}
    {cap cumulative : ℕ → ℝ} {H : State n} (hH : StageBounds cap cumulative H)
    (hcap : ∀ j < n, cap j ≤ cumulative n) :
    outer F b ω hF J fast basis lift Z Kinitial Utag poly N (cumulative n)
      (hH.to_budget hcap) = H.outer := by
  unfold outer
  apply F.restrictedMajorOuterFactors_congr
  · intro j hj
    unfold StageBounds.to_budget
    rfl
  · intro j hj
    unfold StageBounds.to_budget
    rfl

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartBudgetedTreeBounds
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase
local notation "chart" => normalizedRealPolynomialChart (fun i => (N i : ℝ))
  (fullTaggedMajorTopCoordinates J poly)

def AdmissibleChild {n : ℕ} (H : State n) (Hnext : State (n + 1)) : Prop :=
  FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N Bphase (Hnext.q n) Hnext.K
      (Hnext.slow n, Hnext.rat n) ∧
  ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j

def RepresentsCorrection {n : ℕ} (Hnext : State (n + 1)) (q : ℕ)
    (K' : Set Point) (pair : VP × VP) : Prop :=
  Hnext.q n = q ∧ Hnext.K = K' ∧ ∀ t ∈ K',
    eval₂ t (Hnext.slow n) = eval₂ t pair.1 ∧
    eval₂ t (Hnext.rat n) = eval₂ t pair.2 ∧
    eval₂ t (realChartSubstitute chart (Hnext.slow n)) =
      eval₂ t (realChartSubstitute chart pair.1)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

structure FiniteBranchTree (depth : ℕ) (p : ℝ) where
  children : ∀ n, State n → Finset (State (n + 1))
  card : ∀ n, n < depth → ∀ H, (children n H).card ≤
    ⌈Real.exp ((Fintype.card η : ℝ) * Bphase + (p + 8) ^ 8 +
      (p + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254)⌉₊
  admissible : ∀ n, n < depth → ∀ H Hnext, Hnext ∈ children n H →
    AdmissibleChild F b ω hF J fast basis lift Z Utag poly N Bphase H Hnext
  complete : ∀ n, n < depth → ∀ H q K' pair,
    FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N Bphase q K' pair →
    ∃ Hnext ∈ children n H, RepresentsCorrection F b ω hF J fast basis lift Z
      Utag poly N Bphase Hnext q K' pair

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

variable (F b ω hF J fast basis lift Z Utag poly N Bphase)

noncomputable def univInitialHistory : State 0 :=
  initial F b ω hF J fast basis lift Z Set.univ Utag poly N Bphase
    (fun _ _ _ => Set.mem_univ _)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {depth : ℕ} {p : ℝ}

noncomputable def FiniteBranchTree.level
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    (n : ℕ) : Finset (State n) :=
  finiteGradedBranchLevel (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children n

omit [Fintype X] in

theorem FiniteBranchTree.exists_representative_child
    (T : FiniteBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase depth p)
    {n : ℕ} (hn : n < depth) {H : State n} (hH : H ∈ T.level n)
    (q : ℕ) (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N Bphase q K' pair) :
    ∃ Hnext ∈ T.level (n + 1),
      AdmissibleChild F b ω hF J fast basis lift Z Utag poly N Bphase H Hnext ∧
      RepresentsCorrection F b ω hF J fast basis lift Z Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨Hnext, hmem, hrep⟩ := T.complete n hn H q K' pair hpair
  exact ⟨Hnext, finiteGradedBranchLevel_child_mem _ T.children hH hmem,
    T.admissible n hn H Hnext hmem, hrep⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

def AdmissibleChildAt (budget : ℝ) {n : ℕ} (H : State n) (Hnext : State (n + 1)) : Prop :=
  FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
    Z H.outer.1 H.outer.2 H.K Utag poly N budget (Hnext.q n) Hnext.K
      (Hnext.slow n, Hnext.rat n) ∧
  ∀ j < n, Hnext.slow j = H.slow j ∧ Hnext.rat j = H.rat j ∧ Hnext.q j = H.q j

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}

omit [Fintype X] in
theorem append_admissible_is_child_at {n : ℕ} (H : State n)
    (budget : ℝ) (hcap : budget ≤ Bphase) (q : ℕ)
    (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N budget q K' pair) :
    AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase budget H
      (H.append_admissible budget hcap q K' pair hpair) := by
  refine ⟨?_, fun j hj => append_admissible_prefix H budget hcap q K' pair hpair j hj⟩
  rw [append_admissible_K, (append_admissible_entry H budget hcap q K' pair hpair).1,
    (append_admissible_entry H budget hcap q K' pair hpair).2.1,
    (append_admissible_entry H budget hcap q K' pair hpair).2.2]
  exact hpair

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

local notation "Point" => (X ⊕ (Σ j, J j) → ℝ)
local notation "VP" => VectorPolynomial (X ⊕ (Σ j, J j)) ℚ
  (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))
local notation "State" => CertifiedFullChartFiniteHistory F b ω hF J fast basis lift Z
  Set.univ Utag poly N Bphase

variable (stageBudget : ℕ → ℝ)

structure BudgetedBranchTree (depth : ℕ) (p : ℝ) where
  children : ∀ n, State n → Finset (State (n + 1))
  card : ∀ n, n < depth → ∀ H, (children n H).card ≤
    ⌈Real.exp ((Fintype.card η : ℝ) * stageBudget n + (p + 8) ^ 8 +
      (p + fullChartStageCountConstant (n + 1) 254) ^
        fullChartStageCountConstant (n + 1) 254)⌉₊
  admissible : ∀ n, n < depth → ∀ H Hnext, Hnext ∈ children n H →
    AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase (stageBudget n) H Hnext
  complete : ∀ n, n < depth → ∀ H q K' pair,
    FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (stageBudget n) q K' pair →
    ∃ Hnext ∈ children n H, RepresentsCorrection F b ω hF J fast basis lift Z
      Utag poly N Bphase Hnext q K' pair

variable {F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget}

variable {depth : ℕ} {p : ℝ}

noncomputable def BudgetedBranchTree.level
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (n : ℕ) : Finset (State n) :=
  finiteGradedBranchLevel (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children n

omit [Fintype X] in

theorem BudgetedBranchTree.exists_representative_child
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    {n : ℕ} (hn : n < depth) {H : State n} (hH : H ∈ T.level n)
    (q : ℕ) (K' : Set Point) (pair : VP × VP)
    (hpair : FullChartAdmissibleStageCorrection F b ω hF J (n + 1) fast basis lift
      Z H.outer.1 H.outer.2 H.K Utag poly N (stageBudget n) q K' pair) :
    ∃ Hnext ∈ T.level (n + 1),
      AdmissibleChildAt F b ω hF J fast basis lift Z Utag poly N Bphase (stageBudget n) H Hnext ∧
      RepresentsCorrection F b ω hF J fast basis lift Z Utag poly N Bphase Hnext q K' pair := by
  obtain ⟨Hnext, hmem, hrep⟩ := T.complete n hn H q K' pair hpair
  exact ⟨Hnext, finiteGradedBranchLevel_child_mem _ T.children hH hmem,
    T.admissible n hn H Hnext hmem, hrep⟩

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (J : Fin m → Type) [∀ j, Fintype (J j)]
  (fast : Submodule ℚ F.AssociatedGraded)
  (basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast)))
  (lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded)
  (Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J))
  (Utag : ∀ j, Submodule ℝ (J j → ℝ))
  (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)) (N : X → ℕ) (Bphase : ℝ)

variable {F b ω hF J fast basis lift Z Utag poly N Bphase}
variable {stageBudget cumulative : ℕ → ℝ} {depth : ℕ} {p : ℝ}

omit [Fintype X] in

theorem BudgetedBranchTree.stage_bounds
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase stageBudget depth p)
    (hmono : ∀ n < depth, cumulative n ≤ cumulative (n + 1))
    (hcap : ∀ n < depth, stageBudget n ≤ cumulative (n + 1)) :
    ∀ n, n ≤ depth → ∀ H ∈ T.level n, StageBounds stageBudget cumulative H := by
  apply finiteGradedBranchLevel_all_valid
    (univInitialHistory F b ω hF J fast basis lift Z Utag poly N Bphase)
    T.children depth (fun _ H => StageBounds stageBudget cumulative H)
  · unfold univInitialHistory
    exact StageBounds.initial stageBudget cumulative (fun _ _ _ => Set.mem_univ _)
  · intro n hn H _ hH Hnext hnext
    have hadmissible := T.admissible n hn H Hnext hnext
    exact hH.of_admissible_child Hnext hadmissible.2 hadmissible.1
      (hmono n hn) (hcap n hn)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.CertifiedFullChartForwardEarlyTree
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

noncomputable def stageBranchLog (dim n : ℕ) (cap p : ℝ) : ℝ :=
  (dim : ℝ) * cap + (p + 8) ^ 8 +
    (p + fullChartStageCountConstant (n + 1) 254) ^
      fullChartStageCountConstant (n + 1) 254

variable {m : ℕ} {X : Type} [Fintype X] {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}

omit [Fintype X] in

theorem BudgetedBranchTree.card_level_le_prefix_exp
    {cap : ℕ → ℝ} {depth : ℕ} {pTree : ℝ}
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase cap depth pTree)
    (pCount : ℕ → ℝ)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤
        Real.exp (stageBranchLog (Fintype.card η) n (cap n) (pCount n)))
    (n : ℕ) (hn : n ≤ depth) :
    ((T.level n).card : ℝ) ≤ Real.exp
      (∑ j ∈ Finset.range n, stageBranchLog (Fintype.card η) j (cap j) (pCount j)) :=
  finiteGradedBranchLevel_card_le_exp_sum _ T.children depth
    (fun j => stageBranchLog (Fintype.card η) j (cap j) (pCount j)) hsharp n hn

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

section

namespace Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory
open Module VectorPolynomial
open scoped TensorProduct Classical BigOperators

attribute [local irreducible] FullChartAdmissibleStageCorrection
  realSymbolGradeEvaluation restrictedMajorCorrection outer fullChartStageCountConstant

variable {m : ℕ} {X : Type} {ι L η : Type*}
  [LieRing L] [LieAlgebra ℚ L] [Fintype η] {s : ℕ}
  {F : NilpotentLieFiltration L s} {b : Basis ι ℚ L} {ω : ι → ℕ}
  {hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})}
  {J : Fin m → Type} [∀ j, Fintype (J j)]
  {fast : Submodule ℚ F.AssociatedGraded}
  {basis : Basis η ℝ (ℝ ⊗[ℚ] (F.AssociatedGraded ⧸ fast))}
  {lift : (F.AssociatedGraded ⧸ fast) →ₗ[ℚ] F.AssociatedGraded}
  {Z : F.RealPolynomialSymbolGroup (fullTaggedVariableWeight (X := X) J)}
  {Utag : ∀ j, Submodule ℝ (J j → ℝ)}
  {poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ)} {N : X → ℕ} {Bphase : ℝ}
  {depth : ℕ} {pTree : ℝ}

local notation "Cstage" => fun n => fullChartStageCountConstant (n + 1) 254

theorem BudgetedBranchTree.card_level_le_forward_prefix
    (A : ℕ) {x : ℝ} (hx : 0 ≤ x) (hd : (Fintype.card η : ℝ) ≤ x)
    (T : BudgetedBranchTree F b ω hF J fast basis lift Z Utag poly N Bphase
      (fun n => preparedFiniteForwardCap A Cstage n x) depth pTree)
    (hsharp : ∀ n, n < depth → ∀ history ∈ T.level n,
      ((T.children n history).card : ℝ) ≤ Real.exp
        (stageBranchLog (Fintype.card η) n (preparedFiniteForwardCap A Cstage n x)
          (preparedFiniteForwardCount A Cstage n x)))
    (n : ℕ) (hn : n ≤ depth) :
    ((T.level n).card : ℝ) ≤ Real.exp (preparedFiniteForwardPrefixLog A Cstage n x) := by
  apply (T.card_level_le_prefix_exp
    (fun j => preparedFiniteForwardCount A Cstage j x) hsharp n hn).trans
  apply Real.exp_le_exp.mpr
  exact Finset.sum_le_sum (fun j _ =>
    preparedFiniteForward_branch_count_log A Cstage j hx hd)

end Erdos3.NilpotentLieFiltration.CertifiedFullChartFiniteHistory

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.PrimeStabilityTree
namespace OAI

section

namespace Erdos3

open PhysicalEpochStack
open scoped BigOperators

universe u v w

namespace PrimeStabilityContext

variable {ι : Type w} {σ : Type u} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
  {s bound : ℕ}

noncomputable def State.rank {ctx : PrimeStabilityContext.{u, v, w} ι σ s bound}
    {I : Finset ι} {x : ∀ i, σ → ZMod (ctx.moduli i)} (state : ctx.State I x) : ℕ :=
  epochStackRank bound state.stack.dimensions

end PrimeStabilityContext

end Erdos3

end

end OAI
end


