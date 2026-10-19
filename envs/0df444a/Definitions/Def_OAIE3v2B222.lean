-- Prove2me | Definitions.Def_OAIE3v2B222
-- name    : OAIE3v2B222
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-18T04:30:45.124426+00:00
-- url     : https://prove2.me/theorems/48dff035-e615-45a8-afc1-985ead29c357
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 227 of 311
-- statement:
--   Definitions bundle 227 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B199`, `OAIE3v2B200`, `OAIE3v2B201`, `OAIE3v2B202` of this split.
--
--   Modules: `Dynamics/UniformFormalInductionIteration.lean`, `Estimates/CommonFreeSunflower.lean`, `Estimates/FastGradedRelativeInvariance.lean`, `Estimates/FormalInductionStage.lean`, `Estimates/GradedUnitEvaluation.lean`, `Estimates/NativeWeightPairRemoval.lean`, `Estimates/TerminalControlledFactorization.lean`, `Estimates/UnnormalizedCommonSymbolFactorization.lean`, `Linear/FullFastHorizontalSpanning.lean`, `Polynomial/GradedPolynomialSymbolInverse.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B199
import Definitions.Def_OAIE3v2B200
import Definitions.Def_OAIE3v2B201
import Definitions.Def_OAIE3v2B202

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.GradedUnitEvaluation
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

theorem reducedSquareGradedDifference_unit (x : F.squareFiltration.quotientTop.AssociatedGraded) :
    eval (fun _ : Unit => (1 : ℚ))
      (F.firstCoefficientGradedPolynomial e ω hF (fun _ : Unit => 1)
        (F.reducedSquareCoefficientMap (fun _ : Unit => 1) x)) =
      F.reducedSquareGradedDifference e ω hF x := by
  rw [F.firstCoefficientGradedPolynomial_reducedSquare, eval_map,
    F.squareFiltration.quotientTop.gradedSymbolPolynomial_unit_eval]

theorem reducedSquareGradedDifference_relative_lie
    (a : F.adaptedLieSubalgebra (fun _ : Unit => 1))
    (p : F.normalizedRelativeSubmodule (fun _ : Unit => 1)) :
    F.reducedSquareGradedDifference e ω hF
      ⁅F.reducedSquareDiagonalSymbolMap (fun _ : Unit => 1)
          (F.adaptedReducedSymbolMap (fun _ : Unit => 1) a),
        F.reducedRelativeSquareSymbolMap (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p⁆ =
      ⁅F.polynomialSymbolMap (fun _ : Unit => 1) a,
        F.reducedSquareGradedDifference e ω hF
          (F.reducedRelativeSquareSymbolMap (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p)⁆ := by
  rw [← F.reducedRelativeSquareSymbolMap_lie,
    ← F.reducedSquareGradedDifference_unit, F.reducedSquareCoefficientMap_relative,
    F.firstCoefficientGradedPolynomial_normalized_lie]
  change (evalLie (fun _ : Unit => (1 : ℚ))) ⁅_, _⁆ = _
  rw [LieHom.map_lie]
  simp only [evalLie_apply]
  rw [F.adaptedGradedPolynomialLie_unit_eval,
    ← F.reducedSquareCoefficientMap_relative (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one) p,
    F.reducedSquareGradedDifference_unit]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι κ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))

local notation "bG" => F.associatedGradedBasis e ω hF

theorem realLayerOneGradedMap_pure (x : ℝ ⊗[ℚ] (L ⧸ F.layer 2)) :
    basisGradeProjection ((bG).baseChange ℝ) ω 1 ((F.layerOneGradedMap e ω hF).baseChange ℝ x) =
      (F.layerOneGradedMap e ω hF).baseChange ℝ x := by
  change basisCoordinateProjection ((bG).baseChange ℝ) {i | ω i = 1}
    ((F.layerOneGradedMap e ω hF).baseChange ℝ x) = _
  rw [← basisCoordinateProjection_baseChange]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul]
    exact congrArg (fun y => a ⊗ₜ[ℚ] y) (F.layerOneGradedMap_pure e ω hF x)

theorem gradedHorizontalKernel_real_pure (K : Submodule ℚ (L ⧸ F.layer 2))
    (x : ℝ ⊗[ℚ] F.AssociatedGraded) (hx : x ∈ (F.gradedHorizontalKernel e ω hF K).baseChange ℝ) :
    basisGradeProjection ((bG).baseChange ℝ) ω 1 x = x := by
  rw [gradedHorizontalKernel, realification_map] at hx
  obtain ⟨y, _, rfl⟩ := hx
  exact F.realLayerOneGradedMap_pure e ω hF y

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.GradedPolynomialSymbolInverse
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem realAdaptedGradedPolynomialHom_correction
    (hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis e ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers e ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (g : F.realFastDiagonalSubgroup (fun _ : σ => 1) (F.fastPointwiseSquare e ω hF (fun _ => 1) W)) :
    F.associatedGradedFiltration.FormalCorrectionProperty (F.associatedGradedBasis e ω hF) ω
      (realificationLieSubalgebra (F.fullFastGradedDiagonal W))
      (F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1) g.val) :=
  ⟨F.realAdaptedGradedPolynomialLie_fullFast_mem e ω hF W hW g,
    F.realAdaptedGradedPolynomialLie_graded e ω hF (fun _ : σ => 1) g.val.coord,
    F.realAdaptedGradedPolynomialLie_constant e ω hF (fun _ : σ => 1) g.val.coord⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FormalInductionStage
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_stage (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ ν τ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype ν] [Fintype τ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K Ebr Ecur : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (eBr : Basis ν ℚ Ebr) (eCur : Basis τ ℚ Ecur)
    (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {j H : ℕ} (_hj : 2 ≤ j) (_hH : 1 ≤ H)
    (_hBrGrade : ∀ x ∈ Ebr.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w (j - 1) x = x)
    (_hBrU : Ebr.baseChange ℝ ≤ U.toSubmodule)
    (_hBrK : j = 2 → Ebr.baseChange ℝ ≤ K.baseChange ℝ)
    (_hBrV : 2 < j → Ebr.baseChange ℝ ≤ V.baseChange ℝ)
    (_hCurGrade : ∀ x ∈ Ecur.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w j x = x)
    (_hCurU : Ecur.baseChange ℝ ≤ U.toSubmodule)
    (_hCurProjection : ∀ x ∈ U, basisGradeProjection (b.baseChange ℝ) w j x ∈ Ecur.baseChange ℝ)
    (_hBracketMatrix : ∀ i z, RationalHeightLE (bracketSystemMatrix eBr f (fun z => (eK z : L)) i z) H)
    (_hCurrentMatrix : ∀ i z, RationalHeightLE (subspaceQuotientMatrix eCur f i z) H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hBracketBasis : ∀ i z, RationalHeightLE (b.repr (eBr z : L) i) H)
    (_hCurrentBasis : ∀ i z, RationalHeightLE (b.repr (eCur z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hν : (Fintype.card ν : ℝ) ≤ p)
    (_hτ : (Fintype.card τ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hjp : (j : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T j p)
    (_hBracketSource : ∀ α, basisGradeProjection (b.baseChange ℝ) w (j - 1)
      (coefficients X.P.coord α) ∈ Ebr.baseChange ℝ),
    ∃ (Y : F.FormalInductionState b w U V K eK T (j + 1) ((p + C) ^ C))
      (A₁ A₂ B₁ B₂ : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot),
      (A₁ * A₂) * Y.P * (B₂ * B₁) = X.P ∧
      (∀ α, coefficients A₁.coord α ∈ U ∧ coefficients A₂.coord α ∈ U ∧
        coefficients B₁.coord α ∈ U ∧ coefficients B₂.coord α ∈ U) ∧
      (A₁.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        A₂.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        B₁.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
        B₂.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)) ∧
      (coefficients A₁.coord 0 = 0 ∧ coefficients A₂.coord 0 = 0 ∧
        coefficients B₁.coord 0 = 0 ∧ coefficients B₂.coord 0 = 0) ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A₁.coord ∧
      CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A₂.coord ∧
      CoefficientGrid (b.baseChange ℝ) Y.denominator B₁.coord ∧
      CoefficientGrid (b.baseChange ℝ) Y.denominator B₂.coord := by
  classical
  obtain ⟨D, _, hbracketStage⟩ := exists_uniform_controlled_bracket_stage s
  obtain ⟨E, _, hcurrentStage⟩ := exists_uniform_controlled_current_stage s
  obtain ⟨C, hC, hbudget⟩ := exists_formal_stage_budget D E
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ ν τ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K Ebr Ecur hUV hV
    eK eBr eCur f hK j H hj hH hBrGrade hBrU hBrK hBrV hCurGrade hCurU hCurProjection
    hBracketMatrix hCurrentMatrix hKernelBasis hBracketBasis hCurrentBasis hQuotient hStructure
    p hp hμ hι hκ hν hτ hσ hjp hHp T hT X hBracketSource
  let d := (p + D) ^ D
  let t := p + d
  let u := bracketTransitionBudget t
  let v := bracketConstructionBudget u
  let q := u + v
  let z := (q + E) ^ E
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hu : 0 ≤ u := bracketTransitionBudget_nonneg ht
  have hv : 0 ≤ v := bracketConstructionBudget_nonneg hu
  have hq : 0 ≤ q := add_nonneg hu hv
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hpt : p ≤ t := le_add_of_nonneg_right hd
  have htu : t ≤ u := le_bracketTransitionBudget ht
  have huv : u ≤ v := (bracket_construction_budget_bounds hu).1
  have huq : u ≤ q := le_add_of_nonneg_right hv
  have hvq : v ≤ q := le_add_of_nonneg_left hu
  have hpu : p ≤ u := hpt.trans htu
  have hpq : p ≤ q := hpu.trans huq
  have hcap : d + z + 1 ≤ (p + C) ^ C := hbudget p hp
  have hdCap : d ≤ (p + C) ^ C := by linarith
  have hzCap : z ≤ (p + C) ^ C := by linarith
  have hsumCap : d + z ≤ (p + C) ^ C := by linarith
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hTD : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hdCap).trans (hT i)
  have hk (r : κ) : basisGradeProjection (b.baseChange ℝ) w 1 ((1 : ℝ) ⊗ₜ[ℚ] (eK r : L)) =
      (1 : ℝ) ⊗ₜ[ℚ] (eK r : L) := by
    have h := hK _ (bracketSystemLift_mem eK (Pi.single r 1))
    rw [bracketSystemLift_single] at h
    exact h
  obtain ⟨n₀, A₁, B₁, hn₀, hn₀bound, hAB₁, hAhom₁, hBhom₁, hAnorm₁, hBgrid₁,
    hprod₁, hconstant₁, hgraded₁, hU₁, hbelow₁, hbrackets₁, hlifts₁, hrems₁,
    hrawSystem, hliftControls₁, hderivControls₁⟩ :=
    hbracketStage F b w hF hgraded hs U hUV hV eBr f (fun r => (eK r : L)) hk hj
      hBrGrade hBrU hH X.denominator_pos hBracketMatrix hBracketBasis hQuotient hStructure hp
      hμ hι hκ hν hσ hHp hHp hHp X.denominator_bound T hTD X.P X.mem_U X.graded
      hBracketSource X.S X.R X.lift_system X.S_shift X.R_shift X.S_remainder X.R_remainder
      X.lower_bracket X.S_bound X.R_grid X.small X.rational
      (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) X.S (X.k i)) X.derivative_system
      X.small_shift X.rational_shift X.small_bound X.rational_grid
  let P₁ := A₁⁻¹ * X.P * B₁⁻¹
  let S₁ := fun r => dualAdjoint A₁⁻¹ (X.S r)
  let R₁ := fun r => dualAdjoint B₁ (X.R r)
  have hA₁bound : CoefficientBound (b.baseChange ℝ) T (Real.exp d) A₁.coord :=
    (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) _).mpr hAnorm₁
  have hdt : d ≤ t := le_add_of_nonneg_left hp
  have hExpdt : Real.exp d ≤ Real.exp t := Real.exp_le_exp.mpr hdt
  obtain ⟨a, c, n₁, hn₁, hn₁bound, hmidU, hmidK, hmidLower, hmidLift,
    hmidSystem, hmidRemainders, hmidExtra, hmidEquation, hmidBracket, hmidControls, hmidLiftControls⟩ :=
    F.exists_controlled_bracket_to_current_layer b w hF hs U (V.baseChange ℝ) hUV hV eK hK
      hj hH hn₀ hKernelBasis ht (hμ.trans hpt) (hκ.trans hpt)
      (hHp.trans (Real.exp_le_exp.mpr hpt)) (hn₀bound.trans hExpdt) T hTpos X.P A₁ B₁
      X.mem_U (fun α => hBrU (hAB₁ α).1) (fun α => hBrU (hAB₁ α).2)
      (fun α => hBrGrade _ (hAB₁ α).1) (fun α => hBrGrade _ (hAB₁ α).2)
      hAhom₁ hBhom₁ (fun h α => hBrK h (hAB₁ α).1) (fun h α => hBrK h (hAB₁ α).2)
      (fun h α => hBrV h (hAB₁ α).1) (fun h α => hBrV h (hAB₁ α).2)
      X.horizontal X.lower_log X.S X.R X.small X.rational X.k X.lift_system X.derivative_system
      X.small_remainder X.rational_remainder (fun r α => (hrems₁ r α).1)
      (fun r α => (hrems₁ r α).2.1) (fun r α => (hrems₁ r α).2.2)
      (hA₁bound.mono _ T hTpos hExpdt) hBgrid₁
      (fun r => (hliftControls₁ r).1.mono _ T hTpos hExpdt)
      (fun r => (hliftControls₁ r).2.1)
      (fun i => (hderivControls₁ i).1.mono _ T hTpos
        (div_le_div_of_nonneg_right hExpdt (hTpos i).le))
      (fun i => (hderivControls₁ i).2.1)
      (fun r => (hliftControls₁ r).2.2.1) (fun r => (hliftControls₁ r).2.2.2)
      (fun i => (hderivControls₁ i).2.2.1) (fun i => (hderivControls₁ i).2.2.2)
  let Smap₁ := (dualAdjointAddEquiv A₁⁻¹).toAddMonoidHom.comp
    (basisPolynomialLift (Pi.basisFun ℝ κ) X.S).toAddMonoidHom
  let Rmap₁ := (dualAdjointAddEquiv B₁).toAddMonoidHom.comp
    (basisPolynomialLift (Pi.basisFun ℝ κ) X.R).toAddMonoidHom
  let small₁ := fun i => dualAdjoint A₁⁻¹ (X.small i - formalLogDerivative i A₁) +
    if j = 2 then Smap₁ (a i) else 0
  let rational₁ := fun i => dualAdjoint B₁ (X.rational i) - formalLogDerivative i B₁ +
    if j = 2 then Rmap₁ (c i) else 0
  let k₁ := fun i => if j = 2 then X.k i - a i - c i else X.k i
  let extra₁ := fun i => Smap₁ (k₁ i)
  have hHpu : (H : ℝ) ≤ Real.exp u := hHp.trans (Real.exp_le_exp.mpr hpu)
  obtain ⟨nQ, hnQ, hnQbound, hprojectedBound, hprojectedGrid⟩ :=
    uniform_current_layer_inputs_from_ambient b w f j hn₁ hQuotient hu
      (hμ.trans hpu) (hι.trans hpu) hHpu hn₁bound T hTpos small₁ rational₁
      (fun i => (hmidControls i).1) (fun i => (hmidControls i).2.1)
  let nInput := n₁ * nQ
  have hnInput : 0 < nInput := Nat.mul_pos hn₁ hnQ
  have hn₁Input : n₁ ∣ nInput := dvd_mul_right n₁ nQ
  have hnQInput : nQ ∣ nInput := dvd_mul_left nQ n₁
  have hInputBound : (nInput : ℝ) ≤ Real.exp q := by
    calc
      _ = (n₁ : ℝ) * (nQ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp u * Real.exp v := mul_le_mul hn₁bound hnQbound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp q := (Real.exp_add _ _).symm
  have hTE : ∀ i, Real.exp ((q + E) ^ E) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hzCap).trans (hT i)
  have hHq : (H : ℝ) ≤ Real.exp q := hHp.trans (Real.exp_le_exp.mpr hpq)
  have hEuq : Real.exp u ≤ Real.exp q := Real.exp_le_exp.mpr huq
  have hP₁cur : ∀ α, basisGradeProjection (b.baseChange ℝ) w j (coefficients P₁.coord α) ∈ Ecur.baseChange ℝ :=
    fun α => hCurProjection _ (hmidU α)
  obtain ⟨n₂, A₂, B₂, hn₂, hn₂bound, hAB₂, hAhom₂, hBhom₂, hAnorm₂, hBgrid₂,
    hprod₂, hconstant₂, hgraded₂, hU₂, hcurrent₂, hbelow₂, hsystem₂, hshift₂,
    hremainders₂, hK₂, hlower₂, hbracket₂, hextra₂, hlifts₂, hliftRemainders₂,
    hliftControls₂, hderivControls₂⟩ :=
    hcurrentStage F b w hF hgraded hs U (K.baseChange ℝ) hUV hV eCur f hj hCurGrade hCurU
      hH hnInput hCurrentMatrix hCurrentBasis hQuotient hStructure hq (Real.exp_nonneg v)
      (hμ.trans hpq) (hι.trans hpq) (hτ.trans hpq) (hσ.trans hpq) (hjp.trans hpq)
      hHq hHq hHq hInputBound (Real.exp_le_exp.mpr hvq) T hTE P₁
      hmidU hgraded₁ hP₁cur hmidK hmidLower hmidBracket small₁ rational₁ extra₁
      (fun i α => (hmidRemainders i α).1) (fun i α => (hmidRemainders i α).2)
      hmidExtra hmidSystem (fun i => (hmidControls i).2.2.1) (fun i => (hmidControls i).2.2.2)
      hprojectedBound (fun i α => realDenominatorGrid_subset_of_dvd hnQ hnQInput (hprojectedGrid i α))
      S₁ R₁ (fun r => (1 : ℝ) ⊗ₜ[ℚ] (eK r : L))
      (fun r => (hliftControls₁ r).2.2.1) (fun r => (hliftControls₁ r).2.2.2)
      hlifts₁ (fun r α => (hrems₁ r α).1) (fun r α => (hrems₁ r α).2.1)
      (fun r => (hmidLiftControls r).1.mono _ T hTpos hEuq)
      (fun r α => realDenominatorGrid_subset_of_dvd hn₁ hn₁Input ((hmidLiftControls r).2 α))
      (fun i => (hmidControls i).1.mono _ T hTpos (div_le_div_of_nonneg_right hEuq (hTpos i).le))
      (fun i α => realDenominatorGrid_subset_of_dvd hn₁ hn₁Input ((hmidControls i).2.1 α))
  let P₂ := A₂⁻¹ * P₁ * B₂⁻¹
  let S₂ := fun r => dualAdjoint A₂⁻¹ (S₁ r)
  let R₂ := fun r => dualAdjoint B₂ (R₁ r)
  let small₂ := fun i => dualAdjoint A₂⁻¹ (small₁ i - formalLogDerivative i A₂)
  let rational₂ := fun i => dualAdjoint B₂ (rational₁ i) - formalLogDerivative i B₂
  let n := n₀ * n₂
  have hn : 0 < n := Nat.mul_pos hn₀ hn₂
  have hn₀n : n₀ ∣ n := dvd_mul_right n₀ n₂
  have hn₂n : n₂ ∣ n := dvd_mul_left n₂ n₀
  have hnBound : (n : ℝ) ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ = (n₀ : ℝ) * (n₂ : ℝ) := Nat.cast_mul _ _
      _ ≤ Real.exp d * Real.exp z := mul_le_mul hn₀bound hn₂bound (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (d + z) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hsumCap
  have hEz : Real.exp z ≤ Real.exp ((p + C) ^ C) := Real.exp_le_exp.mpr hzCap
  have hS₁eval (x : κ → ℝ) : basisPolynomialLift (Pi.basisFun ℝ κ) S₁ x = Smap₁ x := by
    rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
      (Pi.basisFun ℝ κ) A₁⁻¹ X.S]
    rfl
  have hextraEq : (fun i => dualAdjoint A₂⁻¹ (extra₁ i)) =
      fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S₂ (k₁ i) := by
    funext i
    rw [basisPolynomialLift_adjoint (hnil := F.realification.lowerCentralSeries_eq_bot)
      (Pi.basisFun ℝ κ) A₂⁻¹ S₁]
    change dualAdjoint A₂⁻¹ (Smap₁ (k₁ i)) =
      dualAdjoint A₂⁻¹ (basisPolynomialLift (Pi.basisFun ℝ κ) S₁ (k₁ i))
    rw [hS₁eval]
  have hsystemFinal : PolynomialDerivativeSystemMod ((V.baseChange ℝ).restrictScalars ℚ)
      P₂ small₂ rational₂ (fun i => basisPolynomialLift (Pi.basisFun ℝ κ) S₂ (k₁ i)) := by
    rw [← hextraEq]
    exact hsystem₂
  have hbracketsFinal : ∀ r < (j + 1) - 1, ∀ i α,
      ⁅basisGradeProjection (b.baseChange ℝ) w r (coefficients P₂.coord α),
        (1 : ℝ) ⊗ₜ[ℚ] (eK i : L)⁆ ∈ V.baseChange ℝ := by
    intro r hr i α
    have hrj : r < j := by omega
    have heq := congrArg (fun Q : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L) => coefficients Q α) (hbelow₂ r hrj)
    simp only [coefficients_map, LinearMap.restrictScalars_apply] at heq
    rw [heq]
    exact hbrackets₁ r hrj i α
  let Y : F.FormalInductionState b w U V K eK T (j + 1) ((p + C) ^ C) := {
    P := P₂
    S := S₂
    R := R₂
    small := small₂
    rational := rational₂
    k := k₁
    denominator := n
    denominator_pos := hn
    denominator_bound := hnBound
    constant_zero := hconstant₂.trans (hconstant₁.trans X.constant_zero)
    mem_U := hU₂
    graded := hgraded₂
    horizontal := hK₂
    lower_log := hlower₂
    lower_bracket := hbracketsFinal
    lift_system := hlifts₂
    derivative_system := hsystemFinal
    S_shift := fun r => (hliftControls₂ r).2.2.1
    R_shift := fun r => (hliftControls₂ r).2.2.2
    small_shift := fun i => (hshift₂ i).1
    rational_shift := fun i => (hshift₂ i).2
    S_remainder := fun r α => (hliftRemainders₂ r α).1
    R_remainder := fun r α => (hliftRemainders₂ r α).2
    small_remainder := fun i α => (hremainders₂ i α).1
    rational_remainder := fun i α => (hremainders₂ i α).2
    S_bound := fun r => (hliftControls₂ r).1.mono _ T hTpos hEz
    R_grid := fun r α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n ((hliftControls₂ r).2.1 α)
    small_bound := fun i => (hderivControls₂ i).1.mono _ T hTpos
      (div_le_div_of_nonneg_right hEz (hTpos i).le)
    rational_grid := fun i α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n ((hderivControls₂ i).2 α) }
  refine ⟨Y, A₁, A₂, B₁, B₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (A₁ * A₂) * P₂ * (B₂ * B₁) = X.P
    calc
      _ = A₁ * (A₂ * P₂ * B₂) * B₁ := by group
      _ = A₁ * P₁ * B₁ := by rw [hprod₂]
      _ = X.P := hprod₁
  · intro α
    exact ⟨hBrU (hAB₁ α).1, hCurU (hAB₂ α).1, hBrU (hAB₁ α).2, hCurU (hAB₂ α).2⟩
  · exact ⟨homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        (j - 1) A₁.coord hAhom₁ (fun α => hBrGrade _ (hAB₁ α).1),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        j A₂.coord hAhom₂ (fun α => hCurGrade _ (hAB₂ α).1),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        (j - 1) B₁.coord hBhom₁ (fun α => hBrGrade _ (hAB₁ α).2),
      homogeneous_mem_gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1)
        j B₂.coord hBhom₂ (fun α => hCurGrade _ (hAB₂ α).2)⟩
  · have hzero₁ : Finsupp.weight (fun _ : σ => (1 : ℕ)) (0 : σ →₀ ℕ) ≠ j - 1 := by simp only [map_zero]; omega
    have hzero₂ : Finsupp.weight (fun _ : σ => (1 : ℕ)) (0 : σ →₀ ℕ) ≠ j := by simp only [map_zero]; omega
    exact ⟨hAhom₁ 0 hzero₁, hAhom₂ 0 hzero₂, hBhom₁ 0 hzero₁, hBhom₂ 0 hzero₂⟩
  · exact hA₁bound.mono _ T hTpos (Real.exp_le_exp.mpr hdCap)
  · have hA₂bound : CoefficientBound (b.baseChange ℝ) T (Real.exp z) A₂.coord :=
      (coefficientBound_iff_norm _ T hTpos (Real.exp_nonneg _) _).mpr hAnorm₂
    exact hA₂bound.mono _ T hTpos hEz
  · exact fun α => realDenominatorGrid_subset_of_dvd hn₀ hn₀n (hBgrid₁ α)
  · exact fun α => realDenominatorGrid_subset_of_dvd hn₂ hn₂n (hBgrid₂ α)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.UniformFormalInductionIteration
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_induction_iteration (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp (formalIterationBudget C p (s - 1)) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    Nonempty (F.FormalInductionRun b w U V K eK T X.P (s - 1)
      (formalIterationBudget C p (s - 1))) := by
  classical
  obtain ⟨C, hC, hstage⟩ := exists_formal_induction_stage s
  refine ⟨C, hC, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hrun : ∀ r, r ≤ s - 1 →
      Nonempty (F.FormalInductionRun b w U V K eK T X.P r (formalIterationBudget C p r)) := by
    intro r
    induction r with
    | zero =>
      intro _
      exact ⟨FormalInductionRun.start X⟩
    | succ r ih =>
      intro hr
      obtain ⟨W⟩ := ih (by omega)
      have hj : 2 ≤ 2 + r := by omega
      have hjs : 2 + r ≤ s := by omega
      let g := G (2 + r) hj hjs
      have hpq : p ≤ formalIterationBudget C p r := formalIterationBudget_ge hC hp r
      have hq : 0 ≤ formalIterationBudget C p r := formalIterationBudget_nonneg C hp r
      have hnext : formalIterationBudget C p r ≤ formalIterationBudget C p (r + 1) :=
        formalIterationBudget_monotone hC hp (Nat.le_succ r)
      have hcutoff : ∀ i, Real.exp ((formalIterationBudget C p r + C) ^ C) ≤ T i := by
        intro i
        exact (Real.exp_le_exp.mpr (formalIterationBudget_monotone hC hp hr)).trans (hT i)
      have hν : (Fintype.card (Fin g.bracketRank) : ℝ) ≤ formalIterationBudget C p r := by
        simpa only [Fintype.card_fin] using (hRanks (2 + r) hj hjs).1.trans hpq
      have hτ : (Fintype.card (Fin g.currentRank) : ℝ) ≤ formalIterationBudget C p r := by
        simpa only [Fintype.card_fin] using (hRanks (2 + r) hj hjs).2.trans hpq
      have hjp : ((2 + r : ℕ) : ℝ) ≤ formalIterationBudget C p r :=
        (Nat.cast_le.mpr hjs).trans (hsp.trans hpq)
      obtain ⟨Y, A₁, A₂, B₁, B₂, hfactor, hmem, hdeg, hzero,
        hA₁bound, hA₂bound, hB₁grid, hB₂grid⟩ :=
        hstage F b w hF hgraded hs U V K g.bracketSpace g.currentSpace hUV hV
          eK g.bracketBasis g.currentBasis f hK hj hH
          g.bracket_grade g.bracket_U g.bracket_K g.bracket_V
          g.current_grade g.current_U g.current_projection
          g.bracket_matrix_height g.current_matrix_height hKernelBasis
          g.bracket_basis_height g.current_basis_height hQuotient hStructure hq
          (hμ.trans hpq) (hι.trans hpq) (hκ.trans hpq) hν hτ (hσ.trans hpq) hjp
          (hHp.trans (Real.exp_le_exp.mpr hpq)) T hcutoff W.state
          (W.state.bracket_source g hU hj)
      exact ⟨W.extend hnext hTpos Y A₁ A₂ B₁ B₂ hfactor
        ⟨fun α => (hmem α).1, hdeg.1, hzero.1⟩
        ⟨fun α => (hmem α).2.1, hdeg.2.1, hzero.2.1⟩
        ⟨fun α => (hmem α).2.2.1, hdeg.2.2.1, hzero.2.2.1⟩
        ⟨fun α => (hmem α).2.2.2, hdeg.2.2.2, hzero.2.2.2⟩
        hA₁bound hA₂bound hB₁grid hB₂grid⟩
  exact hrun (s - 1) le_rfl

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_induction_iteration (s : ℕ) :
    ∃ D : ℕ, 2 ≤ D ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + D) ^ D) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    ∃ q : ℝ, p ≤ q ∧ 0 ≤ q ∧ q ≤ (p + D) ^ D ∧
      ∃ W : F.FormalInductionRun b w U V K eK T X.P (s - 1) q,
        (W.denominator : ℝ) ≤ Real.exp ((p + D) ^ D) := by
  obtain ⟨C, hC, hiteration⟩ := exists_formal_induction_iteration s
  obtain ⟨D, hD, hbudget⟩ := exists_formal_iteration_uniform_budget C (s - 1)
  refine ⟨D, hD, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  let q := formalIterationBudget C p (s - 1)
  have hpq : p ≤ q := formalIterationBudget_ge hC hp (s - 1)
  have hq : 0 ≤ q := formalIterationBudget_nonneg C hp (s - 1)
  have htotal : ((s - 1 : ℕ) + 1 : ℝ) * q ≤ (p + D) ^ D := hbudget p hp
  have hqcap : q ≤ (p + D) ^ D := by
    have hmul := mul_nonneg (Nat.cast_nonneg (s - 1) : (0 : ℝ) ≤ (s - 1 : ℕ)) hq
    nlinarith
  have hT' : ∀ i, Real.exp (formalIterationBudget C p (s - 1)) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr hqcap).trans (hT i)
  obtain ⟨W⟩ := hiteration F b w hF hgraded hs U V K hUV hU hV eK f hK hH G
    hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T hT' X
  exact ⟨q, hpq, hq, hqcap, W, W.denominator_bound.trans (Real.exp_le_exp.mpr htotal)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.NativeWeightPairRemoval
namespace OAI

section

namespace Erdos3

open scoped BigOperators

namespace NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem translation_negative (h δ : ℤ) {X : Type*} (S : Finset X) (n : X → ℤ)
    (k : Fin V.outputDim) (f : X → ℂ) (q : ℝ)
    (hcorr : Real.exp (-q) ≤ ‖𝔼 u ∈ S, f u * star
      (V.eval k (fun j => correlationInput h (n u + δ) j.1))‖) :
    ∃ (a : MixedExpansionIndex V) (b : Fin (D.translation.selectedExpansion k a).count)
      (c : Fin (D.lower h δ a).count), Real.exp (-(q + 3 * P)) ≤
        ‖𝔼 u ∈ S, f u * star (D.correction h δ k a b c (n u))‖ :=
  V.mixed_translation_reduction_transfer D.translation h δ (D.lower h δ) S n k f q hcorr

end NativeMixedReductionData

end Erdos3

end

section

namespace Erdos3.NativeMixedReductionData

variable {s : ℕ} {p P : ℝ}
  {V : NativeMultidegreeNilcharacter (fun _ : ReplicatedIndex (mixedCorrelationDegree s) => 1) p}
  (D : NativeMixedReductionData V P)

theorem correction_factorization (k : Fin 4 → Fin V.outputDim) (t : D.TranslationCode k)
    (h₁ h₂ h₃ h₄ δ n : ℤ) (c : D.LowerCode t h₂ h₄ δ) (z : ℂ)
    (hrel : -h₁ + h₂ + h₃ - h₄ = 0) :
    z * star (V.eval (k 0) (fun j => correlationInput h₁ n j.1)) *
        V.eval (k 2) (fun j => correlationInput h₃ n j.1) *
        star (D.correction h₄ δ (k 3) t.fourth t.fourthTerm c.fourth n) *
        D.correction h₂ δ (k 1) t.second t.secondTerm c.second n =
      z * D.translationGlobal k t ![h₁, h₂, h₃, n, δ] *
        D.translationLower t h₂ h₄ δ c n *
        untranslatedMixedProduct V (D.translationCoordinates k t) h₁ h₂ h₃ h₄ n := by
  rw [D.translationGlobal_sample k t h₁ h₂ h₃ h₄ n δ hrel]
  have hzero : D.translationCoordinates k t 0 = k 0 := rfl
  have hone : D.translationCoordinates k t 1 =
      firstTranslationCoordinate (mixedTranslationCoordinates s) t.second := rfl
  have htwo : D.translationCoordinates k t 2 = k 2 := rfl
  have hthree : D.translationCoordinates k t 3 =
      firstTranslationCoordinate (mixedTranslationCoordinates s) t.fourth := rfl
  simp only [correction, translationLower, untranslatedMixedProduct,
    hzero, hone, htwo, hthree, star_mul]
  ring

end Erdos3.NativeMixedReductionData

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FastGradedRelativeInvariance
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem fullFastGradedRelative_lie_mem {u v : F.AssociatedGraded}
    (hu : u ∈ F.fullFastGradedDiagonal W) (hv : v ∈ F.fullFastGradedRelative e ω hF W) :
    ⁅u, v⁆ ∈ F.fullFastGradedRelative e ω hF W := by
  obtain ⟨z, hz, rfl⟩ := hv
  have hz0 : z ∈ (F.reducedSquareSndSymbolMap (fun _ : Unit => 1)).ker.toSubmodule := hz.2
  obtain ⟨p, hp⟩ := (F.reducedRelativeSquareSymbolMap_range
    (fun _ : Unit => 1) (fun _ => Nat.zero_lt_one)).ge hz0
  obtain ⟨a, ha⟩ := F.polynomialSymbolMap_surjective (fun _ : Unit => 1) u
  have hua : F.adaptedReducedSymbolMap (fun _ : Unit => 1) a ∈
      F.reducedSquareFastDiagonalSubalgebra (fun _ : Unit => 1) W := by
    change F.quotientTopSymbolMap (fun _ : Unit => 1)
      (F.polynomialSymbolMap (fun _ : Unit => 1) a) ∈ _
    rw [ha]
    exact hu
  have hz' : z ∈ F.reducedSquareFastRelativeSubmodule (fun _ : Unit => 1) W := hz
  have hbr := F.reducedSquareFastRelative_action_mem (fun _ : Unit => 1) W
    (fun _ => Nat.zero_lt_one) hua hz'
  refine ⟨⁅F.reducedSquareDiagonalSymbolMap (fun _ : Unit => 1)
    (F.adaptedReducedSymbolMap (fun _ : Unit => 1) a), z⁆, hbr, ?_⟩
  rw [← hp, F.reducedSquareGradedDifference_relative_lie, ha]

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.TerminalControlledFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_uniform_formal_induction_factorization (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧
    ∀ {L μ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℝ (ℝ ⊗[ℚ] L)) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ)
    (_hU : BasisGradedSubmodule (b.baseChange ℝ) w U.toSubmodule)
    (_hV : BasisGradedSubmodule (b.baseChange ℝ) w (V.baseChange ℝ))
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s → FormalStageGeometry b w U V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + E) ^ E) ≤ T i)
    (X : F.FormalInductionState b w U V K eK T 2 p),
    ∃ q : ℝ, p ≤ q ∧ 0 ≤ q ∧ q ≤ (p + E) ^ E ∧
      ∃ W : F.FormalInductionRun b w U V K eK T X.P (s - 1) q,
        (W.denominator : ℝ) ≤ Real.exp ((p + E) ^ E) ∧
        ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + E) ^ E) ∧ W.denominator ∣ m ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + E) ^ E)) W.left.prod.coord ∧
          CoefficientGrid (b.baseChange ℝ) m W.right.prod.coord ∧
          F.FormalCorrectionProperty b w U W.left.prod ∧
          F.FormalCorrectionProperty b w U W.right.prod := by
  obtain ⟨D, _, hiteration⟩ := exists_uniform_formal_induction_iteration s
  obtain ⟨C, _, hproducts⟩ := exists_formal_induction_run_product_controls s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C D) ^ D
  obtain ⟨E, hE, hbudget⟩ := exists_natPolynomial_eval_budget (Q + (Q + Polynomial.C C) ^ C)
  refine ⟨E, hE, ?_⟩
  intro L μ ι κ σ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV eK f hK H hH G
    hKernelBasis hQuotient hStructure p hp hμ hι hκ hσ hRanks hsp hHp T hT X
  let t := (p + D) ^ D
  let z := (t + C) ^ C
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have htotal : t + z ≤ (p + E) ^ E := by
    simpa [Q, t, z, Polynomial.eval₂_pow] using hbudget p hp
  have htcap : t ≤ (p + E) ^ E := by linarith
  have hzcap : z ≤ (p + E) ^ E := by linarith
  have hT' : ∀ i, Real.exp ((p + D) ^ D) ≤ T i :=
    fun i => (Real.exp_le_exp.mpr htcap).trans (hT i)
  obtain ⟨q, hpq, hq, hqt, W, hWden⟩ :=
    hiteration F b w hF hgraded hs U V K hUV hU hV eK f hK hH G
      hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T hT' X
  have hpt : p ≤ t := hpq.trans hqt
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  obtain ⟨m, hm, hmp, hdm, hleft, hright, hleftGood, hrightGood⟩ :=
    hproducts F b w hF hgraded hTpos (Nat.sub_le s 1) W hH hStructure ht hqt
      (hμ.trans hpt) (hσ.trans hpt) (hHp.trans (Real.exp_le_exp.mpr hpt)) hWden
  exact ⟨q, hpq, hq, hqt.trans htcap, W,
    hWden.trans (Real.exp_le_exp.mpr htcap), m, hm,
    hmp.trans (Real.exp_le_exp.mpr hzcap), hdm,
    hleft.mono _ T hTpos (Real.exp_le_exp.mpr hzcap), hright, hleftGood, hrightGood⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_formal_stepDrop_subalgebra_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (_hU : BasisGradedSubmodule b w U.toSubmodule) (_hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (G : ∀ j, 2 ≤ j → j ≤ s →
      FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hQuotientU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (_hQuotientK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hRanks : ∀ j hj hjs, ((G j hj hjs).bracketRank : ℝ) ≤ p ∧
      ((G j hj hjs).currentRank : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w (realificationLieSubalgebra U) V K eK T 2 p),
    ∃ Z : LieSubalgebra ℚ L, BasisGradedSubmodule b w Z.toSubmodule ∧
      (∀ x ∈ Z, η (basisGradeProjection b w s x) = 0) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
        (∀ i j, ((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ A P B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A * P * B = X.P ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) A ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) B ∧
          coefficients P.coord 0 = 0 ∧
          P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
          (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A.coord ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            CoefficientGrid (b.baseChange ℝ) m B.coord := by
  obtain ⟨E, hE, hfactor⟩ := exists_uniform_formal_induction_factorization s
  obtain ⟨D, hD, hbasis⟩ := exists_stepDrop_basis_uniform_budget
  let C := max E D
  refine ⟨C, hE.trans (Nat.le_max_left E D), ?_⟩
  intro L μ υ χ ι κ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV η hη eK f
    fU fK hK H hH G hKernelBasis hQuotient hQuotientU hQuotientK hStructure
    p hp hμ hυ hχ hι hκ hσ hRanks hsp hHp T hT X
  have hEC : (p + E) ^ E ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_left E D)
  have hDC : (p + D) ^ D ≤ (p + C) ^ C :=
    shifted_power_self_mono hp (by omega) (Nat.le_max_right E D)
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hRU : BasisGradedSubmodule (b.baseChange ℝ) w (realificationLieSubalgebra U).toSubmodule :=
    hU.baseChange b w U.toSubmodule
  have hRV := hV.baseChange b w V
  have hRUV : ∀ u ∈ realificationLieSubalgebra U, ∀ v ∈ V.baseChange ℝ, ⁅u, v⁆ ∈ V.baseChange ℝ :=
    fun _ hu _ hv => lie_mem_real_baseChange U.toSubmodule V V hUV hu hv
  obtain ⟨q, _, _, _, W, _, m, hm, hmbound, _, hleft, hright, hleftGood, hrightGood⟩ :=
    hfactor F b w hF hgraded hs (realificationLieSubalgebra U) V K hRUV hRU hRV eK f hK hH G
      hKernelBasis hQuotient hStructure hp hμ hι hκ hσ hRanks hsp hHp T
      (fun i => (Real.exp_le_exp.mpr hEC).trans (hT i)) X
  obtain ⟨e, he⟩ := hbasis b w U V K fU fK f eK hH hQuotientU hQuotientK hQuotient
    hKernelBasis hStructure hp hμ hυ hχ hκ hι hHp
  let Z := stepDropSubalgebra b w (F.adaptedBasis_weight_pos b w hF) hgraded U V K hU hUV
  have hcoeff : ∀ α, coefficients W.state.P.coord α ∈ realificationLieSubalgebra Z := by
    intro α
    exact W.terminal_coefficients_mem_rational_stepDrop hs hF α
  refine ⟨Z, stepDropSubmodule_graded b w U V K hU hV,
    (fun _ hx => stepDropSubmodule_top_frequency b w U V K hU hV η hs hη hx), e, ?_,
    W.left.prod, W.state.P, W.right.prod, W.factorization, hleftGood, hrightGood,
    W.state.constant_zero, W.state.graded, hcoeff,
    hleft.mono _ T hTpos (Real.exp_le_exp.mpr hEC), m, hm,
    hmbound.trans (Real.exp_le_exp.mpr hEC), hright⟩
  intro i j
  exact ⟨(he i j).1.trans (Real.exp_le_exp.mpr hDC), (he i j).2.trans (Real.exp_le_exp.mpr hDC)⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_stepDrop_from_formal_state (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {L μ υ χ ι κ σ : Type*} [LieRing L] [LieAlgebra ℚ L]
    [Fintype μ] [Fintype υ] [Fintype χ] [Fintype ι] [Fintype κ] [Fintype σ]
    (F : NilpotentLieFiltration L s) (b : Basis μ ℚ L) (w : μ → ℕ)
    (_hF : ∀ d, F.layer d = Submodule.span ℚ (b '' {i | d ≤ w i}))
    (_hgraded : BasisHomogeneousBrackets b w) (_hs : 2 ≤ s)
    (U : LieSubalgebra ℚ L) (V K : Submodule ℚ L)
    (_hUV : ∀ u ∈ U, ∀ v ∈ V, ⁅u, v⁆ ∈ V)
    (_hU : BasisGradedSubmodule b w U.toSubmodule) (_hV : BasisGradedSubmodule b w V)
    (η : L →ₗ[ℚ] ℚ) (_hη : ∀ x ∈ V, basisGradeProjection b w s x = x → η x = 0)
    (eK : Basis κ ℚ K) (f : Basis ι ℚ (L ⧸ V))
    (fU : Basis υ ℚ (L ⧸ U.toSubmodule)) (fK : Basis χ ℚ (L ⧸ K))
    (_hK : ∀ x ∈ K.baseChange ℝ, basisGradeProjection (b.baseChange ℝ) w 1 x = x)
    {H : ℕ} (_hH : 1 ≤ H)
    (_hKernelBasis : ∀ i z, RationalHeightLE (b.repr (eK z : L) i) H)
    (_hQuotient : ∀ i z, RationalHeightLE (f.repr (V.mkQ (b z)) i) H)
    (_hQuotientU : ∀ i z, RationalHeightLE (fU.repr (U.toSubmodule.mkQ (b z)) i) H)
    (_hQuotientK : ∀ i z, RationalHeightLE (fK.repr (K.mkQ (b z)) i) H)
    (_hStructure : ∀ i z r, RationalHeightLE (b.repr ⁅b i, b z⁆ r) H)
    {p : ℝ} (_hp : 0 ≤ p)
    (_hμ : (Fintype.card μ : ℝ) ≤ p) (_hυ : (Fintype.card υ : ℝ) ≤ p)
    (_hχ : (Fintype.card χ : ℝ) ≤ p) (_hι : (Fintype.card ι : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hsp : (s : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
    (X : F.FormalInductionState b w (realificationLieSubalgebra U) V K eK T 2 p),
    ∃ Z : LieSubalgebra ℚ L, BasisGradedSubmodule b w Z.toSubmodule ∧
      (∀ x ∈ Z, η (basisGradeProjection b w s x) = 0) ∧
      ∃ e : Basis (Fin (Module.finrank ℚ Z)) ℚ Z,
        (∀ i j, ((b.repr (e i : L) j).num.natAbs : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ((b.repr (e i : L) j).den : ℝ) ≤ Real.exp ((p + C) ^ C)) ∧
        ∃ A P B : PolynomialGroup σ F.realification.lowerCentralSeries_eq_bot,
          A * P * B = X.P ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) A ∧
          F.FormalCorrectionProperty b w (realificationLieSubalgebra U) B ∧
          coefficients P.coord 0 = 0 ∧
          P.coord ∈ gradedPolynomialSubmodule (b.baseChange ℝ) w (fun _ : σ => 1) ∧
          (∀ α, coefficients P.coord α ∈ realificationLieSubalgebra Z) ∧
          CoefficientBound (b.baseChange ℝ) T (Real.exp ((p + C) ^ C)) A.coord ∧
          ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
            CoefficientGrid (b.baseChange ℝ) m B.coord := by
  classical
  obtain ⟨E, _, hfinal⟩ := exists_formal_stepDrop_subalgebra_factorization s
  obtain ⟨D, hD, hgeometryBudget⟩ := exists_formal_geometry_uniform_budget
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (((Polynomial.X + Polynomial.C D) ^ D + Polynomial.C E) ^ E)
  refine ⟨C, hC, ?_⟩
  intro L μ υ χ ι κ σ _ _ _ _ _ _ _ _ F b w hF hgraded hs U V K hUV hU hV η hη eK f
    fU fK hK H hH hKernelBasis hQuotient hQuotientU hQuotientK hStructure
    p hp hμ hυ hχ hι hκ hσ hsp hHp T hT X
  let u := (p + D) ^ D
  let r := 2 * Fintype.card υ + Fintype.card χ + Fintype.card ι + Fintype.card μ
  let J := formalGeometryHeight (Fintype.card μ) r H
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpu : p ≤ u := by
    calc
      p ≤ p + D := le_add_of_nonneg_right (Nat.cast_nonneg D)
      _ ≤ (p + D) ^ D := by
        have hDr : (2 : ℝ) ≤ D := Nat.cast_le.mpr hD
        simpa only [pow_one] using pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ p + D)
          (show 1 ≤ D by omega)
  have hr : (r : ℝ) ≤ 5 * p := by
    dsimp [r]
    push_cast
    linarith
  have hHJ : H ≤ J := formalGeometryHeight_ge_input _ _ _
  have hJ : 1 ≤ J := hH.trans hHJ
  have hJu : (J : ℝ) ≤ Real.exp u := hgeometryBudget _ _ _ p hp hμ hr hHp
  have hcap : (u + E) ^ E ≤ (p + C) ^ C := by
    simpa [u, Polynomial.eval₂_pow] using hbudget p hp
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hgeometry (j : ℕ) (hj : 2 ≤ j) :
      ∃ G : FormalStageGeometry b w (realificationLieSubalgebra U) V K eK f j J,
        G.bracketRank ≤ Fintype.card μ ∧ G.currentRank ≤ Fintype.card μ := by
    apply exists_rational_formal_stage_geometry b w U V K hU fU fK f eK hH
    · dsimp [r]; omega
    · dsimp [r]; omega
    · dsimp [r]; omega
    · exact hQuotientU
    · exact hQuotientK
    · exact hQuotient
    · exact hKernelBasis
    · exact hStructure
    · exact hj
  choose G hG using hgeometry
  obtain ⟨Z, hZ, hZη, e, he, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound, m, hm, hmbound, hgrid⟩ :=
    hfinal F b w hF hgraded hs U V K hUV hU hV η hη eK f fU fK hK hJ
      (fun j hj _ => G j hj)
      (fun i z => (hKernelBasis i z).mono hHJ)
      (fun i z => (hQuotient i z).mono hHJ)
      (fun i z => (hQuotientU i z).mono hHJ)
      (fun i z => (hQuotientK i z).mono hHJ)
      (fun i z k => (hStructure i z k).mono hHJ)
      hu (hμ.trans hpu) (hυ.trans hpu) (hχ.trans hpu) (hι.trans hpu) (hκ.trans hpu) (hσ.trans hpu)
      (fun j hj _ => ⟨(Nat.cast_le.mpr (hG j hj).1).trans (hμ.trans hpu),
        (Nat.cast_le.mpr (hG j hj).2).trans (hμ.trans hpu)⟩)
      (hsp.trans hpu) hJu T (fun i => (Real.exp_le_exp.mpr hcap).trans (hT i))
      (X.enlarge hpu hTpos)
  refine ⟨Z, hZ, hZη, e, ?_, A, P, B, hfactor, hA, hB, hzero, hdegree, hcoeff,
    hbound.mono _ T hTpos (Real.exp_le_exp.mpr hcap), m, hm,
    hmbound.trans (Real.exp_le_exp.mpr hcap), hgrid⟩
  intro i j
  exact ⟨(he i j).1.trans (Real.exp_le_exp.mpr hcap), (he i j).2.trans (Real.exp_le_exp.mpr hcap)⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UnnormalizedCommonSymbolFactorization
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial NilpotentLieBCHGroup

universe uσ uι uL

variable {σ : Type uσ} {ι : Type uι} {L : Type uL}
  [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

theorem exists_terminalComposition_bound (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ {σ : Type uσ} {ι : Type uι} {L : Type uL}
        [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
        (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
        (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
        (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded),
        F.TerminalCompositionSpec (σ := σ) e ω hF W C := by
  have hs := exists_formal_polynomial_product_bound.{uσ, uι, uL} (s + 1) 1 2
  obtain ⟨a, _, hslow⟩ := hs
  have hr := exists_formal_polynomial_product_grid.{uσ, uι, uL} (s + 1) 2
  obtain ⟨b, _, hgrid⟩ := hr
  obtain ⟨C, hC, hbudget⟩ := exists_terminalComposition_budget a b
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF W H p hH hp hι hσ hHp hstructure hW η T hT g₀ hn
  obtain ⟨l, hl, hlp, x, g, z, hnative, hx, hz, hterminal⟩ := hn
  obtain ⟨Z, hZ, hZη, bZ, hbZ, A, P, B, hformal, hA, hB, hzero, hdegree, hcoeff,
    hAbound, m, hm, hmp, hBgrid⟩ := hterminal
  let φ := F.realAdaptedGradedPolynomialHom e ω hF (fun _ : σ => 1)
  let bG := F.associatedGradedBasis e ω hF
  let FG := F.associatedGradedFiltration
  have hgraded := F.associatedGradedBasis_homogeneous_brackets e ω hF
  have hlayers := F.associatedGradedFiltration_layer e ω hF
  have hstructureG (i j k : ι) : RationalHeightLE (bG.repr ⁅bG i, bG j⁆ k) H := by
    rw [F.associatedGradedBasis_bracket e ω hF]
    split_ifs
    · exact hstructure i j k
    · exact rationalHeightLE_zero hH
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2 : p ≤ 2 * p := by linarith
  have hι2 := hι.trans hp2
  have hσ2 := hσ.trans hp2
  have hH2 := hHp.trans (Real.exp_le_exp.mpr hp2)
  have hxb := F.realAdaptedGradedPolynomialHom_bound e ω hF (fun _ : σ => 1) T hT
    (Real.exp_nonneg p) x.val hx
  have hzg := F.realAdaptedGradedPolynomialHom_grid e ω hF (fun _ : σ => 1) l z.val hz
  have hxc := F.realAdaptedGradedPolynomialHom_correction e ω hF W hW x
  have hzc := F.realAdaptedGradedPolynomialHom_correction e ω hF W hW z
  have hinput : Real.exp p ≤ Real.exp ((2 * p + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  have hleft := hslow FG bG ω hlayers H (2 * p) hH h2p hι2 hσ2 hH2 hstructureG T hT
    [φ x.val, A] (by simp) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hxc.2.1
      · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hA.2.1) (by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact hxb.mono _ T hT hinput
      · exact hAbound.mono _ T hT hinput)
  have hleftBound : CoefficientBound (bG.baseChange ℝ) T (Real.exp ((2 * p + a) ^ a))
      (φ x.val * A).coord := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft
  have hdenom : ((l * m : ℕ) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add]; congr 1; ring
  have hcommonB : CoefficientGrid (bG.baseChange ℝ) (l * m) B.coord :=
    fun α => realDenominatorGrid_subset_of_dvd hm (dvd_mul_left m l) (hBgrid α)
  have hcommonz : CoefficientGrid (bG.baseChange ℝ) (l * m) (φ z.val).coord :=
    fun α => realDenominatorGrid_subset_of_dvd hl (dvd_mul_right l m) (hzg α)
  have hg := hgrid FG bG ω hlayers H (2 * p) hH h2p hι2 hσ2 hH2 hstructureG
    (l * m) (Nat.mul_pos hl hm) hdenom
  obtain ⟨n, hn, hnp, _, hproducts⟩ := hg
  have hright := hproducts [B, φ z.val] (by simp) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hB.2.1
    · exact FG.gradedPolynomial_mem_adapted bG ω hlayers (fun _ => 1) _ hzc.2.1) (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact hcommonB
    · exact hcommonz)
  have hrightGrid : CoefficientGrid (bG.baseChange ℝ) n (B * φ z.val).coord := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hright
  have hnative' : φ x.val * φ g.val * φ z.val = φ g₀.val := by
    calc
      _ = φ (x.val * g.val * z.val) := by simp only [map_mul]
      _ = φ g₀.val := congrArg φ (congrArg Subtype.val hnative)
  have hfactor : (φ x.val * A) * P * (B * φ z.val) = φ g₀.val := by
    calc
      _ = φ x.val * (A * P * B) * φ z.val := by group
      _ = φ x.val * φ g.val * φ z.val := congrArg (fun t => φ x.val * t * φ z.val) hformal
      _ = _ := hnative'
  have hb := hbudget p hp
  have hep := Real.exp_le_exp.mpr hb.1
  exact ⟨Z, hZ, hZη, bZ, fun i j => ⟨(hbZ i j).1.trans hep, (hbZ i j).2.trans hep⟩,
    φ x.val * A, P, B * φ z.val, hfactor, hxc.mul hgraded hA, hB.mul hgraded hzc,
    hzero, hdegree, hcoeff, hleftBound.mono _ T hT (Real.exp_le_exp.mpr hb.2.1),
    n, hn, hnp.trans (Real.exp_le_exp.mpr hb.2.2), hrightGrid⟩

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CommonFreeSunflower
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

variable {Q : ℝ} (B : D.CoefficientBases Q)

theorem CoefficientBases.freeEvaluation_generator (x : D.CoefficientAlphabet) :
    B.freeEvaluation D (D.coefficientFreeGenerator x) = B.generator D x :=
  FreeDegreeRankLieAlgebra.lift_of _ _ _ _ _ x

end Erdos3.NativeRankRelation.CommonData

end

end OAI
end


