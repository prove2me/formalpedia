-- Prove2me | Definitions.Def_OAIE3v2B107
-- name    : OAIE3v2B107
-- status  : Definition
-- author  : @dbenbenn
-- created : 2026-10-17T10:39:24.070976+00:00
-- url     : https://prove2.me/theorems/4d75a2e4-0cf8-4cfc-98f6-8086bbc09b19
-- title:
--   OpenAI Erdős-3 split, version 2: definitions bundle 109 of 311
-- statement:
--   Definitions bundle 109 of 311 of version 2 of the Erdős Problem 3 split of OpenAI's proof: OpenAI's Lean definitions, structures and instances from the modules listed below of `lean/OAI/Combinatorics/Progressions` (OpenAI, *Quasipolynomial Bounds for Arithmetic Progressions*, September 23, 2026, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a, together with the lemmas those definitions use in their bodies (several of OpenAI's definitions choose witnesses of existence theorems, or build structures that carry proofs, so the bundle has to contain those proofs), OpenAI's `@[simp]` lemmas that later definitions rely on, and OpenAI's scoped notations.
--
--   It imports the definitions bundles `OAIE3v2B087`, `OAIE3v2B088`, `OAIE3v2B089`, `OAIE3v2B090`, `OAIE3v2B092`, `OAIE3v2B298`, `OAIE3v2B095` of this split.
--
--   Modules: `Estimates/CocycleHorizontalNormalization.lean`, `Estimates/ControlledLinearSubspaceLift.lean`, `Estimates/DerivativeIndexBounds.lean`, `Estimates/EuclideanGraphResidual.lean`, `Estimates/LowerStepSquare.lean`, `Estimates/PetalComparisonTree.lean`, `Estimates/QuotientInducedMark.lean`, `Estimates/RealSymbolRepresentativeSplitting.lean`, `Estimates/SquareGradedRelative.lean`, `Estimates/SymbolAbsorptionBounds.lean`, `Geometry/ControlledSumCoordinates.lean`, `Lattices/ScaledLatticeCovolume.lean`, `Linear/BasisGradedCoordinateBasis.lean`, `Linear/CanonicalRankCompatibility.lean`, `Linear/DerivativeVerticalBasis.lean`, `Linear/DualAdjointFiltration.lean`, `Linear/DualIdealSteps.lean`, `Linear/GradeProjectionRemainder.lean`, `Linear/RealDualRationalBounds.lean`, `Nilpotent/BCHLatticeImageGap.lean`, `Nilpotent/BCHSubmoduleRemainder.lean`, `Nilpotent/DualBCHDifferential.lean`, `Nilpotent/RankBracketFactorizationMonotone.lean`, `Nilpotent/RealPolynomialBCH.lean`, `Nilpotent/RealizedDualBCH.lean`, `Polynomial/RankPolynomialFactorization.lean`, `Polynomial/RealGradedSymbolPolynomial.lean`, `Polynomial/ShiftedPolynomialBasis.lean`, `Polynomial/ShiftedPolynomialIdeals.lean`.
--
--   The theorems of the development that the definitions do not need are published separately as statements of this split, each proved by its own submission.
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); definitions carved from lean/OAI/Combinatorics/Progressions

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B087
import Definitions.Def_OAIE3v2B088
import Definitions.Def_OAIE3v2B089
import Definitions.Def_OAIE3v2B090
import Definitions.Def_OAIE3v2B092
import Definitions.Def_OAIE3v2B298
import Definitions.Def_OAIE3v2B095

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHLatticeImageGap
namespace OAI

section

namespace Erdos3

open scoped NNReal

noncomputable def bchInverseBoxConstant (s d H : ℕ) (B : ℝ≥0) : ℝ≥0 :=
  (⟨bchBoxCoordinateBound s d H B, bchBoxCoordinateBound_nonneg _ _ _ B.coe_nonneg⟩ + 2 * B) *
    bchLogMetricConstant s d H 1

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.DualBCHDifferential
namespace OAI


namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualLogDerivative_spec (z : DualGroup hnil) :
    z * (dualConstantHom (dualBaseHom z))⁻¹ = dualTangentElement (dualLogDerivative z) := by
  apply (dualBaseHom_eq_one_iff _).mp
  simp only [map_mul, map_inv, dualBaseHom_constant, mul_inv_cancel]

theorem dualLogDerivative_factorization (z : DualGroup hnil) :
    z = dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z) := by
  calc
    _ = (z * (dualConstantHom (dualBaseHom z))⁻¹) * dualConstantHom (dualBaseHom z) := by group
    _ = _ := by rw [dualLogDerivative_spec]

theorem dualLogDerivative_tangent_mul_constant (x : L) (g : NilpotentLieBCHGroup L s hnil) :
    dualLogDerivative (dualTangentElement x * dualConstantHom g) = x := by
  simp only [dualLogDerivative, map_mul, dualBaseHom_tangent, dualBaseHom_constant, one_mul,
    mul_inv_cancel_right]
  exact dualTangentLinear_infinitesimal x

theorem dualLogDerivative_mul (z w : DualGroup hnil) :
    dualLogDerivative (z * w) = dualLogDerivative z + dualAdjoint (dualBaseHom z) (dualLogDerivative w) := by
  have h : z * w =
      dualTangentElement (dualLogDerivative z + dualAdjoint (dualBaseHom z) (dualLogDerivative w)) *
        dualConstantHom (dualBaseHom z * dualBaseHom w) := by
    calc
      _ = (dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z)) *
          (dualTangentElement (dualLogDerivative w) * dualConstantHom (dualBaseHom w)) :=
        congrArg₂ (· * ·) (dualLogDerivative_factorization z) (dualLogDerivative_factorization w)
      _ = dualTangentElement (dualLogDerivative z) *
          (dualConstantHom (dualBaseHom z) * dualTangentElement (dualLogDerivative w) *
            (dualConstantHom (dualBaseHom z))⁻¹) *
          (dualConstantHom (dualBaseHom z) * dualConstantHom (dualBaseHom w)) := by group
      _ = _ := by rw [dualAdjoint_spec, dualTangentElement_mul, map_mul]
  rw [h, dualLogDerivative_tangent_mul_constant]

theorem dualBCH_insertion_identity (z : DualGroup hnil) (e m : L) :
    dualTangentElement (-e) * z * dualTangentElement (-m) *
        (dualConstantHom (dualBaseHom z))⁻¹ =
      dualTangentElement (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m) := by
  calc
    _ = dualTangentElement (-e) *
        (dualTangentElement (dualLogDerivative z) * dualConstantHom (dualBaseHom z)) *
        dualTangentElement (-m) * (dualConstantHom (dualBaseHom z))⁻¹ :=
      congrArg (fun a => dualTangentElement (-e) * a * dualTangentElement (-m) *
        (dualConstantHom (dualBaseHom z))⁻¹) (dualLogDerivative_factorization z)
    _ = dualTangentElement (-e) * dualTangentElement (dualLogDerivative z) *
        (dualConstantHom (dualBaseHom z) * dualTangentElement (-m) *
          (dualConstantHom (dualBaseHom z))⁻¹) := by group
    _ = dualTangentElement (-e + dualLogDerivative z + -dualAdjoint (dualBaseHom z) m) := by
      rw [dualAdjoint_neg_spec, dualTangentElement_mul, dualTangentElement_mul]
    _ = _ := by congr 1; abel

end Erdos3.NilpotentLieBCHGroup

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualIdealSteps
namespace OAI


namespace Erdos3

open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem dualQuotientEvaluate_lieBCH (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (s : ℕ) {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualQuotientEvaluate J (lieBCH s x y) =
      lieBCH s (dualQuotientEvaluate J x) (dualQuotientEvaluate J y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualQuotientEvaluate J ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualQuotientEvaluate J) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH (dualIdealRealization I J hIJ) s a b

end Erdos3


namespace Erdos3

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

instance dualRealScalarTower [IsScalarTower ℚ ℝ L] : IsScalarTower ℚ ℝ (DualLieAlgebra L) where
  smul_assoc q r x := by
    apply dualCoordinates.injective
    ext <;> simp [smul_assoc]

noncomputable instance dualRealLieAlgebra : LieAlgebra ℝ (DualLieAlgebra L) where
  lie_smul r x y := by
    apply dualCoordinates.injective
    ext
    · simp only [dualCoordinates_apply, dualBaseLinear_lie, dualBaseLinear_smul_real, lie_smul]
    · simp only [dualCoordinates_apply, dualTangentLinear_lie, dualTangentLinear_smul_real,
        dualBaseLinear_smul_real, lie_smul, smul_add]

end Erdos3


namespace Erdos3

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s t : ℕ} (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)
  (I : LieIdeal ℚ L) (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
  (hT : ∀ x y, y ∈ I → T ⁅x, y⁆ = ⁅B x, T y⁆)

include hL hM hT in
theorem dualLinearLift_lieBCH_of_steps {x y : DualLieAlgebra L}
    (hx : x ∈ dualIdealSubalgebra I) (hy : y ∈ dualIdealSubalgebra I) :
    dualLinearLift B T (lieBCH s x y) =
      lieBCH t (dualLinearLift B T x) (dualLinearLift B T y) := by
  let a : dualIdealSubalgebra I := ⟨x, hx⟩
  let b : dualIdealSubalgebra I := ⟨y, hy⟩
  calc
    _ = dualLinearLift B T ((dualIdealSubalgebra I).incl (lieBCH s a b)) :=
      congrArg (dualLinearLift B T) (map_lieBCH (dualIdealSubalgebra I).incl s a b).symm
    _ = _ := map_lieBCH_of_nilpotent_steps (dualIdealMorphism I B T hT)
      (lie_subalgebra_lowerCentralSeries_eq_bot (dualLie_lowerCentralSeries_eq_bot hL)
        (dualIdealSubalgebra I))
      (dualLie_lowerCentralSeries_eq_bot hM) a b

namespace NilpotentLieBCHGroup

include hT in
theorem dualLinearLift_adjoint_of_steps (g : NilpotentLieBCHGroup L s hL)
    (x : L) (hx : x ∈ I) :
    T (dualAdjoint g x) = dualAdjoint (mapOfSteps (hM := hM) B g) (T x) := by
  have hc : dualConstantLie g.coord ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualConstantLie g.coord) ∈ I
    rw [dualTangentLinear_constant]
    exact I.zero_mem
  have ht : dualInfinitesimal x ∈ dualIdealSubalgebra I := by
    change dualTangentLinear (dualInfinitesimal x) ∈ I
    rwa [dualTangentLinear_infinitesimal]
  have hh := dualLinearLift_lieBCH_of_steps hL hM I B T hT
    (lieBCH_mem (dualIdealSubalgebra I) s hc ht) ((dualIdealSubalgebra I).neg_mem hc)
  rw [dualLinearLift_lieBCH_of_steps hL hM I B T hT hc ht, dualLinearLift_constant,
    dualLinearLift_infinitesimal, map_neg, dualLinearLift_constant] at hh
  have he := congrArg dualTangentLinear hh
  rw [dualLinearLift_tangent] at he
  exact he

end NilpotentLieBCHGroup
end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DualAdjointFiltration
namespace OAI


namespace Erdos3

namespace NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  {s : ℕ} {hL : LieModule.lowerCentralSeries ℚ L L s = ⊥}
  {hM : LieModule.lowerCentralSeries ℚ M M s = ⊥}

theorem map_dualAdjoint (φ : L →ₗ⁅ℚ⁆ M) (g : NilpotentLieBCHGroup L s hL) (x : L) :
    φ (dualAdjoint g x) = dualAdjoint (map (hM := hM) φ g) (φ x) :=
  dualLinearLift_adjoint hM ⊤ φ φ.toLinearMap (fun a b _ => φ.map_lie a b) g x (by trivial)

theorem dualAdjoint_eq_self_of_lie_eq_zero (g : NilpotentLieBCHGroup L s hL) (x : L)
    (hgx : ⁅g.coord, x⁆ = 0) : dualAdjoint g x = x := by
  have hc : Commute (dualConstantHom g) (dualTangentElement x) := by
    apply commute_of_lie_eq_zero
    change ⁅dualConstantLie g.coord, dualInfinitesimal x⁆ = 0
    rw [dualConstant_infinitesimal_lie, hgx, map_zero]
  apply dualTangentElement_injective (hnil := hL)
  rw [← dualAdjoint_spec, hc.eq, mul_assoc, mul_inv_cancel, mul_one]

theorem dualAdjoint_sub_mem_ideal (I : LieIdeal ℚ L) (g : NilpotentLieBCHGroup L s hL)
    (x : L) (hgx : ⁅g.coord, x⁆ ∈ I) : dualAdjoint g x - x ∈ I := by
  have hz : ⁅(quotientHom I g).coord, lieQuotientMap I x⁆ = 0 := by
    rw [quotientHom_coord, ← LieHom.map_lie]
    exact (lieQuotientMap_eq_zero I _).mpr hgx
  apply (lieQuotientMap_eq_zero I _).mp
  rw [map_sub, map_dualAdjoint (hM := lie_quotient_lowerCentralSeries_eq_bot hL I)]
  exact sub_eq_zero.mpr (dualAdjoint_eq_self_of_lie_eq_zero (quotientHom I g) _ hz)

end NilpotentLieBCHGroup

namespace NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ} (F : NilpotentLieFiltration L s)

theorem dualAdjoint_sub_mem_layer {i j : ℕ} (g : F.Group) (hg : g.coord ∈ F.layer i)
    (x : L) (hx : x ∈ F.layer j) : dualAdjoint g x - x ∈ F.layer (i + j) :=
  dualAdjoint_sub_mem_ideal (F.layerIdeal (i + j)) g x (F.lie_mem hg hx)

theorem dualAdjoint_sub_mem_next_layer (j : ℕ) (g : F.Group) (x : L) (hx : x ∈ F.layer j) :
    dualAdjoint g x - x ∈ F.layer (j + 1) := by
  have hg : g.coord ∈ F.layer 1 := by rw [F.one_eq_top]; trivial
  simpa only [Nat.add_comm 1 j] using F.dualAdjoint_sub_mem_layer g hg x hx

end NilpotentLieFiltration
end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.BasisGradedCoordinateBasis
namespace OAI

section

namespace Erdos3

open Module

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem sub_basisBelowProjection_mem (b : Basis ι K V) (w : ι → ℕ) (j : ℕ) (x : V) :
    x - basisBelowProjection b w j x ∈ Submodule.span K (b '' {i | j ≤ w i}) := by
  simpa only [basisBelowProjection, Set.compl_ofPred, not_lt] using
    sub_basisCoordinateProjection_mem b {i | w i < j} x

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CocycleHorizontalNormalization
namespace OAI

section

namespace Erdos3

theorem horizontal_parts_separation {ι κ σ : Type*} [Fintype ι] [Fintype κ]
    (U K : Submodule ℝ (ι → ℝ)) (A : Matrix ι κ ℚ)
    (hspan : Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) = U ⊔ K)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l) (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p) (hκ : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    {α : σ →₀ ℕ} (hα : α ≠ 0) (y s r k : ι → ℝ)
    (hsystem : y = s + r + k) (hy : y ∈ U) (hk : k ∈ K)
    (hs : ‖s‖ ≤ Real.exp p / monomialScale T α) (hr : r ∈ realDenominatorGrid l) :
    s ∈ U ⊔ K ∧ r ∈ U ⊔ K := by
  have hsum : s + r ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
    rw [hspan]
    have hmem := (U ⊔ K).sub_mem ((show U ≤ U ⊔ K from le_sup_left) hy)
      ((show K ≤ U ⊔ K from le_sup_right) hk)
    simpa only [hsystem, add_sub_cancel_right] using hmem
  have he := controlled_real_column_span_separation A hH hl hA hp hι hκ hHp hlp T hT hα s r hs hr hsum
  simpa only [hspan] using he

end Erdos3

end

section

namespace Erdos3

theorem controlled_small_vector_separation
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hκ : (Fintype.card κ : ℝ) ≤ p) (hHp : (H : ℝ) ≤ Real.exp p)
    (hlp : (l : ℝ) ≤ Real.exp p) (a b : ι → ℝ)
    (ha : ‖a‖ ≤ Real.exp p / Real.exp (separationBudget p))
    (hb : b ∈ realDenominatorGrid l)
    (hsum : a + b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ)))) :
    a ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) ∧
      b ∈ Submodule.span ℝ (Set.range (fun j i => (A i j : ℝ))) := by
  apply controlled_real_column_span_separation A hH hl hA hp hι hκ hHp hlp
    (fun _ : Unit => Real.exp (separationBudget p)) (fun _ => le_rfl)
    (α := Finsupp.single () 1) (by simp) a b
  · simpa only [monomialScale, Finsupp.prod_single_index, pow_zero, pow_one] using ha
  · exact hb
  · exact hsum

end Erdos3

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

theorem mem_realQuotientStepHom_ker (g : F.realification.Group) :
    g ∈ (F.realQuotientStepHom I hI).ker ↔ g.coord ∈ I.toSubmodule.baseChange ℝ := by
  constructor
  · intro hg
    apply (realification_mkQ_eq_zero_iff I.toSubmodule g.coord).mp
    exact congrArg (fun z : (F.quotientLie I hI).realification.Group => z.coord)
      (MonoidHom.mem_ker.mp hg)
  · intro hg
    apply MonoidHom.mem_ker.mpr
    apply NilpotentLieBCHGroup.ext
    exact (realification_mkQ_eq_zero_iff I.toSubmodule g.coord).mpr hg

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LowerStepSquare
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

omit [Fintype κ] in
theorem scaled_real_basis_central (b : Basis κ ℚ L) (j : κ)
    (hv : ∀ w : L, ⁅b j, w⁆ = 0) (N : ℕ) (w : ℝ ⊗[ℚ] L) :
    ⁅(N : ℝ) • (b.baseChange ℝ) j, w⁆ = 0 := by
  rw [smul_lie, Basis.baseChange_apply]
  change (N : ℝ) • ⁅rationalLieInclusion (b j), w⁆ = 0
  rw [rationalLieInclusion_central _ hv, smul_zero]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem square_top_projections {g : F.squareFiltration.Group}
    (hg : g ∈ F.squareFiltration.subgroup s) :
    F.squareFstHom g ∈ F.subgroup s ∧ F.squareFstHom g = F.squareSndHom g := by
  have h := (F.mem_squareFiltration_top g.coord).mp hg
  exact ⟨h.1, NilpotentLieBCHGroup.ext h.2⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

variable {L ι : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem realLayer_le_span_scaled_basis (b : Basis ι ℚ L) (i : ℕ) (S : Set ι)
    (hS : F.layer i = Submodule.span ℚ (b '' S)) (N : ℕ) (hN : 0 < N) :
    (F.realLayer i).toSubmodule ≤
      Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j)) := by
  rw [F.realLayer_eq_span_basis b i S hS]
  apply Submodule.span_le.mpr
  rintro v ⟨j, hj, rfl⟩
  change b.baseChange ℝ j ∈
    Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j))
  have h : (N : ℝ)⁻¹ • ((N : ℝ) • b.baseChange ℝ j) ∈
      Submodule.span ℝ (Set.range (fun j : S => (N : ℝ) • b.baseChange ℝ j)) :=
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
  simpa only [smul_smul, inv_mul_cancel₀ (show (N : ℝ) ≠ 0 by exact_mod_cast hN.ne'),
    one_smul] using h

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

theorem shiftedPolynomialIdeal_lie_mem {i j : ℕ} {p q : F.adaptedLieSubalgebra w}
    (hp : p ∈ F.shiftedPolynomialIdeal w i) (hq : q ∈ F.shiftedPolynomialIdeal w j) :
    ⁅p, q⁆ ∈ F.shiftedPolynomialIdeal w (i + j) :=
  F.lie_mem_shiftedAdaptedSubmodule w hp hq

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

theorem exists_square_polynomial (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (p q : VectorPolynomial σ ℚ L) (hp : F.Adapted w p) (hq : F.Adapted w q)
    (hdiff : ∀ α, coefficients (p - q) α ∈ F.layer (Finsupp.weight w α + 1))
    (hzero : coefficients (p - q) 0 ∈ F.layer 2) :
    ∃ r : VectorPolynomial σ ℚ F.squareLieSubalgebra,
      F.squareFiltration.Adapted w r ∧
      VectorPolynomial.map F.squareFst.toLinearMap r = p ∧
      VectorPolynomial.map F.squareSnd.toLinearMap r = q := by
  simp only [map_sub, Finsupp.sub_apply] at hdiff hzero
  have hcoeff (α : σ →₀ ℕ) : coefficients (pair p q) α ∈ F.squareLieSubalgebra.toSubmodule := by
    rw [coefficients_pair]
    change (coefficients p α, coefficients q α) ∈ F.squareLieSubalgebra
    rw [F.mem_squareLieSubalgebra]
    change coefficients p α - coefficients q α ∈ F.layer 2
    by_cases hα : α = 0
    · simpa only [hα] using hzero
    · exact F.antitone (by have := positive_weight_of_ne_zero w hw hα; omega) (hdiff α)
  let r := restrictCoefficients F.squareLieSubalgebra.toSubmodule (pair p q) hcoeff
  have hr (α : σ →₀ ℕ) : (coefficients r α : L × L) = (coefficients p α, coefficients q α) := by
    rw [coefficients_restrictCoefficients, coefficients_pair]
  refine ⟨r, ?_, ?_, ?_⟩
  · apply (F.squareFiltration.adapted_iff_coefficients w r).mpr
    intro α
    rw [F.mem_squareFiltration_layer, hr, F.mem_squareLayer]
    exact ⟨(F.adapted_iff_coefficients w p).mp hp α,
      (F.adapted_iff_coefficients w q).mp hq α, hdiff α⟩
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    change (coefficients r α).val.1 = coefficients p α
    rw [hr]
  · apply coefficients.injective
    ext α
    rw [coefficients_map]
    change (coefficients r α).val.2 = coefficients q α
    rw [hr]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct BigOperators

theorem exponent_of_weight_le_one {σ : Type*} (α : σ →₀ ℕ)
    (hα : Finsupp.weight (fun _ : σ => 1) α ≤ 1) :
    α = 0 ∨ ∃ i, α = Finsupp.single i 1 := by
  by_cases hz : α = 0
  · exact Or.inl hz
  · right
    have hp := NilpotentLieFiltration.positive_weight_of_ne_zero (fun _ : σ => 1) (by simp) hz
    have he : Finsupp.weight (fun _ : σ => 1) α = 1 := by omega
    apply (Finsupp.sum_eq_one_iff α).mp
    simpa only [Finsupp.weight_apply, smul_eq_mul, mul_one] using he

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem adaptedPolynomialFiltration_layer (w : σ → ℕ) (j : ℕ) :
    (F.adaptedPolynomialFiltration w).layer j = Submodule.span ℚ
      (F.adaptedMonomialBasis b ω hF w '' {z | j ≤ ω z.val.2}) := by
  ext p
  change (∀ α, coefficients (p : VectorPolynomial σ ℚ L) α ∈ F.layer j) ↔ _
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

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem shiftedMonomialBasis_repr (w : σ → ℕ) (k : ℕ)
    (p : F.shiftedPolynomialIdeal w k) (z : ShiftedMonomialIndex w ω k) :
    (F.shiftedMonomialBasis b ω hF w k).repr p z =
      b.repr (coefficients (p.val : VectorPolynomial σ ℚ L) z.val.val.1) z.val.val.2 := by
  rw [shiftedMonomialBasis, supportedSubmoduleBasis_repr, F.adaptedMonomialBasis_repr]

theorem shiftedPolynomial_next_eq_span (w : σ → ℕ) (k : ℕ) :
    (F.shiftedPolynomialIdeal w (k + 1)).toSubmodule.comap
        (F.shiftedPolynomialIdeal w k).toSubmodule.subtype =
      Submodule.span ℚ (F.shiftedMonomialBasis b ω hF w k ''
        {z | Finsupp.weight w z.val.val.1 + (k + 1) ≤ ω z.val.val.2}) := by
  ext p
  change (∀ α, coefficients (p.val : VectorPolynomial σ ℚ L) α ∈
    F.layer (Finsupp.weight w α + (k + 1))) ↔ _
  rw [basis_mem_span_image_iff]
  simp_rw [F.mem_layer_iff_basis_coordinates b ω hF]
  constructor
  · intro h z hz
    rw [F.shiftedMonomialBasis_repr]
    exact h z.val.val.1 z.val.val.2 hz
  · intro h α i hi
    by_cases hdeg : Finsupp.weight w α + k ≤ ω i
    · have ha : Finsupp.weight w α ≤ ω i := (Nat.le_add_right _ _).trans hdeg
      have hz := h ⟨⟨(α, i), ha⟩, hdeg⟩ hi
      simpa only [F.shiftedMonomialBasis_repr] using hz
    · exact (F.mem_layer_iff_basis_coordinates b ω hF _ _).mp (p.property α) i hdeg

end Erdos3.NilpotentLieFiltration

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

theorem polynomialSymbolBasis_bracket_height (w : σ → ℕ) {H : ℕ} (hH : 1 ≤ H)
    (hb : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (u v z : SymbolBasisIndex w ω) :
    RationalHeightLE ((F.polynomialSymbolBasis b ω hlayers w).repr
      ⁅F.polynomialSymbolBasis b ω hlayers w u, F.polynomialSymbolBasis b ω hlayers w v⁆ z) H := by
  classical
  rw [F.polynomialSymbolBasis_bracket]
  split_ifs
  · exact hb _ _ _
  · exact rationalHeightLE_zero hH

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped BigOperators

variable {σ ι : Type*} (w : σ → ℕ) (ω : ι → ℕ) (s : ℕ)
  (hw : ∀ i, 0 < w i) (hω : ∀ i, ω i ≤ s)

include hw hω

variable [Fintype σ] [Fintype ι]

theorem symbolBasisIndex_card_le [Fintype (SymbolBasisIndex w ω)] :
    Fintype.card (SymbolBasisIndex w ω) ≤ Fintype.card ι * (s + 1) * (Fintype.card σ + 1) ^ s := by
  have hc := Fintype.card_le_of_injective (symbolBasisCode w ω s hw hω)
    (symbolBasisCode_injective w ω s hw hω)
  simp only [Fintype.card_prod, Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin] at hc
  apply hc.trans
  calc
    (∑ n : Fin (s + 1), Fintype.card σ ^ n.val) * Fintype.card ι ≤
        (∑ _ : Fin (s + 1), (Fintype.card σ + 1) ^ s) * Fintype.card ι := by
      apply Nat.mul_le_mul_right
      apply Finset.sum_le_sum
      intro n _
      exact (Nat.pow_le_pow_left (Nat.le_succ _) _).trans
        (Nat.pow_le_pow_right (by omega) (Nat.le_of_lt_succ n.isLt))
    _ = _ := by simp; ring

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

theorem polynomialSymbolFiltration_layer (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (j : ℕ) :
    (F.polynomialSymbolFiltration w).layer j =
      Submodule.span ℚ (F.polynomialSymbolBasis b ω hlayers w ''
        {z : SymbolBasisIndex w ω | j ≤ ω z.val.2}) := by
  apply le_antisymm
  · rintro x ⟨p, hp, rfl⟩
    rw [basis_mem_span_image_iff]
    intro z hz
    change (F.polynomialSymbolBasis b ω hlayers w).repr (F.polynomialSymbolMap w p) z = 0
    rw [F.polynomialSymbolBasis_repr_map]
    exact (F.mem_layer_iff_basis_coordinates b ω hlayers j _).mp (hp z.val.1) z.val.2 hz
  · apply Submodule.span_le.mpr
    rintro _ ⟨z, hz, rfl⟩
    let p := F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩
    refine ⟨p, ?_, ?_⟩
    · change (p : VectorPolynomial σ ℚ L) ∈ F.polynomialLayer j
      change (F.adaptedMonomialBasis b ω hlayers w ⟨z.val, z.property.le⟩ :
        VectorPolynomial σ ℚ L) ∈ F.polynomialLayer j
      rw [F.adaptedMonomialBasis_coe]
      apply F.monomial_mem_polynomialLayer
      rw [hlayers]
      exact Submodule.subset_span ⟨z.val.2, hz, rfl⟩
    · exact (F.polynomialSymbolBasis_apply b ω hlayers w z).symm

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SquareGradedRelative
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s)

def squareDiagonalLayer (j : ℕ) : F.layer j →ₗ[ℚ] F.squareFiltration.layer j where
  toFun x := ⟨⟨(x, x), (F.mem_squareLieSubalgebra _).mpr (by simp)⟩,
    x.property, x.property, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def squareGradedDiagonalPiece (j : ℕ) :
    F.layer j →ₗ[ℚ] F.squareFiltration.AssociatedGraded :=
  (F.squareFiltration.associatedGradedPieceMap j).comp (F.squareDiagonalLayer j)

theorem squareGradedDiagonalPiece_eq_zero_iff (j : ℕ) (x : F.layer j) :
    F.squareGradedDiagonalPiece j x = 0 ↔ (x : L) ∈ F.layer (j + 1) := by
  change F.squareFiltration.associatedGradedPieceMap j (F.squareDiagonalLayer j x) = 0 ↔ _
  rw [F.squareFiltration.associatedGradedPieceMap_eq_zero_iff]
  change ((x : L) ∈ F.layer (j + 1) ∧ (x : L) ∈ F.layer (j + 1) ∧
    (x : L) - x ∈ F.layer (j + 1 + 1)) ↔ _
  simp only [sub_self, Submodule.zero_mem, and_true, and_self]

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

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem realPolynomialSymbolBasis_bracket_support (u v z : SymbolBasisIndex w ω)
    (h : ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr
      ⁅(F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ u,
        (F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ v⁆ z ≠ 0) :
    u.val.1 + v.val.1 = z.val.1 := by
  classical
  by_contra hn
  apply h
  rw [realLieBasis_structure]
  change (((F.polynomialSymbolBasis b ω hlayers w).repr
    ⁅F.polynomialSymbolBasis b ω hlayers w u,
      F.polynomialSymbolBasis b ω hlayers w v⁆ z : ℚ) : ℝ) = 0
  simp only [F.polynomialSymbolBasis_bracket, hn, ↓reduceIte, Rat.cast_zero]

noncomputable def scaledRealPolynomialSymbolBasis (T : σ → ℝ) (hT : ∀ i, 0 < T i) :
    Basis (SymbolBasisIndex w ω) ℝ (F.RealPolynomialSymbol w) :=
  inverseScaledBasis ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ)
    (fun z => monomialScale T z.val.1) (fun z => monomialScale_pos T hT z.val.1)

theorem scaledRealPolynomialSymbolBasis_repr (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr x z =
      monomialScale T z.val.1 *
        ((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z :=
  inverseScaledBasis_repr _ _ _ _ _

theorem scaledRealPolynomialSymbolBasis_structure (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (u v z : SymbolBasisIndex w ω) :
    (F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr
      ⁅F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT u,
        F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT v⁆ z =
      (lieStructureConstants (F.polynomialSymbolBasis b ω hlayers w) u v z : ℝ) := by
  apply Eq.trans (inverseScaledBasis_bracket _ _ _ ?_ u v z)
  · exact realLieBasis_structure _ u v z
  · intro i j k h
    have hijk := F.realPolynomialSymbolBasis_bracket_support b ω hlayers w i j k h
    rw [← hijk, monomialScale_add]

theorem scaledRealPolynomialSymbolBasis_bound_iff (T : σ → ℝ) (hT : ∀ i, 0 < T i)
    (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) (M : ℝ) :
    |(F.scaledRealPolynomialSymbolBasis b ω hlayers w T hT).repr x z| ≤ M ↔
      |((F.polynomialSymbolBasis b ω hlayers w).baseChange ℝ).repr x z| ≤
        M / monomialScale T z.val.1 := by
  rw [F.scaledRealPolynomialSymbolBasis_repr, abs_mul,
    abs_of_pos (monomialScale_pos T hT z.val.1), le_div_iff₀ (monomialScale_pos T hT z.val.1)]
  rw [mul_comm]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ : Type*}

def reindexSymbolBasisIndex (w : σ → ℕ) (ω : ι → ℕ) (e : ι ≃ κ) :
    SymbolBasisIndex w ω ≃ SymbolBasisIndex w (fun k => ω (e.symm k)) where
  toFun z := ⟨(z.val.1, e z.val.2), by simpa only [Equiv.symm_apply_apply] using z.property⟩
  invFun z := ⟨(z.val.1, e.symm z.val.2), z.property⟩
  left_inv z := by apply Subtype.ext; simp only [Equiv.symm_apply_apply]
  right_inv z := by apply Subtype.ext; simp only [Equiv.apply_symm_apply]

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) (e : ι ≃ κ)
  (hF' : ∀ j, F.layer j = Submodule.span ℚ ((b.reindex e) '' {k | j ≤ ω (e.symm k)}))
  (w : σ → ℕ)

theorem polynomialSymbolBasis_repr_reindex (x : F.PolynomialSymbol w)
    (z : SymbolBasisIndex w (fun k => ω (e.symm k))) :
    (F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).repr x z =
      (F.polynomialSymbolBasis b ω hF w).repr x ((reindexSymbolBasisIndex w ω e).symm z) := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolBasis_repr_map, F.polynomialSymbolBasis_repr_map,
    Basis.repr_reindex_apply]
  rfl

theorem realPolynomialSymbolBasis_repr_reindex (x : F.RealPolynomialSymbol w)
    (z : SymbolBasisIndex w (fun k => ω (e.symm k))) :
    ((F.polynomialSymbolBasis (b.reindex e) (fun k => ω (e.symm k)) hF' w).baseChange ℝ).repr x z =
      ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr x
        ((reindexSymbolBasisIndex w ω e).symm z) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [Basis.baseChange_repr_tmul, Basis.baseChange_repr_tmul,
      F.polynomialSymbolBasis_repr_reindex b ω hF e hF' w]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem symbolSlowBound_reindex_iff (T : σ → ℝ) (M : ℝ) (g : F.RealPolynomialSymbolGroup w) :
    F.SymbolSlowBound (b.reindex e) (fun k => ω (e.symm k)) hF' w T M g ↔
      F.SymbolSlowBound b ω hF w T M g := by
  constructor
  · intro hg z
    have hz := hg (reindexSymbolBasisIndex w ω e z)
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w,
      Equiv.symm_apply_apply] at hz
    exact hz
  · intro hg z
    rw [F.realPolynomialSymbolBasis_repr_reindex b ω hF e hF' w]
    exact hg ((reindexSymbolBasisIndex w ω e).symm z)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.RealGradedSymbolPolynomial
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

theorem realificationLinearEquiv_eq_zero_iff
    (x : ℝ ⊗[ℚ] VectorPolynomial σ ℚ V) :
    x = 0 ↔ ∀ α, coefficients (realificationLinearEquiv x) α = 0 := by
  constructor
  · rintro rfl α
    simp only [map_zero, Finsupp.zero_apply]
  · intro hx
    apply realificationLinearEquiv.injective
    apply coefficients.injective
    ext α
    simpa only [map_zero, Finsupp.zero_apply] using hx α

end Linear

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped TensorProduct

section Linear

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

instance realScalarTower : IsScalarTower ℚ ℝ (VectorPolynomial σ ℚ (ℝ ⊗[ℚ] V)) :=
  LinearEquiv.isScalarTower ℝ (realificationLinearEquiv (σ := σ) (V := V)).symm

end Linear

end Erdos3.VectorPolynomial

end

section

namespace Erdos3

open Module VectorPolynomial

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

theorem gradedSymbolPolynomial_injective :
    Function.Injective (F.gradedSymbolPolynomial b ω hlayers w) := by
  intro x y hxy
  apply (F.polynomialSymbolBasis b ω hlayers w).repr.injective
  ext z
  rw [← F.gradedSymbolPolynomial_coefficient, ← F.gradedSymbolPolynomial_coefficient, hxy]

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

theorem realGradedSymbolPolynomial_map_coefficient {W : Type*} [AddCommGroup W] [Module ℚ W]
    (f : F.AssociatedGraded →ₗ[ℚ] W) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (VectorPolynomial.realificationLinearEquiv
      (((VectorPolynomial.map f).comp (F.gradedSymbolPolynomial b ω hlayers w)).baseChange ℝ x)) α =
      f.baseChange ℝ (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a x =>
    rw [LinearMap.baseChange_tmul, coefficients_realificationLinearEquiv_tmul,
      LinearMap.comp_apply, coefficients_map, F.realGradedSymbolPolynomial_coefficient_tmul,
      LinearMap.baseChange_tmul]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

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
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (w : σ → ℕ)

noncomputable def symbolSubalgebraQuotientMap (U : LieSubalgebra ℚ F.AssociatedGraded) :
    F.PolynomialSymbol w →ₗ[ℚ] VectorPolynomial σ ℚ (F.AssociatedGraded ⧸ U.toSubmodule) :=
  (VectorPolynomial.map U.toSubmodule.mkQ).comp (F.gradedSymbolPolynomial b ω hlayers w)

theorem symbolSubalgebraQuotientMap_real_coefficient
    (U : LieSubalgebra ℚ F.AssociatedGraded) (x : F.RealPolynomialSymbol w) (α : σ →₀ ℕ) :
    coefficients (VectorPolynomial.realificationLinearEquiv
      ((F.symbolSubalgebraQuotientMap b ω hlayers w U).baseChange ℝ x)) α =
      U.toSubmodule.mkQ.baseChange ℝ
        (coefficients (F.realGradedSymbolPolynomial b ω hlayers w x) α) := by
  unfold symbolSubalgebraQuotientMap
  exact F.realGradedSymbolPolynomial_map_coefficient b ω hlayers w U.toSubmodule.mkQ x α

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ControlledLinearSubspaceLift
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_constraint_section
    {ι κ μ δ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    (r : ι → δ) (c : κ → δ) (t : μ → δ)
    (Q : Matrix ι κ ℚ) (P : Matrix μ κ ℚ)
    (hQblock : ∀ i j, r i ≠ c j → Q i j = 0)
    (hPblock : ∀ i j, t i ≠ c j → P i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hQ : ∀ i j, RationalHeightLE (Q i j) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : (Fintype.card κ : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ (T : Matrix κ μ ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ t j → T i j = 0) ∧
      (∀ i j, RationalHeightLE (T i j) (rationalKernelHeight (Fintype.card (ι ⊕ μ)) H)) ∧
      (∀ y : μ → ℝ,
        (∃ x : κ → ℝ, (fun i j => (Q i j : ℝ)) *ᵥ x = 0 ∧
          (fun i j => (P i j : ℝ)) *ᵥ x = y) →
        (fun i j => (Q i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = 0 ∧
          (fun i j => (P i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (M : ℝ), 0 ≤ M →
        ∀ y : μ → ℝ, (∀ i, |y i| ≤ M / W (t i)) →
          ∀ i, |((fun i j => (T i j : ℝ)) *ᵥ y) i| ≤
            Real.exp ((p + 2) ^ 18) * M / W (c i)) ∧
      (∀ y : μ → ℝ, y ∈ realDenominatorGrid l →
        (fun i j => (T i j : ℝ)) *ᵥ y ∈ realDenominatorGrid m) := by
  let A := constraintProjectionMatrix Q P
  have hAblock : ∀ i j, Sum.elim r t i ≠ c j → A i j = 0 := by
    intro i j hij
    cases i with
    | inl i => exact hQblock i j hij
    | inr i => exact hPblock i j hij
  have hA : ∀ i j, RationalHeightLE (A i j) H := by
    intro i j
    cases i with
    | inl i => exact hQ i j
    | inr i => exact hP i j
  obtain ⟨S, hS, hSblock, hSH⟩ :=
    exists_bounded_block_image_section (Sum.elim r t) c A hAblock hH hA
  let T : Matrix κ μ ℚ := fun i j => S i (Sum.inr j)
  have hTS (y : μ → ℝ) :
      (fun i j => (S i j : ℝ)) *ᵥ constraintProjectionInput (ι := ι) y =
        (fun i j => (T i j : ℝ)) *ᵥ y :=
    mulVec_constraintProjectionInput _ y
  refine ⟨T, matrixDenominator S * l, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hSH hp hrows hcols hHp hlp,
    ⟨matrixDenominator S, Nat.mul_comm _ _⟩,
    (fun i j hij => hSblock i (Sum.inr j) hij), (fun i j => hSH i (Sum.inr j)), ?_, ?_, ?_⟩
  · intro y hy
    have hAy : constraintProjectionInput (ι := ι) y ∈
        LinearMap.range (Matrix.mulVecLin (fun i j => (A i j : ℝ))) := by
      obtain ⟨x, hxQ, hxP⟩ := hy
      refine ⟨x, ?_⟩
      funext i
      cases i with
      | inl i => exact congrFun hxQ i
      | inr i => exact congrFun hxP i
    have he := real_matrix_image_section_apply A S hS _ hAy
    rw [hTS] at he
    constructor
    · funext i
      exact congrFun he (Sum.inl i)
    · funext i
      exact congrFun he (Sum.inr i)
  · intro W hW M hM y hy i
    have hh := real_image_section_weighted_bound (Sum.elim r t) c S H hSblock hSH
      hp hrows hcols hHp W hW hM (constraintProjectionInput (ι := ι) y)
      (constraintProjectionInput_weighted r t W hW hM y hy) i
    rwa [hTS] at hh
  · intro y hy
    have hh := real_matrix_denominator_grid S l (constraintProjectionInput (ι := ι) y)
      (constraintProjectionInput_grid l y hy)
    rwa [hTS] at hh

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_controlled_block_subspace_lift
    {ι κ μ δ L : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [LieRing L] [LieAlgebra ℚ L]
    (b : Basis ι ℚ L) (c : ι → δ) (r : μ → δ) (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant b c U)
    (P : Matrix μ ι ℚ) (hPblock : ∀ i j, r i ≠ c j → P i j = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (b.repr (v j) i) H)
    (hP : ∀ i j, RationalHeightLE (P i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (T : Matrix ι μ ℚ) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → T i j = 0) ∧
      (∀ y : μ → ℝ,
        (∃ x ∈ U.baseChange ℝ, (fun i j => (P i j : ℝ)) *ᵥ (b.baseChange ℝ).equivFun x = y) →
        (b.baseChange ℝ).equivFun.symm ((fun i j => (T i j : ℝ)) *ᵥ y) ∈ U.baseChange ℝ ∧
          (fun i j => (P i j : ℝ)) *ᵥ ((fun i j => (T i j : ℝ)) *ᵥ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (M : ℝ), 0 ≤ M →
        ∀ y : μ → ℝ, (∀ i, |y i| ≤ M / W (r i)) →
          ∀ i, |((fun i j => (T i j : ℝ)) *ᵥ y) i| ≤
            Real.exp ((q + 2) ^ 18) * M / W (c i)) ∧
      (∀ y : μ → ℝ, y ∈ realDenominatorGrid l →
        (fun i j => (T i j : ℝ)) *ᵥ y ∈ realDenominatorGrid m) := by
  let q : ℝ := (p + 2) ^ 10
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := le_power_budget hp (by decide : 1 ≤ 10)
  have hι : (Fintype.card ι : ℝ) ≤ p := by
    have hsum : (Fintype.card ι : ℝ) + Fintype.card μ ≤ p := by
      simpa only [Fintype.card_sum, Nat.cast_add] using hrows
    exact (le_add_of_nonneg_right (Nat.cast_nonneg _)).trans hsum
  let H' := max (imageDefiningHeight (Fintype.card ι * Fintype.card κ) (Fintype.card ι) H) H
  have hH' : 1 ≤ H' := hH.trans (Nat.le_max_right _ _)
  have hH'q : (H' : ℝ) ≤ Real.exp q := by
    dsimp only [H']
    rw [Nat.cast_max]
    exact max_le (imageDefiningHeight_le_exp _ _ _ hp hcols hι hHp)
      (hHp.trans (Real.exp_le_exp.mpr hpq))
  obtain ⟨Q, hQ, hQblock, hQker⟩ :=
    exists_block_subspace_defining_matrix b c U v hspan hU hH hv
  obtain ⟨T, m, hm, hmp, hlm, hTblock, _, hsolve, hslow, hgrid⟩ :=
    exists_controlled_constraint_section c c r Q P hQblock hPblock hH' hl
      (fun i j => (hQ i j).mono (Nat.le_max_left _ _))
      (fun i j => (hP i j).mono (Nat.le_max_right _ _))
      hq (hrows.trans hpq) (hι.trans hpq) hH'q (hlp.trans (Real.exp_le_exp.mpr hpq))
  refine ⟨T, m, hm, hmp, hlm, hTblock, ?_, hslow, hgrid⟩
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hy
  obtain ⟨hzero, hright⟩ := hsolve y
    ⟨(b.baseChange ℝ).equivFun x, (hQker x).mpr hx, hxy⟩
  refine ⟨(hQker _).mp ?_, hright⟩
  simpa only [LinearEquiv.apply_symm_apply] using hzero

end Erdos3

end

section

namespace Erdos3

open Module
open scoped Matrix TensorProduct

theorem exists_controlled_linear_subspace_lift
    {ι κ μ δ L M : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    (e : Basis ι ℚ L) (f : Basis μ ℚ M) (c : ι → δ) (r : μ → δ)
    (U : Submodule ℚ L) (v : κ → L)
    (hspan : Submodule.span ℚ (Set.range v) = U) (hU : BasisBlockInvariant e c U)
    (φ : L →ₗ[ℚ] M) (hblock : ∀ i j, r i ≠ c j → f.repr (φ (e j)) i = 0)
    {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hv : ∀ j i, RationalHeightLE (e.repr (v j) i) H)
    (hφ : ∀ i j, RationalHeightLE (f.repr (φ (e j)) i) H)
    {p : ℝ} (hp : 0 ≤ p) (hrows : (Fintype.card (ι ⊕ μ) : ℝ) ≤ p)
    (hcols : ((Fintype.card ι * Fintype.card κ : ℕ) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    let q := (p + 2) ^ 10
    ∃ (σ : M →ₗ[ℚ] L) (m : ℕ),
      0 < m ∧ (m : ℝ) ≤ Real.exp ((q + 2) ^ 36) ∧ l ∣ m ∧
      (∀ i j, c i ≠ r j → e.repr (σ (f j)) i = 0) ∧
      (∀ y ∈ (U.map φ).baseChange ℝ,
        σ.baseChange ℝ y ∈ U.baseChange ℝ ∧ φ.baseChange ℝ (σ.baseChange ℝ y) = y) ∧
      (∀ (W : δ → ℝ), (∀ d, 0 < W d) → ∀ (B : ℝ), 0 ≤ B →
        ∀ y : ℝ ⊗[ℚ] M, (∀ i, |(f.baseChange ℝ).equivFun y i| ≤ B / W (r i)) →
          ∀ i, |(e.baseChange ℝ).equivFun (σ.baseChange ℝ y) i| ≤
            Real.exp ((q + 2) ^ 18) * B / W (c i)) ∧
      (∀ y : ℝ ⊗[ℚ] M, (f.baseChange ℝ).equivFun y ∈ realDenominatorGrid l →
        (e.baseChange ℝ).equivFun (σ.baseChange ℝ y) ∈ realDenominatorGrid m) := by
  classical
  let P := LinearMap.toMatrix e f φ
  obtain ⟨T, m, hm, hmp, hlm, hTblock, hsolve, hslow, hgrid⟩ :=
    exists_controlled_block_subspace_lift e c r U v hspan hU P
      (by intro i j hij; simpa only [P, LinearMap.toMatrix_apply] using hblock i j hij) hH hl hv
      (by intro i j; simpa only [P, LinearMap.toMatrix_apply] using hφ i j) hp hrows hcols hHp hlp
  let σ := Matrix.toLin f e T
  have hcoord (y : ℝ ⊗[ℚ] M) :
      (e.baseChange ℝ).equivFun (σ.baseChange ℝ y) =
        (fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y :=
    toLin_baseChange_coordinates e f T y
  have hlift (y : ℝ ⊗[ℚ] M) : σ.baseChange ℝ y =
      (e.baseChange ℝ).equivFun.symm ((fun i j => (T i j : ℝ)) *ᵥ (f.baseChange ℝ).equivFun y) := by
    apply (e.baseChange ℝ).equivFun.injective
    rw [hcoord, LinearEquiv.apply_symm_apply]
  refine ⟨σ, m, hm, hmp, hlm, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    have he := LinearMap.toMatrix_apply f e σ i j
    rw [LinearMap.toMatrix_toLin] at he
    exact he.symm.trans (hTblock i j hij)
  · intro y hy
    rw [realification_map] at hy
    obtain ⟨x, hx, hxy⟩ := hy
    obtain ⟨hmem, hright⟩ := hsolve ((f.baseChange ℝ).equivFun y)
      ⟨x, hx, (baseChange_matrix_apply e f φ x).trans (congrArg (f.baseChange ℝ).equivFun hxy)⟩
    constructor
    · rwa [hlift]
    · apply (f.baseChange ℝ).equivFun.injective
      rw [← baseChange_matrix_apply e f φ, hcoord]
      exact hright
  · intro W hW B hB y hy i
    rw [hcoord]
    exact hslow W hW B hB ((f.baseChange ℝ).equivFun y) hy i
  · intro y hy
    rw [hcoord]
    exact hgrid ((f.baseChange ℝ).equivFun y) hy

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScaledLatticeCovolume
namespace OAI

section

namespace Erdos3

open Module

theorem exists_lattice_index_covolume_factor
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    ∃ L : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (L y) = y) ∧
      (∀ x, L (π x) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ ^ 2 =
        ZLattice.covolume (latticeKernel Λ π) ^ 2 *
        ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) ^ 2 *
        (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det := by
  classical
  let H := latticeImage Λ π
  let K := latticeKernel Λ π
  let : DiscreteTopology H := latticeImage_discrete Λ π hinteger
  let : IsZLattice ℝ H := latticeImage_full Λ π hsurj
  let : IsZLattice ℝ K := latticeKernel_full Λ π hinteger
  let bK := Free.chooseBasis ℤ K
  let bI := IsZLattice.basis H
  let B := bI.ofZLatticeBasis ℝ H
  obtain ⟨L, hright, hsection⟩ := exists_orthogonal_section π hsurj
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg π hxy
    simpa only [hright] using h
  obtain ⟨b, _, hbI, hcov⟩ := exists_lattice_basis_covolume_factor Λ π bK bI
  have hw (j : ι) : (b (Sum.inr j) : E) -
      (LinearMap.ker π).starProjection (b (Sum.inr j) : E) = L (B j) := by
    rw [← hsection]
    apply congrArg L
    simpa only [B, Basis.ofZLatticeBasis_apply] using hbI j
  have hcov' : ZLattice.covolume Λ ^ 2 = ZLattice.covolume K ^ 2 *
      (Matrix.gram ℝ (fun j : ι => L (B j))).det := by
    simpa only [hw] using hcov
  have hgram := gram_det_injective_map_basis L hL (Pi.basisFun ℝ ι) B
  have hB : (B : ι → (ι → ℝ)) = fun j => (bI j).val := by
    funext j
    exact bI.ofZLatticeBasis_apply ℝ H j
  have hdet : |(Pi.basisFun ℝ ι).det B| =
      ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) := by
    rw [Pi.basisFun_det_apply, hB]
    exact (ZLattice.covolume_eq_det H bI).symm.trans
      (integer_lattice_covolume_eq_index H (latticeImage_le_integer Λ π hinteger))
  have hsq := congrArg (fun t : ℝ => t ^ 2) hdet
  rw [sq_abs] at hsq
  refine ⟨L, hright, hsection, ?_⟩
  rw [hgram, hsq] at hcov'
  simpa only [mul_assoc] using hcov'

end Erdos3

end

section

namespace Erdos3

theorem exists_lattice_covolume_identity
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π) :
    ∃ L : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (L y) = y) ∧
      (∀ x, L (π x) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π) *
        ((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) *
        Real.sqrt (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det := by
  let : IsZLattice ℝ (latticeKernel Λ π) := latticeKernel_full Λ π hinteger
  obtain ⟨L, hright, hsection, hsq⟩ := exists_lattice_index_covolume_factor Λ π hinteger hsurj
  refine ⟨L, hright, hsection, ?_⟩
  have h := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq (ZLattice.covolume_pos Λ MeasureTheory.volume).le] at h
  rw [Real.sqrt_mul (mul_nonneg (sq_nonneg _) (sq_nonneg _)),
    Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (ZLattice.covolume_pos (latticeKernel Λ π) MeasureTheory.volume).le,
    Real.sqrt_sq (Nat.cast_nonneg _)] at h
  exact h

end Erdos3

end

section

namespace Erdos3

theorem exists_scaled_lattice_covolume_identity
    {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    [Fintype ι] [DecidableEq ι]
    (Λ : Submodule ℤ E) [DiscreteTopology Λ] [IsZLattice ℝ Λ]
    (π : E →ₗ[ℝ] (ι → ℝ))
    (hinteger : ∀ x ∈ Λ, π x ∈ realIntegerGrid) (hsurj : Function.Surjective π)
    (T : ι → ℝ) (hT : ∀ i, 0 < T i) :
    ∃ G : (ι → ℝ) →ₗ[ℝ] E,
      (∀ y, π (G y) = fun i => T i * y i) ∧
      (∀ x, G (fun i => π x i / T i) = x - (LinearMap.ker π).starProjection x) ∧
      ZLattice.covolume Λ = ZLattice.covolume (latticeKernel Λ π) *
        (((latticeImage Λ π).toAddSubgroup.relIndex integerCoordinateLattice.toAddSubgroup : ℝ) /
          ∏ i, T i) *
        Real.sqrt (Matrix.gram ℝ (fun i : ι => G (Pi.basisFun ℝ ι i))).det := by
  obtain ⟨L, hright, hsection, hcov⟩ := exists_lattice_covolume_identity Λ π hinteger hsurj
  let D := coordinateScaleEquiv T (fun i => (hT i).ne')
  let G := L.comp D.toLinearMap
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg π hxy
    simpa only [hright] using h
  have hscale := scaled_section_gram_sqrt L hL T hT
  have hprod : 0 < ∏ i, T i := Finset.prod_pos (fun i _ => hT i)
  have hroot : Real.sqrt (Matrix.gram ℝ (fun i : ι => L (Pi.basisFun ℝ ι i))).det =
      Real.sqrt (Matrix.gram ℝ (fun i : ι => G (Pi.basisFun ℝ ι i))).det / ∏ i, T i := by
    apply (eq_div_iff hprod.ne').mpr
    dsimp only [G, D, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hscale]
    ring
  refine ⟨G, ?_, ?_, ?_⟩
  · intro y
    exact hright (D y)
  · intro x
    change L (D (D.symm (π x))) = x - (LinearMap.ker π).starProjection x
    rw [LinearEquiv.apply_symm_apply]
    exact hsection x
  · rw [hroot] at hcov
    rw [hcov]
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EuclideanGraphResidual
namespace OAI

section

namespace Erdos3

variable {σ κ : Type*} [Fintype σ] [Fintype κ]

variable (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
  (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ)) (l : ℕ) (hl : 0 < l)

theorem euclideanDerivative_vertical_lattice_full (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    IsZLattice ℝ (latticeKernel (shortVectorLattice Λ R)
      ((euclideanDerivativeShiftMap T hT).comp Z.subtype)) := by
  apply latticeKernel_full
  intro x hx
  exact euclideanDerivativeShiftMap_integer T hT scale hscale Y A l hl x.val hx

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.DerivativeVerticalBasis
namespace OAI

section

namespace Erdos3

theorem exists_derivative_vertical_basis_matrix
    {σ κ : Type*} [Fintype σ] [Fintype κ] [DecidableEq κ]
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0) (scale : κ → ℝ) (hscale : ∀ j, scale j ≠ 0)
    (Y : (σ → ℝ) →ₗ[ℝ] (κ → ℝ)) (A : (κ → ℝ) ≃ₗ[ℝ] (κ → ℝ))
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    ∃ b : Module.Basis (Fin (Module.finrank ℝ V)) ℤ L,
      ∃ B : Matrix κ (Fin (Module.finrank ℝ V)) ℝ,
        LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
        ∀ j, (b j).val.val.val = euclideanVerticalMap scale hscale A (B.col j) := by
  let Λ := euclideanDerivativeLattice T hT scale hscale Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hscale Y A l hl R
  let b := finiteLatticeBasis L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ κ) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let v := fun j => f (b j).val
  have hli : LinearIndependent ℝ v := by
    have h := (b.ofZLatticeBasis ℝ L).linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    simpa only [v, Function.comp_def, Module.Basis.ofZLatticeBasis_apply,
      LinearIsometry.coe_toLinearMap] using h
  have hv (j) : v j ∈ Λ := (b j).property
  have hz (j) : euclideanDerivativeShiftMap T hT (v j) = 0 := (b j).val.property
  obtain ⟨B, hB, hgrid, he⟩ := exists_vertical_derivative_grid_matrix
    T hT scale hscale Y A l hl v hli hv hz
  exact ⟨b, B, hB, hgrid, he⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.DerivativeIndexBounds
namespace OAI

section

namespace Erdos3

theorem euclideanDerivative_vertical_covolume_lower
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let k := Module.finrank ℝ V
    ∃ p : Fin k → Fin m, Function.Injective p ∧
      1 / (l : ℝ) ^ k * (∏ i, scale (p i)) ≤
        ZLattice.covolume (latticeKernel (shortVectorLattice Λ R) π)
          (MeasureTheory.volume (α := V)) := by
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L :=
    euclideanDerivative_vertical_lattice_full T hT scale (fun j => (hscale j).ne') Y A l hl R
  let b := finiteLatticeBasis L
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  let v := fun j => f (b j).val
  have hli : LinearIndependent ℝ v := by
    have h := (b.ofZLatticeBasis ℝ L).linearIndependent.map' f.toLinearMap
      (LinearMap.ker_eq_bot.mpr f.injective)
    simpa only [v, Function.comp_def, Module.Basis.ofZLatticeBasis_apply,
      LinearIsometry.coe_toLinearMap] using h
  have hv (j) : v j ∈ Λ := (b j).property
  have hz (j) : euclideanDerivativeShiftMap T hT (v j) = 0 := (b j).val.property
  obtain ⟨B, hB, hgrid, he⟩ := exists_vertical_derivative_grid_matrix
    T hT scale (fun j => (hscale j).ne') Y A l hl v hli hv hz
  apply weighted_isometric_lattice_covolume_lower L b f Sum.inr Sum.inr_injective
    B hB l hl hgrid (LinearMap.toMatrix' A.toLinearMap) hA hdiag scale hscale
  intro j i
  have hc := congrArg (fun x : EuclideanSpace ℝ (σ ⊕ Fin m) => x (Sum.inr i)) (he j)
  change f (b j).val (Sum.inr i) = scale i * _
  rw [hc, euclideanVerticalMap_apply_inr]
  apply congrArg (fun t : ℝ => scale i * t)
  have hm := congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap (B.col j)) i
  exact hm.symm

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_vertical_minor_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 0 < scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) :
    let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
      LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      (∀ j, (b j).val.val.val = euclideanVerticalMap scale (fun j => (hscale j).ne') A (B.col j)) ∧
      ∃ p : Fin k → Fin m, Function.Injective p ∧ (B.submatrix p id).det ≠ 0 ∧
        1 / (l : ℝ) ^ k * (∏ i, scale (p i)) ≤
          ZLattice.covolume L (MeasureTheory.volume (α := V)) := by
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hscale j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let : IsZLattice ℝ L :=
    euclideanDerivative_vertical_lattice_full T hT scale (fun j => (hscale j).ne') Y A l hl R
  obtain ⟨b, B, hB, hgrid, he⟩ := exists_derivative_vertical_basis_matrix
    T hT scale (fun j => (hscale j).ne') Y A l hl R
  refine ⟨b, B, hB, hgrid, he, ?_⟩
  let f : V →ₗᵢ[ℝ] EuclideanSpace ℝ (σ ⊕ Fin m) := Z.subtypeₗᵢ.comp V.subtypeₗᵢ
  apply weighted_isometric_lattice_minor_data L b f Sum.inr Sum.inr_injective
    B hB l hl hgrid (LinearMap.toMatrix' A.toLinearMap) hA hdiag scale hscale
  intro j i
  have hc := congrArg (fun x : EuclideanSpace ℝ (σ ⊕ Fin m) => x (Sum.inr i)) (he j)
  change (b j).val.val.val (Sum.inr i) = scale i * _
  rw [hc, euclideanVerticalMap_apply_inr]
  apply congrArg (fun t : ℝ => scale i * t)
  exact (congrFun (LinearMap.toMatrix'_mulVec A.toLinearMap (B.col j)) i).symm

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_basis_data
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    let k := Module.finrank ℝ V
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
    ∃ b : Module.Basis (Fin k) ℤ L, ∃ B : Matrix (Fin m) (Fin k) ℝ,
      LinearIndependent ℝ B.col ∧ (∀ j, B.col j ∈ realDenominatorGrid l) ∧
      (∀ j, (b j).val.val.val = euclideanVerticalMap scale hs0 A (B.col j)) ∧
      ∃ p : Fin k → Fin a, Function.Injective p ∧
        (B.submatrix (Fin.castLE ha ∘ p) id).det ≠ 0 := by
  let hspos : ∀ j, 0 < scale j := fun j => lt_of_lt_of_le zero_lt_one (hscale j)
  let Λ := euclideanDerivativeLattice T hT scale (fun j => (hspos j).ne') Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  dsimp only
  intro hupper
  obtain ⟨b, B, hB, hgrid, hrep, p, hp, hdet, hlower⟩ :=
    euclideanDerivative_vertical_minor_data T hT scale hspos Y A hA hdiag l hl R
  have hhor := pivots_lt_of_weighted_bound p hp scale hscale l hl a Tmin C _ hfar hlower hupper hlarge
  let q : Fin (Module.finrank ℝ V) → Fin a := fun i => ⟨(p i).val, hhor i⟩
  have hq (i) : Fin.castLE ha (q i) = p i := Fin.ext rfl
  refine ⟨b, B, hB, hgrid, hrep, q, ?_, ?_⟩
  · intro i j hij
    apply hp
    rw [← hq i, ← hq j, hij]
  · have he : Fin.castLE ha ∘ q = p := funext hq
    simpa only [he] using hdet

end Erdos3

end

section

namespace Erdos3

theorem euclideanDerivative_horizontal_injective
    {σ : Type*} [Fintype σ] {m : ℕ}
    (T : σ → ℝ) (hT : ∀ i, T i ≠ 0)
    (scale : Fin m → ℝ) (hscale : ∀ j, 1 ≤ scale j)
    (Y : (σ → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (A : (Fin m → ℝ) ≃ₗ[ℝ] (Fin m → ℝ))
    (hA : ∀ i j, i < j → (LinearMap.toMatrix' A.toLinearMap) i j = 0)
    (hdiag : ∀ i, (LinearMap.toMatrix' A.toLinearMap) i i = 1)
    (l : ℕ) (hl : 0 < l) (R : ℝ) (a : ℕ) (ha : a ≤ m) (Tmin C : ℝ)
    (hscalehor : ∀ j, j.val < a → scale j = 1)
    (hblock : ∀ i j, i.val < a → j.val < a →
      (LinearMap.toMatrix' A.toLinearMap) i j = (1 : Matrix (Fin m) (Fin m) ℝ) i j)
    (hfar : ∀ i, a ≤ i.val → Tmin ≤ scale i) (hlarge : C * (l : ℝ) ^ m < Tmin) :
    let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
    let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
    let Z := shortVectorSpan Λ R
    let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
    let V := LinearMap.ker π
    let L := latticeKernel (shortVectorLattice Λ R) π
    ZLattice.covolume L (MeasureTheory.volume (α := V)) ≤ C →
      Function.Injective ((euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)) := by
  let hs0 : ∀ j, scale j ≠ 0 := fun j => (lt_of_lt_of_le zero_lt_one (hscale j)).ne'
  let Λ := euclideanDerivativeLattice T hT scale hs0 Y A l hl
  let Z := shortVectorSpan Λ R
  let π := (euclideanDerivativeShiftMap T hT).comp Z.subtype
  let V := LinearMap.ker π
  let L := latticeKernel (shortVectorLattice Λ R) π
  let P := (euclideanHorizontalProjection a ha).comp (Z.subtype.comp V.subtype)
  dsimp only
  intro hupper
  let : IsZLattice ℝ L := euclideanDerivative_vertical_lattice_full T hT scale hs0 Y A l hl R
  obtain ⟨b, B, _, _, hrep, p, _, hdet⟩ := euclideanDerivative_horizontal_basis_data
    T hT scale hscale Y A hA hdiag l hl R a ha Tmin C hfar hlarge hupper
  let bR := b.ofZLatticeBasis ℝ L
  have hcoord (j) (i : Fin a) : P (bR j) i = B (Fin.castLE ha i) j := by
    simp only [bR, Module.Basis.ofZLatticeBasis_apply]
    change (b j).val.val.val (Sum.inr (Fin.castLE ha i)) = B (Fin.castLE ha i) j
    rw [hrep]
    exact euclideanVerticalMap_horizontal scale hs0 hscalehor A hA hblock (B.col j)
      (Fin.castLE ha i) i.isLt
  apply basis_projection_injective_of_minor bR P p
  have he : Matrix.of (fun i j => P (bR j) (p i)) = B.submatrix (Fin.castLE ha ∘ p) id := by
    ext i j
    exact hcoord j (p i)
  rw [he]
  exact hdet

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.RealSymbolRepresentativeSplitting
namespace OAI

section

namespace Erdos3

open scoped TensorProduct
open NilpotentLieBCHGroup

variable {L M : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
  (I : LieIdeal ℚ L)

theorem realification_ideal_intertwining (B : L →ₗ⁅ℚ⁆ M) (T : L →ₗ[ℚ] M)
    (hT : ∀ a b, b ∈ I → T ⁅a, b⁆ = ⁅B a, T b⁆)
    (x y : ℝ ⊗[ℚ] L) (hy : y ∈ I.toSubmodule.baseChange ℝ) :
    T.baseChange ℝ ⁅x, y⁆ = ⁅realificationLieHom B x, T.baseChange ℝ y⁆ := by
  obtain ⟨v, rfl⟩ := hy
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r a =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul q b =>
      change (r * q) ⊗ₜ[ℚ] T ⁅a, b.val⁆ = (r * q) ⊗ₜ[ℚ] ⁅B a, T b.val⁆
      rw [hT a b.val b.property]
    | add v z hv hz => simp only [map_add, lie_add, hv, hz]
  | add x z hx hz => simp only [map_add, add_lie, hx, hz]

variable {s t : ℕ} (hL : LieModule.lowerCentralSeries ℚ L L s = ⊥)
  (hM : LieModule.lowerCentralSeries ℚ M M t = ⊥)

noncomputable def realIdealAdjoint
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL)) :
    (ℝ ⊗[ℚ] I.toSubmodule) ≃ₗ[ℝ] (ℝ ⊗[ℚ] I.toSubmodule) :=
  (realificationSubmoduleEquiv I.toSubmodule).trans
    ((invariantRealAdjoint ⊤ (I.toSubmodule.baseChange ℝ)
      (fun _ _ _ hy => (I.baseChange ℝ).lie_mem hy) g (by trivial)).trans
        (realificationSubmoduleEquiv I.toSubmodule).symm)

theorem realIdealAdjoint_inclusion
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (x : ℝ ⊗[ℚ] I.toSubmodule) :
    I.toSubmodule.subtype.baseChange ℝ (realIdealAdjoint I hL g x) =
      dualAdjoint g (I.toSubmodule.subtype.baseChange ℝ x) := by
  change (realificationSubmoduleEquiv I.toSubmodule
    ((realificationSubmoduleEquiv I.toSubmodule).symm
      ((invariantRealAdjoint ⊤ (I.toSubmodule.baseChange ℝ)
        (fun _ _ _ hy => (I.baseChange ℝ).lie_mem hy) g (by trivial))
          (realificationSubmoduleEquiv I.toSubmodule x))) : ℝ ⊗[ℚ] L) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem realIdealMap_adjoint (B : L →ₗ⁅ℚ⁆ M) (f : I.toSubmodule →ₗ[ℚ] M)
    (hf : ∀ a (p : I.toSubmodule),
      f ⟨⁅a, p.val⁆, I.lie_mem p.property⟩ = ⁅B a, f p⁆)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hL))
    (x : ℝ ⊗[ℚ] I.toSubmodule) :
    f.baseChange ℝ (realIdealAdjoint I hL g x) =
      dualAdjoint (realificationMap (hnil := hL) (hM := hM) B g) (f.baseChange ℝ x) := by
  obtain ⟨T, hTf⟩ := f.exists_extend
  have he (p : I.toSubmodule) : T p.val = f p := DFunLike.congr_fun hTf p
  have hT (a b : L) (hb : b ∈ I) : T ⁅a, b⁆ = ⁅B a, T b⁆ := by
    rw [he ⟨⁅a, b⁆, I.lie_mem hb⟩, he ⟨b, hb⟩]
    exact hf a ⟨b, hb⟩
  have hr (y : ℝ ⊗[ℚ] I.toSubmodule) :
      T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ y) = f.baseChange ℝ y := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hTf]
  have hx : I.toSubmodule.subtype.baseChange ℝ x ∈ I.toSubmodule.baseChange ℝ := ⟨x, rfl⟩
  let J : LieIdeal ℚ (ℝ ⊗[ℚ] L) :=
    { (I.toSubmodule.baseChange ℝ).restrictScalars ℚ with
      lie_mem := fun {a b} hb => (I.baseChange ℝ).lie_mem hb }
  calc
    _ = T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ (realIdealAdjoint I hL g x)) := (hr _).symm
    _ = T.baseChange ℝ (dualAdjoint g (I.toSubmodule.subtype.baseChange ℝ x)) := by
      rw [realIdealAdjoint_inclusion]
    _ = dualAdjoint (realificationMap (hnil := hL) (hM := hM) B g)
        (T.baseChange ℝ (I.toSubmodule.subtype.baseChange ℝ x)) := by
      exact dualLinearLift_adjoint_of_steps (realification_lowerCentralSeries_eq_bot hL)
        (realification_lowerCentralSeries_eq_bot hM) J
        (realLieHomToRat (realificationLieHom B)) ((T.baseChange ℝ).restrictScalars ℚ)
        (realification_ideal_intertwining I B T hT) g _ hx
    _ = _ := by rw [hr]

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

include hF

theorem realBasis_mem_layer (i : ι) : (b.baseChange ℝ) i ∈ F.realification.layer (ω i) := by
  apply (F.real_mem_layer_iff_basis_coordinates b ω hF _ _).mpr
  intro k hk
  have hki : k ≠ i := by rintro rfl; exact hk le_rfl
  rw [Basis.repr_self]
  exact Finsupp.single_eq_of_ne hki

theorem dualAdjoint_realBasis_coordinate (g : F.realification.Group) (i k : ι)
    (hki : ω k ≤ ω i) :
    (b.baseChange ℝ).repr (dualAdjoint g ((b.baseChange ℝ) i)) k =
      (b.baseChange ℝ).repr ((b.baseChange ℝ) i) k := by
  have hd := F.realification.dualAdjoint_sub_mem_next_layer (ω i) g ((b.baseChange ℝ) i)
    (F.realBasis_mem_layer b ω hF i)
  have hz := (F.real_mem_layer_iff_basis_coordinates b ω hF (ω i + 1) _).mp hd k
    (by omega)
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using hz

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.ControlledSumCoordinates
namespace OAI

section

namespace Erdos3

open scoped Matrix

theorem exists_controlled_sum_coordinates {ι κ ν : Type*}
    [Fintype ι] [Fintype κ] [Fintype ν]
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ) {H l : ℕ} (hH : 1 ≤ H) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) H) (hB : ∀ i j, RationalHeightLE (B i j) H)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hHp : (H : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ u : (ι → ℝ) →ₗ[ℝ] (κ → ℝ), ∃ v : (ι → ℝ) →ₗ[ℝ] (ν → ℝ),
        (∀ x, x ∈ Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) ⊔
          Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) →
          A.map (Rat.castHom ℝ) *ᵥ u x + B.map (Rat.castHom ℝ) *ᵥ v x = x) ∧
        (∀ x, ‖u x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖ ∧
          ‖v x‖ ≤ Real.exp ((p + 2) ^ 18) * ‖x‖) ∧
        ∀ x, x ∈ realDenominatorGrid l →
          u x ∈ realDenominatorGrid m ∧ v x ∈ realDenominatorGrid m := by
  classical
  obtain ⟨S, hS, hdecomp⟩ := exists_rational_sum_coordinates A B hH hA hB
  let m := matrixDenominator S * l
  let u : (ι → ℝ) →ₗ[ℝ] (κ → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inl).comp (S.map (Rat.castHom ℝ)).mulVecLin
  let v : (ι → ℝ) →ₗ[ℝ] (ν → ℝ) :=
    (LinearMap.funLeft ℝ ℝ Sum.inr).comp (S.map (Rat.castHom ℝ)).mulVecLin
  have hnorm (x : ι → ℝ) := real_image_section_norm_bound S H hS hp hι hcols hHp x
  have hgrid (x : ι → ℝ) (hx : x ∈ realDenominatorGrid l) := real_matrix_denominator_grid S l x hx
  refine ⟨m, Nat.mul_pos (matrixDenominator_pos S) hl,
    real_image_section_denominator_bound S H l hS hp hι hcols hHp hlp, u, v, hdecomp, ?_, ?_⟩
  · intro x
    exact ⟨(pi_norm_restriction_le (S.map (Rat.castHom ℝ) *ᵥ x) Sum.inl).trans (hnorm x),
      (pi_norm_restriction_le (S.map (Rat.castHom ℝ) *ᵥ x) Sum.inr).trans (hnorm x)⟩
  · intro x hx
    exact ⟨realDenominatorGrid_comp m _ (hgrid x hx) Sum.inl,
      realDenominatorGrid_comp m _ (hgrid x hx) Sum.inr⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.CanonicalRankCompatibility
namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}

variable (F : NilpotentLieFiltration L s)

theorem canonicalDegreeRank_associatedDegree_eq : F.canonicalDegreeRank.associatedDegree = F :=
  eq_of_layer_eq (funext F.canonicalDegreeRank_associatedDegree_layer)

end Erdos3.NilpotentLieFiltration

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.GradeProjectionRemainder
namespace OAI

section

namespace Erdos3

open Module

namespace NilpotentLieFiltration

open scoped TensorProduct

variable {ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : ι → ℕ)
  (hlayers : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ w i}))

include hlayers in
theorem realGradeProjection_eq_zero_of_mem_next_layer (k : ℕ) (x : ℝ ⊗[ℚ] L)
    (hx : x ∈ F.realification.layer (k + 1)) :
    basisGradeProjection (b.baseChange ℝ) w k x = 0 := by
  apply basisGradeProjection_eq_zero_of_mem_higher
  change x ∈ (F.realLayer (k + 1)).toSubmodule at hx
  rwa [F.realLayer_eq_span_basis b (k + 1) _ (hlayers (k + 1))] at hx

end NilpotentLieFiltration
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.RealDualRationalBounds
namespace OAI

section

namespace Erdos3

open Module NilpotentLieBCHGroup
open scoped TensorProduct

variable {ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem real_dual_adjoint_grid_of_rational (e : Basis ι ℚ L) (l m : ℕ) (hl : 0 < l)
    (had : ∀ (g : NilpotentLieBCHGroup L s hnil) (x : L),
      e.equivFun g.coord ∈ denominatorGrid l → e.equivFun x ∈ denominatorGrid l →
      e.equivFun (dualAdjoint g x) ∈ denominatorGrid m)
    (g : NilpotentLieBCHGroup (ℝ ⊗[ℚ] L) s (realification_lowerCentralSeries_eq_bot hnil))
    (x : ℝ ⊗[ℚ] L)
    (hg : (e.baseChange ℝ).equivFun g.coord ∈ realDenominatorGrid l)
    (hx : (e.baseChange ℝ).equivFun x ∈ realDenominatorGrid l) :
    (e.baseChange ℝ).equivFun (dualAdjoint g x) ∈ realDenominatorGrid m := by
  obtain ⟨a, ha, hea⟩ := real_grid_exists_rationalLieInclusion e l hl _ hg
  obtain ⟨b, hb, heb⟩ := real_grid_exists_rationalLieInclusion e l hl _ hx
  let q : NilpotentLieBCHGroup L s hnil := ⟨a⟩
  have hq := had q b ha hb
  have he : rationalLieInclusion (dualAdjoint q b) = dualAdjoint g x :=
    dualLinearLift_adjoint_eq (realification_lowerCentralSeries_eq_bot hnil)
      (⊤ : LieIdeal ℚ L) rationalLieInclusion rationalLieInclusion.toLinearMap
      (fun u v _ => rationalLieInclusion.map_lie u v) q b (by trivial) g x hea heb
  change (fun i => (e.baseChange ℝ).repr (dualAdjoint g x) i) ∈ realDenominatorGrid m
  rw [← he]
  simp_rw [rationalLieInclusion_coordinates]
  exact (real_cast_mem_denominatorGrid_iff m _).mpr hq

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.BCHSubmoduleRemainder
namespace OAI

section

namespace Erdos3

variable {X L : Type*} [LieRing L] [LieAlgebra ℚ L]

theorem lieBCH_sub_add_mem_submodule {s : ℕ} (hs : 1 ≤ s)
    (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (a b : L) (ha : a ∈ K) (hb : b ∈ K) :
    lieBCH s a b - (a + b) ∈ W := by
  classical
  rw [lieBCH_eq_add_nonlinear_sum hs, add_sub_cancel_left]
  apply Submodule.sum_mem
  intro w hw
  apply W.smul_mem
  apply dynkinWord_mem_submodule_of_nonlinear K W hWK hbracket ![a, b]
  · intro i
    fin_cases i
    · exact ha
    · exact hb
  · exact (Finset.mem_filter.mp hw).2

theorem lieBCH_triple_sub_sum_mem_submodule {s : ℕ} (hs : 1 ≤ s)
    (K W : Submodule ℚ L) (hWK : W ≤ K)
    (hbracket : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ W)
    (a b c : L) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    lieBCH s (lieBCH s a b) c - (a + b + c) ∈ W := by
  have hab := lieBCH_sub_add_mem_submodule hs K W hWK hbracket a b ha hb
  have habK : lieBCH s a b ∈ K := by
    simpa only [sub_add_cancel] using K.add_mem (hWK hab) (K.add_mem ha hb)
  have habc := lieBCH_sub_add_mem_submodule hs K W hWK hbracket (lieBCH s a b) c habK hc
  convert W.add_mem habc hab using 1
  abel

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealizedDualBCH
namespace OAI

section

namespace Erdos3.NilpotentLieBCHGroup

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem dualBCH_insertion_quotient (I J : LieIdeal ℚ L)
    (hIJ : ∀ x ∈ I, ∀ y ∈ I, ⁅x, y⁆ ∈ J) (z : DualGroup hnil) (e m : L)
    (hz : dualTangentLinear z.coord ∈ I) (he : e ∈ I) (hm : m ∈ I) :
    lieBCH s
      (lieBCH s
        (lieBCH s (-lieQuotientMap J e)
          (lieQuotientMap J (dualBaseLinear z.coord + dualTangentLinear z.coord)))
        (-lieQuotientMap J m))
      (-lieQuotientMap J (dualBaseLinear z.coord)) =
      lieQuotientMap J (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m) := by
  have ha : dualInfinitesimal (-e) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, dualTangentLinear_infinitesimal]
    exact I.neg_mem he
  have hb : z.coord ∈ dualIdealSubalgebra I := hz
  have hc : dualInfinitesimal (-m) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, dualTangentLinear_infinitesimal]
    exact I.neg_mem hm
  have hd : -dualConstantLie (dualBaseLinear z.coord) ∈ dualIdealSubalgebra I := by
    rw [mem_dualIdealSubalgebra, map_neg, dualTangentLinear_constant, neg_zero]
    exact I.zero_mem
  have hab := lieBCH_mem (dualIdealSubalgebra I) s ha hb
  have habc := lieBCH_mem (dualIdealSubalgebra I) s hab hc
  have h := congrArg (fun g : DualGroup hnil => dualQuotientEvaluate J g.coord)
    (dualBCH_insertion_identity z e m)
  change dualQuotientEvaluate J
    (lieBCH s (lieBCH s (lieBCH s (dualInfinitesimal (-e)) z.coord) (dualInfinitesimal (-m)))
      (-dualConstantLie (dualBaseLinear z.coord))) =
    dualQuotientEvaluate J (dualInfinitesimal (dualLogDerivative z - e - dualAdjoint (dualBaseHom z) m)) at h
  rw [dualQuotientEvaluate_lieBCH I J hIJ s habc hd,
    dualQuotientEvaluate_lieBCH I J hIJ s hab hc,
    dualQuotientEvaluate_lieBCH I J hIJ s ha hb] at h
  simpa only [dualQuotientEvaluate_apply, map_neg, dualBaseLinear_infinitesimal,
    dualTangentLinear_infinitesimal, dualBaseLinear_constant, dualTangentLinear_constant,
    zero_add, add_zero] using h

end Erdos3.NilpotentLieBCHGroup

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RankBracketFactorizationMonotone
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

theorem realifyFunctional_eq_on_submodule {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℚ V) (ξ η : V →ₗ[ℚ] ℚ) (h : ∀ x ∈ P, ξ x = η x)
    (x : ℝ ⊗[ℚ] V) (hx : x ∈ P.baseChange ℝ) :
    realifyFunctional ξ x = realifyFunctional η x := by
  have hker : P ≤ LinearMap.ker (ξ - η) := by
    intro y hy
    change ξ y - η y = 0
    exact sub_eq_zero.mpr (h y hy)
  have hz := (mem_realified_frequency_kernel_iff (ξ - η) x).mp (Submodule.baseChange_mono ℝ hker hx)
  rw [realifyFunctional_sub_apply] at hz
  exact sub_eq_zero.mp hz

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.RealPolynomialBCH
namespace OAI

section

namespace Erdos3

open Module _root_.MvPolynomial
open scoped TensorProduct

variable {ι σ L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} {hnil : LieModule.lowerCentralSeries ℚ L L s = ⊥}

theorem realPolynomialBCHMap_integer (e : Basis ι ℚ L)
    (P : ι → MvPolynomial σ ℚ) (x : σ → ℤ) :
    realPolynomialBCHMap (hnil := realification_lowerCentralSeries_eq_bot hnil)
      (e.baseChange ℝ) P (fun j => (x j : ℝ)) =
        NilpotentLieBCHGroup.realificationHom (polynomialBCHMap e hnil P x) := by
  apply NilpotentLieBCHGroup.ext
  apply (e.baseChange ℝ).equivFun.injective
  rw [realPolynomialBCHMap_coordinates, NilpotentLieBCHGroup.realificationHom_coordinates]
  funext i
  change aeval (fun j => (x j : ℝ)) (P i) =
    ((e.equivFun (polynomialBCHMap e hnil P x).coord i : ℚ) : ℝ)
  rw [polynomialBCHMap_coordinates]
  change aeval (fun j => (x j : ℝ)) (P i) = ((eval (fun j => (x j : ℚ)) (P i) : ℚ) : ℝ)
  induction P i using MvPolynomial.induction_on with
  | C a => simp only [aeval_C, eval_C]; rfl
  | add p q hp hq => simp only [map_add, Rat.cast_add, hp, hq]
  | mul_X p j hp => simp only [map_mul, aeval_X, eval_X, Rat.cast_mul, hp,
      Rat.cast_intCast]

theorem realification_coset_eq
    (Γ : Subgroup (NilpotentLieBCHGroup L s hnil))
    (a b : NilpotentLieBCHGroup L s hnil)
    (hab : (QuotientGroup.mk a : _ ⧸ Γ) = QuotientGroup.mk b) :
    (QuotientGroup.mk (NilpotentLieBCHGroup.realificationHom a) :
      _ ⧸ Γ.map NilpotentLieBCHGroup.realificationHom) =
        QuotientGroup.mk (NilpotentLieBCHGroup.realificationHom b) := by
  apply QuotientGroup.eq.mpr
  rw [← map_inv, ← map_mul]
  exact Subgroup.mem_map.mpr ⟨a⁻¹ * b, QuotientGroup.eq.mp hab, rfl⟩

end Erdos3

end

end OAI
end


